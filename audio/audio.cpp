#include "audio.h"

#include "../flipcraft.h"

#include <furi.h>
#include <furi_hal.h>
#include <furi_hal_resources.h>
#include <stm32wbxx_ll_tim.h>
#include <stm32wbxx_ll_dma.h>

#include <string.h>

namespace {

typedef struct {
    uint8_t vol;
    uint16_t freq;
    uint16_t phase;
} osc_t;

osc_t osc[4];

uint8_t tickRate = 25;
const uint16_t* trackList = nullptr;
const uint8_t* trackBase = nullptr;
uint8_t trackCount = 0;

uint8_t ChannelActiveMute = 0b11110000;

const uint16_t noteTable[64] = {0,    262,  277,  294,  311,  330,  349,  370,  392,  415,
                                440,  466,  494,  523,  554,  587,  622,  659,  698,  740,
                                784,  831,  880,  932,  988,  1047, 1109, 1175, 1245, 1319,
                                1397, 1480, 1568, 1661, 1760, 1865, 1976, 2093, 2217, 2349,
                                2489, 2637, 2794, 2960, 3136, 3322, 3520, 3729, 3951, 4186,
                                4435, 4699, 4978, 5274, 5588, 5920, 6272, 6645, 7040, 7459,
                                7902, 8372, 8870, 9397};

struct ch_t {
    const uint8_t* ptr;
    uint8_t note;

    uint16_t stackPointer[7];
    uint8_t stackCounter[7];
    uint8_t stackTrack[7];

    uint8_t stackIndex;
    uint8_t repeatPoint;

    uint16_t delay;
    uint8_t counter;
    uint8_t track;

    uint16_t freq;
    uint8_t vol;

    int8_t volFreSlide;
    uint8_t volFreConfig;
    uint8_t volFreCount;

    uint8_t arpNotes;
    uint8_t arpTiming;
    uint8_t arpCount;

    uint8_t reConfig;
    uint8_t reCount;

    int8_t transConfig;

    uint8_t treviDepth;
    uint8_t treviConfig;
    uint8_t treviCount;

    int8_t glisConfig;
    uint8_t glisCount;
};

ch_t channel_state[4];

uint16_t read_vle(const uint8_t** pp) {
    uint16_t q = 0;
    uint8_t d;
    do {
        q <<= 7;
        d = *(*pp)++;
        q |= (d & 0x7F);
    } while(d & 0x80);
    return q;
}

inline const uint8_t* getTrackPointer(uint8_t track) {
    return trackBase + trackList[track];
}

inline uint16_t read_u16_le(const uint8_t** pp) {
    uint16_t lo = *(*pp)++;
    uint16_t hi = *(*pp)++;
    return (uint16_t)(lo | (hi << 8));
}

constexpr uint32_t ATM_PWM_ARR = 255;
constexpr uint32_t ATM_PWM_PSC = 7;
constexpr uint32_t ATM_LOGICAL_HZ = 31250;

inline uint32_t tick_div_from_rate(uint8_t tr) {
    if(tr < 1) tr = 1;
    uint32_t div = ATM_LOGICAL_HZ / (uint32_t)tr;
    if(div < 1) div = 1;
    return div;
}

constexpr size_t ATM_SAMPLES_PER_HALF = 128;
constexpr size_t ATM_DMA_TOTAL = ATM_SAMPLES_PER_HALF * 2;

uint32_t dma_buf[ATM_DMA_TOTAL];

bool atm_running = false;
bool atm_paused = false;

uint16_t atm_master_gain_q8 = (uint16_t)(1.25f * 256.0f + 0.5f);

uint32_t atm_tick_div = 0;
uint32_t atm_tick_acc = 0;
volatile uint32_t atm_tick_pending = 0;

volatile uint8_t atm_audio_enabled = 0;

volatile uint8_t atm_song_ended = 0;
const uint8_t* atm_loop_song = nullptr;

void dma_isr(void* ctx);
void ATM_playroutine();

enum { SFX_BASS = 0, SFX_GRANULAR = 1, SFX_STEP = 2, SFX_VOICES = 3 };

constexpr uint16_t SFX_ENV_DIV = 64;

struct SfxVoice {
    volatile uint8_t active;
    uint8_t isNoise;
    uint8_t noiseStride;
    uint8_t noiseCnt;
    int8_t noiseSign;
    uint16_t phase;
    uint16_t phaseInc;
    uint16_t pitchDrop;
    int16_t vol;
    int16_t decay;
    uint16_t envCount;
    uint32_t noise;
};

SfxVoice sfx[SFX_VOICES];

inline uint32_t sfx_noise_step(uint32_t r) {
    r ^= r << 13;
    r ^= r >> 17;
    r ^= r << 5;
    return r ? r : 0xA5A5A5A5u;
}

inline int32_t sfx_render_sample() {
    int32_t acc = 0;
    for(int i = 0; i < SFX_VOICES; i++) {
        SfxVoice* v = &sfx[i];
        if(!__atomic_load_n(&v->active, __ATOMIC_ACQUIRE)) continue;

        int16_t s;
        if(v->isNoise) {
            if(v->noiseCnt == 0) {
                v->noise = sfx_noise_step(v->noise);
                v->noiseSign = (v->noise & 1) ? 1 : -1;
                v->noiseCnt = v->noiseStride;
            }
            v->noiseCnt--;
            s = (int16_t)(v->noiseSign * v->vol);
        } else {
            v->phase = (uint16_t)(v->phase + v->phaseInc);
            s = (v->phase & 0x8000) ? v->vol : (int16_t)(-v->vol);
        }
        acc += s;

        if(++v->envCount >= SFX_ENV_DIV) {
            v->envCount = 0;
            if(v->pitchDrop && v->phaseInc > v->pitchDrop * 2) v->phaseInc -= v->pitchDrop;
            int16_t nv = (int16_t)(v->vol - v->decay);
            if(nv <= 0) {
                v->vol = 0;
                __atomic_store_n(&v->active, (uint8_t)0, __ATOMIC_RELEASE);
            } else {
                v->vol = nv;
            }
        }
    }
    return acc;
}

void sfx_trigger(
    int slot,
    uint8_t isNoise,
    uint16_t phaseInc,
    uint16_t pitchDrop,
    int16_t vol,
    int16_t decay,
    uint8_t noiseStride) {
    SfxVoice* v = &sfx[slot];
    __atomic_store_n(&v->active, (uint8_t)0, __ATOMIC_RELEASE);
    v->isNoise = isNoise;
    v->phase = 0;
    v->phaseInc = phaseInc;
    v->pitchDrop = pitchDrop;
    v->vol = vol;
    v->decay = decay;
    v->envCount = 0;
    v->noiseStride = noiseStride ? noiseStride : 1;
    v->noiseCnt = 0;
    v->noiseSign = 1;
    if(!v->noise) v->noise = 0x1234abcdu ^ ((uint32_t)slot << 16);
    v->noise = sfx_noise_step(v->noise + DWT->CYCCNT);
    __atomic_store_n(&v->active, (uint8_t)1, __ATOMIC_RELEASE);
}

const uint16_t glassPattern[8] = {5243, 6291, 4660, 7000, 5600, 4194, 6900, 5243};

struct GlassVoice {
    volatile uint8_t active;
    uint8_t idx;
    uint8_t len;
    uint16_t stepSamples;
    uint32_t sampleAcc;
    uint16_t phase;
    uint16_t phaseInc;
    int16_t vol;
    int16_t peak;
    int16_t decay;
    uint16_t envCount;
};

GlassVoice glass;

constexpr uint16_t GLASS_ENV_DIV = 32;

inline int32_t glass_render_sample() {
    if(!__atomic_load_n(&glass.active, __ATOMIC_ACQUIRE)) return 0;

    if(glass.sampleAcc == 0) {
        if(glass.idx >= glass.len) {
            __atomic_store_n(&glass.active, (uint8_t)0, __ATOMIC_RELEASE);
            return 0;
        }
        glass.phaseInc = glassPattern[glass.idx];
        glass.idx++;
        glass.phase = 0;
        glass.vol = glass.peak;
        glass.envCount = 0;
        glass.sampleAcc = glass.stepSamples;
    }
    glass.sampleAcc--;

    glass.phase = (uint16_t)(glass.phase + glass.phaseInc);
    int16_t s = (glass.phase & 0x8000) ? glass.vol : (int16_t)(-glass.vol);

    if(++glass.envCount >= GLASS_ENV_DIV) {
        glass.envCount = 0;
        int16_t nv = (int16_t)(glass.vol - glass.decay);
        glass.vol = nv < 0 ? 0 : nv;
    }
    return s;
}

void glass_trigger(uint8_t len) {
    __atomic_store_n(&glass.active, (uint8_t)0, __ATOMIC_RELEASE);
    if(len > 8) len = 8;
    glass.idx = 0;
    glass.len = len;
    glass.stepSamples = 700;
    glass.sampleAcc = 0;
    glass.phase = 0;
    glass.peak = 72;
    glass.vol = 0;
    glass.decay = 4;
    glass.envCount = 0;
    __atomic_store_n(&glass.active, (uint8_t)1, __ATOMIC_RELEASE);
}

inline uint8_t atm_render_sample_u8() {
    osc[2].phase = (uint16_t)(osc[2].phase + osc[2].freq);
    int8_t phase2 = (int8_t)(osc[2].phase >> 8);
    if(phase2 < 0) phase2 = (int8_t)(~phase2);
    phase2 = (int8_t)(phase2 << 1);
    phase2 = (int8_t)(phase2 - 128);
    int8_t c2 = (int8_t)((((int16_t)phase2 * (int8_t)osc[2].vol) << 1) >> 8);
    int16_t mix = c2;

    osc[0].phase = (uint16_t)(osc[0].phase + osc[0].freq);
    int8_t c0 = (int8_t)osc[0].vol;
    if(osc[0].phase >= 0xC000) c0 = (int8_t)(-c0);
    mix += c0;

    osc[1].phase = (uint16_t)(osc[1].phase + osc[1].freq);
    int8_t c1 = (int8_t)osc[1].vol;
    if(osc[1].phase & 0x8000) c1 = (int8_t)(-c1);
    mix += c1;

    uint16_t freq = osc[3].freq;
    freq <<= 1;
    if(freq & 0x8000) freq ^= 1;
    if(freq & 0x4000) freq ^= 1;
    osc[3].freq = freq;

    int8_t c3 = (int8_t)osc[3].vol;
    if(freq & 0x8000) c3 = (int8_t)(-c3);
    mix += c3;

    const uint16_t gain_q8 = __atomic_load_n(&atm_master_gain_q8, __ATOMIC_RELAXED);
    int32_t centered = ((int32_t)mix * (int32_t)gain_q8) >> 9;

    centered += sfx_render_sample();
    centered += glass_render_sample();

    if(centered > 127) centered = 127;
    if(centered < -127) centered = -127;
    int16_t outv = (int16_t)(128 + centered);
    if(outv < 0) outv = 0;
    if(outv > 255) outv = 255;

    atm_tick_acc++;
    if(atm_tick_acc >= atm_tick_div) {
        atm_tick_acc = 0;
        __atomic_fetch_add(&atm_tick_pending, 1, __ATOMIC_RELAXED);
    }

    return (uint8_t)outv;
}

inline void atm_fill_half(size_t half_index) {
    uint32_t* dst = dma_buf + (half_index * ATM_SAMPLES_PER_HALF);
    const uint8_t en = __atomic_load_n(&atm_audio_enabled, __ATOMIC_RELAXED);
    for(size_t i = 0; i < ATM_SAMPLES_PER_HALF; i++) {
        uint8_t s;
        if(!en) {
            s = 128;
        } else if(atm_paused || !atm_running) {
            int32_t c = sfx_render_sample() + glass_render_sample();
            if(c > 127) c = 127;
            if(c < -127) c = -127;
            s = (uint8_t)(128 + c);
        } else {
            s = atm_render_sample_u8();
        }
        uint32_t duty = (uint32_t)s;
        if(duty > ATM_PWM_ARR) duty = ATM_PWM_ARR;
        dst[i] = duty;
    }
}

void tim16_dma_start() {
    furi_check(furi_hal_speaker_is_mine());
    furi_hal_gpio_init_ex(
        &gpio_speaker, GpioModeAltFunctionPushPull, GpioPullNo, GpioSpeedVeryHigh, GpioAltFn14TIM16);

    atm_tick_div = tick_div_from_rate(tickRate);

    for(size_t i = 0; i < ATM_DMA_TOTAL; i++)
        dma_buf[i] = 128;

    atm_tick_acc = 0;
    __atomic_store_n(&atm_tick_pending, 0, __ATOMIC_RELAXED);

    atm_fill_half(0);
    atm_fill_half(1);

    LL_TIM_DisableAllOutputs(TIM16);
    LL_TIM_DisableCounter(TIM16);
    LL_TIM_SetCounter(TIM16, 0);

    LL_TIM_SetPrescaler(TIM16, ATM_PWM_PSC);
    LL_TIM_SetAutoReload(TIM16, ATM_PWM_ARR);
    LL_TIM_EnableARRPreload(TIM16);

    LL_TIM_OC_SetMode(TIM16, LL_TIM_CHANNEL_CH1, LL_TIM_OCMODE_PWM1);
    LL_TIM_OC_EnablePreload(TIM16, LL_TIM_CHANNEL_CH1);
    LL_TIM_OC_SetCompareCH1(TIM16, dma_buf[0]);
    LL_TIM_OC_SetPolarity(TIM16, LL_TIM_CHANNEL_CH1, LL_TIM_OCPOLARITY_HIGH);

    LL_TIM_CC_EnableChannel(TIM16, LL_TIM_CHANNEL_CH1);
    LL_TIM_EnableAllOutputs(TIM16);

    LL_DMA_InitTypeDef dma_init;
    memset(&dma_init, 0, sizeof(dma_init));
    dma_init.Direction = LL_DMA_DIRECTION_MEMORY_TO_PERIPH;
    dma_init.PeriphOrM2MSrcAddress = (uint32_t)&TIM16->CCR1;
    dma_init.PeriphOrM2MSrcIncMode = LL_DMA_PERIPH_NOINCREMENT;
    dma_init.PeriphOrM2MSrcDataSize = LL_DMA_PDATAALIGN_WORD;
    dma_init.MemoryOrM2MDstAddress = (uint32_t)dma_buf;
    dma_init.MemoryOrM2MDstIncMode = LL_DMA_MEMORY_INCREMENT;
    dma_init.MemoryOrM2MDstDataSize = LL_DMA_MDATAALIGN_WORD;
    dma_init.Mode = LL_DMA_MODE_CIRCULAR;
    dma_init.NbData = ATM_DMA_TOTAL;
    dma_init.Priority = LL_DMA_PRIORITY_HIGH;
    dma_init.PeriphRequest = LL_DMAMUX_REQ_TIM16_UP;

    LL_DMA_DisableChannel(DMA1, LL_DMA_CHANNEL_1);
    LL_DMA_Init(DMA1, LL_DMA_CHANNEL_1, &dma_init);

    LL_DMA_EnableIT_HT(DMA1, LL_DMA_CHANNEL_1);
    LL_DMA_EnableIT_TC(DMA1, LL_DMA_CHANNEL_1);

    furi_hal_interrupt_set_isr_ex(
        FuriHalInterruptIdDma1Ch1, FuriHalInterruptPriorityNormal, dma_isr, NULL);

    LL_DMA_EnableChannel(DMA1, LL_DMA_CHANNEL_1);

    LL_TIM_EnableUpdateEvent(TIM16);
    LL_TIM_EnableDMAReq_UPDATE(TIM16);

    LL_TIM_EnableCounter(TIM16);
    LL_TIM_GenerateEvent_UPDATE(TIM16);
}

void tim16_dma_stop() {
    furi_hal_interrupt_set_isr_ex(
        FuriHalInterruptIdDma1Ch1, FuriHalInterruptPriorityNormal, NULL, NULL);

    LL_TIM_DisableDMAReq_UPDATE(TIM16);

    LL_DMA_DisableIT_HT(DMA1, LL_DMA_CHANNEL_1);
    LL_DMA_DisableIT_TC(DMA1, LL_DMA_CHANNEL_1);
    LL_DMA_DisableChannel(DMA1, LL_DMA_CHANNEL_1);

    LL_TIM_DisableAllOutputs(TIM16);
    LL_TIM_DisableCounter(TIM16);
}

void dma_isr(void*) {
    if(LL_DMA_IsActiveFlag_HT1(DMA1)) {
        LL_DMA_ClearFlag_HT1(DMA1);
        atm_fill_half(0);
    }
    if(LL_DMA_IsActiveFlag_TC1(DMA1)) {
        LL_DMA_ClearFlag_TC1(DMA1);
        atm_fill_half(1);
    }
}

void ATM_playroutine() {
    ch_t* ch;

    for(uint8_t n = 0; n < 4; n++) {
        ch = &channel_state[n];

        if(ch->reConfig) {
            if(ch->reCount >= (ch->reConfig & 0x03)) {
                osc[n].freq = noteTable[ch->reConfig >> 2];
                ch->reCount = 0;
            } else {
                ch->reCount++;
            }
        }

        if(ch->glisConfig) {
            if(ch->glisCount >= (uint8_t)(ch->glisConfig & 0x7F)) {
                if(ch->glisConfig & 0x80)
                    ch->note -= 1;
                else
                    ch->note += 1;

                if(ch->note < 1)
                    ch->note = 1;
                else if(ch->note > 63)
                    ch->note = 63;

                ch->freq = noteTable[ch->note];
                ch->glisCount = 0;
            } else {
                ch->glisCount++;
            }
        }

        if(ch->volFreSlide) {
            if(!ch->volFreCount) {
                int16_t vf = ((ch->volFreConfig & 0x40) ? (int16_t)ch->freq : (int16_t)ch->vol);
                vf += ch->volFreSlide;

                if(!(ch->volFreConfig & 0x80)) {
                    if(vf < 0)
                        vf = 0;
                    else if(ch->volFreConfig & 0x40) {
                        if(vf > 9397) vf = 9397;
                    } else {
                        if(vf > 63) vf = 63;
                    }
                }

                if(ch->volFreConfig & 0x40)
                    ch->freq = (uint16_t)vf;
                else
                    ch->vol = (uint8_t)vf;
            }

            if(ch->volFreCount++ >= (ch->volFreConfig & 0x3F)) ch->volFreCount = 0;
        }

        if(ch->arpNotes && ch->note) {
            if((ch->arpCount & 0x1F) < (ch->arpTiming & 0x1F)) {
                ch->arpCount++;
            } else {
                if((ch->arpCount & 0xE0) == 0x00)
                    ch->arpCount = 0x20;
                else if(
                    (ch->arpCount & 0xE0) == 0x20 && !(ch->arpTiming & 0x40) &&
                    (ch->arpNotes != 0xFF))
                    ch->arpCount = 0x40;
                else
                    ch->arpCount = 0x00;

                uint8_t arpNote = ch->note;

                if((ch->arpCount & 0xE0) != 0x00) {
                    if(ch->arpNotes == 0xFF)
                        arpNote = 0;
                    else
                        arpNote = (uint8_t)(arpNote + (ch->arpNotes >> 4));
                }
                if((ch->arpCount & 0xE0) == 0x40)
                    arpNote = (uint8_t)(arpNote + (ch->arpNotes & 0x0F));

                int16_t idx = (int16_t)arpNote + (int16_t)ch->transConfig;
                if(idx < 0) idx = 0;
                if(idx > 63) idx = 63;
                ch->freq = noteTable[idx];
            }
        }

        if(ch->treviDepth) {
            int16_t vt = ((ch->treviConfig & 0x40) ? (int16_t)ch->freq : (int16_t)ch->vol);
            vt = (ch->treviCount & 0x80) ? (vt + ch->treviDepth) : (vt - ch->treviDepth);

            if(vt < 0)
                vt = 0;
            else if(ch->treviConfig & 0x40) {
                if(vt > 9397) vt = 9397;
            } else {
                if(vt > 63) vt = 63;
            }

            if(ch->treviConfig & 0x40)
                ch->freq = (uint16_t)vt;
            else
                ch->vol = (uint8_t)vt;

            if((ch->treviCount & 0x1F) < (ch->treviConfig & 0x1F))
                ch->treviCount++;
            else
                ch->treviCount = (ch->treviCount & 0x80) ? 0 : 0x80;
        }

        if(ch->delay) {
            if(ch->delay != 0xFFFF) ch->delay--;
        } else {
            do {
                uint8_t cmd = *ch->ptr++;

                if(cmd < 64) {
                    if((ch->note = cmd)) ch->note = (uint8_t)(ch->note + (int8_t)ch->transConfig);

                    int16_t ni = (int16_t)ch->note;
                    if(ni < 0) ni = 0;
                    if(ni > 63) ni = 63;
                    ch->freq = noteTable[ni];

                    if(!ch->volFreConfig) ch->vol = ch->reCount;

                    if(ch->arpTiming & 0x20) ch->arpCount = 0;
                } else if(cmd < 160) {
                    switch(cmd - 64) {
                    case 0:
                        ch->vol = *ch->ptr++;
                        ch->reCount = ch->vol;
                        break;

                    case 1:
                    case 4:
                        ch->volFreSlide = (int8_t)(*ch->ptr++);
                        ch->volFreConfig = ((cmd - 64) == 1) ? 0x00 : 0x40;
                        break;

                    case 2:
                    case 5:
                        ch->volFreSlide = (int8_t)(*ch->ptr++);
                        ch->volFreConfig = *ch->ptr++;
                        break;

                    case 3:
                    case 6:
                        ch->volFreSlide = 0;
                        break;

                    case 7:
                        ch->arpNotes = *ch->ptr++;
                        ch->arpTiming = *ch->ptr++;
                        break;

                    case 8:
                        ch->arpNotes = 0;
                        break;

                    case 9:
                        ch->reConfig = *ch->ptr++;
                        break;

                    case 10:
                        ch->reConfig = 0;
                        break;

                    case 11:
                        ch->transConfig = (int8_t)(ch->transConfig + (int8_t)(*ch->ptr++));
                        break;

                    case 12:
                        ch->transConfig = (int8_t)(*ch->ptr++);
                        break;

                    case 13:
                        ch->transConfig = 0;
                        break;

                    case 14:
                    case 16: {
                        uint16_t depth_w = read_u16_le(&ch->ptr);
                        uint16_t cfg_w = read_u16_le(&ch->ptr);
                        ch->treviDepth = (uint8_t)(depth_w & 0xFF);
                        ch->treviConfig =
                            (uint8_t)((cfg_w & 0xFF) + (((cmd - 64) == 14) ? 0x00 : 0x40));
                        break;
                    }

                    case 15:
                    case 17:
                        ch->treviDepth = 0;
                        break;

                    case 18:
                        ch->glisConfig = (int8_t)(*ch->ptr++);
                        break;

                    case 19:
                        ch->glisConfig = 0;
                        break;

                    case 20:
                        ch->arpNotes = 0xFF;
                        ch->arpTiming = *ch->ptr++;
                        break;

                    case 21:
                        ch->arpNotes = 0;
                        break;

                    case 92:
                        tickRate = (uint8_t)(tickRate + *ch->ptr++);
                        if(tickRate < 1) tickRate = 1;
                        atm_tick_div = tick_div_from_rate(tickRate);
                        break;

                    case 93:
                        tickRate = *ch->ptr++;
                        if(tickRate < 1) tickRate = 1;
                        atm_tick_div = tick_div_from_rate(tickRate);
                        break;

                    case 94:
                        for(uint8_t i = 0; i < 4; i++)
                            channel_state[i].repeatPoint = *ch->ptr++;
                        break;

                    case 95:
                        ChannelActiveMute = (uint8_t)(ChannelActiveMute ^ (1 << (n + 4)));
                        ch->vol = 0;
                        ch->delay = 0xFFFF;
                        break;

                    default:
                        break;
                    }
                } else if(cmd < 224) {
                    ch->delay = (uint16_t)(cmd - 159);
                } else if(cmd == 224) {
                    ch->delay = (uint16_t)(read_vle(&ch->ptr) + 65);
                } else if(cmd == 252 || cmd == 253) {
                    uint8_t new_counter = (cmd == 252) ? 0 : *ch->ptr++;
                    uint8_t new_track = *ch->ptr++;

                    if(new_track != ch->track) {
                        ch->stackCounter[ch->stackIndex] = ch->counter;
                        ch->stackTrack[ch->stackIndex] = ch->track;
                        ch->stackPointer[ch->stackIndex] = (uint16_t)(ch->ptr - trackBase);
                        ch->stackIndex++;
                        ch->track = new_track;
                    }
                    ch->counter = new_counter;
                    ch->ptr = getTrackPointer(ch->track);
                } else if(cmd == 254) {
                    if(ch->counter > 0 || ch->stackIndex == 0) {
                        if(ch->counter) ch->counter--;
                        ch->ptr = getTrackPointer(ch->track);
                    } else {
                        if(ch->stackIndex == 0) {
                            ch->delay = 0xFFFF;
                        } else {
                            ch->stackIndex--;
                            ch->ptr = ch->stackPointer[ch->stackIndex] + trackBase;
                            ch->counter = ch->stackCounter[ch->stackIndex];
                            ch->track = ch->stackTrack[ch->stackIndex];
                        }
                    }
                } else if(cmd == 255) {
                    ch->ptr += read_vle(&ch->ptr);
                } else {
                }
            } while(ch->delay == 0);

            if(ch->delay != 0xFFFF) ch->delay--;
        }

        if(!(ChannelActiveMute & (1 << n))) {
            if(n == 3) {
                osc[n].vol = (uint8_t)(ch->vol >> 1);
            } else {
                osc[n].freq = ch->freq;
                osc[n].vol = ch->vol;
            }
        }

        if(!(ChannelActiveMute & 0xF0)) {
            uint8_t repeatSong = 0;
            for(uint8_t j = 0; j < 4; j++)
                repeatSong = (uint8_t)(repeatSong + channel_state[j].repeatPoint);

            if(repeatSong) {
                for(uint8_t k = 0; k < 4; k++) {
                    channel_state[k].ptr = getTrackPointer(channel_state[k].repeatPoint);
                    channel_state[k].delay = 0;
                }
                ChannelActiveMute = 0b11110000;
            } else {
                atm_running = false;
                __atomic_store_n(&atm_song_ended, (uint8_t)1, __ATOMIC_RELEASE);
                for(uint8_t k = 0; k < 4; k++) osc[k].vol = 0;
            }
        }
    }
}

void atm_begin_song(const uint8_t* song) {
    memset(channel_state, 0, sizeof(channel_state));
    ChannelActiveMute = 0b11110000;

    tickRate = 25;
    atm_tick_div = tick_div_from_rate(tickRate);

    osc[3].freq = 0x0001;
    channel_state[3].freq = 0x0001;

    trackCount = *song++;
    trackList = (const uint16_t*)song;
    song += (trackCount << 1);
    trackBase = song + 4;

    for(uint8_t n = 0; n < 4; n++)
        channel_state[n].ptr = getTrackPointer(*song++);

    __atomic_store_n(&atm_song_ended, (uint8_t)0, __ATOMIC_RELEASE);
    atm_running = true;
    atm_paused = false;
}

enum AtmCmdType : uint8_t {
    AtmCmdPlay,
    AtmCmdStop,
    AtmCmdQuit,
};

struct AtmCmd {
    AtmCmdType type;
    const uint8_t* song;
    uint8_t loop;
};

FuriThread* atm_thread = nullptr;
FuriMessageQueue* atm_cmd_q = nullptr;

int32_t atm_thread_fn(void*) {
    AtmCmd cmd;
    bool speaker_owned = false;

    auto ensure_speaker = [&]() -> bool {
        if(speaker_owned) return true;
        if(furi_hal_speaker_acquire(200)) {
            speaker_owned = true;
            tim16_dma_start();
            return true;
        }
        return false;
    };
    auto release_speaker = [&]() {
        if(speaker_owned) {
            tim16_dma_stop();
            furi_hal_speaker_release();
            speaker_owned = false;
        }
    };

    while(true) {
        if(furi_message_queue_get(atm_cmd_q, &cmd, 10) == FuriStatusOk) {
            if(cmd.type == AtmCmdStop || cmd.type == AtmCmdQuit) {
                atm_running = false;
                atm_paused = false;
                atm_loop_song = nullptr;
                __atomic_store_n(&atm_song_ended, (uint8_t)0, __ATOMIC_RELEASE);
                memset(channel_state, 0, sizeof(channel_state));
                ChannelActiveMute = 0b11110000;
                for(uint8_t k = 0; k < 4; k++) osc[k].vol = 0;
                if(cmd.type == AtmCmdQuit) {
                    release_speaker();
                    break;
                }
                continue;
            }

            if(cmd.type == AtmCmdPlay) {
                atm_loop_song = cmd.loop ? cmd.song : nullptr;
                atm_begin_song(cmd.song);
                continue;
            }
        }

        const uint8_t en = __atomic_load_n(&atm_audio_enabled, __ATOMIC_RELAXED);
        if(!en) {
            release_speaker();
        } else if(!speaker_owned) {
            ensure_speaker();
        }

        if(__atomic_load_n(&atm_song_ended, __ATOMIC_ACQUIRE)) {
            __atomic_store_n(&atm_song_ended, (uint8_t)0, __ATOMIC_RELEASE);
            if(atm_loop_song) atm_begin_song(atm_loop_song);
        }

        if(atm_running && en && !atm_paused) {
            uint32_t pending = __atomic_load_n(&atm_tick_pending, __ATOMIC_RELAXED);
            if(pending) {
                __atomic_fetch_sub(&atm_tick_pending, 1, __ATOMIC_RELAXED);
                ATM_playroutine();
            }
        }
    }
    return 0;
}

void atm_push(AtmCmdType type, const uint8_t* song = nullptr, uint8_t loop = 0) {
    if(!atm_cmd_q) return;
    AtmCmd c{type, song, loop};
    furi_message_queue_put(atm_cmd_q, &c, FuriWaitForever);
}

/*
const uint8_t ambientSong[] = {
    0x04, 0x00, 0x00, 0x6A, 0x00, 0xCD, 0x00, 0x08, 0x02, 0x00, 0x01, 0x02, 0x03, 0x9E,
    0x00, 0x01, 0x02, 0x03, 0x9D, 0x0C, 0x43, 0x48, 0x40, 0x03, 0x0D, 0xCF, 0x40, 0x03,
    0x0F, 0xCF, 0x40, 0x03, 0x0F, 0xCF, 0x40, 0x03, 0x11, 0xCF, 0x40, 0x04, 0x11, 0xCF,
    0x40, 0x03, 0x14, 0xCF, 0x40, 0x04, 0x0F, 0xCF, 0x40, 0x03, 0x11, 0xCF, 0x40, 0x04,
    0x0D, 0xCF, 0x40, 0x04, 0x11, 0xCF, 0x40, 0x04, 0x0F, 0xCF, 0x40, 0x04, 0x14, 0xCF,
    0x40, 0x04, 0x11, 0xCF, 0x40, 0x03, 0x14, 0xCF, 0x40, 0x04, 0x0F, 0xCF, 0x40, 0x03,
    0x11, 0xCF, 0x40, 0x03, 0x0D, 0xCF, 0x40, 0x03, 0x0F, 0xCF, 0x40, 0x03, 0x0C, 0xCF,
    0x40, 0x03, 0x0F, 0xCF, 0x40, 0x03, 0x0D, 0xCF, 0x40, 0x02, 0x11, 0xCF, 0x40, 0x02,
    0x0D, 0xCF, 0x40, 0x02, 0x0F, 0xCF, 0x9F, 0x43, 0x48, 0x40, 0x02, 0x11, 0xCF, 0x40,
    0x06, 0x19, 0xCF, 0x40, 0x02, 0x14, 0xCF, 0x40, 0x06, 0x1B, 0xCF, 0x40, 0x07, 0x1D,
    0xCF, 0x40, 0x02, 0x16, 0xCF, 0x40, 0x07, 0x1B, 0xCF, 0x40, 0x07, 0x19, 0xCF, 0x40,
    0x02, 0x14, 0xCF, 0x40, 0x08, 0x16, 0xCF, 0x40, 0x08, 0x19, 0xCF, 0x40, 0x02, 0x16,
    0xCF, 0x40, 0x07, 0x1B, 0xCF, 0x40, 0x02, 0x19, 0xCF, 0x40, 0x07, 0x19, 0xCF, 0x40,
    0x07, 0x16, 0xCF, 0x40, 0x02, 0x11, 0xCF, 0x40, 0x06, 0x14, 0xCF, 0x40, 0x02, 0x11,
    0xCF, 0x40, 0x06, 0x16, 0xCF, 0x40, 0x05, 0x19, 0xCF, 0x40, 0x02, 0x14, 0xCF, 0x40,
    0x04, 0x16, 0xCF, 0x40, 0x04, 0x14, 0xCF, 0x9F, 0x43, 0x48, 0x40, 0x08, 0x0D, 0xA8,
    0x0F, 0xA8, 0x11, 0xA8, 0x14, 0xA8, 0x16, 0xA8, 0x14, 0xA2, 0x0D, 0xA8, 0x0F, 0xA8,
    0x11, 0xA8, 0x14, 0xA8, 0x16, 0xA8, 0x14, 0xA2, 0x40, 0x09, 0x0F, 0xA8, 0x11, 0xA8,
    0x14, 0xA8, 0x16, 0xA8, 0x19, 0xA8, 0x16, 0xA2, 0x0F, 0xA8, 0x11, 0xA8, 0x14, 0xA8,
    0x16, 0xA8, 0x19, 0xA8, 0x16, 0xA2, 0x40, 0x0A, 0x11, 0xA8, 0x14, 0xA8, 0x16, 0xA8,
    0x19, 0xA8, 0x1B, 0xA8, 0x19, 0xA2, 0x11, 0xA8, 0x14, 0xA8, 0x16, 0xA8, 0x19, 0xA8,
    0x1B, 0xA8, 0x19, 0xA2, 0x40, 0x0A, 0x0F, 0xA8, 0x11, 0xA8, 0x14, 0xA8, 0x16, 0xA8,
    0x19, 0xA8, 0x16, 0xA2, 0x0F, 0xA8, 0x11, 0xA8, 0x14, 0xA8, 0x16, 0xA8, 0x19, 0xA8,
    0x16, 0xA2, 0x40, 0x0B, 0x0D, 0xA8, 0x11, 0xA8, 0x14, 0xA8, 0x16, 0xA8, 0x19, 0xA8,
    0x16, 0xA2, 0x0D, 0xA8, 0x11, 0xA8, 0x14, 0xA8, 0x16, 0xA8, 0x19, 0xA8, 0x16, 0xA2,
    0x40, 0x0B, 0x0F, 0xA8, 0x14, 0xA8, 0x16, 0xA8, 0x19, 0xA8, 0x1B, 0xA8, 0x19, 0xA2,
    0x0F, 0xA8, 0x14, 0xA8, 0x16, 0xA8, 0x19, 0xA8, 0x1B, 0xA8, 0x19, 0xA2, 0x40, 0x0A,
    0x11, 0xA8, 0x14, 0xA8, 0x19, 0xA8, 0x1B, 0xA8, 0x1D, 0xA8, 0x1B, 0xA2, 0x11, 0xA8,
    0x14, 0xA8, 0x19, 0xA8, 0x1B, 0xA8, 0x1D, 0xA8, 0x1B, 0xA2, 0x40, 0x0A, 0x0F, 0xA8,
    0x11, 0xA8, 0x16, 0xA8, 0x19, 0xA8, 0x1B, 0xA8, 0x19, 0xA2, 0x0F, 0xA8, 0x11, 0xA8,
    0x16, 0xA8, 0x19, 0xA8, 0x1B, 0xA8, 0x19, 0xA2, 0x40, 0x09, 0x0D, 0xA8, 0x0F, 0xA8,
    0x11, 0xA8, 0x14, 0xA8, 0x16, 0xA8, 0x14, 0xA2, 0x0D, 0xA8, 0x0F, 0xA8, 0x11, 0xA8,
    0x14, 0xA8, 0x16, 0xA8, 0x14, 0xA2, 0x40, 0x08, 0x0C, 0xA8, 0x0F, 0xA8, 0x11, 0xA8,
    0x14, 0xA8, 0x16, 0xA8, 0x14, 0xA2, 0x0C, 0xA8, 0x0F, 0xA8, 0x11, 0xA8, 0x14, 0xA8,
    0x16, 0xA8, 0x14, 0xA2, 0x40, 0x07, 0x0D, 0xA8, 0x11, 0xA8, 0x14, 0xA8, 0x16, 0xA8,
    0x19, 0xA8, 0x16, 0xA2, 0x0D, 0xA8, 0x11, 0xA8, 0x14, 0xA8, 0x16, 0xA8, 0x19, 0xA8,
    0x16, 0xA2, 0x40, 0x06, 0x0D, 0xA8, 0x0F, 0xA8, 0x11, 0xA8, 0x14, 0xA8, 0x16, 0xA8,
    0x14, 0xA2, 0x0D, 0xA8, 0x0F, 0xA8, 0x11, 0xA8, 0x14, 0xA8, 0x16, 0xA8, 0x14, 0xA2,
    0x9F, 0x9F,
};
*/

bool g_initialised = false;

bool isGranular(uint8_t blockId) {
    switch(blockId) {
    case flipcraft::BLOCK_SAND:
    case flipcraft::BLOCK_DIRT:
    case flipcraft::BLOCK_GRASS:
    case flipcraft::BLOCK_LEAVES:
    case flipcraft::BLOCK_SAPLING:
        return true;
    default:
        return false;
    }
}

}

namespace flipcraft {
namespace audio {

void init() {
    if(g_initialised) return;
    memset(sfx, 0, sizeof(sfx));
    memset(&glass, 0, sizeof(glass));
    atm_cmd_q = furi_message_queue_alloc(8, sizeof(AtmCmd));
    if(!atm_cmd_q) return;

    atm_thread = furi_thread_alloc();
    if(!atm_thread) {
        furi_message_queue_free(atm_cmd_q);
        atm_cmd_q = nullptr;
        return;
    }
    furi_thread_set_name(atm_thread, "FlipcraftAudio");
    furi_thread_set_stack_size(atm_thread, 2048);
    furi_thread_set_priority(atm_thread, FuriThreadPriorityHigh);
    furi_thread_set_callback(atm_thread, atm_thread_fn);

    __atomic_store_n(&atm_audio_enabled, (uint8_t)1, __ATOMIC_RELAXED);
    furi_thread_start(atm_thread);
    g_initialised = true;
}

void deinit() {
    if(!g_initialised) return;
    atm_push(AtmCmdQuit);
    furi_thread_join(atm_thread);
    furi_thread_free(atm_thread);
    furi_message_queue_free(atm_cmd_q);
    atm_thread = nullptr;
    atm_cmd_q = nullptr;
    __atomic_store_n(&atm_audio_enabled, (uint8_t)0, __ATOMIC_RELAXED);
    g_initialised = false;
}

void startAmbient() {
    if(!g_initialised) return;
    // atm_push(AtmCmdPlay, ambientSong, 1);
}

void stopAmbient() {
    if(!g_initialised) return;
    atm_push(AtmCmdStop);
}

void blockPlace(uint8_t blockId) {
    if(!g_initialised) return;

    if(blockId == flipcraft::BLOCK_GLASS) {
        glass_trigger(3);
    } else if(isGranular(blockId)) {
        sfx_trigger(SFX_GRANULAR, 1, 0, 0, 60, 1, 4);
    } else {
        sfx_trigger(SFX_BASS, 0, 300, 3, 78, 1, 1);
        sfx_trigger(SFX_GRANULAR, 1, 0, 0, 34, 3, 2);
    }
}

void blockBreak(uint8_t blockId) {
    if(!g_initialised) return;

    if(blockId == flipcraft::BLOCK_GLASS) {
        glass_trigger(8);
    } else if(isGranular(blockId)) {
        sfx_trigger(SFX_GRANULAR, 1, 0, 0, 64, 2, 3);
    } else {
        sfx_trigger(SFX_BASS, 0, 260, 4, 70, 1, 1);
        sfx_trigger(SFX_GRANULAR, 1, 0, 0, 30, 3, 2);
    }
}

void land() {
    if(!g_initialised) return;
    sfx_trigger(SFX_BASS, 0, 200, 3, 82, 1, 1);
    sfx_trigger(SFX_GRANULAR, 1, 0, 0, 26, 3, 6);
}

void footstep() {
    if(!g_initialised) return;
    sfx_trigger(SFX_STEP, 1, 0, 0, 18, 2, 16);
}

}
}

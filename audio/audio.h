#pragma once

#include <cstdint>

namespace flipcraft {
namespace audio {

void init();
void deinit();

void startAmbient();
void stopAmbient();

void blockPlace(uint8_t blockId);
void blockBreak(uint8_t blockId);
void land();
void footstep();

}
}

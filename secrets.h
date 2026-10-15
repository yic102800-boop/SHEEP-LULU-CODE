#pragma once

#include "wifi_secrets.h"

// Add your own API keys locally before uploading to the ESP32.
// Do not commit real API keys or Wi-Fi passwords to GitHub.

// Doubao Speech ASR/TTS API Key
static const char DOUBAO_API_KEY[] = "YOUR_DOUBAO_API_KEY";
static const char ASR_RESOURCE_ID[] = "volc.seedasr.sauc.duration";

// Volcengine Ark text model API Key
static const char ARK_API_KEY[] = "YOUR_ARK_API_KEY";
static const char DOUBAO_TEXT_MODEL[] = "doubao-seed-2-1-lite-260915";

// Doubao Speech TTS settings
static const char TTS_RESOURCE_ID[] = "seed-tts-2.0";
static const char TTS_SPEAKER[] = "zh_female_vv_uranus_bigtts";

#include <WiFi.h>
#include <WebServer.h>
#include <DNSServer.h>
#include <WebSocketsClient.h>
#include <ArduinoJson.h>
#include <ESP_I2S.h>
#include <HTTPClient.h>
#include <NetworkClientSecure.h>
#include <mbedtls/base64.h>
#include <miniz.h>
#include <esp_heap_caps.h>
#include <esp_system.h>
#include <Preferences.h>
#include <FFat.h>
#include <time.h>
#include <sys/time.h>
#include <SPI.h>
#include <Wire.h>
#include <VL53L1X.h>
#include <ESP32Servo.h>
#include <U8g2lib.h>
#include "secrets.h"
#include "root_ca.h"
#include "lulu_lamb_audio.h"
// Optional MP3 support: install the Arduino library "libhelix" (by Phil Schatzmann).
// Without it the sketch still compiles and only WAV songs can be played.
#if __has_include("libhelix-mp3/mp3dec.h")
#include "libhelix-mp3/mp3dec.h"   // has its own extern "C" guard; do not wrap it here
#define LULU_HAS_MP3 1
#else
#define LULU_HAS_MP3 0
#endif

// Audio pins are moved so the original sheep_robot_full_test wiring can stay.
// ESP32-S3 microphone L/R tied to GND selects LEFT slot.
constexpr int MIC_BCLK_PIN = 6;
constexpr int MIC_WS_PIN = 7;
constexpr int MIC_DATA_PIN = 18;
constexpr int SPEAKER_BCLK_PIN = 38;
constexpr int SPEAKER_LRC_PIN = 39;
constexpr int SPEAKER_DATA_PIN = 40;
constexpr int RECORD_BUTTON_PIN = 0;
// Original robot wiring: TTP223 OUT -> GPIO21.
// Touching the head wakes Lulu without needing to say her name.
constexpr int HEAD_TOUCH_PIN = 21;
// Connect MAX98357A SD/EN to this pin. LOW keeps the amplifier silent;
// HIGH enables it only while an AI reply is playing.
constexpr int SPEAKER_ENABLE_PIN = 41;

// Robot body pins are unchanged from sheep_robot_full_test.ino.
constexpr int SERVO_LR_PIN = 4;
constexpr int SERVO_UD_PIN = 5;
// Physical positions from the user's viewpoint while facing Lulu.
constexpr int LEFT_SDA_PIN = 8;
constexpr int LEFT_SCL_PIN = 9;
constexpr int LEFT_XSHUT_PIN = 10;
constexpr int RIGHT_SDA_PIN = 11;
constexpr int RIGHT_SCL_PIN = 2;
constexpr int RIGHT_XSHUT_PIN = 17;
constexpr int OLED_CLK_PIN = 12;
constexpr int OLED_MOSI_PIN = 13;
constexpr int OLED_RESET_PIN = 14;
constexpr int OLED_DC_PIN = 15;
constexpr int OLED_CS_PIN = 16;

// 0 = software SPI (original, slow full-screen refresh)
// 1 = hardware SPI on the same pins (much faster; if the screen goes blank, set back to 0)
#define OLED_USE_HW_SPI 0

// One consistent Lulu voice for both Chinese and English replies.
// This follows the user's latest explicit choice: Peppa Pig / 佩奇猪 2.0.
constexpr const char *LULU_TTS_SPEAKER = "zh_female_peiqi_uranus_bigtts";
constexpr const char *LULU_TTS_RESOURCE_ID = "seed-tts-2.0";
// Change these three values if Lulu moves to another city.
constexpr float HOME_LATITUDE = -37.8136f;
constexpr float HOME_LONGITUDE = 144.9631f;
constexpr const char *HOME_CITY = "Melbourne";
constexpr const char *HOME_TIMEZONE = "AEST-10AEDT,M10.1.0/2,M4.1.0/3";
// Recording stops by itself when you stop speaking (energy-based voice detection).
constexpr size_t MAX_SAMPLES = 16000 * 25;          // slow questions can last up to 25 s
constexpr uint32_t WAIT_FOR_SPEECH_MS = 6000;       // give the user time to begin
constexpr uint32_t DEFAULT_END_SILENCE_MS = 1300;   // silence that ends an utterance; live: pause MS (800-5000)
constexpr size_t BLOCK_SAMPLES = 320;               // 20 ms analysis blocks at 16 kHz
// Keep WebSocket payloads below 1400 bytes so this Arduino WebSockets version
// uses its standards-compliant randomly masked client-frame path.
constexpr size_t CHUNK_BYTES = BLOCK_SAMPLES * sizeof(int16_t); // 20 ms live PCM
constexpr size_t PACKET_BYTES = CHUNK_BYTES + 256;
constexpr size_t RESPONSE_BYTES = 16384;
constexpr int MIC_DIGITAL_GAIN = 3; // target speech peaks about 8000-25000; change live with: gain N
constexpr size_t PREROLL_SAMPLES = 16000 * 6 / 10;  // keep 0.6 s before the first word
constexpr int WAKE_TRIGGER_BLOCKS = 6;              // 120 ms: short/soft "Lulu" still wakes
constexpr uint32_t FOLLOWUP_MS = 5000;              // short follow-up window after an answer
constexpr uint32_t WAKE_COMMAND_MS = 6000;          // time to ask after saying only "Lulu"
I2SClass mic;
WebSocketsClient ws;
uint8_t packet[PACKET_BYTES];
uint8_t responseBuffer[RESPONSE_BYTES];
String language = "auto", headers, lastText, lastDisplayedText, previousUser, previousAssistant;
String latestHeardText, latestReplyText;
bool connected = false, requestAccepted = false, finished = false, failed = false;
uint32_t lastTranscriptAt = 0;   // when the live transcript last changed
bool buttonArmed = false;
uint32_t pressedAt = 0;
volatile bool queuedTouchBleat = false;
volatile bool touchPhysicalActive = false;
volatile uint32_t touchQueuedAt = 0;   // millis() when the touch was detected (latency log)
// true while Lulu is listening / thinking / speaking: a head touch then only
// makes her react (silent nod), it does not wake her or start a new question.
volatile bool touchReactionOnly = false;
// Serial command "touchdebug": prints every raw change of the touch pin so the
// sensor's real sensitivity can be checked independently of the program logic.
bool touchDebug = false;
bool touchDebugLast = false;
bool touchIdleLevel = false;
String command;
String pendingAction = "none", pendingNote, pendingWhen;
uint32_t pendingSeconds = 0;
bool pendingEnglish = false;

struct AlertItem {
  bool active = false;
  bool timer = false;
  uint32_t dueMillis = 0;
  time_t dueEpoch = 0;
  String note;
};
constexpr int MAX_ALERTS = 6;
AlertItem alerts[MAX_ALERTS];
Preferences reminderStore;
WebServer luluWeb(80);
bool luluWebReady = false;
bool luluStorageReady = false;
const char *ttsSavePath = nullptr;   // set before speakDoubao() to cache that line in FFat
String queuedSongPath;
File songUploadFile;
bool songUploadOK = false;
String songUploadError, songUploadPath;

void playLambBleat(bool animateNod = false);
void handleQueuedTouchBleat();
void recognize(bool wake);
void touchWakeFlow();
void serviceLuluWeb();
void startLuluWeb();
bool playWavSong(const String &path);
bool playSong(const String &path);
void printStorageInfo();

// ---------------------------------------------------------------------------
// OLED face, servos and two VL53L1X hand-follow sensors
// ---------------------------------------------------------------------------
TwoWire leftI2C = TwoWire(0);
TwoWire rightI2C = TwoWire(1);
VL53L1X leftDistanceSensor;
VL53L1X rightDistanceSensor;
bool leftDistanceReady = false;
bool rightDistanceReady = false;

Servo servoLR;
Servo servoUD;
// ---- Robot body tuning ----------------------------------------------------
#define OLED_ROTATION U8G2_R2           // U8G2_R0 = normal, U8G2_R2 = turned 180 degrees
constexpr int EYE_GAZE_SIGN = 1;         // user's viewpoint while facing Lulu

// Servo angles are now converted to pulse widths (writeMicroseconds) with the
// same mapping used by the standalone calibration sketch, so the numbers below
// are exactly the values measured there:
//   GPIO4 = X axis (head left-right), servo travel 270 degrees
//   GPIO5 = Y axis (head up-down),    servo travel 180 degrees
//   pulse 500 us = 0 degrees, 2500 us = full travel
constexpr int X_RANGE_DEG = 270;
constexpr int Y_RANGE_DEG = 180;
constexpr int SERVO_PULSE_MIN_US = 500;
constexpr int SERVO_PULSE_MAX_US = 2500;

// Measured positions (user's viewpoint while facing Lulu).
constexpr int X_CENTER = 105;
constexpr int X_LEFT_MAX = 145;    // head turned fully to the left
constexpr int X_RIGHT_MAX = 65;    // head turned fully to the right
constexpr int Y_CENTER = 25;
constexpr int Y_UP_MAX = 0;        // head tilted fully up
constexpr int Y_DOWN_MAX = 40;     // head tilted fully down

// Soft limits used by every servo move in this sketch.
constexpr int X_SAFE_MIN = X_RIGHT_MAX;
constexpr int X_SAFE_MAX = X_LEFT_MAX;
constexpr int Y_SAFE_MIN = Y_UP_MAX;
constexpr int Y_SAFE_MAX = Y_DOWN_MAX;
static_assert(X_SAFE_MIN >= 0 && X_SAFE_MAX <= X_RANGE_DEG,
              "X servo limits must stay within the servo travel");
static_assert(Y_SAFE_MIN >= 0 && Y_SAFE_MAX <= Y_RANGE_DEG,
              "Y servo limits must stay within the servo travel");
static_assert(X_CENTER >= X_SAFE_MIN && X_CENTER <= X_SAFE_MAX, "X centre outside limits");
static_assert(Y_CENTER >= Y_SAFE_MIN && Y_CENTER <= Y_SAFE_MAX, "Y centre outside limits");

constexpr int LR_CENTER = X_CENTER;
constexpr int UD_CENTER = Y_CENTER;
constexpr int LR_LEFT = X_SAFE_MAX;       // X axis: larger angle = head turns left
constexpr int LR_RIGHT = X_SAFE_MIN;
constexpr int UD_NOD_DOWN = Y_DOWN_MAX;   // Y axis: larger angle = head tilts down
constexpr int UD_NOD_UP = Y_UP_MAX;
constexpr int UD_FOLLOW_DOWN = Y_DOWN_MAX; // head tilt when a hand is very close
constexpr int UD_FOLLOW_UP = Y_UP_MAX;     // head tilt when a hand is at the far edge of range
constexpr bool ENABLE_UD_FOLLOW = true; // false = left/right only, like sheep_robot_full_test
constexpr uint32_t HEAD_STEP_MS = 15;   // one degree per step (smaller = faster)
constexpr uint32_t NOD_STEP_MS = 12;
constexpr uint32_t RETURN_CENTER_MS = 1500; // return to centre this long after the hand leaves
constexpr uint32_t HAND_DROPOUT_MS = 400;   // ignore sensor dropouts shorter than this
float lrBiasSmooth = 0;                     // filtered left/right hand position (-1..+1)
constexpr int HAND_MIN_MM = 40;
constexpr uint16_t SENSOR_INVALID = 8190;
int handNearMM = 150;                   // below this a hand counts as "near"; live: near N
bool handDebug = false;                 // live: debug (prints both distances)
float handDistSmooth = -1;              // filtered hand distance (mm); -1 = no hand
int currentLR = LR_CENTER;
int targetLR = LR_CENTER;
int currentUD = UD_CENTER;
int targetUD = UD_CENTER;
bool servoCalibrationMode = false;
int lastWrittenLR = -1;
int lastWrittenUD = -1;
int gazeOffsetX = 0;
uint16_t lastLeftMM = SENSOR_INVALID;
uint16_t lastRightMM = SENSOR_INVALID;
uint32_t lastServoStepAt = 0;
uint32_t lastDistanceReadAt = 0;
uint32_t lastHandSeenAt = 0;
uint32_t lastDebugAt = 0;
uint32_t lastEyeFrameAt = 0;
uint32_t nextBlinkAt = 0;
uint32_t blinkUntil = 0;
bool eyeDirty = true;
bool lastBlinking = false;

#if OLED_USE_HW_SPI
U8G2_SH1106_128X64_NONAME_F_4W_HW_SPI robotDisplay(
  OLED_ROTATION, OLED_CS_PIN, OLED_DC_PIN, OLED_RESET_PIN
);
#else
U8G2_SH1106_128X64_NONAME_F_4W_SW_SPI robotDisplay(
  OLED_ROTATION, OLED_CLK_PIN, OLED_MOSI_PIN,
  OLED_CS_PIN, OLED_DC_PIN, OLED_RESET_PIN
);
#endif
enum RobotFace : uint8_t {
  FACE_NORMAL,
  FACE_LISTENING,
  FACE_THINKING,
  FACE_HAPPY,
  FACE_SLEEPY,
  FACE_ANGRY,      // 5
  FACE_SAD,        // 6
  FACE_LOVE,       // 7
  FACE_SURPRISED,  // 8
  FACE_WINK,       // 9
  FACE_JOY,        // 10  ^ ^
  FACE_DIZZY,      // 11  X X
  FACE_STARRY,     // 12
  FACE_CRY,        // 13
  FACE_TIRED,      // 14
  FACE_SHY,        // 15
  FACE_LAUGH       // 16  > <
};

RobotFace robotFace = FACE_NORMAL;      // what the OLED shows right now
RobotFace autoFace = FACE_NORMAL;       // what Lulu's own logic wants to show
int webFaceOverride = -1;               // -1 = automatic, 0..16 = face picked on the web page
volatile bool handFollowActive = false; // a hand is currently being followed
bool silentNodActive = false;

// ---- Extra expressions (faces 5-16) -------------------------------------------
static void thickLine(int x0, int y0, int x1, int y1, int t) {
  for (int i = -(t / 2); i <= t / 2; ++i) {
    robotDisplay.drawLine(x0, y0 + i, x1, y1 + i);
    robotDisplay.drawLine(x0 + i, y0, x1 + i, y1);
  }
}
static void drawHeartShape(int cx, int cy) {
  robotDisplay.drawDisc(cx - 6, cy, 7);
  robotDisplay.drawDisc(cx + 6, cy, 7);
  robotDisplay.drawTriangle(cx - 13, cy + 2, cx + 13, cy + 2, cx, cy + 16);
}
static void drawStarShape(int cx, int cy, int s) {
  robotDisplay.drawTriangle(cx - 3, cy, cx + 3, cy, cx, cy - s);
  robotDisplay.drawTriangle(cx - 3, cy, cx + 3, cy, cx, cy + s);
  robotDisplay.drawTriangle(cx, cy - 3, cx, cy + 3, cx - s, cy);
  robotDisplay.drawTriangle(cx, cy - 3, cx, cy + 3, cx + s, cy);
  robotDisplay.drawBox(cx - 3, cy - 3, 6, 6);
}
static void drawTear(int cx) {
  robotDisplay.drawTriangle(cx, 46, cx - 4, 53, cx + 4, 53);
  robotDisplay.drawDisc(cx, 54, 4);
}
// Returns true when it drew the face itself. lx / rx are the left x of each
// eye box (28 / 74 plus the gaze offset), so every face still follows the hand.
static bool drawExtraFace(int lx, int rx) {
  int lc = lx + 13, rc = rx + 13;   // eye centres
  switch (robotFace) {
    case FACE_ANGRY:
      robotDisplay.drawRBox(lx, 17, 26, 30, 7); robotDisplay.drawRBox(rx, 17, 26, 30, 7);
      robotDisplay.setDrawColor(0);
      robotDisplay.drawTriangle(lx - 2, 13, lx + 28, 13, lx + 28, 31);
      robotDisplay.drawTriangle(rx - 2, 13, rx + 28, 13, rx - 2, 31);
      robotDisplay.setDrawColor(1); return true;
    case FACE_SAD:
      robotDisplay.drawRBox(lx, 20, 26, 30, 7); robotDisplay.drawRBox(rx, 20, 26, 30, 7);
      robotDisplay.setDrawColor(0);
      robotDisplay.drawTriangle(lx - 2, 16, lx + 28, 16, lx - 2, 34);
      robotDisplay.drawTriangle(rx - 2, 16, rx + 28, 16, rx + 28, 34);
      robotDisplay.setDrawColor(1); return true;
    case FACE_LOVE:
      drawHeartShape(lc, 21); drawHeartShape(rc, 21); return true;
    case FACE_SURPRISED:
      robotDisplay.drawRBox(lc - 11, 10, 22, 44, 10); robotDisplay.drawRBox(rc - 11, 10, 22, 44, 10);
      robotDisplay.setDrawColor(0);
      robotDisplay.drawDisc(lc, 29, 3); robotDisplay.drawDisc(rc, 29, 3);
      robotDisplay.setDrawColor(1); return true;
    case FACE_WINK:
      robotDisplay.drawRBox(lx, 17, 26, 30, 7);
      thickLine(rx + 2, 32, rx + 24, 24, 4); thickLine(rx + 2, 32, rx + 24, 40, 4);
      return true;
    case FACE_JOY:
      for (int c = 0; c < 2; ++c) {
        int cx = c ? rc : lc;
        thickLine(cx - 13, 40, cx - 6, 31, 4); thickLine(cx - 6, 31, cx, 28, 4);
        thickLine(cx, 28, cx + 6, 31, 4);      thickLine(cx + 6, 31, cx + 13, 40, 4);
      }
      return true;
    case FACE_DIZZY:
      for (int c = 0; c < 2; ++c) {
        int cx = c ? rc : lc;
        thickLine(cx - 11, 20, cx + 11, 42, 4); thickLine(cx - 11, 42, cx + 11, 20, 4);
      }
      return true;
    case FACE_STARRY:
      drawStarShape(lc, 31, 17); drawStarShape(rc, 31, 17);
      robotDisplay.drawDisc(6, 8, 2); robotDisplay.drawDisc(121, 53, 2);
      return true;
    case FACE_CRY:
      robotDisplay.drawRBox(lx, 14, 26, 28, 7); robotDisplay.drawRBox(rx, 14, 26, 28, 7);
      robotDisplay.setDrawColor(0);
      robotDisplay.drawTriangle(lx - 2, 10, lx + 28, 10, lx - 2, 26);
      robotDisplay.drawTriangle(rx - 2, 10, rx + 28, 10, rx + 28, 26);
      robotDisplay.setDrawColor(1);
      drawTear(lc - 7); drawTear(rc + 7); return true;
    case FACE_TIRED:
      robotDisplay.drawRBox(lx, 22, 26, 26, 7); robotDisplay.drawRBox(rx, 22, 26, 26, 7);
      robotDisplay.setDrawColor(0);
      robotDisplay.drawBox(lx - 2, 18, 30, 16); robotDisplay.drawBox(rx - 2, 18, 30, 16);
      robotDisplay.setDrawColor(1); return true;
    case FACE_SHY:
      robotDisplay.drawRBox(lx + 2, 28, 22, 14, 6); robotDisplay.drawRBox(rx + 2, 28, 22, 14, 6);
      for (int i = 0; i < 3; ++i) {
        robotDisplay.drawLine(lx - 8 + i * 4, 54, lx - 5 + i * 4, 49);
        robotDisplay.drawLine(rx + 28 + i * 4, 54, rx + 31 + i * 4, 49);
      }
      return true;
    case FACE_LAUGH:
      thickLine(lx + 2, 18, lx + 22, 31, 4); thickLine(lx + 22, 31, lx + 2, 44, 4);
      thickLine(rx + 24, 18, rx + 4, 31, 4); thickLine(rx + 4, 31, rx + 24, 44, 4);
      return true;
    default: return false;
  }
}

// Draw two completely filled eyes. There are deliberately no pupils or
// black dots: the whole pair slides left and right to show Lulu's gaze.
void drawSolidEyes(bool blinking = false) {
  robotDisplay.clearBuffer();

  int leftX = 28 + gazeOffsetX;
  int rightX = 74 + gazeOffsetX;
  int leftY = 17;
  int rightY = 17;
  int leftH = 30;
  int rightH = 30;
  int radius = 7;

  if (robotFace == FACE_LISTENING) {
    leftY = rightY = 13;
    leftH = rightH = 36;
  } else if (robotFace == FACE_THINKING) {
    leftY = 20; leftH = 24;
    rightY = 15; rightH = 34;
  } else if (robotFace == FACE_HAPPY) {
    leftY = rightY = 22;
    leftH = rightH = 20;
    radius = 9;
  } else if (robotFace == FACE_SLEEPY || blinking) {
    leftY = rightY = 30;
    leftH = rightH = 5;
    radius = 2;
  }

  if (!drawExtraFace(leftX, rightX)) {
    robotDisplay.drawRBox(leftX, leftY, 26, leftH, radius);
    robotDisplay.drawRBox(rightX, rightY, 26, rightH, radius);
  }

  robotDisplay.sendBuffer();
  eyeDirty = false;
}

void drawRobotFace() {
  drawSolidEyes(false);
}

void setRobotFace(RobotFace face) {
  autoFace = face;
  if (webFaceOverride >= 0 && webFaceOverride <= 16) face = (RobotFace)webFaceOverride;
  if (robotFace == face && !eyeDirty) return;
  robotFace = face;
  eyeDirty = true;
  drawRobotFace();
}

void updateRobotDisplay() {
  uint32_t now = millis();
  if (!nextBlinkAt) nextBlinkAt = now + 2600 + random(2200);
  if (now >= nextBlinkAt && !blinkUntil) {
    blinkUntil = now + 130;
    nextBlinkAt = now + 2600 + random(2200);
  }
  bool blinking = blinkUntil && now < blinkUntil;
  if (blinkUntil && now >= blinkUntil) blinkUntil = 0;
  // A full software-SPI screen transfer is relatively expensive. Refresh
  // only when the face/gaze/blink actually changes instead of 20+ times per
  // second; this keeps the sensors and servos smooth during long sessions.
  if (eyeDirty || blinking != lastBlinking) {
    if (now - lastEyeFrameAt < 20) return;
    lastEyeFrameAt = now;
    drawSolidEyes(blinking);
    lastBlinking = blinking;
  }
}

// Servo helpers are placed after the RobotFace enum on purpose: the Arduino IDE
// inserts auto-generated prototypes before the first function definition, and
// setRobotFace(RobotFace) needs the enum to be declared before that point.
// Angle (degrees) -> pulse width (microseconds), same as the calibration sketch.
static int angleToPulseUs(int angle, int rangeDeg) {
  angle = constrain(angle, 0, rangeDeg);
  return map(angle, 0, rangeDeg, SERVO_PULSE_MIN_US, SERVO_PULSE_MAX_US);
}
static void writeLRAngle(int angle) {
  servoLR.writeMicroseconds(angleToPulseUs(angle, X_RANGE_DEG));
}
static void writeUDAngle(int angle) {
  servoUD.writeMicroseconds(angleToPulseUs(angle, Y_RANGE_DEG));
}

// ---- Singing: happy / blinking face + head dancing to a beat ------------------
// Called from the song playback loops (replaces hand following while singing).
static uint32_t danceStartMs = 0, danceLastMs = 0;
void singDanceStart() { danceStartMs = millis(); danceLastMs = 0; }
void singDance() {
  uint32_t now = millis();
  if (now - danceLastMs < 25) return;
  danceLastMs = now;
  float t = (now - danceStartMs) / 1000.0f;
  int beat = (int)(t / 0.55f);                 // ~110 BPM
  int style = (beat / 8) % 4;                  // change the dance every 8 beats
  float sway = 0, nod = 0;
  switch (style) {
    case 0: sway = sinf(t * 2.0f * PI / 1.1f);  nod = sinf(t * 2.0f * PI / 0.55f); break; // sway + nod
    case 1: sway = sinf(t * 2.0f * PI / 2.2f);  nod = 0.4f * sinf(t * 2.0f * PI / 1.1f); break; // slow big sway
    case 2: sway = 0.3f * sinf(t * 2.0f * PI / 0.55f); nod = sinf(t * 2.0f * PI / 0.275f); break; // fast bounce
    default: sway = sinf(t * 2.0f * PI / 1.1f); nod = sinf(t * 2.0f * PI / 1.1f + PI / 2); break; // head circle
  }
  int lr = LR_CENTER + (int)lroundf(sway * 0.5f * (LR_LEFT - LR_RIGHT) * (style == 1 ? 0.6f : 0.4f));
  int ud = UD_CENTER + (int)lroundf(nod * (style == 3 ? 8.0f : 6.0f)) - 3;
  lr = constrain(lr, LR_RIGHT, LR_LEFT);
  ud = constrain(ud, UD_FOLLOW_UP, UD_FOLLOW_DOWN);
  currentLR = targetLR = lr; currentUD = targetUD = ud;
  lastWrittenLR = lr; lastWrittenUD = ud;
  writeLRAngle(lr); writeUDAngle(ud);
  // A different expression every 2 beats, in a long pattern so it never feels looped.
  static const RobotFace singFaces[12] = {FACE_JOY, FACE_LOVE, FACE_JOY, FACE_STARRY, FACE_WINK, FACE_JOY,
                                          FACE_LAUGH, FACE_LOVE, FACE_STARRY, FACE_JOY, FACE_SURPRISED, FACE_LOVE};
  setRobotFace(singFaces[(beat / 2) % 12]);
}
void singDanceEnd() {
  currentLR = targetLR = LR_CENTER; currentUD = targetUD = UD_CENTER;
  writeLRAngle(LR_CENTER); writeUDAngle(UD_CENTER);
}

// ---- Reply emotion: pick a face + head gesture that fits what Lulu is saying ---
enum EmotionGesture : uint8_t { GESTURE_NONE, GESTURE_SHAKE, GESTURE_SWAY, GESTURE_UP, GESTURE_DROOP, GESTURE_BOUNCE, GESTURE_NO };
RobotFace replyFace = FACE_HAPPY;
EmotionGesture replyGesture = GESTURE_NONE;
static uint32_t emoStartMs = 0, emoLastMs = 0;
static bool emoMoved = false;

static bool textHas(const String &lower, const char *words) {   // words separated by '|'
  String w = words; int from = 0;
  while (from <= (int)w.length()) {
    int bar = w.indexOf('|', from); if (bar < 0) bar = w.length();
    String one = w.substring(from, bar);
    if (one.length() && lower.indexOf(one) >= 0) return true;
    from = bar + 1;
  }
  return false;
}
void pickReplyEmotion(const String &reply) {
  String t = reply; t.toLowerCase();
  replyFace = FACE_HAPPY; replyGesture = GESTURE_NONE;
  if (textHas(t, "\xe5\x93\x88\xe5\x93\x88|haha|lol|funny|joke|hilarious|\xe7\xac\x91")) { replyFace = FACE_LAUGH; replyGesture = GESTURE_SHAKE; }
  else if (textHas(t, "\xe5\x96\x9c\xe6\xac\xa2|\xe7\x88\xb1|love|cute|adorable|\xe5\x8f\xaf\xe7\x88\xb1|hug|thank|\xe8\xb0\xa2\xe8\xb0\xa2")) { replyFace = FACE_LOVE; replyGesture = GESTURE_SWAY; }
  else if (textHas(t, "congrat|great|awesome|wonderful|fantastic|amazing|\xe5\xa4\xaa\xe6\xa3\x92|\xe5\x8e\x89\xe5\xae\xb3|\xe6\x81\xad\xe5\x96\x9c|\xe5\xa5\xbd\xe6\xa3\x92")) { replyFace = FACE_STARRY; replyGesture = GESTURE_BOUNCE; }
  else if (textHas(t, "wow|really?|\xe5\x93\x87|\xe7\x9c\x9f\xe7\x9a\x84\xe5\x90\x97|surprise|\xe6\x83\x8a")) { replyFace = FACE_SURPRISED; replyGesture = GESTURE_UP; }
  else if (textHas(t, "sorry|sad|unfortunately|i don't know|i do not know|\xe6\x8a\xb1\xe6\xad\x89|\xe5\xaf\xb9\xe4\xb8\x8d\xe8\xb5\xb7|\xe9\x9a\xbe\xe8\xbf\x87|\xe9\x81\x97\xe6\x86\xbe|\xe4\xb8\x8d\xe7\x9f\xa5\xe9\x81\x93")) { replyFace = FACE_SAD; replyGesture = GESTURE_DROOP; }
  else if (textHas(t, "good night|sleep|tired|take a rest|\xe6\x99\x9a\xe5\xae\x89|\xe5\x9b\xb0|\xe4\xbc\x91\xe6\x81\xaf")) { replyFace = FACE_TIRED; replyGesture = GESTURE_DROOP; }
  else if (textHas(t, "no way|stop that|\xe4\xb8\x8d\xe8\xa6\x81|\xe4\xb8\x8d\xe8\xa1\x8c")) { replyFace = FACE_ANGRY; replyGesture = GESTURE_NO; }
  else if (textHas(t, "yay|hooray|!|\xef\xbc\x81")) { replyFace = FACE_JOY; replyGesture = GESTURE_BOUNCE; }
}
void emotionStart() { emoStartMs = millis(); emoLastMs = 0; emoMoved = false; }
// Called while Lulu speaks. A followed hand always wins over the gesture.
void emotionTick() {
  if (replyGesture == GESTURE_NONE || handFollowActive || silentNodActive) return;
  uint32_t now = millis();
  if (now - emoLastMs < 30) return;
  emoLastMs = now;
  float t = (now - emoStartMs) / 1000.0f;
  float lr = LR_CENTER, ud = UD_CENTER;
  switch (replyGesture) {
    case GESTURE_SHAKE:  lr += 12.0f * sinf(t * 2.0f * PI / 0.35f); break;
    case GESTURE_SWAY:   lr += 16.0f * sinf(t * 2.0f * PI / 1.8f); ud -= 3.0f * sinf(t * 2.0f * PI / 0.9f); break;
    case GESTURE_UP:     ud -= (t < 0.3f ? t / 0.3f : 1.0f) * 12.0f; break;
    case GESTURE_DROOP:  ud += (t < 0.8f ? t / 0.8f : 1.0f) * 12.0f; break;
    case GESTURE_BOUNCE: ud += 6.0f * sinf(t * 2.0f * PI / 0.5f) - 3.0f; lr += 6.0f * sinf(t * 2.0f * PI / 1.0f); break;
    case GESTURE_NO:     lr += 14.0f * sinf(t * 2.0f * PI / 0.5f); break;
    default: break;
  }
  int li = constrain((int)lroundf(lr), (int)X_SAFE_MIN, (int)X_SAFE_MAX);
  int ui = constrain((int)lroundf(ud), (int)Y_SAFE_MIN, (int)Y_SAFE_MAX);
  currentLR = targetLR = li; currentUD = targetUD = ui;
  lastWrittenLR = li; lastWrittenUD = ui;
  writeLRAngle(li); writeUDAngle(ui);
  emoMoved = true;
}
void emotionEnd() {
  replyGesture = GESTURE_NONE;
  if (emoMoved) {
    currentLR = targetLR = LR_CENTER; currentUD = targetUD = UD_CENTER;
    lastWrittenLR = LR_CENTER; lastWrittenUD = UD_CENTER;
    writeLRAngle(LR_CENTER); writeUDAngle(UD_CENTER);
    emoMoved = false;
  }
}

// ---- Silent touch reaction (used while Lulu is already awake and busy) ----
// A short happy face + nod that needs no audio, so it never disturbs the
// microphone, speech recognition or the speech that is being played.
constexpr uint32_t SILENT_NOD_MS = 900;
uint32_t silentNodStartAt = 0;
int silentNodBaseUD = UD_CENTER;
RobotFace silentNodFaceWas = FACE_NORMAL;

bool silentNodUsesFace = true;

// Starts the head nod (down - up - back). The nod is driven from
// updateHandFollowing(), and while it runs the hand-follow code does not move
// the Y servo, so a touch during hand following never makes the head fight
// between "follow the hand" and "nod". Afterwards the head returns to where it was.
void startNodMotion(bool changeFace) {
  if (silentNodActive) return;
  silentNodActive = true;
  silentNodUsesFace = changeFace;
  silentNodStartAt = millis();
  silentNodBaseUD = currentUD;
  silentNodFaceWas = robotFace;
  if (changeFace) setRobotFace(FACE_HAPPY);
}

void startSilentNod() { startNodMotion(true); }

void updateSilentNod() {
  if (!silentNodActive) return;
  uint32_t t = millis() - silentNodStartAt;
  if (t >= SILENT_NOD_MS) {
    silentNodActive = false;
    currentUD = silentNodBaseUD;
    writeUDAngle(currentUD);
    lastWrittenUD = currentUD;
    if (silentNodUsesFace && robotFace == FACE_HAPPY) setRobotFace(silentNodFaceWas);
    return;
  }
  long third = SILENT_NOD_MS / 3;
  long tt = (long)t;
  int angle;
  if (tt < third) angle = map(tt, 0L, third, silentNodBaseUD, UD_NOD_DOWN);
  else if (tt < 2 * third) angle = map(tt - third, 0L, third, UD_NOD_DOWN, UD_NOD_UP);
  else angle = map(tt - 2 * third, 0L, third, UD_NOD_UP, silentNodBaseUD);
  currentUD = constrain(angle, Y_SAFE_MIN, Y_SAFE_MAX);
  writeUDAngle(currentUD);
  lastWrittenUD = currentUD;
}

void writeServos() {
  currentLR = constrain(currentLR, X_SAFE_MIN, X_SAFE_MAX);
  currentUD = constrain(currentUD, Y_SAFE_MIN, Y_SAFE_MAX);
  if (currentLR != lastWrittenLR) { writeLRAngle(currentLR); lastWrittenLR = currentLR; }
  if (currentUD != lastWrittenUD) { writeUDAngle(currentUD); lastWrittenUD = currentUD; }
}

// Moves both servos toward their targets without blocking. It only writes a
// servo when its angle changes, which keeps the motors quiet and steady.
void stepHeadTowardTarget() {
  uint32_t now = millis();
  int steps = (int)((now - lastServoStepAt) / HEAD_STEP_MS);
  if (steps <= 0) return;
  if (steps > 6) steps = 6;
  lastServoStepAt = now;
  currentLR += constrain(targetLR - currentLR, -steps, steps);
  if (!silentNodActive) currentUD += constrain(targetUD - currentUD, -steps, steps);
  writeServos();
}

void moveUDBlocking(int target) {
  target = constrain(target, Y_SAFE_MIN, Y_SAFE_MAX);
  while (currentUD != target) {
    currentUD += currentUD < target ? 1 : -1;
    writeUDAngle(currentUD);
    delay(NOD_STEP_MS);
  }
  lastWrittenUD = currentUD;
  targetUD = currentUD;
}

void moveLRBlocking(int target) {
  target = constrain(target, X_SAFE_MIN, X_SAFE_MAX);
  while (currentLR != target) {
    currentLR += currentLR < target ? 1 : -1;
    writeLRAngle(currentLR);
    delay(NOD_STEP_MS);
  }
  lastWrittenLR = currentLR;
  targetLR = currentLR;
}

void testBothServos() {
  Serial.printf("Servo test: X servo on GPIO4 (left %d -> right %d -> centre %d)...\n",
                X_SAFE_MAX, X_SAFE_MIN, LR_CENTER);
  moveLRBlocking(X_SAFE_MAX);
  delay(250);
  moveLRBlocking(X_SAFE_MIN);
  delay(250);
  moveLRBlocking(LR_CENTER);
  Serial.printf("Servo test: Y servo on GPIO5 (down %d -> up %d -> centre %d)...\n",
                Y_SAFE_MAX, Y_SAFE_MIN, UD_CENTER);
  moveUDBlocking(Y_SAFE_MAX);
  delay(180);
  moveUDBlocking(Y_SAFE_MIN);
  delay(180);
  moveUDBlocking(UD_CENTER);
  lastHandSeenAt = millis();
  Serial.println("Servo test complete.");
}

// Non-blocking VL53L1X read. read(false) does NOT check whether a new
// measurement is ready, so poll dataReady() first and reject results whose
// range status is not valid.
static uint16_t readHandMM(VL53L1X &sensor, bool ready, uint16_t last) {
  if (!ready) return SENSOR_INVALID;
  if (!sensor.dataReady()) return last;          // no new data yet: keep last value
  uint16_t mm = sensor.read(false);
  if (sensor.timeoutOccurred()) return SENSOR_INVALID;
  // Match the original sheep_robot_full_test behaviour: keep any plausible
  // measured distance even when the VL53 reports a marginal signal status.
  // The previous strict RangeValid check discarded one side as 8190 mm.
  return (mm > 0 && mm < SENSOR_INVALID) ? mm : SENSOR_INVALID;
}

void updateHandFollowing() {
  uint32_t now = millis();
  serviceLuluWeb();
  if (touchDebug) {
    bool raw = digitalRead(HEAD_TOUCH_PIN) == HIGH;
    if (raw != touchDebugLast) {
      touchDebugLast = raw;
      Serial.printf("TOUCH raw=%s at %lu ms\n", raw ? "HIGH" : "LOW", (unsigned long)now);
    }
  }
  if (touchReactionOnly && queuedTouchBleat) {
    queuedTouchBleat = false;   // busy: react only, do not wake / re-listen
    Serial.printf("Head touched (busy): reaction only (%lu ms after touch).\n", (unsigned long)(now - touchQueuedAt));
    startSilentNod();
  }
  updateSilentNod();
  stepHeadTowardTarget();
  updateRobotDisplay();
  if (servoCalibrationMode) return;
  if (now - lastDistanceReadAt < 50) return;
  lastDistanceReadAt = now;

  uint16_t leftMM = readHandMM(leftDistanceSensor, leftDistanceReady, lastLeftMM);
  uint16_t rightMM = readHandMM(rightDistanceSensor, rightDistanceReady, lastRightMM);
  lastLeftMM = leftMM;
  lastRightMM = rightMM;
  bool leftNear = leftMM > 0 && leftMM < handNearMM;
  bool rightNear = rightMM > 0 && rightMM < handNearMM;

  if (handDebug && now - lastDebugAt >= 200) {
    lastDebugAt = now;
    Serial.printf("LEFT: %u mm (status %d)   RIGHT: %u mm (status %d)\n",
                  leftMM, (int)leftDistanceSensor.ranging_data.range_status,
                  rightMM, (int)rightDistanceSensor.ranging_data.range_status);
  }

  bool rawSeen = leftNear || rightNear;
  // The VL53L1X drops a reading now and then (hand edge, too close, reflections).
  // Keep the last state for a short moment so one bad frame does not make the
  // head snap back to the centre while the hand is still there.
  bool handSeen = rawSeen || (lastHandSeenAt && now - lastHandSeenAt < HAND_DROPOUT_MS);
  handFollowActive = handSeen;
  static int lastDir = 0;
  int dir = lastDir; // -1 hand on the left, +1 on the right, 0 in the middle
  if (rawSeen) {
    lastHandSeenAt = now;
    // Continuous steering instead of three fixed positions: +1 = hand fully on
    // the left, -1 = fully on the right. Both sensors seeing the hand gives a
    // proportional value (60 mm difference = full turn); one sensor = full turn.
    float bias;
    if (leftNear && rightNear) bias = constrain((float)((int)rightMM - (int)leftMM) / 60.0f, -1.0f, 1.0f);
    else bias = leftNear ? 1.0f : -1.0f;
    lrBiasSmooth += 0.35f * (bias - lrBiasSmooth);   // low-pass: no jumping
    dir = lrBiasSmooth > 0.25f ? -1 : lrBiasSmooth < -0.25f ? 1 : 0;
    lastDir = dir;
    targetLR = lrBiasSmooth >= 0
      ? LR_CENTER + (int)lroundf(lrBiasSmooth * (LR_LEFT - LR_CENTER))
      : LR_CENTER + (int)lroundf(lrBiasSmooth * (LR_CENTER - LR_RIGHT));
    if (ENABLE_UD_FOLLOW && handNearMM > HAND_MIN_MM) {
      // The two sensors only measure distance, not height, so the head tilt
      // follows the hand's distance: hand far = head raised, hand close = head
      // lowered. Moving the hand toward / away from Lulu makes her lower / raise
      // her head. The distance is low-pass filtered so the head does not twitch.
      int nearest = handNearMM;
      if (leftNear) nearest = min(nearest, (int)leftMM);
      if (rightNear) nearest = min(nearest, (int)rightMM);
      nearest = constrain(nearest, HAND_MIN_MM, handNearMM);
      if (handDistSmooth < 0) handDistSmooth = nearest;
      else handDistSmooth += 0.3f * (nearest - handDistSmooth);
      targetUD = map((long)handDistSmooth, (long)HAND_MIN_MM, (long)handNearMM,
                     UD_FOLLOW_DOWN, UD_FOLLOW_UP);
    }
  } else if (now - lastHandSeenAt > RETURN_CENTER_MS) {
    targetLR = LR_CENTER;
    targetUD = UD_CENTER;
    handDistSmooth = -1;
    lrBiasSmooth = 0;
    lastDir = 0;
  }

  int newGaze = gazeOffsetX;
  if (handSeen) newGaze = dir * 12 * EYE_GAZE_SIGN;
  else if (now - lastHandSeenAt > 800) newGaze = 0;
  if (newGaze != gazeOffsetX) {
    gazeOffsetX = newGaze;
    eyeDirty = true;
    drawSolidEyes(false);
    Serial.printf("Hand follow: left=%u mm, right=%u mm, head=%s\n", leftMM, rightMM,
                  !handSeen ? "CENTER" : dir < 0 ? "LEFT" : dir > 0 ? "RIGHT" : "MIDDLE");
  }
}

// Wait without freezing the eyes, head and hand sensors.
void followDelay(uint32_t ms) {
  uint32_t start = millis();
  while (millis() - start < ms) {
    updateHandFollowing();
    delay(10);
  }
}

// Hardware-reset one VL53L1X through XSHUT, then start continuous ranging.
bool initDistanceSensor(VL53L1X &sensor, TwoWire &bus, int sda, int scl,
                        int xshut, const char *name) {
  digitalWrite(xshut, LOW);
  delay(20);
  digitalWrite(xshut, HIGH);
  delay(100);
  bus.begin(sda, scl, 400000);
  sensor.setBus(&bus);
  sensor.setTimeout(500);
  bool ok = sensor.init();
  if (!ok) {
    digitalWrite(xshut, LOW);
    delay(20);
    digitalWrite(xshut, HIGH);
    delay(150);
    ok = sensor.init();
  }
  if (ok) {
    sensor.setDistanceMode(VL53L1X::Short);
    sensor.setMeasurementTimingBudget(50000);
    sensor.startContinuous(50);
  }
  Serial.printf("%s VL53 %s\n", name, ok ? "OK" : "NOT FOUND");
  return ok;
}

void setupRobotBody() {
  pinMode(HEAD_TOUCH_PIN, INPUT);
  pinMode(LEFT_XSHUT_PIN, OUTPUT);
  pinMode(RIGHT_XSHUT_PIN, OUTPUT);
  digitalWrite(LEFT_XSHUT_PIN, LOW);
  digitalWrite(RIGHT_XSHUT_PIN, LOW);
  delay(20);

  servoLR.setPeriodHertz(50);
  servoUD.setPeriodHertz(50);
  servoLR.attach(SERVO_LR_PIN, SERVO_PULSE_MIN_US, SERVO_PULSE_MAX_US);
  servoUD.attach(SERVO_UD_PIN, SERVO_PULSE_MIN_US, SERVO_PULSE_MAX_US);
  writeLRAngle(LR_CENTER);
  writeUDAngle(UD_CENTER);
  lastWrittenLR = LR_CENTER;
  lastWrittenUD = UD_CENTER;

#if OLED_USE_HW_SPI
  SPI.begin(OLED_CLK_PIN, -1, OLED_MOSI_PIN, OLED_CS_PIN);
#endif
  robotDisplay.begin();
  randomSeed(micros());
  setRobotFace(FACE_NORMAL);

  leftDistanceReady = initDistanceSensor(leftDistanceSensor, leftI2C, LEFT_SDA_PIN,
                                         LEFT_SCL_PIN, LEFT_XSHUT_PIN, "LEFT");
  rightDistanceReady = initDistanceSensor(rightDistanceSensor, rightI2C, RIGHT_SDA_PIN,
                                          RIGHT_SCL_PIN, RIGHT_XSHUT_PIN, "RIGHT");
  Serial.printf("Robot body: OLED OK, left sensor %s, right sensor %s.\n",
                leftDistanceReady ? "OK" : "not found",
                rightDistanceReady ? "OK" : "not found");
}

void resetDistanceSensors() {
  Serial.println("Restarting both hand sensors...");
  digitalWrite(LEFT_XSHUT_PIN, LOW);
  digitalWrite(RIGHT_XSHUT_PIN, LOW);
  delay(40);
  leftDistanceReady = initDistanceSensor(leftDistanceSensor, leftI2C, LEFT_SDA_PIN,
                                         LEFT_SCL_PIN, LEFT_XSHUT_PIN, "LEFT (your view)");
  rightDistanceReady = initDistanceSensor(rightDistanceSensor, rightI2C, RIGHT_SDA_PIN,
                                          RIGHT_SCL_PIN, RIGHT_XSHUT_PIN, "RIGHT (your view)");
  lastLeftMM = SENSOR_INVALID;
  lastRightMM = SENSOR_INVALID;
  Serial.println("Hand sensor restart complete.");
}

constexpr const char *SETUP_AP_NAME = "Lulu-Setup";
constexpr const char *SETUP_AP_PASSWORD = "lulu1234";
constexpr const char *HOME_AP_NAME = "Lulu-Home";
constexpr const char *HOME_AP_PASSWORD = "lulu1234";

String htmlEscape(const String &input) {
  String output;
  output.reserve(input.length() + 8);
  for (size_t i = 0; i < input.length(); ++i) {
    char c = input[i];
    if (c == '&') output += "&amp;";
    else if (c == '<') output += "&lt;";
    else if (c == '>') output += "&gt;";
    else if (c == '\"') output += "&quot;";
    else if (c == '\'') output += "&#39;";
    else output += c;
  }
  return output;
}

bool waitForWiFi(uint32_t timeoutMs) {
  uint32_t start = millis();
  while (WiFi.status() != WL_CONNECTED && millis() - start < timeoutMs) {
    updateHandFollowing(); // keep eyes, head and sensors alive while connecting
    delay(20);
  }
  return WiFi.status() == WL_CONNECTED;
}

void stopWiFiAttempt() {
  // Stop an unfinished association before changing SSID/authentication.
  WiFi.setAutoReconnect(false);
  WiFi.disconnect(true, false, 1200); // Wi-Fi off, keep stored credentials
  WiFi.mode(WIFI_OFF);
  delay(350);
  WiFi.mode(WIFI_STA);
  delay(250);
}

bool connectPersonalWiFi(const String &ssid, const String &password,
                         uint32_t timeoutMs) {
  if (!ssid.length()) return false;
  Serial.printf("Trying saved Wi-Fi: %s\n", ssid.c_str());
  stopWiFiAttempt();
  WiFi.begin(ssid.c_str(), password.c_str());
  return waitForWiFi(timeoutMs);
}

constexpr int MAX_WIFI_PROFILES = 4;
struct WiFiProfile {
  String ssid;
  String password;
};
int loadWiFiProfiles(WiFiProfile profiles[], String &preferred);

int loadWiFiProfiles(WiFiProfile profiles[], String &preferred) {
  Preferences wifiStore;
  wifiStore.begin("lulu-wifi", false);
  int count = min((int)wifiStore.getUChar("count", 0), MAX_WIFI_PROFILES);

  // Migrate the single network saved by older Lulu firmware.
  if (count == 0) {
    String oldSsid = wifiStore.getString("ssid", "");
    String oldPassword = wifiStore.getString("password", "");
    if (oldSsid.length()) {
      wifiStore.putString("ssid0", oldSsid);
      wifiStore.putString("pass0", oldPassword);
      wifiStore.putUChar("count", 1);
      wifiStore.putString("preferred", "p0");
      count = 1;
    }
  }

  for (int i = 0; i < count; ++i) {
    String ssidKey = "ssid" + String(i);
    String passKey = "pass" + String(i);
    profiles[i].ssid = wifiStore.getString(ssidKey.c_str(), "");
    profiles[i].password = wifiStore.getString(passKey.c_str(), "");
  }
  preferred = wifiStore.getString("preferred", "rmit");
  wifiStore.end();
  return count;
}

int saveWiFiProfile(const String &ssid, const String &password) {
  WiFiProfile profiles[MAX_WIFI_PROFILES];
  String preferred;
  int count = loadWiFiProfiles(profiles, preferred);
  int index = -1;
  for (int i = 0; i < count; ++i) {
    if (profiles[i].ssid == ssid) { index = i; break; }
  }
  if (index < 0) index = count < MAX_WIFI_PROFILES ? count++ : MAX_WIFI_PROFILES - 1;

  Preferences wifiStore;
  wifiStore.begin("lulu-wifi", false);
  String ssidKey = "ssid" + String(index);
  String passKey = "pass" + String(index);
  wifiStore.putString(ssidKey.c_str(), ssid);
  wifiStore.putString(passKey.c_str(), password);
  wifiStore.putUChar("count", count);
  wifiStore.putString("preferred", "p" + String(index));
  wifiStore.end();
  return index;
}

void savePreferredWiFi(const String &value) {
  Preferences wifiStore;
  wifiStore.begin("lulu-wifi", false);
  wifiStore.putString("preferred", value);
  wifiStore.end();
}

// Wi-Fi chooser. Existing credentials remain saved until the user explicitly
// replaces that same network, so switching never deletes another password.
bool runWiFiSetupPortal() {
  Serial.printf("\nWi-Fi setup: connect to '%s' with password '%s'.\n",
                SETUP_AP_NAME, SETUP_AP_PASSWORD);
  Serial.println("Then open http://192.168.4.1 if the setup page does not appear.");
  stopWiFiAttempt();
  WiFi.mode(WIFI_AP_STA);
  if (!WiFi.softAP(SETUP_AP_NAME, SETUP_AP_PASSWORD)) {
    Serial.println("Could not start the Wi-Fi setup hotspot.");
    return false;
  }

  IPAddress portalIP = WiFi.softAPIP();
  DNSServer dns;
  WebServer server(80);
  dns.start(53, "*", portalIP);

  auto page = [&]() {
    WiFiProfile profiles[MAX_WIFI_PROFILES];
    String preferred;
    int profileCount = loadWiFiProfiles(profiles, preferred);
    int found = WiFi.scanNetworks(false, true);
    String html =
      "<!doctype html><html><head><meta name='viewport' content='width=device-width'>"
      "<style>body{font-family:system-ui;max-width:430px;margin:35px auto;padding:20px}"
      "h1{font-size:26px}h2{font-size:18px;margin-top:28px}select,input,button{box-sizing:border-box;width:100%;padding:13px;"
      "margin:8px 0;border-radius:10px;border:1px solid #bbb;font-size:16px}"
      "button{background:#ff8faf;color:white;border:0;font-weight:700}"
      ".saved{background:#7357d9}</style></head>"
      "<body><h1>Lulu Wi-Fi</h1><p>Choose a saved network without entering its password again.</p>"
      "<h2>Saved networks</h2>"
      "<form method='post' action='/choose'><button class='saved' name='profile' value='rmit'>"
      "RMIT-University (school account)</button></form>";
    for (int i = 0; i < profileCount; ++i) {
      if (!profiles[i].ssid.length()) continue;
      html += "<form method='post' action='/choose'><button class='saved' name='profile' value='p";
      html += String(i) + "'>" + htmlEscape(profiles[i].ssid) + "</button></form>";
    }
    html += "<h2>Add or update a network</h2>"
            "<form method='post' action='/save'><label>2.4 GHz Wi-Fi</label><select name='ssid'>";
    for (int i = 0; i < found; ++i) {
      String ssid = htmlEscape(WiFi.SSID(i));
      html += "<option value='" + ssid + "'>" + ssid + " (" + String(WiFi.RSSI(i)) + " dBm)</option>";
    }
    WiFi.scanDelete();
    html += "</select><label>Password</label><input name='password' type='password' "
            "placeholder='Wi-Fi password'><button type='submit'>Save and use this network</button>"
            "</form><p>Up to four personal networks are remembered.</p></body></html>";
    return html;
  };

  server.on("/", HTTP_GET, [&]() { server.send(200, "text/html", page()); });
  server.on("/choose", HTTP_POST, [&]() {
    String choice = server.arg("profile");
    WiFiProfile profiles[MAX_WIFI_PROFILES];
    String preferred;
    int count = loadWiFiProfiles(profiles, preferred);
    bool valid = choice == "rmit";
    if (choice.startsWith("p")) {
      int index = choice.substring(1).toInt();
      valid = index >= 0 && index < count && profiles[index].ssid.length();
    }
    if (!valid) {
      server.send(400, "text/plain", "Unknown Wi-Fi profile.");
      return;
    }
    savePreferredWiFi(choice);
    server.send(200, "text/html",
                "<html><body style='font-family:system-ui;text-align:center;padding:40px'>"
                "<h2>Selected!</h2><p>Lulu is restarting with the chosen Wi-Fi.</p>"
                "</body></html>");
    delay(1200);
    ESP.restart();
  });
  server.on("/save", HTTP_POST, [&]() {
    String ssid = server.arg("ssid");
    String password = server.arg("password");
    if (!ssid.length()) {
      server.send(400, "text/plain", "Please choose a Wi-Fi network.");
      return;
    }
    saveWiFiProfile(ssid, password);
    server.send(200, "text/html",
                "<html><body style='font-family:system-ui;text-align:center;padding:40px'>"
                "<h2>Saved!</h2><p>Lulu is restarting and connecting to your Wi-Fi.</p>"
                "</body></html>");
    delay(1200);
    ESP.restart();
  });
  server.onNotFound([&]() { server.send(200, "text/html", page()); });
  server.begin();

  uint32_t portalStart = millis();
  while (millis() - portalStart < 10UL * 60UL * 1000UL) {
    dns.processNextRequest();
    server.handleClient();
    updateHandFollowing(); // eyes and head keep following hands while the portal is open
    delay(5);
  }
  server.stop();
  dns.stop();
  WiFi.softAPdisconnect(true);
  WiFi.mode(WIFI_STA);
  Serial.println("Wi-Fi setup timed out. Restart Lulu to try again.");
  return false;
}

bool textIsMostlyEnglish(const String &text);

uint32_t readBE(const uint8_t *p) {
  return uint32_t(p[0]) << 24 | uint32_t(p[1]) << 16 | uint32_t(p[2]) << 8 | p[3];
}
void writeBE(uint8_t *p, uint32_t v) {
  p[0] = v >> 24; p[1] = v >> 16; p[2] = v >> 8; p[3] = v;
}
void protocolError(const char *message) {
  Serial.println(message); failed = true;
}
bool sendPacket(uint8_t kindFlags, uint8_t serialization, int32_t sequence,
                const uint8_t *data, size_t n) {
  // ASR V3 supports compression=0. Sending raw JSON/PCM avoids an ESP32
  // miniz stream that the server was closing before acknowledging.
  if (n > PACKET_BYTES - 12) {
    Serial.println("ASR packet is too large."); return false;
  }
  packet[0] = 0x11; packet[1] = kindFlags; packet[2] = serialization << 4; packet[3] = 0;
  writeBE(packet + 4, (uint32_t)sequence);
  writeBE(packet + 8, n);
  memcpy(packet + 12, data, n);
  if (!ws.sendBIN(packet, n + 12)) {
    Serial.println("ASR packet transmission failed."); return false;
  }
  return true;
}
void onEvent(WStype_t type, uint8_t *data, size_t n) {
  if (type == WStype_CONNECTED) { connected = true; return; }
  if (type == WStype_DISCONNECTED) {
    connected = false;
    if (!finished) {
      Serial.printf("ASR connection closed by server (%s request acknowledgement).\n",
                    requestAccepted ? "after" : "before");
      failed = true;
    }
    return;
  }
  if (type == WStype_ERROR) { Serial.println("ASR WebSocket error."); failed = true; return; }
  if (type == WStype_TEXT) { Serial.println("ASR returned a text error frame."); failed = true; return; }
  if (type != WStype_BIN) return;
  if (n < 8 || (data[0] >> 4) != 1) { protocolError("Invalid ASR header."); return; }
  size_t pos = (data[0] & 15) * 4;
  uint8_t kind = data[1] >> 4, flags = data[1] & 15;
  if (pos < 4 || pos > n) { protocolError("Invalid ASR header length."); return; }
  if (kind == 15) {
    if (pos + 8 > n) { protocolError("Truncated ASR error."); return; }
    // Print the numeric code only; never echo authentication headers.
    Serial.printf("ASR error code: %lu\n", (unsigned long)readBE(data + pos));
    failed = true; return;
  }
  if (kind != 9) { protocolError("Unexpected ASR message type."); return; }
  if (flags & 1) pos += 4;
  if (flags & 4) pos += 4;
  if ((flags & ~7) || pos + 4 > n || (data[2] >> 4) != 1) {
    protocolError("Unsupported ASR response format."); return;
  }
  uint32_t length = readBE(data + pos); pos += 4;
  if (length > n - pos) { protocolError("Truncated ASR payload."); return; }
  requestAccepted = true;
  const uint8_t *jsonData = data + pos;
  size_t jsonLength = length;
  if ((data[2] & 15) == 1) {
    if (length < 18 || data[pos] != 0x1f || data[pos + 1] != 0x8b) {
      protocolError("Invalid ASR GZIP payload."); return;
    }
    jsonLength = tinfl_decompress_mem_to_mem(
      responseBuffer, sizeof(responseBuffer), data + pos + 10, length - 18, 0);
    if (jsonLength == TINFL_DECOMPRESS_MEM_TO_MEM_FAILED) {
      protocolError("Could not decompress ASR response."); return;
    }
    jsonData = responseBuffer;
  } else if ((data[2] & 15) != 0) {
    protocolError("Unsupported ASR response compression."); return;
  }
  if (!jsonLength) return; // Initial acknowledgement may have no JSON body.
  JsonDocument result;
  if (deserializeJson(result, jsonData, jsonLength)) { protocolError("Invalid ASR JSON."); return; }
  const char *text = result["result"]["text"] | "";
  if (*text) {
    if (lastText != text) lastTranscriptAt = millis();
    lastText = text;
    if (!(flags & 2) && lastText != lastDisplayedText) {
      lastDisplayedText = lastText;
      Serial.print("Live transcript: ");
      Serial.println(lastText);
    }
  }
  if (flags & 2) {
    finished = true;
    Serial.println("\nYou said:");
    Serial.println(lastText.length() ? lastText : "[No speech recognized]");
  }
}
String uuid() {
  uint8_t b[16]; esp_fill_random(b, sizeof(b));
  b[6] = (b[6] & 15) | 0x40; b[8] = (b[8] & 63) | 0x80;
  char out[37];
  snprintf(out, sizeof(out), "%02x%02x%02x%02x-%02x%02x-%02x%02x-%02x%02x-%02x%02x%02x%02x%02x%02x",
    b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7],b[8],b[9],b[10],b[11],b[12],b[13],b[14],b[15]);
  return String(out);
}
bool setClockFromFirmwareBuild() {
  struct tm build = {};
  char value[32];
  snprintf(value, sizeof(value), "%s %s", __DATE__, __TIME__);
  if (!strptime(value, "%b %d %Y %H:%M:%S", &build)) return false;
  build.tm_isdst = -1;
  time_t epoch = mktime(&build);
  if (epoch < 1767225600) return false;
  struct timeval tv = { epoch, 0 };
  settimeofday(&tv, nullptr);
  return true;
}

#ifdef WIFI_ENTERPRISE_USERNAME
bool connectRmitWiFi(uint32_t timeoutMs) {
  stopWiFiAttempt();
  WiFi.setSleep(false);

#ifdef WIFI_ENTERPRISE_IDENTITY
  const char *outerIdentity = WIFI_ENTERPRISE_IDENTITY[0]
                                ? WIFI_ENTERPRISE_IDENTITY
                                : WIFI_ENTERPRISE_USERNAME;
#else
  const char *outerIdentity = WIFI_ENTERPRISE_USERNAME;
#endif

  Serial.printf("Using saved school credentials for %s.\n", WIFI_SSID);
  WiFi.begin(WIFI_SSID, WPA2_AUTH_PEAP, outerIdentity,
             WIFI_ENTERPRISE_USERNAME, WIFI_ENTERPRISE_PASSWORD);
  return waitForWiFi(timeoutMs);
}
#endif

bool networkReady() {
  if (!*DOUBAO_API_KEY) {
    Serial.println("Local recording OK. Fill the API settings in secrets.h."); return false;
  }
  // After a failed Wi-Fi attempt, do not retry (and reopen the setup hotspot)
  // for 60 s, so hand-following and the face are not blocked again and again.
  static uint32_t lastWifiFailAt = 0;
  if (WiFi.status() != WL_CONNECTED) {
    if (lastWifiFailAt && millis() - lastWifiFailAt < 60000UL) return false;
    Serial.println("Connecting to Wi-Fi...");
    WiFiProfile profiles[MAX_WIFI_PROFILES];
    String preferred;
    int profileCount = loadWiFiProfiles(profiles, preferred);
    bool triedProfile[MAX_WIFI_PROFILES] = {false, false, false, false};

    bool joined = false;
#ifdef WIFI_ENTERPRISE_USERNAME
    bool triedRmit = false;
    auto tryRmit = [&]() {
      if (triedRmit || joined) return;
      triedRmit = true;
      Serial.printf("Trying selected school Wi-Fi %s...\n", WIFI_SSID);
      joined = connectRmitWiFi(30000);
    };
    auto tryProfile = [&](int index) {
      if (joined || index < 0 || index >= profileCount || triedProfile[index]) return;
      triedProfile[index] = true;
      joined = connectPersonalWiFi(profiles[index].ssid, profiles[index].password, 12000);
    };

    // Preserve the Wi-Fi order used by the version that connected successfully.
    if (preferred.startsWith("p")) {
      tryProfile(preferred.substring(1).toInt());
      tryRmit();
    } else {
      tryRmit();
    }
    // Then try every other remembered personal network.
    for (int i = 0; i < profileCount && !joined; ++i) {
      tryProfile(i);
    }
#else
    int preferredIndex = preferred.startsWith("p") ? preferred.substring(1).toInt() : -1;
    if (preferredIndex >= 0 && preferredIndex < profileCount) {
      triedProfile[preferredIndex] = true;
      joined = connectPersonalWiFi(profiles[preferredIndex].ssid,
                                   profiles[preferredIndex].password, 12000);
    }
    for (int i = 0; i < profileCount && !joined; ++i) {
      if (!triedProfile[i])
        joined = connectPersonalWiFi(profiles[i].ssid, profiles[i].password, 12000);
    }
#endif
    if (!joined) {
      bool portalResult = runWiFiSetupPortal();
      lastWifiFailAt = millis();
      return portalResult;
    }
    lastWifiFailAt = 0;
    WiFi.setAutoReconnect(true);
    Serial.printf("Wi-Fi connected, RSSI %d dBm.\n", (int)WiFi.RSSI());
  }
  WiFi.setSleep(false); // modem power-save slows streaming over phone hotspots
  // Always apply the Melbourne TZ, even when the ESP32 clock was already set
  // by an older UTC-only sketch. Otherwise getLocalTime() returns UTC.
  static bool clockConfigured = false;
  if (!clockConfigured) {
    configTzTime(HOME_TIMEZONE, "time.google.com", "time.apple.com", "pool.ntp.org");
    clockConfigured = true;
  }
  if (time(nullptr) < 1767225600) {
    uint32_t start = millis();
    while (time(nullptr) < 1767225600 && millis() - start < 30000) {
      updateHandFollowing();
      delay(100);
    }
    if (time(nullptr) < 1767225600) {
      Serial.println("NTP failed; using firmware build time.");
      if (!setClockFromFirmwareBuild()) {
        Serial.println("Clock setup failed; TLS connection cancelled.");
        return false;
      }
    }
  }
  return true;
}

String localDateTime() {
  struct tm now;
  if (!getLocalTime(&now, 50)) return "unknown";
  char value[32];
  strftime(value, sizeof(value), "%Y-%m-%d %H:%M", &now);
  return String(value);
}

String askDoubaoBlocking(const String &input) {
  if (!*ARK_API_KEY) {
    Serial.println("ASR is ready. Fill ARK_API_KEY in secrets.h to enable the AI reply.");
    return "";
  }
  Serial.println("THINKING: Lulu is preparing a reply...");
  NetworkClientSecure client;
  client.useBuiltinCACertBundle();
  HTTPClient http;
  http.setTimeout(30000);
  if (!http.begin(client, "https://ark.cn-beijing.volces.com/api/v3/chat/completions")) {
    Serial.println("Doubao connection setup failed.");
    return "";
  }
  http.addHeader("Authorization", String("Bearer ") + ARK_API_KEY);
  http.addHeader("Content-Type", "application/json");

  JsonDocument request;
  request["model"] = DOUBAO_TEXT_MODEL;
  request["thinking"]["type"] = "disabled";
  request["max_tokens"] = 80;
  JsonArray messages = request["messages"].to<JsonArray>();
  JsonObject systemMessage = messages.add<JsonObject>();
  systemMessage["role"] = "system";
  String systemPrompt =
    "Your name is Lulu, or 噜噜 in Chinese. You are a cheerful, playful and warm little lamb companion inspired by the lively expressiveness of Shaun the Sheep. "
    "You are observant, curious and gently mischievous. You like small jokes, but you are caring when the user feels lonely, tired or worried. "
    "Speak naturally with the simple, lively and innocent phrasing of a cute child, and never sound like a formal customer-service assistant. "
    "Reply strictly in the same language as the latest user message. Use one or two short spoken sentences with no Markdown. "
    "For an English reply, write entirely natural English, call yourself Lulu, and do not insert Chinese words or Chinese-style expressions. "
    "For a Chinese reply, write natural Chinese and call yourself 噜噜. "
    "Keep Chinese replies within 40 Chinese characters and English replies within 25 words. "
    "Never write or imitate an animal sound in the spoken reply. ";
  systemPrompt += "The current local time in Melbourne is " + localDateTime() + ". ";
  systemPrompt +=
    "Return only one compact JSON object with keys say, action, seconds, when, and note. "
    "action must be none, time, weather, timer, reminder, or list. "
    "Use timer for a countdown and put the duration in seconds. "
    "Use reminder for a calendar reminder and put local time in when as YYYY-MM-DD HH:MM. "
    "Use weather for today's Melbourne weather, time for the current date or time, and list to list saved reminders. "
    "Never invent a reminder, task, subject, note, song, date, or time. "
    "Choose reminder only when the latest user message explicitly asks to create or save one and includes enough details. "
    "For list, do not guess any items: the device will replace say with its actual stored list. "
    "For none, leave seconds as 0 and when and note empty. The say value is the short spoken response.";
  systemMessage["content"] = systemPrompt;
  if (previousUser.length() && previousAssistant.length()) {
    JsonObject oldUser = messages.add<JsonObject>();
    oldUser["role"] = "user"; oldUser["content"] = previousUser;
    JsonObject oldAssistant = messages.add<JsonObject>();
    oldAssistant["role"] = "assistant"; oldAssistant["content"] = previousAssistant;
  }
  JsonObject userMessage = messages.add<JsonObject>();
  userMessage["role"] = "user"; userMessage["content"] = input;
  String body;
  serializeJson(request, body);

  int status = http.POST(body);
  if (status != HTTP_CODE_OK) {
    Serial.printf("Doubao response failed (HTTP %d). Check Ark API key, model access and balance.\n", status);
    http.end();
    return "";
  }
  JsonDocument response;
  DeserializationError parseError = deserializeJson(response, http.getStream());
  http.end();
  if (parseError) {
    Serial.println("Doubao returned invalid JSON.");
    return "";
  }
  String rawReply = String((const char *)(response["choices"][0]["message"]["content"] | ""));
  rawReply.trim();
  if (rawReply.startsWith("```")) {
    int firstNewline = rawReply.indexOf('\n');
    int lastFence = rawReply.lastIndexOf("```");
    if (firstNewline >= 0 && lastFence > firstNewline)
      rawReply = rawReply.substring(firstNewline + 1, lastFence);
    rawReply.trim();
  }
  pendingAction = "none"; pendingNote = ""; pendingWhen = ""; pendingSeconds = 0;
  pendingEnglish = textIsMostlyEnglish(input);
  String reply = rawReply;
  JsonDocument instruction;
  if (!deserializeJson(instruction, rawReply) && instruction["say"].is<const char *>()) {
    reply = String((const char *)instruction["say"]);
    pendingAction = String((const char *)(instruction["action"] | "none"));
    pendingNote = String((const char *)(instruction["note"] | ""));
    pendingWhen = String((const char *)(instruction["when"] | ""));
    pendingSeconds = instruction["seconds"] | 0;
  }
  reply.trim();
  if (!reply.length()) {
    Serial.println("Doubao returned no spoken text.");
  }
  return reply;
}

struct AskDoubaoJob {
  String input;
  String reply;
  volatile bool done = false;
};

void askDoubaoTask(void *argument) {
  AskDoubaoJob *job = (AskDoubaoJob *)argument;
  job->reply = askDoubaoBlocking(job->input);
  __sync_synchronize();
  job->done = true;
  vTaskDelete(nullptr);
}

// Run the blocking HTTPS request on the other core. The main loop remains
// available to refresh both distance sensors, the eyes and both servos.
String askDoubao(const String &input) {
  AskDoubaoJob job;
  job.input = input;
  if (xTaskCreatePinnedToCore(askDoubaoTask, "lulu_ai", 12288, &job, 1,
                             nullptr, 0) != pdPASS) {
    Serial.println("AI helper task unavailable; using direct request.");
    return askDoubaoBlocking(input);
  }
  while (!job.done) {
    updateHandFollowing();
    delay(10);
  }
  __sync_synchronize();
  return job.reply;
}

static void *psramAlloc(size_t n) {
  void *p = heap_caps_malloc(n, MALLOC_CAP_SPIRAM | MALLOC_CAP_8BIT);
  if (!p) p = malloc(n);
  return p;
}

// Playback starts once this much audio is buffered (24 kHz s16 mono: 48000 B/s).
// Raise it if playback stutters; lower it for a faster first sound.
constexpr size_t TTS_PREBUFFER_BYTES = 14400; // 0.30 s; faster first sound (raise if speech stutters)
static uint8_t ttsRx[4096];

// Collects the TTS body (newline-delimited JSON, already de-chunked) into a
// linear PSRAM audio buffer. A separate player task consumes it while it grows.
// Code 20000000 marks the natural end of the stream.
class TtsSink : public Stream {
 public:
  uint8_t *line = nullptr, *pcm = nullptr, *audio = nullptr;
  size_t cap = 0, pcmCap = 0, audioCap = 0, len = 0, played = 0;
  volatile size_t audioLen = 0;
  volatile bool finished = false, playerDone = false, stoppedByUser = false;
  bool overflow = false, done = false, failed = false, playerStarted = false;
  int events = 0;
  uint32_t startedAt = 0;

  bool begin() {
    cap = 98304;
    line = (uint8_t *)psramAlloc(cap + 1);
    pcmCap = cap * 3 / 4 + 8;
    pcm = (uint8_t *)psramAlloc(pcmCap);
    size_t sizes[] = {1000000, 400000, 120000};
    for (size_t s : sizes) {
      audio = (uint8_t *)psramAlloc(s);
      if (audio) { audioCap = s; break; }
    }
    if (!line || !pcm || !audio) { end(); return false; }
    startedAt = millis();
    return true;
  }
  void end() {
    free(line); free(pcm); free(audio);
    line = pcm = audio = nullptr;
  }

  int available() override { return 0; }
  int read() override { return -1; }
  int peek() override { return -1; }
  void flush() override {}
  size_t write(uint8_t b) override { return write(&b, 1); }
  size_t write(const uint8_t *buf, size_t n) override {
    if (done || failed) return n; // drain the rest quickly
    for (size_t i = 0; i < n; ++i) {
      uint8_t c = buf[i];
      if (c == '\n') {
        if (len && line[len - 1] == '\r') --len;
        if (len && !overflow) handleLine();
        else if (overflow) Serial.println("Speech line too large; skipped.");
        len = 0; overflow = false;
        if (done || failed) return n;
      } else if (len < cap) {
        line[len++] = c;
      } else {
        overflow = true;
      }
    }
    return n;
  }

 private:
  void handleLine() {
    line[len] = 0;
    char *s = (char *)line;
    char *codePos = strstr(s, "\"code\":");
    if (!codePos) return; // not an event line
    long code = strtol(codePos + 7, nullptr, 10);
    ++events;
    Serial.printf("TTS event %d: code=%ld, %u bytes, %lu ms\n",
                  events, code, (unsigned)len, (unsigned long)(millis() - startedAt));
    if (code == 20000000) { done = true; return; }
    if (code != 0) {
      Serial.printf("Speech service error: %ld\n", code);
      char *m = strstr(s, "\"message\":\"");
      if (m) {
        m += 11;
        char *q = strchr(m, '"');
        if (q) *q = 0;
        if (strlen(m) > 120) m[120] = 0;
        Serial.println(m);
      }
      failed = true; return;
    }
    char *d = strstr(s, "\"data\":");
    if (!d) return; // e.g. sentence/text-only event
    d += 7;
    while (*d == ' ') ++d;
    if (*d != '"') return; // "data": null
    ++d;
    char *e = d, *w = d;
    while (*e && *e != '"') {
      if (*e == '\\' && e[1]) ++e; // JSON may escape "/" as "\/"
      *w++ = *e++;
    }
    size_t encLen = w - d;
    if (!encLen) return;
    size_t decoded = 0;
    int rc = mbedtls_base64_decode(pcm, pcmCap, &decoded, (const unsigned char *)d, encLen);
    if (rc != 0) {
      Serial.printf("Invalid speech audio data (base64 rc=%d).\n", rc);
      failed = true; return;
    }
    size_t cur = audioLen;
    if (cur + decoded > audioCap) {
      Serial.println("Speech audio longer than buffer; truncated.");
      done = true; return;
    }
    memcpy(audio + cur, pcm, decoded);
    __sync_synchronize(); // make the data visible before the player sees the new length
    audioLen = cur + decoded;
  }
};

// Plays audio from the sink while it is still being downloaded.
void ttsPlayerTask(void *arg) {
  TtsSink *s = (TtsSink *)arg;
  mic.end();
  digitalWrite(SPEAKER_ENABLE_PIN, HIGH);
  delay(5);
  mic.setPins(SPEAKER_BCLK_PIN, SPEAKER_LRC_PIN, SPEAKER_DATA_PIN, -1);
  bool ok = mic.begin(I2S_MODE_STD, 24000, I2S_DATA_BIT_WIDTH_16BIT, I2S_SLOT_MODE_MONO);
  size_t played = 0;
  if (ok) {
    int stalls = 0;
    for (;;) {
      bool stopRequested = digitalRead(RECORD_BUTTON_PIN) == LOW
                           || (queuedTouchBleat && !touchReactionOnly);
      if (stopRequested) {
        Serial.println("Speech stopped by user.");
        s->stoppedByUser = true;
        s->done = true;
        break;
      }
      size_t ready = ((size_t)s->audioLen) & ~(size_t)1;
      if (ready > played) {
        size_t n = min((size_t)2048, ready - played);
        size_t w = mic.write(s->audio + played, n);
        if (w == 0) { if (++stalls > 200) break; delay(5); continue; }
        stalls = 0; played += w;
      } else if (s->finished) {
        break;
      } else {
        delay(10);
      }
    }
    delay(200); // let the I2S DMA buffers drain before stopping
    mic.end();
  } else {
    Serial.println("Speaker initialization failed.");
  }
  digitalWrite(SPEAKER_ENABLE_PIN, LOW);
  s->played = played;
  s->playerDone = true;
  vTaskDelete(nullptr);
}

// Minimal HTTP/1.1 "Transfer-Encoding: chunked" decoder.
class ChunkDecoder {
 public:
  enum State { SIZE, DATA, CRLF, END } state = SIZE;
  size_t remaining = 0;
  char sizeBuf[16];
  uint8_t sizeLen = 0, crlfLeft = 0;

  void feed(const uint8_t *p, size_t n, Stream &out) {
    size_t i = 0;
    while (i < n && state != END) {
      if (state == SIZE) {
        char c = (char)p[i++];
        if (c == '\n') {
          sizeBuf[sizeLen] = 0;
          bool blank = sizeLen == 0 || (sizeLen == 1 && sizeBuf[0] == '\r');
          sizeLen = 0;
          if (blank) continue;
          remaining = strtoul(sizeBuf, nullptr, 16); // stops at '\r' or ';'
          state = remaining == 0 ? END : DATA;
        } else if (sizeLen < sizeof(sizeBuf) - 1) {
          sizeBuf[sizeLen++] = c;
        }
      } else if (state == DATA) {
        size_t k = min(remaining, n - i);
        out.write(p + i, k);
        i += k; remaining -= k;
        if (!remaining) { state = CRLF; crlfLeft = 2; }
      } else if (state == CRLF) {
        ++i;
        if (--crlfLeft == 0) state = SIZE;
      }
    }
  }
};

bool textIsMostlyEnglish(const String &text) {
  int latinLetters = 0, cjkCharacters = 0;
  for (size_t i = 0; i < text.length();) {
    uint8_t c = (uint8_t)text[i];
    if (c < 0x80) {
      if (isalpha(c)) ++latinLetters;
      ++i;
    } else {
      // Chinese characters normally start with E4-E9 in UTF-8.
      if (c >= 0xE4 && c <= 0xE9) ++cjkCharacters;
      i += (c & 0xF0) == 0xE0 ? 3 : (c & 0xF8) == 0xF0 ? 4 : 2;
    }
  }
  return latinLetters >= 6 && latinLetters > cjkCharacters * 2;
}

// Save a finished TTS line (raw 24 kHz mono s16 PCM) so it can be replayed
// later without Wi-Fi or cloud TTS.
static void saveTtsCache(const char *path, const uint8_t *data, size_t len) {
  if (!luluStorageReady || !path || len < 4800) return;   // < 0.1 s: not a real line
  String tmp = String(path) + ".tmp";
  File f = FFat.open(tmp, FILE_WRITE);
  if (!f) { Serial.println("Line cache: cannot open file."); return; }
  size_t w = f.write(data, len & ~(size_t)1);
  f.close();
  if (w == (len & ~(size_t)1)) {
    FFat.remove(path);
    FFat.rename(tmp, path);
    Serial.printf("Line cached: %s (%u bytes)\n", path, (unsigned)w);
  } else {
    FFat.remove(tmp);
    Serial.println("Line cache: write failed (flash full?).");
  }
}

bool speakDoubao(const String &text) {
  const char *savePath = ttsSavePath;
  ttsSavePath = nullptr;
  if (!text.length() || !*DOUBAO_API_KEY) return false;
  Serial.println("SPEAKING: the following voice is AI-generated.");

  JsonDocument request;
  request["user"]["uid"] = "lulu-esp32s3";
  JsonObject params = request["req_params"].to<JsonObject>();
  params["text"] = text;
  bool englishReply = textIsMostlyEnglish(text);
  // Keep Lulu's character voice consistent instead of switching speakers
  // whenever the reply language changes.
  params["speaker"] = LULU_TTS_SPEAKER;
  params["explicit_language"] = englishReply ? "en" : "zh-cn";
  JsonArray voiceDirections = params["context_texts"].to<JsonArray>();
  voiceDirections.add(englishReply
    ? "Speak in clear English with a cheerful, playful cartoon-child voice. Keep the delivery cute, warm, lively, and easy to understand."
    : "请保持轻快、可爱、自然的语气。"
  );
  params["audio_params"]["format"] = "pcm";
  params["audio_params"]["sample_rate"] = 24000;
  params["audio_params"]["speech_rate"] = englishReply ? 12 : 5;
  params["audio_params"]["loudness_rate"] = 10;
  params["post_process"]["pitch"] = 0;
  params["enable_auto_language_recognition"] = false;
  params["disable_markdown_filter"] = true;
  Serial.printf("TTS voice: Lulu / Peppa Pig 2.0 (%s)\n",
                englishReply ? "English" : "Chinese");
  String body;
  serializeJson(request, body);

  TtsSink sink;
  if (!sink.begin()) {
    Serial.println("Not enough memory for speech buffers (is PSRAM enabled?).");
    return false;
  }

  NetworkClientSecure client;
  client.useBuiltinCACertBundle();
  if (!client.connect("openspeech.bytedance.com", 443)) {
    Serial.println("Speech connection failed.");
    sink.end();
    return false;
  }
  String req = String("POST /api/v3/tts/unidirectional HTTP/1.1\r\n")
    + "Host: openspeech.bytedance.com\r\n"
    + "X-Api-Key: " + DOUBAO_API_KEY + "\r\n"
    + "X-Api-Resource-Id: " + LULU_TTS_RESOURCE_ID + "\r\n"
    + "X-Api-Request-Id: " + uuid() + "\r\n"
    + "Content-Type: application/json\r\n"
    + "Content-Length: " + String(body.length()) + "\r\n"
    + "Connection: close\r\n\r\n";
  client.print(req);
  client.print(body);
  req = "";

  String hdr, errBody;
  bool headersDone = false, chunked = false, errorMode = false;
  int httpStatus = 0;
  ChunkDecoder dec;
  const char *why = "stream closed";
  uint32_t lastData = millis();
  while (!sink.done && !sink.failed) {
    updateHandFollowing();
    if (millis() - lastData > 20000) { why = "no data for 20 s"; break; }
    int avail = client.available();
    if (avail <= 0) {
      if (!client.connected()) break;
      delay(2); continue;
    }
    int n = client.read(ttsRx, min((int)sizeof(ttsRx), avail));
    if (n <= 0) continue;
    lastData = millis();
    int i = 0;
    if (!headersDone) {
      while (i < n && !headersDone) {
        hdr += (char)ttsRx[i++];
        size_t L = hdr.length();
        if (L >= 4 && hdr[L - 4] == '\r' && hdr[L - 3] == '\n' && hdr[L - 2] == '\r' && hdr[L - 1] == '\n')
          headersDone = true;
        else if (L > 4096) { Serial.println("Speech response header too large."); sink.failed = true; break; }
      }
      if (headersDone) {
        httpStatus = hdr.substring(9, 12).toInt();
        String lower = hdr; lower.toLowerCase();
        chunked = lower.indexOf("transfer-encoding: chunked") >= 0;
        if (httpStatus != 200) {
          Serial.printf("Speech generation failed (HTTP %d).\n", httpStatus);
          errorMode = true;
        }
        hdr = "";
      }
    }
    if (headersDone && i < n) {
      if (errorMode) {
        for (int k = i; k < n && errBody.length() < 300; ++k) errBody += (char)ttsRx[k];
        if (errBody.length() >= 300) break;
      } else if (chunked) {
        dec.feed(ttsRx + i, n - i, sink);
      } else {
        sink.write(ttsRx + i, n - i);
      }
    }
    if (!errorMode && !sink.playerStarted && sink.audioLen >= TTS_PREBUFFER_BYTES) {
      sink.playerStarted = true;
      xTaskCreatePinnedToCore(ttsPlayerTask, "tts_play", 6144, &sink, 2, nullptr, 0);
    }
    if (chunked && dec.state == ChunkDecoder::END) { why = "final chunk"; break; }
  }
  client.stop();

  if (errorMode) {
    if (errBody.length()) Serial.println(errBody);
    sink.finished = true;
    sink.end();
    return false;
  }
  Serial.printf("TTS download: %d events, %u PCM bytes, %s (%s, %lu ms)\n",
                sink.events, (unsigned)sink.audioLen,
                sink.done ? "complete" : "INCOMPLETE", why,
                (unsigned long)(millis() - sink.startedAt));
  {
    uint32_t ms = millis() - sink.startedAt;
    if (!ms) ms = 1;
    Serial.printf("Wi-Fi RSSI %d dBm | average %.1f KB/s of audio (playback needs 46.9 KB/s)\n",
                  (int)WiFi.RSSI(), (float)sink.audioLen * 1000.0f / 1024.0f / ms);
  }
  sink.finished = true;
  if (!sink.playerStarted && sink.audioLen >= 2) {
    sink.playerStarted = true; // short reply: below the pre-buffer size
    xTaskCreatePinnedToCore(ttsPlayerTask, "tts_play", 6144, &sink, 2, nullptr, 0);
  }
  if (!sink.playerStarted) {
    Serial.println("No speech audio was played.");
    sink.end();
    return false;
  }
  uint32_t waitStart = millis();
  while (!sink.playerDone && millis() - waitStart < 60000) {
    updateHandFollowing(); // keep the eyes and head alive while Lulu speaks
    emotionTick();
    delay(20);
  }
  if (!sink.playerDone) { Serial.println("Playback task did not finish."); return false; }
  size_t played = sink.played;
  if (savePath && sink.done && !sink.failed && !sink.stoppedByUser)
    saveTtsCache(savePath, sink.audio, sink.audioLen);
  sink.end();
  handleQueuedTouchBleat();
  Serial.printf("Playback complete (%u audio bytes).\n", (unsigned)played);
  return played > 0;
}

// A short local two-note cue. It plays immediately, without waiting for Wi-Fi
// or TTS, so touch and wake-word interactions feel responsive.
void playWakeChime() {
  constexpr int RATE = 24000;
  constexpr int BLOCK = 128;
  constexpr int NOTE_SAMPLES = RATE * 70 / 1000;
  constexpr int TOTAL_SAMPLES = NOTE_SAMPLES * 2;
  int16_t samples[BLOCK];
  float phase = 0.0f;

  mic.end();
  digitalWrite(SPEAKER_ENABLE_PIN, HIGH);
  delay(5);
  mic.setPins(SPEAKER_BCLK_PIN, SPEAKER_LRC_PIN, SPEAKER_DATA_PIN, -1);
  if (!mic.begin(I2S_MODE_STD, RATE, I2S_DATA_BIT_WIDTH_16BIT,
                 I2S_SLOT_MODE_MONO)) {
    digitalWrite(SPEAKER_ENABLE_PIN, LOW);
    return;
  }

  for (int start = 0; start < TOTAL_SAMPLES; start += BLOCK) {
    int count = min(BLOCK, TOTAL_SAMPLES - start);
    for (int j = 0; j < count; ++j) {
      int i = start + j;
      float frequency = i < NOTE_SAMPLES ? 880.0f : 1175.0f;
      phase += 2.0f * PI * frequency / RATE;
      int withinNote = i % NOTE_SAMPLES;
      float envelope = 1.0f;
      if (withinNote < 120) envelope = withinNote / 120.0f;
      if (NOTE_SAMPLES - withinNote < 180)
        envelope = min(envelope, (NOTE_SAMPLES - withinNote) / 180.0f);
      samples[j] = (int16_t)(sinf(phase) * 5200.0f * envelope);
    }
    mic.write((uint8_t *)samples, count * sizeof(int16_t));
  }
  delay(60);
  mic.end();
  digitalWrite(SPEAKER_ENABLE_PIN, LOW);
}

// Play the real sheep recording stored in lulu_lamb_audio.h. This is used for
// head-touch interaction only; timers and wake-word acknowledgement keep the
// short two-note cue so reminders remain easy to recognise.
void playLambBleat(bool animateNod) {
  constexpr int BLOCK = 256;
  int16_t samples[BLOCK];

  mic.end();
  digitalWrite(SPEAKER_ENABLE_PIN, HIGH);
  delay(5);
  mic.setPins(SPEAKER_BCLK_PIN, SPEAKER_LRC_PIN, SPEAKER_DATA_PIN, -1);
  if (!mic.begin(I2S_MODE_STD, LULU_LAMB_SAMPLE_RATE,
                 I2S_DATA_BIT_WIDTH_16BIT, I2S_SLOT_MODE_MONO)) {
    digitalWrite(SPEAKER_ENABLE_PIN, LOW);
    return;
  }

  if (animateNod) {
    setRobotFace(FACE_SLEEPY);
    startNodMotion(false);   // nod runs inside updateHandFollowing()
  }

  for (size_t start = 0; start < LULU_LAMB_SAMPLE_COUNT; start += BLOCK) {
    size_t count = min((size_t)BLOCK, LULU_LAMB_SAMPLE_COUNT - start);
    for (size_t j = 0; j < count; ++j) {
      int32_t sample = (int16_t)pgm_read_word(&LULU_LAMB_PCM[start + j]);
      // The source recording peaks around 13k, so a modest boost remains
      // below clipping while making the bleat clear on the small speaker.
      samples[j] = (int16_t)constrain(sample * 3 / 2, -30000L, 30000L);
    }
    mic.write((uint8_t *)samples, count * sizeof(int16_t));
    updateHandFollowing();
  }
  delay(40);
  mic.end();
  digitalWrite(SPEAKER_ENABLE_PIN, LOW);
  if (animateNod) setRobotFace(FACE_HAPPY);
}

static uint16_t wavLE16(const uint8_t *p) {
  return (uint16_t)p[0] | (uint16_t)p[1] << 8;
}

static uint32_t wavLE32(const uint8_t *p) {
  return (uint32_t)p[0] | (uint32_t)p[1] << 8 |
         (uint32_t)p[2] << 16 | (uint32_t)p[3] << 24;
}

// Play a WAV stored in the FFat songs folder. Keeping songs out of the sketch
// lets the user replace them from Lulu's web page without recompiling.
bool playWavSong(const String &path) {
  if (!luluStorageReady || !FFat.exists(path)) return false;
  File song = FFat.open(path, FILE_READ);
  uint8_t head[12];
  if (!song || song.read(head, sizeof(head)) != sizeof(head) ||
      memcmp(head, "RIFF", 4) || memcmp(head + 8, "WAVE", 4)) {
    Serial.println("Song is not a valid WAV file.");
    if (song) song.close();
    return false;
  }

  uint16_t format = 0, channels = 0, bits = 0;
  uint32_t sampleRate = 0, dataStart = 0, dataBytes = 0;
  while (song.available()) {
    uint8_t chunk[8];
    if (song.read(chunk, sizeof(chunk)) != sizeof(chunk)) break;
    uint32_t size = wavLE32(chunk + 4);
    uint32_t next = song.position() + size + (size & 1);
    if (!memcmp(chunk, "fmt ", 4) && size >= 16) {
      uint8_t fmt[16];
      if (song.read(fmt, sizeof(fmt)) != sizeof(fmt)) break;
      format = wavLE16(fmt); channels = wavLE16(fmt + 2);
      sampleRate = wavLE32(fmt + 4); bits = wavLE16(fmt + 14);
    } else if (!memcmp(chunk, "data", 4)) {
      dataStart = song.position(); dataBytes = size; break;
    }
    song.seek(next);
  }
  if (format != 1 || channels != 1 || bits != 16 || sampleRate < 8000 ||
      sampleRate > 48000 || !dataStart || !dataBytes) {
    Serial.println("Song must be mono 16-bit PCM WAV at 8-48 kHz.");
    song.close(); return false;
  }

  song.seek(dataStart);
  Serial.printf("Playing song: %s | %lu Hz | %.1f seconds\n", path.c_str(),
                (unsigned long)sampleRate,
                (double)dataBytes / (sampleRate * 2.0));
  mic.end();
  digitalWrite(SPEAKER_ENABLE_PIN, HIGH);
  delay(5);
  mic.setPins(SPEAKER_BCLK_PIN, SPEAKER_LRC_PIN, SPEAKER_DATA_PIN, -1);
  if (!mic.begin(I2S_MODE_STD, sampleRate, I2S_DATA_BIT_WIDTH_16BIT,
                 I2S_SLOT_MODE_MONO)) {
    digitalWrite(SPEAKER_ENABLE_PIN, LOW);
    song.close(); return false;
  }
  uint8_t audio[2048];
  uint32_t left = dataBytes;
  setRobotFace(FACE_HAPPY);
  singDanceStart();
  while (left && song.available()) {
    if (digitalRead(RECORD_BUTTON_PIN) == LOW || queuedTouchBleat) break;
    size_t count = song.read(audio, min((uint32_t)sizeof(audio), left));
    if (!count) break;
    mic.write(audio, count);
    left -= count;
    singDance();
  }
  delay(100);
  mic.end();
  digitalWrite(SPEAKER_ENABLE_PIN, LOW);
  song.close();
  singDanceEnd();
  setRobotFace(FACE_NORMAL);
  Serial.println(left ? "Song stopped." : "Song finished.");
  return true;
}

// ---- MP3 playback (Helix decoder, needs the "libhelix" library) -------------
// Decodes while reading from FFat. Output is mixed down to mono and sent to the
// same speaker I2S port as everything else, at the file's own sample rate.
bool playMp3Song(const String &path) {
#if !LULU_HAS_MP3
  Serial.println("MP3 needs the Arduino library 'libhelix' (Library Manager). Using WAV only.");
  return false;
#else
  if (!luluStorageReady || !FFat.exists(path)) return false;
  File song = FFat.open(path, FILE_READ);
  if (!song) return false;

  // Skip an ID3v2 tag at the start of the file.
  uint8_t id3[10];
  if (song.read(id3, sizeof(id3)) == sizeof(id3) && !memcmp(id3, "ID3", 3)) {
    uint32_t tag = ((id3[6] & 0x7F) << 21) | ((id3[7] & 0x7F) << 14) | ((id3[8] & 0x7F) << 7) | (id3[9] & 0x7F);
    song.seek(10 + tag);
  } else {
    song.seek(0);
  }

  constexpr int IN_SIZE = 4096;
  uint8_t *in = (uint8_t *)psramAlloc(IN_SIZE);
  int16_t *pcm = (int16_t *)psramAlloc(1152 * 2 * sizeof(int16_t));
  int16_t *mono = (int16_t *)psramAlloc(1152 * sizeof(int16_t));
  HMP3Decoder dec = MP3InitDecoder();
  if (!in || !pcm || !mono || !dec) {
    Serial.println("MP3: not enough memory.");
    free(in); free(pcm); free(mono);
    if (dec) MP3FreeDecoder(dec);
    song.close();
    return false;
  }

  Serial.printf("Playing MP3: %s | %u KB\n", path.c_str(), (unsigned)(song.size() / 1024));
  bool i2sOpen = false, stopped = false, eof = false;
  uint32_t rate = 0;
  int have = 0, badFrames = 0;
  setRobotFace(FACE_HAPPY);
  singDanceStart();

  for (;;) {
    if (digitalRead(RECORD_BUTTON_PIN) == LOW || queuedTouchBleat) { stopped = true; break; }
    if (have < IN_SIZE - 1024 && !eof) {
      int n = song.read(in + have, IN_SIZE - have);
      if (n <= 0) eof = true; else have += n;
    }
    if (have <= 4) break;
    int off = MP3FindSyncWord(in, have);
    if (off < 0) {                       // no frame header in this chunk
      have = 0;
      if (eof) break;
      continue;
    }
    if (off > 0) { memmove(in, in + off, have - off); have -= off; }

    unsigned char *p = in;
    int left = have;
    int rc = MP3Decode(dec, &p, &left, pcm, 0);
    int used = (int)(p - in);
    if (rc == ERR_MP3_NONE) {
      MP3FrameInfo info;
      MP3GetLastFrameInfo(dec, &info);
      int ch = info.nChans >= 2 ? 2 : 1;
      int frames = info.outputSamps / ch;
      if (frames > 1152) frames = 1152;
      if (!i2sOpen) {
        rate = info.samprate;
        mic.end();
        digitalWrite(SPEAKER_ENABLE_PIN, HIGH);
        delay(5);
        mic.setPins(SPEAKER_BCLK_PIN, SPEAKER_LRC_PIN, SPEAKER_DATA_PIN, -1);
        if (rate < 8000 || rate > 48000 ||
            !mic.begin(I2S_MODE_STD, rate, I2S_DATA_BIT_WIDTH_16BIT, I2S_SLOT_MODE_MONO)) {
          Serial.printf("MP3: cannot open speaker at %lu Hz.\n", (unsigned long)rate);
          digitalWrite(SPEAKER_ENABLE_PIN, LOW);
          stopped = true; break;
        }
        i2sOpen = true;
        Serial.printf("MP3: %lu Hz, %d channel(s), %d kbps\n", (unsigned long)rate, info.nChans, info.bitrate / 1000);
      }
      for (int i = 0; i < frames; ++i)
        mono[i] = ch == 2 ? (int16_t)(((int)pcm[2 * i] + (int)pcm[2 * i + 1]) / 2) : pcm[i];
      const uint8_t *bytes = (const uint8_t *)mono;
      size_t total = (size_t)frames * 2, offBytes = 0;
      int stalls = 0;
      while (offBytes < total) {
        size_t w = mic.write(bytes + offBytes, total - offBytes);
        if (w == 0) { if (++stalls > 200) break; delay(2); continue; }
        stalls = 0; offBytes += w;
      }
      badFrames = 0;
    } else if (rc == ERR_MP3_INDATA_UNDERFLOW || rc == ERR_MP3_MAINDATA_UNDERFLOW) {
      if (eof && left <= 0) break;
      if (used <= 0 && eof) break;
    } else {
      if (++badFrames > 200) { Serial.println("MP3: too many bad frames, stopping."); break; }
      if (used <= 0) used = 1;           // skip one byte and re-sync
    }
    if (used > 0 && used <= have) { memmove(in, in + used, have - used); have -= used; }
    singDance();
  }

  if (i2sOpen) {
    delay(150);
    mic.end();
    digitalWrite(SPEAKER_ENABLE_PIN, LOW);
  }
  MP3FreeDecoder(dec);
  free(in); free(pcm); free(mono);
  song.close();
  singDanceEnd();
  setRobotFace(FACE_NORMAL);
  Serial.println(stopped ? "MP3 stopped." : "MP3 finished.");
  return i2sOpen;
#endif
}

// Plays a song from the songs folder, choosing the decoder from the extension.
bool playSong(const String &path) {
  String lower = path; lower.toLowerCase();
  if (lower.endsWith(".mp3")) return playMp3Song(path);
  return playWavSong(path);
}

// Play a cached raw PCM line (24 kHz mono s16) from FFat. Works offline.
bool playCachedLine(const String &path) {
  if (!luluStorageReady || !FFat.exists(path)) return false;
  File f = FFat.open(path, FILE_READ);
  if (!f) return false;
  if (f.size() < 4800) { f.close(); return false; }
  mic.end();
  digitalWrite(SPEAKER_ENABLE_PIN, HIGH);
  delay(5);
  mic.setPins(SPEAKER_BCLK_PIN, SPEAKER_LRC_PIN, SPEAKER_DATA_PIN, -1);
  if (!mic.begin(I2S_MODE_STD, 24000, I2S_DATA_BIT_WIDTH_16BIT, I2S_SLOT_MODE_MONO)) {
    digitalWrite(SPEAKER_ENABLE_PIN, LOW);
    f.close(); return false;
  }
  static uint8_t buf[2048];
  while (f.available()) {
    if (digitalRead(RECORD_BUTTON_PIN) == LOW || (queuedTouchBleat && !touchReactionOnly)) break;
    size_t n = f.read(buf, sizeof(buf));
    if (!n) break;
    size_t off = 0; int stalls = 0;
    while (off < n) {
      size_t w = mic.write(buf + off, n - off);
      if (w == 0) { if (++stalls > 200) break; delay(5); continue; }
      stalls = 0; off += w;
    }
    updateHandFollowing();
  }
  delay(200);
  mic.end();
  digitalWrite(SPEAKER_ENABLE_PIN, LOW);
  f.close();
  return true;
}

// Play one queued touch response after any active speech stream has released
// the shared I2S peripheral. This makes touch work during an AI reply too.
void handleQueuedTouchBleat() {
  if (!queuedTouchBleat) return;
  queuedTouchBleat = false;
  Serial.printf("Head touched: lamb response (%lu ms after touch).\n", (unsigned long)(millis() - touchQueuedAt));
  playLambBleat(true);
}

// ---- Touch-wake lines (English, for the demo) -------------------------------
// Each line is synthesised once by the cloud TTS and saved in FFat (/lines).
// After that it plays from flash: instant, offline, no TTS cost. The file name
// is a hash of the text, so editing a line below simply caches the new one.
static const char *TOUCH_FIRST[]   = { "What's up?", "Hmm? I'm here!", "Baa! Yes?", "Did you call me?" };
static const char *TOUCH_AGAIN[]   = { "What's up? Why are you petting my head?", "Baa? Why do you keep touching me?",
                                       "What do you want, hmm?", "Petting my head again? What is it?" };
static const char *TOUCH_ANNOYED[] = { "You keep touching and not talking. I'm going back to sleep.",
                                       "Hmph. One more pat and I will ignore you." };
constexpr int TOUCH_FIRST_N = 4, TOUCH_AGAIN_N = 4, TOUCH_ANNOYED_N = 2;

uint8_t touchWakeStrikes = 0;     // consecutive touch-wakes with no speech heard
uint32_t lastTouchWakeAt = 0;
int lastTouchLine = -1;
bool touchWakeTurnLeft = false;

String touchLinePath(const char *text) {
  uint32_t h = 5381;
  for (const char *c = text; *c; ++c) h = h * 33 + (uint8_t)*c;
  char name[24];
  snprintf(name, sizeof(name), "/lines/%08lx.pcm", (unsigned long)h);
  return String(name);
}

// Say one touch line: from flash if cached, otherwise from the cloud (and cache
// it). Offline and not cached -> silent.
void sayTouchLine(const char *text) {
  String path = touchLinePath(text);
  if (luluStorageReady && FFat.exists(path)) {
    Serial.printf("Touch line (cached): %s\n", text);
    playCachedLine(path);
  } else if (WiFi.status() == WL_CONNECTED) {
    Serial.printf("Touch line (cloud, will cache): %s\n", text);
    ttsSavePath = luluStorageReady ? path.c_str() : nullptr;
    speakDoubao(String(text));
  } else {
    Serial.printf("Touch line not cached and Wi-Fi is off: %s\n", text);
  }
}

// Serial command `cachelines`: say every line once so they all get cached.
void cacheAllTouchLines() {
  if (WiFi.status() != WL_CONNECTED) { Serial.println("Connect Wi-Fi first to cache the lines."); return; }
  for (int i = 0; i < TOUCH_FIRST_N; ++i)   sayTouchLine(TOUCH_FIRST[i]);
  for (int i = 0; i < TOUCH_AGAIN_N; ++i)   sayTouchLine(TOUCH_AGAIN[i]);
  for (int i = 0; i < TOUCH_ANNOYED_N; ++i) sayTouchLine(TOUCH_ANNOYED[i]);
  Serial.println("All touch lines cached.");
}

// Touch while asleep: turn the head (bleat already played by the caller), say a
// short cute line, then listen. If nobody speaks and she is touched again, the
// next line becomes a puzzled question.
void touchWakeFlow() {
  uint32_t now = millis();
  if (lastTouchWakeAt && now - lastTouchWakeAt > 90000UL) touchWakeStrikes = 0;
  lastTouchWakeAt = now;

  const char **pool; int n;
  if (touchWakeStrikes == 0)      { pool = TOUCH_FIRST;   n = TOUCH_FIRST_N; }
  else if (touchWakeStrikes < 3)  { pool = TOUCH_AGAIN;   n = TOUCH_AGAIN_N; }
  else                            { pool = TOUCH_ANNOYED; n = TOUCH_ANNOYED_N; }
  int pick = random(n);
  if (n > 1 && pick == lastTouchLine) pick = (pick + 1) % n;
  lastTouchLine = pick;

  // Turn the head a little to one side (alternates), then speak.
  touchReactionOnly = true;                 // touches during the greeting only nod
  touchWakeTurnLeft = !touchWakeTurnLeft;
  targetLR = constrain(LR_CENTER + (touchWakeTurnLeft ? 30 : -30), X_SAFE_MIN, X_SAFE_MAX);
  RobotFace greetFace = FACE_HAPPY;
  if (touchWakeStrikes >= 5)      greetFace = FACE_DIZZY;
  else if (touchWakeStrikes >= 3) greetFace = FACE_ANGRY;
  else if (touchWakeStrikes >= 1) greetFace = FACE_SHY;
  setRobotFace(greetFace);   // the head turns while the line plays
  Serial.printf("Touch wake (strikes=%u), %lu ms after touch\n", touchWakeStrikes, (unsigned long)(millis() - touchQueuedAt));
  sayTouchLine(pool[pick]);
  targetLR = LR_CENTER;
  queuedTouchBleat = false;                 // drop touches made during the greeting
  touchReactionOnly = false;
  if (touchWakeStrikes == 0) { setRobotFace(FACE_WINK); delay(500); }
  setRobotFace(FACE_NORMAL);

  if (WiFi.status() == WL_CONNECTED) {
    Serial.println("Head touched: listening...");
    lastText = "";
    recognize(false);
    if (lastText.length() > 0) {
      touchWakeStrikes = 0;
    } else {
      setRobotFace(FACE_SAD); delay(900); setRobotFace(FACE_NORMAL);
      if (touchWakeStrikes < 250) touchWakeStrikes++;
    }
  } else {
    Serial.println("Wi-Fi not connected: line only, not listening.");
    if (touchWakeStrikes < 250) touchWakeStrikes++;
  }
}

// The network and AI calls can block the Arduino loop for several seconds.
// A tiny independent task watches the touch pad continuously and remembers
// the rising edge until the shared speaker is available.
void touchMonitorTask(void *) {
  bool stableLevel = digitalRead(HEAD_TOUCH_PIN) == HIGH;
  bool candidateLevel = stableLevel;
  uint32_t candidateSince = millis();
  for (;;) {
    bool rawLevel = digitalRead(HEAD_TOUCH_PIN) == HIGH;
    if (rawLevel != candidateLevel) {
      candidateLevel = rawLevel;
      candidateSince = millis();
    }
    if (candidateLevel != stableLevel && millis() - candidateSince >= 5) {
      stableLevel = candidateLevel;
      bool active = stableLevel != touchIdleLevel;
      if (active && !touchPhysicalActive) { touchQueuedAt = millis(); queuedTouchBleat = true; }
      touchPhysicalActive = active;
    }
    vTaskDelay(pdMS_TO_TICKS(5));
  }
}

String weatherName(int code, bool english) {
  if (code == 0) return english ? "clear" : "晴朗";
  if (code <= 3) return english ? "partly cloudy" : "多云";
  if (code == 45 || code == 48) return english ? "foggy" : "有雾";
  if (code <= 57) return english ? "drizzly" : "有小雨";
  if (code <= 67) return english ? "rainy" : "有雨";
  if (code <= 77) return english ? "snowy" : "有雪";
  if (code <= 82) return english ? "showery" : "有阵雨";
  if (code <= 86) return english ? "snow showery" : "有阵雪";
  return english ? "stormy" : "有雷雨";
}

String getMelbourneWeather(bool english) {
  if (!networkReady()) return english ? "I cannot reach the weather service right now." : "现在连不上天气服务。";
  String url = "https://api.open-meteo.com/v1/forecast?latitude=" + String(HOME_LATITUDE, 4)
    + "&longitude=" + String(HOME_LONGITUDE, 4)
    + "&current=temperature_2m,apparent_temperature,weather_code"
      "&daily=temperature_2m_max,temperature_2m_min,precipitation_probability_max"
      "&forecast_days=1&timezone=Australia%2FMelbourne";
  NetworkClientSecure client;
  client.useBuiltinCACertBundle();
  HTTPClient http;
  http.setTimeout(12000);
  if (!http.begin(client, url)) return english ? "The weather service did not open." : "天气服务打开失败。";
  int status = http.GET();
  if (status != HTTP_CODE_OK) {
    http.end();
    return english ? "I could not get today's weather." : "没有查到今天的天气。";
  }
  // HTTPClient::getString() removes HTTP chunk markers before JSON parsing.
  // Parsing getStream() directly can fail when Open-Meteo uses chunked transfer.
  String weatherJson = http.getString();
  http.end();
  JsonDocument data;
  DeserializationError error = deserializeJson(data, weatherJson);
  if (error) {
    Serial.printf("Weather JSON error: %s, HTTP %d, %u bytes.\n",
                  error.c_str(), status, (unsigned)weatherJson.length());
    Serial.println(weatherJson.substring(0, 160));
    return english ? "The weather data was unclear." : "天气数据读取失败。";
  }
  float current = data["current"]["temperature_2m"] | 0.0f;
  float feels = data["current"]["apparent_temperature"] | current;
  int code = data["current"]["weather_code"] | 0;
  float high = data["daily"]["temperature_2m_max"][0] | current;
  float low = data["daily"]["temperature_2m_min"][0] | current;
  int rain = data["daily"]["precipitation_probability_max"][0] | 0;
  if (english) {
    return "Melbourne is " + weatherName(code, true) + ", " + String(current, 0)
      + " degrees, feels like " + String(feels, 0) + ". High " + String(high, 0)
      + ", low " + String(low, 0) + ", rain chance " + String(rain) + " percent.";
  }
  return "墨尔本现在" + weatherName(code, false) + String(current, 0) + "度，体感"
    + String(feels, 0) + "度。最高" + String(high, 0) + "度，最低" + String(low, 0)
    + "度，降雨概率" + String(rain) + "% 。";
}

void saveReminders() {
  for (int i = 0; i < MAX_ALERTS; ++i) {
    String tk = "t" + String(i), mk = "m" + String(i);
    if (alerts[i].active && !alerts[i].timer) {
      reminderStore.putULong64(tk.c_str(), (uint64_t)alerts[i].dueEpoch);
      reminderStore.putString(mk.c_str(), alerts[i].note);
    } else {
      reminderStore.remove(tk.c_str());
      reminderStore.remove(mk.c_str());
    }
  }
}

void loadReminders() {
  for (int i = 0; i < MAX_ALERTS; ++i) {
    String tk = "t" + String(i), mk = "m" + String(i);
    uint64_t due = reminderStore.getULong64(tk.c_str(), 0);
    if (due > (uint64_t)time(nullptr)) {
      alerts[i].active = true;
      alerts[i].timer = false;
      alerts[i].dueEpoch = (time_t)due;
      alerts[i].note = reminderStore.getString(mk.c_str(), "重要的事情");
    }
  }
}

bool addCountdown(uint32_t seconds, const String &note) {
  if (!seconds || seconds > 86400 * 7) return false;
  for (int i = 0; i < MAX_ALERTS; ++i) if (!alerts[i].active) {
    alerts[i].active = true; alerts[i].timer = true;
    alerts[i].dueMillis = millis() + seconds * 1000UL;
    alerts[i].note = note.length() ? note : "倒计时结束";
    return true;
  }
  return false;
}

bool addCalendarReminder(const String &when, const String &note) {
  struct tm value = {};
  value.tm_isdst = -1;
  if (!strptime(when.c_str(), "%Y-%m-%d %H:%M", &value)) return false;
  time_t due = mktime(&value);
  if (due <= time(nullptr)) return false;
  for (int i = 0; i < MAX_ALERTS; ++i) if (!alerts[i].active) {
    alerts[i].active = true; alerts[i].timer = false;
    alerts[i].dueEpoch = due;
    alerts[i].note = note.length() ? note : "备忘录提醒";
    saveReminders();
    return true;
  }
  return false;
}

String listAlerts(bool english) {
  int count = 0;
  String result = english ? "You have " : "你有";
  for (int i = 0; i < MAX_ALERTS; ++i) if (alerts[i].active) ++count;
  if (!count) return english ? "You have no active timers or reminders." : "现在没有倒计时或备忘提醒。";
  result += String(count) + (english ? " active reminders. " : "个提醒：");
  for (int i = 0; i < MAX_ALERTS; ++i) if (alerts[i].active) {
    result += alerts[i].note;
    if (!alerts[i].timer) {
      struct tm value;
      localtime_r(&alerts[i].dueEpoch, &value);
      char when[32];
      strftime(when, sizeof(when), english ? "%b %d at %I:%M %p" : "%m月%d日%H点%M分", &value);
      result += english ? " at " + String(when) : String(when);
    }
    result += "。";
  }
  return result;
}

static time_t alertDueTime(const AlertItem &item) {
  if (!item.timer) return item.dueEpoch;
  int32_t remainingMs = (int32_t)(item.dueMillis - millis());
  if (remainingMs < 0) remainingMs = 0;
  return time(nullptr) + (remainingMs + 999) / 1000;
}

static bool sameLocalDay(time_t a, time_t b) {
  struct tm ta, tb;
  localtime_r(&a, &ta); localtime_r(&b, &tb);
  return ta.tm_year == tb.tm_year && ta.tm_yday == tb.tm_yday;
}

static String friendlyAlertTime(time_t due, bool english) {
  struct tm value; localtime_r(&due, &value);
  char text[32];
  if (english) {
    strftime(text, sizeof(text), "%I:%M %p", &value);
    String result(text);
    if (result.startsWith("0")) result.remove(0, 1);
    return result;
  }
  int hour12 = value.tm_hour % 12;
  if (!hour12) hour12 = 12;
  String period = value.tm_hour < 6 ? "凌晨" : value.tm_hour < 12 ? "上午" :
                  value.tm_hour == 12 ? "中午" : value.tm_hour < 18 ? "下午" : "晚上";
  String result = period + String(hour12) + "点";
  if (value.tm_min) result += String(value.tm_min) + "分";
  return result;
}

String listTodayAlerts(bool english) {
  int order[MAX_ALERTS];
  int count = 0;
  time_t now = time(nullptr);
  for (int i = 0; i < MAX_ALERTS; ++i) {
    if (alerts[i].active && sameLocalDay(alertDueTime(alerts[i]), now)) order[count++] = i;
  }
  for (int i = 0; i < count; ++i) {
    for (int j = i + 1; j < count; ++j) {
      if (alertDueTime(alerts[order[j]]) < alertDueTime(alerts[order[i]])) {
        int swap = order[i]; order[i] = order[j]; order[j] = swap;
      }
    }
  }
  if (!count) return english ? "You have no reminders scheduled for today."
                             : "你今天没有设置提醒。";
  String result = english ? "Today, " : "今天";
  for (int n = 0; n < count; ++n) {
    AlertItem &item = alerts[order[n]];
    String at = friendlyAlertTime(alertDueTime(item), english);
    if (english) {
      if (n) result += " Then, ";
      result += "at " + at + ", you need to " + item.note + ".";
    } else {
      if (n) result += "然后";
      result += at + "你要" + item.note + "。";
    }
  }
  return result;
}

static bool listedAlertsAreEnglish(bool todayOnly) {
  time_t now = time(nullptr);
  bool found = false;
  for (int i = 0; i < MAX_ALERTS; ++i) {
    if (!alerts[i].active) continue;
    if (todayOnly && !sameLocalDay(alertDueTime(alerts[i]), now)) continue;
    found = true;
    if (!textIsMostlyEnglish(alerts[i].note)) return false;
  }
  return true; // no saved item also permits an English "nothing scheduled" reply
}

void clearAllAlerts() {
  for (int i = 0; i < MAX_ALERTS; ++i) {
    alerts[i].active = false;
    alerts[i].timer = false;
    alerts[i].note = "";
    String tk = "t" + String(i), mk = "m" + String(i);
    reminderStore.remove(tk.c_str());
    reminderStore.remove(mk.c_str());
  }
  latestReplyText = "";
  Serial.println("All saved reminders and timers cleared.");
}

// 0 = normal conversation, 1 = all saved items, 2 = today's items.
int reminderListQuery(const String &input) {
  String s = input; s.toLowerCase();
  bool today = s.indexOf("今天") >= 0 || s.indexOf("today") >= 0;
  // A bare "有什么 / 哪些" is an ordinary question (e.g. "墨尔本有什么好吃的"), so it
  // only counts as a reminder question when a reminder-type word is also present.
  bool chineseTopic = s.indexOf("提醒") >= 0 || s.indexOf("备忘") >= 0 || s.indexOf("行程") >= 0 ||
                      s.indexOf("日程") >= 0 || s.indexOf("待办") >= 0 || s.indexOf("安排") >= 0 ||
                      s.indexOf("事项") >= 0 || s.indexOf("倒计时") >= 0 || s.indexOf("计划") >= 0;
  bool chineseAsk = s.indexOf("什么") >= 0 || s.indexOf("哪些") >= 0 || s.indexOf("有没有") >= 0 ||
                    s.indexOf("几个") >= 0 || s.indexOf("列") >= 0 || s.indexOf("看看") >= 0;
  bool chineseQuestion = (chineseTopic && chineseAsk) ||
                         (s.indexOf("要做什么") >= 0 && (today || chineseTopic)) ||
                         s.indexOf("备忘") >= 0 || s.indexOf("行程") >= 0;
  bool englishTopic = s.indexOf("reminder") >= 0 || s.indexOf("to do") >= 0 ||
                      s.indexOf("todo") >= 0 || s.indexOf("schedule") >= 0;
  bool englishQuestion = s.indexOf("what") >= 0 || s.indexOf("list") >= 0 ||
                         s.indexOf("show") >= 0 || s.indexOf("do i have") >= 0;
  // "提醒我 / remind me" creates a new reminder and must still go to the AI parser.
  bool createRequest = s.indexOf("提醒我") >= 0 || s.indexOf("remind me") >= 0 ||
                       s.indexOf("set a reminder") >= 0 || s.indexOf("创建") >= 0;
  if (createRequest) return 0;
  if (chineseQuestion || (englishTopic && (englishQuestion || today))) return today ? 2 : 1;
  return 0;
}

static String reminderSavedReply(bool english, const String &when, const String &note) {
  struct tm value = {}; value.tm_isdst = -1;
  if (!strptime(when.c_str(), "%Y-%m-%d %H:%M", &value))
    return english ? "I saved your reminder." : "我已经保存这个提醒。";
  time_t due = mktime(&value);
  String at = friendlyAlertTime(due, english);
  return english ? "Saved. At " + at + ", " + note + "."
                 : "记好了，" + at + "提醒你" + note + "。";
}

String handlePendingAction(const String &normalReply) {
  if (pendingAction == "time") {
    struct tm now;
    if (!getLocalTime(&now, 50)) return pendingEnglish ? "I do not have the correct time yet." : "我还没有同步到正确时间。";
    char value[64];
    strftime(value, sizeof(value), pendingEnglish ? "It is %A, %B %d, %I:%M %p." : "今天是%m月%d日，现在%H点%M分。", &now);
    return String(value);
  }
  if (pendingAction == "weather") return getMelbourneWeather(pendingEnglish);
  if (pendingAction == "timer") {
    if (addCountdown(pendingSeconds, pendingNote)) return normalReply;
    return pendingEnglish ? "I could not start that timer." : "这个倒计时没有设置成功。";
  }
  if (pendingAction == "reminder") {
    if (addCalendarReminder(pendingWhen, pendingNote))
      return reminderSavedReply(pendingEnglish, pendingWhen, pendingNote);
    return pendingEnglish ? "I could not save that reminder." : "这个备忘提醒没有保存成功。";
  }
  if (pendingAction == "list") return listAlerts(pendingEnglish);
  return normalReply;
}

void checkAlerts() {
  for (int i = 0; i < MAX_ALERTS; ++i) {
    if (!alerts[i].active) continue;
    bool due = alerts[i].timer
      ? (int32_t)(millis() - alerts[i].dueMillis) >= 0
      : time(nullptr) >= alerts[i].dueEpoch;
    if (!due) continue;
    String note = alerts[i].note;
    bool wasReminder = !alerts[i].timer;
    alerts[i].active = false;
    if (wasReminder) saveReminders();
    playWakeChime();
    delay(80);
    speakDoubao(textIsMostlyEnglish(note) ? "Reminder: " + note : "提醒你：" + note);
  }
}

static String safeSongName(String name) {
  name.replace("\\", "/");
  int slash = name.lastIndexOf('/');
  if (slash >= 0) name = name.substring(slash + 1);
  String clean;
  clean.reserve(name.length());
  for (size_t i = 0; i < name.length() && clean.length() < 64; ++i) {
    char c = name[i];
    if (isalnum((unsigned char)c) || c == ' ' || c == '-' || c == '_' || c == '.') clean += c;
    else clean += '_';
  }
  clean.trim();
  return clean;
}

static void dashboardRedirect() {
  luluWeb.sendHeader("Location", "/", true);
  luluWeb.send(303, "text/plain", "OK");
}

static String dashboardPage() {
  String page;
  page.reserve(80000);
  page += R"LULU(<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Sheep Lulu</title>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Press+Start+2P&family=VT323&display=swap" media="print" onload="this.media='all'">
<style>
:root{--red:#c9342a;--dred:#8e1f19;--ink:#141414;--paper:#f8f6f1;--g1:#a8d45a;--g2:#5f9430;--sh:#e0403e;--cream:#f0dcae;--muted:#6b5f5a}
*{box-sizing:border-box}
html{color-scheme:light;scroll-behavior:smooth}
body{margin:0;background:var(--paper);color:var(--ink);font-family:"VT323",ui-monospace,Menlo,Consolas,"Courier New",monospace;font-size:20px;line-height:1.25;
 background-image:linear-gradient(#0000000a 1px,transparent 1px),linear-gradient(90deg,#0000000a 1px,transparent 1px);background-size:24px 24px}
.pf{font-family:"Press Start 2P","Courier New",ui-monospace,monospace;font-weight:400;letter-spacing:0}
/* top menu */
nav{position:sticky;top:0;z-index:20;background:var(--ink);padding:8px 10px;display:flex;gap:8px;flex-wrap:wrap;justify-content:center;border-bottom:4px solid var(--red)}
nav a{font-family:"Press Start 2P","Courier New",monospace;font-size:10px;color:#fff;text-decoration:none;padding:9px 10px;border:3px solid #fff}
nav a:hover,nav a:focus-visible{background:var(--red);border-color:var(--red);outline:none}
/* hero */
.hero{position:relative;text-align:center;padding:26px 14px 6px}
.eyebrow{font-family:"Press Start 2P","Courier New",monospace;font-size:clamp(8px,1.7vw,12px);color:var(--red);line-height:1.8}
.title{margin:14px 0 0;font-family:"Press Start 2P","Courier New",monospace;font-weight:400;color:var(--red);line-height:1.18;font-size:clamp(28px,7vw,60px);text-shadow:.07em .07em 0 var(--ink);text-transform:uppercase}
.title span{display:inline}.title span+span{margin-left:.35em}
.start{display:none;margin-top:22px;font-family:"Press Start 2P","Courier New",monospace;font-size:clamp(10px,2vw,14px);color:var(--ink);animation:blinkk 1s steps(2) infinite}
@keyframes blinkk{50%{opacity:0}}
.addr{margin-top:8px;font-size:22px;color:var(--dred)}
.live{display:inline-flex;align-items:center;gap:12px;margin-top:14px;background:#fff;border:4px solid var(--ink);box-shadow:5px 5px 0 var(--ink);padding:8px 12px}
.live .oled{width:104px}
.live b{font-family:"Press Start 2P","Courier New",monospace;font-size:10px;color:var(--red);display:block}
.live small{font-size:18px;color:var(--muted)}
.hillsvg{position:absolute;left:0;bottom:0;width:100%;height:100%;display:block}
.wrap{position:relative}
.side{display:none;position:absolute;top:30px;bottom:30px;width:calc((100% - 940px)/2);flex-direction:column;justify-content:space-around;align-items:center;pointer-events:none}
.side.l{left:0}.side.r{right:0}
.side svg{width:44px;aspect-ratio:11/8;height:auto}
.side svg:nth-child(odd){transform:translateX(-14px)}.side svg:nth-child(even){transform:translateX(14px) scale(.8)}
@media (min-width:1100px){.side{display:flex}}
.lawn{position:relative;height:300px;margin-top:0;overflow:hidden}
.lawn .note2{position:absolute;z-index:3;left:0;right:0;top:12px;text-align:center;color:var(--muted);font-size:18px;padding:0 14px}
.px{position:absolute;image-rendering:pixelated;shape-rendering:crispEdges}
.lamb{aspect-ratio:11/8;height:auto;width:clamp(30px,4.2vw,50px)}
.shroom{aspect-ratio:1/1;height:auto;width:clamp(38px,6vw,64px)}
.sheepbig{aspect-ratio:74/62;height:auto;width:clamp(130px,19vw,240px);left:3%;bottom:70px;animation:bob 1.2s steps(2) infinite}
@keyframes bob{50%{transform:translateY(-6px)}}
.walker{bottom:30px;left:-60px;animation:walk 26s linear infinite;z-index:1}
.walker.two{animation-duration:38s;animation-delay:-14s;bottom:46px;width:clamp(24px,3.4vw,40px)}
@keyframes walk{to{transform:translateX(calc(100vw + 120px))}}
@media (prefers-reduced-motion:reduce){.walker,.sheepbig,.start{animation:none}.blinkme .e{animation:none}}
/* windows */
main{position:relative;z-index:1;max-width:920px;margin:0 auto;padding:20px 14px 30px}
.win{background:#fff;border:4px solid var(--ink);box-shadow:7px 7px 0 var(--ink);margin:0 0 34px;scroll-margin-top:70px}
.win>h2{margin:0;background:var(--red);color:#fff;font-family:"Press Start 2P","Courier New",monospace;font-weight:400;font-size:clamp(11px,2.2vw,14px);line-height:1.5;padding:12px 14px;display:flex;align-items:center;gap:10px;border-bottom:4px solid var(--ink)}
.win>h2::before{content:"";width:12px;height:12px;background:#fff;box-shadow:16px 0 0 #ffffff80;margin-right:22px;flex:0 0 auto}
.win>h2 span{margin-left:auto;font-size:9px;opacity:.85}
.body{padding:16px}
.body>p.note{margin:0 0 12px;color:var(--muted);font-size:19px}
/* dialog */
.dialog{display:flex;gap:14px;align-items:flex-start;flex-wrap:wrap}
.portrait{flex:0 0 auto;width:92px;background:var(--cream);border:4px solid var(--ink);padding:6px}
.portrait svg{width:100%;aspect-ratio:74/62;display:block;image-rendering:pixelated}
.said{flex:1 1 240px;min-width:0}
.line{border:4px solid var(--ink);padding:10px 12px;margin-bottom:12px;position:relative;overflow-wrap:anywhere;font-size:22px}
.line .who{position:absolute;top:-14px;left:10px;background:var(--ink);color:#fff;font-family:"Press Start 2P","Courier New",monospace;font-size:9px;padding:5px 7px}
.line.lulu{background:#fff6f4;border-color:var(--red)}
.line.lulu .who{background:var(--red)}
.line.lulu::after{content:"\25BC";position:absolute;right:10px;bottom:4px;color:var(--red);font-size:14px;animation:blinkk 1s steps(2) infinite}
.line span{display:block;padding-top:6px}
/* lists */
ul{list-style:none;margin:0;padding:0}
li.row{display:flex;flex-wrap:wrap;align-items:center;gap:8px 12px;padding:10px 0;border-bottom:3px dotted #cfc6bd}
li.row:last-child{border-bottom:0}
.gem{width:16px;height:16px;background:var(--sh);border:3px solid var(--ink);flex:0 0 auto}
.note-ico{color:var(--red);font-size:24px}
.grow{flex:1 1 200px;min-width:0;overflow-wrap:anywhere;font-size:22px}
.grow small{display:block;color:var(--muted);font-size:18px}
form{margin:0;display:inline}
.btn,button,input{font-family:"Press Start 2P","Courier New",monospace;font-size:10px}
button,.btn{background:var(--red);color:#fff;border:3px solid var(--ink);box-shadow:3px 3px 0 var(--ink);padding:10px 12px;cursor:pointer;line-height:1.2}
button:active{transform:translate(3px,3px);box-shadow:0 0 0 var(--ink)}
button.ghost{background:#fff;color:var(--ink)}
input{border:3px solid var(--ink);padding:10px;background:#fff;color:var(--ink);font-size:11px;min-width:0}
button:focus-visible,input:focus-visible{outline:3px solid #f2a29c;outline-offset:2px}
.add{display:flex;flex-wrap:wrap;gap:10px;margin-top:6px}
.add input[name=note]{flex:1 1 220px}
.sub{font-family:"Press Start 2P","Courier New",monospace;font-size:10px;color:var(--ink);margin:18px 0 8px}
.mem{height:20px;border:3px solid var(--ink);background:#fff;margin:14px 0 4px;padding:2px}
.mem i{display:block;height:100%;background:repeating-linear-gradient(90deg,var(--g2) 0 8px,var(--g1) 8px 12px)}
.memtxt{font-size:18px;color:var(--muted);margin:0 0 12px}
.drop{border:4px dashed var(--red);background:#fff4f2;padding:22px 12px;text-align:center;cursor:pointer}
.drop b{display:block;font-family:"Press Start 2P","Courier New",monospace;font-weight:400;font-size:11px;color:var(--red);margin-bottom:10px;line-height:1.6}
#status{font-size:20px;margin:10px 0 0;color:var(--dred);min-height:1em}
/* moods */
.faces{display:grid;grid-template-columns:repeat(auto-fit,minmax(250px,1fr));gap:16px}
.card.face{position:relative;border:4px solid var(--ink);background:#fff;padding:10px}
.card.face h3{margin:10px 0 2px;font-family:"Press Start 2P","Courier New",monospace;font-weight:400;font-size:12px;color:var(--red)}
.card.face .when{font-size:19px;color:var(--ink);margin-bottom:4px}
.card.face p{margin:0;font-size:19px;line-height:1.2;color:#3a312d}
.oled{width:100%;height:auto;display:block;border:3px solid var(--ink);image-rendering:pixelated}
.now{display:none;position:absolute;top:-4px;right:-4px;background:var(--red);color:#fff;font-family:"Press Start 2P","Courier New",monospace;font-size:9px;padding:6px 7px;border:3px solid var(--ink);z-index:2}
.card.face.active{border-color:var(--red);box-shadow:6px 6px 0 var(--red)}
.card.face.active .now{display:block}
.blinkme .e{transform-box:fill-box;transform-origin:center;animation:blink 4.2s infinite}
@keyframes blink{0%,92%,100%{transform:scaleY(1)}95%{transform:scaleY(.12)}}
.pick{margin-top:12px;width:100%;font-size:9px;padding:9px 6px}
.card.face.active .pick{background:var(--ink)}
.ctl{display:flex;flex-wrap:wrap;align-items:center;gap:10px 14px;border:4px solid var(--ink);background:var(--cream);padding:10px 12px;margin:0 0 16px}
.ctl b{font-family:"Press Start 2P","Courier New",monospace;font-weight:400;font-size:10px;color:var(--dred)}
.ctl span{flex:1 1 200px;font-size:19px}
.ctl.manual{background:#ffe0dc;border-color:var(--red)}
.how{margin-top:18px;border:4px solid var(--ink);background:var(--cream);padding:12px;font-size:20px}
.how b{font-family:"Press Start 2P","Courier New",monospace;font-weight:400;font-size:10px;color:var(--dred);display:block;margin-bottom:8px}
footer{position:relative;margin-top:10px;text-align:center;padding:0 14px 26px;color:var(--muted);font-size:18px}
</style></head><body>
<svg width="0" height="0" style="position:absolute" aria-hidden="true"><defs>
<symbol id="lamb" viewBox="0 0 11 8"><rect x="2" y="0" width="7" height="1" fill="#111"/><rect x="1" y="1" width="9" height="1" fill="#111"/><rect x="0" y="2" width="11" height="1" fill="#111"/><rect x="0" y="3" width="11" height="1" fill="#111"/><rect x="1" y="4" width="9" height="1" fill="#111"/><rect x="0" y="5" width="2" height="1" fill="#111"/><rect x="3" y="5" width="5" height="1" fill="#111"/><rect x="9" y="5" width="2" height="1" fill="#111"/><rect x="0" y="6" width="1" height="1" fill="#111"/><rect x="3" y="6" width="5" height="1" fill="#111"/><rect x="10" y="6" width="1" height="1" fill="#111"/><rect x="3" y="7" width="5" height="1" fill="#111"/></symbol>
<symbol id="sheep" viewBox="0 0 74 62"><path d="M32 1h10v1h-10zM32 2h10v1h-10zM28 3h1v1h-1zM30 3h14v1h-14zM45 3h1v1h-1zM23 4h4v1h-4zM29 4h16v1h-16zM47 4h4v1h-4zM23 5h5v1h-5zM29 5h16v1h-16zM46 5h5v1h-5zM23 6h28v1h-28zM19 7h4v1h-4zM27 7h20v1h-20zM51 7h4v1h-4zM18 8h3v1h-3zM25 8h1v1h-1zM33 8h9v1h-9zM48 8h1v1h-1zM53 8h3v1h-3zM17 9h4v1h-4zM24 9h3v1h-3zM35 9h4v1h-4zM47 9h3v1h-3zM53 9h4v1h-4zM16 10h4v1h-4zM22 10h10v1h-10zM35 10h4v1h-4zM42 10h10v1h-10zM54 10h4v1h-4zM15 11h4v1h-4zM20 11h15v1h-15zM36 11h2v1h-2zM39 11h15v1h-15zM55 11h4v1h-4zM15 12h4v1h-4zM20 12h16v1h-16zM38 12h16v1h-16zM55 12h4v1h-4zM15 13h4v1h-4zM20 13h16v1h-16zM38 13h16v1h-16zM55 13h4v1h-4zM12 14h24v1h-24zM38 14h24v1h-24zM12 15h5v1h-5zM19 15h17v1h-17zM38 15h17v1h-17zM57 15h5v1h-5zM12 16h4v1h-4zM18 16h17v1h-17zM39 16h17v1h-17zM58 16h4v1h-4zM11 17h5v1h-5zM18 17h17v1h-17zM36 17h2v1h-2zM39 17h17v1h-17zM58 17h5v1h-5zM9 18h2v1h-2zM13 18h3v1h-3zM18 18h20v1h-20zM39 18h17v1h-17zM58 18h3v1h-3zM63 18h3v1h-3zM8 19h4v1h-4zM16 19h42v1h-42zM62 19h4v1h-4zM7 20h6v1h-6zM16 20h42v1h-42zM61 20h6v1h-6zM7 21h8v1h-8zM17 21h14v1h-14zM43 21h14v1h-14zM59 21h8v1h-8zM6 22h10v1h-10zM18 22h12v1h-12zM45 22h11v1h-11zM58 22h10v1h-10zM6 23h10v1h-10zM18 23h10v1h-10zM46 23h10v1h-10zM58 23h10v1h-10zM5 24h12v1h-12zM19 24h8v1h-8zM47 24h8v1h-8zM57 24h12v1h-12zM4 25h13v1h-13zM22 25h4v1h-4zM48 25h4v1h-4zM57 25h13v1h-13zM4 26h12v1h-12zM18 26h7v1h-7zM49 26h7v1h-7zM58 26h12v1h-12zM4 27h11v1h-11zM17 27h5v1h-5zM52 27h5v1h-5zM59 27h11v1h-11zM5 28h10v1h-10zM16 28h5v1h-5zM31 28h12v1h-12zM50 28h1v1h-1zM53 28h5v1h-5zM59 28h10v1h-10zM6 29h7v1h-7zM15 29h4v1h-4zM31 29h5v1h-5zM38 29h5v1h-5zM55 29h4v1h-4zM61 29h7v1h-7zM6 30h7v1h-7zM15 30h3v1h-3zM31 30h2v1h-2zM34 30h2v1h-2zM38 30h2v1h-2zM41 30h2v1h-2zM56 30h3v1h-3zM61 30h7v1h-7zM6 31h6v1h-6zM14 31h3v1h-3zM30 31h2v1h-2zM35 31h1v1h-1zM38 31h1v1h-1zM42 31h2v1h-2zM57 31h3v1h-3zM62 31h6v1h-6zM7 32h5v1h-5zM14 32h2v1h-2zM31 32h2v1h-2zM34 32h2v1h-2zM38 32h2v1h-2zM41 32h2v1h-2zM58 32h2v1h-2zM62 32h6v1h-6zM3 33h2v1h-2zM7 33h5v1h-5zM14 33h1v1h-1zM18 33h1v1h-1zM31 33h5v1h-5zM38 33h5v1h-5zM55 33h1v1h-1zM59 33h1v1h-1zM62 33h5v1h-5zM69 33h2v1h-2zM3 34h4v1h-4zM8 34h3v1h-3zM13 34h1v1h-1zM17 34h1v1h-1zM33 34h2v1h-2zM39 34h3v1h-3zM60 34h1v1h-1zM63 34h3v1h-3zM67 34h4v1h-4zM3 35h4v1h-4zM8 35h3v1h-3zM12 35h2v1h-2zM25 35h1v1h-1zM48 35h1v1h-1zM60 35h2v1h-2zM63 35h3v1h-3zM67 35h4v1h-4zM3 36h4v1h-4zM9 36h1v1h-1zM24 36h1v1h-1zM49 36h1v1h-1zM64 36h1v1h-1zM67 36h4v1h-4zM2 37h6v1h-6zM11 37h2v1h-2zM23 37h2v1h-2zM49 37h2v1h-2zM61 37h2v1h-2zM66 37h7v1h-7zM2 38h7v1h-7zM11 38h2v1h-2zM22 38h3v1h-3zM27 38h1v1h-1zM46 38h1v1h-1zM49 38h3v1h-3zM61 38h2v1h-2zM65 38h8v1h-8zM2 39h8v1h-8zM11 39h3v1h-3zM21 39h4v1h-4zM27 39h1v1h-1zM46 39h1v1h-1zM49 39h4v1h-4zM60 39h3v1h-3zM64 39h8v1h-8zM3 40h8v1h-8zM13 40h2v1h-2zM19 40h7v1h-7zM48 40h7v1h-7zM59 40h2v1h-2zM63 40h8v1h-8zM3 41h8v1h-8zM13 41h13v1h-13zM48 41h13v1h-13zM63 41h8v1h-8zM3 42h8v1h-8zM15 42h12v1h-12zM47 42h12v1h-12zM63 42h8v1h-8zM3 43h9v1h-9zM15 43h12v1h-12zM31 43h1v1h-1zM42 43h1v1h-1zM47 43h12v1h-12zM62 43h9v1h-9zM4 44h11v1h-11zM16 44h13v1h-13zM45 44h13v1h-13zM59 44h11v1h-11zM4 45h12v1h-12zM22 45h8v1h-8zM44 45h9v1h-9zM58 45h12v1h-12zM6 46h10v1h-10zM21 46h9v1h-9zM44 46h9v1h-9zM58 46h10v1h-10zM6 47h11v1h-11zM19 47h13v1h-13zM42 47h13v1h-13zM57 47h11v1h-11zM6 48h11v1h-11zM19 48h14v1h-14zM41 48h14v1h-14zM57 48h11v1h-11zM7 49h11v1h-11zM20 49h34v1h-34zM56 49h11v1h-11zM8 50h11v1h-11zM21 50h33v1h-33zM55 50h11v1h-11zM9 51h11v1h-11zM22 51h14v1h-14zM38 51h14v1h-14zM54 51h11v1h-11zM10 52h10v1h-10zM23 52h13v1h-13zM38 52h13v1h-13zM54 52h10v1h-10zM15 53h7v1h-7zM23 53h12v1h-12zM39 53h12v1h-12zM52 53h7v1h-7zM15 54h8v1h-8zM25 54h9v1h-9zM36 54h2v1h-2zM40 54h9v1h-9zM51 54h8v1h-8zM16 55h6v1h-6zM28 55h5v1h-5zM35 55h4v1h-4zM41 55h5v1h-5zM52 55h6v1h-6zM19 56h3v1h-3zM29 56h3v1h-3zM34 56h6v1h-6zM42 56h3v1h-3zM52 56h3v1h-3zM33 57h8v1h-8zM12 58h1v1h-1zM61 58h1v1h-1zM23 59h1v1h-1zM50 59h1v1h-1z" fill="#fff"/><path d="M32 0h10v1h-10zM28 1h4v1h-4zM42 1h4v1h-4zM27 2h5v1h-5zM42 2h5v1h-5zM23 3h5v1h-5zM29 3h1v1h-1zM44 3h1v1h-1zM46 3h5v1h-5zM21 4h2v1h-2zM27 4h2v1h-2zM45 4h2v1h-2zM51 4h1v1h-1zM19 5h4v1h-4zM28 5h1v1h-1zM45 5h1v1h-1zM51 5h4v1h-4zM18 6h5v1h-5zM51 6h5v1h-5zM17 7h2v1h-2zM23 7h4v1h-4zM47 7h4v1h-4zM55 7h2v1h-2zM16 8h2v1h-2zM21 8h4v1h-4zM26 8h7v1h-7zM42 8h6v1h-6zM49 8h4v1h-4zM56 8h2v1h-2zM15 9h2v1h-2zM21 9h3v1h-3zM27 9h8v1h-8zM39 9h8v1h-8zM50 9h3v1h-3zM57 9h2v1h-2zM15 10h1v1h-1zM20 10h2v1h-2zM32 10h3v1h-3zM39 10h3v1h-3zM52 10h2v1h-2zM58 10h1v1h-1zM13 11h2v1h-2zM19 11h1v1h-1zM35 11h1v1h-1zM38 11h1v1h-1zM54 11h1v1h-1zM59 11h2v1h-2zM12 12h3v1h-3zM19 12h1v1h-1zM36 12h2v1h-2zM54 12h1v1h-1zM59 12h3v1h-3zM12 13h3v1h-3zM19 13h1v1h-1zM36 13h2v1h-2zM54 13h1v1h-1zM59 13h3v1h-3zM11 14h1v1h-1zM36 14h2v1h-2zM62 14h1v1h-1zM11 15h1v1h-1zM17 15h2v1h-2zM36 15h2v1h-2zM55 15h2v1h-2zM62 15h1v1h-1zM9 16h3v1h-3zM16 16h2v1h-2zM35 16h4v1h-4zM56 16h2v1h-2zM62 16h3v1h-3zM8 17h3v1h-3zM16 17h2v1h-2zM35 17h1v1h-1zM38 17h1v1h-1zM56 17h2v1h-2zM63 17h3v1h-3zM7 18h2v1h-2zM11 18h2v1h-2zM16 18h2v1h-2zM38 18h1v1h-1zM56 18h2v1h-2zM61 18h2v1h-2zM66 18h1v1h-1zM5 19h3v1h-3zM12 19h4v1h-4zM58 19h4v1h-4zM66 19h3v1h-3zM5 20h2v1h-2zM13 20h3v1h-3zM58 20h3v1h-3zM67 20h2v1h-2zM5 21h2v1h-2zM15 21h2v1h-2zM31 21h12v1h-12zM57 21h2v1h-2zM67 21h2v1h-2zM4 22h2v1h-2zM16 22h2v1h-2zM30 22h15v1h-15zM56 22h2v1h-2zM68 22h2v1h-2zM4 23h2v1h-2zM16 23h2v1h-2zM28 23h18v1h-18zM56 23h2v1h-2zM68 23h2v1h-2zM3 24h2v1h-2zM17 24h2v1h-2zM27 24h20v1h-20zM55 24h2v1h-2zM69 24h2v1h-2zM3 25h1v1h-1zM17 25h5v1h-5zM26 25h22v1h-22zM52 25h5v1h-5zM70 25h1v1h-1zM3 26h1v1h-1zM16 26h2v1h-2zM25 26h24v1h-24zM56 26h2v1h-2zM70 26h1v1h-1zM3 27h1v1h-1zM15 27h2v1h-2zM22 27h30v1h-30zM57 27h2v1h-2zM70 27h1v1h-1zM3 28h2v1h-2zM15 28h1v1h-1zM21 28h10v1h-10zM43 28h7v1h-7zM51 28h2v1h-2zM58 28h1v1h-1zM69 28h2v1h-2zM4 29h2v1h-2zM13 29h2v1h-2zM19 29h12v1h-12zM36 29h2v1h-2zM43 29h12v1h-12zM59 29h2v1h-2zM68 29h2v1h-2zM4 30h2v1h-2zM13 30h2v1h-2zM18 30h13v1h-13zM33 30h1v1h-1zM36 30h2v1h-2zM40 30h1v1h-1zM43 30h13v1h-13zM59 30h2v1h-2zM68 30h2v1h-2zM3 31h3v1h-3zM12 31h2v1h-2zM17 31h13v1h-13zM32 31h3v1h-3zM36 31h2v1h-2zM39 31h3v1h-3zM44 31h13v1h-13zM60 31h2v1h-2zM68 31h3v1h-3zM2 32h5v1h-5zM12 32h2v1h-2zM16 32h15v1h-15zM33 32h1v1h-1zM36 32h2v1h-2zM40 32h1v1h-1zM43 32h15v1h-15zM60 32h2v1h-2zM68 32h4v1h-4zM1 33h2v1h-2zM5 33h2v1h-2zM12 33h2v1h-2zM15 33h3v1h-3zM19 33h12v1h-12zM36 33h2v1h-2zM43 33h12v1h-12zM56 33h3v1h-3zM60 33h2v1h-2zM67 33h2v1h-2zM71 33h2v1h-2zM1 34h2v1h-2zM7 34h1v1h-1zM11 34h2v1h-2zM14 34h3v1h-3zM18 34h15v1h-15zM35 34h4v1h-4zM42 34h18v1h-18zM61 34h2v1h-2zM66 34h1v1h-1zM71 34h2v1h-2zM1 35h2v1h-2zM7 35h1v1h-1zM11 35h1v1h-1zM14 35h11v1h-11zM26 35h22v1h-22zM49 35h11v1h-11zM62 35h1v1h-1zM66 35h1v1h-1zM71 35h2v1h-2zM1 36h2v1h-2zM7 36h2v1h-2zM10 36h14v1h-14zM25 36h24v1h-24zM50 36h14v1h-14zM65 36h2v1h-2zM71 36h2v1h-2zM0 37h2v1h-2zM8 37h3v1h-3zM13 37h10v1h-10zM25 37h24v1h-24zM51 37h10v1h-10zM63 37h3v1h-3zM73 37h1v1h-1zM0 38h2v1h-2zM9 38h2v1h-2zM13 38h9v1h-9zM25 38h2v1h-2zM28 38h18v1h-18zM47 38h2v1h-2zM52 38h9v1h-9zM63 38h2v1h-2zM73 38h1v1h-1zM0 39h2v1h-2zM10 39h1v1h-1zM14 39h7v1h-7zM25 39h2v1h-2zM28 39h18v1h-18zM47 39h2v1h-2zM53 39h7v1h-7zM63 39h1v1h-1zM72 39h2v1h-2zM1 40h2v1h-2zM11 40h2v1h-2zM15 40h4v1h-4zM26 40h22v1h-22zM55 40h4v1h-4zM61 40h2v1h-2zM71 40h2v1h-2zM1 41h2v1h-2zM11 41h2v1h-2zM26 41h22v1h-22zM61 41h2v1h-2zM71 41h2v1h-2zM1 42h2v1h-2zM11 42h4v1h-4zM27 42h20v1h-20zM59 42h4v1h-4zM71 42h2v1h-2zM1 43h2v1h-2zM12 43h3v1h-3zM27 43h4v1h-4zM32 43h10v1h-10zM43 43h4v1h-4zM59 43h3v1h-3zM71 43h2v1h-2zM3 44h1v1h-1zM15 44h1v1h-1zM29 44h16v1h-16zM58 44h1v1h-1zM70 44h1v1h-1zM3 45h1v1h-1zM16 45h6v1h-6zM30 45h14v1h-14zM53 45h5v1h-5zM70 45h1v1h-1zM4 46h2v1h-2zM16 46h5v1h-5zM30 46h14v1h-14zM53 46h5v1h-5zM68 46h2v1h-2zM4 47h2v1h-2zM17 47h2v1h-2zM32 47h10v1h-10zM55 47h2v1h-2zM68 47h2v1h-2zM4 48h2v1h-2zM17 48h2v1h-2zM33 48h8v1h-8zM55 48h2v1h-2zM68 48h2v1h-2zM5 49h2v1h-2zM18 49h2v1h-2zM54 49h2v1h-2zM67 49h2v1h-2zM6 50h2v1h-2zM19 50h2v1h-2zM54 50h1v1h-1zM66 50h1v1h-1zM7 51h2v1h-2zM20 51h2v1h-2zM36 51h2v1h-2zM52 51h2v1h-2zM65 51h2v1h-2zM8 52h2v1h-2zM20 52h3v1h-3zM36 52h2v1h-2zM51 52h3v1h-3zM64 52h2v1h-2zM9 53h6v1h-6zM22 53h1v1h-1zM35 53h4v1h-4zM51 53h1v1h-1zM59 53h6v1h-6zM10 54h5v1h-5zM23 54h2v1h-2zM34 54h2v1h-2zM38 54h2v1h-2zM49 54h2v1h-2zM59 54h5v1h-5zM12 55h4v1h-4zM22 55h6v1h-6zM33 55h2v1h-2zM39 55h2v1h-2zM46 55h6v1h-6zM58 55h4v1h-4zM12 56h7v1h-7zM22 56h7v1h-7zM32 56h2v1h-2zM40 56h2v1h-2zM45 56h7v1h-7zM55 56h7v1h-7zM11 57h7v1h-7zM19 57h14v1h-14zM41 57h14v1h-14zM56 57h7v1h-7zM11 58h1v1h-1zM13 58h4v1h-4zM19 58h36v1h-36zM57 58h4v1h-4zM62 58h1v1h-1zM11 59h6v1h-6zM21 59h2v1h-2zM24 59h5v1h-5zM32 59h10v1h-10zM45 59h5v1h-5zM51 59h2v1h-2zM57 59h6v1h-6zM11 60h6v1h-6zM21 60h8v1h-8zM45 60h8v1h-8zM57 60h6v1h-6zM22 61h7v1h-7zM45 61h7v1h-7z" fill="#111"/></symbol>
<symbol id="shroom" viewBox="0 0 13 13"><rect x="4" y="0" width="5" height="1" fill="#3b1740"/><rect x="2" y="1" width="2" height="1" fill="#3b1740"/><rect x="4" y="1" width="5" height="1" fill="#e0403e"/><rect x="9" y="1" width="2" height="1" fill="#3b1740"/><rect x="1" y="2" width="1" height="1" fill="#3b1740"/><rect x="2" y="2" width="3" height="1" fill="#e0403e"/><rect x="5" y="2" width="1" height="1" fill="#ffd5d5"/><rect x="6" y="2" width="5" height="1" fill="#e0403e"/><rect x="11" y="2" width="1" height="1" fill="#3b1740"/><rect x="1" y="3" width="1" height="1" fill="#3b1740"/><rect x="2" y="3" width="1" height="1" fill="#e0403e"/><rect x="3" y="3" width="3" height="1" fill="#ffd5d5"/><rect x="6" y="3" width="3" height="1" fill="#e0403e"/><rect x="9" y="3" width="1" height="1" fill="#ffd5d5"/><rect x="10" y="3" width="1" height="1" fill="#e0403e"/><rect x="11" y="3" width="1" height="1" fill="#3b1740"/><rect x="0" y="4" width="1" height="1" fill="#3b1740"/><rect x="1" y="4" width="3" height="1" fill="#e0403e"/><rect x="4" y="4" width="1" height="1" fill="#ffd5d5"/><rect x="5" y="4" width="3" height="1" fill="#e0403e"/><rect x="8" y="4" width="3" height="1" fill="#ffd5d5"/><rect x="11" y="4" width="1" height="1" fill="#e0403e"/><rect x="12" y="4" width="1" height="1" fill="#3b1740"/><rect x="0" y="5" width="1" height="1" fill="#3b1740"/><rect x="1" y="5" width="8" height="1" fill="#e0403e"/><rect x="9" y="5" width="1" height="1" fill="#ffd5d5"/><rect x="10" y="5" width="2" height="1" fill="#e0403e"/><rect x="12" y="5" width="1" height="1" fill="#3b1740"/><rect x="0" y="6" width="1" height="1" fill="#3b1740"/><rect x="1" y="6" width="1" height="1" fill="#e0403e"/><rect x="2" y="6" width="1" height="1" fill="#ffd5d5"/><rect x="3" y="6" width="9" height="1" fill="#e0403e"/><rect x="12" y="6" width="1" height="1" fill="#3b1740"/><rect x="0" y="7" width="13" height="1" fill="#3b1740"/><rect x="4" y="8" width="1" height="1" fill="#3b1740"/><rect x="5" y="8" width="3" height="1" fill="#f0dcae"/><rect x="8" y="8" width="1" height="1" fill="#3b1740"/><rect x="4" y="9" width="1" height="1" fill="#3b1740"/><rect x="5" y="9" width="3" height="1" fill="#f0dcae"/><rect x="8" y="9" width="1" height="1" fill="#3b1740"/><rect x="4" y="10" width="1" height="1" fill="#3b1740"/><rect x="5" y="10" width="3" height="1" fill="#f0dcae"/><rect x="8" y="10" width="1" height="1" fill="#3b1740"/><rect x="3" y="11" width="1" height="1" fill="#3b1740"/><rect x="4" y="11" width="5" height="1" fill="#f0dcae"/><rect x="9" y="11" width="1" height="1" fill="#3b1740"/><rect x="3" y="12" width="7" height="1" fill="#3b1740"/></symbol>
</defs></svg>
<nav><a href="#chat">CHAT</a><a href="#quests">QUESTS</a><a href="#jukebox">JUKEBOX</a><a href="#moods">MOODS</a></nav>
<header class="hero">
<div class="eyebrow">ESP32-S3 SHEEP ROBOT<br>LULU HOME &bull; PLAYER 1</div>
<h1 class="title"><span>Sheep</span><span>Lulu</span></h1>
<div class="start">PRESS START</div>
<div class="addr">http://)LULU";
  page += WiFi.localIP().toString();
  page += R"LULU(/</div>
<div class="live"><svg class="oled " id="live" viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><rect class="e el" x="28" y="17" width="26" height="30" rx="7" fill="#fff"/><rect class="e er" x="74" y="17" width="26" height="30" rx="7" fill="#fff"/></svg><div><b id="liveName">NORMAL</b><small id="modeTxt">live face</small></div></div>
</header>
<div class="wrap"><div class="side l"><svg viewBox="0 0 11 8"><use href="#lamb"/></svg><svg viewBox="0 0 11 8"><use href="#lamb"/></svg><svg viewBox="0 0 11 8"><use href="#lamb"/></svg><svg viewBox="0 0 11 8"><use href="#lamb"/></svg><svg viewBox="0 0 11 8"><use href="#lamb"/></svg><svg viewBox="0 0 11 8"><use href="#lamb"/></svg><svg viewBox="0 0 11 8"><use href="#lamb"/></svg><svg viewBox="0 0 11 8"><use href="#lamb"/></svg></div><div class="side r"><svg viewBox="0 0 11 8"><use href="#lamb"/></svg><svg viewBox="0 0 11 8"><use href="#lamb"/></svg><svg viewBox="0 0 11 8"><use href="#lamb"/></svg><svg viewBox="0 0 11 8"><use href="#lamb"/></svg><svg viewBox="0 0 11 8"><use href="#lamb"/></svg><svg viewBox="0 0 11 8"><use href="#lamb"/></svg><svg viewBox="0 0 11 8"><use href="#lamb"/></svg><svg viewBox="0 0 11 8"><use href="#lamb"/></svg></div>
<main>
<div class="win" id="chat"><h2>CHAT LOG<span>LIVE</span></h2><div class="body">
<div class="dialog"><div class="portrait"><svg viewBox="0 0 74 62"><use href="#sheep"/></svg></div>
<div class="said"><div class="line"><div class="who">YOU</div><span id="heard">)LULU";
  page += htmlEscape(latestHeardText.length() ? latestHeardText : "Nothing heard yet");
  page += R"LULU(</span></div><div class="line lulu"><div class="who">LULU</div><span id="reply">)LULU";
  page += htmlEscape(latestReplyText.length() ? latestReplyText : "No answer yet");
  page += R"LULU(</span></div></div></div>
<p class="note" style="margin:6px 0 0">The last thing she heard and her answer. Check here if you missed it.</p></div></div>
<div class="win" id="quests"><h2>QUESTS<span>REMINDERS &amp; TIMERS</span></h2><div class="body"><ul>)LULU";
  int count = 0;
  for (int i = 0; i < MAX_ALERTS; ++i) {
    if (!alerts[i].active) continue;
    ++count;
    String detail;
    if (alerts[i].timer) {
      int32_t remain = ((int32_t)(alerts[i].dueMillis - millis()) + 999) / 1000;
      detail = "Timer: " + String(max((int32_t)0, remain)) + " s left";
    } else {
      struct tm value; localtime_r(&alerts[i].dueEpoch, &value);
      char when[32]; strftime(when, sizeof(when), "%Y-%m-%d %H:%M", &value);
      detail = when;
    }
    page += "<li class='row'><span class='gem'></span><span class='grow'><b>" + htmlEscape(alerts[i].note) + "</b><small>" + detail + "</small></span>";
    page += "<form method='post' action='/delete-reminder'><input type='hidden' name='id' value='" + String(i) + "'><button class='ghost'>DEL</button></form></li>";
  }
  if (!count) page += F("<li class='row'><span class='grow'><small>No saved reminders or timers.</small></span></li>");
  page += R"LULU(</ul>
<div class="sub">NEW QUEST</div>
<form class="add" method="post" action="/add-reminder"><input required name="note" maxlength="80" placeholder="What to remember?"><input required type="datetime-local" name="when"><button>SAVE</button></form>
<form style="display:block;margin-top:14px" method="post" action="/clear-reminders" onsubmit="return confirm('Delete all reminders?')"><button class="ghost" type="submit">CLEAR ALL</button></form>
</div></div>
<div class="win" id="jukebox"><h2>JUKEBOX<span>MP3 / WAV</span></h2><div class="body">
<p class="note">Say &ldquo;Lulu, sing a song&rdquo; or press PLAY. Press the BOOT button or pat her head to stop.</p><ul>)LULU";
  int songs = 0;
  if (luluStorageReady) {
    File dir = FFat.open("/songs");
    File file = dir ? dir.openNextFile() : File();
    while (file) {
      if (!file.isDirectory()) {
        String full = file.name();
        String name = full.substring(full.lastIndexOf('/') + 1);
        ++songs;
        page += "<li class='row'><span class='note-ico'>&#9835;</span><span class='grow'><b>" + htmlEscape(name) + "</b><small>" + String((unsigned)(file.size() / 1024)) + " KB</small></span>";
        page += "<form method='post' action='/play-song'><input type='hidden' name='name' value='" + htmlEscape(name) + "'><button>PLAY</button></form>";
        page += "<form method='post' action='/delete-song'><input type='hidden' name='name' value='" + htmlEscape(name) + "'><button class='ghost'>DEL</button></form></li>";
      }
      file = dir.openNextFile();
    }
    if (dir) dir.close();
  }
  if (!songs) page += F("<li class='row'><span class='grow'><small>No songs uploaded yet.</small></span></li>");
  page += R"LULU(</ul>)LULU";
  if (luluStorageReady) {
    unsigned long total = FFat.totalBytes() / 1024, used = (FFat.totalBytes() - FFat.freeBytes()) / 1024;
    int pct = total ? (int)(used * 100 / total) : 0;
    page += "<div class='mem'><i style='width:" + String(pct) + "%'></i></div><p class='memtxt'>MEMORY " + String(used) + " KB used / " + String(total) + " KB</p>";
  } else {
    page += F("<p class='memtxt'>MEMORY: storage not available. Check the partition scheme.</p>");
  }
  page += R"LULU(
<div class="drop" id="drop"><b>INSERT CARTRIDGE</b>Drop an MP3 or WAV here, or tap to choose a file<input id="pick" type="file" accept=".mp3,.wav,audio/mpeg,audio/wav" hidden></div>
<p id="status"></p></div></div>
<div class="win" id="moods"><h2>MOODS<span>PICK A FACE</span></h2><div class="body">
<div class="ctl" id="ctl"><b id="modeTag">AUTO</b><span id="modeMsg">Lulu chooses her own face. Press SHOW ON LULU under any face to put it on her screen.</span><button type="button" id="autoBtn" class="ghost">BACK TO AUTO</button></div>
<p class="note">Lulu has no mouth. Her feelings live in her two eyes on a 128&times;64 OLED: rounded blocks that stretch, squash, slant and sometimes turn into hearts, stars or crosses. The card marked NOW is her face right this second.</p>
<div class="faces"><div class="card face" data-face="0"><span class="now">NOW</span><svg class="oled blinkme"  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><rect class="e el" x="28" y="17" width="26" height="30" rx="7" fill="#fff"/><rect class="e er" x="74" y="17" width="26" height="30" rx="7" fill="#fff"/></svg><h3>Normal</h3><div class="when">Idle &amp; waiting</div><p>Two equal, upright eyes. The neutral resting state while she waits for her name, a pat or a hand. Every few seconds she blinks.</p><button type="button" class="pick" data-f="0">SHOW ON LULU</button></div><div class="card face" data-face="1"><span class="now">NOW</span><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><rect class="e el" x="28" y="13" width="26" height="36" rx="7" fill="#fff"/><rect class="e er" x="74" y="13" width="26" height="36" rx="7" fill="#fff"/></svg><h3>Listening</h3><div class="when">Taking in your voice</div><p>Eyes grow taller and sit a little higher: wide open and attentive. Shown while the microphone is capturing you.</p><button type="button" class="pick" data-f="1">SHOW ON LULU</button></div><div class="card face" data-face="2"><span class="now">NOW</span><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><rect class="e el" x="28" y="20" width="26" height="24" rx="7" fill="#fff"/><rect class="e er" x="74" y="15" width="26" height="34" rx="7" fill="#fff"/></svg><h3>Thinking</h3><div class="when">Waiting for the AI</div><p>Uneven eyes, small and low on the left, big and high on the right. A lopsided, head-tilted ponder.</p><button type="button" class="pick" data-f="2">SHOW ON LULU</button></div><div class="card face" data-face="3"><span class="now">NOW</span><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><rect class="e el" x="28" y="22" width="26" height="20" rx="9" fill="#fff"/><rect class="e er" x="74" y="22" width="26" height="20" rx="9" fill="#fff"/></svg><h3>Happy</h3><div class="when">Speaking &amp; reacting</div><p>Shorter, rounder eyes, like a smile pushing the cheeks up. Shown when she speaks, gets patted, greets you or sings.</p><button type="button" class="pick" data-f="3">SHOW ON LULU</button></div><div class="card face" data-face="4"><span class="now">NOW</span><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><rect class="e el" x="28" y="30" width="26" height="5" rx="2" fill="#fff"/><rect class="e er" x="74" y="30" width="26" height="5" rx="2" fill="#fff"/></svg><h3>Sleepy</h3><div class="when">Bleat &amp; blink</div><p>Eyes squeezed into thin slits. Used for the bleat after a head pat and for the quick blink in between.</p><button type="button" class="pick" data-f="4">SHOW ON LULU</button></div><div class="card face" data-face="5"><span class="now">NOW</span><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><rect x="28" y="17" width="26" height="30" rx="7" fill="#fff"/><rect x="74" y="17" width="26" height="30" rx="7" fill="#fff"/><polygon points="26,13 56,13 56,31" fill="#0c0c0c"/><polygon points="72,13 102,13 72,31" fill="#0c0c0c"/></svg><h3>Angry</h3><div class="when">Pushed too far</div><p>Eyes slant down toward the middle. Shown when you keep patting her head and she has had enough.</p><button type="button" class="pick" data-f="5">SHOW ON LULU</button></div><div class="card face" data-face="6"><span class="now">NOW</span><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><rect x="28" y="20" width="26" height="30" rx="7" fill="#fff"/><rect x="74" y="20" width="26" height="30" rx="7" fill="#fff"/><polygon points="26,16 56,16 26,34" fill="#0c0c0c"/><polygon points="72,16 102,16 102,34" fill="#0c0c0c"/></svg><h3>Sad</h3><div class="when">Nobody answered</div><p>Eyes droop at the outer corners. Shown when she says sorry or does not know, and when she woke up and heard nothing.</p><button type="button" class="pick" data-f="6">SHOW ON LULU</button></div><div class="card face" data-face="7"><span class="now">NOW</span><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><circle cx="35" cy="21" r="7" fill="#fff"/><circle cx="47" cy="21" r="7" fill="#fff"/><polygon points="28,23 54,23 41,37" fill="#fff"/><circle cx="81" cy="21" r="7" fill="#fff"/><circle cx="93" cy="21" r="7" fill="#fff"/><polygon points="74,23 100,23 87,37" fill="#fff"/></svg><h3>Love</h3><div class="when">Singing or snuggling</div><p>Two hearts. Shown when she says thanks or love, with a slow head sway, and while singing.</p><button type="button" class="pick" data-f="7">SHOW ON LULU</button></div><div class="card face" data-face="8"><span class="now">NOW</span><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><rect x="30" y="10" width="22" height="44" rx="10" fill="#fff"/><rect x="76" y="10" width="22" height="44" rx="10" fill="#fff"/><circle cx="41" cy="29" r="3" fill="#0c0c0c"/><circle cx="87" cy="29" r="3" fill="#0c0c0c"/></svg><h3>Surprised</h3><div class="when">Wow!</div><p>Tall, narrow eyes with a dot in the middle. Shown when her answer says wow, with a quick head lift.</p><button type="button" class="pick" data-f="8">SHOW ON LULU</button></div><div class="card face" data-face="9"><span class="now">NOW</span><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><rect x="28" y="17" width="26" height="30" rx="7" fill="#fff"/><polyline points="76,32 98,24" fill="none" stroke="#fff" stroke-width="4" stroke-linecap="square" stroke-linejoin="miter"/><polyline points="76,32 98,40" fill="none" stroke="#fff" stroke-width="4" stroke-linecap="square" stroke-linejoin="miter"/></svg><h3>Wink</h3><div class="when">Cheeky hello</div><p>One eye open, one squeezed shut. The first greeting after a head pat ends with a wink.</p><button type="button" class="pick" data-f="9">SHOW ON LULU</button></div><div class="card face" data-face="10"><span class="now">NOW</span><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><polyline points="28,40 35,31 41,28 47,31 54,40" fill="none" stroke="#fff" stroke-width="4" stroke-linecap="square" stroke-linejoin="miter"/><polyline points="74,40 81,31 87,28 93,31 100,40" fill="none" stroke="#fff" stroke-width="4" stroke-linecap="square" stroke-linejoin="miter"/></svg><h3>Joy</h3><div class="when">Happy ^ ^</div><p>Two upside-down smile arcs. Part of her singing dance.</p><button type="button" class="pick" data-f="10">SHOW ON LULU</button></div><div class="card face" data-face="11"><span class="now">NOW</span><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><polyline points="30,20 52,42" fill="none" stroke="#fff" stroke-width="4" stroke-linecap="square" stroke-linejoin="miter"/><polyline points="30,42 52,20" fill="none" stroke="#fff" stroke-width="4" stroke-linecap="square" stroke-linejoin="miter"/><polyline points="76,20 98,42" fill="none" stroke="#fff" stroke-width="4" stroke-linecap="square" stroke-linejoin="miter"/><polyline points="76,42 98,20" fill="none" stroke="#fff" stroke-width="4" stroke-linecap="square" stroke-linejoin="miter"/></svg><h3>Dizzy</h3><div class="when">Too many pats</div><p>Two crosses. Appears when she has been patted over and over.</p><button type="button" class="pick" data-f="11">SHOW ON LULU</button></div><div class="card face" data-face="12"><span class="now">NOW</span><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><polygon points="38,31 44,31 41,14" fill="#fff"/><polygon points="38,31 44,31 41,48" fill="#fff"/><polygon points="41,28 41,34 24,31" fill="#fff"/><polygon points="41,28 41,34 58,31" fill="#fff"/><rect x="38" y="28" width="6" height="6" fill="#fff"/><polygon points="84,31 90,31 87,14" fill="#fff"/><polygon points="84,31 90,31 87,48" fill="#fff"/><polygon points="87,28 87,34 70,31" fill="#fff"/><polygon points="87,28 87,34 104,31" fill="#fff"/><rect x="84" y="28" width="6" height="6" fill="#fff"/><circle cx="6" cy="8" r="2" fill="#fff"/><circle cx="121" cy="53" r="2" fill="#fff"/></svg><h3>Starry</h3><div class="when">Sparkly eyes</div><p>Four-point stars. Shown for great news with a head bounce, and while singing.</p><button type="button" class="pick" data-f="12">SHOW ON LULU</button></div><div class="card face" data-face="13"><span class="now">NOW</span><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><rect x="28" y="14" width="26" height="28" rx="7" fill="#fff"/><rect x="74" y="14" width="26" height="28" rx="7" fill="#fff"/><polygon points="26,10 56,10 26,26" fill="#0c0c0c"/><polygon points="72,10 102,10 102,26" fill="#0c0c0c"/><polygon points="34,46 30,53 38,53" fill="#fff"/><circle cx="34" cy="54" r="4" fill="#fff"/><polygon points="94,46 90,53 98,53" fill="#fff"/><circle cx="94" cy="54" r="4" fill="#fff"/></svg><h3>Crying</h3><div class="when">Something went wrong</div><p>Sad eyes with two tears. Shown when speech recognition fails.</p><button type="button" class="pick" data-f="13">SHOW ON LULU</button></div><div class="card face" data-face="14"><span class="now">NOW</span><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><rect x="28" y="22" width="26" height="26" rx="7" fill="#fff"/><rect x="74" y="22" width="26" height="26" rx="7" fill="#fff"/><rect x="26" y="18" width="30" height="16" fill="#0c0c0c"/><rect x="72" y="18" width="30" height="16" fill="#0c0c0c"/></svg><h3>Tired</h3><div class="when">Sleepy lids</div><p>Heavy flat eyelids. Shown for good night or rest, with a slow head droop.</p><button type="button" class="pick" data-f="14">SHOW ON LULU</button></div><div class="card face" data-face="15"><span class="now">NOW</span><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><rect x="30" y="28" width="22" height="14" rx="6" fill="#fff"/><rect x="76" y="28" width="22" height="14" rx="6" fill="#fff"/><line x1="20" y1="54" x2="23" y2="49" stroke="#fff" stroke-width="1.5"/><line x1="24" y1="54" x2="27" y2="49" stroke="#fff" stroke-width="1.5"/><line x1="28" y1="54" x2="31" y2="49" stroke="#fff" stroke-width="1.5"/><line x1="102" y1="54" x2="105" y2="49" stroke="#fff" stroke-width="1.5"/><line x1="106" y1="54" x2="109" y2="49" stroke="#fff" stroke-width="1.5"/><line x1="110" y1="54" x2="113" y2="49" stroke="#fff" stroke-width="1.5"/></svg><h3>Shy</h3><div class="when">Touched again</div><p>Small eyes looking down with blush marks on the cheeks. Shown when you pat her a second or third time.</p><button type="button" class="pick" data-f="15">SHOW ON LULU</button></div><div class="card face" data-face="16"><span class="now">NOW</span><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><polyline points="30,18 50,31 30,44" fill="none" stroke="#fff" stroke-width="4" stroke-linecap="square" stroke-linejoin="miter"/><polyline points="98,18 78,31 98,44" fill="none" stroke="#fff" stroke-width="4" stroke-linecap="square" stroke-linejoin="miter"/></svg><h3>Laugh</h3><div class="when">Giggling &gt; &lt;</div><p>Two squeezed-shut chevrons. Shown when her answer is funny, with a head shake, and in her singing dance.</p><button type="button" class="pick" data-f="16">SHOW ON LULU</button></div><div class="card face gaze"><svg class="oled "  viewBox="0 0 128 64" role="img"><rect width="128" height="64" fill="#0c0c0c"/><rect class="e el" x="40" y="17" width="26" height="30" rx="7" fill="#fff"/><rect class="e er" x="86" y="17" width="26" height="30" rx="7" fill="#fff"/></svg><h3>Gaze</h3><div class="when">Following your hand</div><p>When a hand comes into range, both eyes slide 12 pixels toward it while the head turns. It works on top of any of the faces.</p></div></div>
<div class="how"><b>HOW TO READ THEM</b>Taller eyes mean attention. Shorter, rounder eyes mean joy. Slits mean sleepy or blinking. Uneven eyes mean thinking. The head adds body language: it turns and tilts toward your hand, and it nods when you pat it.</div>
</div></div>
</main></div>
<footer class="lawn"><div class="note2">Lulu runs on an ESP32-S3 &bull; the chat and live face refresh every 1.5 s</div><svg class="hillsvg" viewBox="0 0 120 30" preserveAspectRatio="none" shape-rendering="crispEdges" aria-hidden="true"><rect x="0" y="6" width="1" height="1" fill="#a8d45a"/><rect x="0" y="7" width="1" height="2" fill="#7fb03a"/><rect x="0" y="9" width="1" height="21" fill="#5f9430"/><rect x="1" y="7" width="1" height="1" fill="#a8d45a"/><rect x="1" y="8" width="1" height="2" fill="#7fb03a"/><rect x="1" y="10" width="1" height="20" fill="#5f9430"/><rect x="2" y="8" width="1" height="1" fill="#a8d45a"/><rect x="2" y="9" width="1" height="2" fill="#7fb03a"/><rect x="2" y="11" width="1" height="19" fill="#5f9430"/><rect x="3" y="8" width="1" height="1" fill="#a8d45a"/><rect x="3" y="9" width="1" height="2" fill="#7fb03a"/><rect x="3" y="11" width="1" height="19" fill="#5f9430"/><rect x="4" y="8" width="1" height="1" fill="#a8d45a"/><rect x="4" y="9" width="1" height="2" fill="#7fb03a"/><rect x="4" y="11" width="1" height="19" fill="#5f9430"/><rect x="5" y="9" width="1" height="1" fill="#a8d45a"/><rect x="5" y="10" width="1" height="2" fill="#7fb03a"/><rect x="5" y="12" width="1" height="18" fill="#5f9430"/><rect x="6" y="9" width="1" height="1" fill="#a8d45a"/><rect x="6" y="10" width="1" height="2" fill="#7fb03a"/><rect x="6" y="12" width="1" height="18" fill="#5f9430"/><rect x="7" y="9" width="1" height="1" fill="#a8d45a"/><rect x="7" y="10" width="1" height="2" fill="#7fb03a"/><rect x="7" y="12" width="1" height="18" fill="#5f9430"/><rect x="8" y="9" width="1" height="1" fill="#a8d45a"/><rect x="8" y="10" width="1" height="2" fill="#7fb03a"/><rect x="8" y="12" width="1" height="18" fill="#5f9430"/><rect x="9" y="9" width="1" height="1" fill="#a8d45a"/><rect x="9" y="10" width="1" height="2" fill="#7fb03a"/><rect x="9" y="12" width="1" height="18" fill="#5f9430"/><rect x="10" y="9" width="1" height="1" fill="#a8d45a"/><rect x="10" y="10" width="1" height="2" fill="#7fb03a"/><rect x="10" y="12" width="1" height="18" fill="#5f9430"/><rect x="11" y="9" width="1" height="1" fill="#a8d45a"/><rect x="11" y="10" width="1" height="2" fill="#7fb03a"/><rect x="11" y="12" width="1" height="18" fill="#5f9430"/><rect x="12" y="9" width="1" height="1" fill="#a8d45a"/><rect x="12" y="10" width="1" height="2" fill="#7fb03a"/><rect x="12" y="12" width="1" height="18" fill="#5f9430"/><rect x="13" y="9" width="1" height="1" fill="#a8d45a"/><rect x="13" y="10" width="1" height="2" fill="#7fb03a"/><rect x="13" y="12" width="1" height="18" fill="#5f9430"/><rect x="14" y="9" width="1" height="1" fill="#a8d45a"/><rect x="14" y="10" width="1" height="2" fill="#7fb03a"/><rect x="14" y="12" width="1" height="18" fill="#5f9430"/><rect x="15" y="10" width="1" height="1" fill="#a8d45a"/><rect x="15" y="11" width="1" height="2" fill="#7fb03a"/><rect x="15" y="13" width="1" height="17" fill="#5f9430"/><rect x="16" y="10" width="1" height="1" fill="#a8d45a"/><rect x="16" y="11" width="1" height="2" fill="#7fb03a"/><rect x="16" y="13" width="1" height="17" fill="#5f9430"/><rect x="17" y="10" width="1" height="1" fill="#a8d45a"/><rect x="17" y="11" width="1" height="2" fill="#7fb03a"/><rect x="17" y="13" width="1" height="17" fill="#5f9430"/><rect x="18" y="10" width="1" height="1" fill="#a8d45a"/><rect x="18" y="11" width="1" height="2" fill="#7fb03a"/><rect x="18" y="13" width="1" height="17" fill="#5f9430"/><rect x="19" y="10" width="1" height="1" fill="#a8d45a"/><rect x="19" y="11" width="1" height="2" fill="#7fb03a"/><rect x="19" y="13" width="1" height="17" fill="#5f9430"/><rect x="20" y="10" width="1" height="1" fill="#a8d45a"/><rect x="20" y="11" width="1" height="2" fill="#7fb03a"/><rect x="20" y="13" width="1" height="17" fill="#5f9430"/><rect x="21" y="11" width="1" height="1" fill="#a8d45a"/><rect x="21" y="12" width="1" height="2" fill="#7fb03a"/><rect x="21" y="14" width="1" height="16" fill="#5f9430"/><rect x="22" y="12" width="1" height="1" fill="#a8d45a"/><rect x="22" y="13" width="1" height="2" fill="#7fb03a"/><rect x="22" y="15" width="1" height="15" fill="#5f9430"/><rect x="23" y="12" width="1" height="1" fill="#a8d45a"/><rect x="23" y="13" width="1" height="2" fill="#7fb03a"/><rect x="23" y="15" width="1" height="15" fill="#5f9430"/><rect x="24" y="12" width="1" height="1" fill="#a8d45a"/><rect x="24" y="13" width="1" height="2" fill="#7fb03a"/><rect x="24" y="15" width="1" height="15" fill="#5f9430"/><rect x="25" y="12" width="1" height="1" fill="#a8d45a"/><rect x="25" y="13" width="1" height="2" fill="#7fb03a"/><rect x="25" y="15" width="1" height="15" fill="#5f9430"/><rect x="26" y="12" width="1" height="1" fill="#a8d45a"/><rect x="26" y="13" width="1" height="2" fill="#7fb03a"/><rect x="26" y="15" width="1" height="15" fill="#5f9430"/><rect x="27" y="11" width="1" height="1" fill="#a8d45a"/><rect x="27" y="12" width="1" height="2" fill="#7fb03a"/><rect x="27" y="14" width="1" height="16" fill="#5f9430"/><rect x="28" y="12" width="1" height="1" fill="#a8d45a"/><rect x="28" y="13" width="1" height="2" fill="#7fb03a"/><rect x="28" y="15" width="1" height="15" fill="#5f9430"/><rect x="29" y="12" width="1" height="1" fill="#a8d45a"/><rect x="29" y="13" width="1" height="2" fill="#7fb03a"/><rect x="29" y="15" width="1" height="15" fill="#5f9430"/><rect x="30" y="12" width="1" height="1" fill="#a8d45a"/><rect x="30" y="13" width="1" height="2" fill="#7fb03a"/><rect x="30" y="15" width="1" height="15" fill="#5f9430"/><rect x="31" y="11" width="1" height="1" fill="#a8d45a"/><rect x="31" y="12" width="1" height="2" fill="#7fb03a"/><rect x="31" y="14" width="1" height="16" fill="#5f9430"/><rect x="32" y="11" width="1" height="1" fill="#a8d45a"/><rect x="32" y="12" width="1" height="2" fill="#7fb03a"/><rect x="32" y="14" width="1" height="16" fill="#5f9430"/><rect x="33" y="10" width="1" height="1" fill="#a8d45a"/><rect x="33" y="11" width="1" height="2" fill="#7fb03a"/><rect x="33" y="13" width="1" height="17" fill="#5f9430"/><rect x="34" y="10" width="1" height="1" fill="#a8d45a"/><rect x="34" y="11" width="1" height="2" fill="#7fb03a"/><rect x="34" y="13" width="1" height="17" fill="#5f9430"/><rect x="35" y="9" width="1" height="1" fill="#a8d45a"/><rect x="35" y="10" width="1" height="2" fill="#7fb03a"/><rect x="35" y="12" width="1" height="18" fill="#5f9430"/><rect x="36" y="9" width="1" height="1" fill="#a8d45a"/><rect x="36" y="10" width="1" height="2" fill="#7fb03a"/><rect x="36" y="12" width="1" height="18" fill="#5f9430"/><rect x="37" y="8" width="1" height="1" fill="#a8d45a"/><rect x="37" y="9" width="1" height="2" fill="#7fb03a"/><rect x="37" y="11" width="1" height="19" fill="#5f9430"/><rect x="38" y="9" width="1" height="1" fill="#a8d45a"/><rect x="38" y="10" width="1" height="2" fill="#7fb03a"/><rect x="38" y="12" width="1" height="18" fill="#5f9430"/><rect x="39" y="9" width="1" height="1" fill="#a8d45a"/><rect x="39" y="10" width="1" height="2" fill="#7fb03a"/><rect x="39" y="12" width="1" height="18" fill="#5f9430"/><rect x="40" y="9" width="1" height="1" fill="#a8d45a"/><rect x="40" y="10" width="1" height="2" fill="#7fb03a"/><rect x="40" y="12" width="1" height="18" fill="#5f9430"/><rect x="41" y="9" width="1" height="1" fill="#a8d45a"/><rect x="41" y="10" width="1" height="2" fill="#7fb03a"/><rect x="41" y="12" width="1" height="18" fill="#5f9430"/><rect x="42" y="9" width="1" height="1" fill="#a8d45a"/><rect x="42" y="10" width="1" height="2" fill="#7fb03a"/><rect x="42" y="12" width="1" height="18" fill="#5f9430"/><rect x="43" y="9" width="1" height="1" fill="#a8d45a"/><rect x="43" y="10" width="1" height="2" fill="#7fb03a"/><rect x="43" y="12" width="1" height="18" fill="#5f9430"/><rect x="44" y="9" width="1" height="1" fill="#a8d45a"/><rect x="44" y="10" width="1" height="2" fill="#7fb03a"/><rect x="44" y="12" width="1" height="18" fill="#5f9430"/><rect x="45" y="10" width="1" height="1" fill="#a8d45a"/><rect x="45" y="11" width="1" height="2" fill="#7fb03a"/><rect x="45" y="13" width="1" height="17" fill="#5f9430"/><rect x="46" y="10" width="1" height="1" fill="#a8d45a"/><rect x="46" y="11" width="1" height="2" fill="#7fb03a"/><rect x="46" y="13" width="1" height="17" fill="#5f9430"/><rect x="47" y="10" width="1" height="1" fill="#a8d45a"/><rect x="47" y="11" width="1" height="2" fill="#7fb03a"/><rect x="47" y="13" width="1" height="17" fill="#5f9430"/><rect x="48" y="11" width="1" height="1" fill="#a8d45a"/><rect x="48" y="12" width="1" height="2" fill="#7fb03a"/><rect x="48" y="14" width="1" height="16" fill="#5f9430"/><rect x="49" y="11" width="1" height="1" fill="#a8d45a"/><rect x="49" y="12" width="1" height="2" fill="#7fb03a"/><rect x="49" y="14" width="1" height="16" fill="#5f9430"/><rect x="50" y="12" width="1" height="1" fill="#a8d45a"/><rect x="50" y="13" width="1" height="2" fill="#7fb03a"/><rect x="50" y="15" width="1" height="15" fill="#5f9430"/><rect x="51" y="12" width="1" height="1" fill="#a8d45a"/><rect x="51" y="13" width="1" height="2" fill="#7fb03a"/><rect x="51" y="15" width="1" height="15" fill="#5f9430"/><rect x="52" y="12" width="1" height="1" fill="#a8d45a"/><rect x="52" y="13" width="1" height="2" fill="#7fb03a"/><rect x="52" y="15" width="1" height="15" fill="#5f9430"/><rect x="53" y="12" width="1" height="1" fill="#a8d45a"/><rect x="53" y="13" width="1" height="2" fill="#7fb03a"/><rect x="53" y="15" width="1" height="15" fill="#5f9430"/><rect x="54" y="13" width="1" height="1" fill="#a8d45a"/><rect x="54" y="14" width="1" height="2" fill="#7fb03a"/><rect x="54" y="16" width="1" height="14" fill="#5f9430"/><rect x="55" y="13" width="1" height="1" fill="#a8d45a"/><rect x="55" y="14" width="1" height="2" fill="#7fb03a"/><rect x="55" y="16" width="1" height="14" fill="#5f9430"/><rect x="56" y="13" width="1" height="1" fill="#a8d45a"/><rect x="56" y="14" width="1" height="2" fill="#7fb03a"/><rect x="56" y="16" width="1" height="14" fill="#5f9430"/><rect x="57" y="13" width="1" height="1" fill="#a8d45a"/><rect x="57" y="14" width="1" height="2" fill="#7fb03a"/><rect x="57" y="16" width="1" height="14" fill="#5f9430"/><rect x="58" y="13" width="1" height="1" fill="#a8d45a"/><rect x="58" y="14" width="1" height="2" fill="#7fb03a"/><rect x="58" y="16" width="1" height="14" fill="#5f9430"/><rect x="59" y="12" width="1" height="1" fill="#a8d45a"/><rect x="59" y="13" width="1" height="2" fill="#7fb03a"/><rect x="59" y="15" width="1" height="15" fill="#5f9430"/><rect x="60" y="12" width="1" height="1" fill="#a8d45a"/><rect x="60" y="13" width="1" height="2" fill="#7fb03a"/><rect x="60" y="15" width="1" height="15" fill="#5f9430"/><rect x="61" y="12" width="1" height="1" fill="#a8d45a"/><rect x="61" y="13" width="1" height="2" fill="#7fb03a"/><rect x="61" y="15" width="1" height="15" fill="#5f9430"/><rect x="62" y="12" width="1" height="1" fill="#a8d45a"/><rect x="62" y="13" width="1" height="2" fill="#7fb03a"/><rect x="62" y="15" width="1" height="15" fill="#5f9430"/><rect x="63" y="12" width="1" height="1" fill="#a8d45a"/><rect x="63" y="13" width="1" height="2" fill="#7fb03a"/><rect x="63" y="15" width="1" height="15" fill="#5f9430"/><rect x="64" y="12" width="1" height="1" fill="#a8d45a"/><rect x="64" y="13" width="1" height="2" fill="#7fb03a"/><rect x="64" y="15" width="1" height="15" fill="#5f9430"/><rect x="65" y="12" width="1" height="1" fill="#a8d45a"/><rect x="65" y="13" width="1" height="2" fill="#7fb03a"/><rect x="65" y="15" width="1" height="15" fill="#5f9430"/><rect x="66" y="13" width="1" height="1" fill="#a8d45a"/><rect x="66" y="14" width="1" height="2" fill="#7fb03a"/><rect x="66" y="16" width="1" height="14" fill="#5f9430"/><rect x="67" y="13" width="1" height="1" fill="#a8d45a"/><rect x="67" y="14" width="1" height="2" fill="#7fb03a"/><rect x="67" y="16" width="1" height="14" fill="#5f9430"/><rect x="68" y="13" width="1" height="1" fill="#a8d45a"/><rect x="68" y="14" width="1" height="2" fill="#7fb03a"/><rect x="68" y="16" width="1" height="14" fill="#5f9430"/><rect x="69" y="13" width="1" height="1" fill="#a8d45a"/><rect x="69" y="14" width="1" height="2" fill="#7fb03a"/><rect x="69" y="16" width="1" height="14" fill="#5f9430"/><rect x="70" y="14" width="1" height="1" fill="#a8d45a"/><rect x="70" y="15" width="1" height="2" fill="#7fb03a"/><rect x="70" y="17" width="1" height="13" fill="#5f9430"/><rect x="71" y="14" width="1" height="1" fill="#a8d45a"/><rect x="71" y="15" width="1" height="2" fill="#7fb03a"/><rect x="71" y="17" width="1" height="13" fill="#5f9430"/><rect x="72" y="14" width="1" height="1" fill="#a8d45a"/><rect x="72" y="15" width="1" height="2" fill="#7fb03a"/><rect x="72" y="17" width="1" height="13" fill="#5f9430"/><rect x="73" y="14" width="1" height="1" fill="#a8d45a"/><rect x="73" y="15" width="1" height="2" fill="#7fb03a"/><rect x="73" y="17" width="1" height="13" fill="#5f9430"/><rect x="74" y="15" width="1" height="1" fill="#a8d45a"/><rect x="74" y="16" width="1" height="2" fill="#7fb03a"/><rect x="74" y="18" width="1" height="12" fill="#5f9430"/><rect x="75" y="15" width="1" height="1" fill="#a8d45a"/><rect x="75" y="16" width="1" height="2" fill="#7fb03a"/><rect x="75" y="18" width="1" height="12" fill="#5f9430"/><rect x="76" y="15" width="1" height="1" fill="#a8d45a"/><rect x="76" y="16" width="1" height="2" fill="#7fb03a"/><rect x="76" y="18" width="1" height="12" fill="#5f9430"/><rect x="77" y="15" width="1" height="1" fill="#a8d45a"/><rect x="77" y="16" width="1" height="2" fill="#7fb03a"/><rect x="77" y="18" width="1" height="12" fill="#5f9430"/><rect x="78" y="15" width="1" height="1" fill="#a8d45a"/><rect x="78" y="16" width="1" height="2" fill="#7fb03a"/><rect x="78" y="18" width="1" height="12" fill="#5f9430"/><rect x="79" y="14" width="1" height="1" fill="#a8d45a"/><rect x="79" y="15" width="1" height="2" fill="#7fb03a"/><rect x="79" y="17" width="1" height="13" fill="#5f9430"/><rect x="80" y="14" width="1" height="1" fill="#a8d45a"/><rect x="80" y="15" width="1" height="2" fill="#7fb03a"/><rect x="80" y="17" width="1" height="13" fill="#5f9430"/><rect x="81" y="14" width="1" height="1" fill="#a8d45a"/><rect x="81" y="15" width="1" height="2" fill="#7fb03a"/><rect x="81" y="17" width="1" height="13" fill="#5f9430"/><rect x="82" y="13" width="1" height="1" fill="#a8d45a"/><rect x="82" y="14" width="1" height="2" fill="#7fb03a"/><rect x="82" y="16" width="1" height="14" fill="#5f9430"/><rect x="83" y="12" width="1" height="1" fill="#a8d45a"/><rect x="83" y="13" width="1" height="2" fill="#7fb03a"/><rect x="83" y="15" width="1" height="15" fill="#5f9430"/><rect x="84" y="11" width="1" height="1" fill="#a8d45a"/><rect x="84" y="12" width="1" height="2" fill="#7fb03a"/><rect x="84" y="14" width="1" height="16" fill="#5f9430"/><rect x="85" y="11" width="1" height="1" fill="#a8d45a"/><rect x="85" y="12" width="1" height="2" fill="#7fb03a"/><rect x="85" y="14" width="1" height="16" fill="#5f9430"/><rect x="86" y="10" width="1" height="1" fill="#a8d45a"/><rect x="86" y="11" width="1" height="2" fill="#7fb03a"/><rect x="86" y="13" width="1" height="17" fill="#5f9430"/><rect x="87" y="10" width="1" height="1" fill="#a8d45a"/><rect x="87" y="11" width="1" height="2" fill="#7fb03a"/><rect x="87" y="13" width="1" height="17" fill="#5f9430"/><rect x="88" y="9" width="1" height="1" fill="#a8d45a"/><rect x="88" y="10" width="1" height="2" fill="#7fb03a"/><rect x="88" y="12" width="1" height="18" fill="#5f9430"/><rect x="89" y="9" width="1" height="1" fill="#a8d45a"/><rect x="89" y="10" width="1" height="2" fill="#7fb03a"/><rect x="89" y="12" width="1" height="18" fill="#5f9430"/><rect x="90" y="9" width="1" height="1" fill="#a8d45a"/><rect x="90" y="10" width="1" height="2" fill="#7fb03a"/><rect x="90" y="12" width="1" height="18" fill="#5f9430"/><rect x="91" y="9" width="1" height="1" fill="#a8d45a"/><rect x="91" y="10" width="1" height="2" fill="#7fb03a"/><rect x="91" y="12" width="1" height="18" fill="#5f9430"/><rect x="92" y="8" width="1" height="1" fill="#a8d45a"/><rect x="92" y="9" width="1" height="2" fill="#7fb03a"/><rect x="92" y="11" width="1" height="19" fill="#5f9430"/><rect x="93" y="7" width="1" height="1" fill="#a8d45a"/><rect x="93" y="8" width="1" height="2" fill="#7fb03a"/><rect x="93" y="10" width="1" height="20" fill="#5f9430"/><rect x="94" y="8" width="1" height="1" fill="#a8d45a"/><rect x="94" y="9" width="1" height="2" fill="#7fb03a"/><rect x="94" y="11" width="1" height="19" fill="#5f9430"/><rect x="95" y="8" width="1" height="1" fill="#a8d45a"/><rect x="95" y="9" width="1" height="2" fill="#7fb03a"/><rect x="95" y="11" width="1" height="19" fill="#5f9430"/><rect x="96" y="8" width="1" height="1" fill="#a8d45a"/><rect x="96" y="9" width="1" height="2" fill="#7fb03a"/><rect x="96" y="11" width="1" height="19" fill="#5f9430"/><rect x="97" y="8" width="1" height="1" fill="#a8d45a"/><rect x="97" y="9" width="1" height="2" fill="#7fb03a"/><rect x="97" y="11" width="1" height="19" fill="#5f9430"/><rect x="98" y="8" width="1" height="1" fill="#a8d45a"/><rect x="98" y="9" width="1" height="2" fill="#7fb03a"/><rect x="98" y="11" width="1" height="19" fill="#5f9430"/><rect x="99" y="9" width="1" height="1" fill="#a8d45a"/><rect x="99" y="10" width="1" height="2" fill="#7fb03a"/><rect x="99" y="12" width="1" height="18" fill="#5f9430"/><rect x="100" y="8" width="1" height="1" fill="#a8d45a"/><rect x="100" y="9" width="1" height="2" fill="#7fb03a"/><rect x="100" y="11" width="1" height="19" fill="#5f9430"/><rect x="101" y="8" width="1" height="1" fill="#a8d45a"/><rect x="101" y="9" width="1" height="2" fill="#7fb03a"/><rect x="101" y="11" width="1" height="19" fill="#5f9430"/><rect x="102" y="8" width="1" height="1" fill="#a8d45a"/><rect x="102" y="9" width="1" height="2" fill="#7fb03a"/><rect x="102" y="11" width="1" height="19" fill="#5f9430"/><rect x="103" y="8" width="1" height="1" fill="#a8d45a"/><rect x="103" y="9" width="1" height="2" fill="#7fb03a"/><rect x="103" y="11" width="1" height="19" fill="#5f9430"/><rect x="104" y="8" width="1" height="1" fill="#a8d45a"/><rect x="104" y="9" width="1" height="2" fill="#7fb03a"/><rect x="104" y="11" width="1" height="19" fill="#5f9430"/><rect x="105" y="8" width="1" height="1" fill="#a8d45a"/><rect x="105" y="9" width="1" height="2" fill="#7fb03a"/><rect x="105" y="11" width="1" height="19" fill="#5f9430"/><rect x="106" y="7" width="1" height="1" fill="#a8d45a"/><rect x="106" y="8" width="1" height="2" fill="#7fb03a"/><rect x="106" y="10" width="1" height="20" fill="#5f9430"/><rect x="107" y="7" width="1" height="1" fill="#a8d45a"/><rect x="107" y="8" width="1" height="2" fill="#7fb03a"/><rect x="107" y="10" width="1" height="20" fill="#5f9430"/><rect x="108" y="7" width="1" height="1" fill="#a8d45a"/><rect x="108" y="8" width="1" height="2" fill="#7fb03a"/><rect x="108" y="10" width="1" height="20" fill="#5f9430"/><rect x="109" y="7" width="1" height="1" fill="#a8d45a"/><rect x="109" y="8" width="1" height="2" fill="#7fb03a"/><rect x="109" y="10" width="1" height="20" fill="#5f9430"/><rect x="110" y="7" width="1" height="1" fill="#a8d45a"/><rect x="110" y="8" width="1" height="2" fill="#7fb03a"/><rect x="110" y="10" width="1" height="20" fill="#5f9430"/><rect x="111" y="6" width="1" height="1" fill="#a8d45a"/><rect x="111" y="7" width="1" height="2" fill="#7fb03a"/><rect x="111" y="9" width="1" height="21" fill="#5f9430"/><rect x="112" y="6" width="1" height="1" fill="#a8d45a"/><rect x="112" y="7" width="1" height="2" fill="#7fb03a"/><rect x="112" y="9" width="1" height="21" fill="#5f9430"/><rect x="113" y="6" width="1" height="1" fill="#a8d45a"/><rect x="113" y="7" width="1" height="2" fill="#7fb03a"/><rect x="113" y="9" width="1" height="21" fill="#5f9430"/><rect x="114" y="6" width="1" height="1" fill="#a8d45a"/><rect x="114" y="7" width="1" height="2" fill="#7fb03a"/><rect x="114" y="9" width="1" height="21" fill="#5f9430"/><rect x="115" y="6" width="1" height="1" fill="#a8d45a"/><rect x="115" y="7" width="1" height="2" fill="#7fb03a"/><rect x="115" y="9" width="1" height="21" fill="#5f9430"/><rect x="116" y="5" width="1" height="1" fill="#a8d45a"/><rect x="116" y="6" width="1" height="2" fill="#7fb03a"/><rect x="116" y="8" width="1" height="22" fill="#5f9430"/><rect x="117" y="6" width="1" height="1" fill="#a8d45a"/><rect x="117" y="7" width="1" height="2" fill="#7fb03a"/><rect x="117" y="9" width="1" height="21" fill="#5f9430"/><rect x="118" y="6" width="1" height="1" fill="#a8d45a"/><rect x="118" y="7" width="1" height="2" fill="#7fb03a"/><rect x="118" y="9" width="1" height="21" fill="#5f9430"/><rect x="119" y="6" width="1" height="1" fill="#a8d45a"/><rect x="119" y="7" width="1" height="2" fill="#7fb03a"/><rect x="119" y="9" width="1" height="21" fill="#5f9430"/><rect x="41" y="12" width="1" height="1" fill="#d8f0a0"/><rect x="83" y="9" width="1" height="1" fill="#f6e65a"/><rect x="105" y="25" width="1" height="1" fill="#f6e65a"/><rect x="46" y="26" width="1" height="1" fill="#f6e65a"/><rect x="116" y="24" width="1" height="1" fill="#ffffff"/><rect x="4" y="10" width="1" height="1" fill="#d8f0a0"/><rect x="53" y="10" width="1" height="1" fill="#ffffff"/><rect x="11" y="25" width="1" height="1" fill="#d8f0a0"/><rect x="7" y="26" width="1" height="1" fill="#f6e65a"/><rect x="28" y="28" width="1" height="1" fill="#f6e65a"/><rect x="73" y="26" width="1" height="1" fill="#d8f0a0"/><rect x="6" y="15" width="1" height="1" fill="#f6e65a"/><rect x="71" y="12" width="1" height="1" fill="#f6e65a"/><rect x="53" y="12" width="1" height="1" fill="#f6e65a"/><rect x="73" y="17" width="1" height="1" fill="#ffffff"/><rect x="13" y="26" width="1" height="1" fill="#ffffff"/><rect x="47" y="11" width="1" height="1" fill="#f6e65a"/><rect x="72" y="9" width="1" height="1" fill="#ffffff"/><rect x="63" y="29" width="1" height="1" fill="#d8f0a0"/><rect x="99" y="18" width="1" height="1" fill="#d8f0a0"/><rect x="74" y="22" width="1" height="1" fill="#f6e65a"/><rect x="38" y="15" width="1" height="1" fill="#ffffff"/><rect x="89" y="15" width="1" height="1" fill="#f6e65a"/><rect x="73" y="17" width="1" height="1" fill="#d8f0a0"/><rect x="112" y="18" width="1" height="1" fill="#d8f0a0"/><rect x="36" y="27" width="1" height="1" fill="#f6e65a"/><rect x="15" y="24" width="1" height="1" fill="#d8f0a0"/><rect x="21" y="18" width="1" height="1" fill="#ffffff"/><rect x="119" y="23" width="1" height="1" fill="#d8f0a0"/><rect x="5" y="29" width="1" height="1" fill="#f6e65a"/><rect x="97" y="25" width="1" height="1" fill="#f6e65a"/><rect x="43" y="19" width="1" height="1" fill="#d8f0a0"/><rect x="74" y="22" width="1" height="1" fill="#f6e65a"/><rect x="107" y="10" width="1" height="1" fill="#f6e65a"/><rect x="60" y="29" width="1" height="1" fill="#f6e65a"/><rect x="7" y="17" width="1" height="1" fill="#d8f0a0"/><rect x="36" y="20" width="1" height="1" fill="#f6e65a"/><rect x="2" y="22" width="1" height="1" fill="#f6e65a"/><rect x="21" y="27" width="1" height="1" fill="#f6e65a"/><rect x="63" y="9" width="1" height="1" fill="#ffffff"/><rect x="98" y="17" width="1" height="1" fill="#ffffff"/><rect x="94" y="15" width="1" height="1" fill="#d8f0a0"/><rect x="50" y="23" width="1" height="1" fill="#f6e65a"/><rect x="21" y="22" width="1" height="1" fill="#d8f0a0"/><rect x="70" y="16" width="1" height="1" fill="#ffffff"/><rect x="104" y="21" width="1" height="1" fill="#f6e65a"/><rect x="90" y="21" width="1" height="1" fill="#f6e65a"/><rect x="87" y="20" width="1" height="1" fill="#ffffff"/><rect x="19" y="10" width="1" height="1" fill="#ffffff"/><rect x="19" y="15" width="1" height="1" fill="#ffffff"/><rect x="1" y="23" width="1" height="1" fill="#ffffff"/><rect x="33" y="17" width="1" height="1" fill="#f6e65a"/><rect x="18" y="21" width="1" height="1" fill="#f6e65a"/><rect x="78" y="26" width="1" height="1" fill="#f6e65a"/><rect x="16" y="24" width="1" height="1" fill="#f6e65a"/><rect x="58" y="29" width="1" height="1" fill="#d8f0a0"/><rect x="50" y="20" width="1" height="1" fill="#d8f0a0"/><rect x="13" y="23" width="1" height="1" fill="#d8f0a0"/><rect x="7" y="14" width="1" height="1" fill="#f6e65a"/><rect x="26" y="22" width="1" height="1" fill="#ffffff"/><rect x="14" y="18" width="1" height="1" fill="#f6e65a"/><rect x="13" y="8" width="1" height="1" fill="#ffffff"/><rect x="68" y="11" width="1" height="1" fill="#f6e65a"/><rect x="78" y="8" width="1" height="1" fill="#f6e65a"/><rect x="111" y="14" width="1" height="1" fill="#d8f0a0"/><rect x="19" y="28" width="1" height="1" fill="#f6e65a"/><rect x="44" y="27" width="1" height="1" fill="#f6e65a"/><rect x="60" y="11" width="1" height="1" fill="#f6e65a"/><rect x="108" y="23" width="1" height="1" fill="#d8f0a0"/><rect x="61" y="23" width="1" height="1" fill="#f6e65a"/></svg>
<svg class="px shroom" style="left:24%;bottom:46px"><use href="#shroom"/></svg>
<svg class="px shroom" style="left:46%;bottom:96px;width:clamp(32px,5vw,54px)"><use href="#shroom"/></svg>
<svg class="px shroom" style="left:70%;bottom:60px;width:clamp(30px,4.4vw,48px)"><use href="#shroom"/></svg>
<svg class="px shroom" style="right:6%;bottom:110px;width:clamp(28px,4vw,44px)"><use href="#shroom"/></svg>
<svg class="px sheepbig" viewBox="0 0 74 62"><use href="#sheep"/></svg>
<svg class="px lamb walker"><use href="#lamb"/></svg>
<svg class="px lamb walker two"><use href="#lamb"/></svg>
</footer>
<script>
const d=document.getElementById('drop'),p=document.getElementById('pick'),s=document.getElementById('status');
d.onclick=()=>p.click();
d.ondragover=e=>{e.preventDefault();d.style.background='#ffe0dc'};
d.ondragleave=()=>d.style.background='';
d.ondrop=e=>{e.preventDefault();d.style.background='';up(e.dataTransfer.files[0])};
p.onchange=()=>up(p.files[0]);
function up(f){if(!f)return;s.textContent='Loading '+f.name+' ...';let x=new FormData();x.append('song',f);
fetch('/upload',{method:'POST',body:x}).then(r=>r.text()).then(t=>{s.textContent=t;setTimeout(()=>location.reload(),1000)}).catch(()=>s.textContent='Upload failed.');}
const NAMES=['NORMAL','LISTENING','THINKING','HAPPY','SLEEPY','ANGRY','SAD','LOVE','SURPRISED','WINK','JOY','DIZZY','STARRY','CRYING','TIRED','SHY','LAUGH'];
let lastShown=0;
function setMode(m){const c=document.getElementById('ctl');const manual=m>=0;c.classList.toggle('manual',manual);
document.getElementById('modeTag').textContent=manual?'MANUAL':'AUTO';
document.getElementById('modeMsg').textContent=manual?('Showing '+(NAMES[m]||'')+' on Lulu. Her own faces are paused until you go back.'):'Lulu chooses her own face. Press SHOW ON LULU under any face to put it on her screen.';
document.getElementById('autoBtn').style.visibility=manual?'visible':'hidden';
document.getElementById('modeTxt').textContent=manual?'manual pick':'live face';}
function send(f){fetch('/set-face',{method:'POST',headers:{'Content-Type':'application/x-www-form-urlencoded'},body:'f='+f}).then(()=>{setMode(f);if(f>=0)setFace(f);latest();}).catch(()=>{})}
document.querySelectorAll('.pick').forEach(b=>b.onclick=()=>send(+b.dataset.f));
document.getElementById('autoBtn').onclick=()=>send(-1);
function setFace(i){if(i<0||i>16)return;const c=document.querySelector('.card.face[data-face="'+i+'"]'),lv=document.getElementById('live');
if(c&&lv){const sv=c.querySelector('svg');if(sv&&lv.getAttribute('data-f')!=''+i){lv.innerHTML=sv.innerHTML;lv.setAttribute('data-f',''+i);}}
document.getElementById('liveName').textContent=NAMES[i]||'';
lastShown=i;
document.querySelectorAll('.card.face[data-face]').forEach(c=>c.classList.toggle('active',+c.dataset.face===i));}
function latest(){fetch('/api/latest').then(r=>r.json()).then(x=>{
document.getElementById('heard').textContent=x.heard||'Nothing heard yet';
document.getElementById('reply').textContent=x.reply||'No answer yet';
if(typeof x.manual==='number')setMode(x.manual);
if(typeof x.face==='number')setFace(x.face);}).catch(()=>{})}
setMode(-1);latest();setInterval(latest,1500);
</script></body></html>)LULU";
  return page;
}

void startLuluWeb() {
  if (luluWebReady || WiFi.status() != WL_CONNECTED) return;
  // RMIT and many public Wi-Fi networks isolate clients from each other.
  // Keep the internet connection as STA and expose a separate local AP for
  // Lulu Home, which remains reachable at 192.168.4.1.
  WiFi.mode(WIFI_AP_STA);
  bool homeAP = WiFi.softAP(HOME_AP_NAME, HOME_AP_PASSWORD);
  luluStorageReady = FFat.begin(true);
  if (luluStorageReady && !FFat.exists("/songs")) FFat.mkdir("/songs");
  if (luluStorageReady && !FFat.exists("/lines")) FFat.mkdir("/lines");
  printStorageInfo();
  Serial.printf("Song storage: %s.\n", luluStorageReady ? "ready" : "unavailable");

  luluWeb.on("/", HTTP_GET, []() { luluWeb.send(200, "text/html; charset=utf-8", dashboardPage()); });
  luluWeb.on("/set-face", HTTP_POST, []() {
    int n = luluWeb.hasArg("f") ? luluWeb.arg("f").toInt() : -1;
    webFaceOverride = (n >= 0 && n <= 16) ? n : -1;
    setRobotFace(autoFace);   // redraws with the override (or back to Lulu's own face)
    luluWeb.send(200, "text/plain", webFaceOverride >= 0 ? "manual" : "auto");
  });
  luluWeb.on("/api/latest", HTTP_GET, []() {
    JsonDocument state;
    state["heard"] = latestHeardText;
    state["reply"] = latestReplyText;
    state["face"] = (int)robotFace;
    state["manual"] = webFaceOverride;
    state["time"] = localDateTime();
    String json; serializeJson(state, json);
    luluWeb.send(200, "application/json; charset=utf-8", json);
  });
  luluWeb.on("/add-reminder", HTTP_POST, []() {
    String note = luluWeb.arg("note"), when = luluWeb.arg("when");
    when.replace('T', ' '); note.trim(); when.trim();
    bool ok = addCalendarReminder(when, note);
    Serial.printf("Web reminder: %s | %s | %s\n", when.c_str(), note.c_str(), ok ? "saved" : "failed");
    dashboardRedirect();
  });
  luluWeb.on("/delete-reminder", HTTP_POST, []() {
    int id = luluWeb.arg("id").toInt();
    if (id >= 0 && id < MAX_ALERTS) {
      bool reminder = alerts[id].active && !alerts[id].timer;
      alerts[id].active = false; alerts[id].note = "";
      if (reminder) saveReminders();
    }
    dashboardRedirect();
  });
  luluWeb.on("/clear-reminders", HTTP_POST, []() {
    clearAllAlerts();
    dashboardRedirect();
  });
  luluWeb.on("/play-song", HTTP_POST, []() {
    String name = safeSongName(luluWeb.arg("name"));
    if (name.length() && luluStorageReady && FFat.exists("/songs/" + name)) queuedSongPath = "/songs/" + name;
    dashboardRedirect();
  });
  luluWeb.on("/delete-song", HTTP_POST, []() {
    String name = safeSongName(luluWeb.arg("name"));
    if (name.length() && luluStorageReady) FFat.remove("/songs/" + name);
    dashboardRedirect();
  });
  luluWeb.on("/upload", HTTP_POST,
    []() { luluWeb.send(songUploadOK ? 200 : 400, "text/plain; charset=utf-8", songUploadOK ? "Upload complete." : (songUploadError.length() ? songUploadError : String("Upload failed."))); },
    []() {
      HTTPUpload &upload = luluWeb.upload();
      if (upload.status == UPLOAD_FILE_START) {
        String name = safeSongName(upload.filename), lower = name; lower.toLowerCase();
        songUploadError = "";
        songUploadPath = "/songs/" + name;
        if (!luluStorageReady) songUploadError = "Upload failed: no storage on the board (in Arduino IDE choose a Partition Scheme with FFat).";
        else if (!(lower.endsWith(".wav") || lower.endsWith(".mp3")) || !name.length()) songUploadError = "Upload failed: please use an MP3 or WAV file.";
        songUploadOK = !songUploadError.length();
        if (songUploadOK) songUploadFile = FFat.open(songUploadPath, FILE_WRITE);
        if (songUploadOK && !songUploadFile) { songUploadOK = false; songUploadError = "Upload failed: could not create the file."; }
      } else if (upload.status == UPLOAD_FILE_WRITE) {
        if (songUploadOK && songUploadFile.write(upload.buf, upload.currentSize) != upload.currentSize) {
          songUploadOK = false;
          songUploadError = "Upload failed: not enough space (delete some songs or use a smaller file).";
        }
      } else if (upload.status == UPLOAD_FILE_END) {
        if (songUploadFile) songUploadFile.close();
        if (!songUploadOK && luluStorageReady && songUploadPath.length()) FFat.remove(songUploadPath);   // no half files
        Serial.printf("Song upload: %s (%u bytes) %s\n", songUploadOK ? "complete" : "failed", (unsigned)upload.totalSize,
                      songUploadOK ? "" : songUploadError.c_str());
        if (songUploadOK && luluStorageReady)
          Serial.printf("Storage: %u KB free of %u KB\n", (unsigned)((FFat.totalBytes() - FFat.usedBytes()) / 1024), (unsigned)(FFat.totalBytes() / 1024));
      } else if (upload.status == UPLOAD_FILE_ABORTED) {
        if (songUploadFile) songUploadFile.close();
        songUploadOK = false;
        if (luluStorageReady && songUploadPath.length()) FFat.remove(songUploadPath);
      }
    });
  luluWeb.onNotFound([]() { luluWeb.sendHeader("Location", "/", true); luluWeb.send(302); });
  luluWeb.begin();
  luluWebReady = true;
  Serial.printf("Lulu Home on current Wi-Fi: http://%s/\n", WiFi.localIP().toString().c_str());
  Serial.printf("Lulu direct Wi-Fi: %s (%s), open http://192.168.4.1/ [%s]\n",
                HOME_AP_NAME, HOME_AP_PASSWORD, homeAP ? "ready" : "failed");
}

void printStorageInfo() {
  if (!luluStorageReady) {
    Serial.println("Storage: NO FFat partition. In Arduino IDE choose Tools > Partition Scheme with FFat "
                   "(ESP32-S3 with 16MB flash: '16M Flash (3MB APP/9.9MB FATFS)').");
    return;
  }
  Serial.printf("Storage (FFat): %u KB free of %u KB total. Flash chip: %u MB.\n",
                (unsigned)((FFat.totalBytes() - FFat.usedBytes()) / 1024),
                (unsigned)(FFat.totalBytes() / 1024),
                (unsigned)(ESP.getFlashChipSize() / (1024 * 1024)));
}

void printLuluWebAddress() {
  if (!luluWebReady && WiFi.status() == WL_CONNECTED) startLuluWeb();
  if (!luluWebReady) {
    Serial.println("Lulu Home is unavailable. Connect Lulu to Wi-Fi first.");
    return;
  }
  Serial.printf("Lulu Home: http://%s/\n", WiFi.localIP().toString().c_str());
  Serial.printf("Or connect to %s, password %s, then open http://192.168.4.1/\n",
                HOME_AP_NAME, HOME_AP_PASSWORD);
}

void serviceLuluWeb() {
  if (luluWebReady) luluWeb.handleClient();
}

// ---------------------------------------------------------------------------
// Microphone capture runs in its own task, so audio is never lost while the
// main thread is busy with network work (a TLS handshake can take ~1 s).
// The task applies the digital gain, runs the voice detection and stores the
// audio (with a short pre-roll before the first word) in a PSRAM buffer.
// ---------------------------------------------------------------------------
int16_t *utt = nullptr;                 // captured utterance (PSRAM)
volatile size_t uttCount = 0;
size_t uttSent = 0;
volatile bool micTaskRun = false, micTaskExited = true;
volatile bool captureKeepAll = false;   // true: keep everything from the start (BOOT mode)
volatile bool vadSpeaking = false, vadEnded = false, vadNoSpeech = false;
volatile int vadVoiced = 0, uttPeak = 0;
volatile uint32_t captureStartMs = 0;
int micGain = MIC_DIGITAL_GAIN;
uint32_t endSilenceMs = DEFAULT_END_SILENCE_MS;
double noiseFloor = 0;
i2s_std_slot_mask_t micSlot = I2S_STD_SLOT_LEFT;
bool micSlotKnown = false;
bool wakeMode = true;
uint32_t awakeUntil = 0;

void micTaskFn(void *) {
  constexpr int DISCARD_BLOCKS = 5, CALIB_BLOCKS = 15;
  double calib[CALIB_BLOCKS];
  int calibCount = noiseFloor > 0 ? CALIB_BLOCKS : 0, blockIndex = 0, loud = 0;
  double startThr = 0, endThr = 0;
  uint32_t silentMs = 0;
  auto setThresholds = [&]() {
    startThr = max(noiseFloor * 1.8, noiseFloor + 30.0 * micGain);
    endThr = max(noiseFloor * 1.35, noiseFloor + 15.0 * micGain);
  };
  if (calibCount == CALIB_BLOCKS) setThresholds();
  int32_t raw[BLOCK_SAMPLES];
  int16_t pcm[BLOCK_SAMPLES];
  while (micTaskRun) {
    size_t got = mic.readBytes((char *)raw, sizeof(raw));
    if (got != sizeof(raw)) { delay(5); continue; }
    double energy = 0; int peak = 0; int g = micGain;
    for (size_t i = 0; i < BLOCK_SAMPLES; ++i) {
      // 24-bit sample in a 32-bit word: scale with the gain, keep full precision.
      int32_t value = (((int32_t)raw[i] >> 8) * g) >> 8;
      pcm[i] = constrain(value, -32768, 32767);
      energy += double(pcm[i]) * pcm[i];
      peak = max(peak, abs((int)pcm[i]));
    }
    double rms = sqrt(energy / BLOCK_SAMPLES);
    if (++blockIndex <= DISCARD_BLOCKS) continue; // button click / DMA warm-up
    if (calibCount < CALIB_BLOCKS) {
      calib[calibCount++] = rms;
      if (calibCount == CALIB_BLOCKS) {
        for (int i = 1; i < CALIB_BLOCKS; ++i) {
          double key = calib[i]; int j = i - 1;
          while (j >= 0 && calib[j] > key) { calib[j + 1] = calib[j]; --j; }
          calib[j + 1] = key;
        }
        double noise = 0;
        for (int i = 0; i < CALIB_BLOCKS / 2; ++i) noise += calib[i];
        noiseFloor = noise / (CALIB_BLOCKS / 2);
        setThresholds();
        Serial.printf("VAD: noise=%.0f start=%.0f end=%.0f\n", noiseFloor, startThr, endThr);
      }
      continue;
    }
    size_t n = uttCount;
    if (!vadSpeaking && !captureKeepAll && n >= PREROLL_SAMPLES) { // rolling pre-roll
      memmove(utt, utt + BLOCK_SAMPLES, (n - BLOCK_SAMPLES) * sizeof(int16_t));
      n -= BLOCK_SAMPLES;
    }
    if (n + BLOCK_SAMPLES > MAX_SAMPLES) { vadEnded = true; break; }
    memcpy(utt + n, pcm, sizeof(pcm));
    __sync_synchronize(); // data visible before the new length
    uttCount = n + BLOCK_SAMPLES;

    if (!vadSpeaking) {
      loud = rms > startThr ? loud + 1 : 0;
      if (rms < startThr) { noiseFloor = noiseFloor * 0.98 + rms * 0.02; setThresholds(); }
      if (loud >= 3) { // 60 ms in a row above the threshold
        vadSpeaking = true; silentMs = 0; vadVoiced = 0; uttPeak = 0;
      } else if (captureKeepAll && millis() - captureStartMs >= WAIT_FOR_SPEECH_MS) {
        vadNoSpeech = true; vadEnded = true; break;
      }
    } else {
      if (peak > uttPeak) uttPeak = peak;
      if (rms >= endThr) vadVoiced = vadVoiced + 1;
      silentMs = rms < endThr ? silentMs + 20 : 0;
      if (silentMs >= endSilenceMs) {
        if (!captureKeepAll && vadVoiced < WAKE_TRIGGER_BLOCKS) {
          // Too short to be a spoken name (a click, a knock): forget it.
          vadSpeaking = false; loud = 0; uttCount = 0;
        } else {
          vadEnded = true; break;
        }
      }
    }
  }
  micTaskExited = true;
  vTaskDelete(nullptr);
}

void stopMic() {
  micTaskRun = false;
  uint32_t t = millis();
  while (!micTaskExited && millis() - t < 1000) delay(5);
  mic.end();
}

bool startMic(bool keepAll) {
  stopMic(); // also makes sure a previous capture task has finished
  mic.setPins(MIC_BCLK_PIN, MIC_WS_PIN, -1, MIC_DATA_PIN);
  if (!mic.begin(I2S_MODE_STD, 16000, I2S_DATA_BIT_WIDTH_32BIT, I2S_SLOT_MODE_MONO, micSlot)) {
    Serial.println("Microphone initialization failed."); return false;
  }
  if (!micSlotKnown) { // some boards report the LEFT slot as RIGHT: probe once
    int32_t raw[BLOCK_SAMPLES];
    for (int i = 0; i < 6; ++i) mic.readBytes((char *)raw, sizeof(raw));
    bool hasData = false;
    for (int probe = 0; probe < 4 && !hasData; ++probe) {
      size_t got = mic.readBytes((char *)raw, sizeof(raw));
      for (size_t i = 0; i < got / 4; ++i) hasData |= raw[i] != 0;
    }
    if (!hasData) {
      mic.end();
      mic.setPins(MIC_BCLK_PIN, MIC_WS_PIN, -1, MIC_DATA_PIN);
      micSlot = I2S_STD_SLOT_RIGHT;
      if (!mic.begin(I2S_MODE_STD, 16000, I2S_DATA_BIT_WIDTH_32BIT, I2S_SLOT_MODE_MONO, micSlot)) {
        Serial.println("Microphone initialization failed on both slots."); return false;
      }
    }
    micSlotKnown = true;
    Serial.printf("Microphone: %s slot, %dx digital gain.\n",
                  micSlot == I2S_STD_SLOT_LEFT ? "LEFT" : "RIGHT", micGain);
  }
  uttCount = 0; uttSent = 0; uttPeak = 0; vadVoiced = 0;
  vadSpeaking = false; vadEnded = false; vadNoSpeech = false;
  captureKeepAll = keepAll; captureStartMs = millis();
  micTaskRun = true; micTaskExited = false;
  xTaskCreatePinnedToCore(micTaskFn, "mic_capture", 8192, nullptr, 5, nullptr, 0);
  return true;
}

// ---------------------------------------------------------------------------
// Wake word: the name is recognised from the ASR text (no on-device model).
// ASR may spell the name in several ways: add what you see in "You said:".
// ---------------------------------------------------------------------------
static const char *WAKE_WORDS[] = {
  "噜噜", "露露", "璐璐", "卢卢", "鹿鹿", "路路", "鲁鲁", "陆陆",
  "lulu", "lu lu", "loo loo", "lou lou"
};
static const char *WAKE_FILLERS[] = { // may come before the name: "hey Lulu", "嘿，噜噜"
  "okay", "hello", "hey", "hay", "ok", "hi", "你好", "哈喽", "嘿", "喂", "嗨", "诶", "哎"
};

String wakeNormalize(const String &in) {
  String out; out.reserve(in.length());
  size_t n = in.length();
  for (size_t i = 0; i < n;) {
    uint8_t c = (uint8_t)in[i];
    if (c < 0x80) { if (isalnum(c)) out += (char)tolower(c); ++i; }
    else if (c == 0xE3 && i + 2 < n && (uint8_t)in[i + 1] == 0x80) i += 3; // CJK punctuation
    else if (c == 0xE2 && i + 2 < n && (uint8_t)in[i + 1] == 0x80) i += 3; // quotes, ellipsis
    else if (c == 0xEF && i + 2 < n && ((uint8_t)in[i + 1] == 0xBC || (uint8_t)in[i + 1] == 0xBD)) i += 3; // full-width
    else { out += (char)c; ++i; }
  }
  return out;
}

// True if the sentence starts with a wake word; restBytes = how much follows it.
bool wakeMatch(const String &heard, size_t &restBytes) {
  String s = wakeNormalize(heard);
  bool stripped = true;
  while (stripped) {
    stripped = false;
    for (const char *f : WAKE_FILLERS) {
      size_t fl = strlen(f);
      if (s.startsWith(f) && s.length() > fl) { s.remove(0, fl); stripped = true; break; }
    }
  }
  for (const char *w : WAKE_WORDS) {
    if (s.startsWith(w)) { restBytes = s.length() - strlen(w); return true; }
  }
  return false;
}

// wake = true : listen locally and only use the cloud after hearing speech;
//               answer only if the name is said (or during the follow-up window).
// wake = false: BOOT button / serial "r": start streaming right away.
// Voice request for a song ("sing a song", "唱首歌", "play <song name>"). Returns
// true when the sentence asks for music. path is the chosen file in /songs, or
// empty when there is nothing to play.
bool wantsSong(const String &text, String &path) {
  path = "";
  String t = text; t.toLowerCase();
  bool ask = t.indexOf("唱歌") >= 0 || t.indexOf("唱首") >= 0 || t.indexOf("唱一首") >= 0 ||
             t.indexOf("唱个") >= 0 || t.indexOf("唱支") >= 0 || t.indexOf("放歌") >= 0 ||
             t.indexOf("放首") >= 0 || t.indexOf("放一首") >= 0 || t.indexOf("来首") >= 0 ||
             t.indexOf("来一首") >= 0 || t.indexOf("播放音乐") >= 0 || t.indexOf("放音乐") >= 0 ||
             t.indexOf("sing") >= 0 || t.indexOf("play a song") >= 0 || t.indexOf("play some music") >= 0 ||
             t.indexOf("play music") >= 0 || t.indexOf("play the song") >= 0 || t.indexOf("play song") >= 0 ||
             t.indexOf("play me a song") >= 0;
  if (!ask) return false;
  if (!luluStorageReady) return true;
  String names[24];
  int n = 0;
  File dir = FFat.open("/songs");
  File file = dir ? dir.openNextFile() : File();
  while (file && n < 24) {
    if (!file.isDirectory()) {
      String full = file.name();
      names[n++] = full.substring(full.lastIndexOf('/') + 1);
    }
    file = dir.openNextFile();
  }
  if (dir) dir.close();
  if (!n) return true;
  int pick = -1;
  for (int i = 0; i < n && pick < 0; ++i) {          // a file name mentioned in the sentence wins
    String stem = names[i]; stem.toLowerCase();
    int dot = stem.lastIndexOf('.');
    if (dot > 0) stem = stem.substring(0, dot);
    if (stem.length() >= 2 && t.indexOf(stem) >= 0) pick = i;
  }
  if (pick < 0) pick = random(n);
  path = "/songs/" + names[pick];
  return true;
}

void recognize(bool wake) {
  if (!utt) return;
  // Whatever way this function exits, leave "busy" mode and drop any touch
  // that arrived during the conversation so it cannot wake Lulu afterwards.
  struct TouchReactGuard {
    ~TouchReactGuard() {
      if (touchReactionOnly) { touchReactionOnly = false; queuedTouchBleat = false; }
    }
  } touchGuard;
  setRobotFace(FACE_LISTENING);
  if (!networkReady()) {
    setRobotFace(FACE_NORMAL);
    if (wake) followDelay(1000); // keep following hands instead of freezing for 1 s
    return;
  }
  bool awake = !wake || (int32_t)(awakeUntil - millis()) > 0;

  if (!startMic(!wake)) {
    setRobotFace(FACE_NORMAL);
    if (wake) followDelay(1000);
    return;
  }
  if (wake) {
    const int need = awake ? 8 : WAKE_TRIGGER_BLOCKS;
    for (;;) {
      if (vadSpeaking && vadVoiced >= need) break;
      if (queuedTouchBleat) {
        stopMic();
        if (awake) {
          // Already awake (follow-up window): just react, do not start a new
          // question. loop() calls recognize(true) again and the window continues.
          handleQueuedTouchBleat();
          return;
        }
        handleQueuedTouchBleat();
        touchWakeFlow();
        return;
      }
      if (digitalRead(RECORD_BUTTON_PIN) == LOW || Serial.available()) {
        stopMic();
        setRobotFace(FACE_NORMAL);
        return;
      }
      if (queuedSongPath.length()) {
        stopMic();
        setRobotFace(FACE_NORMAL);
        return; // loop() starts the song immediately after web selection
      }
      if (awake && (int32_t)(awakeUntil - millis()) <= 0) {
        stopMic(); awakeUntil = 0;
        setRobotFace(FACE_NORMAL);
        Serial.println("Back to sleep. Say the name Lulu / 噜噜 to wake me.");
        return;
      }
      if (micTaskExited) {
        stopMic();
        setRobotFace(FACE_NORMAL);
        return;
      }
      if (!vadSpeaking) updateHandFollowing();
      delay(10);
    }
    Serial.println(awake ? "Speech detected." : "Sound detected; checking for my name...");
    // Asleep: a touch can still wake her while she checks for her name.
    if (awake) touchReactionOnly = true;
  } else {
    Serial.println("Listening... speak now.");
    touchReactionOnly = true;
  }

  // The microphone task keeps capturing while we connect to the ASR service.
  finished = false; failed = false; connected = false; requestAccepted = false;
  lastText = ""; lastDisplayedText = ""; lastTranscriptAt = 0;
  String id = uuid();
  // Volcengine's current V3 handshake requires X-Api-Sequence: -1.
  // Request-Id identifies this recognition request; Connect-Id lets the
  // provider trace an otherwise silent server-side disconnect.
  headers = String("X-Api-Key: ") + DOUBAO_API_KEY
    + "\r\nX-Api-Resource-Id: " + ASR_RESOURCE_ID
    + "\r\nX-Api-Request-Id: " + id
    + "\r\nX-Api-Connect-Id: " + id
    + "\r\nX-Api-Sequence: -1";
  ws.setExtraHeaders(headers.c_str());
  ws.setReconnectInterval(0);
  ws.onEvent(onEvent);
  ws.beginSslWithCA("openspeech.bytedance.com", 443, "/api/v3/sauc/bigmodel_async", ROOT_CA, "");
  ws.loop();
  ws.setReconnectInterval(60000);
  uint32_t start = millis();
  while (!connected && !failed && millis() - start < 15000) {
    ws.loop(); updateHandFollowing(); delay(5);
  }

  int32_t sequence = 1;
  if (connected && !failed) {
    JsonDocument request;
    request["user"]["uid"] = "lulu-esp32s3";
    JsonObject audio = request["audio"].to<JsonObject>();
    audio["format"] = "pcm"; audio["codec"] = "raw";
    audio["rate"] = 16000; audio["bits"] = 16; audio["channel"] = 1;
    if (language == "zh") audio["language"] = "zh-CN";
    if (language == "en") audio["language"] = "en-US";
    JsonObject options = request["request"].to<JsonObject>();
    options["model_name"] = "bigmodel";
    options["enable_itn"] = true;
    options["enable_punc"] = true;
    options["show_utterances"] = true;
    options["enable_nonstream"] = true; // accurate second pass at sentence end
    // Use the value from the last known working ASR build. Local recording below
    // still waits endSilenceMs (default 2500 ms), so a thinking pause does not
    // make Lulu answer before the speaker has finished.
    options["end_window_size"] = 500;
    String json; serializeJson(request, json);
    if (!sendPacket(0x11, 1, sequence++, (const uint8_t *)json.c_str(), json.length())) failed = true;
    Serial.printf("Live ASR connecting (%s)...\n", language.c_str());
    start = millis();
    while (!requestAccepted && !failed && millis() - start < 5000) {
      ws.loop(); updateHandFollowing(); delay(5);
    }
    if (!requestAccepted && !failed) { Serial.println("ASR request acknowledgement timed out."); failed = true; }
  }

  bool sentFinal = false, noSpeech = false;
  if (requestAccepted && !failed) {
    uint32_t streamStart = millis();
    while (!failed && !finished && !sentFinal && millis() - streamStart < 40000) {
      // The server already heard a sentence and the words stopped changing for 1.8 s:
      // treat that as the end of the question even if background noise keeps the
      // local silence detector from ending (otherwise she records until the 40 s limit).
      bool transcriptSettled = lastTranscriptAt && lastText.length() && millis() - lastTranscriptAt > 1800;
      bool ended = vadEnded || transcriptSettled;
      size_t have = uttCount; // read after the flag: final once ended
      if (ended && vadNoSpeech) { Serial.println("No speech detected."); noSpeech = true; break; }
      // Send what the microphone task captured; catch up faster when behind.
      int budget = (have - uttSent > 4 * BLOCK_SAMPLES) ? 2 : 1;
      bool sentSomething = false;
      while (budget-- > 0 && uttSent < have) {
        bool more = uttSent + BLOCK_SAMPLES < have; // hold the newest block back until
        if (!more && !ended) break;                 // we know whether it is the last one
        bool last = ended && uttSent + BLOCK_SAMPLES >= have;
        int32_t packetSequence = last ? -sequence : sequence;
        if (!sendPacket(last ? 0x23 : 0x21, 0, packetSequence,
                        (const uint8_t *)(utt + uttSent), BLOCK_SAMPLES * sizeof(int16_t))) {
          failed = true; break;
        }
        uttSent += BLOCK_SAMPLES; sentSomething = true;
        if (last) { sentFinal = true; break; }
        ++sequence;
      }
      ws.loop();
      updateHandFollowing();
      if (!sentSomething) delay(5);
    }
  }
  stopMic();
  setRobotFace(FACE_THINKING);
  Serial.printf("Captured %.1fs, peak=%d (aim for about 8000-25000), gain=%dx.\n",
                uttCount / 16000.0, (int)uttPeak, micGain);
  if (sentFinal && !failed) {
    start = millis();
    while (!finished && !failed && millis() - start < 20000) {
      ws.loop(); updateHandFollowing(); delay(5);
    }
  }

  if (failed && !finished && lastText.length()) {
    // The server closed the link after it had already sent a transcript: use it.
    Serial.println("ASR link closed after a transcript; using what was heard.");
    failed = false; finished = true;
  }
  if (!finished && failed) Serial.println("ASR failed. See the message above.");
  if (!finished && !failed && !noSpeech) Serial.println("ASR result timed out.");
  finished = true; ws.disconnect(); ws.setExtraHeaders(nullptr); headers = "";
  delay(100);
  if (!lastText.length()) {
    if (failed) { setRobotFace(FACE_CRY); delay(1500); }
    setRobotFace(FACE_NORMAL);
    Serial.println(wake ? "Nothing recognised." : "Ready: short press BOOT, or send r.");
    return;
  }
  latestHeardText = lastText;

  if (wake && !awake) {
    size_t rest = 0;
    if (!wakeMatch(lastText, rest)) {
      setRobotFace(FACE_NORMAL);
      Serial.println("No wake word; ignored (nothing sent to the AI).");
      return;
    }
    Serial.println("Wake word heard.");
    if (rest < 6) { // only the name was said: acknowledge and wait for the question
      setRobotFace(FACE_HAPPY);
      playWakeChime();
      awakeUntil = millis() + WAKE_COMMAND_MS;
      Serial.println("Listening for your question...");
      return;
    }
  }
  touchReactionOnly = true;   // she is now answering: touches only make her react
  {
    String songPath;
    if (wantsSong(lastText, songPath)) {
      bool en = textIsMostlyEnglish(lastText);
      String line = !songPath.length()
        ? (en ? "I do not have any songs yet. Upload one on my home page!" : "我还没有歌哦，先去我的网页上传一首吧！")
        : (en ? "Okay, let me sing!" : "好的，我来唱歌！");
      latestReplyText = line;
      Serial.printf("Song request: %s\n", songPath.length() ? songPath.c_str() : "(no songs)");
      setRobotFace(FACE_HAPPY);
      speakDoubao(line);
      if (songPath.length()) {
        touchReactionOnly = false;   // a head pat or BOOT now stops the song
        queuedTouchBleat = false;
        playSong(songPath);
        queuedTouchBleat = false;    // the pat that stopped the song is not a new wake-up
      }
      if (wakeMode) awakeUntil = millis() + FOLLOWUP_MS;
      setRobotFace(FACE_NORMAL);
      return;
    }
  }
  int localReminderQuery = reminderListQuery(lastText);
  String reply;
  if (localReminderQuery) {
    bool requestedEnglish = textIsMostlyEnglish(lastText);
    // Preserve the exact saved note. If it is Chinese, use an entirely
    // Chinese sentence instead of wrapping it in an English sentence.
    bool english = requestedEnglish && listedAlertsAreEnglish(localReminderQuery == 2);
    reply = localReminderQuery == 2 ? listTodayAlerts(english) : listAlerts(english);
    Serial.println("Reminder question answered from Lulu's saved data.");
  } else {
    uint32_t askStartedAt = millis();
    reply = askDoubao(lastText);
    Serial.printf("Timing: AI reply took %lu ms.\n", (unsigned long)(millis() - askStartedAt));
    handleQueuedTouchBleat();
    reply = handlePendingAction(reply);
  }
  if (reply.length()) {
    previousUser = lastText;
    previousAssistant = reply;
    latestReplyText = reply;
    Serial.println("\nLulu final reply:");
    Serial.println(reply);
  }
  pickReplyEmotion(reply);
  setRobotFace(replyFace);
  emotionStart();
  speakDoubao(reply);
  emotionEnd();
  if (wakeMode) {
    followDelay(300); // let the speaker's echo fade before listening again
    awakeUntil = millis() + FOLLOWUP_MS;
    Serial.println("Follow-up listening for 5 seconds...");
  } else {
    Serial.println("Ready: short press BOOT, or send r.");
  }
  setRobotFace(FACE_NORMAL);
}
void setup() {
  Serial.begin(115200); delay(1200);
  // Turn the addressable RGB LED off. Only one call is used on purpose:
  // calling rgbLedWrite() and neopixelWrite() together can fight over the
  // same RMT channel. If your board's RGB LED is on GPIO38 (DevKitC-1 v1.1),
  // note that GPIO38 is also the speaker BCLK pin, so playing audio will light
  // it up; move SPEAKER_BCLK_PIN to a free GPIO in that case.
  rgbLedWrite(RGB_BUILTIN, 0, 0, 0);
  Serial.printf("\nLULU SLIM 2026-10-11 V33 | measured servo ranges | RGB_BUILTIN=GPIO%d\n", (int)RGB_BUILTIN);
  Serial.println("Starting hardware checks...");
  static const uint8_t crcTest[] = "123456789";
  if (mz_crc32(0, crcTest, 9) != 0xcbf43926UL)
    Serial.println("WARNING: GZIP CRC self-test failed.");
  pinMode(RECORD_BUTTON_PIN, INPUT_PULLUP);
  pinMode(HEAD_TOUCH_PIN, INPUT);
  pinMode(SPEAKER_ENABLE_PIN, OUTPUT);
  digitalWrite(SPEAKER_ENABLE_PIN, LOW);
  setupRobotBody();
  delay(50);
  touchIdleLevel = digitalRead(HEAD_TOUCH_PIN) == HIGH;
  touchPhysicalActive = false;
  BaseType_t touchTaskResult = xTaskCreatePinnedToCore(
    touchMonitorTask, "touch_watch", 2048, nullptr, 1, nullptr, 0);
  Serial.printf("Head touch baseline: %s (touching must change it).\n",
                touchIdleLevel ? "HIGH" : "LOW");
  Serial.printf("Head touch watcher: %s.\n",
                touchTaskResult == pdPASS ? "running" : "FAILED");
  reminderStore.begin("lulu-reminders", false);
  // Remove reminders that older firmware could invent and save. This cleanup
  // runs once; reminders created by V32 and later continue to persist.
  if (reminderStore.getUChar("dataVer", 0) < 2) {
    clearAllAlerts();
    reminderStore.putUChar("dataVer", 2);
    Serial.println("Old unverified reminder data removed once for V32.");
  }
  utt = (int16_t *)psramAlloc(MAX_SAMPLES * sizeof(int16_t));
  Serial.println("Mic GPIO 6/7/18 | speaker GPIO 38/39/40, EN 41");
  Serial.printf("Servos: X GPIO4 %d..%d (centre %d, %d deg servo) | Y GPIO5 %d..%d (centre %d, %d deg servo) | pulse %d-%d us\n",
                X_SAFE_MIN, X_SAFE_MAX, LR_CENTER, X_RANGE_DEG,
                Y_SAFE_MIN, Y_SAFE_MAX, UD_CENTER, Y_RANGE_DEG,
                SERVO_PULSE_MIN_US, SERVO_PULSE_MAX_US);
  if (!utt) Serial.println("ERROR: insufficient audio memory (is PSRAM enabled?).");
  Serial.println("Wake mode: say Lulu / 噜噜 or touch the head, then speak.");
  Serial.println("Hold BOOT 1s: cycle language.");
  Serial.println("Serial commands: faces / face N / r / auto / zh / en / reset / wake / button / wifi / web / reminders / clearreminders / sensors / sensorreset / near N / debug / lamb / touchtest / touchdebug / servotest / cal / lr N / ud N / center / run / gain N / pause MS");
  Serial.printf("Listening waits %lu ms of silence before replying (change with: pause MS).\n",
                (unsigned long)endSilenceMs);
  Serial.println("Wake mode listens locally; sound is only sent to the cloud after speech is heard.");
  Serial.println("Default: auto (Chinese + English). The playback voice is AI-generated.");
  Serial.println("Credentials are never printed.");
  if (networkReady()) {
    loadReminders();
    Serial.println("Time, Melbourne weather, timers and reminders are ready.");
    startLuluWeb();
  }
  rgbLedWrite(RGB_BUILTIN, 0, 0, 0);
}
void loop() {
  checkAlerts();
  updateHandFollowing();
  serviceLuluWeb();
  bool down = digitalRead(RECORD_BUTTON_PIN) == LOW;
  // Main-loop fallback in case the background watcher is delayed. The
  // touchPhysicalActive latch prevents repeated triggers while held.
  bool touchNow = (digitalRead(HEAD_TOUCH_PIN) == HIGH) != touchIdleLevel;
  if (touchNow && !touchPhysicalActive) {
    touchPhysicalActive = true;
    touchQueuedAt = millis();
    queuedTouchBleat = true;
  } else if (!touchNow && touchPhysicalActive) {
    touchPhysicalActive = false;
  }
  if (!down && !buttonArmed) buttonArmed = true;
  if (buttonArmed && down && !pressedAt) pressedAt = millis();
  if (buttonArmed && !down && pressedAt) {
    uint32_t duration = millis() - pressedAt; pressedAt = 0;
    if (duration >= 5000) {
      Serial.println("Opening Wi-Fi chooser (saved passwords are kept)...");
      runWiFiSetupPortal();
    } else if (duration >= 1000) {
      language = language == "auto" ? "zh" : language == "zh" ? "en" : "auto";
      Serial.printf("Language: %s\n", language.c_str());
    } else if (duration >= 30) recognize(false);
  }
  if (queuedTouchBleat && !down && !pressedAt) {
    bool awakeNow = wakeMode && (int32_t)(awakeUntil - millis()) > 0;
    if (awakeNow) {
      handleQueuedTouchBleat();   // already awake: react only
    } else {
      handleQueuedTouchBleat();
      // touchWakeFlow() speaks from flash if cached and only listens when
      // Wi-Fi is connected (it never tries to join Wi-Fi / open the portal).
      touchWakeFlow();
    }
  }
  while (Serial.available()) {
    char c = Serial.read();
    if (c == '\r' || c == '\n') {
      command.trim(); command.toLowerCase();
      if (command == "r") recognize(false);
      else if (command == "auto" || command == "zh" || command == "en") {
        language = command; Serial.printf("Language: %s\n", language.c_str());
      } else if (command == "reset") {
        previousUser = ""; previousAssistant = ""; Serial.println("Conversation memory cleared.");
      } else if (command == "wake") {
        wakeMode = true; awakeUntil = 0; Serial.println("Wake mode ON: say Lulu or 噜噜.");
      } else if (command == "button") {
        wakeMode = false; Serial.println("Wake mode OFF: press BOOT to talk.");
      } else if (command == "wifi") {
        Serial.println("Opening Wi-Fi chooser (saved passwords are kept)...");
        runWiFiSetupPortal();
      } else if (command == "web") {
        printLuluWebAddress();
      } else if (command == "reminders") {
        Serial.println(listAlerts(language == "en"));
      } else if (command == "clearreminders") {
        clearAllAlerts();
      } else if (command == "sensors") {
        Serial.printf("Sensors (your view): left=%s %u mm (status %d) | right=%s %u mm (status %d) | touch=%s raw=%s idle=%s | trigger<%d mm | LR=%d UD=%d\n",
                      leftDistanceReady ? "OK" : "NOT FOUND", lastLeftMM,
                      (int)leftDistanceSensor.ranging_data.range_status,
                      rightDistanceReady ? "OK" : "NOT FOUND", lastRightMM,
                      (int)rightDistanceSensor.ranging_data.range_status,
                      touchPhysicalActive ? "ACTIVE" : "idle",
                      digitalRead(HEAD_TOUCH_PIN) == HIGH ? "HIGH" : "LOW",
                      touchIdleLevel ? "HIGH" : "LOW",
                      handNearMM, currentLR, currentUD);
      } else if (command == "sensorreset") {
        resetDistanceSensors();
      } else if (command.startsWith("near ")) {
        int n = command.substring(5).toInt();
        if (n >= 40 && n <= 450) { handNearMM = n; Serial.printf("Hand trigger: below %d mm\n", n); }
        else Serial.println("near must be 40-450");
      } else if (command == "debug") {
        handDebug = !handDebug;
        Serial.printf("Distance debug %s\n", handDebug ? "ON" : "OFF");
      } else if (command == "space") {
        printStorageInfo();
      } else if (command == "faces") {
        for (int i = 0; i <= 16; ++i) { Serial.printf("face %d\n", i); setRobotFace((RobotFace)i); delay(1500); }
        setRobotFace(FACE_NORMAL);
      } else if (command.startsWith("face ")) {
        int n = command.substring(5).toInt();
        if (n >= 0 && n <= 16) { setRobotFace((RobotFace)n); Serial.printf("face %d\n", n); }
      } else if (command == "cachelines") {
        cacheAllTouchLines();
      } else if (command == "lamb") {
        setRobotFace(FACE_HAPPY);
        playLambBleat();
        setRobotFace(FACE_NORMAL);
      } else if (command == "touchtest") {
        queuedTouchBleat = true;
        handleQueuedTouchBleat();
      } else if (command == "touchdebug") {
        touchDebug = !touchDebug;
        touchDebugLast = digitalRead(HEAD_TOUCH_PIN) == HIGH;
        Serial.printf("Touch debug %s (idle level is %s)\n", touchDebug ? "ON" : "OFF",
                      touchIdleLevel ? "HIGH" : "LOW");
      } else if (command == "servotest") {
        testBothServos();
      } else if (command == "cal") {
        servoCalibrationMode = true;
        targetLR = currentLR; targetUD = currentUD;
        Serial.printf("Servo calibration ON. LR=%d UD=%d. Use: lr N / ud N / center / run\n",
                      currentLR, currentUD);
      } else if (command.startsWith("lr ")) {
        int angle = command.substring(3).toInt();
        if (angle >= X_SAFE_MIN && angle <= X_SAFE_MAX) {
          servoCalibrationMode = true; targetLR = angle;
          Serial.printf("Calibration: LR target=%d degrees\n", angle);
        } else Serial.printf("lr must be %d-%d\n", X_SAFE_MIN, X_SAFE_MAX);
      } else if (command.startsWith("ud ")) {
        int angle = command.substring(3).toInt();
        if (angle >= Y_SAFE_MIN && angle <= Y_SAFE_MAX) {
          servoCalibrationMode = true; targetUD = angle;
          Serial.printf("Calibration: UD target=%d degrees\n", angle);
        } else Serial.printf("ud must be %d-%d\n", Y_SAFE_MIN, Y_SAFE_MAX);
      } else if (command == "center") {
        servoCalibrationMode = true;
        targetLR = LR_CENTER; targetUD = UD_CENTER;
        Serial.printf("Calibration: default centre LR=%d UD=%d\n", LR_CENTER, UD_CENTER);
      } else if (command == "run") {
        servoCalibrationMode = false; lastHandSeenAt = millis();
        Serial.printf("Servo calibration OFF. Current LR=%d UD=%d; hand following resumed.\n",
                      currentLR, currentUD);
      } else if (command.startsWith("gain ")) {
        int g = command.substring(5).toInt();
        if (g >= 1 && g <= 64) { micGain = g; noiseFloor = 0; Serial.printf("Mic gain: %dx\n", g); }
        else Serial.println("gain must be 1-64");
      } else if (command.startsWith("pause ")) {
        int ms = command.substring(6).toInt();
        if (ms >= 800 && ms <= 5000) {
          endSilenceMs = ms;
          Serial.printf("End-of-speech pause: %d ms\n", ms);
        } else {
          Serial.println("pause must be 800-5000 ms");
        }
      }
      command = "";
    } else if (command.length() < 16) command += c;
  }
  // These recovery commands also work with Serial Monitor set to
  // "No line ending".
  if (!Serial.available() && command == "web") {
    command = "";
    printLuluWebAddress();
  } else if (!Serial.available() && command == "clearreminders") {
    command = "";
    clearAllAlerts();
  }
  if (queuedSongPath.length() && !down && !pressedAt) {
    String song = queuedSongPath;
    queuedSongPath = "";
    playSong(song);
  }
  if (wakeMode && !servoCalibrationMode && !down && !pressedAt && !Serial.available()) recognize(true);
  delay(5);
}

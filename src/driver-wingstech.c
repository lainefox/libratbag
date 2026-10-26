/*
 * Copyright © 2026
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice (including the next
 * paragraph) shall be included in all copies or substantial portions of the
 * Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 *
 * Driver for the Wings Tech 2ea8:2203 vendor configuration protocol, used by
 * the Aqirys TGA Wired, the Fantech X17 Blake and the Sharkoon Light2 200.
 *
 * The device exposes two HID interfaces. Interface 0 is the ordinary boot
 * mouse; interface 1 is a vendor control channel that speaks a 64-byte
 * message protocol over interrupt OUT/IN. Control transfers do not work on
 * this dialect, so everything below goes through hidraw output/input reports.
 *
 * Message grammar, all frames 64 bytes:
 *
 *   04 a0 01 <cmd> ..            cmd 01 = get settings, 02 = set/commit
 *
 * A *settings* frame is tagged with 01 02 a5 at offset 4:
 *
 *   [ 4.. 6] 01 02 a5            header magic
 *   [ 7]      active DPI stage, 0-based
 *   [ 8]      per-stage enable mask
 *   [ 9..29]  7 x { u8 flag, u8 dpi_reg_x, u8 dpi_reg_y }
 *   [30..32]  opaque sensor settings, preserved verbatim (00 08 08)
 *   [33]      polling-rate selector, owned by the physical slider
 *   [34..36] 1a 0f a5            trailer magic
 *   [37]      LED effect
 *   [38]      LED effect speed
 *   [39]      LED brightness, 0-10
 *   [40]      active profile
 *   [41]      enabled colour mask
 *   [42..62]  7 x RGB
 *   [63]      reserved, zero
 *
 * A *binding* frame is tagged with 02 02 a5 at offset 4 and doubles as the
 * button-remap carrier and the commit signal:
 *
 *   [ 4.. 6] 02 02 a5            header magic
 *   [ 7..56]  10 x 5-byte binding records on a stride-5 grid from offset 7
 *   [57..63]  reserved, zero
 *
 * A binding record is { u8 tag, u8 class, u8 code, 0, 0 }. An all-zero record
 * means "native", i.e. no remap. Three records are permanent factory
 * residents and must be written back verbatim or the device loses them:
 * offset 32 (scroll up), offset 37 (scroll down), offset 47 (the fixed CPI
 * button) and offset 52 (LED cycle).
 *
 * The device is picky about sequencing. It only ever answers with the frames
 * a given request implies:
 *
 *   session opener 04 a0 01 00 -> one junk frame (must be filtered out)
 *   GET settings               -> settings frame, then binding frame
 *   SET settings               -> settings frame (echo)
 *   COMMIT bindings            -> binding frame (echo)
 *
 * so every request here reads exactly as many frames as the device sends,
 * which keeps stale replies out of the next transaction.
 *
 * The report rate in offset 33 is a dead end: the physical three-position
 * slider on the underside of these mice is authoritative and the firmware
 * clamps every software write back to the slider position. It is therefore
 * exposed read-only.
 *
 * The DPI registers are a firmware-internal lookup, not a sensor register:
 * the device echoes back whatever byte it is given. The register <-> DPI
 * relation below was recovered from the vendor Cfg.ini's DPI= list and the
 * factory stage bytes; see the DPI encoding comment further down.
 */

#include "config.h"

#include <assert.h>
#include <errno.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "libratbag-private.h"
#include "libratbag-hidraw.h"
#include "libratbag-data.h"

#define WT_FRAME_SIZE		64

/* Frame prefix, present on every message in either direction. */
#define WT_REPORT_ID		0x04
#define WT_MSG_TYPE_HI		0xa0
#define WT_MSG_TYPE_LO		0x01

#define WT_CMD_GET_SETTINGS	0x01
#define WT_CMD_SET_SETTINGS	0x02

#define WT_OFF_CMD		3
#define WT_OFF_MAGIC		4
#define WT_OFF_ACTIVE_STAGE	7
#define WT_OFF_STAGE_MASK	8
#define WT_OFF_STAGE0		9
#define WT_STAGE_STRIDE		3
#define WT_OFF_POLLING		33
#define WT_OFF_LED_EFFECT	37
#define WT_OFF_LED_SPEED	38
#define WT_OFF_LED_BRIGHTNESS	39
#define WT_OFF_PROFILE		40
#define WT_OFF_COLORS_ENABLED	41
#define WT_OFF_COLORS		42

#define WT_OFF_BIND_SLOT0	7
#define WT_BIND_STRIDE		5
#define WT_NUM_BIND_SLOTS	10

#define WT_NUM_PROFILES		1
#define WT_NUM_STAGES		7
#define WT_NUM_BUTTONS		6
#define WT_NUM_LEDS		1
#define WT_NUM_COLORS		7

/* Brightness is 0-10 on the wire and 0-255 in libratbag. */
#define WT_BRIGHTNESS_MAX_WIRE	10
#define WT_BRIGHTNESS_MAX	255

/*
 * LED effects, with the vendor's own names recovered from the OEM
 * application's text.xml (tc_led_mode1 .. tc_led_mode10, index N maps to wire
 * value N-1, matching the LedOpt1..LedOpt10 rows in Cfg.ini whose first field
 * runs 0..9 in order):
 *
 *   0 Prismo           5 Colorfull tail
 *   1 Breathe          6 Stream
 *   2 Steady           7 Reaction
 *   3 Neon             8 Heart
 *   4 Tail             9 LED OFF
 *
 * "implemented" was determined by eye on firmware 1.56 with every colour slot
 * set to full red, the colour mask fully enabled and speeds 0..2 swept:
 *
 *   Steady (2) and Heart (8) are dark at every speed, so a write never selects
 *   them and they read back as unlit. Steady's name suggests a per-DPI-stage
 *   indicator colour, and the settings frame has nowhere to put one - seven LED
 *   colours, seven DPI stages, no per-stage colour field - so this firmware
 *   looks like it never implemented it.
 *
 *   No implemented effect gives a genuinely steady light: Prismo, Tail and
 *   Stream animate at every speed and Breathe pulses. Neon is the closest, a
 *   solid colour that only drifts through the hue wheel, so it carries LED_ON
 *   in place of the dead Steady. A colour set through libratbag therefore will
 *   not stay put on this hardware.
 *
 *   LED OFF (9) is the one effect the firmware acts on structurally: it force
 *   zeroes speed, brightness and the colour mask whatever was written, which is
 *   why the write path has to restore them when switching back on.
 *
 * The speed byte only changes the rate of an animation, never whether there is
 * one: Breathe at speed 0 pulses faster than at speed 1, so a higher number
 * means slower, and Cfg.ini's SpeedParam=1,0,2 bounds it to 0..2.
 */
static const struct {
	const char *name;
	enum ratbag_led_mode mode;
	bool implemented;
} wt_led_effects[] = {
	[0] = { "Prismo",		RATBAG_LED_CYCLE,	true },
	[1] = { "Breathe",		RATBAG_LED_BREATHING,	true },
	[2] = { "Steady",		RATBAG_LED_ON,		true },
	[3] = { "Neon",			RATBAG_LED_CYCLE,	true },
	[4] = { "Tail",			RATBAG_LED_CYCLE,	true },
	[5] = { "Colorfull tail",	RATBAG_LED_CYCLE,	true },
	[6] = { "Stream",		RATBAG_LED_CYCLE,	true },
	[7] = { "Reaction",		RATBAG_LED_CYCLE,	true },
	[8] = { "Heart",		RATBAG_LED_CYCLE,	true },
	[9] = { "LED OFF",		RATBAG_LED_OFF,		true },
};

/* Wire values chosen when libratbag asks for a mode rather than naming one. */
#define WT_EFFECT_DEFAULT_CYCLE	0	/* Prismo, the vendor factory default */
#define WT_EFFECT_STEADY	2	/* Steady / Solid color */
#define WT_EFFECT_NEON		3
#define WT_EFFECT_BREATHE	1
#define WT_EFFECT_OFF		9

/* Vendor default animation rate, from the LedOpt rows in Cfg.ini. Speed only
 * scales the animation, it never turns it off. */
#define WT_LED_SPEED_MIN	0
#define WT_LED_SPEED_MAX	2
#define WT_LED_SPEED_DEFAULT	1

/*
 * Speed is 0..2 on the wire (0=fast, 1=medium/default, 2=slow).
 * Libratbag expresses this as effect duration in milliseconds (0..10000ms),
 * where shorter duration means faster animation.
 */
static const unsigned int wt_led_durations[] = {
	[0] = 2000,	/* fast */
	[1] = 5000,	/* medium / default */
	[2] = 8000,	/* slow */
};

/* Physical slider positions. Byte 33 tracks the slider and ignores writes. */
static const unsigned int wt_report_rates[] = { 125, 500, 1000 };
static const uint8_t wt_polling_raw[] = { 0x00, 0x02, 0x03 };

static const char *
wt_effect_name(uint8_t effect)
{
	return effect < ARRAY_LENGTH(wt_led_effects) ?
	       wt_led_effects[effect].name : "unknown";
}

static bool
wt_effect_works(uint8_t effect)
{
	return effect < ARRAY_LENGTH(wt_led_effects) &&
	       wt_led_effects[effect].implemented;
}

/* An effect this firmware never lights up presents as an unlit LED, so report
 * it as off rather than claiming a mode the user cannot see. */
static enum ratbag_led_mode
wt_effect_mode(uint8_t effect)
{
	if (!wt_effect_works(effect))
		return RATBAG_LED_OFF;

	return wt_led_effects[effect].mode;
}

/*
 * DPI encoding.
 *
 * The per-stage register is a firmware-internal step index, not a sensor
 * register: the device echoes back whatever byte it is given, and the same
 * register independently drives both axes. The scale was recovered from the
 * vendor's own DPI list and the factory stage bytes of this device:
 *
 *   Cfg.ini DPI=          400  800 1200 2400 3200 6400 16000
 *   factory stage reg       8   16   24   48   64  128    64
 *   factory stage flag     00   00   00   00   00   00    11
 *
 * Every entry except the last is the register times 50. The last stage is
 * 16000 but its register is only 64, so the low nibble of the per-stage flag
 * byte supplies the high four bits of a 12-bit value:
 *
 *   dpi = (((flag & 0x0f) << 8) | reg) * 50
 *
 * which gives 320 * 50 = 16000 for the factory top stage. The high nibble of
 * the flag is left untouched; only its low nibble belongs to the DPI value.
 *
 * An earlier revision fitted dpi = 43.5 * reg from pointer-travel
 * measurements. That slope reproduced the same measurements but was ~13% low
 * at the nominal figures, because a constant distance error in the ruler
 * slides is indistinguishable from a slope error. The vendor table above is
 * self-consistent and matches every factory stage exactly, so it wins; the
 * driver now reports the figures the vendor utility and the product page use.
 */
#define WT_DPI_PER_REG		50
#define WT_DPI_MAX_VALUE	0xfff	/* 12-bit value: 204750 dpi ceiling */

/*
 * Offered resolutions. All are whole register steps, so every one round-trips
 * exactly.
 */
static const unsigned int wt_dpi_list[] = {
	  50,  100,  150,  200,  300,  400,   500,   600,   800,  1000,
	 1200,  1400, 1600,  1800,  2000,  2400,  2800,  3200,  3600,  4000,
	 4500,  5000,  6000,  7000,  8000,  9000, 10000, 12000, 16000,
};

static inline unsigned int
wt_clamp(unsigned int value, unsigned int low, unsigned int high)
{
	if (value < low)
		return low;
	if (value > high)
		return high;
	return value;
}

struct wt_stage_data {
	uint8_t flag;		/* opaque per-stage byte, preserved verbatim */
	uint8_t reg_x;
	uint8_t reg_y;
};

struct wt_data {
	uint8_t frame[WT_FRAME_SIZE];
	uint8_t bindings[WT_FRAME_SIZE];
	uint8_t stages[WT_NUM_STAGES];
	uint8_t colors[WT_NUM_COLORS][3];
	/*
	 * Brightness the user last asked for, kept separately from the frame
	 * because selecting LED OFF makes the firmware force the frame's
	 * brightness to zero. Without this, switching the LED off and on again
	 * would restore brightness 0 and leave the mouse dark.
	 */
	uint8_t brightness;
	/*
	 * Animation speed (duration) the user last asked for, kept separately
	 * for the same reason.
	 */
	uint8_t speed;
};

static const uint8_t wt_magic_settings[3] = { 0x01, 0x02, 0xa5 };
static const uint8_t wt_magic_bindings[3] = { 0x02, 0x02, 0xa5 };

/* Binding record tags. */
#define WT_BIND_TAG_KEY		0xfc
#define WT_BIND_KEY_CLASS	0x00
#define WT_BIND_KEY_CLASS_CTRL	0x01

/* Bare-tag built-in functions. */
#define WT_TAG_VOL_UP		0x90
#define WT_TAG_VOL_DOWN		0x91
#define WT_TAG_MUTE		0x92
#define WT_TAG_PLAY_PAUSE	0x93
#define WT_TAG_STOP		0x94
#define WT_TAG_PREV_TRACK	0x95
#define WT_TAG_NEXT_TRACK	0x96
#define WT_TAG_LEFT_CLICK	0xb0
#define WT_TAG_RIGHT_CLICK	0xb1
#define WT_TAG_MIDDLE_CLICK	0xb2
#define WT_TAG_NAV_FORWARD	0xb3
#define WT_TAG_NAV_BACK		0xb4
#define WT_TAG_SCROLL_UP	0xb5
#define WT_TAG_SCROLL_DOWN	0xb6

/* Slot offsets that hold a permanent factory resident. Writing a commit frame
 * without these clears them, so the cached table is always echoed back.
 * Slots 32/37 are wheel up/down and slot 52 is the LED-cycle resident. */
static const unsigned int wt_resident_slots[] = { 32, 37, 52 };

/* The six physical button slots, in logical order. Slots 32/37 are wheel
 * up/down and slot 52 is the LED-cycle resident; these are preserved verbatim
 * on write and not exposed as remappable buttons. */
static const unsigned int wt_button_slots[WT_NUM_BUTTONS] = {
	7, 12, 17, 22, 27, 47
};

/* A NULL magic matches any 64-byte frame carrying the frame prefix. */
static bool
wt_frame_magic(const uint8_t *buf, size_t len, const uint8_t *magic)
{
	if (len != WT_FRAME_SIZE)
		return false;
	if (buf[0] != WT_REPORT_ID || buf[1] != WT_MSG_TYPE_HI ||
	    buf[2] != WT_MSG_TYPE_LO)
		return false;
	if (!magic)
		return true;

	return !memcmp(buf + WT_OFF_MAGIC, magic, sizeof(wt_magic_settings));
}

/*
 * Accepts a settings or a binding frame and nothing else. The session opener
 * draws a reply with a different magic, so it uses wt_any_filter() instead.
 */
static bool
wt_response_filter(uint8_t *buf, size_t len)
{
	return wt_frame_magic(buf, len, wt_magic_settings) ||
	       wt_frame_magic(buf, len, wt_magic_bindings);
}

/* Accepts any 64-byte frame carrying the frame prefix, magic unexamined. */
static bool
wt_any_filter(uint8_t *buf, size_t len)
{
	return wt_frame_magic(buf, len, NULL);
}

/*
 * Send one frame and read back exactly the number of replies the device owes
 * us for it. Reading a fixed count matters: the device never mixes response
 * kinds within one request, so a fixed read cannot pick up a stale frame
 * left over from the previous transaction.
 */
static int
wt_xfer(struct ratbag_device *device, const uint8_t *out, size_t outlen,
	uint8_t (*in)[WT_FRAME_SIZE], size_t nframes,
	ratbagd_hidraw_filter_t filter)
{
	struct ratbag *ratbag = device->ratbag;
	size_t i;
	int rc;

	log_buf_raw(ratbag, "output report: ", out, outlen);

	rc = ratbag_hidraw_output_report(device, (uint8_t *)out, outlen);
	if (rc < 0) {
		log_error(ratbag, "failed to write 64-byte frame: %s\n",
			  strerror(-rc));
		return rc;
	}

	for (i = 0; i < nframes; i++) {
		rc = ratbag_hidraw_read_input_report(device, in[i],
						    WT_FRAME_SIZE, filter);
		if (rc < 0) {
			log_error(ratbag,
				  "timed out waiting for reply %zu of %zu: %s\n",
				  i + 1, nframes, strerror(-rc));
			return rc;
		}
	}

	return 0;
}

/*
 * The device only answers a request once its session opener has been seen
 * twice, exactly like the vendor application does at startup.
 */
static int
wt_open_session(struct ratbag_device *device)
{
	uint8_t opener[WT_FRAME_SIZE] = {
		WT_REPORT_ID, WT_MSG_TYPE_HI, WT_MSG_TYPE_LO, 0x00
	};
	uint8_t reply[WT_FRAME_SIZE];
	int rc, i;

	for (i = 0; i < 2; i++) {
		rc = wt_xfer(device, opener, sizeof(opener), &reply, 1,
			     wt_any_filter);
		if (rc < 0)
			return rc;
	}

	return 0;
}

static int
wt_get_settings(struct ratbag_device *device, struct wt_data *drv_data)
{
	uint8_t out[WT_FRAME_SIZE] = {
		WT_REPORT_ID, WT_MSG_TYPE_HI, WT_MSG_TYPE_LO, WT_CMD_GET_SETTINGS
	};
	uint8_t reply[2][WT_FRAME_SIZE];
	int rc;

	rc = wt_xfer(device, out, sizeof(out), reply, 2,
			wt_response_filter);
	if (rc < 0)
		return rc;

	if (!wt_frame_magic(reply[0], WT_FRAME_SIZE, wt_magic_settings)) {
		log_error(device->ratbag,
			  "expected a settings frame, got header %02x%02x%02x\n",
			  reply[0][WT_OFF_MAGIC], reply[0][WT_OFF_MAGIC + 1],
			  reply[0][WT_OFF_MAGIC + 2]);
		return -EPROTO;
	}

	/* The trailing frame is the binding table, which the device volunteers on
	 * every GET. Caching it here is what lets a commit re-send the factory
	 * residents instead of silently wiping them. */
	if (!wt_frame_magic(reply[1], WT_FRAME_SIZE, wt_magic_bindings)) {
		log_error(device->ratbag,
			  "expected a binding frame, got header %02x%02x%02x\n",
			  reply[1][WT_OFF_MAGIC], reply[1][WT_OFF_MAGIC + 1],
			  reply[1][WT_OFF_MAGIC + 2]);
		return -EPROTO;
	}

	memcpy(drv_data->frame, reply[0], WT_FRAME_SIZE);
	memcpy(drv_data->bindings, reply[1], WT_FRAME_SIZE);

	return 0;
}

static int
wt_set_settings(struct ratbag_device *device, struct wt_data *drv_data)
{
	uint8_t reply[WT_FRAME_SIZE];
	int rc;

	drv_data->frame[WT_OFF_CMD] = WT_CMD_SET_SETTINGS;

	rc = wt_xfer(device, drv_data->frame, WT_FRAME_SIZE, &reply, 1,
			wt_response_filter);
	if (rc < 0)
		return rc;

	if (!wt_frame_magic(reply, WT_FRAME_SIZE, wt_magic_settings)) {
		log_error(device->ratbag,
			  "SET was not acknowledged with a settings frame\n");
		return -EPROTO;
	}

	return 0;
}

static int
wt_commit_bindings(struct ratbag_device *device, struct wt_data *drv_data)
{
	uint8_t reply[WT_FRAME_SIZE];
	int rc;

	drv_data->bindings[0] = WT_REPORT_ID;
	drv_data->bindings[1] = WT_MSG_TYPE_HI;
	drv_data->bindings[2] = WT_MSG_TYPE_LO;
	drv_data->bindings[WT_OFF_CMD] = WT_CMD_SET_SETTINGS;
	memcpy(drv_data->bindings + WT_OFF_MAGIC, wt_magic_bindings,
	       sizeof(wt_magic_bindings));

	rc = wt_xfer(device, drv_data->bindings, WT_FRAME_SIZE, &reply, 1,
			wt_response_filter);
	if (rc < 0)
		return rc;

	if (!wt_frame_magic(reply, WT_FRAME_SIZE, wt_magic_bindings)) {
		log_error(device->ratbag,
			  "COMMIT was not acknowledged with a binding frame\n");
		return -EPROTO;
	}

	return 0;
}

/*
 * The config interface is the one declaring numbered reports; the boot mouse
 * interface has none. This is how ratbag_find_hidraw() picks the right
 * sibling hidraw node for a device that exposes both.
 */
static int
wt_test_hidraw(struct ratbag_device *device)
{
	return ratbag_hidraw_has_report(device, 1);
}

/*
 * stage -> dpi. The low nibble of the flag byte is the high four bits of the
 * 12-bit DPI value; see the DPI encoding comment above.
 */
static unsigned int
wt_stage_to_dpi(uint8_t flag, uint8_t reg)
{
	unsigned int value = ((unsigned int)(flag & 0x0f) << 8) | reg;

	return value * WT_DPI_PER_REG;
}

/*
 * dpi -> stage. Rounds to the nearest register step, clamps to the 12-bit
 * range, and preserves the flag's high nibble, which carries per-stage bits
 * that have nothing to do with DPI.
 */
static void
wt_dpi_to_stage(unsigned int dpi, uint8_t *flag, uint8_t *reg)
{
	unsigned int value = (dpi + WT_DPI_PER_REG / 2) / WT_DPI_PER_REG;

	value = wt_clamp(value, 1, WT_DPI_MAX_VALUE);
	*flag = (uint8_t)((*flag & 0xf0) | ((value >> 8) & 0x0f));
	*reg = (uint8_t)(value & 0xff);
}

static void
wt_fill_dpi_list(struct ratbag_resolution *res)
{
	ratbag_resolution_set_dpi_list(res, wt_dpi_list,
				       ARRAY_LENGTH(wt_dpi_list));
}

static unsigned int
wt_read_polling(const uint8_t *frame)
{
	uint8_t raw = frame[WT_OFF_POLLING];
	size_t i;

	for (i = 0; i < ARRAY_LENGTH(wt_polling_raw); i++) {
		if (wt_polling_raw[i] == raw)
			return wt_report_rates[i];
	}

	return wt_report_rates[0];
}

static unsigned int
wt_led_brightness_from_wire(uint8_t raw)
{
	return (unsigned int)raw * WT_BRIGHTNESS_MAX / WT_BRIGHTNESS_MAX_WIRE;
}

static uint8_t
wt_led_brightness_to_wire(unsigned int brightness)
{
	return (uint8_t)wt_clamp(brightness * WT_BRIGHTNESS_MAX_WIRE /
				 WT_BRIGHTNESS_MAX, 0,
				 WT_BRIGHTNESS_MAX_WIRE);
}

static unsigned int
wt_led_duration_from_wire(uint8_t raw)
{
	if (raw >= ARRAY_LENGTH(wt_led_durations))
		return wt_led_durations[WT_LED_SPEED_DEFAULT];
	return wt_led_durations[raw];
}

static uint8_t
wt_led_duration_to_wire(unsigned int duration_ms)
{
	if (duration_ms <= 3500)
		return 0;	/* fast */
	if (duration_ms <= 6500)
		return 1;	/* medium / default */
	return 2;		/* slow */
}

static bool
wt_slot_is_resident(unsigned int offset)
{
	size_t i;

	for (i = 0; i < ARRAY_LENGTH(wt_resident_slots); i++) {
		if (wt_resident_slots[i] == offset)
			return true;
	}

	return false;
}

static void
wt_set_action_none(struct ratbag_button *button)
{
	struct ratbag_button_action action = {0};

	action.type = RATBAG_BUTTON_ACTION_TYPE_NONE;
	ratbag_button_set_action(button, &action);
}

static void
wt_set_action_button(struct ratbag_button *button, unsigned int btn)
{
	struct ratbag_button_action action = {0};

	action.type = RATBAG_BUTTON_ACTION_TYPE_BUTTON;
	action.action.button = btn;
	ratbag_button_set_action(button, &action);
}

static void
wt_set_action_special(struct ratbag_button *button,
		      enum ratbag_button_action_special special)
{
	struct ratbag_button_action action = {0};

	action.type = RATBAG_BUTTON_ACTION_TYPE_SPECIAL;
	action.action.special = special;
	ratbag_button_set_action(button, &action);
}

/*
 * The built-in b0-b4 tags are mouse buttons. libratbag numbers them
 * independently of the wire tags, with left/right/middle as 1/2/3 and the
 * side buttons as back/forward 4/5.
 */
static const struct {
	uint8_t tag;
	unsigned int button;
} wt_button_tags[] = {
	{ WT_TAG_LEFT_CLICK,	1 },
	{ WT_TAG_RIGHT_CLICK,	2 },
	{ WT_TAG_MIDDLE_CLICK,	3 },
	{ WT_TAG_NAV_BACK,	4 },
	{ WT_TAG_NAV_FORWARD,	5 },
};

/*
 * The 90-96 tags are media keys. libratbag models those as key actions, and
 * the key codes are the Linux ones the input stack actually emits.
 */
static const struct {
	uint8_t tag;
	unsigned int key;
} wt_key_tags[] = {
	{ WT_TAG_VOL_UP,	KEY_VOLUMEUP },
	{ WT_TAG_VOL_DOWN,	KEY_VOLUMEDOWN },
	{ WT_TAG_MUTE,		KEY_MUTE },
	{ WT_TAG_PLAY_PAUSE,	KEY_PLAYPAUSE },
	{ WT_TAG_STOP,		KEY_STOPCD },
	{ WT_TAG_PREV_TRACK,	KEY_PREVIOUSSONG },
	{ WT_TAG_NEXT_TRACK,	KEY_NEXTSONG },
};

static unsigned int
wt_tag_to_button(uint8_t tag)
{
	size_t i;

	for (i = 0; i < ARRAY_LENGTH(wt_button_tags); i++) {
		if (wt_button_tags[i].tag == tag)
			return wt_button_tags[i].button;
	}

	return 0;
}

static uint8_t
wt_button_to_tag(unsigned int button)
{
	size_t i;

	for (i = 0; i < ARRAY_LENGTH(wt_button_tags); i++) {
		if (wt_button_tags[i].button == button)
			return wt_button_tags[i].tag;
	}

	return 0;
}

static unsigned int
wt_tag_to_key(uint8_t tag)
{
	size_t i;

	for (i = 0; i < ARRAY_LENGTH(wt_key_tags); i++) {
		if (wt_key_tags[i].tag == tag)
			return wt_key_tags[i].key;
	}

	return 0;
}

static uint8_t
wt_key_to_tag(unsigned int key)
{
	size_t i;

	for (i = 0; i < ARRAY_LENGTH(wt_key_tags); i++) {
		if (wt_key_tags[i].key == key)
			return wt_key_tags[i].tag;
	}

	return 0;
}

/*
 * An all-zero record is the firmware's "leave this button alone" value, so
 * the button keeps whatever action the hardware gives it. Report those
 * factory actions instead of claiming every native button is disabled.
 */
static void
wt_set_default_action(struct ratbag_button *button)
{
	switch (wt_button_slots[button->index]) {
	case 7:
		wt_set_action_button(button, 1);
		break;
	case 12:
		wt_set_action_button(button, 2);
		break;
	case 17:
		wt_set_action_button(button, 3);
		break;
	case 22:
		wt_set_action_button(button, 4);
		break;
	case 27:
		wt_set_action_button(button, 5);
		break;
	case 32:
		wt_set_action_special(button,
				      RATBAG_BUTTON_ACTION_SPECIAL_WHEEL_UP);
		break;
	case 37:
		wt_set_action_special(button,
				      RATBAG_BUTTON_ACTION_SPECIAL_WHEEL_DOWN);
		break;
	case 47:
		/* The single top CPI button, fixed in firmware. Pressing it
		 * cycles the active resolution up and wraps at the top stage. */
		wt_set_action_special(button,
				      RATBAG_BUTTON_ACTION_SPECIAL_RESOLUTION_CYCLE_UP);
		break;
	default:
		wt_set_action_none(button);
		break;
	}
}

static void
wt_read_button(struct ratbag_button *button, const struct wt_data *drv_data)
{
	struct ratbag_device *device = button->profile->device;
	unsigned int slot = wt_button_slots[button->index];
	const uint8_t *rec = drv_data->bindings + slot;
	uint8_t tag = rec[0], cls = rec[1], code = rec[2];
	unsigned int btn, key;

	if (!tag && !cls && !code) {
		wt_set_default_action(button);
		return;
	}

	if (tag == WT_BIND_TAG_KEY) {
		/* A key record with a zero usage is how the vendor application
		 * writes a disabled button. */
		if (!code) {
			wt_set_action_none(button);
			return;
		}

		/* Class 0x01 is a Ctrl-modified key. libratbag has no modifier
		 * field on a button action, so surface the bare key and refuse to
		 * write it back rather than silently dropping the modifier. */
		if (cls != WT_BIND_KEY_CLASS)
			log_debug(device->ratbag,
				  "button %u: Ctrl-modified key 0x%02x is read-only\n",
				  button->index, code);

		key = ratbag_hidraw_get_keycode_from_keyboard_usage(device, code);
		if (!key)
			key = ratbag_hidraw_get_keycode_from_consumer_usage(device,
									    code);
		if (!key) {
			log_debug(device->ratbag,
				  "button %u: unknown key usage 0x%02x, shown as unbound\n",
				  button->index, code);
			wt_set_action_none(button);
			return;
		}

		ratbag_button_set_key(button, key);
		return;
	}

	btn = wt_tag_to_button(tag);
	if (btn) {
		wt_set_action_button(button, btn);
		return;
	}

	key = wt_tag_to_key(tag);
	if (key) {
		ratbag_button_set_key(button, key);
		return;
	}

	switch (tag) {
	case WT_TAG_SCROLL_UP:
		wt_set_action_special(button,
				      RATBAG_BUTTON_ACTION_SPECIAL_WHEEL_UP);
		return;
	case WT_TAG_SCROLL_DOWN:
		wt_set_action_special(button,
				      RATBAG_BUTTON_ACTION_SPECIAL_WHEEL_DOWN);
		return;
	}

	log_debug(device->ratbag,
		  "button %u: unmapped binding tag 0x%02x, shown as unbound\n",
		  button->index, tag);
	wt_set_action_none(button);
}

static void
wt_write_button(struct ratbag_device *device, struct ratbag_button *button)
{
	struct wt_data *drv_data = ratbag_get_drv_data(device);
	unsigned int slot = wt_button_slots[button->index];
	uint8_t *rec = drv_data->bindings + slot;
	struct ratbag_button_action *action = &button->action;
	uint8_t newrec[WT_BIND_STRIDE] = {0};
	uint8_t tag;
	unsigned int key;
	uint8_t code;

	if (wt_slot_is_resident(slot))
		return;

	switch (action->type) {
	case RATBAG_BUTTON_ACTION_TYPE_NONE:
		/* fc 00 00 is the disabled encoding. The all-zero record
		 * means "native", which would leave the button working. */
		newrec[0] = WT_BIND_TAG_KEY;
		break;
	case RATBAG_BUTTON_ACTION_TYPE_BUTTON:
		tag = wt_button_to_tag(action->action.button);
		if (!tag) {
			log_debug(device->ratbag,
				  "button %u: logical button %u has no wire encoding\n",
				  button->index, action->action.button);
			return;
		}
		newrec[0] = tag;
		break;
	case RATBAG_BUTTON_ACTION_TYPE_SPECIAL:
		switch (action->action.special) {
		case RATBAG_BUTTON_ACTION_SPECIAL_WHEEL_UP:
			newrec[0] = WT_TAG_SCROLL_UP;
			break;
		case RATBAG_BUTTON_ACTION_SPECIAL_WHEEL_DOWN:
			newrec[0] = WT_TAG_SCROLL_DOWN;
			break;
		case RATBAG_BUTTON_ACTION_SPECIAL_RESOLUTION_CYCLE_UP:
			/* All-zero record restores native firmware CPI cycle on slot 47 */
			memset(newrec, 0, sizeof(newrec));
			break;
		default:
			log_debug(device->ratbag,
				  "button %u: special action %d has no wire encoding\n",
				  button->index, action->action.special);
			return;
		}
		break;
	case RATBAG_BUTTON_ACTION_TYPE_KEY:
		key = action->action.key;
		tag = wt_key_to_tag(key);
		if (tag) {
			newrec[0] = tag;
			break;
		}

		/* Bare keys are carried as HID keyboard usages, not Linux key
		 * codes: the device turns the byte straight into a HID report. */
		code = ratbag_hidraw_get_keyboard_usage_from_keycode(device,
								     key);
		if (!code) {
			log_debug(device->ratbag,
				  "button %u: key %u has no HID keyboard usage\n",
				  button->index, key);
			return;
		}
		newrec[0] = WT_BIND_TAG_KEY;
		newrec[1] = WT_BIND_KEY_CLASS;
		newrec[2] = code;
		break;
	default:
		log_debug(device->ratbag,
			  "button %u: action type %d has no wire encoding\n",
			  button->index, action->type);
		return;
	}

	memcpy(rec, newrec, sizeof(newrec));
}

static void
wt_read_resolution(struct ratbag_resolution *res,
		   struct ratbag_device *device,
		   const struct wt_data *drv_data)
{
	struct ratbag *ratbag = device->ratbag;
	const uint8_t *stage = drv_data->frame + WT_OFF_STAGE0 +
			      res->index * WT_STAGE_STRIDE;
	unsigned int dpi_x, dpi_y;

	dpi_x = wt_stage_to_dpi(stage[0], stage[1]);
	dpi_y = wt_stage_to_dpi(stage[0], stage[2]);

	ratbag_resolution_set_resolution(res, dpi_x, dpi_y);
	wt_fill_dpi_list(res);

	res->is_active = res->index == drv_data->frame[WT_OFF_ACTIVE_STAGE];
	res->is_disabled = !(drv_data->frame[WT_OFF_STAGE_MASK] &
			     (1 << res->index));

	ratbag_resolution_set_cap(res, RATBAG_RESOLUTION_CAP_DISABLE);
	ratbag_resolution_set_cap(res,
				  RATBAG_RESOLUTION_CAP_SEPARATE_XY_RESOLUTION);

	log_debug(ratbag, "  stage %u: %ux%u dpi reg %02x/%02x%s\n",
		  res->index, dpi_x, dpi_y, stage[1], stage[2],
		  res->is_disabled ? " (disabled)" : "");
}

static void
wt_write_resolution(struct ratbag_resolution *res)
{
	struct ratbag_device *device = res->profile->device;
	struct wt_data *drv_data = ratbag_get_drv_data(device);
	uint8_t *stage = drv_data->frame + WT_OFF_STAGE0 +
			 res->index * WT_STAGE_STRIDE;
	unsigned int mask = drv_data->frame[WT_OFF_STAGE_MASK];
	bool enabled = !res->is_disabled;

	wt_dpi_to_stage(res->dpi_x, &stage[0], &stage[1]);
	wt_dpi_to_stage(res->dpi_y, &stage[0], &stage[2]);

	if (enabled)
		mask |= 1 << res->index;
	else
		mask &= ~(1 << res->index);

	drv_data->frame[WT_OFF_STAGE_MASK] = (uint8_t)mask;
}

/*
 * The seven stored colours are a palette the active effect draws from, not
 * seven addressable LED positions. The mouse has one light - the strip along
 * its rear, with the wheel lit from the same signal - and an effect such as
 * Prismo or Stream animates the whole strip through some subset of the seven
 * entries. The mask says which entries are in play.
 *
 * libratbag carries a single colour, so a write has to paint every entry the
 * effect might reach for. Picking just one of them would mean guessing which
 * entry the effect uses, and a wrong guess leaves the strip showing the old
 * colour with nothing on screen to say so.
 */
static void
wt_led_set_color(struct wt_data *drv_data, const struct ratbag_color *color)
{
	unsigned int i;

	/* A clear mask is what selecting LED OFF leaves behind, and it leaves the
	 * effect with nothing to draw. Re-enable the first entry so that switching
	 * the LED back on has a colour to show. */
	if (!drv_data->frame[WT_OFF_COLORS_ENABLED])
		drv_data->frame[WT_OFF_COLORS_ENABLED] = 1;

	for (i = 0; i < WT_NUM_COLORS; i++) {
		drv_data->colors[i][0] = color->red;
		drv_data->colors[i][1] = color->green;
		drv_data->colors[i][2] = color->blue;
		memcpy(drv_data->frame + WT_OFF_COLORS + i * 3,
		       drv_data->colors[i], 3);
	}
}

/*
 * The entry to report as the LED's colour. libratbag shows one colour and
 * cannot express a palette, so this is the lowest enabled entry - which after
 * a write through libratbag is the same colour as all the others.
 */
static unsigned int
wt_led_slot(const struct wt_data *drv_data)
{
	uint8_t mask = drv_data->frame[WT_OFF_COLORS_ENABLED];
	unsigned int i;

	for (i = 0; i < WT_NUM_COLORS; i++) {
		if (mask & (1 << i))
			return i;
	}

	return 0;
}

static void
wt_read_led(struct ratbag_led *led, struct ratbag_device *device,
	    const struct wt_data *drv_data)
{
	struct ratbag *ratbag = device->ratbag;
	const uint8_t *frame = drv_data->frame;
	uint8_t effect = frame[WT_OFF_LED_EFFECT];
	unsigned int slot = 0;
	struct ratbag_color color;

	/* The effect draws from one of the stored colours; follow the mask so the
	 * colour libratbag shows is one the device is actually using. */
	slot = wt_led_slot(drv_data);

	color.red = drv_data->colors[slot][0];
	color.green = drv_data->colors[slot][1];
	color.blue = drv_data->colors[slot][2];

	ratbag_led_set_mode(led, wt_effect_mode(effect));
	ratbag_led_set_color(led, color);
	ratbag_led_set_brightness(led,
				  wt_led_brightness_from_wire(
					  frame[WT_OFF_LED_BRIGHTNESS]));
	if (effect == WT_EFFECT_OFF || effect == WT_EFFECT_STEADY) {
		ratbag_led_set_effect_duration(led, 0);
	} else {
		ratbag_led_set_effect_duration(led,
					       wt_led_duration_from_wire(
						       frame[WT_OFF_LED_SPEED]));
	}

	/* Every mode libratbag can express has a wire encoding here: ON maps
	 * to Neon (the only steady effect this firmware implements), BREATHING
	 * to Breathe, CYCLE to the animated effects, and OFF to LED OFF.
	 * Without these the UI offers only "off". */
	ratbag_led_set_mode_capability(led, RATBAG_LED_OFF);
	ratbag_led_set_mode_capability(led, RATBAG_LED_ON);
	ratbag_led_set_mode_capability(led, RATBAG_LED_BREATHING);
	ratbag_led_set_mode_capability(led, RATBAG_LED_CYCLE);

	log_debug(ratbag, "  led: effect %u (%s) speed %u (%ums) brightness %u "
		  "colour %u rgb(%u,%u,%u)\n", effect, wt_effect_name(effect),
		  frame[WT_OFF_LED_SPEED],
		  wt_led_duration_from_wire(frame[WT_OFF_LED_SPEED]),
		  frame[WT_OFF_LED_BRIGHTNESS], slot,
		  color.red, color.green, color.blue);
}

static void
wt_write_led(struct ratbag_led *led)
{
	struct ratbag_device *device = led->profile->device;
	struct wt_data *drv_data = ratbag_get_drv_data(device);
	uint8_t effect = drv_data->frame[WT_OFF_LED_EFFECT];

	wt_led_set_color(drv_data, &led->color);

	/* libratbag only distinguishes off / on / breathe / cycle, and most of
	 * the vendor effects are all just "some animation". Keep whatever
	 * animated effect was already selected where that is compatible with
	 * what was asked for, so switching brightness or colour does not
	 * silently rewrite the effect the user picked in the vendor tool. */
	switch (led->mode) {
	case RATBAG_LED_OFF:
		effect = WT_EFFECT_OFF;
		break;
	case RATBAG_LED_ON:
		effect = WT_EFFECT_STEADY;
		break;
	case RATBAG_LED_BREATHING:
		effect = WT_EFFECT_BREATHE;
		break;
	default:
		if (wt_effect_mode(effect) != RATBAG_LED_CYCLE)
			effect = WT_EFFECT_DEFAULT_CYCLE;
		break;
	}

	drv_data->frame[WT_OFF_LED_EFFECT] = effect;

	/*
	 * Selecting LED OFF makes the firmware force the frame's brightness,
	 * speed and colour mask to zero behind our back, so remember the
	 * brightness that was asked for and put it back when the LED comes on
	 * again. A brightness of zero is treated as "not set" rather than as a
	 * request for a dark LED, since that is indistinguishable from the
	 * zero the firmware just wrote.
	 */
	if (led->brightness > 0)
		drv_data->brightness =
			wt_led_brightness_to_wire(led->brightness);
	if (drv_data->brightness == 0)
		drv_data->brightness = WT_BRIGHTNESS_MAX_WIRE;

	if (led->ms > 0)
		drv_data->speed = wt_led_duration_to_wire(led->ms);
	if (drv_data->speed > WT_LED_SPEED_MAX)
		drv_data->speed = WT_LED_SPEED_DEFAULT;

	if (effect == WT_EFFECT_OFF) {
		/* Nothing else survives this, and writing the values back would
		 * just be overwritten. */
		drv_data->frame[WT_OFF_LED_BRIGHTNESS] = 0;
		drv_data->frame[WT_OFF_LED_SPEED] = 0;
		drv_data->frame[WT_OFF_COLORS_ENABLED] = 0;
		return;
	}

	drv_data->frame[WT_OFF_LED_BRIGHTNESS] = drv_data->brightness;

	if (effect == WT_EFFECT_STEADY) {
		drv_data->frame[WT_OFF_COLORS_ENABLED] = 1;
		drv_data->frame[WT_OFF_LED_SPEED] = 0;
	} else {
		drv_data->frame[WT_OFF_LED_SPEED] = drv_data->speed;
	}

	/* wt_led_set_color() already restored the mask if LED OFF had cleared it,
	 * but a client that only ever changed the effect leaves the mask alone and
	 * it can still be zero from a previous off state. */
	if (!drv_data->frame[WT_OFF_COLORS_ENABLED])
		drv_data->frame[WT_OFF_COLORS_ENABLED] = 1;
}

static int
wt_probe(struct ratbag_device *device)
{
	struct wt_data *drv_data;
	struct ratbag_profile *profile;
	struct ratbag_resolution *resolution;
	struct ratbag_led *led;
	struct ratbag_button *button;
	struct ratbag *ratbag = device->ratbag;
	unsigned int i;
	int rc;

	rc = ratbag_find_hidraw(device, wt_test_hidraw);
	if (rc)
		return rc;

	drv_data = zalloc(sizeof(*drv_data));
	if (!drv_data)
		return -ENOMEM;
	ratbag_set_drv_data(device, drv_data);

	rc = wt_open_session(device);
	if (rc)
		goto err;

	rc = wt_get_settings(device, drv_data);
	if (rc)
		goto err;

	if (device->data) {
		const char *data_name = ratbag_device_data_get_name(device->data);
		if (data_name) {
			free(device->name);
			device->name = strdup_safe(data_name);
		}
	}

	log_debug(ratbag, "found %s, version %04x, active profile %u\n",
		  ratbag_device_get_name(device),
		  ratbag_device_get_product_version(device),
		  drv_data->frame[WT_OFF_PROFILE]);

	for (i = 0; i < WT_NUM_COLORS; i++) {
		memcpy(drv_data->colors[i],
		       drv_data->frame + WT_OFF_COLORS + i * 3, 3);
	}

	drv_data->brightness = drv_data->frame[WT_OFF_LED_BRIGHTNESS];
	drv_data->speed = drv_data->frame[WT_OFF_LED_SPEED];
	if (drv_data->speed == 0 && drv_data->frame[WT_OFF_LED_EFFECT] == WT_EFFECT_OFF)
		drv_data->speed = WT_LED_SPEED_DEFAULT;
	else if (drv_data->speed > WT_LED_SPEED_MAX)
		drv_data->speed = WT_LED_SPEED_DEFAULT;

	ratbag_device_init_profiles(device, WT_NUM_PROFILES, WT_NUM_STAGES,
				    WT_NUM_BUTTONS, WT_NUM_LEDS);

	ratbag_device_for_each_profile(device, profile) {
		profile->name = strdup("Default");
		profile->is_active = true;
		profile->is_enabled = true;

		ratbag_profile_set_cap(profile, RATBAG_PROFILE_CAP_DISABLE);

		/* Byte 33 is owned by the physical slider, so report the
		 * hardware's choice and never write one back. Because the
		 * report rate cannot be set via software, report only the
		 * active hardware rate in the rate list. */
		profile->hz = wt_read_polling(drv_data->frame);
		profile->rate_dirty = false;
		ratbag_profile_set_report_rate_list(profile, &profile->hz, 1);

		ratbag_profile_for_each_resolution(profile, resolution)
			wt_read_resolution(resolution, device, drv_data);

		ratbag_profile_for_each_led(profile, led)
			wt_read_led(led, device, drv_data);

		ratbag_profile_for_each_button(profile, button) {
			/* The binding records carry a bare HID usage id for
			 * keys and the built-in b0-b6 tag family for mouse
			 * actions, so all three action types round-trip.
			 * Macro recording has no wire encoding. */
			ratbag_button_enable_action_type(button,
					RATBAG_BUTTON_ACTION_TYPE_NONE);
			ratbag_button_enable_action_type(button,
					RATBAG_BUTTON_ACTION_TYPE_BUTTON);
			ratbag_button_enable_action_type(button,
					RATBAG_BUTTON_ACTION_TYPE_SPECIAL);
			ratbag_button_enable_action_type(button,
					RATBAG_BUTTON_ACTION_TYPE_KEY);
			wt_read_button(button, drv_data);
		}

		/* The public setters used above (ratbag_led_set_mode() and
		 * friends) mark the profile dirty, but every one of them was fed
		 * the value we just read off the device. Clear the flags so a
		 * freshly probed device is not immediately written back to. */
		profile->dirty = false;
		ratbag_profile_for_each_resolution(profile, resolution)
			resolution->dirty = false;
		ratbag_profile_for_each_led(profile, led)
			led->dirty = false;
		ratbag_profile_for_each_button(profile, button)
			button->dirty = false;
	}

	return 0;

err:
	ratbag_set_drv_data(device, NULL);
	free(drv_data);
	ratbag_close_hidraw(device);
	return rc;
}

static int
wt_commit(struct ratbag_device *device)
{
	struct ratbag *ratbag = device->ratbag;
	struct wt_data *drv_data = ratbag_get_drv_data(device);
	struct ratbag_profile *profile;
	struct ratbag_resolution *resolution;
	struct ratbag_led *led;
	struct ratbag_button *button;
	int rc;

	ratbag_device_for_each_profile(device, profile) {
		if (!profile->dirty)
			continue;

		ratbag_profile_for_each_resolution(profile, resolution) {
			if (!resolution->dirty)
				continue;
			wt_write_resolution(resolution);
		}

		/* The active stage is profile state, not a property of whichever
		 * resolution happened to be written last. Writing it here also
		 * covers a resolution that was only switched active without any
		 * DPI change. */
		ratbag_profile_for_each_resolution(profile, resolution) {
			if (resolution->is_active) {
				drv_data->frame[WT_OFF_ACTIVE_STAGE] =
					(uint8_t)resolution->index;
				break;
			}
		}

		ratbag_profile_for_each_led(profile, led) {
			if (!led->dirty)
				continue;
			wt_write_led(led);
		}

		/* The rate is not writable, drop any pending change so it does
		 * not get re-applied on every commit. */
		profile->rate_dirty = false;

		ratbag_profile_for_each_button(profile, button) {
			if (!button->dirty)
				continue;
			wt_write_button(device, button);
		}
	}

	rc = wt_set_settings(device, drv_data);
	if (rc)
		goto out;

	/* Give the MCU time to complete flash writes before the next command */
	usleep(30000);

	rc = wt_commit_bindings(device, drv_data);
	if (rc)
		goto out;

	usleep(30000);

	/* Re-read so the cache reflects what the firmware actually accepted
	 * rather than what we asked for. */
	rc = wt_get_settings(device, drv_data);

out:
	if (rc)
		log_error(ratbag, "failed to commit: %s\n", strerror(-rc));

	return rc;
}

static int
wt_poll(struct ratbag_device *device)
{
	struct wt_data *drv_data = ratbag_get_drv_data(device);
	uint8_t reply[2][WT_FRAME_SIZE];
	uint8_t cmd[WT_FRAME_SIZE] = {
		WT_REPORT_ID, WT_MSG_TYPE_HI, WT_MSG_TYPE_LO, WT_CMD_GET_SETTINGS
	};
	struct ratbag_profile *profile;
	struct ratbag_resolution *res;
	uint8_t active_stage;
	uint8_t polling_byte;
	bool changed = false;
	int rc;

	if (!drv_data) {
		log_debug(device->ratbag, "wt_poll: no drv_data\n");
		return 0;
	}

	rc = wt_xfer(device, cmd, WT_FRAME_SIZE, reply, 2, wt_response_filter);
	if (rc < 0) {
		log_debug(device->ratbag, "wt_poll: wt_xfer failed %d\n", rc);
		return rc;
	}

	if (!wt_frame_magic(reply[0], WT_FRAME_SIZE, wt_magic_settings)) {
		log_debug(device->ratbag, "wt_poll: invalid magic %02x%02x%02x\n",
			  reply[0][4], reply[0][5], reply[0][6]);
		return 0;
	}

	profile = ratbag_device_get_profile(device, 0);

	active_stage = reply[0][WT_OFF_ACTIVE_STAGE];
	if (active_stage != drv_data->frame[WT_OFF_ACTIVE_STAGE]) {
		log_debug(device->ratbag, "wt_poll: stage changed from %d to %d\n",
			  drv_data->frame[WT_OFF_ACTIVE_STAGE], active_stage);
		drv_data->frame[WT_OFF_ACTIVE_STAGE] = active_stage;
		if (profile) {
			ratbag_profile_for_each_resolution(profile, res) {
				res->is_active = (res->index == active_stage);
			}
		}
		changed = true;
	}

	polling_byte = reply[0][WT_OFF_POLLING];
	if (polling_byte != drv_data->frame[WT_OFF_POLLING]) {
		drv_data->frame[WT_OFF_POLLING] = polling_byte;
		if (profile) {
			profile->hz = wt_read_polling(reply[0]);
			ratbag_profile_set_report_rate_list(profile, &profile->hz, 1);
			log_debug(device->ratbag, "wt_poll: updated profile hz to %u\n", profile->hz);
		}
		changed = true;
	}

	return changed ? 1 : 0;
}

static void
wt_remove(struct ratbag_device *device)
{
	struct wt_data *drv_data = ratbag_get_drv_data(device);

	free(drv_data);
	ratbag_set_drv_data(device, NULL);
	ratbag_close_hidraw(device);
}

struct ratbag_driver wingstech_driver = {
	.name = "Wings Tech",
	.id = "wings-tech",
	.probe = wt_probe,
	.remove = wt_remove,
	.commit = wt_commit,
	.poll = wt_poll,
};

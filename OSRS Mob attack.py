import ctypes
import json
import os
import random
import time
from dataclasses import dataclass
from datetime import datetime
from typing import List, Optional, Tuple

import cv2
import mss
import numpy as np
import psutil
import pyautogui
from pynput import keyboard


BASE_DIR = os.path.dirname(os.path.abspath(__file__))

# -----------------------------
# CONFIG
# -----------------------------
WINDOW_PROCESS_NAME = "osclient.exe"
WINDOW_TITLE_HINT = "Old School RuneScape"

MOB_CONFIG_DIR = os.path.join(BASE_DIR, "config", "mob")
LEGACY_GOBLIN_CONF_PATH = os.path.join(BASE_DIR, "mob", "goblin", "goblin.conf")
SCRIPT_CONF_PATH = os.path.join(BASE_DIR, "config", "script.conf")

# Regioes relativas ao client da janela
GAME_VIEW_REL = (0.02, 0.04, 0.74, 0.66)
MOB_HUB_REGION_REL = (0.00, 0.00, 0.22, 0.12)

# Cores HSV
HSV_RED_RANGES = [
    ((0, 120, 80), (10, 255, 255)),
    ((170, 120, 80), (180, 255, 255)),
]
HSV_YELLOW_RANGE = ((20, 90, 90), (40, 255, 255))
HSV_MOB_GREEN_RANGE = ((35, 90, 60), (90, 255, 255))

# Deteccao por cor (mob)
PALETTE_MAX_CLUSTERS = 4
COLOR_H_TOL_BASE = 10
COLOR_S_TOL_BASE = 45
COLOR_V_TOL_BASE = 45
COLOR_MIN_AREA = 65
COLOR_MAX_AREA_RATIO = 0.12
COLOR_EDGE_DENSITY_MIN = 0.042
PALETTE_MIN_COLORS_IN_BBOX = 2
PALETTE_MIN_PIXELS_PER_COLOR = 8
CANDIDATE_TOP_K = 10
CENTER_DISTANCE_PENALTY = 2100.0
CENTER_DISTANCE_POWER = 1.35
CENTER_CLOSENESS_BONUS = 900.0
CENTER_CLOSENESS_POWER = 1.85
AREA_SCORE_WEIGHT = 1.9
COLOR_PIXEL_SCORE_WEIGHT = 1.4
EDGE_SCORE_WEIGHT = 420.0
COLOR_HITS_SCORE_WEIGHT = 220.0

# Marcador de clique (apos left click)
CLICK_MARKER_WAIT_SECONDS = 0.10
CLICK_MARKER_BOX = 26
CLICK_MARKER_RED_MIN_PIXELS = 16
CLICK_MARKER_YELLOW_MIN_PIXELS = 16

# Timings
MAIN_LOOP_SLEEP = 0.05
WINDOW_REFRESH_SECONDS = 1.0
MIN_SECONDS_BETWEEN_ATTACKS = 0.55
AFTER_ATTACK_SLEEP = 0.24
NO_TARGET_STREAK_FOR_SCAN = 5
NO_TARGET_SPIN_BEFORE_TILT_DOWN_SECONDS = 10.0
CAMERA_ZOOM_OUT_SCROLL_AMOUNT = -280
CAMERA_ZOOM_IN_SCROLL_AMOUNT = 1400
CAMERA_SCAN_COOLDOWN_SECONDS = 0.60
CAMERA_ROTATE_RIGHT_60_SECONDS = 0.58
CAMERA_TILT_UP_SECONDS = 3.0
CAMERA_TILT_DOWN_SECONDS = 3.0
SAFETY_PAUSE_INTERVAL_MIN_SECONDS = 120.0
SAFETY_PAUSE_INTERVAL_MAX_SECONDS = 600.0
SAFETY_PAUSE_DURATION_MIN_SECONDS = 30.0
SAFETY_PAUSE_DURATION_MAX_SECONDS = 180.0

# Controle de combate
POST_CLICK_WAIT_HUB_SECONDS = 10.0
POST_CLICK_MAX_LOCK_SECONDS = 55.0
POST_COMBAT_NEXT_TARGET_DELAY_SECONDS = 2.5
SEARCH_SCAN_LIMIT = 10
DEFAULT_COMBAT_GREEN_MIN_PIXELS = 220
DEFAULT_MAX_RUNTIME_HOURS = 3.0

LOG_VERBOSE = False


@dataclass
class Region:
    left: int
    top: int
    width: int
    height: int

    @property
    def monitor(self):
        return {
            "left": self.left,
            "top": self.top,
            "width": self.width,
            "height": self.height,
        }


@dataclass
class ClientRect:
    left: int
    top: int
    width: int
    height: int


class POINT(ctypes.Structure):
    _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long)]


class RECT(ctypes.Structure):
    _fields_ = [
        ("left", ctypes.c_long),
        ("top", ctypes.c_long),
        ("right", ctypes.c_long),
        ("bottom", ctypes.c_long),
    ]


class MobSupportBot:
    def __init__(self):
        self.running = True
        self.enabled = False
        self.session_running = False
        self.last_attack_at = 0.0
        self.last_window_refresh = 0.0
        self.last_window_warn = 0.0
        self.last_camera_scan = 0.0
        self.next_safety_pause_at: Optional[float] = None
        self.no_target_streak = 0
        self.no_target_scan_started_at: Optional[float] = None
        self.no_target_scan_tilt_down_done = False
        self.failed_engage_attempts = 0
        self.prev_in_combat = False

        # Lock apos qualquer clique:
        # aguarda ate 4s pelo hub; se hub aparecer, espera sumir para liberar.
        self.post_click_wait_active = False
        self.post_click_wait_started_at = 0.0
        self.post_click_wait_seen_hub = False

        self.hwnd: Optional[int] = None
        self.client_rect: Optional[ClientRect] = None

        # Cores de mob
        self.samples: List[Tuple[int, int, int]] = []
        self.palette: List[Tuple[int, int, int, int, int, int]] = []
        self.current_mob_name: Optional[str] = None
        self.current_mob_conf_path: Optional[str] = None
        self.hub_green_samples: List[Tuple[int, int, int]] = []
        self.hub_red_samples: List[Tuple[int, int, int]] = []
        self.hub_green_range = HSV_MOB_GREEN_RANGE
        self.hub_red_ranges = HSV_RED_RANGES
        self.combat_green_min_pixels = DEFAULT_COMBAT_GREEN_MIN_PIXELS
        self.runtime_limit_enabled = True
        self.max_runtime_hours = DEFAULT_MAX_RUNTIME_HOURS
        self.max_runtime_seconds = int(DEFAULT_MAX_RUNTIME_HOURS * 3600.0)
        self.humanized_pauses_enabled = True
        self.safety_pause_interval_min_seconds = SAFETY_PAUSE_INTERVAL_MIN_SECONDS
        self.safety_pause_interval_max_seconds = SAFETY_PAUSE_INTERVAL_MAX_SECONDS
        self.safety_pause_duration_min_seconds = SAFETY_PAUSE_DURATION_MIN_SECONDS
        self.safety_pause_duration_max_seconds = SAFETY_PAUSE_DURATION_MAX_SECONDS
        self.session_started_at = 0.0
        self.last_auto_reload_check = 0.0
        self.mob_conf_mtime = 0.0
        self.script_conf_mtime = 0.0

        pyautogui.FAILSAFE = True
        self.sct = mss.mss()
        self.listener = None
        self.user32 = ctypes.windll.user32
        self._migrate_legacy_goblin_conf()
        self._load_script_conf()
        self._update_conf_mtimes()

    def _on_key_press(self, key):
        try:
            if key == keyboard.Key.f8:
                self.session_running = False
                print("[BOT] Sessao encerrada (F8).")
            elif key == keyboard.Key.f7:
                self.enabled = not self.enabled
                state = "RODANDO" if self.enabled else "PAUSADO"
                print(f"[BOT] Estado: {state} (F7).")
                if self.enabled:
                    if self.humanized_pauses_enabled:
                        self._schedule_next_safety_pause(time.time())
                    else:
                        self.next_safety_pause_at = None
                else:
                    self.next_safety_pause_at = None
        except Exception:
            pass

    def _schedule_next_safety_pause(self, now: float):
        delta = random.uniform(
            self.safety_pause_interval_min_seconds,
            self.safety_pause_interval_max_seconds,
        )
        self.next_safety_pause_at = now + delta

    @staticmethod
    def _safe_float(value, default: float) -> float:
        try:
            return float(value)
        except Exception:
            return float(default)

    def _set_safety_pause_interval_range(self, min_seconds: float, max_seconds: float):
        lo = max(10.0, min(float(min_seconds), float(max_seconds)))
        hi = max(lo, min(7200.0, max(float(min_seconds), float(max_seconds))))
        self.safety_pause_interval_min_seconds = lo
        self.safety_pause_interval_max_seconds = hi

    def _set_safety_pause_duration_range(self, min_seconds: float, max_seconds: float):
        lo = max(1.0, min(float(min_seconds), float(max_seconds)))
        hi = max(lo, min(3600.0, max(float(min_seconds), float(max_seconds))))
        self.safety_pause_duration_min_seconds = lo
        self.safety_pause_duration_max_seconds = hi

    @staticmethod
    def _slugify_mob_name(name: str) -> str:
        base = (name or "").strip().lower()
        out = []
        prev_dash = False
        for ch in base:
            if ch.isalnum():
                out.append(ch)
                prev_dash = False
            else:
                if not prev_dash:
                    out.append("-")
                    prev_dash = True
        slug = "".join(out).strip("-")
        return slug

    @staticmethod
    def _build_mob_conf_path(mob_name: str) -> str:
        return os.path.join(MOB_CONFIG_DIR, f"{mob_name}.conf")

    def _migrate_legacy_goblin_conf(self):
        os.makedirs(MOB_CONFIG_DIR, exist_ok=True)
        target = self._build_mob_conf_path("goblin")
        try:
            if os.path.isfile(LEGACY_GOBLIN_CONF_PATH) and not os.path.isfile(target):
                os.replace(LEGACY_GOBLIN_CONF_PATH, target)
                print("[BOT] goblin.conf migrado para config/mob/goblin.conf")
            legacy_dir = os.path.dirname(LEGACY_GOBLIN_CONF_PATH)
            legacy_root = os.path.dirname(legacy_dir)
            if os.path.isdir(legacy_dir) and not os.listdir(legacy_dir):
                os.rmdir(legacy_dir)
            if os.path.isdir(legacy_root) and not os.listdir(legacy_root):
                os.rmdir(legacy_root)
        except Exception:
            pass

    def _list_mob_configs(self) -> List[Tuple[str, str]]:
        os.makedirs(MOB_CONFIG_DIR, exist_ok=True)
        out = []
        for fn in sorted(os.listdir(MOB_CONFIG_DIR)):
            if not fn.lower().endswith(".conf"):
                continue
            name = os.path.splitext(fn)[0]
            path = os.path.join(MOB_CONFIG_DIR, fn)
            out.append((name, path))
        return out

    def _set_active_mob(self, mob_name: str, conf_path: str):
        self.current_mob_name = mob_name
        self.current_mob_conf_path = conf_path
        self._load_conf()
        self._update_conf_mtimes()

    def _start_listener(self):
        if self.listener is not None:
            return
        self.listener = keyboard.Listener(on_press=self._on_key_press)
        self.listener.start()

    def _stop_listener(self):
        if self.listener is None:
            return
        try:
            self.listener.stop()
        except Exception:
            pass
        self.listener = None

    def _list_candidate_hwnds(self):
        hwnds = []

        @ctypes.WINFUNCTYPE(ctypes.c_bool, ctypes.c_void_p, ctypes.c_void_p)
        def enum_proc(hwnd, _):
            if not self.user32.IsWindowVisible(hwnd) or self.user32.IsIconic(hwnd):
                return True
            pid = ctypes.c_ulong(0)
            self.user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
            if pid.value == 0:
                return True
            try:
                pname = psutil.Process(pid.value).name().lower()
            except Exception:
                return True
            if pname != WINDOW_PROCESS_NAME.lower():
                return True
            length = self.user32.GetWindowTextLengthW(hwnd)
            buff = ctypes.create_unicode_buffer(length + 1)
            self.user32.GetWindowTextW(hwnd, buff, length + 1)
            title = buff.value or ""
            if WINDOW_TITLE_HINT and WINDOW_TITLE_HINT.lower() not in title.lower():
                return True
            rect = RECT()
            self.user32.GetWindowRect(hwnd, ctypes.byref(rect))
            area = max(0, rect.right - rect.left) * max(0, rect.bottom - rect.top)
            if area > 0:
                hwnds.append((hwnd, area))
            return True

        self.user32.EnumWindows(enum_proc, 0)
        hwnds.sort(key=lambda x: x[1], reverse=True)
        return hwnds

    def _get_client_rect(self, hwnd: int) -> Optional[ClientRect]:
        rect = RECT()
        if not self.user32.GetClientRect(hwnd, ctypes.byref(rect)):
            return None
        width = rect.right - rect.left
        height = rect.bottom - rect.top
        if width <= 0 or height <= 0:
            return None
        pt = POINT(0, 0)
        if not self.user32.ClientToScreen(hwnd, ctypes.byref(pt)):
            return None
        return ClientRect(left=pt.x, top=pt.y, width=width, height=height)

    def _refresh_window(self):
        now = time.time()
        if now - self.last_window_refresh < WINDOW_REFRESH_SECONDS:
            return
        self.last_window_refresh = now
        candidates = self._list_candidate_hwnds()
        if not candidates:
            self.hwnd = None
            self.client_rect = None
            return
        self.hwnd = int(candidates[0][0])
        self.client_rect = self._get_client_rect(self.hwnd)

    def _region_from_rel(self, rel: Tuple[float, float, float, float]) -> Optional[Region]:
        if self.client_rect is None:
            return None
        x, y, w, h = rel
        return Region(
            left=int(self.client_rect.left + x * self.client_rect.width),
            top=int(self.client_rect.top + y * self.client_rect.height),
            width=max(1, int(w * self.client_rect.width)),
            height=max(1, int(h * self.client_rect.height)),
        )

    def _point_from_rel(self, rel: Tuple[float, float]) -> Optional[Tuple[int, int]]:
        if self.client_rect is None:
            return None
        x, y = rel
        return (
            int(self.client_rect.left + x * self.client_rect.width),
            int(self.client_rect.top + y * self.client_rect.height),
        )

    def _grab_bgr(self, region: Region) -> np.ndarray:
        img = np.array(self.sct.grab(region.monitor))
        return cv2.cvtColor(img, cv2.COLOR_BGRA2BGR)

    @staticmethod
    def _build_mask_hsv(frame_bgr: np.ndarray, ranges):
        hsv = cv2.cvtColor(frame_bgr, cv2.COLOR_BGR2HSV)
        mask = None
        for low, high in ranges:
            part = cv2.inRange(hsv, np.array(low, dtype=np.uint8), np.array(high, dtype=np.uint8))
            mask = part if mask is None else cv2.bitwise_or(mask, part)
        return mask

    def _load_conf(self):
        self.samples = []
        self.palette = []
        if not self.current_mob_conf_path or not os.path.isfile(self.current_mob_conf_path):
            return
        try:
            with open(self.current_mob_conf_path, "r", encoding="utf-8") as f:
                data = json.load(f)
            items = data.get("samples", [])
            parsed = []
            for it in items:
                if isinstance(it, (list, tuple)) and len(it) == 3:
                    h, s, v = int(it[0]), int(it[1]), int(it[2])
                    if 0 <= h <= 179 and 0 <= s <= 255 and 0 <= v <= 255:
                        parsed.append((h, s, v))
            self.samples = parsed
            self._rebuild_palette()
            print(f"[BOT] Cores carregadas: {len(self.samples)}")
        except Exception:
            print("[BOT] Falha ao ler conf do mob.")

    def _save_conf(self):
        if not self.current_mob_conf_path:
            print("[BOT] Nenhum mob carregado para salvar.")
            return
        os.makedirs(os.path.dirname(self.current_mob_conf_path), exist_ok=True)
        data = {
            "samples": [[h, s, v] for h, s, v in self.samples],
            "updated_at": datetime.now().isoformat(),
        }
        with open(self.current_mob_conf_path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=True, indent=2)
        print(f"[BOT] Conf salva em: {self.current_mob_conf_path}")

    def _reset_active_mob_conf(self):
        if not self.current_mob_conf_path:
            print("[BOT] Nenhum mob carregado para limpar.")
            return
        self.samples = []
        self.palette = []
        os.makedirs(os.path.dirname(self.current_mob_conf_path), exist_ok=True)
        data = {"samples": [], "updated_at": datetime.now().isoformat()}
        with open(self.current_mob_conf_path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=True, indent=2)
        self._update_conf_mtimes()
        print("[BOT] Arquivo do mob limpo.")

    @staticmethod
    def _safe_mtime(path: str) -> float:
        try:
            return os.path.getmtime(path)
        except Exception:
            return 0.0

    def _set_max_runtime_hours(self, hours_value: float):
        try:
            hv = float(hours_value)
        except Exception:
            hv = DEFAULT_MAX_RUNTIME_HOURS
        hv = max(0.1, min(24.0, hv))
        self.max_runtime_hours = hv
        self.max_runtime_seconds = int(hv * 3600.0)

    def _update_conf_mtimes(self):
        self.mob_conf_mtime = self._safe_mtime(self.current_mob_conf_path) if self.current_mob_conf_path else 0.0
        self.script_conf_mtime = self._safe_mtime(SCRIPT_CONF_PATH)

    def _auto_reload_configs_if_changed(self):
        now = time.time()
        if now - self.last_auto_reload_check < 1.0:
            return
        self.last_auto_reload_check = now
        gm = self._safe_mtime(self.current_mob_conf_path) if self.current_mob_conf_path else 0.0
        sm = self._safe_mtime(SCRIPT_CONF_PATH)
        if gm and gm != self.mob_conf_mtime:
            self._load_conf()
            self.mob_conf_mtime = gm
            if self.current_mob_name:
                print(f"[BOT] {self.current_mob_name}.conf recarregado automaticamente.")
        if sm and sm != self.script_conf_mtime:
            self._load_script_conf()
            self.script_conf_mtime = sm
            print("[BOT] script.conf recarregado automaticamente.")

    def _load_script_conf(self):
        if not os.path.isfile(SCRIPT_CONF_PATH):
            # Compatibilidade: le valores antigos no goblin.conf (se existirem).
            try:
                if self.current_mob_conf_path and os.path.isfile(self.current_mob_conf_path):
                    with open(self.current_mob_conf_path, "r", encoding="utf-8") as f:
                        data = json.load(f)
                    hub_g = data.get("hub_green_samples", [])
                    hub_r = data.get("hub_red_samples", [])
                    self.hub_green_samples = [
                        (int(x[0]), int(x[1]), int(x[2]))
                        for x in hub_g
                        if isinstance(x, (list, tuple)) and len(x) == 3
                    ]
                    self.hub_red_samples = [
                        (int(x[0]), int(x[1]), int(x[2]))
                        for x in hub_r
                        if isinstance(x, (list, tuple)) and len(x) == 3
                    ]
                    self._rebuild_hub_ranges()
            except Exception:
                pass
            return
        try:
            with open(SCRIPT_CONF_PATH, "r", encoding="utf-8-sig") as f:
                data = json.load(f)
            hub_g = data.get("hub_green_samples", [])
            hub_r = data.get("hub_red_samples", [])
            cmin = data.get("combat_green_min_pixels", DEFAULT_COMBAT_GREEN_MIN_PIXELS)
            runtime_enabled = data.get("runtime_limit_enabled", True)
            max_runtime_h = data.get("max_runtime_hours", DEFAULT_MAX_RUNTIME_HOURS)
            humanized_pauses = data.get("humanized_pauses_enabled", True)
            pause_interval_min = data.get(
                "safety_pause_interval_min_seconds",
                SAFETY_PAUSE_INTERVAL_MIN_SECONDS,
            )
            pause_interval_max = data.get(
                "safety_pause_interval_max_seconds",
                SAFETY_PAUSE_INTERVAL_MAX_SECONDS,
            )
            pause_duration_min = data.get(
                "safety_pause_duration_min_seconds",
                SAFETY_PAUSE_DURATION_MIN_SECONDS,
            )
            pause_duration_max = data.get(
                "safety_pause_duration_max_seconds",
                SAFETY_PAUSE_DURATION_MAX_SECONDS,
            )
            self.hub_green_samples = [
                (int(x[0]), int(x[1]), int(x[2]))
                for x in hub_g
                if isinstance(x, (list, tuple)) and len(x) == 3
            ]
            self.hub_red_samples = [
                (int(x[0]), int(x[1]), int(x[2]))
                for x in hub_r
                if isinstance(x, (list, tuple)) and len(x) == 3
            ]
            try:
                cmin_int = int(cmin)
            except Exception:
                cmin_int = DEFAULT_COMBAT_GREEN_MIN_PIXELS
            self.combat_green_min_pixels = max(20, min(5000, cmin_int))
            self.runtime_limit_enabled = bool(runtime_enabled)
            self._set_max_runtime_hours(max_runtime_h)
            self.humanized_pauses_enabled = bool(humanized_pauses)
            self._set_safety_pause_interval_range(
                self._safe_float(pause_interval_min, SAFETY_PAUSE_INTERVAL_MIN_SECONDS),
                self._safe_float(pause_interval_max, SAFETY_PAUSE_INTERVAL_MAX_SECONDS),
            )
            self._set_safety_pause_duration_range(
                self._safe_float(pause_duration_min, SAFETY_PAUSE_DURATION_MIN_SECONDS),
                self._safe_float(pause_duration_max, SAFETY_PAUSE_DURATION_MAX_SECONDS),
            )
            self._rebuild_hub_ranges()
            print(f"[BOT] Config script carregada: {SCRIPT_CONF_PATH}")
        except Exception:
            print("[BOT] Falha ao ler script.conf")

    def _save_script_conf(self):
        os.makedirs(os.path.dirname(SCRIPT_CONF_PATH), exist_ok=True)
        data = {
            "combat_green_min_pixels": self.combat_green_min_pixels,
            "runtime_limit_enabled": self.runtime_limit_enabled,
            "max_runtime_hours": self.max_runtime_hours,
            "humanized_pauses_enabled": self.humanized_pauses_enabled,
            "safety_pause_interval_min_seconds": self.safety_pause_interval_min_seconds,
            "safety_pause_interval_max_seconds": self.safety_pause_interval_max_seconds,
            "safety_pause_duration_min_seconds": self.safety_pause_duration_min_seconds,
            "safety_pause_duration_max_seconds": self.safety_pause_duration_max_seconds,
            "hub_green_samples": [[h, s, v] for h, s, v in self.hub_green_samples],
            "hub_red_samples": [[h, s, v] for h, s, v in self.hub_red_samples],
            "updated_at": datetime.now().isoformat(),
        }
        with open(SCRIPT_CONF_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=True, indent=2)
        print(f"[BOT] Config geral salva em: {SCRIPT_CONF_PATH}")

    def _capture_hsv_from_cursor(self) -> Optional[Tuple[int, int, int]]:
        if self.client_rect is None:
            return None
        cx, cy = pyautogui.position()
        if not (
            self.client_rect.left <= cx < self.client_rect.left + self.client_rect.width
            and self.client_rect.top <= cy < self.client_rect.top + self.client_rect.height
        ):
            print("[BOT] Cursor fora da janela.")
            return None
        full = self._grab_bgr(
            Region(
                self.client_rect.left,
                self.client_rect.top,
                self.client_rect.width,
                self.client_rect.height,
            )
        )
        rx = cx - self.client_rect.left
        ry = cy - self.client_rect.top
        left = max(0, rx - 2)
        right = min(full.shape[1], rx + 3)
        top = max(0, ry - 2)
        bottom = min(full.shape[0], ry + 3)
        crop = full[top:bottom, left:right]
        if crop.size == 0:
            return None
        hsv = cv2.cvtColor(crop, cv2.COLOR_BGR2HSV)
        h = int(np.mean(hsv[:, :, 0]))
        s = int(np.mean(hsv[:, :, 1]))
        v = int(np.mean(hsv[:, :, 2]))
        return (h, s, v)

    def _capture_sample_from_cursor(self):
        hsv = self._capture_hsv_from_cursor()
        if hsv is None:
            return
        h, s, v = hsv
        self.samples.append((h, s, v))
        if len(self.samples) > 40:
            self.samples = self.samples[-40:]
        self._rebuild_palette()
        print(f"[BOT] Amostra capturada HSV=({h},{s},{v}) total={len(self.samples)}")

    def _rebuild_hub_ranges(self):
        # Verde do hub
        if self.hub_green_samples:
            arr = np.array(self.hub_green_samples, dtype=np.float32)
            h = int(np.median(arr[:, 0])) % 180
            s = int(np.median(arr[:, 1]))
            v = int(np.median(arr[:, 2]))
            h_tol = int(np.clip(9 + np.std(arr[:, 0]) * 0.5, 8, 22))
            s_tol = int(np.clip(30 + np.std(arr[:, 1]) * 0.4, 25, 95))
            v_tol = int(np.clip(30 + np.std(arr[:, 2]) * 0.4, 25, 95))
            self.hub_green_range = (
                (max(0, h - h_tol), max(0, s - s_tol), max(0, v - v_tol)),
                (min(179, h + h_tol), min(255, s + s_tol), min(255, v + v_tol)),
            )
        else:
            self.hub_green_range = HSV_MOB_GREEN_RANGE

        # Vermelho do hub (pode cruzar 0/179)
        if self.hub_red_samples:
            arr = np.array(self.hub_red_samples, dtype=np.float32)
            # media circular em hue
            angles = arr[:, 0] * (2.0 * np.pi / 180.0)
            angle = np.arctan2(float(np.mean(np.sin(angles))), float(np.mean(np.cos(angles))))
            if angle < 0:
                angle += 2.0 * np.pi
            h = int(round(angle * 180.0 / (2.0 * np.pi))) % 180
            s = int(np.median(arr[:, 1]))
            v = int(np.median(arr[:, 2]))
            h_tol = int(np.clip(10 + np.std(arr[:, 0]) * 0.55, 8, 24))
            s_tol = int(np.clip(30 + np.std(arr[:, 1]) * 0.4, 25, 95))
            v_tol = int(np.clip(30 + np.std(arr[:, 2]) * 0.4, 25, 95))
            s_low, s_high = max(0, s - s_tol), min(255, s + s_tol)
            v_low, v_high = max(0, v - v_tol), min(255, v + v_tol)
            h_low, h_high = h - h_tol, h + h_tol
            if h_low < 0:
                self.hub_red_ranges = [
                    ((0, s_low, v_low), (h_high, s_high, v_high)),
                    ((180 + h_low, s_low, v_low), (179, s_high, v_high)),
                ]
            elif h_high > 179:
                self.hub_red_ranges = [
                    ((h_low, s_low, v_low), (179, s_high, v_high)),
                    ((0, s_low, v_low), (h_high - 180, s_high, v_high)),
                ]
            else:
                self.hub_red_ranges = [
                    ((h_low, s_low, v_low), (h_high, s_high, v_high))
                ]
        else:
            self.hub_red_ranges = HSV_RED_RANGES

    def _rebuild_palette(self):
        self.palette = []
        if not self.samples:
            return
        arr = np.array(self.samples, dtype=np.float32)
        k = int(np.clip(len(arr) // 6, 1, PALETTE_MAX_CLUSTERS))
        k = min(k, len(arr))
        if k <= 1:
            h = int(np.median(arr[:, 0])) % 180
            s = int(np.median(arr[:, 1]))
            v = int(np.median(arr[:, 2]))
            h_tol = COLOR_H_TOL_BASE
            s_tol = COLOR_S_TOL_BASE
            v_tol = COLOR_V_TOL_BASE
            self.palette = [(h, s, v, h_tol, s_tol, v_tol)]
            return
        criteria = (cv2.TERM_CRITERIA_EPS + cv2.TERM_CRITERIA_MAX_ITER, 25, 0.5)
        _, labels, _ = cv2.kmeans(arr, k, None, criteria, 3, cv2.KMEANS_PP_CENTERS)
        labels = labels.flatten()
        out = []
        for i in range(k):
            pts = arr[labels == i]
            if len(pts) < 8:
                continue
            h = int(np.median(pts[:, 0])) % 180
            s = int(np.median(pts[:, 1]))
            v = int(np.median(pts[:, 2]))
            h_tol = int(np.clip(COLOR_H_TOL_BASE - 2 + np.std(pts[:, 0]) * 0.5, 8, 20))
            s_tol = int(np.clip(COLOR_S_TOL_BASE - 8 + np.std(pts[:, 1]) * 0.4, 24, 80))
            v_tol = int(np.clip(COLOR_V_TOL_BASE - 8 + np.std(pts[:, 2]) * 0.4, 24, 80))
            out.append((h, s, v, h_tol, s_tol, v_tol))
        self.palette = out

    @staticmethod
    def _hsv_mask_from_center(hsv_img, h, s, v, h_tol, s_tol, v_tol):
        h_low, h_high = h - h_tol, h + h_tol
        s_low, s_high = max(0, s - s_tol), min(255, s + s_tol)
        v_low, v_high = max(0, v - v_tol), min(255, v + v_tol)
        if h_low < 0:
            m1 = cv2.inRange(hsv_img, np.array((0, s_low, v_low), dtype=np.uint8), np.array((h_high, s_high, v_high), dtype=np.uint8))
            m2 = cv2.inRange(hsv_img, np.array((180 + h_low, s_low, v_low), dtype=np.uint8), np.array((179, s_high, v_high), dtype=np.uint8))
            return cv2.bitwise_or(m1, m2)
        if h_high > 179:
            m1 = cv2.inRange(hsv_img, np.array((h_low, s_low, v_low), dtype=np.uint8), np.array((179, s_high, v_high), dtype=np.uint8))
            m2 = cv2.inRange(hsv_img, np.array((0, s_low, v_low), dtype=np.uint8), np.array((h_high - 180, s_high, v_high), dtype=np.uint8))
            return cv2.bitwise_or(m1, m2)
        return cv2.inRange(
            hsv_img,
            np.array((h_low, s_low, v_low), dtype=np.uint8),
            np.array((h_high, s_high, v_high), dtype=np.uint8),
        )

    def _find_candidates_by_color_and_motion(self, frame_bgr: np.ndarray, region: Region) -> List[Tuple[int, int, float]]:
        if not self.palette:
            return []
        hsv = cv2.cvtColor(frame_bgr, cv2.COLOR_BGR2HSV)
        masks = [self._hsv_mask_from_center(hsv, *p) for p in self.palette]
        combined = masks[0].copy()
        for m in masks[1:]:
            combined = cv2.bitwise_or(combined, m)
        kernel = np.ones((3, 3), np.uint8)
        combined = cv2.morphologyEx(combined, cv2.MORPH_OPEN, kernel, iterations=1)
        combined = cv2.morphologyEx(combined, cv2.MORPH_DILATE, kernel, iterations=1)
        contours, _ = cv2.findContours(combined, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
        if not contours:
            return []

        edge = cv2.Canny(cv2.cvtColor(frame_bgr, cv2.COLOR_BGR2GRAY), 45, 120)
        cx = region.left + region.width // 2
        cy = region.top + region.height // 2
        diag = float((region.width * region.width + region.height * region.height) ** 0.5)
        if diag < 1.0:
            diag = 1.0
        max_area = int(frame_bgr.shape[0] * frame_bgr.shape[1] * COLOR_MAX_AREA_RATIO)
        out = []

        for c in contours:
            area = cv2.contourArea(c)
            if area < COLOR_MIN_AREA or area > max_area:
                continue
            x, y, w, h = cv2.boundingRect(c)
            if w <= 0 or h <= 0:
                continue
            ar = float(w) / float(h)
            if ar < 0.22 or ar > 2.8:
                continue

            roi_e = edge[y : y + h, x : x + w]
            edge_density = float(np.count_nonzero(roi_e)) / float(roi_e.size) if roi_e.size else 0.0
            if edge_density < COLOR_EDGE_DENSITY_MIN:
                continue

            color_hits = 0
            for m in masks:
                roi = m[y : y + h, x : x + w]
                if roi.size and int(np.count_nonzero(roi)) >= PALETTE_MIN_PIXELS_PER_COLOR:
                    color_hits += 1
            if color_hits < min(PALETTE_MIN_COLORS_IN_BBOX, len(masks)):
                continue

            sx = region.left + x + w // 2
            sy = region.top + y + h // 2

            dx = abs(sx - cx)
            dy = abs(sy - cy)
            roi_combined = combined[y : y + h, x : x + w]
            color_pixels = int(np.count_nonzero(roi_combined)) if roi_combined.size else 0
            center_dist_norm = float((dx * dx + dy * dy) ** 0.5) / diag
            center_dist_norm = max(0.0, min(1.0, center_dist_norm))
            center_closeness = 1.0 - center_dist_norm
            score = (
                AREA_SCORE_WEIGHT * float(area)
                + COLOR_PIXEL_SCORE_WEIGHT * float(color_pixels)
                + EDGE_SCORE_WEIGHT * edge_density
                + COLOR_HITS_SCORE_WEIGHT * float(color_hits)
                + CENTER_CLOSENESS_BONUS * (center_closeness ** CENTER_CLOSENESS_POWER)
                - CENTER_DISTANCE_PENALTY * (center_dist_norm ** CENTER_DISTANCE_POWER)
            )
            out.append((sx, sy, score))

        out.sort(key=lambda t: t[2], reverse=True)
        return out[:CANDIDATE_TOP_K]

    def _perform_camera_scan(self, now: float):
        if now - self.last_camera_scan < CAMERA_SCAN_COOLDOWN_SECONDS:
            return
        self.last_camera_scan = now
        pyautogui.keyDown("right")
        time.sleep(CAMERA_ROTATE_RIGHT_60_SECONDS)
        pyautogui.keyUp("right")

    @staticmethod
    def _tilt_camera_up():
        pyautogui.keyDown("up")
        time.sleep(CAMERA_TILT_UP_SECONDS)
        pyautogui.keyUp("up")

    @staticmethod
    def _tilt_camera_down():
        pyautogui.keyDown("down")
        time.sleep(CAMERA_TILT_DOWN_SECONDS)
        pyautogui.keyUp("down")

    @staticmethod
    def _zoom_out_camera():
        pyautogui.scroll(CAMERA_ZOOM_OUT_SCROLL_AMOUNT)

    @staticmethod
    def _zoom_in_camera():
        pyautogui.scroll(CAMERA_ZOOM_IN_SCROLL_AMOUNT)

    def _is_in_combat(self) -> bool:
        region = self._region_from_rel(MOB_HUB_REGION_REL)
        if region is None:
            return False
        frame = self._grab_bgr(region)
        red_mask = self._build_mask_hsv(frame, self.hub_red_ranges)
        green_mask = self._build_mask_hsv(frame, [self.hub_green_range])
        red_pixels = int(np.count_nonzero(red_mask))
        green_pixels = int(np.count_nonzero(green_mask))
        # Regra solicitada:
        # - se nao existe verde no hub => fora de combate
        # - se existe verde (com ou sem vermelho) => em combate
        # O vermelho e mantido apenas para diagnostico futuro.
        _ = red_pixels
        return green_pixels >= self.combat_green_min_pixels

    @staticmethod
    def _click(x: int, y: int):
        pyautogui.moveTo(x, y, duration=0.04)
        pyautogui.click(x, y)

    def _attack_target(self, x: int, y: int) -> bool:
        if self.client_rect is None:
            return False
        self._click(x, y)
        time.sleep(CLICK_MARKER_WAIT_SECONDS)

        half = CLICK_MARKER_BOX // 2
        left = max(self.client_rect.left, x - half)
        top = max(self.client_rect.top, y - half)
        right = min(self.client_rect.left + self.client_rect.width, x + half)
        bottom = min(self.client_rect.top + self.client_rect.height, y + half)
        if right <= left or bottom <= top:
            return False
        frame = self._grab_bgr(Region(left, top, right - left, bottom - top))
        red_mask = self._build_mask_hsv(frame, HSV_RED_RANGES)
        yellow_mask = self._build_mask_hsv(frame, [HSV_YELLOW_RANGE])
        red_pixels = int(np.count_nonzero(red_mask))
        yellow_pixels = int(np.count_nonzero(yellow_mask))
        if red_pixels >= CLICK_MARKER_RED_MIN_PIXELS and red_pixels >= yellow_pixels:
            return True
        if yellow_pixels >= CLICK_MARKER_YELLOW_MIN_PIXELS:
            return False
        return False

    def _prompt_choice(self, valid_choices: List[str]) -> str:
        while True:
            value = input("> ").strip()
            if value in valid_choices:
                return value
            print("[BOT] Opcao invalida.")

    @staticmethod
    def _clear_screen():
        try:
            os.system("cls" if os.name == "nt" else "clear")
        except Exception:
            pass

    def _print_header(self, title: str):
        self._clear_screen()
        print()
        print("=" * 56)
        print(f" OSRS Mob attack :: {title}")
        print("=" * 56)

    def _menu_new_mob(self):
        self._print_header("Inserir Novo Mob")
        raw = input("Digite o nome do mob: ").strip()
        mob_name = self._slugify_mob_name(raw)
        if not mob_name:
            print("[BOT] Nome invalido.")
            return
        conf_path = self._build_mob_conf_path(mob_name)
        self._set_active_mob(mob_name, conf_path)
        if not os.path.isfile(conf_path):
            self._save_conf()
        while True:
            self._print_header(f"Configurar Mob [{mob_name}]")
            print("1 - Coletar Amostras de cores do Mob")
            print("2 - Limpar amostras")
            print("3 - Salvar configuracao")
            print("0 - Voltar")
            choice = self._prompt_choice(["1", "2", "3", "0"])
            if choice == "1":
                self.last_window_refresh = 0.0
                self._refresh_window()
                if self.client_rect is None:
                    print("[BOT] Janela do jogo nao encontrada.")
                    continue
                print("[BOT] Posicione o mouse sobre o mob e pressione ENTER.")
                input()
                self._capture_sample_from_cursor()
            elif choice == "2":
                self._reset_active_mob_conf()
            elif choice == "3":
                self._save_conf()
                print("[BOT] Configuracao salva. Retornando ao menu principal.")
                return
            elif choice == "0":
                return

    def _menu_loaded_mob(self):
        if not self.current_mob_name:
            return
        while True:
            self._print_header(f"Mob Carregado [{self.current_mob_name}]")
            print("1 - Iniciar/Pausar")
            print("2 - Excluir mob")
            print("0 - Voltar")
            choice = self._prompt_choice(["1", "2", "0"])
            if choice == "1":
                self.run_session()
                if not self.running:
                    return
            elif choice == "2":
                conf_path = self.current_mob_conf_path
                if conf_path and os.path.isfile(conf_path):
                    os.remove(conf_path)
                    print(f"[BOT] Mob excluido: {os.path.basename(conf_path)}")
                self.current_mob_name = None
                self.current_mob_conf_path = None
                self.samples = []
                self.palette = []
                self._update_conf_mtimes()
                return
            elif choice == "0":
                return

    def _menu_load_mob(self):
        mobs = self._list_mob_configs()
        self._print_header("Carregar Mob")
        if not mobs:
            print("[BOT] Nenhum mob encontrado em config/mob.")
            return
        for idx, (name, _) in enumerate(mobs, start=1):
            print(f"{idx} - {name}")
        print("0 - Voltar")
        while True:
            raw = input("Selecione um numero e ENTER: ").strip()
            if raw == "0":
                return
            try:
                sel = int(raw)
            except Exception:
                print("[BOT] Opcao invalida.")
                continue
            if 1 <= sel <= len(mobs):
                mob_name, conf_path = mobs[sel - 1]
                self._set_active_mob(mob_name, conf_path)
                print(f"[BOT] Mob carregado: {mob_name}")
                self._menu_loaded_mob()
                return
            print("[BOT] Opcao invalida.")

    @staticmethod
    def _on_off_text(flag: bool) -> str:
        return "Ativado" if flag else "Desativado"

    def _menu_tempo_programado(self):
        while True:
            self._print_header("Configuracao :: Tempo Programado")
            print(f"Status: {self._on_off_text(self.runtime_limit_enabled)}")
            print(f"Tempo atual: {self.max_runtime_hours:.2f} hora(s)")
            print("1 - Ativar/Desativar")
            print("2 - Definir Tempo de Execucao")
            print("0 - Voltar")
            choice = self._prompt_choice(["1", "2", "0"])
            if choice == "1":
                self.runtime_limit_enabled = not self.runtime_limit_enabled
                self._save_script_conf()
                print(
                    f"[BOT] Tempo Programado: {self._on_off_text(self.runtime_limit_enabled)}."
                )
                time.sleep(1.0)
            elif choice == "2":
                print("Informe o novo valor em horas (ex.: 3, 2.5).")
                raw = input("> ").strip().replace(",", ".")
                try:
                    hours = float(raw)
                except Exception:
                    print("[BOT] Valor invalido.")
                    time.sleep(1.0)
                    continue
                self._set_max_runtime_hours(hours)
                self._save_script_conf()
                print(
                    f"[BOT] Tempo maximo atualizado para {self.max_runtime_hours:.2f} hora(s)."
                )
                time.sleep(1.0)
            elif choice == "0":
                return

    def _menu_pausas_programadas(self):
        while True:
            self._print_header("Configuracao :: Pausas Programadas")
            print(f"Status: {self._on_off_text(self.humanized_pauses_enabled)}")
            print(
                f"Intervalo entre pausas: {self.safety_pause_interval_min_seconds:.0f}s a {self.safety_pause_interval_max_seconds:.0f}s"
            )
            print(
                f"Duracao da pausa: {self.safety_pause_duration_min_seconds:.0f}s a {self.safety_pause_duration_max_seconds:.0f}s"
            )
            print("1 - Ativar/Desativar")
            print("2 - Definir Intervalo entre Pausas")
            print("3 - Definir Duracao da Pausa")
            print("0 - Voltar")
            choice = self._prompt_choice(["1", "2", "3", "0"])
            if choice == "1":
                self.humanized_pauses_enabled = not self.humanized_pauses_enabled
                if not self.humanized_pauses_enabled:
                    self.next_safety_pause_at = None
                elif self.enabled:
                    self._schedule_next_safety_pause(time.time())
                self._save_script_conf()
                print(
                    f"[BOT] Pausas Programadas: {self._on_off_text(self.humanized_pauses_enabled)}."
                )
                time.sleep(1.0)
            elif choice == "2":
                print("Minimo em segundos para intervalo entre pausas (ex.: 120):")
                raw_min = input("> ").strip().replace(",", ".")
                print("Maximo em segundos para intervalo entre pausas (ex.: 600):")
                raw_max = input("> ").strip().replace(",", ".")
                try:
                    vmin = float(raw_min)
                    vmax = float(raw_max)
                except Exception:
                    print("[BOT] Valor invalido.")
                    time.sleep(1.0)
                    continue
                self._set_safety_pause_interval_range(vmin, vmax)
                if self.humanized_pauses_enabled and self.enabled:
                    self._schedule_next_safety_pause(time.time())
                self._save_script_conf()
                print(
                    f"[BOT] Intervalo atualizado para {self.safety_pause_interval_min_seconds:.0f}s a {self.safety_pause_interval_max_seconds:.0f}s."
                )
                time.sleep(1.0)
            elif choice == "3":
                print("Minimo em segundos para duracao da pausa (ex.: 30):")
                raw_min = input("> ").strip().replace(",", ".")
                print("Maximo em segundos para duracao da pausa (ex.: 180):")
                raw_max = input("> ").strip().replace(",", ".")
                try:
                    vmin = float(raw_min)
                    vmax = float(raw_max)
                except Exception:
                    print("[BOT] Valor invalido.")
                    time.sleep(1.0)
                    continue
                self._set_safety_pause_duration_range(vmin, vmax)
                self._save_script_conf()
                print(
                    f"[BOT] Duracao atualizada para {self.safety_pause_duration_min_seconds:.0f}s a {self.safety_pause_duration_max_seconds:.0f}s."
                )
                time.sleep(1.0)
            elif choice == "0":
                return

    def _menu_configuracao(self):
        while True:
            self._print_header("Configuracao")
            print(
                f"1 - Tempo Programado de Execucao [{self._on_off_text(self.runtime_limit_enabled)}]"
            )
            print(
                f"2 - Pausas Programadas (Humanizacao) [{self._on_off_text(self.humanized_pauses_enabled)}]"
            )
            print("0 - Voltar")
            choice = self._prompt_choice(["1", "2", "0"])
            if choice == "1":
                self._menu_tempo_programado()
            elif choice == "2":
                self._menu_pausas_programadas()
            elif choice == "0":
                return

    def run_session(self):
        if not self.current_mob_conf_path:
            print("[BOT] Nenhum mob carregado.")
            return
        self.post_click_wait_active = False
        self.post_click_wait_seen_hub = False
        self.post_click_wait_started_at = 0.0
        self.no_target_streak = 0
        self.no_target_scan_started_at = None
        self.no_target_scan_tilt_down_done = False
        self.failed_engage_attempts = 0
        self.enabled = True
        self.session_running = True
        self.session_started_at = time.time()
        if self.humanized_pauses_enabled:
            self._schedule_next_safety_pause(time.time())
        else:
            self.next_safety_pause_at = None
        print("[BOT] Sessao iniciada.")
        print("[BOT] F7 = iniciar/pausar | F8 = sair da sessao")
        self._start_listener()
        while self.running and self.session_running:
            just_left_combat = False
            self._refresh_window()
            if self.client_rect is None:
                now = time.time()
                if now - self.last_window_warn > 3:
                    self.last_window_warn = now
                    print("[BOT] Janela do jogo nao encontrada.")
                time.sleep(MAIN_LOOP_SLEEP)
                continue

            self._auto_reload_configs_if_changed()

            if not self.enabled:
                time.sleep(MAIN_LOOP_SLEEP)
                continue

            if not self.palette:
                print("[BOT] Sem cores no mob carregado.")
                self.enabled = False
                time.sleep(MAIN_LOOP_SLEEP)
                continue

            now = time.time()
            if (
                self.runtime_limit_enabled
                and self.session_started_at > 0
                and (now - self.session_started_at) >= self.max_runtime_seconds
            ):
                self.enabled = False
                self.session_running = False
                self.running = False
                hhmmss = datetime.now().strftime("%H:%M:%S")
                print(
                    f"[BOT] [{hhmmss}] Tempo programado atingido ({self.max_runtime_hours:.2f}h). Bot pausado e encerrado."
                )
                break

            in_combat = self._is_in_combat()
            self.prev_in_combat = in_combat

            if self.post_click_wait_active:
                if in_combat:
                    if not self.post_click_wait_seen_hub:
                        self.post_click_wait_seen_hub = True
                        self._tilt_camera_up()
                        self._zoom_in_camera()
                    self.failed_engage_attempts = 0
                    time.sleep(MAIN_LOOP_SLEEP)
                    continue
                if not self.post_click_wait_seen_hub:
                    if now - self.post_click_wait_started_at < POST_CLICK_WAIT_HUB_SECONDS:
                        time.sleep(MAIN_LOOP_SLEEP)
                        continue
                    self.post_click_wait_active = False
                    self.post_click_wait_seen_hub = False
                    self.failed_engage_attempts += 1
                    if self.failed_engage_attempts >= 1:
                        # Inicia busca sem alvo com camera alta (zoom out + giro).
                        # A descida total da camera ocorre apenas no fluxo de busca
                        # apos NO_TARGET_SPIN_BEFORE_TILT_DOWN_SECONDS.
                        self._zoom_out_camera()
                        self._perform_camera_scan(time.time())
                        self.failed_engage_attempts = 0
                else:
                    self.post_click_wait_active = False
                    self.post_click_wait_seen_hub = False
                    self.no_target_streak = 0
                    self.failed_engage_attempts = 0
                    time.sleep(POST_COMBAT_NEXT_TARGET_DELAY_SECONDS)
                    self.last_attack_at = 0.0
                    just_left_combat = True
                if now - self.post_click_wait_started_at > POST_CLICK_MAX_LOCK_SECONDS:
                    self.post_click_wait_active = False
                    self.post_click_wait_seen_hub = False

            if in_combat:
                self.no_target_scan_started_at = None
                self.no_target_scan_tilt_down_done = False
                time.sleep(MAIN_LOOP_SLEEP)
                continue

            if (
                self.humanized_pauses_enabled
                and self.next_safety_pause_at is not None
                and now >= self.next_safety_pause_at
                and not self.post_click_wait_active
                and not just_left_combat
            ):
                pause_seconds = random.uniform(
                    self.safety_pause_duration_min_seconds,
                    self.safety_pause_duration_max_seconds,
                )
                hhmmss = datetime.now().strftime("%H:%M:%S")
                print(
                    f"[BOT] [{hhmmss}] Pausa de seguranca: {pause_seconds:.1f}s (random)."
                )
                time.sleep(pause_seconds)
                self._schedule_next_safety_pause(time.time())
                continue

            if just_left_combat or (now - self.last_attack_at >= MIN_SECONDS_BETWEEN_ATTACKS):
                game_region = self._region_from_rel(GAME_VIEW_REL)
                if game_region is not None:
                    frame = self._grab_bgr(game_region)
                    if float(np.mean(frame)) < 8.0:
                        time.sleep(MAIN_LOOP_SLEEP)
                        continue
                    candidates = self._find_candidates_by_color_and_motion(frame, game_region) or []
                    attacked = False
                    for sx, sy, _ in candidates[:SEARCH_SCAN_LIMIT]:
                        tx = sx + np.random.randint(-6, 7)
                        ty = sy + np.random.randint(-6, 7)
                        red_ok = self._attack_target(tx, ty)
                        self.last_attack_at = now
                        self.post_click_wait_active = True
                        self.post_click_wait_started_at = now
                        self.post_click_wait_seen_hub = False
                        self.no_target_streak = 0
                        self.no_target_scan_started_at = None
                        self.no_target_scan_tilt_down_done = False
                        attacked = True
                        if LOG_VERBOSE and red_ok:
                            print("[BOT] Marcador vermelho detectado.")
                        time.sleep(AFTER_ATTACK_SLEEP)
                        break
                    if not attacked:
                        self.no_target_streak += 1
                        if self.no_target_streak >= NO_TARGET_STREAK_FOR_SCAN:
                            if self.no_target_scan_started_at is None:
                                self.no_target_scan_started_at = now
                            if now - self.last_camera_scan >= CAMERA_SCAN_COOLDOWN_SECONDS:
                                self._zoom_out_camera()
                                self._perform_camera_scan(now)
                            if (
                                not self.no_target_scan_tilt_down_done
                                and (now - self.no_target_scan_started_at) >= NO_TARGET_SPIN_BEFORE_TILT_DOWN_SECONDS
                            ):
                                self._tilt_camera_down()
                                self.no_target_scan_tilt_down_done = True

            time.sleep(MAIN_LOOP_SLEEP)
        self._stop_listener()
        self.enabled = False
        self.session_running = False
        if self.running:
            print("[BOT] Retornando ao menu principal.")

    def run(self):
        while self.running:
            self._print_header("Menu Principal")
            print("1 - Carregar Mob")
            print("2 - Inserir novo Mob")
            print("3 - Configuracao")
            print("0 - Sair")
            choice = self._prompt_choice(["1", "2", "3", "0"])
            if choice == "1":
                self._menu_load_mob()
            elif choice == "2":
                self._menu_new_mob()
            elif choice == "3":
                self._menu_configuracao()
            elif choice == "0":
                self.running = False
        self._stop_listener()
        print("[BOT] Encerrado.")


if __name__ == "__main__":
    bot = MobSupportBot()
    bot.run()

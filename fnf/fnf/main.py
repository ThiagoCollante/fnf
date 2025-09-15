import pygame
import math
import os
import json
import shutil
import tkinter as tk
from tkinter import filedialog
import pydub

try:
    from pydub import AudioSegment
    PYDUB_AVAILABLE = True
except ImportError:
    PYDUB_AVAILABLE = False

# --- Constants ---
SCREEN_WIDTH = 1200
SCREEN_HEIGHT = 600
FPS = 60

# --- MODIFIED: Font settings ---
# Place your desired .otf or .ttf font in an 'assets/fonts/' directory
# If the font is not found, a default font will be used.
FONT_FILENAME = "custom_font.ttf"
# --- END MODIFICATION ---

# Colors
BLACK = (0, 0, 0); WHITE = (255, 255, 255); GRAY = (150, 150, 150); RED = (200, 0, 0)
DARK_GRAY = (30, 30, 30)
CHECKER_COLOR_A = (40, 40, 40); CHECKER_COLOR_B = (55, 55, 55)
LANE_COLORS = [(0, 255, 255), (255, 0, 255), (255, 255, 0), (0, 255, 0)]

# Game settings
INITIAL_NOTE_SPEED = 7
LANE_COUNT = 4; LANE_WIDTH = 120; NOTE_WIDTH = 120
SPRITE_SIZES = {'normal': (NOTE_WIDTH, 30), 'hold_start': (NOTE_WIDTH, 20), 'hold_middle': (NOTE_WIDTH, 20), 'hold_end': (NOTE_WIDTH, 20)}
KEY_MAP = { pygame.K_s: 0, pygame.K_d: 1, pygame.K_j: 2, pygame.K_k: 3 }; KEY_LABELS = ['S', 'D', 'J', 'K']
PLAYHEAD_Y = SCREEN_HEIGHT - 100

# --- Helper Functions ---

def load_font(font_name, size):
    script_dir = os.path.dirname(__file__)
    fonts_path = os.path.join(script_dir, "assets", "fonts")
    font_path = os.path.join(fonts_path, font_name)
    if not os.path.isdir(fonts_path):
        os.makedirs(fonts_path)
    if os.path.exists(font_path):
        try:
            return pygame.font.Font(font_path, size)
        except pygame.error as e:
            print(f"Error loading font '{font_name}': {e}. Falling back to default.")
    return pygame.font.Font(None, size)

def create_placeholder_sprites():
    sprites = {}
    for name, size in SPRITE_SIZES.items():
        sprites[name] = pygame.Surface(size, pygame.SRCALPHA)
        if name in ['normal', 'hold_start', 'hold_end']: pygame.draw.rect(sprites[name], WHITE, sprites[name].get_rect(), border_radius=8)
        else: sprites[name].fill(WHITE)
    return sprites

def colorize_sprite(sprite, color):
    image = sprite.copy(); image.fill(color, special_flags=pygame.BLEND_RGBA_MULT); return image

# --- Note Class ---
class Note:
    def __init__(self, lane, speed, lane_geo, game_sprites, duration=None):
        self.lane, self.speed, self.y, self.is_active = lane, speed, 0.0, True; lane_sprites = game_sprites[self.lane]; self.is_hold = duration is not None
        if self.is_hold: self.start_img, self.middle_img, self.end_img, self.held_img = lane_sprites['hold_start'], lane_sprites['hold_middle'], lane_sprites['hold_end'], lane_sprites['hold_start_held']; self.image = self.start_img
        else: self.image = lane_sprites['normal']
        self.rect = self.image.get_rect(centerx=lane_geo[self.lane]['center_x'], centery=int(self.y)); self.duration = duration
        self.full_tail_length = (self.duration / (1000.0 / FPS)) * self.speed if self.is_hold else 0; self.is_hit = self.is_holding = False; self.hold_start_time = self.hold_end_time = None

    def update(self):
        if not (self.is_hold and self.is_holding): self.y += self.speed; self.rect.centery = int(self.y)

    def draw(self, screen, current_game_time):
        if not self.is_hold: screen.blit(self.image, self.rect); return
        current_tail_length = self.full_tail_length
        if self.is_holding and self.hold_start_time is not None: elapsed = current_game_time - self.hold_start_time; remaining = max(0, self.duration - elapsed); current_tail_length = max(0, (remaining / (1000.0 / FPS)) * self.speed)
        if current_tail_length > 0:
            scaled_middle = pygame.transform.scale(self.middle_img, (self.rect.width, int(current_tail_length))); middle_rect = scaled_middle.get_rect(midbottom=self.rect.midtop); screen.blit(scaled_middle, middle_rect)
            end_rect = self.end_img.get_rect(midbottom=middle_rect.midtop); screen.blit(self.end_img, end_rect)
        head_image = self.held_img if self.is_holding else self.start_img; screen.blit(head_image, self.rect)

# --- GameSession Class ---
class GameSession:
    JUDGEMENT_WINDOWS = {'perfect': 22, 'great': 45, 'good': 90}
    ACCURACY_VALUES = {'perfect': 1.0, 'great': 0.7, 'good': 0.4, 'miss': 0.0}
    SCORE_VALUES = {'perfect': 100, 'great': 70, 'good': 40, 'miss': 0}
    RANK_THRESHOLDS = {'S': 95.0, 'A': 90.0, 'B': 85.0, 'C': 75.0, 'D': 50.0, 'F': 0.0}

    def __init__(self, screen, clock, song_data, sprites):
        self.screen, self.clock, self.song_data, self.note_sprites = screen, clock, song_data, sprites
        self.font = load_font(FONT_FILENAME, 40)
        self.key_label_font = load_font(FONT_FILENAME, 46)
        self.countdown_font = load_font(FONT_FILENAME, 120)
        self.judgement_font = load_font(FONT_FILENAME, 54)
        self.rank_font = load_font(FONT_FILENAME, 160)
        self.stats_font = load_font(FONT_FILENAME, 34)

        self.lane_geometry = self._calculate_lane_geometry()
        self.key_press_feedback = {i: 0 for i in range(LANE_COUNT)}
        self.is_running = True

        self.reset_stats()

        self.countdown_duration = 3000
        self.session_init_time = 0
        self.song_start_time = 0
        self.music_started = False
        self.music_loaded = False
        self.chart_start_offset = 0
        self.scroll_time_ms = 0
        
        self.fade_in_duration = 0
        self.fade_start_time = 0

    def reset_stats(self):
        self.score = 0
        self.combo = 0
        self.max_combo = 0
        self.judgements = {'perfect': 0, 'great': 0, 'good': 0, 'miss': 0}
        self.total_notes = len(self.song_data.get('chart', []))
        self.notes = []
        self.next_note_index = 0
        self.current_game_time = 0
        self.judgement_timer = 0
        self.active_judgement_text = ""

    def _calculate_lane_geometry(self):
        geo = {}
        total_lanes_width = LANE_COUNT * LANE_WIDTH
        left_half_width = SCREEN_WIDTH / 2

        start_x = (left_half_width - total_lanes_width) / 2

        for i in range(LANE_COUNT):
            center_x = start_x + (i * LANE_WIDTH) + LANE_WIDTH / 2
            keypad_rect = self.note_sprites[i]['normal'].get_rect(center=(center_x, PLAYHEAD_Y))
            geo[i] = {'keypad_rect': keypad_rect, 'center_x': center_x}
        return geo

    def run(self, fade_in_duration=0):
        if fade_in_duration > 0:
            self.fade_in_duration = fade_in_duration
            self.fade_start_time = pygame.time.get_ticks()
            
        note_speed = self.song_data.get('speed', INITIAL_NOTE_SPEED)

        scroll_distance_pixels = PLAYHEAD_Y
        scroll_time_frames = scroll_distance_pixels / note_speed
        self.scroll_time_ms = scroll_time_frames * (1000.0 / FPS)

        use_custom_start = self.song_data.get('use_custom_start', False)
        if use_custom_start:
            self.chart_start_offset = self.song_data.get('start_offset_ms', 0)
        else:
            first_note_time = 0
            if self.song_data['chart']:
                self.song_data['chart'].sort(key=lambda x: x['time'])
                first_note_time = self.song_data['chart'][0]['time']
            self.chart_start_offset = max(0, first_note_time - self.scroll_time_ms)

        self.session_init_time = pygame.time.get_ticks()
        self.song_start_time = self.session_init_time + self.countdown_duration

        try:
            if self.song_data['audio_path'] and os.path.exists(self.song_data['audio_path']):
                pygame.mixer.music.load(self.song_data['audio_path'])
                pygame.mixer.music.set_volume(0.7)
                self.music_loaded = True
        except pygame.error as e:
            print(f"Could not load music: {e}")
            self.music_loaded = False

        while self.is_running:
            self.clock.tick(FPS)
            current_ticks = pygame.time.get_ticks()
            self.current_game_time = (current_ticks - self.song_start_time) + self.chart_start_offset
            self.handle_events()
            self.update()
            self.draw()

            if self.music_loaded:
                if self.music_started and not pygame.mixer.music.get_busy():
                    self.is_running = False
            else:
                all_notes_spawned = self.next_note_index >= len(self.song_data['chart'])
                if all_notes_spawned and not self.notes:
                    self.is_running = False

        pygame.mixer.music.stop()
        self.run_end_screen()

    def handle_events(self):
        for event in pygame.event.get():
            if event.type == pygame.QUIT: self.is_running = False
            if event.type == pygame.KEYDOWN:
                if event.key == pygame.K_ESCAPE: self.is_running = False
                if event.key in KEY_MAP:
                    lane = KEY_MAP[event.key]; self.key_press_feedback[lane] = 10; self.check_hit(lane)
            if event.type == pygame.KEYUP and event.key in KEY_MAP:
                self.check_release(KEY_MAP[event.key])

    def check_hit(self, lane):
        for note in self.notes:
            if note.is_active and not note.is_hit and note.lane == lane:
                delta = abs(note.rect.centery - PLAYHEAD_Y)
                if delta < self.JUDGEMENT_WINDOWS['good']:
                    judgement = 'good'
                    if delta < self.JUDGEMENT_WINDOWS['great']: judgement = 'great'
                    if delta < self.JUDGEMENT_WINDOWS['perfect']: judgement = 'perfect'

                    self.judgements[judgement] += 1
                    self.score += self.SCORE_VALUES[judgement]
                    self.combo += 1
                    self.show_judgement(judgement)

                    note.is_hit = True
                    if note.is_hold:
                        note.is_holding = True
                        note.hold_start_time = self.current_game_time
                        note.hold_end_time = self.current_game_time + note.duration
                    else:
                        note.is_active = False
                    return

    def check_release(self, lane):
        for note in self.notes:
            if note.lane == lane and note.is_hold and note.is_holding:
                note.is_holding = False; note.is_active = False
                if self.current_game_time >= note.hold_end_time:
                    self.combo += 1
                    self.score += self.SCORE_VALUES['perfect']
                return

    def update(self):
        if self.current_game_time >= self.chart_start_offset:
            if not self.music_started and self.music_loaded:
                pygame.mixer.music.play(start=self.chart_start_offset / 1000.0)
                self.music_started = True

        chart = self.song_data['chart']; note_speed = self.song_data.get('speed', INITIAL_NOTE_SPEED)
        while self.next_note_index < len(chart) and \
              self.current_game_time >= (chart[self.next_note_index]['time'] - self.scroll_time_ms):
            note_data = chart[self.next_note_index]
            self.notes.append(Note(note_data['lane'], note_speed, self.lane_geometry, self.note_sprites, note_data.get('duration')))
            self.next_note_index += 1

        for note in self.notes:
            note.update()
            if note.is_active and not note.is_hit and note.rect.top > PLAYHEAD_Y + self.JUDGEMENT_WINDOWS['good']:
                note.is_active = False
                self.combo = 0
                self.judgements['miss'] += 1
                self.show_judgement('miss')
            if note.is_holding and self.current_game_time >= note.hold_end_time:
                note.is_holding = False; note.is_active = False
                self.combo += 1
                self.score += self.SCORE_VALUES['perfect']

        if self.combo > self.max_combo:
            self.max_combo = self.combo

        self.notes = [n for n in self.notes if n.is_active]
        for i in range(LANE_COUNT):
            if self.key_press_feedback[i] > 0: self.key_press_feedback[i] -= 1

        if self.judgement_timer > 0:
            self.judgement_timer -= 1
        else:
            self.active_judgement_text = ""

    def draw(self):
        self.screen.fill(BLACK)

        total_lanes_width = LANE_COUNT * LANE_WIDTH
        left_half_width = SCREEN_WIDTH / 2
        start_x = (left_half_width - total_lanes_width) / 2

        track_rect = pygame.Rect(start_x, 0, total_lanes_width, SCREEN_HEIGHT)
        pygame.draw.rect(self.screen, DARK_GRAY, track_rect)
        for i in range(LANE_COUNT + 1):
            line_x = start_x + i * LANE_WIDTH
            pygame.draw.line(self.screen, BLACK, (line_x, 0), (line_x, SCREEN_HEIGHT), 2)

        for note in sorted(self.notes, key=lambda n: not n.is_hold):
            note.draw(self.screen, self.current_game_time)

        judgement_rect = None
        track_center_x = start_x + total_lanes_width / 2

        if self.judgement_timer > 0 and self.active_judgement_text:
            judgement_colors = {'PERFECT': (255, 215, 0), 'GREAT': (0, 255, 0), 'GOOD': (0, 191, 255), 'MISS': (255, 0, 0)}
            color = judgement_colors.get(self.active_judgement_text, WHITE)
            judgement_surf = self.judgement_font.render(self.active_judgement_text, True, color)
            alpha = max(0, 255 * (self.judgement_timer / 30.0))
            judgement_surf.set_alpha(alpha)
            judgement_rect = judgement_surf.get_rect(center=(track_center_x, SCREEN_HEIGHT / 2 - 80))
            self.screen.blit(judgement_surf, judgement_rect)

        if self.combo > 2:
            combo_surf = self.judgement_font.render(str(self.combo), True, WHITE)
            y_pos = (judgement_rect.bottom + 40) if judgement_rect else (SCREEN_HEIGHT / 2)
            combo_rect = combo_surf.get_rect(center=(track_center_x, y_pos))
            self.screen.blit(combo_surf, combo_rect)

        for i in range(LANE_COUNT):
            pad_rect = self.lane_geometry[i]['keypad_rect']
            sprite = self.note_sprites[0]['normal'] if self.key_press_feedback[i] > 0 else self.note_sprites[i]['normal']
            self.screen.blit(sprite, pad_rect)
            text_surface = self.key_label_font.render(KEY_LABELS[i], True, WHITE)
            text_rect = text_surface.get_rect(centerx=pad_rect.centerx, top=pad_rect.bottom + 10)
            self.screen.blit(text_surface, text_rect)

        stats_x = SCREEN_WIDTH / 2 + 50
        y_offset = 50

        notes_judged = sum(self.judgements.values())
        live_accuracy = ((sum(self.judgements[j] * self.ACCURACY_VALUES[j] for j in self.judgements) / notes_judged) * 100.0) if notes_judged > 0 else 100.0

        stats_to_draw = [
            f"Score: {self.score}",
            f"Accuracy: {live_accuracy:.2f}%",
            f"Max Combo: {self.max_combo}",
        ]
        for text in stats_to_draw:
            stat_surf = self.font.render(text, True, WHITE)
            self.screen.blit(stat_surf, (stats_x, y_offset))
            y_offset += 35

        y_offset += 20

        for j, count in self.judgements.items():
            color = {'perfect': (255, 215, 0), 'great': (0, 255, 0), 'good': (0, 191, 255), 'miss': (255, 0, 0)}[j]
            j_text = self.stats_font.render(f"{j.upper()}: {count}", True, color)
            self.screen.blit(j_text, (stats_x, y_offset))
            y_offset += 30

        time_until_real_start = self.song_start_time - pygame.time.get_ticks()
        if time_until_real_start > 0:
            countdown_val = math.ceil(time_until_real_start / 1000)
            countdown_text = self.countdown_font.render(str(countdown_val), True, WHITE)
            text_rect = countdown_text.get_rect(center=(SCREEN_WIDTH / 4, SCREEN_HEIGHT / 2))
            self.screen.blit(countdown_text, text_rect)
            
        if self.fade_in_duration > 0:
            elapsed = pygame.time.get_ticks() - self.fade_start_time
            if elapsed < self.fade_in_duration:
                progress = elapsed / self.fade_in_duration
                alpha = max(0, 255 * (1 - progress))
                fade_surface = pygame.Surface(self.screen.get_size())
                fade_surface.fill(BLACK)
                fade_surface.set_alpha(alpha)
                self.screen.blit(fade_surface, (0, 0))
            else:
                self.fade_in_duration = 0

        pygame.display.flip()

    def show_judgement(self, judgement):
        self.active_judgement_text = judgement.upper()
        self.judgement_timer = 30
        
    def _create_vinyl_overlay(self, diameter):
        overlay = pygame.Surface((diameter, diameter), pygame.SRCALPHA)
        center_pos = (diameter // 2, diameter // 2)
        for r in range(diameter // 2, int(diameter * 0.2), -3): pygame.draw.circle(overlay, (0, 0, 0, 50), center_pos, r, 1)
        pygame.draw.circle(overlay, (25, 25, 25), center_pos, int(diameter * 0.2))
        pygame.draw.circle(overlay, (15, 15, 15), center_pos, int(diameter * 0.18), 5)
        pygame.draw.circle(overlay, (0, 0, 0, 128), center_pos, int(diameter * 0.02))
        return overlay

    def run_end_screen(self):
        final_accuracy = ((sum(self.judgements[j] * self.ACCURACY_VALUES[j] for j in self.judgements) / self.total_notes) * 100) if self.total_notes > 0 else 100.0

        rank = 'F'
        for r, threshold in sorted(self.RANK_THRESHOLDS.items(), key=lambda item: item[1], reverse=True):
            if final_accuracy >= threshold:
                rank = r
                break

        vinyl_surface = None
        END_SCREEN_VINYL_DIAMETER = 1200 # Made vinyl bigger
        icon_path = os.path.join(self.song_data['folder_path'], "icon.png")
        if os.path.exists(icon_path):
            try:
                vinyl_overlay = self._create_vinyl_overlay(END_SCREEN_VINYL_DIAMETER)
                loaded_icon = pygame.image.load(icon_path).convert_alpha()
                scaled_icon = pygame.transform.smoothscale(loaded_icon, (END_SCREEN_VINYL_DIAMETER, END_SCREEN_VINYL_DIAMETER))
                
                vinyl_surface = pygame.Surface((END_SCREEN_VINYL_DIAMETER, END_SCREEN_VINYL_DIAMETER), pygame.SRCALPHA)
                pygame.draw.circle(vinyl_surface, (255, 255, 255), vinyl_surface.get_rect().center, END_SCREEN_VINYL_DIAMETER // 2)
                vinyl_surface.blit(scaled_icon, (0, 0), special_flags=pygame.BLEND_RGBA_MIN)
                vinyl_surface.blit(vinyl_overlay, (0, 0))
            except pygame.error as e:
                print(f"Error loading icon for end screen vinyl: {e}")

        rank_image = None
        script_dir = os.path.dirname(__file__)
        rank_image_path = os.path.join(script_dir, "assets", "ranks", f"rank_{rank}.png")
        if os.path.exists(rank_image_path):
            try:
                rank_image = pygame.image.load(rank_image_path).convert_alpha()
                rank_image = pygame.transform.scale(rank_image, (150, 150))
            except pygame.error as e:
                print(f"Error loading rank image {rank_image_path}: {e}")

        pulse_amplitude, pulse_speed, vinyl_rotation_angle = 10, 0.8, 0.0

        waiting = True
        while waiting:
            for event in pygame.event.get():
                if event.type == pygame.QUIT or (event.type == pygame.KEYDOWN and event.key in [pygame.K_RETURN, pygame.K_ESCAPE]):
                    waiting = False

            self.screen.fill(BLACK)
            overlay = pygame.Surface((SCREEN_WIDTH, SCREEN_HEIGHT), pygame.SRCALPHA); overlay.fill((0, 0, 0, 180)); self.screen.blit(overlay, (0, 0))

            # --- MODIFIED: "Results" title positioning ---
            title_text = self.font.render("Results", True, WHITE)
            title_rect = title_text.get_rect(centerx=(SCREEN_WIDTH * 0.75), top=40)
            self.screen.blit(title_text, title_rect)

            if vinyl_surface:
                vinyl_rotation_angle = (vinyl_rotation_angle + 0.25) % 360
                
                current_pulse_offset = pulse_amplitude * math.sin(pygame.time.get_ticks() * pulse_speed / 100)
                size_val = int(END_SCREEN_VINYL_DIAMETER + current_pulse_offset)
                size = (size_val, size_val)

                pulsed_vinyl = pygame.transform.smoothscale(vinyl_surface, size)
                rotated_pulsed_vinyl = pygame.transform.rotate(pulsed_vinyl, vinyl_rotation_angle)
                
                # --- MODIFIED: Vinyl positioning ---
                icon_rect = rotated_pulsed_vinyl.get_rect(center=(0, SCREEN_HEIGHT / 2))
                self.screen.blit(rotated_pulsed_vinyl, icon_rect)

            block_start_x, y_offset = SCREEN_WIDTH / 2 + 40, 120

            if rank_image:
                rank_rect = rank_image.get_rect(left=block_start_x, top=y_offset)
                self.screen.blit(rank_image, rank_rect)
            else:
                rank_text = self.rank_font.render(rank, True, LANE_COLORS[0])
                rank_rect = rank_text.get_rect(left=block_start_x, top=y_offset)
                self.screen.blit(rank_text, rank_rect)

            stats_x, stats_y_start = rank_rect.right + 20, rank_rect.top + 20
            self.screen.blit(self.stats_font.render(f"Accuracy: {final_accuracy:.2f}%", True, WHITE), (stats_x, stats_y_start))
            self.screen.blit(self.stats_font.render(f"Score: {self.score}", True, WHITE), (stats_x, stats_y_start + 30))
            self.screen.blit(self.stats_font.render(f"Max Combo: {self.max_combo}", True, WHITE), (stats_x, stats_y_start + 60))

            y_offset = rank_rect.bottom + 30
            for i, (j, count) in enumerate(self.judgements.items()):
                color = {'perfect': (255, 215, 0), 'great': (0, 255, 0), 'good': (0, 191, 255), 'miss': (255, 0, 0)}[j]
                j_text = self.stats_font.render(f"{j.upper()}: {count}", True, color)
                self.screen.blit(j_text, (block_start_x, y_offset + i * 30))

            # --- MODIFIED: "Continue" prompt positioning ---
            prompt_text = self.font.render("Press Enter to Continue", True, WHITE)
            prompt_rect = prompt_text.get_rect(centerx=(SCREEN_WIDTH * 0.75), bottom=SCREEN_HEIGHT - 40)
            self.screen.blit(prompt_text, prompt_rect)

            pygame.display.flip()
            self.clock.tick(FPS)

    def _round_corners(self, surface, radius):
        mask = pygame.Surface(surface.get_size(), pygame.SRCALPHA)
        pygame.draw.rect(mask, (255, 255, 255, 255), mask.get_rect(), border_radius=radius)
        rounded_surface = surface.copy()
        rounded_surface.blit(mask, (0,0), special_flags=pygame.BLEND_RGBA_MIN)
        return rounded_surface

# --- ChartEditor Class ---
class ChartEditor:
    def __init__(self, screen, clock, song_info, sprites):
        self.screen, self.clock, self.song_info, self.note_sprites = screen, clock, song_info, sprites
        self.font_small = load_font(FONT_FILENAME, 26)
        self.font_menu = load_font(FONT_FILENAME, 30)
        self.new_chart = self.song_info.get('chart', [])
        self.is_running, self.music_playing = True, False
        self.start_x = (SCREEN_WIDTH - (LANE_COUNT * LANE_WIDTH)) / 2
        self.bpm = float(self.song_info.get('bpm', 120.0))
        self.note_speed = float(self.song_info.get('speed', INITIAL_NOTE_SPEED))
        self.scroll_ms, self.snap = 0.0, 4
        self.use_custom_start = self.song_info.get('use_custom_start', False)
        self.custom_start_ms = self.song_info.get('start_offset_ms', 0)
        self.playback_start_tick, self.playback_start_scroll_ms = 0, 0.0
        self.hold_note_starts = {}
        self.highlight_sprites = self._create_highlight_sprites(sprites)
        self.selection_box, self.selection_start_pos = None, None
        self.selected_notes, self.note_clipboard = set(), []
        self.track_surface = self.create_checkered_surface()
        self.save_button_rect = pygame.Rect(10, SCREEN_HEIGHT - 60, 150, 50)
        self.debug_menu_visible, self.selected_menu_index = False, 0
        self.debug_menu_items = self.build_menu_items()
        self.music_loaded = False
        
        self.fade_in_duration = 0
        self.fade_start_time = 0
        
        try:
            if self.song_info.get('audio_path') and os.path.exists(self.song_info['audio_path']):
                pygame.mixer.music.load(self.song_info['audio_path']); pygame.mixer.music.set_volume(0.7); self.music_loaded = True
        except pygame.error as e: print(f"Could not load music for chart editor: {e}")
        self.recalculate_timing()

    def _create_highlight_sprites(self, base_sprites):
        highlight_cache = {lane_idx: {name: (sprite if name == 'hold_start_held' else self._apply_overlay(sprite)) for name, sprite in lane_sprites.items()} for lane_idx, lane_sprites in enumerate(base_sprites)}
        return highlight_cache

    def _apply_overlay(self, sprite):
        highlight = sprite.copy()
        overlay = pygame.Surface(sprite.get_size(), pygame.SRCALPHA)
        overlay.fill((255, 255, 255, 120))
        highlight.blit(overlay, (0, 0))
        return highlight

    def build_menu_items(self):
        return [
            {'label': 'BPM', 'type': 'float', 'obj': self, 'attr': 'bpm', 'step': 0.5, 'big_step': 5.0},
            {'label': 'Note Speed', 'type': 'float', 'obj': self, 'attr': 'note_speed', 'step': 0.1, 'big_step': 1.0},
            {'label': 'Custom Start', 'type': 'bool', 'obj': self, 'attr': 'use_custom_start'},
            {'label': 'Start Time (ms)', 'type': 'int', 'obj': self, 'attr': 'custom_start_ms', 'step': 100, 'big_step': 1000},
            {'label': 'Save Chart', 'type': 'action', 'action': self.save_chart},
            {'label': 'Reload Chart', 'type': 'action', 'action': self.reload_chart}
        ]

    def recalculate_timing(self):
        self.pixels_per_second = self.note_speed * FPS

    def create_checkered_surface(self):
        track_width = LANE_WIDTH * LANE_COUNT; surface = pygame.Surface((track_width, SCREEN_HEIGHT)); tile_size = 30
        for y in range(0, SCREEN_HEIGHT, tile_size):
            for x in range(0, track_width, tile_size):
                color = CHECKER_COLOR_A if (x // tile_size + y // tile_size) % 2 == 0 else CHECKER_COLOR_B
                surface.fill(color, (x, y, tile_size, tile_size))
        return surface

    def run(self, fade_in_duration=0):
        if fade_in_duration > 0:
            self.fade_in_duration = fade_in_duration
            self.fade_start_time = pygame.time.get_ticks()
            
        while self.is_running:
            dt = self.clock.tick(FPS)
            if self.music_playing:
                self.scroll_ms = self.playback_start_scroll_ms + (pygame.time.get_ticks() - self.playback_start_tick)
            self.handle_events(); self.handle_continuous_input(dt); self.draw()
        return self.song_info

    def handle_events(self):
        for event in pygame.event.get():
            mods = pygame.key.get_mods()
            is_ctrl, is_shift = mods & pygame.KMOD_CTRL, mods & pygame.KMOD_SHIFT
            if event.type == pygame.QUIT: self.is_running = False
            if event.type == pygame.KEYDOWN:
                if event.key == pygame.K_7: self.debug_menu_visible = not self.debug_menu_visible; continue
                if self.debug_menu_visible: self.handle_menu_input(event.key); continue
                if is_ctrl and event.key == pygame.K_c: self.copy_selection()
                elif is_ctrl and event.key == pygame.K_v: self.paste_selection()
                elif event.key in [pygame.K_DELETE, pygame.K_BACKSPACE]: self.delete_selection()
                elif event.key == pygame.K_e and self.new_chart: self.scroll_ms = self.new_chart[-1]['time']
                elif event.key == pygame.K_s and self.use_custom_start: self.custom_start_ms = self.scroll_ms
                elif event.key == pygame.K_ESCAPE: self.is_running = False
                elif self.music_loaded and event.key == pygame.K_p:
                    if self.music_playing: pygame.mixer.music.pause()
                    else:
                        self.playback_start_tick, self.playback_start_scroll_ms = pygame.time.get_ticks(), self.scroll_ms
                        if not pygame.mixer.music.get_busy(): pygame.mixer.music.play(start=self.scroll_ms / 1000.0)
                        else: pygame.mixer.music.unpause()
                    self.music_playing = not self.music_playing
                elif self.music_loaded and event.key == pygame.K_r:
                    pygame.mixer.music.stop(); self.scroll_ms = 0; self.music_playing = False
                elif event.key in [pygame.K_1, pygame.K_2, pygame.K_4, pygame.K_8]: self.snap = int(pygame.key.name(event.key))
            elif event.type == pygame.MOUSEBUTTONDOWN:
                if not self.debug_menu_visible:
                    if event.button == 1: self.selection_start_pos = event.pos
                    elif not self.music_playing and event.button == 4: self.scroll_ms = max(0, self.scroll_ms - 50)
                    elif not self.music_playing and event.button == 5: self.scroll_ms += 50
            elif event.type == pygame.MOUSEMOTION and self.selection_start_pos:
                self.selection_box = pygame.Rect(self.selection_start_pos, (event.pos[0] - self.selection_start_pos[0], event.pos[1] - self.selection_start_pos[1]))
            elif event.type == pygame.MOUSEBUTTONUP and not self.debug_menu_visible:
                if event.button == 1: self._handle_left_click_up(event.pos, is_ctrl, is_shift)
                elif event.button == 3: self._handle_right_click(event.pos)
                self.selection_box, self.selection_start_pos = None, None

    def _handle_left_click_up(self, pos, is_ctrl, is_shift):
        was_drag = self.selection_box and (abs(self.selection_box.width) > 5 or abs(self.selection_box.height) > 5)
        if was_drag:
            self._handle_selection_drag()
        else:
            if not (is_shift or is_ctrl): self.selected_notes.clear()
            if self.save_button_rect.collidepoint(pos): self.save_chart()
            else:
                lane = self.get_lane_from_mouse(pos[0])
                if lane is not None:
                    time_ms = self.get_time_from_mouse(pos[1])
                    if is_shift: self.handle_hold_note_placement(time_ms, lane)
                    else: self.add_note(time_ms, lane)

    def _handle_selection_drag(self):
        selection_rect_norm = self.selection_box.copy(); selection_rect_norm.normalize()
        newly_selected = {i for i, note in enumerate(self.new_chart) if selection_rect_norm.colliderect(self._get_note_rect(note))}
        if pygame.key.get_mods() & pygame.KMOD_CTRL: self.selected_notes.symmetric_difference_update(newly_selected)
        else: self.selected_notes.update(newly_selected)

    def _get_note_rect(self, note):
        y = PLAYHEAD_Y + ((note['time'] - self.scroll_ms) / 1000.0) * self.pixels_per_second
        return self.note_sprites[note['lane']]['normal'].get_rect(center=(self.start_x + (note['lane'] + 0.5) * LANE_WIDTH, y))

    def _handle_right_click(self, pos):
        lane = self.get_lane_from_mouse(pos[0])
        if lane is not None:
            time_ms = self.get_time_from_mouse(pos[1])
            self.remove_note(time_ms, lane)

    def copy_selection(self):
        if not self.selected_notes: return
        notes_to_copy = [self.new_chart[i] for i in sorted(list(self.selected_notes))]
        if not notes_to_copy: return
        min_time = min(n['time'] for n in notes_to_copy)
        self.note_clipboard = [{'lane': n['lane'], 'relative_time': n['time'] - min_time, 'duration': n.get('duration')} for n in notes_to_copy]
        print(f"Copied {len(self.note_clipboard)} notes.")

    def paste_selection(self):
        if not self.note_clipboard: return
        paste_time = self.get_time_from_mouse(pygame.mouse.get_pos()[1])
        for note_data in self.note_clipboard:
            new_note = {'lane': note_data['lane'], 'time': paste_time + note_data['relative_time']}
            if note_data['duration'] is not None: new_note['duration'] = note_data['duration']
            self.new_chart.append(new_note)
        self.new_chart.sort(key=lambda x: x['time'])
        print(f"Pasted {len(self.note_clipboard)} notes.")

    def delete_selection(self):
        if not self.selected_notes: return
        self.new_chart = [note for i, note in enumerate(self.new_chart) if i not in self.selected_notes]
        self.selected_notes.clear(); print(f"Deleted selected notes.")

    def handle_hold_note_placement(self, time_ms, lane):
        if lane in self.hold_note_starts:
            start_time = self.hold_note_starts.pop(lane)
            if time_ms < start_time: start_time, time_ms = time_ms, start_time
            duration = time_ms - start_time
            if duration > 50: self.add_note(start_time, lane, duration=duration)
        else: self.hold_note_starts[lane] = time_ms

    def handle_continuous_input(self, dt):
        if not self.debug_menu_visible and not self.music_playing:
            keys = pygame.key.get_pressed(); scroll_speed = 500 * (dt / 1000.0)
            if keys[pygame.K_UP]: self.scroll_ms = max(0, self.scroll_ms - scroll_speed)
            if keys[pygame.K_DOWN]: self.scroll_ms += scroll_speed

    def handle_menu_input(self, key):
        mods = pygame.key.get_mods(); is_shift = mods & pygame.KMOD_SHIFT
        selected_item = self.debug_menu_items[self.selected_menu_index]
        if key == pygame.K_UP: self.selected_menu_index = (self.selected_menu_index - 1) % len(self.debug_menu_items)
        elif key == pygame.K_DOWN: self.selected_menu_index = (self.selected_menu_index + 1) % len(self.debug_menu_items)
        elif key == pygame.K_RETURN and selected_item['type'] == 'action': selected_item['action']()
        elif selected_item['type'] == 'bool' and key in [pygame.K_LEFT, pygame.K_RIGHT, pygame.K_RETURN]:
            setattr(selected_item['obj'], selected_item['attr'], not getattr(selected_item['obj'], selected_item['attr']))
        elif selected_item['type'] in ['float', 'int']:
            step = selected_item.get('big_step' if is_shift else 'step', 1)
            current_val = getattr(selected_item['obj'], selected_item['attr'])
            new_val = max(0, current_val + (step if key == pygame.K_RIGHT else -step if key == pygame.K_LEFT else 0))
            setattr(selected_item['obj'], selected_item['attr'], new_val)
            self.recalculate_timing()

    def get_lane_from_mouse(self, mx):
        if self.start_x <= mx < self.start_x + LANE_WIDTH * LANE_COUNT: return int((mx - self.start_x) // LANE_WIDTH)

    def get_time_from_mouse(self, my):
        pixel_offset = my - PLAYHEAD_Y; time_offset = (pixel_offset / self.pixels_per_second) * 1000
        target_time = self.scroll_ms + time_offset; ms_per_snap = (60000.0 / self.bpm) / self.snap
        return round(target_time / ms_per_snap) * ms_per_snap

    def add_note(self, time_ms, lane, duration=None):
        if any(n['lane'] == lane and abs(n['time'] - time_ms) < 10 for n in self.new_chart): return
        note_data = {"time": max(0, time_ms), "lane": lane}
        if duration is not None: note_data["duration"] = duration
        self.new_chart.append(note_data); self.new_chart.sort(key=lambda x: x['time'])

    def remove_note(self, time_ms, lane):
        self.new_chart = [n for n in self.new_chart if not (n['lane'] == lane and abs(n['time'] - time_ms) < 20)]

    def save_chart(self):
        save_path = os.path.join(self.song_info['folder_path'], "chart.json")
        output_data = {"title": self.song_info['title'], "artist": self.song_info['artist'], "bpm": self.bpm, "speed": self.note_speed, "audio_file": os.path.basename(self.song_info.get('audio_path','')), "use_custom_start": self.use_custom_start, "start_offset_ms": self.custom_start_ms, "chart": self.new_chart}
        with open(save_path, 'w') as f: json.dump(output_data, f, indent=4)
        self.song_info.update(output_data); print(f"Chart saved to {save_path}")

    def reload_chart(self):
        chart_path = os.path.join(self.song_info['folder_path'], "chart.json")
        if os.path.exists(chart_path):
            try:
                with open(chart_path, 'r') as f: reloaded_data = json.load(f)
                self.new_chart = reloaded_data.get('chart', [])
                self.bpm = float(reloaded_data.get('bpm', 120.0))
                self.note_speed = float(reloaded_data.get('speed', INITIAL_NOTE_SPEED))
                self.use_custom_start = reloaded_data.get('use_custom_start', False)
                self.custom_start_ms = reloaded_data.get('start_offset_ms', 0)
                self.recalculate_timing(); print("Chart reloaded from file.")
            except (json.JSONDecodeError, KeyError) as e: print(f"Error reloading chart: {e}")

    def draw(self):
        self.screen.fill(BLACK); self.screen.blit(self.track_surface, (self.start_x, 0))
        ms_per_beat = 60000.0 / self.bpm; ms_per_snap = ms_per_beat / self.snap
        start_vis_time = self.scroll_ms - (PLAYHEAD_Y / self.pixels_per_second * 1000)
        end_vis_time = self.scroll_ms + ((SCREEN_HEIGHT - PLAYHEAD_Y) / self.pixels_per_second * 1000)
        first_beat = int(start_vis_time / ms_per_snap) * ms_per_snap
        for beat_time in range(int(first_beat), int(end_vis_time), int(ms_per_snap)):
            y = PLAYHEAD_Y + ((beat_time - self.scroll_ms) / 1000.0) * self.pixels_per_second
            if 0 < y < SCREEN_HEIGHT: pygame.draw.line(self.screen, (70,70,70), (self.start_x, y), (self.start_x + LANE_WIDTH * LANE_COUNT, y), 1)

        for i, note in enumerate(self.new_chart):
            y = PLAYHEAD_Y + ((note['time'] - self.scroll_ms) / 1000.0) * self.pixels_per_second
            if -50 < y < SCREEN_HEIGHT + 500: self._draw_note(note, y, i in self.selected_notes)

        for lane, start_time in self.hold_note_starts.items():
            start_y = PLAYHEAD_Y + ((start_time - self.scroll_ms) / 1000.0) * self.pixels_per_second
            start_sprite = self.note_sprites[lane]['hold_end']
            rect = start_sprite.get_rect(center=(self.start_x + (lane + 0.5) * LANE_WIDTH, start_y))
            self.screen.blit(start_sprite, rect)
            if self.get_lane_from_mouse(pygame.mouse.get_pos()[0]) == lane:
                pygame.draw.line(self.screen, LANE_COLORS[lane], rect.center, (rect.centerx, pygame.mouse.get_pos()[1]), 10)

        if self.selection_box: self._draw_selection_box()
        if self.use_custom_start:
            y = PLAYHEAD_Y + ((self.custom_start_ms - self.scroll_ms) / 1000.0) * self.pixels_per_second
            if 0 < y < SCREEN_HEIGHT: pygame.draw.line(self.screen, (0, 255, 0), (self.start_x, y), (self.start_x + LANE_WIDTH * LANE_COUNT, y), 3)

        pygame.draw.line(self.screen, WHITE, (self.start_x, PLAYHEAD_Y), (self.start_x + LANE_WIDTH * LANE_COUNT, PLAYHEAD_Y), 3)
        self._draw_ui_text()
        if self.debug_menu_visible: self.draw_debug_menu()
        
        if self.fade_in_duration > 0:
            elapsed = pygame.time.get_ticks() - self.fade_start_time
            if elapsed < self.fade_in_duration:
                progress = elapsed / self.fade_in_duration
                alpha = max(0, 255 * (1 - progress))
                fade_surface = pygame.Surface(self.screen.get_size())
                fade_surface.fill(BLACK)
                fade_surface.set_alpha(alpha)
                self.screen.blit(fade_surface, (0, 0))
            else:
                self.fade_in_duration = 0
                
        pygame.display.flip()

    def _draw_note(self, note, y, is_selected):
        lane, duration = note['lane'], note.get('duration')
        sprite_set = self.highlight_sprites if is_selected else self.note_sprites
        center_x = self.start_x + (lane + 0.5) * LANE_WIDTH
        if duration:
            end_y = PLAYHEAD_Y + ((note['time'] + duration - self.scroll_ms) / 1000.0) * self.pixels_per_second
            tail_height = end_y - y
            if tail_height > 0:
                scaled_tail = pygame.transform.scale(sprite_set[lane]['hold_middle'], (NOTE_WIDTH, int(tail_height)))
                self.screen.blit(scaled_tail, (self.start_x + lane * LANE_WIDTH, y))
            self.screen.blit(sprite_set[lane]['hold_start'], sprite_set[lane]['hold_start'].get_rect(center=(center_x, end_y)))
            self.screen.blit(sprite_set[lane]['hold_end'], sprite_set[lane]['hold_end'].get_rect(center=(center_x, y)))
        else:
            self.screen.blit(sprite_set[lane]['normal'], sprite_set[lane]['normal'].get_rect(center=(center_x, y)))

    def _draw_selection_box(self):
        sel_rect_norm = self.selection_box.copy(); sel_rect_norm.normalize()
        s = pygame.Surface(sel_rect_norm.size, pygame.SRCALPHA)
        s.fill((100, 100, 255, 60)); pygame.draw.rect(s, (150, 150, 255), s.get_rect(), 2)
        self.screen.blit(s, sel_rect_norm.topleft)

    def _draw_ui_text(self):
        ui_text_lines = [ f"Time: {self.scroll_ms:.0f}ms | Selected: {len(self.selected_notes)}", "P: Play | R: Rewind | E: End", "Ctrl+C: Copy | Ctrl+V: Paste | Del: Delete", "Shift+Click: Hold Note" ]
        if self.use_custom_start: ui_text_lines.append("S: Set Start Time")
        if not self.music_loaded: ui_text_lines.insert(0, "No Audio File Loaded")
        for i, text in enumerate(ui_text_lines):
            color = RED if text.startswith("No Audio") else WHITE
            self.screen.blit(self.font_small.render(text, True, color), (10, 10 + i * 30))
        pygame.draw.rect(self.screen, RED, self.save_button_rect)
        save_text = self.font_small.render("Save Chart", True, WHITE)
        self.screen.blit(save_text, save_text.get_rect(center=self.save_button_rect.center))

    def draw_debug_menu(self):
        overlay = pygame.Surface((400, 300), pygame.SRCALPHA); overlay.fill((0, 0, 0, 180))
        for i, item in enumerate(self.debug_menu_items):
            color = (255, 255, 0) if i == self.selected_menu_index else WHITE
            label = f"{item['label']}: "
            if item['type'] in ['float', 'int']: text = f"{label}{getattr(item['obj'], item['attr']):.1f}" if item['type'] == 'float' else f"{label}{int(getattr(item['obj'], item['attr']))}"
            elif item['type'] == 'bool': text = f"{label}[{'On' if getattr(item['obj'], item['attr']) else 'Off'}]"
            else: text = item['label']
            overlay.blit(self.font_menu.render(text, True, color), (20, 20 + i * 35))
        self.screen.blit(overlay, (SCREEN_WIDTH - 410, 10))


# --- App Class ---
class App:
    def __init__(self):
        pygame.init(); pygame.mixer.init()
        self.screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT))
        pygame.display.set_caption("Python Rhythm Hero")
        self.clock = pygame.time.Clock()
        self.font_title = load_font(FONT_FILENAME, 60)
        self.font_menu = load_font(FONT_FILENAME, 42)
        self.root = tk.Tk(); self.root.withdraw()
        self.load_assets(); self.songs = self.load_songs()
        self.selected_song_index = 0
        self.menu_scroll_position = 0.0
        self.game_state = "MAIN_MENU"; self.menu_option = "PLAY"

        self.next_game_state = None
        self.transition_start_time = 0
        self.ANIMATION_DURATION = 1200
        self.CENTERING_PHASE_DURATION = 600
        self.BOUNCE_PHASE_DURATION = self.ANIMATION_DURATION - self.CENTERING_PHASE_DURATION
        self.FADE_IN_FROM_BLACK_DURATION = 500
        
        self.action_select_target = 0.0
        self.action_select_lerp = 0.0

        self.VINYL_DIAMETER = 750
        self.vinyl_rotation_angle = 0.0
        self.vinyl_overlay = self._create_vinyl_overlay(self.VINYL_DIAMETER)

        self.vinyl_current_surface = None
        self.vinyl_target_surface = None
        self.is_vinyl_transitioning = False
        self.vinyl_transition_progress = 1.0

        self._load_song_icon(self.selected_song_index, initial_load=True)

    def load_assets(self):
        script_dir = os.path.dirname(__file__); assets_path = os.path.join(script_dir, "assets")
        sprite_filenames = {'normal': 'normal_note.png', 'hold_start': 'hold_start.png', 'hold_middle': 'hold_middle.png', 'hold_end': 'hold_end.png'}
        try:
            base_sprites = {name: pygame.transform.scale(pygame.image.load(os.path.join(assets_path, fn)).convert_alpha(), SPRITE_SIZES[name]) for name, fn in sprite_filenames.items()}
        except (pygame.error, FileNotFoundError):
            print("WARNING: Using placeholder graphics for notes."); base_sprites = create_placeholder_sprites()
        self.note_sprites = [{'normal': colorize_sprite(base_sprites['normal'], color), 'hold_start': colorize_sprite(base_sprites['hold_start'], color), 'hold_middle': colorize_sprite(base_sprites['hold_middle'], color), 'hold_end': colorize_sprite(base_sprites['hold_end'], color), 'hold_start_held': base_sprites['hold_start']} for color in LANE_COLORS]

    def load_songs(self):
        songs_path = os.path.join(os.path.dirname(__file__), "songs")
        if not os.path.exists(songs_path): os.makedirs(songs_path)
        songs = []
        for song_folder in os.listdir(songs_path):
            chart_path = os.path.join(songs_path, song_folder, "chart.json")
            if os.path.exists(chart_path):
                try:
                    with open(chart_path, 'r') as f: song_data = json.load(f)
                    folder_path = os.path.join(songs_path, song_folder)
                    song_data['folder_path'] = folder_path
                    song_data['audio_path'] = self._get_audio_path(folder_path, song_data.get('audio_file', ''))
                    songs.append(song_data)
                except (json.JSONDecodeError, KeyError) as e: print(f"Error loading {song_folder}: {e}")
        return songs if songs else [self.create_default_song()]

    def _get_audio_path(self, folder_path, audio_file):
        if not audio_file: return ""
        audio_path = os.path.join(folder_path, audio_file)
        if audio_file.lower().endswith('.mp3'):
            if not PYDUB_AVAILABLE:
                print(f"WARNING: pydub not found. Cannot play .mp3: {audio_file}"); return ""
            ogg_filename = os.path.splitext(audio_file)[0] + ".ogg"
            ogg_path = os.path.join(folder_path, ogg_filename)
            if not os.path.exists(ogg_path):
                try:
                    print(f"Converting {audio_file}..."); AudioSegment.from_mp3(audio_path).export(ogg_path, format="ogg")
                except Exception as e:
                    print(f"ERROR: Could not convert MP3: {e}"); return ""
            return ogg_path
        return audio_path if os.path.exists(audio_path) else ""

    def create_default_song(self):
        print("No songs found. Creating a default song.")
        default_song_path = os.path.join(os.path.dirname(__file__), "songs", "default_song")
        os.makedirs(default_song_path, exist_ok=True)
        chart_data = {"title": "Default Song", "artist": "Pygame", "bpm": 120, "speed": 7, "audio_file": "", "chart": []}
        with open(os.path.join(default_song_path, "chart.json"), 'w') as f: json.dump(chart_data, f, indent=4)
        chart_data.update({'folder_path': default_song_path, 'audio_path': ""})
        return chart_data

    def run(self):
        running = True
        while running:
            if self.game_state in ["MAIN_MENU", "ACTION_SELECT"]:
                running = self.run_main_menu()
            elif self.game_state == "TRANSITION_TO_GAME":
                running = self.run_transition_animation()
            elif self.game_state == "PLAYING":
                GameSession(self.screen, self.clock, self.songs[self.selected_song_index], self.note_sprites).run(fade_in_duration=self.FADE_IN_FROM_BLACK_DURATION)
                self.game_state = "MAIN_MENU"
                self.action_select_target = 0.0
            elif self.game_state == "CHARTING":
                updated_song_data = ChartEditor(self.screen, self.clock, self.songs[self.selected_song_index].copy(), self.note_sprites).run(fade_in_duration=self.FADE_IN_FROM_BLACK_DURATION)
                if updated_song_data: self.songs[self.selected_song_index] = updated_song_data
                self.game_state = "MAIN_MENU"
                self.action_select_target = 0.0
                pygame.mixer.music.stop()
        pygame.quit()

    def run_main_menu(self):
        self.action_select_lerp += (self.action_select_target - self.action_select_lerp) * 0.08

        if self.is_vinyl_transitioning:
            self.vinyl_transition_progress += 0.05
            if self.vinyl_transition_progress >= 1.0:
                self.vinyl_transition_progress = 1.0
                self.is_vinyl_transitioning = False
                self.vinyl_current_surface = self.vinyl_target_surface
                self.vinyl_target_surface = None

        if self.game_state == "MAIN_MENU":
            num_items = len(self.songs) + 1
            target_pos = float(self.selected_song_index)
            current_pos = self.menu_scroll_position

            distance = target_pos - current_pos
            if abs(distance) > num_items / 2:
                if distance > 0: current_pos += num_items
                else: target_pos += num_items

            scroll_speed = 0.1
            self.menu_scroll_position = current_pos + (target_pos - current_pos) * scroll_speed

            if self.menu_scroll_position < 0: self.menu_scroll_position += num_items
            self.menu_scroll_position %= num_items

        for event in pygame.event.get():
            if event.type == pygame.QUIT or (event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE): return False
            if event.type == pygame.KEYDOWN: self._handle_menu_keypress(event.key)

        self.draw_main_menu()
        self.clock.tick(FPS)
        return True

    def run_transition_animation(self):
        for event in pygame.event.get():
            if event.type == pygame.QUIT or (event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE):
                return False

        elapsed = pygame.time.get_ticks() - self.transition_start_time
        overall_progress = min(1.0, elapsed / self.ANIMATION_DURATION)

        start_pos = (0, SCREEN_HEIGHT / 2)
        end_pos = (SCREEN_WIDTH / 2, SCREEN_HEIGHT / 2)
        
        centering_progress = min(1.0, elapsed / self.CENTERING_PHASE_DURATION)
        eased_centering_progress = 1 - pow(1 - centering_progress, 3)

        current_x = start_pos[0] + (end_pos[0] - start_pos[0]) * eased_centering_progress
        current_y = start_pos[1] + (end_pos[1] - start_pos[1]) * eased_centering_progress

        current_size = self.VINYL_DIAMETER
        if elapsed > self.CENTERING_PHASE_DURATION:
            bounce_progress = (elapsed - self.CENTERING_PHASE_DURATION) / self.BOUNCE_PHASE_DURATION
            n1 = 7.5625
            d1 = 2.75
            if bounce_progress < 1 / d1: scale_factor = n1 * bounce_progress * bounce_progress
            elif bounce_progress < 2 / d1: bounce_progress -= 1.5 / d1; scale_factor = n1 * bounce_progress * bounce_progress + 0.75
            elif bounce_progress < 2.5 / d1: bounce_progress -= 2.25 / d1; scale_factor = n1 * bounce_progress * bounce_progress + 0.9375
            else: bounce_progress -= 2.625 / d1; scale_factor = n1 * bounce_progress * bounce_progress + 0.984375
            
            final_scale = 0.8
            scale_range = 1.0 - final_scale 
            current_scale = 1.0 - (scale_range * scale_factor)
            current_size = int(self.VINYL_DIAMETER * current_scale)
        
        self.screen.fill(BLACK)

        if self.vinyl_current_surface and current_size > 1:
            self.vinyl_rotation_angle = (self.vinyl_rotation_angle + 0.5) % 360
            scaled_vinyl = pygame.transform.smoothscale(self.vinyl_current_surface, (current_size, current_size))
            rotated_vinyl = pygame.transform.rotate(scaled_vinyl, self.vinyl_rotation_angle)
            vinyl_rect = rotated_vinyl.get_rect(center=(current_x, current_y))
            self.screen.blit(rotated_vinyl, vinyl_rect)

        pygame.display.flip()
        self.clock.tick(FPS)

        if overall_progress >= 1.0:
            self.game_state = self.next_game_state
            self.next_game_state = None

        return True

    def _create_vinyl_overlay(self, diameter):
        overlay = pygame.Surface((diameter, diameter), pygame.SRCALPHA)
        center_pos = (diameter // 2, diameter // 2)
        for r in range(diameter // 2, int(diameter * 0.2), -3): pygame.draw.circle(overlay, (0, 0, 0, 50), center_pos, r, 1)
        pygame.draw.circle(overlay, (25, 25, 25), center_pos, int(diameter * 0.2))
        pygame.draw.circle(overlay, (15, 15, 15), center_pos, int(diameter * 0.18), 5)
        pygame.draw.circle(overlay, (0, 0, 0, 128), center_pos, int(diameter * 0.02))
        return overlay

    def _load_song_icon(self, index, initial_load=False):
        vinyl_surface = None
        if index < len(self.songs):
            song_data = self.songs[index]
            icon_path = os.path.join(song_data['folder_path'], "icon.png")
            if os.path.exists(icon_path):
                try:
                    loaded_icon = pygame.image.load(icon_path).convert_alpha()
                    scaled_icon = pygame.transform.smoothscale(loaded_icon, (self.VINYL_DIAMETER, self.VINYL_DIAMETER))
                    vinyl_surface = pygame.Surface((self.VINYL_DIAMETER, self.VINYL_DIAMETER), pygame.SRCALPHA)
                    pygame.draw.circle(vinyl_surface, (255, 255, 255), vinyl_surface.get_rect().center, self.VINYL_DIAMETER // 2)
                    vinyl_surface.blit(scaled_icon, (0, 0), special_flags=pygame.BLEND_RGBA_MIN)
                    vinyl_surface.blit(self.vinyl_overlay, (0, 0))
                except pygame.error as e: print(f"Error loading icon for {song_data['title']}: {e}")
        if initial_load: self.vinyl_current_surface = vinyl_surface
        else: return vinyl_surface

    def _start_vinyl_transition(self, new_index):
        if self.is_vinyl_transitioning: return
        self.is_vinyl_transitioning = True
        self.vinyl_transition_progress = 0.0
        self.vinyl_target_surface = self._load_song_icon(new_index)

    def _handle_menu_keypress(self, key):
        if self.game_state == "ACTION_SELECT":
            if key in [pygame.K_LEFT, pygame.K_RIGHT]: self.menu_option = "CHART" if self.menu_option == "PLAY" else "PLAY"
            elif key == pygame.K_RETURN:
                self.next_game_state = "PLAYING" if self.menu_option == "PLAY" else "CHARTING"
                self.game_state = "TRANSITION_TO_GAME"
                self.transition_start_time = pygame.time.get_ticks()
            elif key == pygame.K_BACKSPACE:
                self.game_state = "MAIN_MENU"
                self.action_select_target = 0.0
        elif self.game_state == "MAIN_MENU":
            num_menu_items = len(self.songs) + 1
            prev_index = self.selected_song_index
            if key == pygame.K_UP: self.selected_song_index = (self.selected_song_index - 1) % num_menu_items
            elif key == pygame.K_DOWN: self.selected_song_index = (self.selected_song_index + 1) % num_menu_items
            if prev_index != self.selected_song_index: self._start_vinyl_transition(self.selected_song_index)
            if key == pygame.K_RETURN:
                if self.selected_song_index < len(self.songs):
                    self.game_state = "ACTION_SELECT"
                    self.action_select_target = 1.0
                else: self.create_new_chart_session()

    def create_new_chart_session(self):
        audio_path = filedialog.askopenfilename(title="Select an Audio File", filetypes=[("Audio Files", "*.mp3 *.ogg *.wav")])
        if not audio_path: return
        songs_dir = os.path.join(os.path.dirname(__file__), "songs")
        file_name = os.path.basename(audio_path)
        folder_name = os.path.splitext(file_name)[0]
        new_song_path = os.path.join(songs_dir, folder_name)
        os.makedirs(new_song_path, exist_ok=True)
        shutil.copy(audio_path, new_song_path)
        chart_data = {"title": folder_name, "artist": "Unknown", "bpm": 120, "speed": 7, "audio_file": file_name, "chart": []}
        with open(os.path.join(new_song_path, "chart.json"), 'w') as f: json.dump(chart_data, f, indent=4)
        self.songs = self.load_songs()
        self.selected_song_index = next((i for i, s in enumerate(self.songs) if s['folder_path'] == new_song_path), 0)
        self.game_state = "CHARTING"
        self.action_select_target = 0.0

    def draw_main_menu(self):
        self.screen.fill(BLACK)
        self.vinyl_rotation_angle = (self.vinyl_rotation_angle + 0.25) % 360

        ease = 1 - pow(1 - self.action_select_lerp, 3)
        start_size = self.VINYL_DIAMETER
        end_size = self.VINYL_DIAMETER * 1.2
        current_size = int(start_size + (end_size - start_size) * ease)
        start_x = 0
        end_x = 0
        current_x = start_x + (end_x - start_x) * ease

        if self.is_vinyl_transitioning:
            eased_progress = 1 - (1 - self.vinyl_transition_progress) ** 2
            if self.vinyl_current_surface:
                size = (current_size, current_size)
                start_x_trans, end_x_trans = current_x, current_x - self.VINYL_DIAMETER // 2
                current_x_trans = start_x_trans + (end_x_trans - start_x_trans) * eased_progress
                scaled = pygame.transform.smoothscale(self.vinyl_current_surface, size)
                rotated = pygame.transform.rotate(scaled, self.vinyl_rotation_angle)
                rect = rotated.get_rect(center=(current_x_trans, SCREEN_HEIGHT / 2))
                self.screen.blit(rotated, rect)
            if self.vinyl_target_surface:
                size = (current_size, current_size)
                start_x_trans, end_x_trans = current_x - self.VINYL_DIAMETER // 2, current_x
                target_x_trans = start_x_trans + (end_x_trans - start_x_trans) * eased_progress
                scaled = pygame.transform.smoothscale(self.vinyl_target_surface, size)
                rotated = pygame.transform.rotate(scaled, self.vinyl_rotation_angle)
                rect = rotated.get_rect(center=(target_x_trans, SCREEN_HEIGHT / 2))
                self.screen.blit(rotated, rect)
        else:
            if self.vinyl_current_surface:
                scaled_vinyl = pygame.transform.smoothscale(self.vinyl_current_surface, (current_size, current_size))
                rotated_vinyl = pygame.transform.rotate(scaled_vinyl, self.vinyl_rotation_angle)
                vinyl_rect = rotated_vinyl.get_rect(center=(current_x, SCREEN_HEIGHT / 2))
                self.screen.blit(rotated_vinyl, vinyl_rect)

        title = self.font_title.render("Python Rhythm Hero", True, WHITE)
        title.set_alpha(255 * (1 - self.action_select_lerp))
        if title.get_alpha() > 5:
            self.screen.blit(title, (SCREEN_WIDTH / 2 - title.get_width() / 2, 50))

        list_alpha = 255 * (1 - self.action_select_lerp)
        if list_alpha > 5:
            menu_items = [f"{s['title']}" for s in self.songs]
            menu_items.append("Create New Chart...")
            num_items = len(menu_items)
            center_y = SCREEN_HEIGHT / 2 + 20
            num_visible_items, max_font_size, font_size_step = 2, 42, 10
            max_alpha, alpha_step, base_vertical_spacing, spacing_falloff = 255, 85, 50, 0.8
            y_positions = {0: center_y}
            last_y, current_spacing = center_y, base_vertical_spacing
            for i in range(1, num_visible_items + 2):
                y_positions[i] = last_y + current_spacing; last_y = y_positions[i]; current_spacing *= spacing_falloff
            last_y, current_spacing = center_y, base_vertical_spacing
            for i in range(1, num_visible_items + 2):
                y_positions[-i] = last_y - current_spacing; last_y = y_positions[-i]; current_spacing *= spacing_falloff
            center_item_index = round(self.menu_scroll_position)
            for i in range(-num_visible_items, num_visible_items + 1):
                item_index = (center_item_index + i) % num_items
                distance = item_index - self.menu_scroll_position
                if abs(distance) > num_items / 2: distance -= math.copysign(num_items, distance)
                if abs(distance) > num_visible_items + 0.5: continue
                font_size = max(12, int(max_font_size - abs(distance) * font_size_step))
                alpha = max(0, int(max_alpha - abs(distance) * alpha_step))
                color = WHITE if item_index == self.selected_song_index else GRAY
                temp_font = load_font(FONT_FILENAME, font_size)
                text_surf = temp_font.render(menu_items[item_index], True, color)
                text_surf.set_alpha(alpha * (list_alpha / 255.0))
                floor_dist, ceil_dist = math.floor(distance), math.ceil(distance)
                if floor_dist == ceil_dist: y_pos = y_positions.get(floor_dist, 0)
                else:
                    y1, y2 = y_positions.get(floor_dist, 0), y_positions.get(ceil_dist, 0)
                    y_pos = y1 + (y2 - y1) * (distance - floor_dist)
                text_rect = text_surf.get_rect(center=(SCREEN_WIDTH / 2, y_pos))
                self.screen.blit(text_surf, text_rect)

        ui_alpha = 255 * self.action_select_lerp
        if ui_alpha > 5:
            song = self.songs[self.selected_song_index]
            title_surf = self.font_title.render(song['title'], True, WHITE)
            artist_surf = self.font_menu.render(song.get('artist', 'Unknown Artist'), True, GRAY)
            title_surf.set_alpha(ui_alpha); artist_surf.set_alpha(ui_alpha)
            title_rect = title_surf.get_rect(center=(SCREEN_WIDTH * 0.75, 120))
            artist_rect = artist_surf.get_rect(center=(SCREEN_WIDTH * 0.75, 180))
            self.screen.blit(title_surf, title_rect)
            self.screen.blit(artist_surf, artist_rect)
            play_text = self.font_menu.render("Play", True, WHITE if self.menu_option == "PLAY" else GRAY)
            chart_text = self.font_menu.render("Chart", True, WHITE if self.menu_option == "CHART" else GRAY)
            play_text.set_alpha(ui_alpha); chart_text.set_alpha(ui_alpha)
            play_rect = play_text.get_rect(center=(SCREEN_WIDTH * 0.65, SCREEN_HEIGHT - 100))
            chart_rect = chart_text.get_rect(center=(SCREEN_WIDTH * 0.85, SCREEN_HEIGHT - 100))
            self.screen.blit(play_text, play_rect)
            self.screen.blit(chart_text, chart_rect)

        pygame.display.flip()

if __name__ == "__main__":
    app = App()
    app.run()
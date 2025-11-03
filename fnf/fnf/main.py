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
DARK_GRAY = (30, 30, 30, 200) 
CHECKER_COLOR_A = (40, 40, 40, 180); CHECKER_COLOR_B = (55, 55, 55, 180) 
LANE_COLORS = [(0, 255, 255), (255, 0, 255), (255, 255, 0), (0, 255, 0)]

# Game settings
INITIAL_NOTE_SPEED = 7
LANE_COUNT = 4; LANE_WIDTH = 120; NOTE_WIDTH = 120
SPRITE_SIZES = {'normal': (NOTE_WIDTH, 30), 'hold_start': (NOTE_WIDTH, 20), 'hold_middle': (NOTE_WIDTH, 20), 'hold_end': (NOTE_WIDTH, 20)}
KEY_MAP = { pygame.K_s: 0, pygame.K_d: 1, pygame.K_j: 2, pygame.K_k: 3 }; KEY_LABELS = ['S', 'D', 'J', 'K']
PLAYHEAD_Y = SCREEN_HEIGHT - 100

# --- Helper Functions ---

def create_shadow_surface(diameter, spread=30, intensity=220, steps=20):
    """Creates a surface with a soft, blurred circular shadow."""
    shadow_size = diameter + spread * 2
    shadow_surf = pygame.Surface((shadow_size, shadow_size), pygame.SRCALPHA)
    center = (shadow_size // 2, shadow_size // 2)
    
    for i in range(steps, 0, -1):
        progress = i / steps
        radius = (diameter / 2) + (spread * progress)
        alpha = (intensity / steps) * (1 - (progress * 0.75))
        pygame.draw.circle(shadow_surf, (0, 0, 0, alpha), center, radius)
        
    return shadow_surf

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

def render_text_with_shadow(surface, font, text, color, shadow_color, alpha=255, **pos_kwargs):
    """Renders text with a shadow and blits it, returning the final text rect."""
    shadow_offset = 2
    shadow_pos = {}
    for key, val in pos_kwargs.items():
        if key in ('center', 'topleft', 'topright', 'bottomleft', 'bottomright', 
                   'midtop', 'midleft', 'midbottom', 'midright'):
            shadow_pos[key] = (val[0] + shadow_offset, val[1] + shadow_offset)
        else:
            shadow_pos[key] = val
    if 'centerx' in shadow_pos: shadow_pos['centerx'] += shadow_offset
    if 'centery' in shadow_pos: shadow_pos['centery'] += shadow_offset

    shadow_surf = font.render(text, True, shadow_color)
    shadow_surf.set_alpha(alpha)
    shadow_rect = shadow_surf.get_rect(**shadow_pos)
    
    text_surf = font.render(text, True, color)
    text_surf.set_alpha(alpha)
    text_rect = text_surf.get_rect(**pos_kwargs)

    surface.blit(shadow_surf, shadow_rect)
    surface.blit(text_surf, text_rect)
    return text_rect

def create_placeholder_sprites():
    sprites = {}
    for name, size in SPRITE_SIZES.items():
        sprites[name] = pygame.Surface(size, pygame.SRCALPHA)
        if name in ['normal', 'hold_start', 'hold_end']: pygame.draw.rect(sprites[name], WHITE, sprites[name].get_rect(), border_radius=8)
        else: sprites[name].fill(WHITE)
    return sprites

def colorize_sprite(sprite, color):
    image = sprite.copy(); image.fill(color, special_flags=pygame.BLEND_RGBA_MULT); return image

def load_and_blur_bg(path):
    """Loads an image, resizes it to fit screen (cover), and applies a higher-quality blur."""
    if not path or not os.path.exists(path):
        return None
    try:
        img = pygame.image.load(path).convert()
        
        img_rect = img.get_rect()
        screen_aspect = SCREEN_WIDTH / SCREEN_HEIGHT
        img_aspect = img_rect.width / img_rect.height

        if img_aspect > screen_aspect:
            new_height = SCREEN_HEIGHT
            new_width = int(new_height * img_aspect)
        else:
            new_width = SCREEN_WIDTH
            new_height = int(new_width / img_aspect)

        scaled_img = pygame.transform.scale(img, (new_width, new_height))
        
        fitted_surface = pygame.Surface((SCREEN_WIDTH, SCREEN_HEIGHT))
        blit_pos = ((SCREEN_WIDTH - new_width) // 2, (SCREEN_HEIGHT - new_height) // 2)
        fitted_surface.blit(scaled_img, blit_pos)

        blurred_surface = fitted_surface.copy()
        alpha_surf = fitted_surface.copy()
        alpha_surf.set_alpha(20) 
        
        for dx in [-3, 3]:
            for dy in [-3, 3]:
                blurred_surface.blit(alpha_surf, (dx, dy))
        
        return blurred_surface
    except pygame.error as e:
        print(f"Error loading or blurring background image {path}: {e}")
        return None

# --- Note Class ---
class Note:
    def __init__(self, lane, speed, lane_geo, game_sprites, duration=None):
        self.lane, self.speed, self.y, self.is_active = lane, speed, 0.0, True
        lane_sprites = game_sprites[self.lane]
        self.is_hold = duration is not None
        
        if self.is_hold:
            self.start_img = lane_sprites['hold_start']
            self.end_img = lane_sprites['hold_end']
            self.held_img = lane_sprites['hold_start_held']
            self.image = self.start_img
            self.middle_ribbon = self._create_ribbon(lane_sprites['hold_middle'])
        else:
            self.image = lane_sprites['normal']
        
        self.rect = self.image.get_rect(centerx=lane_geo[self.lane]['center_x'], centery=int(self.y))
        self.duration = duration
        self.full_tail_length = (self.duration / (1000.0 / FPS)) * self.speed if self.is_hold else 0
        self.is_hit = self.is_holding = False
        self.hold_start_time = self.hold_end_time = None

    def _create_ribbon(self, middle_sprite):
        height = middle_sprite.get_height()
        ribbon = pygame.Surface((middle_sprite.get_width(), SCREEN_HEIGHT * 2), pygame.SRCALPHA)
        for y in range(0, SCREEN_HEIGHT * 2, height):
            ribbon.blit(middle_sprite, (0, y))
        return ribbon

    def update(self):
        if not (self.is_hold and self.is_holding):
            self.y += self.speed
            self.rect.centery = int(self.y)

    def draw(self, screen, current_game_time):
        if not self.is_hold:
            screen.blit(self.image, self.rect)
            return

        current_tail_length = self.full_tail_length
        if self.is_holding and self.hold_start_time is not None:
            elapsed = current_game_time - self.hold_start_time
            remaining = max(0, self.duration - elapsed)
            current_tail_length = max(0, (remaining / (1000.0 / FPS)) * self.speed)
        
        if current_tail_length > 0:
            ribbon_height = self.middle_ribbon.get_height()
            y = self.rect.midtop[1]
            remaining_length = int(current_tail_length)

            while remaining_length > 0:
                chunk_height = min(remaining_length, ribbon_height)
                source_rect = pygame.Rect(0, 0, self.rect.width, chunk_height)
                dest_y = y - remaining_length
                dest_rect = pygame.Rect(self.rect.left, dest_y, self.rect.width, chunk_height)
                screen.blit(self.middle_ribbon, dest_rect, source_rect)
                remaining_length -= chunk_height
            
            end_rect = self.end_img.get_rect(midbottom=self.rect.midtop, y=self.rect.midtop[1] - current_tail_length)
            screen.blit(self.end_img, end_rect)
            
        head_image = self.held_img if self.is_holding else self.start_img
        screen.blit(head_image, self.rect)


# --- GameSession Class ---
class GameSession:
    JUDGEMENT_WINDOWS = {'perfect': 22, 'great': 45, 'good': 90}
    ACCURACY_VALUES = {'perfect': 1.0, 'great': 0.7, 'good': 0.4, 'miss': 0.0}
    SCORE_VALUES = {'perfect': 100, 'great': 70, 'good': 40, 'miss': 0}
    HOLD_SCORE_PER_MS = 0.2  # Points awarded per millisecond of holding
    RANK_THRESHOLDS = {'S': 95.0, 'A': 90.0, 'B': 85.0, 'C': 75.0, 'D': 50.0, 'F': 0.0}

    def __init__(self, screen, clock, song_data, sprites):
        self.screen, self.clock, self.song_data, self.note_sprites = screen, clock, song_data, sprites
        self.font = load_font(FONT_FILENAME, 40)
        self.font_song_title = load_font(FONT_FILENAME, 48)
        self.key_label_font = load_font(FONT_FILENAME, 46)
        self.countdown_font = load_font(FONT_FILENAME, 120)
        self.judgement_font = load_font(FONT_FILENAME, 54)
        self.rank_font = load_font(FONT_FILENAME, 160)
        self.stats_font = load_font(FONT_FILENAME, 34)

        self.lane_geometry = self._calculate_lane_geometry()
        self.key_press_feedback = {i: 0 for i in range(LANE_COUNT)}
        self.is_running = True
        
        self.background_image = load_and_blur_bg(self.song_data.get('background_path'))
        
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
                if self.song_data['chart']:
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
        best_note_to_hit = None
        min_delta = float('inf')
        for note in self.notes:
            if note.is_active and not note.is_hit and note.lane == lane:
                delta = abs(note.rect.centery - PLAYHEAD_Y)
                if delta < min_delta:
                    min_delta = delta
                    best_note_to_hit = note
        
        if best_note_to_hit and min_delta < self.JUDGEMENT_WINDOWS['good']:
            judgement = 'good'
            if min_delta < self.JUDGEMENT_WINDOWS['great']: judgement = 'great'
            if min_delta < self.JUDGEMENT_WINDOWS['perfect']: judgement = 'perfect'

            self.judgements[judgement] += 1
            self.score += self.SCORE_VALUES[judgement]
            self.combo += 1
            self.show_judgement(judgement)

            best_note_to_hit.is_hit = True
            if best_note_to_hit.is_hold:
                best_note_to_hit.is_holding = True
                best_note_to_hit.hold_start_time = self.current_game_time
                best_note_to_hit.hold_end_time = self.current_game_time + best_note_to_hit.duration
            else:
                best_note_to_hit.is_active = False

    def check_release(self, lane):
        for note in self.notes:
            if note.lane == lane and note.is_hold and note.is_holding:
                note.is_holding = False
                note.is_active = False

                # --- MODIFICATION: Calculate score based on hold duration ---
                # Calculate how long the note was actually held down
                held_duration = self.current_game_time - note.hold_start_time
                # The score is based on the shorter of actual hold time or the note's full duration
                actual_held_time = min(held_duration, note.duration)
                
                hold_score = actual_held_time * self.HOLD_SCORE_PER_MS
                self.score += int(hold_score)
                
                # Only award combo if the note was held for its full required duration
                if self.current_game_time >= note.hold_end_time:
                    self.combo += 1
                # --- END MODIFICATION ---
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
                # --- MODIFICATION: Score is based on the note's total duration ---
                hold_score = note.duration * self.HOLD_SCORE_PER_MS
                self.score += int(hold_score)
                # --- END MODIFICATION ---

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
        if self.background_image:
            self.screen.blit(self.background_image, (0, 0))
        else:
            self.screen.fill(BLACK)

        total_lanes_width = LANE_COUNT * LANE_WIDTH
        left_half_width = SCREEN_WIDTH / 2
        start_x = (left_half_width - total_lanes_width) / 2
        track_rect = pygame.Rect(start_x, 0, total_lanes_width, SCREEN_HEIGHT)
        
        track_overlay = pygame.Surface(track_rect.size, pygame.SRCALPHA)
        track_overlay.fill(DARK_GRAY)
        self.screen.blit(track_overlay, track_rect.topleft)

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
            alpha = max(0, 255 * (self.judgement_timer / 30.0))
            judgement_rect = render_text_with_shadow(self.screen, self.judgement_font, self.active_judgement_text, color, BLACK, 
                                                    alpha=alpha, center=(track_center_x, SCREEN_HEIGHT / 2 - 80))

        if self.combo > 2:
            y_pos = (judgement_rect.bottom + 40) if judgement_rect else (SCREEN_HEIGHT / 2)
            render_text_with_shadow(self.screen, self.judgement_font, str(self.combo), WHITE, BLACK, center=(track_center_x, y_pos))

        for i in range(LANE_COUNT):
            pad_rect = self.lane_geometry[i]['keypad_rect']
            sprite = self.note_sprites[0]['normal'] if self.key_press_feedback[i] > 0 else self.note_sprites[i]['normal']
            self.screen.blit(sprite, pad_rect)
            render_text_with_shadow(self.screen, self.key_label_font, KEY_LABELS[i], WHITE, BLACK, centerx=pad_rect.centerx, top=pad_rect.bottom + 10)

        stats_x = SCREEN_WIDTH / 2 + 50
        y_offset = 50
        notes_judged = sum(self.judgements.values())
        live_accuracy = ((sum(self.judgements[j] * self.ACCURACY_VALUES[j] for j in self.judgements) / notes_judged) * 100.0) if notes_judged > 0 else 100.0

        stats_to_draw = [f"Score: {self.score}", f"Accuracy: {live_accuracy:.2f}%", f"Max Combo: {self.max_combo}"]
        for text in stats_to_draw:
            render_text_with_shadow(self.screen, self.font, text, WHITE, BLACK, topleft=(stats_x, y_offset))
            y_offset += 35
        y_offset += 20

        for j, count in self.judgements.items():
            color = {'perfect': (255, 215, 0), 'great': (0, 255, 0), 'good': (0, 191, 255), 'miss': (255, 0, 0)}[j]
            render_text_with_shadow(self.screen, self.stats_font, f"{j.upper()}: {count}", color, BLACK, topleft=(stats_x, y_offset))
            y_offset += 30

        time_until_real_start = self.song_start_time - pygame.time.get_ticks()
        if time_until_real_start > 0:
            countdown_val = math.ceil(time_until_real_start / 1000)
            render_text_with_shadow(self.screen, self.countdown_font, str(countdown_val), WHITE, BLACK, center=(SCREEN_WIDTH / 4, SCREEN_HEIGHT / 2))
            
        if self.fade_in_duration > 0:
            elapsed = pygame.time.get_ticks() - self.fade_start_time
            if elapsed < self.fade_in_duration:
                progress = elapsed / self.fade_in_duration
                alpha = max(0, 255 * (1 - progress))
                fade_surface = pygame.Surface(self.screen.get_size()); fade_surface.fill(BLACK); fade_surface.set_alpha(alpha)
                self.screen.blit(fade_surface, (0, 0))
            else: self.fade_in_duration = 0

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
            if final_accuracy >= threshold: rank = r; break

        vinyl_surface = None
        END_SCREEN_VINYL_DIAMETER = 1200
        icon_path = os.path.join(self.song_data['folder_path'], "icon.png")
        if os.path.exists(icon_path):
            try:
                shadow_spread = 30
                full_diameter = END_SCREEN_VINYL_DIAMETER + shadow_spread * 2
                shadow = create_shadow_surface(END_SCREEN_VINYL_DIAMETER, spread=shadow_spread)
                vinyl_overlay = self._create_vinyl_overlay(END_SCREEN_VINYL_DIAMETER)
                loaded_icon = pygame.image.load(icon_path).convert_alpha()
                scaled_icon = pygame.transform.smoothscale(loaded_icon, (END_SCREEN_VINYL_DIAMETER, END_SCREEN_VINYL_DIAMETER))
                vinyl_art = pygame.Surface((END_SCREEN_VINYL_DIAMETER, END_SCREEN_VINYL_DIAMETER), pygame.SRCALPHA)
                pygame.draw.circle(vinyl_art, WHITE, vinyl_art.get_rect().center, END_SCREEN_VINYL_DIAMETER // 2)
                vinyl_art.blit(scaled_icon, (0, 0), special_flags=pygame.BLEND_RGBA_MIN)
                vinyl_art.blit(vinyl_overlay, (0, 0))
                vinyl_surface = pygame.Surface((full_diameter, full_diameter), pygame.SRCALPHA)
                vinyl_surface.blit(shadow, (0, 0))
                vinyl_surface.blit(vinyl_art, (shadow_spread, shadow_spread))
            except pygame.error as e: print(f"Error loading icon for end screen vinyl: {e}")

        rank_image = None
        script_dir = os.path.dirname(__file__)
        rank_image_path = os.path.join(script_dir, "assets", "ranks", f"rank_{rank}.png")
        if os.path.exists(rank_image_path):
            try:
                rank_image = pygame.image.load(rank_image_path).convert_alpha()
                rank_image = pygame.transform.scale(rank_image, (150, 150))
            except pygame.error as e: print(f"Error loading rank image {rank_image_path}: {e}")

        pulse_amplitude, pulse_speed, vinyl_rotation_angle = 10, 0.8, 0.0
        
        # --- MODIFICATION: Prepare variables for dynamic rank positioning ---
        miss_stat_rect = None
        continue_text_rect = None
        # --- END MODIFICATION ---

        waiting = True
        while waiting:
            for event in pygame.event.get():
                if event.type == pygame.QUIT or (event.type == pygame.KEYDOWN and event.key in [pygame.K_RETURN, pygame.K_ESCAPE]): waiting = False

            if self.background_image: self.screen.blit(self.background_image, (0,0))
            else: self.screen.fill(BLACK)
            overlay = pygame.Surface((SCREEN_WIDTH, SCREEN_HEIGHT), pygame.SRCALPHA); overlay.fill((0, 0, 0, 180)); self.screen.blit(overlay, (0, 0))
            
            if vinyl_surface:
                vinyl_rotation_angle = (vinyl_rotation_angle + 0.25) % 360
                current_pulse_offset = pulse_amplitude * math.sin(pygame.time.get_ticks() * pulse_speed / 100)
                size_val = int(vinyl_surface.get_width() + current_pulse_offset)
                pulsed_vinyl = pygame.transform.smoothscale(vinyl_surface, (size_val, size_val))
                rotated_pulsed_vinyl = pygame.transform.rotate(pulsed_vinyl, vinyl_rotation_angle)
                icon_rect = rotated_pulsed_vinyl.get_rect(center=(0, SCREEN_HEIGHT / 2))
                self.screen.blit(rotated_pulsed_vinyl, icon_rect)
            
            # Layout variables
            right_panel_center_x = SCREEN_WIDTH * 0.75
            y_offset = 40
            
            render_text_with_shadow(self.screen, self.font_song_title, self.song_data['title'], WHITE, BLACK, centerx=right_panel_center_x, top=y_offset)
            y_offset += 80

            stats_start_x = SCREEN_WIDTH / 2 + 50

            # Main stats (Score, Accuracy, Combo)
            stats_to_draw = [
                f"Score: {self.score}",
                f"Accuracy: {final_accuracy:.2f}%",
                f"Max Combo: {self.max_combo}"
            ]
            for text in stats_to_draw:
                render_text_with_shadow(self.screen, self.font, text, WHITE, BLACK, topleft=(stats_start_x, y_offset))
                y_offset += 35

            y_offset += 20

            # Detailed judgement counts
            for j, count in self.judgements.items():
                color = {'perfect': (255, 215, 0), 'great': (0, 255, 0), 'good': (0, 191, 255), 'miss': (255, 0, 0)}[j]
                rect = render_text_with_shadow(self.screen, self.stats_font, f"{j.upper()}: {count}", color, BLACK, topleft=(stats_start_x, y_offset))
                if j == 'miss':
                    miss_stat_rect = rect
                y_offset += 30
            
            # --- MODIFICATION: Dynamically position rank between miss stat and continue text ---
            continue_text_rect = render_text_with_shadow(self.screen, self.font, "Press Enter to Continue", WHITE, BLACK, centerx=right_panel_center_x, bottom=SCREEN_HEIGHT - 40)

            if miss_stat_rect and continue_text_rect:
                # Calculate the midpoint Y value
                midpoint_y = miss_stat_rect.bottom + (continue_text_rect.top - miss_stat_rect.bottom) / 2
                
                if rank_image:
                    rank_rect = rank_image.get_rect(centerx=right_panel_center_x, centery=midpoint_y)
                    self.screen.blit(rank_image, rank_rect)
                else:
                    render_text_with_shadow(self.screen, self.rank_font, rank, LANE_COLORS[0], BLACK, centerx=right_panel_center_x, centery=midpoint_y)
            # --- END MODIFICATION ---

            pygame.display.flip()
            self.clock.tick(FPS)

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
        self.background_image = load_and_blur_bg(self.song_info.get('background_path'))
        self.fade_in_duration = 0
        self.fade_start_time = 0
        
        try:
            if self.song_info.get('audio_path') and os.path.exists(self.song_info['audio_path']):
                pygame.mixer.music.load(self.song_info['audio_path']); pygame.mixer.music.set_volume(0.7); self.music_loaded = True
        except pygame.error as e: print(f"Could not load music for chart editor: {e}")
        self.recalculate_timing()

    def _create_highlight_sprites(self, base_sprites):
        return {lane_idx: {name: (sprite if name == 'hold_start_held' else self._apply_overlay(sprite)) for name, sprite in lane_sprites.items()} for lane_idx, lane_sprites in enumerate(base_sprites)}

    def _apply_overlay(self, sprite):
        highlight = sprite.copy()
        overlay = pygame.Surface(sprite.get_size(), pygame.SRCALPHA); overlay.fill((255, 255, 255, 120))
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
        track_width = LANE_WIDTH * LANE_COUNT
        surface = pygame.Surface((track_width, SCREEN_HEIGHT), pygame.SRCALPHA)
        tile_size = 30
        for y in range(0, SCREEN_HEIGHT, tile_size):
            for x in range(0, track_width, tile_size):
                color = CHECKER_COLOR_A if (x // tile_size + y // tile_size) % 2 == 0 else CHECKER_COLOR_B
                surface.fill(color, (x, y, tile_size, tile_size))
        return surface

    def run(self, fade_in_duration=0):
        if fade_in_duration > 0:
            self.fade_in_duration = fade_in_duration; self.fade_start_time = pygame.time.get_ticks()
            
        while self.is_running:
            dt = self.clock.tick(FPS)
            if self.music_playing: self.scroll_ms = self.playback_start_scroll_ms + (pygame.time.get_ticks() - self.playback_start_tick)
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
                elif self.music_loaded and event.key == pygame.K_r: pygame.mixer.music.stop(); self.scroll_ms = 0; self.music_playing = False
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
        if was_drag: self._handle_selection_drag()
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
            setattr(selected_item['obj'], selected_item['attr'], new_val); self.recalculate_timing()

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
        output_data = {"title": self.song_info['title'], "bpm": self.bpm, "speed": self.note_speed, "audio_file": os.path.basename(self.song_info.get('audio_path','')), "use_custom_start": self.use_custom_start, "start_offset_ms": self.custom_start_ms, "chart": self.new_chart}
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
        if self.background_image: self.screen.blit(self.background_image, (0, 0))
        else: self.screen.fill(BLACK)
        
        self.screen.blit(self.track_surface, (self.start_x, 0))
        
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
                progress = elapsed / self.fade_in_duration; alpha = max(0, 255 * (1 - progress))
                fade_surface = pygame.Surface(self.screen.get_size()); fade_surface.fill(BLACK); fade_surface.set_alpha(alpha)
                self.screen.blit(fade_surface, (0, 0))
            else: self.fade_in_duration = 0
            
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
        s = pygame.Surface(sel_rect_norm.size, pygame.SRCALPHA); s.fill((100, 100, 255, 60)); pygame.draw.rect(s, (150, 150, 255), s.get_rect(), 2)
        self.screen.blit(s, sel_rect_norm.topleft)

    def _draw_ui_text(self):
        lines = [ f"Time: {self.scroll_ms:.0f}ms | Selected: {len(self.selected_notes)}", "P: Play | R: Rewind | E: End", "Ctrl+C: Copy | Ctrl+V: Paste | Del: Delete", "Shift+Click: Hold Note" ]
        if self.use_custom_start: lines.append("S: Set Start Time")
        y_offset = 10
        if not self.music_loaded:
            render_text_with_shadow(self.screen, self.font_small, "No Audio File Loaded", RED, BLACK, topleft=(10, y_offset)); y_offset += 30
        for line in lines:
            render_text_with_shadow(self.screen, self.font_small, line, WHITE, BLACK, topleft=(10, y_offset)); y_offset += 30
        pygame.draw.rect(self.screen, RED, self.save_button_rect)
        render_text_with_shadow(self.screen, self.font_small, "Save Chart", WHITE, BLACK, center=self.save_button_rect.center)

    def draw_debug_menu(self):
        overlay = pygame.Surface((400, 300), pygame.SRCALPHA); overlay.fill((0, 0, 0, 180))
        y_offset = 20
        for i, item in enumerate(self.debug_menu_items):
            color = (255, 255, 0) if i == self.selected_menu_index else WHITE
            label = f"{item['label']}: "
            if item['type'] in ['float', 'int']: text = f"{label}{getattr(item['obj'], item['attr']):.1f}" if item['type'] == 'float' else f"{label}{int(getattr(item['obj'], item['attr']))}"
            elif item['type'] == 'bool': text = f"{label}[{'On' if getattr(item['obj'], item['attr']) else 'Off'}]"
            else: text = item['label']
            render_text_with_shadow(overlay, self.font_menu, text, color, BLACK, topleft=(20, y_offset)); y_offset += 35
        self.screen.blit(overlay, (SCREEN_WIDTH - 410, 10))


# --- App Class ---
class App:
    def __init__(self):
        pygame.init(); pygame.mixer.init()
        self.screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT))
        pygame.display.set_caption("Huergo Dance Revolution")
        self.clock = pygame.time.Clock()
        self.font_title = load_font(FONT_FILENAME, 60)
        self.font_menu = load_font(FONT_FILENAME, 42)
        self.root = tk.Tk(); self.root.withdraw()
        self.load_assets(); self.songs = self.load_songs()
        self.selected_song_index = 0
        self.menu_scroll_position = 0.0
        self.game_state = "MAIN_MENU"; self.menu_option = "PLAY"
        self.font_cache = {}
        self.menu_background = None
        self._update_menu_background(self.selected_song_index)
        self.next_game_state = None
        self.transition_start_time = 0
        self.ANIMATION_DURATION, self.CENTERING_PHASE_DURATION = 1200, 600
        self.BOUNCE_PHASE_DURATION = self.ANIMATION_DURATION - self.CENTERING_PHASE_DURATION
        self.FADE_IN_FROM_BLACK_DURATION = 500
        self.action_select_target = 0.0; self.action_select_lerp = 0.0
        self.VINYL_DIAMETER = 750; self.vinyl_rotation_angle = 0.0
        self.vinyl_overlay = self._create_vinyl_overlay(self.VINYL_DIAMETER)
        self.vinyl_current_surface, self.vinyl_target_surface = None, None
        self.is_vinyl_transitioning = False; self.vinyl_transition_progress = 1.0
        self._load_song_icon(self.selected_song_index, initial_load=True)

        # --- MODIFICATION: Add variables for song preview ---
        self.song_selection_time = 0
        self.is_preview_playing = False
        self.PREVIEW_DELAY_MS = 2000 # 2 seconds
        self.song_selection_time = pygame.time.get_ticks()
        # --- END MODIFICATION ---

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
                    with open(chart_path, 'r', encoding='utf-8') as f: song_data = json.load(f)
                    folder_path = os.path.join(songs_path, song_folder)
                    song_data['folder_path'] = folder_path
                    song_data['audio_path'] = self._get_audio_path(folder_path, song_data.get('audio_file', ''))
                    bg_path = os.path.join(folder_path, "bg.png")
                    song_data['background_path'] = bg_path if os.path.exists(bg_path) else None
                    songs.append(song_data)
                except (json.JSONDecodeError, KeyError) as e: print(f"Error loading {song_folder}: {e}")
        return songs if songs else [self.create_default_song()]

    def _get_audio_path(self, folder_path, audio_file):
        if not audio_file: return ""
        audio_path = os.path.join(folder_path, audio_file)
        if audio_file.lower().endswith('.mp3'):
            if not PYDUB_AVAILABLE: print(f"WARNING: pydub not found. Cannot play .mp3: {audio_file}"); return ""
            ogg_filename = os.path.splitext(audio_file)[0] + ".ogg"
            ogg_path = os.path.join(folder_path, ogg_filename)
            if not os.path.exists(ogg_path):
                try:
                    print(f"Converting {audio_file}..."); AudioSegment.from_mp3(audio_path).export(ogg_path, format="ogg")
                except Exception as e: print(f"ERROR: Could not convert MP3: {e}"); return ""
            return ogg_path
        return audio_path if os.path.exists(audio_path) else ""

    def create_default_song(self):
        print("No songs found. Creating a default song.")
        default_song_path = os.path.join(os.path.dirname(__file__), "songs", "default_song")
        os.makedirs(default_song_path, exist_ok=True)
        chart_data = {"title": "Default Song", "bpm": 120, "speed": 7, "audio_file": "", "chart": []}
        with open(os.path.join(default_song_path, "chart.json"), 'w') as f: json.dump(chart_data, f, indent=4)
        chart_data.update({'folder_path': default_song_path, 'audio_path': "", 'background_path': None})
        return chart_data

    def run(self):
        running = True
        while running:
            if self.game_state in ["MAIN_MENU", "ACTION_SELECT"]: running = self.run_main_menu()
            elif self.game_state == "TRANSITION_TO_GAME": running = self.run_transition_animation()
            elif self.game_state == "PLAYING":
                GameSession(self.screen, self.clock, self.songs[self.selected_song_index], self.note_sprites).run(fade_in_duration=self.FADE_IN_FROM_BLACK_DURATION)
                self.game_state = "MAIN_MENU"; self.action_select_target = 0.0
            elif self.game_state == "CHARTING":
                updated_song_data = ChartEditor(self.screen, self.clock, self.songs[self.selected_song_index].copy(), self.note_sprites).run(fade_in_duration=self.FADE_IN_FROM_BLACK_DURATION)
                if updated_song_data: self.songs[self.selected_song_index] = updated_song_data
                self.game_state = "MAIN_MENU"; self.action_select_target = 0.0; pygame.mixer.music.stop()
        pygame.quit()

    def run_main_menu(self):
        self.action_select_lerp += (self.action_select_target - self.action_select_lerp) * 0.08
        if self.is_vinyl_transitioning:
            self.vinyl_transition_progress += 0.05
            if self.vinyl_transition_progress >= 1.0:
                self.vinyl_transition_progress = 1.0; self.is_vinyl_transitioning = False
                self.vinyl_current_surface = self.vinyl_target_surface; self.vinyl_target_surface = None

        # --- MODIFICATION: Check for music preview ---
        current_ticks = pygame.time.get_ticks()
        if (self.game_state == "MAIN_MENU" and
            not self.is_preview_playing and
            self.selected_song_index < len(self.songs) and
            (current_ticks - self.song_selection_time > self.PREVIEW_DELAY_MS)):
            
            self.is_preview_playing = True
            song_data = self.songs[self.selected_song_index]
            audio_path = song_data.get('audio_path')
            
            if audio_path and os.path.exists(audio_path):
                try:
                    pygame.mixer.music.load(audio_path)
                    pygame.mixer.music.set_volume(0.5) # Set a reasonable preview volume
                    pygame.mixer.music.play(loops=-1) # Loop the preview
                except pygame.error as e:
                    print(f"Error playing preview for {audio_path}: {e}")
                    self.is_preview_playing = False # Reset on error
        # --- END MODIFICATION ---

        if self.game_state == "MAIN_MENU":
            num_items = len(self.songs) + 1; target_pos = float(self.selected_song_index); current_pos = self.menu_scroll_position
            distance = target_pos - current_pos
            if abs(distance) > num_items / 2:
                if distance > 0: current_pos += num_items
                else: target_pos += num_items
            self.menu_scroll_position = current_pos + (target_pos - current_pos) * 0.1
            if self.menu_scroll_position < 0: self.menu_scroll_position += num_items
            self.menu_scroll_position %= num_items
        for event in pygame.event.get():
            if event.type == pygame.QUIT or (event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE): return False
            if event.type == pygame.KEYDOWN: self._handle_menu_keypress(event.key)
        self.draw_main_menu(); self.clock.tick(FPS); return True

    def run_transition_animation(self):
        for event in pygame.event.get():
            if event.type == pygame.QUIT or (event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE): return False
        elapsed = pygame.time.get_ticks() - self.transition_start_time
        overall_progress = min(1.0, elapsed / self.ANIMATION_DURATION)
        centering_progress = min(1.0, elapsed / self.CENTERING_PHASE_DURATION)
        eased_centering_progress = 1 - pow(1 - centering_progress, 3)
        current_x = 0 + (SCREEN_WIDTH / 2 - 0) * eased_centering_progress
        current_y = SCREEN_HEIGHT / 2
        
        vinyl_base_size = self.vinyl_current_surface.get_width() if self.vinyl_current_surface else self.VINYL_DIAMETER
        current_size = vinyl_base_size

        if elapsed > self.CENTERING_PHASE_DURATION:
            bounce_progress = (elapsed - self.CENTERING_PHASE_DURATION) / self.BOUNCE_PHASE_DURATION
            n1, d1 = 7.5625, 2.75
            if bounce_progress < 1 / d1: scale_factor = n1 * bounce_progress * bounce_progress
            elif bounce_progress < 2 / d1: bounce_progress -= 1.5 / d1; scale_factor = n1 * bounce_progress * bounce_progress + 0.75
            elif bounce_progress < 2.5 / d1: bounce_progress -= 2.25 / d1; scale_factor = n1 * bounce_progress * bounce_progress + 0.9375
            else: bounce_progress -= 2.625 / d1; scale_factor = n1 * bounce_progress * bounce_progress + 0.984375
            current_scale = 1.0 - ((1.0 - 0.8) * scale_factor)
            current_size = int(vinyl_base_size * current_scale)

        if self.menu_background: self.screen.blit(self.menu_background, (0, 0))
        else: self.screen.fill(BLACK)
        
        if self.vinyl_current_surface and current_size > 1:
            self.vinyl_rotation_angle = (self.vinyl_rotation_angle + 0.5) % 360
            scaled_vinyl = pygame.transform.smoothscale(self.vinyl_current_surface, (current_size, current_size))
            rotated_vinyl = pygame.transform.rotate(scaled_vinyl, self.vinyl_rotation_angle)
            self.screen.blit(rotated_vinyl, rotated_vinyl.get_rect(center=(current_x, current_y)))
            
        pygame.display.flip(); self.clock.tick(FPS)
        if overall_progress >= 1.0: self.game_state = self.next_game_state; self.next_game_state = None
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
                    shadow_spread = 25
                    full_diameter = self.VINYL_DIAMETER + shadow_spread * 2
                    shadow = create_shadow_surface(self.VINYL_DIAMETER, spread=shadow_spread)
                    loaded_icon = pygame.image.load(icon_path).convert_alpha()
                    scaled_icon = pygame.transform.smoothscale(loaded_icon, (self.VINYL_DIAMETER, self.VINYL_DIAMETER))
                    vinyl_art = pygame.Surface((self.VINYL_DIAMETER, self.VINYL_DIAMETER), pygame.SRCALPHA)
                    pygame.draw.circle(vinyl_art, WHITE, vinyl_art.get_rect().center, self.VINYL_DIAMETER // 2)
                    vinyl_art.blit(scaled_icon, (0, 0), special_flags=pygame.BLEND_RGBA_MIN)
                    vinyl_art.blit(self.vinyl_overlay, (0, 0))
                    vinyl_surface = pygame.Surface((full_diameter, full_diameter), pygame.SRCALPHA)
                    vinyl_surface.blit(shadow, (0, 0))
                    vinyl_surface.blit(vinyl_art, (shadow_spread, shadow_spread))
                except pygame.error as e: print(f"Error loading icon for {song_data['title']}: {e}")
        if initial_load: self.vinyl_current_surface = vinyl_surface
        else: return vinyl_surface

    def _update_menu_background(self, index):
        path = self.songs[index].get('background_path') if index < len(self.songs) else None
        self.menu_background = load_and_blur_bg(path)

    def _start_vinyl_transition(self, new_index):
        self.is_vinyl_transitioning = True
        self.vinyl_transition_progress = 0.0
        self.vinyl_target_surface = self._load_song_icon(new_index)

    def _handle_menu_keypress(self, key):
        if self.game_state == "ACTION_SELECT":
            if key in [pygame.K_LEFT, pygame.K_RIGHT]: self.menu_option = "CHART" if self.menu_option == "PLAY" else "PLAY"
            elif key == pygame.K_RETURN:
                self.next_game_state = "PLAYING" if self.menu_option == "PLAY" else "CHARTING"
                self.game_state = "TRANSITION_TO_GAME"; self.transition_start_time = pygame.time.get_ticks()
            elif key == pygame.K_BACKSPACE: 
                self.game_state = "MAIN_MENU"; self.action_select_target = 0.0
                # --- MODIFICATION: Reset preview timer on backward navigation ---
                self.song_selection_time = pygame.time.get_ticks()
                # --- END MODIFICATION ---
        elif self.game_state == "MAIN_MENU":
            num_menu_items = len(self.songs) + 1; prev_index = self.selected_song_index
            if key == pygame.K_UP: self.selected_song_index = (self.selected_song_index - 1) % num_menu_items
            elif key == pygame.K_DOWN: self.selected_song_index = (self.selected_song_index + 1) % num_menu_items
            if prev_index != self.selected_song_index: 
                self._start_vinyl_transition(self.selected_song_index); self._update_menu_background(self.selected_song_index)
                # --- MODIFICATION: Stop music and reset timer on song change ---
                pygame.mixer.music.stop()
                self.is_preview_playing = False
                self.song_selection_time = pygame.time.get_ticks()
                # --- END MODIFICATION ---
            if key == pygame.K_RETURN:
                # --- MODIFICATION: Stop music when selecting an option ---
                pygame.mixer.music.stop()
                self.is_preview_playing = False
                # --- END MODIFICATION ---
                if self.selected_song_index < len(self.songs): self.game_state = "ACTION_SELECT"; self.action_select_target = 1.0
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
        chart_data = {"title": folder_name, "bpm": 120, "speed": 7, "audio_file": file_name, "chart": []}
        with open(os.path.join(new_song_path, "chart.json"), 'w') as f: json.dump(chart_data, f, indent=4)
        self.songs = self.load_songs()
        self.selected_song_index = next((i for i, s in enumerate(self.songs) if s['folder_path'] == new_song_path), 0)
        self.game_state = "CHARTING"; self.action_select_target = 0.0

    def draw_main_menu(self):
        if self.menu_background: self.screen.blit(self.menu_background, (0, 0))
        else: self.screen.fill(BLACK)
            
        self.vinyl_rotation_angle = (self.vinyl_rotation_angle + 0.25) % 360
        ease = 1 - pow(1 - self.action_select_lerp, 3)

        if self.vinyl_current_surface:
                vinyl_base_size = self.vinyl_current_surface.get_width()
                current_size = int(vinyl_base_size + (vinyl_base_size * 1.2 - vinyl_base_size) * ease)
        else:
                current_size = 0

        if self.is_vinyl_transitioning:
            eased_progress = 1 - (1 - self.vinyl_transition_progress) ** 2
            if self.vinyl_current_surface:
                trans_x = 0 + (0 - self.vinyl_current_surface.get_width() // 2 - 0) * eased_progress
                scaled = pygame.transform.smoothscale(self.vinyl_current_surface, (current_size, current_size))
                rotated = pygame.transform.rotate(scaled, self.vinyl_rotation_angle)
                self.screen.blit(rotated, rotated.get_rect(center=(trans_x, SCREEN_HEIGHT / 2)))
            if self.vinyl_target_surface:
                trans_x = 0 - self.vinyl_target_surface.get_width() // 2 + (0 - (0 - self.vinyl_target_surface.get_width() // 2)) * eased_progress
                scaled = pygame.transform.smoothscale(self.vinyl_target_surface, (current_size, current_size))
                rotated = pygame.transform.rotate(scaled, self.vinyl_rotation_angle)
                self.screen.blit(rotated, rotated.get_rect(center=(trans_x, SCREEN_HEIGHT / 2)))
        elif self.vinyl_current_surface:
            scaled = pygame.transform.smoothscale(self.vinyl_current_surface, (current_size, current_size))
            rotated = pygame.transform.rotate(scaled, self.vinyl_rotation_angle)
            self.screen.blit(rotated, rotated.get_rect(center=(0, SCREEN_HEIGHT / 2)))

        title_alpha = 255 * (1 - self.action_select_lerp)
        if title_alpha > 5:
            render_text_with_shadow(self.screen, self.font_title, "Huergo Dance Revolution", WHITE, BLACK, alpha=title_alpha, center=(SCREEN_WIDTH / 2, 50))

        list_alpha = 255 * (1 - self.action_select_lerp)
        if list_alpha > 5:
            menu_items = [f"{s['title']}" for s in self.songs] + ["Create New Chart..."]
            num_items = len(menu_items); center_y = SCREEN_HEIGHT / 2 + 20; num_visible = 2
            max_font, f_step, max_alpha, a_step, v_space, falloff = 42, 10, 255, 85, 50, 0.8
            y_pos = {0: center_y}; last_y, c_space = center_y, v_space
            for i in range(1, num_visible + 2): y_pos[i] = last_y + c_space; last_y = y_pos[i]; c_space *= falloff
            last_y, c_space = center_y, v_space
            for i in range(1, num_visible + 2): y_pos[-i] = last_y - c_space; last_y = y_pos[-i]; c_space *= falloff
            center_idx = round(self.menu_scroll_position)
            for i in range(-num_visible, num_visible + 1):
                item_idx = (center_idx + i) % num_items; dist = item_idx - self.menu_scroll_position
                if abs(dist) > num_items / 2: dist -= math.copysign(num_items, dist)
                if abs(dist) > num_visible + 0.5: continue
                font_size = max(12, int(max_font - abs(dist) * f_step)); alpha = max(0, int(max_alpha - abs(dist) * a_step))
                if font_size not in self.font_cache: self.font_cache[font_size] = load_font(FONT_FILENAME, font_size)
                font = self.font_cache[font_size]
                floor_d, ceil_d = math.floor(dist), math.ceil(dist)
                y = y_pos.get(floor_d, 0) if floor_d == ceil_d else y_pos.get(floor_d, 0) + (y_pos.get(ceil_d, 0) - y_pos.get(floor_d, 0)) * (dist - floor_d)
                render_text_with_shadow(self.screen, font, menu_items[item_idx], WHITE if item_idx == self.selected_song_index else GRAY, BLACK, alpha=alpha * (list_alpha / 255.0), center=(SCREEN_WIDTH / 2, y))

        ui_alpha = 255 * self.action_select_lerp
        if ui_alpha > 5:
            song = self.songs[self.selected_song_index]
            render_text_with_shadow(self.screen, self.font_title, song['title'], WHITE, BLACK, alpha=ui_alpha, center=(SCREEN_WIDTH * 0.75, 150))
            play_color = WHITE if self.menu_option == "PLAY" else GRAY
            chart_color = WHITE if self.menu_option == "CHART" else GRAY
            render_text_with_shadow(self.screen, self.font_menu, "Play", play_color, BLACK, alpha=ui_alpha, center=(SCREEN_WIDTH * 0.65, SCREEN_HEIGHT - 100))
            render_text_with_shadow(self.screen, self.font_menu, "Chart", chart_color, BLACK, alpha=ui_alpha, center=(SCREEN_WIDTH * 0.85, SCREEN_HEIGHT - 100))

        pygame.display.flip()

if __name__ == "__main__":
    app = App()
    app.run()
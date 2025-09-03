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
SCREEN_WIDTH = 1000
SCREEN_HEIGHT = 600
FPS = 60

# Colors
BLACK = (0, 0, 0); WHITE = (255, 255, 255); GRAY = (50, 50, 50); RED = (200, 0, 0)
CHECKER_COLOR_A = (40, 40, 40); CHECKER_COLOR_B = (55, 55, 55)
LANE_COLORS = [(0, 255, 255), (255, 0, 255), (255, 255, 0), (0, 255, 0)]

# Game settings
INITIAL_NOTE_SPEED = 7
LANE_COUNT = 4; LANE_WIDTH = 120; NOTE_WIDTH = 120
SPRITE_SIZES = {'normal': (NOTE_WIDTH, 30), 'hold_start': (NOTE_WIDTH, 20), 'hold_middle': (NOTE_WIDTH, 20), 'hold_end': (NOTE_WIDTH, 20)}
KEY_MAP = { pygame.K_s: 0, pygame.K_d: 1, pygame.K_j: 2, pygame.K_k: 3 }; KEY_LABELS = ['S', 'D', 'J', 'K']
PLAYHEAD_Y = SCREEN_HEIGHT - 100; HIT_TOLERANCE = 45

# --- Helper Functions (unchanged) ---
def create_placeholder_sprites():
    sprites = {}
    for name, size in SPRITE_SIZES.items():
        sprites[name] = pygame.Surface(size, pygame.SRCALPHA)
        if name in ['normal', 'hold_start', 'hold_end']: pygame.draw.rect(sprites[name], WHITE, sprites[name].get_rect(), border_radius=8)
        else: sprites[name].fill(WHITE)
    return sprites
def colorize_sprite(sprite, color):
    image = sprite.copy(); image.fill(color, special_flags=pygame.BLEND_RGBA_MULT); return image

# --- Note Class (unchanged) ---
class Note:
    def __init__(self, lane, speed, lane_geo, game_sprites, duration=None):
        self.lane, self.speed, self.y, self.is_active = lane, speed, 0.0, True; lane_sprites = game_sprites[self.lane]; self.is_hold = duration is not None
        if self.is_hold: self.start_img, self.middle_img, self.end_img, self.held_img = lane_sprites['hold_start'], lane_sprites['hold_middle'], lane_sprites['hold_end'], lane_sprites['hold_start_held']; self.image = self.start_img
        else: self.image = lane_sprites['normal']
        self.rect = self.image.get_rect(centerx=lane_geo[self.lane]['center_x'], centery=int(self.y)); self.duration = duration
        self.full_tail_length = (self.duration / (1000.0 / FPS)) * self.speed if self.is_hold else 0; self.is_hit = self.is_holding = False; self.hold_start_time = self.hold_end_time = None
    def update(self):
        if not (self.is_hold and self.is_holding): self.y += self.speed; self.rect.centery = int(self.y)
        if (self.is_hold and self.y - self.full_tail_length > SCREEN_HEIGHT) or (not self.is_hold and self.y > SCREEN_HEIGHT): self.is_active = False
    def draw(self, screen, current_game_time):
        if not self.is_hold: screen.blit(self.image, self.rect); return
        current_tail_length = self.full_tail_length
        if self.is_holding and self.hold_start_time is not None: elapsed = current_game_time - self.hold_start_time; remaining = max(0, self.duration - elapsed); current_tail_length = max(0, (remaining / (1000.0 / FPS)) * self.speed)
        if current_tail_length > 0:
            scaled_middle = pygame.transform.scale(self.middle_img, (self.rect.width, int(current_tail_length))); middle_rect = scaled_middle.get_rect(midbottom=self.rect.midtop); screen.blit(scaled_middle, middle_rect)
            end_rect = self.end_img.get_rect(midbottom=middle_rect.midtop); screen.blit(self.end_img, end_rect)
        head_image = self.held_img if self.is_holding else self.start_img; screen.blit(head_image, self.rect)

# --- REPLACE THE ENTIRE GameSession CLASS WITH THIS ---
# --- REPLACE THE ENTIRE GameSession CLASS WITH THIS ---
class GameSession:
    # --- Constants for accuracy, judgements, and ranks ---
    JUDGEMENT_WINDOWS = {'perfect': 22, 'great': 45, 'good': 90}
    ACCURACY_VALUES = {'perfect': 1.0, 'great': 0.7, 'good': 0.4, 'miss': 0.0}
    SCORE_VALUES = {'perfect': 100, 'great': 70, 'good': 40, 'miss': 0}
    RANK_THRESHOLDS = {'S': 95.0, 'A': 90.0, 'B': 85.0, 'C': 75.0, 'D': 50.0, 'F': 0.0}

    def __init__(self, screen, clock, song_data, sprites):
        self.screen, self.clock, self.song_data, self.note_sprites = screen, clock, song_data, sprites
        # --- MODIFIED: Added more fonts for the UI and end screen ---
        self.font = pygame.font.Font(None, 48); self.key_label_font = pygame.font.Font(None, 56)
        self.countdown_font = pygame.font.Font(None, 150)
        self.judgement_font = pygame.font.Font(None, 64)
        self.rank_font = pygame.font.Font(None, 200)
        self.stats_font = pygame.font.Font(None, 42)

        self.lane_geometry = self._calculate_lane_geometry()
        self.key_press_feedback = {i: 0 for i in range(LANE_COUNT)}
        self.is_running = True
        
        # --- NEW: Gameplay state variables ---
        self.reset_stats()

        self.countdown_duration = 3000
        self.session_init_time = 0
        self.song_start_time = 0
        self.music_started = False
        self.music_loaded = False
        self.chart_start_offset = 0
        self.scroll_time_ms = 0
        
    def reset_stats(self):
        # --- NEW: Helper function to initialize all stats ---
        self.score = 0
        self.combo = 0
        self.max_combo = 0
        self.judgements = {'perfect': 0, 'great': 0, 'good': 0, 'miss': 0}
        self.total_notes = len(self.song_data.get('chart', []))
        self.notes = []
        self.next_note_index = 0
        self.current_game_time = 0
        self.judgement_text = ""
        self.judgement_timer = 0
        self.judgement_color = WHITE

    def _calculate_lane_geometry(self):
        # (This method is unchanged)
        geo = {}; start_x = (SCREEN_WIDTH - (LANE_COUNT * LANE_WIDTH)) / 2
        for i in range(LANE_COUNT): center_x = start_x + (i * LANE_WIDTH) + LANE_WIDTH / 2; keypad_rect = self.note_sprites[i]['normal'].get_rect(center=(center_x, PLAYHEAD_Y)); geo[i] = {'keypad_rect': keypad_rect, 'center_x': center_x}
        return geo

    def run(self):
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
        # --- MODIFIED: Removed time check to allow hits before song starts ---
        for event in pygame.event.get():
            if event.type == pygame.QUIT: self.is_running = False
            if event.type == pygame.KEYDOWN:
                if event.key == pygame.K_ESCAPE: self.is_running = False
                if event.key in KEY_MAP:
                    lane = KEY_MAP[event.key]; self.key_press_feedback[lane] = 10; self.check_hit(lane)
            if event.type == pygame.KEYUP and event.key in KEY_MAP:
                self.check_release(KEY_MAP[event.key])

    def check_hit(self, lane):
        # --- MODIFIED: Removed line that caused hold notes to jump ---
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
                        # note.rect.centery = PLAYHEAD_Y # <--- THIS LINE WAS REMOVED
                    else:
                        note.is_active = False
                    return

    def check_release(self, lane):
        # (This method is unchanged)
        for note in self.notes:
            if note.lane == lane and note.is_hold and note.is_holding:
                note.is_holding = False; note.is_active = False
                if self.current_game_time >= note.hold_end_time: 
                    self.combo += 1
                    self.score += self.SCORE_VALUES['perfect']
                return

    def update(self):
        # (This method is unchanged)
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

    def draw(self):
        # --- MODIFIED: Removed time check for key press feedback ---
        self.screen.fill(BLACK)
        start_x = (SCREEN_WIDTH - (LANE_COUNT * LANE_WIDTH)) / 2
        track_rect = pygame.Rect(start_x, 0, LANE_WIDTH * LANE_COUNT, SCREEN_HEIGHT)
        pygame.draw.rect(self.screen, GRAY, track_rect)
        for i in range(LANE_COUNT + 1):
            line_x = start_x + i * LANE_WIDTH; pygame.draw.line(self.screen, BLACK, (line_x, 0), (line_x, SCREEN_HEIGHT), 2)
        for note in sorted(self.notes, key=lambda n: not n.is_hold):
            note.draw(self.screen, self.current_game_time)
        for i in range(LANE_COUNT):
            pad_rect = self.lane_geometry[i]['keypad_rect']
            # is_active_play = self.current_game_time >= self.chart_start_offset # <--- THIS LINE WAS REMOVED
            sprite = self.note_sprites[0]['normal'] if self.key_press_feedback[i] > 0 else self.note_sprites[i]['normal']
            self.screen.blit(sprite, pad_rect)
            text_surface = self.key_label_font.render(KEY_LABELS[i], True, WHITE)
            text_rect = text_surface.get_rect(centerx=pad_rect.centerx, top=pad_rect.bottom + 10)
            self.screen.blit(text_surface, text_rect)

        if self.current_game_time >= self.chart_start_offset:
            score_text = self.font.render(f"Score: {self.score}", True, WHITE)
            self.screen.blit(score_text, (10, 10))

        if self.judgement_timer > 0:
            judgement_surf = self.judgement_font.render(self.judgement_text, True, self.judgement_color)
            judgement_rect = judgement_surf.get_rect(center=(SCREEN_WIDTH / 2, SCREEN_HEIGHT / 2 - 50))
            self.screen.blit(judgement_surf, judgement_rect)
        
        if self.combo > 2:
            combo_text = self.judgement_font.render(f"{self.combo}", True, WHITE)
            combo_rect = combo_text.get_rect(center=(SCREEN_WIDTH / 2, SCREEN_HEIGHT / 2 + 20))
            self.screen.blit(combo_text, combo_rect)

        time_until_real_start = self.song_start_time - pygame.time.get_ticks()
        if time_until_real_start > 0:
            countdown_val = math.ceil(time_until_real_start / 1000)
            countdown_text = self.countdown_font.render(str(countdown_val), True, WHITE)
            text_rect = countdown_text.get_rect(center=(SCREEN_WIDTH / 2, SCREEN_HEIGHT / 2))
            self.screen.blit(countdown_text, text_rect)
        pygame.display.flip()
        
    def show_judgement(self, judgement):
        # (This method is unchanged)
        self.judgement_text = judgement.upper()
        self.judgement_timer = 30 
        colors = {'perfect': (255, 215, 0), 'great': (0, 255, 0), 'good': (0, 191, 255), 'miss': (255, 0, 0)}
        self.judgement_color = colors[judgement]
        
    def run_end_screen(self):
        # (This method is unchanged)
        if self.total_notes > 0:
            accuracy_score = sum(self.judgements[j] * self.ACCURACY_VALUES[j] for j in self.judgements)
            final_accuracy = (accuracy_score / self.total_notes) * 100
        else:
            final_accuracy = 100.0

        rank = 'F'
        for r, threshold in sorted(self.RANK_THRESHOLDS.items(), key=lambda item: item[1], reverse=True):
            if final_accuracy >= threshold:
                rank = r
                break
        
        song_icon = None
        icon_path = os.path.join(self.song_data['folder_path'], "icon.png")
        if os.path.exists(icon_path):
            try:
                loaded_icon = pygame.image.load(icon_path).convert_alpha()
                song_icon = pygame.transform.scale(loaded_icon, (350, 350))
                song_icon = self._round_corners(song_icon, 35)
            except pygame.error as e:
                print(f"Error loading icon.png: {e}")

        rank_image = None
        rank_image_path = os.path.join("assets", "ranks", f"rank_{rank}.png")
        if os.path.exists(rank_image_path):
            try:
                rank_image = pygame.image.load(rank_image_path).convert_alpha()
                rank_image = pygame.transform.scale(rank_image, (150, 150))
            except pygame.error as e:
                print(f"Error loading rank image {rank_image_path}: {e}")
                rank_image = None
        
        pulse_amplitude = 7
        pulse_speed = 0.8
        current_pulse_offset = 0
        
        waiting = True
        while waiting:
            for event in pygame.event.get():
                if event.type == pygame.QUIT: waiting = False
                if event.type == pygame.KEYDOWN:
                    if event.key in [pygame.K_RETURN, pygame.K_ESCAPE]:
                        waiting = False

            self.screen.fill(BLACK)
            overlay = pygame.Surface((SCREEN_WIDTH, SCREEN_HEIGHT), pygame.SRCALPHA)
            overlay.fill((0, 0, 0, 180))
            self.screen.blit(overlay, (0, 0))

            title_text = self.font.render("Results", True, WHITE)
            self.screen.blit(title_text, (SCREEN_WIDTH / 2 - title_text.get_width() / 2, 20))

            if song_icon:
                current_pulse_offset = pulse_amplitude * math.sin(pygame.time.get_ticks() * pulse_speed / 100)
                scaled_icon_width = song_icon.get_width() + current_pulse_offset
                scaled_icon_height = song_icon.get_height() + current_pulse_offset
                animated_icon = pygame.transform.scale(song_icon, (int(scaled_icon_width), int(scaled_icon_height)))
                icon_rect = animated_icon.get_rect(center=(SCREEN_WIDTH / 4, SCREEN_HEIGHT / 2))
                self.screen.blit(animated_icon, icon_rect)

            y_offset = 120
            block_start_x = SCREEN_WIDTH / 2 + 40
            rank_rect = None

            if rank_image:
                rank_rect = rank_image.get_rect(left=block_start_x, top=y_offset)
                self.screen.blit(rank_image, rank_rect)
            else:
                rank_text = self.rank_font.render(rank, True, LANE_COLORS[0])
                rank_rect = rank_text.get_rect(left=block_start_x, top=y_offset)
                self.screen.blit(rank_text, rank_rect)

            stats_x = rank_rect.right + 20
            stats_y_start = rank_rect.top + 20

            acc_text = self.stats_font.render(f"Accuracy: {final_accuracy:.2f}%", True, WHITE)
            self.screen.blit(acc_text, (stats_x, stats_y_start))
            
            score_text = self.stats_font.render(f"Score: {self.score}", True, WHITE)
            self.screen.blit(score_text, (stats_x, stats_y_start + 35))
            
            combo_text = self.stats_font.render(f"Max Combo: {self.max_combo}", True, WHITE)
            self.screen.blit(combo_text, (stats_x, stats_y_start + 70))
            
            y_offset = rank_rect.bottom + 30
            
            for i, (j, count) in enumerate(self.judgements.items()):
                color = {'perfect': (255, 215, 0), 'great': (0, 255, 0), 'good': (0, 191, 255), 'miss': (255, 0, 0)}[j]
                j_text = self.stats_font.render(f"{j.upper()}: {count}", True, color)
                self.screen.blit(j_text, (block_start_x, y_offset + i * 30))

            prompt_text = self.font.render("Press Enter to Continue", True, WHITE)
            self.screen.blit(prompt_text, (SCREEN_WIDTH / 2 - prompt_text.get_width() / 2, SCREEN_HEIGHT - 50))

            pygame.display.flip()
            self.clock.tick(FPS)
            
    def _round_corners(self, surface, radius):
        # (This method is unchanged)
        mask = pygame.Surface(surface.get_size(), pygame.SRCALPHA)
        pygame.draw.rect(mask, (255, 255, 255, 0), mask.get_rect())
        pygame.draw.rect(mask, (255, 255, 255, 255), mask.get_rect(), border_radius=radius)
        rounded_surface = pygame.Surface(surface.get_size(), pygame.SRCALPHA)
        rounded_surface.blit(surface, (0,0))
        rounded_surface.blit(mask, (0,0), special_flags=pygame.BLEND_RGBA_MULT)
        return rounded_surface# --- REPLACE THE ENTIRE ChartEditor CLASS WITH THIS ---
class ChartEditor:
    def __init__(self, screen, clock, song_info, sprites):
        self.screen, self.clock, self.song_info, self.note_sprites = screen, clock, song_info, sprites
        self.font_small = pygame.font.Font(None, 32); self.font_menu = pygame.font.Font(None, 36)
        self.new_chart = self.song_info.get('chart', [])
        self.is_running = True
        self.music_playing = False
        self.start_x = (SCREEN_WIDTH - (LANE_COUNT * LANE_WIDTH)) / 2
        
        # Load chart properties
        self.bpm = float(self.song_info.get('bpm', 120.0))
        self.note_speed = float(self.song_info.get('speed', INITIAL_NOTE_SPEED))
        self.scroll_ms = 0.0
        self.snap = 4

        # Custom start time properties
        self.use_custom_start = self.song_info.get('use_custom_start', False)
        self.custom_start_ms = self.song_info.get('start_offset_ms', 0)
        
        # Timing variables for accurate playback
        self.playback_start_tick = 0
        self.playback_start_scroll_ms = 0.0
        
        # --- NEW: Dictionary to track the start of hold notes ---
        self.hold_note_starts = {} # {lane: time_ms}
        
        self.track_surface = self.create_checkered_surface()
        self.save_button_rect = pygame.Rect(10, SCREEN_HEIGHT - 60, 150, 50)
        self.debug_menu_visible = False
        self.selected_menu_index = 0
        self.debug_menu_items = self.build_menu_items()
        
        self.music_loaded = False
        try:
            if self.song_info['audio_path'] and os.path.exists(self.song_info['audio_path']):
                pygame.mixer.music.load(self.song_info['audio_path']); pygame.mixer.music.set_volume(0.7); self.music_loaded = True
        except pygame.error as e: print(f"Could not load music for chart editor: {e}")
        
        self.recalculate_timing()

    def build_menu_items(self):
        # (This method is unchanged)
        return [
            {'label': 'BPM', 'type': 'float', 'obj': self, 'attr': 'bpm', 'step': 0.5, 'big_step': 5.0},
            {'label': 'Note Speed', 'type': 'float', 'obj': self, 'attr': 'note_speed', 'step': 0.1, 'big_step': 1.0},
            {'label': 'Custom Start', 'type': 'bool', 'obj': self, 'attr': 'use_custom_start'},
            {'label': 'Start Time (ms)', 'type': 'int', 'obj': self, 'attr': 'custom_start_ms', 'step': 100, 'big_step': 1000},
            {'label': 'Save Chart', 'type': 'action', 'action': self.save_chart},
            {'label': 'Reload Chart', 'type': 'action', 'action': self.reload_chart}
        ]
        
    def recalculate_timing(self):
        # (This method is unchanged)
        self.pixels_per_second = self.note_speed * FPS

    def create_checkered_surface(self):
        # (This method is unchanged)
        track_width = LANE_WIDTH * LANE_COUNT; surface = pygame.Surface((track_width, SCREEN_HEIGHT)); tile_size = 30
        for y in range(0, SCREEN_HEIGHT, tile_size):
            for x in range(0, track_width, tile_size): rect = pygame.Rect(x, y, tile_size, tile_size); color = CHECKER_COLOR_A if (x // tile_size + y // tile_size) % 2 == 0 else CHECKER_COLOR_B; surface.fill(color, rect)
        return surface

    def run(self):
        # (This method is unchanged)
        while self.is_running:
            dt = self.clock.tick(FPS)
            if self.music_playing:
                elapsed_time = pygame.time.get_ticks() - self.playback_start_tick
                self.scroll_ms = self.playback_start_scroll_ms + elapsed_time
            self.handle_events(); self.handle_continuous_input(dt); self.draw()
        return self.song_info

    def handle_events(self):
        for event in pygame.event.get():
            if event.type == pygame.QUIT: self.is_running = False
            if event.type == pygame.KEYDOWN:
                if event.key == pygame.K_7: self.debug_menu_visible = not self.debug_menu_visible; continue
                if self.debug_menu_visible: self.handle_menu_input(event.key); continue
                
                if event.key == pygame.K_s and self.use_custom_start:
                    self.custom_start_ms = self.scroll_ms
                    print(f"Custom start time set to: {self.custom_start_ms:.0f} ms")
                    continue

                if event.key == pygame.K_ESCAPE: 
                    # --- NEW: Clear pending holds on exit ---
                    if self.hold_note_starts: self.hold_note_starts.clear()
                    else: self.is_running = False
                if self.music_loaded:
                    if event.key == pygame.K_p:
                        if self.music_playing: pygame.mixer.music.pause()
                        else:
                            self.playback_start_tick = pygame.time.get_ticks(); self.playback_start_scroll_ms = self.scroll_ms
                            if not pygame.mixer.music.get_busy(): pygame.mixer.music.play(start=self.scroll_ms / 1000.0)
                            else: pygame.mixer.music.unpause()
                        self.music_playing = not self.music_playing
                    if event.key == pygame.K_r: pygame.mixer.music.stop(); self.scroll_ms = 0; self.music_playing = False
                if event.key in [pygame.K_1, pygame.K_2, pygame.K_4, pygame.K_8]: self.snap = int(pygame.key.name(event.key))
            if event.type == pygame.MOUSEBUTTONDOWN:
                if not self.debug_menu_visible:
                    if not self.music_playing:
                        if event.button == 4: self.scroll_ms = max(0, self.scroll_ms - 50)
                        if event.button == 5: self.scroll_ms += 50
                    if self.save_button_rect.collidepoint(event.pos): self.save_chart(); continue
                    
                    # --- NEW: Modified note placement logic ---
                    mx, my = event.pos
                    lane = self.get_lane_from_mouse(mx)
                    if lane is not None:
                        time_ms = self.get_time_from_mouse(my)
                        mods = pygame.key.get_mods()
                        is_shift = mods & pygame.KMOD_SHIFT

                        if event.button == 1: # Left Click
                            if is_shift:
                                self.handle_hold_note_placement(time_ms, lane)
                            else:
                                self.add_note(time_ms, lane)
                        if event.button == 3: # Right Click
                            self.remove_note(time_ms, lane)
    
    # --- NEW: Method to manage hold note creation ---
    def handle_hold_note_placement(self, time_ms, lane):
        if lane in self.hold_note_starts:
            # This is the second click, finish the note
            start_time = self.hold_note_starts.pop(lane)
            
            # Ensure start is before end
            if time_ms < start_time:
                start_time, time_ms = time_ms, start_time

            duration = time_ms - start_time
            if duration > 50: # Minimum duration
                self.add_note(start_time, lane, duration=duration)
        else:
            # This is the first click, start the note
            self.hold_note_starts[lane] = time_ms

    def handle_continuous_input(self, dt):
        # (This method is unchanged)
        if not self.debug_menu_visible and not self.music_playing:
            keys = pygame.key.get_pressed(); scroll_speed = 500 * (dt / 1000.0)
            if keys[pygame.K_UP]: self.scroll_ms = max(0, self.scroll_ms - scroll_speed)
            if keys[pygame.K_DOWN]: self.scroll_ms += scroll_speed

    def handle_menu_input(self, key):
        # (This method is unchanged)
        mods = pygame.key.get_mods(); is_shift = mods & pygame.KMOD_SHIFT
        selected_item = self.debug_menu_items[self.selected_menu_index]
        if key == pygame.K_UP: self.selected_menu_index = (self.selected_menu_index - 1) % len(self.debug_menu_items)
        elif key == pygame.K_DOWN: self.selected_menu_index = (self.selected_menu_index + 1) % len(self.debug_menu_items)
        elif key == pygame.K_RETURN and selected_item['type'] == 'action': selected_item['action']()
        elif selected_item['type'] == 'bool':
            if key in [pygame.K_LEFT, pygame.K_RIGHT, pygame.K_RETURN]:
                current_val = getattr(selected_item['obj'], selected_item['attr'])
                setattr(selected_item['obj'], selected_item['attr'], not current_val)
        elif selected_item['type'] in ['float', 'int']:
            step = selected_item.get('big_step', 1) if is_shift else selected_item.get('step', 1)
            current_val = getattr(selected_item['obj'], selected_item['attr'])
            if key == pygame.K_LEFT: setattr(selected_item['obj'], selected_item['attr'], current_val - step)
            elif key == pygame.K_RIGHT: setattr(selected_item['obj'], selected_item['attr'], current_val + step)
            if getattr(selected_item['obj'], selected_item['attr']) < 0:
                   setattr(selected_item['obj'], selected_item['attr'], 0)
            self.recalculate_timing()

    def get_lane_from_mouse(self, mx):
        # (This method is unchanged)
        if self.start_x <= mx < self.start_x + LANE_WIDTH * LANE_COUNT: return int((mx - self.start_x) // LANE_WIDTH)

    def get_time_from_mouse(self, my):
        # (This method is unchanged)
        pixel_offset = my - PLAYHEAD_Y; time_offset = (pixel_offset / self.pixels_per_second) * 1000; target_time = self.scroll_ms + time_offset; ms_per_beat = 60000.0 / self.bpm; ms_per_snap = ms_per_beat / self.snap
        return round(target_time / ms_per_snap) * ms_per_snap

    # --- NEW: add_note now accepts a duration ---
    def add_note(self, time_ms, lane, duration=None):
        # Check for duplicates
        if any(note['lane'] == lane and abs(note['time'] - time_ms) < 10 for note in self.new_chart): return
        
        note_data = {"time": max(0, time_ms), "lane": lane}
        if duration is not None:
            note_data["duration"] = duration
        
        self.new_chart.append(note_data)
        self.new_chart.sort(key=lambda x: x['time'])

    def remove_note(self, time_ms, lane):
        # (This method is unchanged)
        self.new_chart = [n for n in self.new_chart if not (n['lane'] == lane and abs(n['time'] - time_ms) < 20)]

    def save_chart(self):
        # (This method is unchanged)
        save_path = os.path.join(self.song_info['folder_path'], "chart.json")
        output_data = {
            "title": self.song_info['title'], "artist": self.song_info['artist'],
            "bpm": self.bpm, "speed": self.note_speed,
            "audio_file": os.path.basename(self.song_info.get('audio_path','')),
            "use_custom_start": self.use_custom_start,
            "start_offset_ms": self.custom_start_ms,
            "chart": self.new_chart
        }
        with open(save_path, 'w') as f: json.dump(output_data, f, indent=4)
        self.song_info.update(output_data)
        print(f"Chart saved to {save_path}")

    def reload_chart(self):
        # (This method is unchanged)
        chart_path = os.path.join(self.song_info['folder_path'], "chart.json")
        if os.path.exists(chart_path):
            with open(chart_path, 'r') as f:
                try:
                    reloaded_data = json.load(f)
                    self.new_chart = reloaded_data.get('chart', [])
                    self.bpm = float(reloaded_data.get('bpm', 120.0))
                    self.note_speed = float(reloaded_data.get('speed', INITIAL_NOTE_SPEED))
                    self.use_custom_start = reloaded_data.get('use_custom_start', False)
                    self.custom_start_ms = reloaded_data.get('start_offset_ms', 0)
                    self.recalculate_timing()
                    print("Chart reloaded from file.")
                except (json.JSONDecodeError, KeyError) as e: print(f"Error reloading chart: {e}")

    # --- REPLACE THIS METHOD IN YOUR ChartEditor CLASS ---
    def draw(self):
        self.screen.fill(BLACK); self.screen.blit(self.track_surface, (self.start_x, 0))
        ms_per_beat = 60000.0 / self.bpm; ms_per_snap = ms_per_beat / self.snap; start_time = max(0, int(self.scroll_ms - (PLAYHEAD_Y / self.pixels_per_second * 1000))); end_time = int(self.scroll_ms + ((SCREEN_HEIGHT - PLAYHEAD_Y) / self.pixels_per_second * 1000))
        for beat_time in range(int(start_time // ms_per_snap) * int(ms_per_snap), end_time, int(ms_per_snap)):
            y = PLAYHEAD_Y + ((beat_time - self.scroll_ms) / 1000.0) * self.pixels_per_second
            if 0 < y < SCREEN_HEIGHT: pygame.draw.line(self.screen, (70,70,70), (self.start_x, y), (self.start_x + LANE_WIDTH * LANE_COUNT, y), 1)
        
        for note in self.new_chart:
            y = PLAYHEAD_Y + ((note['time'] - self.scroll_ms) / 1000.0) * self.pixels_per_second
            if -50 < y < SCREEN_HEIGHT + 500:
                lane = note['lane']
                duration = note.get('duration')
                
                if duration: # It's a hold note
                    end_y = PLAYHEAD_Y + ((note['time'] + duration - self.scroll_ms) / 1000.0) * self.pixels_per_second
                    
                    middle_sprite = self.note_sprites[lane]['hold_middle']
                    tail_height = end_y - y
                    if tail_height > 0:
                        tail_rect = pygame.Rect(self.start_x + lane * LANE_WIDTH, y, NOTE_WIDTH, tail_height)
                        scaled_tail = pygame.transform.scale(middle_sprite, (tail_rect.width, int(tail_height)))
                        self.screen.blit(scaled_tail, tail_rect)

                    # Draw end cap (now uses 'hold_start' sprite)
                    end_sprite = self.note_sprites[lane]['hold_start'] # --- REVERSED ---
                    end_rect = end_sprite.get_rect(center=(self.start_x + (lane + 0.5) * LANE_WIDTH, end_y))
                    self.screen.blit(end_sprite, end_rect)
                    
                    # Draw start cap (now uses 'hold_end' sprite)
                    start_sprite = self.note_sprites[lane]['hold_end'] # --- REVERSED ---
                    rect = start_sprite.get_rect(center=(self.start_x + (lane + 0.5) * LANE_WIDTH, y))
                    self.screen.blit(start_sprite, rect)

                else: # It's a tap note
                    sprite = self.note_sprites[lane]['normal']
                    rect = sprite.get_rect(center=(self.start_x + (lane + 0.5) * LANE_WIDTH, y))
                    self.screen.blit(sprite, rect)
        
        mx, my = pygame.mouse.get_pos()
        for lane, start_time in self.hold_note_starts.items():
            start_y = PLAYHEAD_Y + ((start_time - self.scroll_ms) / 1000.0) * self.pixels_per_second
            
            # Draw a start marker (now uses 'hold_end' sprite for consistency)
            start_sprite = self.note_sprites[lane]['hold_end'] # --- REVERSED ---
            rect = start_sprite.get_rect(center=(self.start_x + (lane + 0.5) * LANE_WIDTH, start_y))
            self.screen.blit(start_sprite, rect)

            mouse_lane = self.get_lane_from_mouse(mx)
            if mouse_lane == lane:
                color = LANE_COLORS[lane]
                pygame.draw.line(self.screen, color, rect.center, (rect.centerx, my), 10)

        if self.use_custom_start:
            y = PLAYHEAD_Y + ((self.custom_start_ms - self.scroll_ms) / 1000.0) * self.pixels_per_second
            if 0 < y < SCREEN_HEIGHT:
                pygame.draw.line(self.screen, (0, 255, 0), (self.start_x, y), (self.start_x + LANE_WIDTH * LANE_COUNT, y), 3)

        pygame.draw.line(self.screen, WHITE, (self.start_x, PLAYHEAD_Y), (self.start_x + LANE_WIDTH * LANE_COUNT, PLAYHEAD_Y), 3)
        
        ui_text = [
            f"Time: {self.scroll_ms:.0f}ms", f"Snap: 1/{int(self.snap)}",
            "P: Play/Pause | R: Rewind | 7: Debug Menu",
            "Shift+Click: Start/End Hold Note",
            "S: Set Start Time" if self.use_custom_start else ""
        ]

        if not self.music_loaded: ui_text.insert(0, "No Audio File Loaded")
        for i, text in enumerate(ui_text):
            if not text: continue
            text_surf = self.font_small.render(text, True, RED if text.startswith("No Audio") else WHITE); self.screen.blit(text_surf, (10, 10 + i * 35))
        pygame.draw.rect(self.screen, RED, self.save_button_rect); save_text = self.font_small.render("Save Chart", True, WHITE)
        self.screen.blit(save_text, (self.save_button_rect.x + 20, self.save_button_rect.y + 15))
        if self.debug_menu_visible: self.draw_debug_menu()
        pygame.display.flip()

    def draw_debug_menu(self):
        # (This method is unchanged)
        overlay = pygame.Surface((400, 300), pygame.SRCALPHA); overlay.fill((0, 0, 0, 180)); x, y = SCREEN_WIDTH - 410, 10
        for i, item in enumerate(self.debug_menu_items):
            color = (255, 255, 0) if i == self.selected_menu_index else WHITE; label = item['label']
            if item['type'] in ['float', 'int']:
                value = getattr(item['obj'], item['attr'])
                text = f"{label}: {value:.1f}" if item['type'] == 'float' else f"{label}: {int(value)}"
            elif item['type'] == 'bool':
                value = getattr(item['obj'], item['attr'])
                status = "On" if value else "Off"
                text = f"{label}: [{status}]"
            else: text = label
            text_surf = self.font_menu.render(text, True, color); overlay.blit(text_surf, (20, 20 + i * 40))
        self.screen.blit(overlay, (x, y))

# --- CHANGE 2: App class now updates song data after charting ---
class App:
    def __init__(self):
        pygame.init(); pygame.mixer.init(); self.screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT)); pygame.display.set_caption("Python Rhythm Hero")
        self.clock = pygame.time.Clock(); self.font_title = pygame.font.Font(None, 74); self.font_menu = pygame.font.Font(None, 50)
        self.root = tk.Tk(); self.root.withdraw(); self.load_assets(); self.songs = self.load_songs()
        self.selected_song_index = 0; self.game_state = "MAIN_MENU"; self.menu_option = "PLAY"
    def load_assets(self):
        assets_path = os.path.join(os.path.dirname(__file__), "assets")
        sprite_filenames = {'normal': 'normal_note.png', 'hold_start': 'hold_start.png', 'hold_middle': 'hold_middle.png', 'hold_end': 'hold_end.png'}
        base_sprites = {}
        try:
            for name, filename in sprite_filenames.items(): image = pygame.image.load(os.path.join(assets_path, filename)).convert_alpha(); base_sprites[name] = pygame.transform.scale(image, SPRITE_SIZES[name])
        except FileNotFoundError: print("WARNING: Using placeholder graphics."); base_sprites = create_placeholder_sprites()
        self.note_sprites = []
        for color in LANE_COLORS: self.note_sprites.append({'normal': colorize_sprite(base_sprites['normal'], color), 'hold_start': colorize_sprite(base_sprites['hold_start'], color), 'hold_middle': colorize_sprite(base_sprites['hold_middle'], color), 'hold_end': colorize_sprite(base_sprites['hold_end'], color), 'hold_start_held': base_sprites['hold_start']})
    def load_songs(self):
        songs, songs_path = [], os.path.join(os.path.dirname(__file__), "songs")
        if not os.path.exists(songs_path): os.makedirs(songs_path)
        for song_folder in os.listdir(songs_path):
            chart_path = os.path.join(songs_path, song_folder, "chart.json")
            if os.path.exists(chart_path):
                with open(chart_path, 'r') as f:
                    try:
                        song_data = json.load(f); folder_path = os.path.join(songs_path, song_folder); song_data['folder_path'] = folder_path
                        audio_file = song_data.get('audio_file', ''); audio_path = os.path.join(folder_path, audio_file)
                        if audio_file.lower().endswith('.mp3'):
                            if PYDUB_AVAILABLE:
                                ogg_filename = os.path.splitext(audio_file)[0] + ".ogg"; ogg_path = os.path.join(folder_path, ogg_filename)
                                if not os.path.exists(ogg_path):
                                    try: print(f"Converting {audio_file}..."); sound = AudioSegment.from_mp3(audio_path); sound.export(ogg_path, format="ogg")
                                    except Exception as e: print(f"ERROR: Could not convert MP3: {e}"); audio_path = None
                                audio_path = ogg_path
                            else: print(f"WARNING: pydub not found. Cannot play .mp3: {audio_file}"); audio_path = None
                        song_data['audio_path'] = audio_path if audio_path and os.path.exists(audio_path) else ""; songs.append(song_data)
                    except (json.JSONDecodeError, KeyError) as e: print(f"Error loading {song_folder}: {e}")
        if not songs: return [self.create_default_song()]
        return songs
    def create_default_song(self):
        print("No songs found. Creating a default song..."); songs_dir = os.path.join(os.path.dirname(__file__), "songs"); default_song_path = os.path.join(songs_dir, "default_song")
        os.makedirs(default_song_path, exist_ok=True)
        chart_data = {"title": "Default Song", "artist": "Pygame", "bpm": 120, "speed": 7, "audio_file": "", "chart": []}
        with open(os.path.join(default_song_path, "chart.json"), 'w') as f: json.dump(chart_data, f, indent=4)
        chart_data['folder_path'] = default_song_path; chart_data['audio_path'] = ""
        return chart_data
    def run(self):
        running = True
        while running:
            if self.game_state in ["MAIN_MENU", "ACTION_SELECT"]:
                running = self.run_main_menu()
            elif self.game_state == "PLAYING":
                game = GameSession(self.screen, self.clock, self.songs[self.selected_song_index], self.note_sprites)
                game.run()
                self.game_state = "MAIN_MENU"
            elif self.game_state == "CHARTING":
                editor = ChartEditor(self.screen, self.clock, self.songs[self.selected_song_index].copy(), self.note_sprites)
                updated_song_data = editor.run() # Capture the returned data
                
                # Update the master list of songs with the new data
                if updated_song_data:
                    self.songs[self.selected_song_index] = updated_song_data
                    
                self.game_state = "MAIN_MENU"
                pygame.mixer.music.stop()
        pygame.quit()
    def run_main_menu(self):
        num_menu_items = len(self.songs) + 1
        for event in pygame.event.get():
            if event.type == pygame.QUIT: return False
            if event.type == pygame.KEYDOWN:
                if event.key == pygame.K_ESCAPE: return False
                if self.game_state == "ACTION_SELECT":
                    if event.key in [pygame.K_LEFT, pygame.K_RIGHT]: self.menu_option = "CHART" if self.menu_option == "PLAY" else "PLAY"
                    elif event.key == pygame.K_RETURN: self.game_state = "PLAYING" if self.menu_option == "PLAY" else "CHARTING"
                    elif event.key == pygame.K_BACKSPACE: self.game_state = "MAIN_MENU"
                elif self.game_state == "MAIN_MENU":
                    if event.key == pygame.K_UP: self.selected_song_index = (self.selected_song_index - 1) % num_menu_items
                    elif event.key == pygame.K_DOWN: self.selected_song_index = (self.selected_song_index + 1) % num_menu_items
                    elif event.key == pygame.K_RETURN:
                        if self.selected_song_index < len(self.songs): self.game_state = "ACTION_SELECT"
                        else: self.create_new_chart_session()
        self.draw_main_menu(); self.clock.tick(FPS); return True
    def create_new_chart_session(self):
        audio_path = filedialog.askopenfilename(title="Select an Audio File", filetypes=[("Audio Files", "*.mp3 *.ogg *.wav")]);
        if not audio_path: return
        songs_dir = os.path.join(os.path.dirname(__file__), "songs"); file_name = os.path.basename(audio_path)
        folder_name = os.path.splitext(file_name)[0]; new_song_path = os.path.join(songs_dir, folder_name)
        os.makedirs(new_song_path, exist_ok=True); shutil.copy(audio_path, new_song_path)
        chart_data = {"title": folder_name, "artist": "Unknown", "bpm": 120, "speed": 7, "audio_file": file_name, "chart": []}
        with open(os.path.join(new_song_path, "chart.json"), 'w') as f: json.dump(chart_data, f, indent=4)
        self.songs = self.load_songs() # Reload all songs
        for i, song in enumerate(self.songs):
            if song['folder_path'] == new_song_path: self.selected_song_index = i; break
        self.game_state = "CHARTING"
    def draw_main_menu(self):
        self.screen.fill(BLACK); title = self.font_title.render("Python Rhythm Hero", True, WHITE)
        self.screen.blit(title, (SCREEN_WIDTH/2 - title.get_width()/2, 50)); y_offset = 200
        for i, song in enumerate(self.songs):
            color = WHITE if i == self.selected_song_index else GRAY
            song_text = self.font_menu.render(f"{song['title']} - {song['artist']}", True, color)
            self.screen.blit(song_text, (SCREEN_WIDTH/2 - song_text.get_width()/2, y_offset + i * 60))
        create_color = WHITE if self.selected_song_index == len(self.songs) else GRAY
        create_text = self.font_menu.render("Create New Chart...", True, create_color)
        self.screen.blit(create_text, (SCREEN_WIDTH/2 - create_text.get_width()/2, y_offset + len(self.songs) * 60))
        if self.game_state == "ACTION_SELECT":
            play_text = self.font_menu.render("Play", True, WHITE if self.menu_option == "PLAY" else GRAY)
            chart_text = self.font_menu.render("Chart", True, WHITE if self.menu_option == "CHART" else GRAY)
            self.screen.blit(play_text, (SCREEN_WIDTH/2 - 150, 500)); self.screen.blit(chart_text, (SCREEN_WIDTH/2 + 50, 500))
        pygame.display.flip()

if __name__ == "__main__":
    app = App()
    app.run()
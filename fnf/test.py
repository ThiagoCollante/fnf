import pygame
import sys
import math

# --- Initialization ---
pygame.init()

# --- Screen Setup ---
infoObject = pygame.display.Info()
screen_width, screen_height = infoObject.current_w, infoObject.current_h
screen = pygame.display.set_mode((screen_width, screen_height), pygame.FULLSCREEN)
pygame.display.set_caption("Bouncing RGB DVD Logo")

# --- Load and Prepare the Logo ---
try:
    original_logo_img = pygame.image.load('dvd_logo.png').convert_alpha()
except pygame.error:
    print("Unable to load image 'dvd_logo.png'. Make sure it's in the correct directory.")
    sys.exit()

# Scale the logo to be smaller
logo_width, logo_height = original_logo_img.get_size()
# 👇 CHANGED THE DIVISOR FROM 4 TO 8 TO MAKE THE LOGO SMALLER 👇
if logo_width > screen_width / 8:
    new_width = screen_width / 8
    new_height = new_width * (logo_height / logo_width)
    original_logo_img = pygame.transform.scale(original_logo_img, (int(new_width), int(new_height)))

logo_rect = original_logo_img.get_rect()

# --- Create a 'white' version of the logo for consistent coloring ---
white_logo_base = pygame.Surface(original_logo_img.get_size(), pygame.SRCALPHA)
for x in range(original_logo_img.get_width()):
    for y in range(original_logo_img.get_height()):
        color = original_logo_img.get_at((x, y))
        if color.a > 0:
            white_logo_base.set_at((x, y), (255, 255, 255, color.a))

# --- Movement and Position (GUARANTEED CORNER HIT LOGIC) ---
travel_width = screen_width - logo_rect.width
travel_height = screen_height - logo_rect.height

# 👇 REVERTED THIS VALUE TO THE OLDER, SLOWER SPEED 👇
base_speed = 3

common_divisor = math.gcd(travel_width, travel_height)
speed_x = speed_y = base_speed * (common_divisor // base_speed)

if speed_x == 0:
    speed_x = speed_y = common_divisor if common_divisor > 0 else base_speed

logo_rect.x = speed_x * 50
logo_rect.y = speed_y * 30
logo_rect.x = logo_rect.x % travel_width
logo_rect.y = logo_rect.y % travel_height

# --- RGB Color Cycling Variables ---
current_hue = 0.0
color_speed = 0.5

# --- Clock and Background ---
bg_color = pygame.Color('black')
clock = pygame.time.Clock()

# HSL to RGB function
def hsl_to_rgb(h, s, l):
    c = (1 - abs(2 * l - 1)) * s; x = c * (1 - abs((h / 60) % 2 - 1)); m = l - c/2
    r, g, b = 0, 0, 0
    if 0 <= h < 60: r,g,b = c,x,0
    elif 60 <= h < 120: r,g,b = x,c,0
    elif 120 <= h < 180: r,g,b = 0,c,x
    elif 180 <= h < 240: r,g,b = 0,x,c
    elif 240 <= h < 300: r,g,b = x,0,c
    elif 300 <= h < 360: r,g,b = c,0,x
    return int((r+m)*255), int((g+m)*255), int((b+m)*255)

# --- Main Game Loop ---
running = True
while running:
    for event in pygame.event.get():
        if event.type == pygame.QUIT: running = False
        if event.type == pygame.KEYDOWN:
            if event.key == pygame.K_ESCAPE: running = False

    logo_rect.x += speed_x
    logo_rect.y += speed_y

    if logo_rect.left <= 0 or logo_rect.right >= screen_width: speed_x *= -1
    if logo_rect.top <= 0 or logo_rect.bottom >= screen_height: speed_y *= -1

    current_hue = (current_hue + color_speed) % 360
    current_rgb = hsl_to_rgb(current_hue, 1.0, 0.5)

    colored_logo_img = white_logo_base.copy()
    colored_logo_img.fill(current_rgb, special_flags=pygame.BLEND_MULT)

    screen.fill(bg_color)
    screen.blit(colored_logo_img, logo_rect)
    pygame.display.flip()

    clock.tick(60)

pygame.quit()
sys.exit()
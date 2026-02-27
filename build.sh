#!/bin/bash
set -e

echo "→ Setting up build venv..."
python3 -m venv .build-venv
source .build-venv/bin/activate
pip install -q flask rumps pyinstaller

echo "→ Downloading yt-dlp (universal macOS)..."
mkdir -p bin
curl -L https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp_macos \
     -o bin/yt-dlp && chmod +x bin/yt-dlp

echo "→ Downloading ffmpeg (universal macOS)..."
curl -L "https://evermeet.cx/ffmpeg/getrelease/ffmpeg/zip" -o /tmp/ffmpeg.zip
unzip -o /tmp/ffmpeg.zip ffmpeg -d bin/
chmod +x bin/ffmpeg

echo "→ Building .app..."
.build-venv/bin/pyinstaller downloads.spec --noconfirm

echo "→ Zipping..."
cd dist && zip -r "../+downloads.zip" "+downloads.app" && cd ..

echo "✓ Done → +downloads.zip (~50MB)"
echo "Upload with: scp +downloads.zip root@157.245.117.102:/var/www/html/"

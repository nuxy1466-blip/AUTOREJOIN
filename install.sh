#!/bin/sh
# STAR AUTOREJOIN installer (Termux)
REPO="nuxy1466-blip/AUTOREJOIN"
TAG="V5.0"
FILE="Star_v5-5-3.py"
DEST="$HOME/$FILE"
TMP="$HOME/.star_dl.tmp"

say() { printf '\033[1;36m[*]\033[0m %s\n' "$1"; }
bad() { printf '\033[1;31m[x]\033[0m %s\n' "$1"; rm -f "$TMP"; exit 1; }

say "ติดตั้งแพ็กเกจที่ต้องใช้..."
command -v python >/dev/null 2>&1 && command -v curl >/dev/null 2>&1 || {
  pkg update -y >/dev/null 2>&1
  pkg install -y python curl || bad "pkg install ไม่สำเร็จ (ลอง pkg update แล้วรันใหม่)"
}
python -c "import requests" >/dev/null 2>&1 || pip install requests || bad "pip install requests ไม่สำเร็จ"

say "ดาวน์โหลด $FILE ..."
ok=0
for url in \
  "https://github.com/$REPO/releases/download/$TAG/$FILE" \
  "https://github.com/$REPO/releases/latest/download/$FILE"; do
  if curl -fL --retry 3 --connect-timeout 15 -o "$TMP" "$url" 2>/dev/null && [ -s "$TMP" ]; then
    ok=1; break
  fi
done
[ "$ok" = 1 ] || bad "โหลดไม่ได้ — เช็กว่าอัปโหลด $FILE ใน Release แล้ว และแท็กคือ $TAG"
python -m py_compile "$TMP" 2>/dev/null || bad "ไฟล์ที่โหลดมาไม่ใช่ Python ที่ถูกต้อง"

mv -f "$TMP" "$DEST"
rm -rf "$HOME/__pycache__" 2>/dev/null

# สร้างคำสั่งลัด: พิมพ์ star เพื่อรัน
LAUNCH="${PREFIX:-/data/data/com.termux/files/usr}/bin/star"
printf '#!/bin/sh\nexec python "%s" "$@"\n' "$DEST" > "$LAUNCH" && chmod +x "$LAUNCH"

say "ติดตั้งเสร็จ → $DEST"
say "ครั้งต่อไปพิมพ์ star เพื่อรัน (อัปเดต: รันคำสั่งติดตั้งซ้ำ)"

[ "$NOSTART" = 1 ] && exit 0
# รันผ่าน curl | sh แล้ว stdin เป็นท่อ → ต้องผูกกับ /dev/tty ไม่งั้นพิมพ์ในเมนูไม่ได้
if [ -r /dev/tty ]; then exec python "$DEST" < /dev/tty; else exec python "$DEST"; fi

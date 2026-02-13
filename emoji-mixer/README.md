# Samurai Emoji Debugger

Alat profesional untuk pembuatan custom emoji dan pengujian stabilitas Unicode pada game.

## Fitur Utama
- **Custom Emoji Builder (ZWJ)**: Gabungkan berbagai emoji menggunakan Zero Width Joiner untuk membuat kombinasi baru (misal: 🦹‍♂️ kustom).
- **Bug / Stress Test Generator**: Hasilkan urutan Unicode kompleks untuk menguji parser dan layout engine game:
  - **ZWJ Flooding**: Menguji performa render layout.
  - **BiDi Overrides**: Menguji penanganan arah teks (RTL/LTR).
  - **Lone Surrogates**: Menguji ketahanan parser terhadap urutan UTF-16 yang tidak valid.
  - **Variation Selector Flood**: Menguji batas memori/buffer render.
- **Fancy Fonts**: Transformasi teks ke berbagai gaya Unicode (Bold, Script, Fraktur).
- **Salin Kode**: Satu klik untuk menyalin hasil pengujian ke clipboard.

## Teknologi
- Next.js 15
- Tailwind CSS v4
- Sawarabi Mincho Font

## Cara Menjalankan Lokal
1. Masuk ke direktori: `cd emoji-mixer`
2. Install dependensi: `npm install`
3. Jalankan server dev: `npm run dev`

## Deployment ke Vercel
Jalankan `vercel` di dalam folder `emoji-mixer` atau atur Root Directory ke `emoji-mixer` pada dashboard Vercel.

# Panduan Pemindaian Signature Otomatis

Script `Signature_Scanner_Automated.lua` dirancang untuk membantu Anda menemukan alamat memori yang penting (seperti flag anti-cheat atau fungsi game) secara otomatis menggunakan "Signature" atau "Array of Bytes" (AOB).

## 1. Apa itu Signature?

Signature adalah pola unik dari angka atau byte di dalam memori yang tidak berubah meskipun alamat memorinya berubah (misalnya setelah update game atau restart).

Contoh Signature (Hex): `h 00 00 A0 E3 1E FF 2F E1`

## 2. Cara Menemukan Signature Sendiri

Untuk membuat bypass yang stabil, Anda harus menemukan pola unik:
1. Cari nilai yang ingin Anda ubah di Game Guardian (misalnya HP atau Flag Deteksi).
2. Lihat alamat di sekitar nilai tersebut (Memory Viewer).
3. Ambil beberapa byte sebelum dan sesudah nilai tersebut.
4. Tes pola tersebut menggunakan fitur "Search" di GG untuk memastikan pola tersebut hanya menghasilkan 1 atau sedikit hasil.

## 3. Cara Mengedit Script

Buka file `Signature_Scanner_Automated.lua` dan temukan bagian `SIGNATURE_LIBRARY`. Anda bisa menambahkan pola Anda sendiri di sana:

```lua
local SIGNATURE_LIBRARY = {
  {
    name = "My Custom Bypass",
    pattern = "h 12 34 56 78", -- Pola hex Anda
    type = gg.TYPE_DWORD,
    region = gg.REGION_CODE_APP
  },
}
```

## 4. Menggunakan Fitur Code Generator

Setelah script menemukan alamat yang cocok dengan pola Anda:
1. Pilih menu "Salin Kode Snippet".
2. Script akan otomatis membuat kode Lua yang siap digunakan di script bypass Anda yang lain.
3. Kode tersebut akan berisi perintah `gg.setValues` untuk mengubah nilai pada alamat yang baru saja ditemukan.

## 5. Tips Keamanan (Anti-Banned)

- **Gunakan Group Search:** Gunakan pola seperti `100;200;300::17` untuk mencari beberapa nilai yang berdekatan. Ini jauh lebih akurat daripada mencari satu nilai saja.
- **Pilih Region yang Tepat:** Jika kode berada di library native, gunakan `REGION_CODE_APP`. Jika di Java Heap, gunakan `REGION_JAVA_HEAP`.
- **Cek Manual:** Selalu verifikasi hasil scan otomatis Anda secara manual di Memory Viewer sebelum melakukan perubahan besar.

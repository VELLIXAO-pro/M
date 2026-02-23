# Samurai GG Tools

Kumpulan skrip dan alat untuk Game Guardian, AndLua+, dan Frida.

## Apa itu AGG (AndLua+ Game Guardian)?

**AGG** merujuk pada integrasi antara **AndLua+** dan **Game Guardian**. Ini memungkinkan pengembang untuk membuat **Mod Menu** melayang (floating menu) dengan antarmuka yang lebih modern dan fungsional dibandingkan menu standar Game Guardian.

### Fitur Utama:
- **Custom UI**: Membuat floating icon dan menu menggunakan layout `.aly` AndLua+.
- **Script Integration**: Menjalankan fungsi Game Guardian (`gg.*`) dari aplikasi AndLua+.
- **Automated Cheats**: Memudahkan implementasi fitur seperti "Auto Search" atau "Group Search".

## Alat yang Tersedia

### 1. Frida Memory Kernel (`AggFridaKernel.js`)
Skrip Frida untuk memantau memori di `dalvik-main` (Java Heap). Berguna untuk mendeteksi perubahan nilai memori saat pemain melakukan aksi di dalam game.

**Fitur:**
- Otomatis mendeteksi rentang memori `dalvik-main`.
- Mendeteksi tipe data (DWORD, FLOAT, Pointer) secara otomatis.
- Hook pada event UI (Click, Text Change) untuk menampilkan log memori secara real-time.
- Mendukung `rpc.exports` untuk dikontrol dari luar.

**Cara Pakai:**
```bash
frida -U -f com.target.game -l AggFridaKernel.js
```
Gunakan `rpc.exports.addWatch("0x12345678")` di konsol Frida untuk mulai memantau alamat.

### 2. Java Native Pointer Analyzer (`Pointer.lua`)
Skrip Game Guardian untuk menganalisis struktur memori dan rantai pointer pada game berbasis Java Native (JNI).

### 3. Telegram GG Controller (`TelegramGG.lua`)
Memungkinkan pengendalian Game Guardian secara jarak jauh melalui Telegram Bot API.

### 4. AndLua+ Injector Framework (`AndLua_Injector/`)
Framework dasar untuk membuat injector aplikasi AndLua+ yang dapat memanipulasi memori aplikasi lain di perangkat non-root (debuggable).

---
*Created by Jules for the AGG Community*

# Panduan Analisis Memori Game Guardian

Dokumen ini menjelaskan konsep dasar pemetaan memori Android dan cara menggunakan API Game Guardian untuk melakukan analisis data yang stabil.

## 1. Memahami Region Memori Android

Saat melakukan analisis memori dengan Game Guardian, penting untuk memilih region yang tepat agar pencarian lebih efisien dan akurat.

- **Java Heap (Jh):** Berisi objek-objek yang dikelola oleh runtime Java (ART/Dalvik). Ini adalah tempat utama untuk data game yang ditulis dalam Java.
- **Java (J):** Region memori lain yang terkait dengan eksekusi Java.
- **C++ Heap (Ch):** Berisi alokasi memori dari kode native (C/C++). Banyak game berat menggunakan region ini untuk performa tinggi.
- **Anonymous (A):** Region memori yang tidak memiliki nama file terkait. Sering digunakan untuk alokasi dinamis besar, cache, atau data yang bersifat sementara.
- **Code App (Xa):** Berisi kode biner aplikasi. Biasanya bersifat *read-only*.

## 2. Menggunakan API Game Guardian untuk Pelacakan Data

Untuk memantau perubahan data secara real-time, kita dapat menggunakan kombinasi fungsi `gg.getResults` dan `gg.getValues`.

### Mendapatkan Hasil Pencarian
```lua
-- Mengambil 100 hasil pertama dari daftar hasil saat ini
local results = gg.getResults(100)
```

### Membaca Nilai Terbaru
```lua
-- Memperbarui nilai dalam tabel results dengan data terbaru dari memori
results = gg.getValues(results)

for i, v in ipairs(results) do
  print("Alamat: " .. v.address .. " | Nilai: " .. v.value)
end
```

## 3. Praktik Terbaik Pemrograman Modular di Lua

Agar script Anda mudah dikelola dan dikembangkan, gunakan pendekatan modular:

1.  **Gunakan Tabel Konfigurasi:** Simpan semua konstanta dalam satu tabel di awal script.
2.  **Fungsi yang Terfokus:** Buat fungsi kecil yang hanya melakukan satu tugas (misalnya, hanya untuk format teks atau hanya untuk membaca memori).
3.  **Pemisahan Logika UI dan Data:** Pisahkan fungsi yang menampilkan menu (`gg.choice`) dari fungsi yang melakukan pemrosesan data.

## 4. Cara Menggunakan Template Analisis

Template `Memory_Analysis_Template.lua` yang disertakan menyediakan kerangka kerja dasar untuk:
1.  Memilih region memori yang ingin difokuskan.
2.  Menganalisis dan menampilkan ringkasan nilai dari hasil pencarian.
3.  Memantau perubahan nilai pada alamat tertentu secara terus-menerus (Monitoring).

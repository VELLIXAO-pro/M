# Analisis Lanjutan Java Heap (dalvik-main)

Dokumen ini ditujukan untuk analisis memori pada region `dalvik-main` (Java Heap) ketika tidak ada metadata biner atau library native yang dapat dijadikan acuan.

## 1. Karakteristik Java Heap Tanpa Metadata

Pada game yang sepenuhnya berjalan di Java Heap, data disimpan sebagai objek-objek ART (Android Runtime).
- **Tanpa Simbol:** Anda tidak akan menemukan nama fungsi atau variabel.
- **Dinamis:** Alamat memori berubah setiap kali Garbage Collector (GC) berjalan.
- **Struktur Objek:** Objek Java memiliki header (biasanya berisi *Class Pointer* dan *Lock Word*).

## 2. Teknik Pencarian Tanpa Metadata (Reconnaissance)

### A. Mencari Objek Melalui Penyelarasan (Alignment)
Objek di Java Heap selalu selaras dengan kelipatan 4 atau 8 byte. Jika Anda menemukan nilai yang tampak seperti alamat memori (0x10000 - 0x7FFFFFFF) pada alamat yang selaras, itu kemungkinan besar adalah *Class Pointer*.

### B. Analisis Perilaku Nilai (Value Behavior Analysis)
Karena Anda tidak memiliki metadata, satu-satunya cara mengidentifikasi kegunaan alamat memori adalah dengan memantau perubahannya:
1. Cari nilai yang berubah saat Anda melakukan aksi tertentu di game (misalnya, saat anti-cheat memindai memori).
2. Gunakan fitur **Snapshot** untuk membandingkan keadaan memori "Sebelum Terdeteksi" dan "Sesudah Terdeteksi".

### C. Melacak Rantai Pointer (Pointer Chasing)
Untuk mendapatkan akses yang stabil ke objek di Java Heap, Anda harus menemukan "Static Root" atau rantai pointer yang mengarah ke objek target.
- Gunakan `Java_Heap_Recon.lua` untuk melacak level pointer secara otomatis.

## 3. Strategi Menemukan Flag Anti-Cheat

Anti-cheat berbasis Java sering kali menyimpan status deteksi dalam variabel boolean atau integer sederhana di dalam objek "SecurityManager" atau "Validator".

1. **Identifikasi Objek Keamanan:** Cari objek yang selalu aktif di latar belakang (nilai yang diperbarui secara periodik).
2. **Ubah Status Deteksi:** Jika Anda menemukan alamat yang berubah dari `0` menjadi `1` tepat sebelum banned, itu adalah flag deteksi.
3. **Freeze atau Patch:** Gunakan Game Guardian untuk membekukan nilai tersebut kembali ke `0` untuk mencegah sistem mengirim laporan banned ke server.

## 4. Cara Menggunakan Java Heap Recon Script

1. Lakukan pencarian awal untuk nilai yang Anda curigai.
2. Tambahkan alamat tersebut ke daftar hasil.
3. Jalankan `Java_Heap_Recon.lua`.
4. Gunakan **Scan Headers** untuk melihat struktur objek di sekitar alamat tersebut.
5. Gunakan **Trace Pointer** untuk melihat apakah alamat tersebut adalah bagian dari struktur yang lebih besar.

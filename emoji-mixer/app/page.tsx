"use client";

import { useState, useEffect } from "react";
import { convertToFancy, decorateText, mixEmojis, fancyStyles } from "@/lib/emoji-logic";

export default function Home() {
  const [text, setText] = useState("");
  const [emoji1, setEmoji1] = useState("🔥");
  const [emoji2, setEmoji2] = useState("✨");
  const [mode, setMode] = useState<"none" | "interleave" | "wrap" | "border" | "mix">("interleave");
  const [style, setStyle] = useState<keyof typeof fancyStyles | "normal">("normal");
  const [result, setResult] = useState("");

  useEffect(() => {
    let processed = text;

    if (style !== "normal") {
      processed = convertToFancy(processed, style);
    }

    if (mode === "interleave" || mode === "wrap" || mode === "border") {
      processed = decorateText(processed, emoji1, mode as any);
    } else if (mode === "mix") {
      processed = mixEmojis(processed, emoji1, emoji2);
    }

    setResult(processed);
  }, [text, emoji1, emoji2, mode, style]);

  const copyToClipboard = () => {
    if (!result) return;
    navigator.clipboard.writeText(result);
    alert("Teks berhasil disalin!");
  };

  return (
    <main className="min-h-screen bg-background text-foreground p-4 md:p-8 flex flex-col items-center">
      <header className="mb-8 text-center">
        <h1 className="text-4xl md:text-6xl font-bold text-crimson mb-2 tracking-widest uppercase">
          Samurai Emoji Mixer
        </h1>
        <p className="text-gold opacity-80">Buat teks kustom dengan sentuhan emoji</p>
      </header>

      <div className="w-full max-w-2xl bg-white/5 border border-gold/20 rounded-xl p-6 shadow-2xl backdrop-blur-sm">
        {/* Input Teks */}
        <div className="mb-6">
          <label htmlFor="input-text" className="block text-gold text-sm font-semibold mb-2 uppercase tracking-wider">Masukkan Teks</label>
          <textarea
            id="input-text"
            className="w-full bg-black/50 border border-crimson/30 rounded-lg p-3 text-white focus:outline-none focus:border-crimson transition-colors"
            placeholder="Tulis sesuatu di sini..."
            rows={3}
            value={text}
            onChange={(e) => setText(e.target.value)}
          />
        </div>

        {/* Emoji & Gaya */}
        <div className="grid grid-cols-1 md:grid-cols-2 gap-6 mb-6">
          <div>
            <label htmlFor="custom-emoji" className="block text-gold text-sm font-semibold mb-2 uppercase tracking-wider">Pilih Emoji</label>
            <div className="flex flex-wrap gap-2 mb-2">
              {["🔥", "✨", "🌸", "👹", "⚔️", "🏮", "💎", "👑"].map((e) => (
                <button
                  key={e}
                  onClick={() => setEmoji1(e)}
                  className={`p-2 rounded bg-black/30 hover:bg-crimson/20 transition-colors ${emoji1 === e ? "border border-crimson" : "border border-transparent"}`}
                >
                  {e}
                </button>
              ))}
            </div>
            <input
              id="custom-emoji"
              type="text"
              className="w-full bg-black/50 border border-crimson/30 rounded-lg p-2 text-white"
              placeholder="Emoji kustom..."
              value={emoji1}
              onChange={(e) => setEmoji1(e.target.value)}
            />
          </div>

          <div>
            <label htmlFor="font-style" className="block text-gold text-sm font-semibold mb-2 uppercase tracking-wider">Gaya Font</label>
            <select
              id="font-style"
              className="w-full bg-black/50 border border-crimson/30 rounded-lg p-2 text-white appearance-none"
              value={style}
              onChange={(e) => setStyle(e.target.value as any)}
            >
              <option value="normal">Normal</option>
              <option value="doubleStruck">Double Struck</option>
              <option value="script">Script</option>
              <option value="bold">Bold</option>
              <option value="monospace">Monospace</option>
              <option value="fraktur">Fraktur</option>
            </select>
          </div>
        </div>

        {/* Mode Dekorasi */}
        <div className="mb-6">
          <label className="block text-gold text-sm font-semibold mb-2 uppercase tracking-wider">Mode Dekorasi</label>
          <div className="flex flex-wrap gap-2">
            {[
              { id: "none", label: "Tanpa Emoji" },
              { id: "interleave", label: "Antara Huruf" },
              { id: "wrap", label: "Bungkus Huruf" },
              { id: "border", label: "Pinggiran" },
              { id: "mix", label: "Mix 2 Emoji" },
            ].map((m) => (
              <button
                key={m.id}
                onClick={() => setMode(m.id as any)}
                className={`px-4 py-2 rounded-lg text-sm font-medium transition-all ${
                  mode === m.id
                    ? "bg-crimson text-white"
                    : "bg-black/30 text-gray-400 hover:text-white hover:bg-crimson/30"
                }`}
              >
                {m.label}
              </button>
            ))}
          </div>
          {mode === "mix" && (
             <div className="mt-4 flex items-center gap-4">
                <div>
                  <label htmlFor="second-emoji" className="block text-gold text-xs mb-1 uppercase">Emoji Kedua</label>
                  <input
                    id="second-emoji"
                    type="text"
                    className="w-20 bg-black/50 border border-crimson/30 rounded-lg p-2 text-white"
                    value={emoji2}
                    onChange={(e) => setEmoji2(e.target.value)}
                  />
                </div>
                <div className="flex gap-2 self-end">
                   {["💠", "⚡", "🌀", "📍"].map(e => (
                      <button key={e} onClick={() => setEmoji2(e)} className="p-2 bg-black/30 rounded hover:bg-gold/20">{e}</button>
                   ))}
                </div>
             </div>
          )}
        </div>

        {/* Hasil */}
        <div className="mt-8">
          <label className="block text-gold text-sm font-semibold mb-2 uppercase tracking-wider">Hasil</label>
          <div className="relative">
            <div id="result-display" className="w-full min-h-[100px] bg-black/60 border-2 border-dashed border-crimson/50 rounded-lg p-4 text-xl break-all whitespace-pre-wrap">
              {result || "Hasil akan muncul di sini..."}
            </div>
            {result && (
              <button
                onClick={copyToClipboard}
                className="absolute top-2 right-2 bg-gold text-black px-3 py-1 rounded text-xs font-bold hover:bg-crimson hover:text-white transition-all uppercase shadow-lg"
              >
                Salin
              </button>
            )}
          </div>
        </div>
      </div>

      <footer className="mt-12 text-gray-500 text-sm italic">
        Samurai Panel &copy; 2025 - Made for Warriors
      </footer>
    </main>
  );
}

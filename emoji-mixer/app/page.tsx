"use client";

import { useState, useMemo } from "react";
import {
  convertToFancy,
  decorateText,
  mixEmojis,
  generateBug,
  buildCustomEmoji,
  fancyStyles
} from "@/lib/emoji-logic";

export default function Home() {
  const [activeTab, setActiveTab] = useState<"standard" | "bug" | "custom">("standard");

  // Standard State
  const [text, setText] = useState("");
  const [emoji1, setEmoji1] = useState("🔥");
  const [emoji2, setEmoji2] = useState("✨");
  const [mode, setMode] = useState<"none" | "interleave" | "wrap" | "border" | "mix">("interleave");
  const [style, setStyle] = useState<keyof typeof fancyStyles | "normal">("normal");

  // Bug State
  const [bugType, setBugType] = useState<'bidi' | 'zwj_flood' | 'surrogate' | 'variation'>('zwj_flood');
  const [intensity, setIntensity] = useState(10);

  // Custom State
  const [customParts, setCustomParts] = useState<string[]>(["🦹", "♂️"]);

  const result = useMemo(() => {
    if (activeTab === "standard") {
      let processed = text;
      if (style !== "normal") processed = convertToFancy(processed, style);
      if (mode === "interleave" || mode === "wrap" || mode === "border") {
        processed = decorateText(processed, emoji1, mode as 'interleave' | 'wrap' | 'border');
      } else if (mode === "mix") {
        processed = mixEmojis(processed, emoji1, emoji2);
      }
      return processed;
    } else if (activeTab === "bug") {
      return generateBug(bugType, intensity);
    } else if (activeTab === "custom") {
      return buildCustomEmoji(customParts);
    }
    return "";
  }, [text, emoji1, emoji2, mode, style, activeTab, bugType, intensity, customParts]);

  const copyToClipboard = () => {
    if (!result) return;
    navigator.clipboard.writeText(result);
    alert("Teks berhasil disalin!");
  };

  return (
    <main className="min-h-screen bg-background text-foreground p-4 md:p-8 flex flex-col items-center">
      <header className="mb-8 text-center">
        <h1 className="text-4xl md:text-5xl font-bold text-crimson mb-2 tracking-widest uppercase">
          Samurai Emoji Debugger
        </h1>
        <p className="text-gold opacity-80 font-mono">Game Testing & Emoji Customization Lab</p>
      </header>

      <div className="w-full max-w-3xl bg-white/5 border border-gold/20 rounded-2xl overflow-hidden shadow-2xl backdrop-blur-md">
        {/* Tabs */}
        <div className="flex bg-black/40 border-b border-gold/10">
          {(["standard", "custom", "bug"] as const).map((tabId) => {
             const labels = {
               standard: "Mixer Standar",
               custom: "Custom Emoji (ZWJ)",
               bug: "Bug / Stress Test"
             };
             return (
              <button
                key={tabId}
                onClick={() => setActiveTab(tabId)}
                className={`flex-1 py-4 text-sm font-bold uppercase tracking-wider transition-all ${
                  activeTab === tabId
                    ? "bg-crimson text-white border-b-2 border-gold"
                    : "text-gray-500 hover:text-gold hover:bg-white/5"
                }`}
              >
                {labels[tabId]}
              </button>
             );
          })}
        </div>

        <div className="p-6 md:p-8">
          {activeTab === "standard" && (
            <div className="space-y-6 animate-in fade-in duration-500">
              <div>
                <label htmlFor="standard-input" className="block text-gold text-xs font-bold mb-2 uppercase">Input Teks</label>
                <textarea
                  id="standard-input"
                  className="w-full bg-black/50 border border-crimson/30 rounded-xl p-4 text-white focus:ring-2 focus:ring-crimson/50 focus:outline-none transition-all"
                  placeholder="Ketik sesuatu..."
                  rows={2}
                  value={text}
                  onChange={(e) => setText(e.target.value)}
                />
              </div>

              <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
                <div>
                  <label htmlFor="emoji-1" className="block text-gold text-xs font-bold mb-2 uppercase">Emoji Utama</label>
                  <div className="flex gap-2 mb-3">
                    {["🔥", "👹", "⚔️", "🏮", "🌸"].map(e => (
                      <button key={e} onClick={() => setEmoji1(e)} className={`p-2 bg-white/5 rounded-lg border ${emoji1 === e ? 'border-crimson' : 'border-transparent'}`}>{e}</button>
                    ))}
                  </div>
                  <input
                    id="emoji-1"
                    type="text"
                    className="w-full bg-black/50 border border-crimson/30 rounded-lg p-3"
                    value={emoji1}
                    onChange={(e) => setEmoji1(e.target.value)}
                  />
                </div>
                <div>
                  <label htmlFor="font-style" className="block text-gold text-xs font-bold mb-2 uppercase">Gaya Font</label>
                  <select
                    id="font-style"
                    className="w-full bg-black/50 border border-crimson/30 rounded-lg p-3 text-white"
                    value={style}
                    onChange={(e) => setStyle(e.target.value as keyof typeof fancyStyles | "normal")}
                  >
                    <option value="normal">Normal</option>
                    <option value="bold">Bold</option>
                    <option value="script">Script</option>
                    <option value="fraktur">Fraktur</option>
                    <option value="monospace">Monospace</option>
                  </select>
                </div>
              </div>

              <div>
                <label className="block text-gold text-xs font-bold mb-2 uppercase">Mode Dekorasi</label>
                <div className="flex flex-wrap gap-2">
                  {(["none", "interleave", "wrap", "mix"] as const).map(mId => {
                    const labels = {
                      none: "Polos",
                      interleave: "Sela-Sela",
                      wrap: "Bungkus",
                      mix: "Mix 2 Emoji"
                    };
                    return (
                      <button
                        key={mId}
                        onClick={() => setMode(mId)}
                        className={`px-4 py-2 rounded-lg text-xs font-bold uppercase tracking-tighter transition-all ${mode === mId ? "bg-crimson" : "bg-white/5 text-gray-400 hover:text-white"}`}
                      >
                        {labels[mId]}
                      </button>
                    );
                  })}
                </div>
                {mode === "mix" && (
                   <div className="mt-4">
                      <label htmlFor="emoji-2" className="block text-gold text-xs font-bold mb-2 uppercase">Emoji Kedua</label>
                      <input
                        id="emoji-2"
                        type="text"
                        className="w-full bg-black/50 border border-crimson/30 rounded-lg p-3"
                        value={emoji2}
                        onChange={(e) => setEmoji2(e.target.value)}
                      />
                   </div>
                )}
              </div>
            </div>
          )}

          {activeTab === "custom" && (
            <div className="space-y-6 animate-in slide-in-from-right duration-500">
              <div className="bg-gold/10 border border-gold/30 p-4 rounded-xl text-gold text-xs">
                💡 Mode ini menggabungkan beberapa emoji menggunakan **Zero Width Joiner (ZWJ)**.
                Sering digunakan untuk membuat kombinasi emoji yang belum ada di keyboard.
              </div>
              <div>
                <label htmlFor="custom-parts" className="block text-gold text-xs font-bold mb-2 uppercase">Emoji Parts (Pisahkan dengan Koma)</label>
                <input
                  id="custom-parts"
                  type="text"
                  className="w-full bg-black/50 border border-crimson/30 rounded-xl p-4 text-white text-2xl tracking-widest"
                  value={customParts.join(",")}
                  onChange={(e) => setCustomParts(e.target.value.split(",").map(p => p.trim()))}
                />
                <div className="mt-4 flex gap-2">
                   {["👨", "👩", "👶", "🦹", "🦸", "☠️", "🏴‍☠️"].map(e => (
                     <button key={e} onClick={() => setCustomParts([...customParts, e])} className="p-3 bg-white/5 rounded-xl hover:bg-gold/20 text-xl">+</button>
                   ))}
                   <button onClick={() => setCustomParts([])} className="ml-auto px-4 py-2 bg-crimson/20 text-crimson rounded-lg text-xs font-bold uppercase">Reset</button>
                </div>
              </div>
            </div>
          )}

          {activeTab === "bug" && (
            <div className="space-y-6 animate-in slide-in-from-right duration-500">
              <div className="bg-crimson/10 border border-crimson/30 p-4 rounded-xl text-crimson text-xs font-bold">
                ⚠️ PERINGATAN: Karakter di bawah ini dirancang untuk pengujian kestabilan game.
                Beberapa urutan mungkin menyebabkan lag atau crash pada aplikasi yang tidak memiliki proteksi Unicode.
              </div>

              <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
                <div>
                  <label htmlFor="bug-type" className="block text-gold text-xs font-bold mb-2 uppercase">Tipe Pengujian</label>
                  <select
                    id="bug-type"
                    className="w-full bg-black/50 border border-crimson/30 rounded-lg p-3 text-white"
                    value={bugType}
                    onChange={(e) => setBugType(e.target.value as 'bidi' | 'zwj_flood' | 'surrogate' | 'variation')}
                  >
                    <option value="zwj_flood">ZWJ Flooding (Layout Engine Test)</option>
                    <option value="bidi">BiDi Override (UI/Text Direction Bug)</option>
                    <option value="surrogate">Lone Surrogates (Parser/Buffer Bug)</option>
                    <option value="variation">Variation Selector Flood (Memory Test)</option>
                  </select>
                </div>
                <div>
                  <label htmlFor="intensity" className="block text-gold text-xs font-bold mb-2 uppercase">Intensitas: {intensity}</label>
                  <input
                    id="intensity"
                    type="range"
                    min="1"
                    max="100"
                    value={intensity}
                    onChange={(e) => setIntensity(parseInt(e.target.value))}
                    className="w-full accent-crimson bg-black/50 rounded-lg h-2"
                  />
                </div>
              </div>
            </div>
          )}

          {/* Result Box */}
          <div className="mt-10 border-t border-gold/10 pt-8">
            <div className="flex justify-between items-end mb-3">
              <label className="block text-gold text-xs font-bold uppercase tracking-widest">Preview & Output</label>
              <span className="text-[10px] text-gray-500 font-mono">Length: {result.length} chars</span>
            </div>
            <div className="relative group">
              <div id="result-display" className="w-full min-h-[120px] bg-black/80 border-2 border-dashed border-crimson/40 rounded-2xl p-6 text-2xl break-all whitespace-pre-wrap font-serif shadow-inner">
                {result || <span className="text-gray-700 italic">Menunggu input...</span>}
              </div>
              {result && (
                <button
                  onClick={copyToClipboard}
                  className="absolute top-4 right-4 bg-gold text-black px-6 py-2 rounded-full text-xs font-black uppercase hover:bg-crimson hover:text-white transition-all transform hover:scale-105 shadow-xl"
                >
                  Salin Kode
                </button>
              )}
            </div>
          </div>
        </div>
      </div>

      <footer className="mt-12 text-gray-600 text-[10px] uppercase tracking-[0.2em] font-bold">
        Samurai Panel &copy; 2025 - Professional Game Testing Tools
      </footer>
    </main>
  );
}

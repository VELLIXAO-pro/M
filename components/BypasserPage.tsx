"use client";

import React, { useState } from "react";
import { motion, AnimatePresence } from "framer-motion";
import { Sword, Shield, Zap, ExternalLink, RefreshCw, Copy, Check, Terminal, Info } from "lucide-react";
import { cn } from "@/lib/utils";
import { identifyService } from "@/lib/bypasser";

export default function BypasserPage() {
  const [url, setUrl] = useState("");
  const [status, setStatus] = useState<string[]>([]);
  const [isBypassing, setIsBypassing] = useState(false);
  const [destination, setDestination] = useState<string | null>(null);
  const [copied, setCopied] = useState(false);

  const addStatus = (msg: string) => {
    setStatus((prev) => [...prev, msg].slice(-8));
  };

  const handleBypass = async (e: React.FormEvent) => {
    e.preventDefault();
    if (!url) return;

    setIsBypassing(true);
    setDestination(null);
    setStatus([]);

    const service = identifyService(url);
    addStatus(`[INIT] Target detected: ${service}`);

    await new Promise(r => setTimeout(r, 600));
    addStatus("[UPDATE] Verifying bypass engine version 2.3.2...");

    await new Promise(r => setTimeout(r, 800));
    addStatus("[NET] Handshaking with skipped.lol API...");

    if (service === "Unknown") {
      addStatus("[ERROR] Unrecognized link pattern. Please check the URL.");
      setIsBypassing(false);
      return;
    }

    addStatus(`[CORE] Intercepting ${service} redirection chain...`);

    try {
      const response = await fetch("/api/bypass", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ url }),
      });

      const data = await response.json();

      if (data.success && data.destination) {
        addStatus("[SOLVE] Cryptographic challenge bypassed.");
        await new Promise(r => setTimeout(r, 1000));
        addStatus("[SUCCESS] Destination extracted successfully.");
        setDestination(data.destination);
      } else {
        addStatus(`[FAIL] Backend error: ${data.error || "Unknown error"}`);
      }
    } catch (err) {
      addStatus("[ERROR] Network failure. Check your connection.");
    } finally {
      setIsBypassing(false);
    }
  };

  const copyToClipboard = () => {
    if (destination) {
      navigator.clipboard.writeText(destination);
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
    }
  };

  return (
    <main className="flex-1 flex flex-col items-center justify-center p-4 relative overflow-hidden bg-[#1a1a1a]">
      {/* Grid Mesh Background */}
      <div className="absolute inset-0 mesh-background pointer-events-none opacity-20" />

      {/* Background Orbs */}
      <motion.div
        animate={{
          scale: [1, 1.2, 1],
          opacity: [0.1, 0.15, 0.1],
        }}
        transition={{ duration: 10, repeat: Infinity, ease: "linear" }}
        className="absolute top-[-10%] left-[-10%] w-[800px] h-[800px] rounded-full bg-samurai-crimson/10 blur-[120px] pointer-events-none"
      />
      <motion.div
        animate={{
          scale: [1, 1.3, 1],
          opacity: [0.05, 0.08, 0.05],
        }}
        transition={{ duration: 15, repeat: Infinity, ease: "linear", delay: 2 }}
        className="absolute bottom-[-15%] right-[-10%] w-[700px] h-[700px] rounded-full bg-samurai-gold/5 blur-[120px] pointer-events-none"
      />

      <motion.div
        initial={{ opacity: 0, y: 30 }}
        animate={{ opacity: 1, y: 0 }}
        transition={{ duration: 0.8, ease: "easeOut" }}
        className="w-full max-w-2xl z-10"
      >
        <div className="text-center mb-10">
          <motion.div
            initial={{ scale: 0.8, opacity: 0 }}
            animate={{ scale: 1, opacity: 1 }}
            transition={{ delay: 0.2, type: "spring", stiffness: 100 }}
          >
            <h1 className="text-7xl md:text-8xl font-marker text-samurai-crimson mb-2 gold-text-glow leading-tight drop-shadow-[0_0_15px_rgba(220,20,60,0.5)]">
              VELLTOOLS
            </h1>
            <h2 className="text-2xl md:text-3xl font-samurai tracking-[0.3em] text-samurai-gold/80 flex items-center justify-center gap-4 uppercase">
              <motion.span
                initial={{ width: 0 }}
                animate={{ width: 48 }}
                transition={{ delay: 0.5, duration: 0.8 }}
                className="h-[1px] bg-samurai-gold/30 block"
              />
              Bypasser
              <motion.span
                initial={{ width: 0 }}
                animate={{ width: 48 }}
                transition={{ delay: 0.5, duration: 0.8 }}
                className="h-[1px] bg-samurai-gold/30 block"
              />
            </h2>
          </motion.div>
        </div>

        <div className="bg-black/60 backdrop-blur-2xl border border-white/10 rounded-3xl p-8 md:p-10 crimson-border-glow shadow-[0_0_50px_rgba(0,0,0,0.5)] relative overflow-hidden group/card">
          {/* Decorative Corner */}
          <div className="absolute top-0 right-0 w-24 h-24 pointer-events-none">
            <div className="absolute top-4 right-4 w-8 h-[1px] bg-samurai-crimson/40 group-hover/card:w-12 transition-all duration-500"></div>
            <div className="absolute top-4 right-4 w-[1px] h-8 bg-samurai-crimson/40 group-hover/card:h-12 transition-all duration-500"></div>
          </div>
          <div className="absolute bottom-0 left-0 w-24 h-24 pointer-events-none">
            <div className="absolute bottom-4 left-4 w-8 h-[1px] bg-samurai-crimson/40 group-hover/card:w-12 transition-all duration-500"></div>
            <div className="absolute bottom-4 left-4 w-[1px] h-8 bg-samurai-crimson/40 group-hover/card:h-12 transition-all duration-500"></div>
          </div>

          <form onSubmit={handleBypass} className="space-y-8">
            <div className="relative group">
              <label className="block text-xs font-samurai text-samurai-gold/50 mb-3 uppercase tracking-[0.2em] font-bold flex items-center gap-2">
                <Info className="w-3 h-3 text-samurai-gold/30" />
                Insert Target URL
              </label>
              <div className="relative">
                <input
                  type="url"
                  value={url}
                  onChange={(e) => setUrl(e.target.value)}
                  placeholder="https://work.ink/..."
                  className="w-full bg-white/5 border border-white/10 rounded-xl py-5 px-14 focus:outline-none focus:border-samurai-crimson/60 focus:ring-1 focus:ring-samurai-crimson/30 transition-all font-mono text-sm placeholder:text-white/20"
                  disabled={isBypassing}
                  required
                />
                <Sword className="absolute left-5 top-1/2 -translate-y-1/2 w-5 h-5 text-samurai-crimson group-focus-within:rotate-45 transition-transform duration-500" />
              </div>
            </div>

            <button
              type="submit"
              disabled={isBypassing || !url}
              className={cn(
                "w-full py-5 rounded-xl font-marker text-2xl tracking-widest transition-all duration-500 flex items-center justify-center gap-4 shadow-lg overflow-hidden relative",
                isBypassing
                  ? "bg-white/5 text-white/20 cursor-not-allowed"
                  : "samurai-gradient text-white hover:scale-[1.01] hover:shadow-[0_10px_30px_rgba(220,20,60,0.4)] active:scale-95 group/btn"
              )}
            >
              {!isBypassing && (
                <motion.div
                  className="absolute inset-0 bg-white/10 -translate-x-full group-hover/btn:translate-x-full transition-transform duration-1000 ease-in-out"
                  style={{ skewX: "-20deg" }}
                />
              )}
              {isBypassing ? (
                <>
                  <RefreshCw className="w-6 h-6 animate-spin text-samurai-gold" />
                  SHARPENING BLADE...
                </>
              ) : (
                <>
                  <Zap className="w-6 h-6 group-hover/btn:text-samurai-gold transition-colors" />
                  EXECUTE BYPASS
                </>
              )}
            </button>
          </form>

          {/* Terminal Output */}
          <div className="mt-10 space-y-2 bg-black/40 rounded-xl p-6 font-mono text-[11px] md:text-xs border border-white/5 shadow-inner overflow-hidden relative">
            <div className="absolute top-2 right-4 flex gap-1.5 opacity-30">
              <div className="w-2 h-2 rounded-full bg-samurai-crimson animate-pulse"></div>
              <div className="w-2 h-2 rounded-full bg-samurai-gold animate-pulse" style={{ animationDelay: "0.2s" }}></div>
              <div className="w-2 h-2 rounded-full bg-green-500 animate-pulse" style={{ animationDelay: "0.4s" }}></div>
            </div>
            <div className="flex items-center gap-2 text-samurai-gold/40 mb-3 border-b border-white/5 pb-2 uppercase tracking-tighter font-bold">
              <Terminal className="w-3 h-3" />
              System Console v2.3.2
            </div>
            <div className="space-y-1.5 max-h-[160px] overflow-y-auto custom-scrollbar">
              <AnimatePresence mode="popLayout">
                {status.map((msg, i) => (
                  <motion.div
                    key={`${msg}-${i}`}
                    initial={{ opacity: 0, x: -5 }}
                    animate={{ opacity: 1, x: 0 }}
                    className={cn(
                      "flex gap-3 leading-relaxed",
                      msg.includes("[ERROR]") || msg.includes("[FAIL]") ? "text-samurai-crimson" :
                      msg.includes("[SUCCESS]") ? "text-green-400 font-bold" : "text-white/70"
                    )}
                  >
                    <span className="text-samurai-gold/40 shrink-0 select-none">[{new Date().toLocaleTimeString([], { hour12: false, hour: '2-digit', minute: '2-digit', second: '2-digit' })}]</span>
                    <span>{msg}</span>
                  </motion.div>
                ))}
                {status.length === 0 && !isBypassing && (
                  <motion.div
                    initial={{ opacity: 0 }}
                    animate={{ opacity: 0.3 }}
                    className="italic tracking-wide"
                  >
                    System idle. Awaiting command...
                  </motion.div>
                )}
              </AnimatePresence>
            </div>
          </div>

          {/* Success Result */}
          <AnimatePresence>
            {destination && (
              <motion.div
                initial={{ opacity: 0, height: 0, y: 20 }}
                animate={{ opacity: 1, height: "auto", y: 0 }}
                exit={{ opacity: 0, height: 0, y: 20 }}
                className="mt-8 pt-8 border-t border-white/10"
              >
                <motion.div
                  initial={{ scale: 0.95 }}
                  animate={{ scale: 1 }}
                  className="p-6 bg-green-500/5 border border-green-500/20 rounded-2xl space-y-5 shadow-xl relative overflow-hidden group/result"
                >
                  <div className="absolute inset-0 bg-green-500/5 translate-y-full group-hover/result:translate-y-0 transition-transform duration-700" />

                  <div className="flex items-center gap-3 text-green-400 font-samurai uppercase text-xs tracking-[0.3em] font-bold relative z-10">
                    <Shield className="w-4 h-4 animate-bounce" />
                    Victory Achieved
                  </div>

                  <div className="flex flex-col sm:flex-row gap-4 relative z-10">
                    <motion.a
                      whileHover={{ scale: 1.02, y: -2 }}
                      whileTap={{ scale: 0.98 }}
                      href={destination}
                      target="_blank"
                      rel="noopener noreferrer"
                      className="flex-[2] bg-green-600 hover:bg-green-500 text-white py-4 px-6 rounded-xl font-samurai font-bold text-center flex items-center justify-center gap-2 transition-all shadow-lg shadow-green-900/40"
                    >
                      <ExternalLink className="w-5 h-5" />
                      UNLEASH CONTENT
                    </motion.a>
                    <motion.button
                      whileHover={{ scale: 1.02, y: -2 }}
                      whileTap={{ scale: 0.98 }}
                      onClick={copyToClipboard}
                      className="flex-1 bg-white/5 hover:bg-white/10 text-white/90 py-4 px-6 rounded-xl font-samurai text-sm flex items-center justify-center gap-2 transition-all border border-white/10 backdrop-blur-sm"
                    >
                      {copied ? <Check className="w-4 h-4 text-green-400" /> : <Copy className="w-4 h-4" />}
                      {copied ? "COPIED" : "GET URL"}
                    </motion.button>
                  </div>
                </motion.div>
              </motion.div>
            )}
          </AnimatePresence>
        </div>

        {/* Footer info */}
        <div className="mt-10 flex flex-col md:flex-row items-center justify-between gap-6 px-4">
          <div className="flex flex-col gap-1">
            <div className="text-white/20 text-[10px] font-samurai tracking-[0.3em] uppercase flex items-center gap-2">
              <span className="w-4 h-[1px] bg-white/10"></span>
              Designed for Warriors by VELL
            </div>
            <div className="text-white/10 text-[8px] font-mono tracking-widest uppercase ml-6">
              EST. 2024 • VERSION 2.3.2
            </div>
          </div>
          <div className="flex gap-8">
            <a href="https://skipped.lol/" target="_blank" className="group flex items-center gap-2">
              <div className="w-1.5 h-1.5 rounded-full bg-samurai-gold/30 group-hover:bg-samurai-gold transition-colors" />
              <span className="text-white/20 group-hover:text-samurai-gold transition-colors text-[10px] font-samurai tracking-[0.3em] uppercase underline-offset-4 underline decoration-white/5">Engine</span>
            </a>
            <a href="https://wa.me/6285706400133" target="_blank" className="group flex items-center gap-2">
              <div className="w-1.5 h-1.5 rounded-full bg-samurai-crimson/30 group-hover:bg-samurai-crimson transition-colors" />
              <span className="text-white/20 group-hover:text-samurai-crimson transition-colors text-[10px] font-samurai tracking-[0.3em] uppercase underline-offset-4 underline decoration-white/5">Support</span>
            </a>
          </div>
        </div>
      </motion.div>

      {/* Scroll text decoration */}
      <div className="absolute left-8 top-1/2 -translate-y-1/2 hidden xl:block select-none pointer-events-none opacity-[0.03]">
        <div className="rotate-90 text-white font-samurai text-9xl tracking-[0.8em] whitespace-nowrap uppercase">
          VELTOOLS BYPASSER
        </div>
      </div>
      <div className="absolute right-8 top-1/2 -translate-y-1/2 hidden xl:block select-none pointer-events-none opacity-[0.03]">
        <div className="-rotate-90 text-white font-samurai text-9xl tracking-[0.8em] whitespace-nowrap uppercase">
          SAMURAI EDITION
        </div>
      </div>
    </main>
  );
}

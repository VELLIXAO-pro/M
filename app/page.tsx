"use client";

import { useState } from "react";
import { motion, AnimatePresence } from "framer-motion";
import { Download, Shield, Zap, ExternalLink, AlertCircle, Loader2 } from "lucide-react";
import { clsx, type ClassValue } from "clsx";
import { twMerge } from "tailwind-merge";

function cn(...inputs: ClassValue[]) {
  return twMerge(clsx(inputs));
}

export default function Home() {
  const [url, setUrl] = useState("");
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const handleDownload = async () => {
    if (!url) {
      setError("Please enter a valid URL");
      return;
    }
    setError(null);
    setLoading(true);

    try {
      const downloadUrl = `/api/download?url=${encodeURIComponent(url)}`;

      // We use a traditional anchor tag click to trigger the download from the API
      const link = document.createElement("a");
      link.href = downloadUrl;
      // The filename is handled by Content-Disposition in the API
      document.body.appendChild(link);
      link.click();
      document.body.removeChild(link);
    } catch (err: any) {
      setError(err.message || "An unexpected error occurred");
    } finally {
      setLoading(false);
    }
  };

  return (
    <main className="min-h-screen bg-[#1a1a1a] text-white flex flex-col items-center justify-center p-4 relative overflow-hidden">
      {/* Background Decorative Elements */}
      <div className="absolute top-[-10%] left-[-10%] w-[40%] h-[40%] bg-crimson/10 rounded-full blur-[120px]" />
      <div className="absolute bottom-[-10%] right-[-10%] w-[40%] h-[40%] bg-gold/5 rounded-full blur-[120px]" />

      <div className="z-10 w-full max-w-2xl">
        <motion.div
          initial={{ opacity: 0, y: 20 }}
          animate={{ opacity: 1, y: 0 }}
          transition={{ duration: 0.8 }}
          className="text-center mb-12"
        >
          <div className="flex justify-center mb-6">
            <div className="p-4 border-2 border-crimson rounded-full bg-crimson/5 shadow-[0_0_20px_rgba(220,20,60,0.3)]">
              <Shield className="w-12 h-12 text-crimson" />
            </div>
          </div>
          <h1 className="text-4xl md:text-6xl font-bold mb-4 tracking-tighter">
            VELL <span className="text-crimson">RAW</span> DOWNLOADER
          </h1>
          <p className="text-gray-400 text-lg md:text-xl font-sawarabi">
            Unleash the source, bypass the restrictions.
          </p>
        </motion.div>

        <motion.div
          initial={{ opacity: 0, scale: 0.95 }}
          animate={{ opacity: 1, scale: 1 }}
          transition={{ delay: 0.2, duration: 0.6 }}
          className="bg-[#242424] border border-white/10 p-8 rounded-2xl shadow-2xl backdrop-blur-sm"
        >
          <div className="space-y-6">
            <div>
              <label className="block text-xs uppercase tracking-widest text-gold mb-2 font-bold">
                Target Script URL
              </label>
              <div className="relative group">
                <input
                  type="text"
                  value={url}
                  onChange={(e) => setUrl(e.target.value)}
                  placeholder="https://raw.githubusercontent.com/... or https://api.luarmor.net/..."
                  className="w-full bg-black/50 border border-white/10 rounded-xl py-4 px-5 focus:outline-none focus:border-crimson transition-all duration-300 text-gray-200 placeholder:text-gray-600"
                />
                <div className="absolute inset-0 rounded-xl bg-crimson/5 opacity-0 group-focus-within:opacity-100 pointer-events-none transition-opacity" />
              </div>
            </div>

            <AnimatePresence>
              {error && (
                <motion.div
                  initial={{ opacity: 0, height: 0 }}
                  animate={{ opacity: 1, height: "auto" }}
                  exit={{ opacity: 0, height: 0 }}
                  className="flex items-center gap-3 text-crimson bg-crimson/10 p-4 rounded-xl border border-crimson/20"
                >
                  <AlertCircle className="w-5 h-5 shrink-0" />
                  <p className="text-sm font-medium">{error}</p>
                </motion.div>
              )}
            </AnimatePresence>

            <button
              onClick={handleDownload}
              disabled={loading}
              className={cn(
                "w-full group relative overflow-hidden rounded-xl py-4 font-bold tracking-widest uppercase transition-all duration-300 active:scale-[0.98]",
                loading
                  ? "bg-gray-800 cursor-not-allowed"
                  : "bg-crimson hover:bg-[#b01030] hover:shadow-[0_0_30px_rgba(220,20,60,0.4)]"
              )}
            >
              <div className="relative z-10 flex items-center justify-center gap-3">
                {loading ? (
                  <>
                    <Loader2 className="w-5 h-5 animate-spin" />
                    <span>Executing...</span>
                  </>
                ) : (
                  <>
                    <Download className="w-5 h-5 group-hover:translate-y-0.5 transition-transform" />
                    <span>Execute Download</span>
                  </>
                )}
              </div>
            </button>
          </div>
        </motion.div>

        <motion.div
          initial={{ opacity: 0 }}
          animate={{ opacity: 1 }}
          transition={{ delay: 0.6, duration: 1 }}
          className="mt-12 flex flex-col items-center gap-6"
        >
          <div className="flex gap-8 text-gray-500">
            <div className="flex items-center gap-2">
              <Zap className="w-4 h-4 text-gold" />
              <span className="text-xs font-bold uppercase tracking-widest">Instant Fetch</span>
            </div>
            <div className="flex items-center gap-2">
              <Shield className="w-4 h-4 text-gold" />
              <span className="text-xs font-bold uppercase tracking-widest">Auto Bypass</span>
            </div>
          </div>

          <a
            href="https://vellixao.vercel.app"
            target="_blank"
            rel="noopener noreferrer"
            className="flex items-center gap-2 text-gold/60 hover:text-gold transition-colors duration-300 text-sm font-bold tracking-widest uppercase"
          >
            Vellixao Portal
            <ExternalLink className="w-3 h-3" />
          </a>
        </motion.div>
      </div>

      {/* Footer Branding */}
      <div className="absolute bottom-6 left-0 right-0 text-center pointer-events-none opacity-20">
        <p className="text-[10vw] font-black leading-none text-white tracking-tighter">VELL TOOLS</p>
      </div>
    </main>
  );
}

"use client";

import { motion } from "framer-motion";
import Navbar from "@/components/Navbar";
import ToolList from "@/components/ToolList";
import ScriptSection from "@/components/ScriptSection";
import { Sword, ChevronDown } from "lucide-react";

export default function Home() {
  return (
    <main className="min-h-screen relative overflow-hidden">
      <Navbar />

      {/* Hero Section */}
      <section className="relative h-screen flex items-center justify-center pt-16">
        <div className="absolute inset-0 bg-[url('https://images.unsplash.com/photo-1542332213-31f87348057f?q=80&w=2070&auto=format&fit=crop')] bg-cover bg-center opacity-20 grayscale brightness-50"></div>
        <div className="absolute inset-0 bg-gradient-to-t from-samurai-black via-transparent to-samurai-black/50"></div>

        <div className="relative z-10 text-center px-4 max-w-4xl mx-auto">
          <motion.div
            initial={{ opacity: 0, scale: 0.8 }}
            animate={{ opacity: 1, scale: 1 }}
            transition={{ duration: 0.8 }}
          >
            <h1 className="text-6xl md:text-8xl font-marker text-white mb-6 tracking-tighter drop-shadow-[0_5px_15px_rgba(220,20,60,0.5)]">
              SAMURAI <span className="text-samurai-red italic">SCRIPTS</span>
            </h1>
            <p className="text-xl md:text-2xl text-samurai-gold font-bold mb-12 tracking-[0.2em] uppercase">
              Precision. Power. Perfection.
            </p>

            <div className="flex flex-col sm:flex-row gap-6 justify-center">
              <a
                href="#tools"
                className="bg-samurai-red hover:bg-red-700 text-white px-10 py-4 rounded-sm font-bold text-lg transition-all flex items-center justify-center gap-2 transform hover:scale-105"
              >
                EXPLORE TOOLS <Sword size={20} />
              </a>
              <a
                href="#scripts"
                className="border-2 border-samurai-gold text-samurai-gold hover:bg-samurai-gold hover:text-black px-10 py-4 rounded-sm font-bold text-lg transition-all flex items-center justify-center gap-2 transform hover:scale-105"
              >
                VIEW SCRIPTS
              </a>
            </div>
          </motion.div>

          <motion.div
            animate={{ y: [0, 10, 0] }}
            transition={{ repeat: Infinity, duration: 2 }}
            className="absolute bottom-10 left-1/2 -translate-x-1/2 text-samurai-red"
          >
            <ChevronDown size={48} />
          </motion.div>
        </div>
      </section>

      <ToolList />
      <ScriptSection />

      {/* Footer */}
      <footer className="bg-zinc-950 py-12 border-t border-samurai-red/20">
        <div className="max-w-7xl mx-auto px-4 text-center">
          <div className="flex items-center justify-center gap-2 mb-6">
            <span className="font-marker text-3xl text-samurai-gold tracking-widest">SAMURAI</span>
          </div>
          <p className="text-gray-500 max-w-md mx-auto mb-8">
            Platform penyedia tool Game Guardian terbaik untuk komunitas modder Indonesia.
          </p>
          <div className="flex justify-center gap-6 mb-8 text-gray-400">
            <a href="#" className="hover:text-samurai-red">YouTube</a>
            <a href="#" className="hover:text-samurai-red">Telegram</a>
            <a href="#" className="hover:text-samurai-red">WhatsApp</a>
          </div>
          <div className="text-sm text-zinc-600">
            © {new Date().getFullYear()} Samurai Tools. Built with Honor.
          </div>
        </div>
      </footer>
    </main>
  );
}

"use client";

import { motion } from "framer-motion";
import { Shield, Sword } from "lucide-react";

export default function Navbar() {
  return (
    <nav className="fixed top-0 w-full z-50 bg-samurai-black/80 backdrop-blur-md border-b border-samurai-red/30">
      <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8">
        <div className="flex items-center justify-between h-16">
          <div className="flex items-center gap-2">
            <Shield className="text-samurai-red w-8 h-8" />
            <span className="font-marker text-2xl text-samurai-gold tracking-wider">
              SAMURAI TOOLS
            </span>
          </div>
          <div className="hidden md:block">
            <div className="flex items-baseline space-x-8">
              <a href="#" className="text-gray-300 hover:text-samurai-gold transition-colors">Home</a>
              <a href="#tools" className="text-gray-300 hover:text-samurai-gold transition-colors">Tools</a>
              <a href="#scripts" className="text-gray-300 hover:text-samurai-gold transition-colors">Scripts</a>
              <button className="bg-samurai-red text-white px-6 py-2 rounded-sm font-bold hover:bg-red-700 transition-all flex items-center gap-2">
                <Sword size={18} />
                CONNECT
              </button>
            </div>
          </div>
        </div>
      </div>
    </nav>
  );
}

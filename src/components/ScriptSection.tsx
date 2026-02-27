"use client";

import { motion } from "framer-motion";
import { Download, Terminal, Code, Sparkles } from "lucide-react";

const scripts = [
  { name: "Pointer.lua", size: "12 KB", type: "Memory Analyzer" },
  { name: "AutoEdit.lua", size: "8 KB", type: "Automation" },
  { name: "MemoryTools.lua", size: "15 KB", type: "Utility" },
  { name: "ValueBehavior.lua", size: "20 KB", type: "Analyzer" }
];

export default function ScriptSection() {
  return (
    <section id="scripts" className="py-24 px-4 bg-black">
      <div className="max-w-7xl mx-auto">
        <div className="flex flex-col md:flex-row justify-between items-end mb-12 gap-6">
          <div>
            <h2 className="text-3xl font-marker text-samurai-gold mb-2">SCRIPT REPOSITORY</h2>
            <p className="text-gray-400">Koleksi script Game Guardian premium hasil riset mandiri.</p>
          </div>
          <div className="flex items-center gap-2 text-samurai-red bg-samurai-red/10 px-4 py-2 border border-samurai-red/30 rounded">
            <Sparkles size={18} />
            <span className="font-bold">NEW UPDATE V2.0</span>
          </div>
        </div>

        <div className="overflow-x-auto">
          <table className="w-full text-left border-collapse">
            <thead>
              <tr className="border-b border-zinc-800">
                <th className="py-4 px-6 text-samurai-red font-marker">FILE NAME</th>
                <th className="py-4 px-6 text-samurai-red font-marker">TYPE</th>
                <th className="py-4 px-6 text-samurai-red font-marker">SIZE</th>
                <th className="py-4 px-6 text-samurai-red font-marker text-right">ACTION</th>
              </tr>
            </thead>
            <tbody>
              {scripts.map((script, index) => (
                <motion.tr
                  key={index}
                  initial={{ opacity: 0 }}
                  whileInView={{ opacity: 1 }}
                  transition={{ delay: index * 0.1 }}
                  className="border-b border-zinc-900 hover:bg-zinc-900/30 transition-colors"
                >
                  <td className="py-4 px-6 flex items-center gap-3">
                    <Code className="text-samurai-gold" size={20} />
                    <span className="font-bold text-gray-200">{script.name}</span>
                  </td>
                  <td className="py-4 px-6">
                    <span className="px-3 py-1 bg-zinc-800 text-xs rounded-full text-gray-400">{script.type}</span>
                  </td>
                  <td className="py-4 px-6 text-gray-400">{script.size}</td>
                  <td className="py-4 px-6 text-right">
                    <a
                      href="https://vellixao.vercel.app"
                      className="text-samurai-red hover:text-samurai-gold transition-colors inline-flex items-center gap-1 font-bold"
                    >
                      GET <Download size={16} />
                    </a>
                  </td>
                </motion.tr>
              ))}
            </tbody>
          </table>
        </div>
      </div>
    </section>
  );
}

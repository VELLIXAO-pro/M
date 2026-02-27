"use client";

import { motion } from "framer-motion";
import { ChevronRight, Download, Zap, MousePointer2, Calculator } from "lucide-react";

const tools = [
  {
    title: "Pointer Track",
    description: "Lacak alamat memori dengan presisi tinggi. Tool ini memungkinkan Anda mengikuti rantai pointer dalam Java Heap atau Native memory secara otomatis.",
    details: "Mendeteksi struktur objek Java, class pointer, dan field offsets secara cerdas. Dilengkapi dengan deteksi level pointer hingga 4 kedalaman.",
    icon: <MousePointer2 className="w-12 h-12 text-samurai-gold" />,
    url: "https://vellixao.vercel.app"
  },
  {
    title: "Offset Calculator",
    description: "Kalkulator khusus untuk menghitung jarak antar alamat memori secara instan dalam format Hex atau Decimal.",
    details: "Memudahkan modifikasi script Game Guardian dengan menghitung base address dan offset secara akurat. Mendukung perhitungan batch untuk banyak alamat sekaligus.",
    icon: <Calculator className="w-12 h-12 text-samurai-red" />,
    url: "https://vellixao.vercel.app"
  }
];

export default function ToolList() {
  return (
    <section id="tools" className="py-24 px-4 bg-gradient-to-b from-samurai-black to-black">
      <div className="max-w-7xl mx-auto">
        <motion.div
          initial={{ opacity: 0, y: 20 }}
          whileInView={{ opacity: 1, y: 0 }}
          viewport={{ once: true }}
          className="text-center mb-16"
        >
          <h2 className="text-4xl md:text-5xl font-marker text-samurai-red mb-4">MASTER TOOLS</h2>
          <div className="h-1 w-24 bg-samurai-gold mx-auto"></div>
        </motion.div>

        <div className="grid grid-cols-1 md:grid-cols-2 gap-12">
          {tools.map((tool, index) => (
            <motion.div
              key={index}
              initial={{ opacity: 0, x: index % 2 === 0 ? -30 : 30 }}
              whileInView={{ opacity: 1, x: 0 }}
              viewport={{ once: true }}
              className="bg-zinc-900/50 border-2 border-samurai-red/20 p-8 rounded-lg hover:border-samurai-red/60 transition-all group relative overflow-hidden"
            >
              <div className="absolute top-0 right-0 p-4 opacity-10 group-hover:opacity-30 transition-opacity">
                {tool.icon}
              </div>

              <div className="flex items-center gap-4 mb-6">
                <div className="p-3 bg-samurai-black border border-samurai-gold/30 rounded-lg">
                  {tool.icon}
                </div>
                <h3 className="text-2xl font-bold text-samurai-gold uppercase tracking-widest">{tool.title}</h3>
              </div>

              <p className="text-gray-300 mb-6 leading-relaxed">
                {tool.description}
              </p>

              <div className="bg-black/40 p-4 rounded border-l-4 border-samurai-red mb-8">
                <p className="text-sm text-gray-400 italic">
                  {tool.details}
                </p>
              </div>

              <a
                href={tool.url}
                target="_blank"
                className="inline-flex items-center gap-2 bg-samurai-red hover:bg-red-700 text-white font-bold py-3 px-8 rounded-sm transition-all group-hover:gap-4"
              >
                DOWNLOAD <Download size={18} />
              </a>
            </motion.div>
          ))}
        </div>
      </div>
    </section>
  );
}

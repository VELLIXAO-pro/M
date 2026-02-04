"use client";

import { useState, useRef } from "react";
import { Upload, FileCode, Download, Shield, Zap, Info, Loader2 } from "lucide-react";
import { LuaVM } from "@/lib/lua-vm";
import { beautifyLua } from "@/lib/beautify";

export default function Home() {
  const [file, setFile] = useState<File | null>(null);
  const [isProcessing, setIsProcessing] = useState(false);
  const [result, setResult] = useState<string | null>(null);
  const [logs, setLogs] = useState<string[]>([]);
  const fileInputRef = useRef<HTMLInputElement>(null);

  const addLog = (message: string) => {
    setLogs((prev) => [...prev, `[${new Date().toLocaleTimeString()}] ${message}`]);
  };

  const handleFileChange = (e: React.ChangeEvent<HTMLInputElement>) => {
    if (e.target.files && e.target.files[0]) {
      const selectedFile = e.target.files[0];
      if (selectedFile.name.endsWith(".lua")) {
        setFile(selectedFile);
        setResult(null);
        setLogs([]);
        addLog(`Selected file: ${selectedFile.name}`);
      } else {
        alert("Please select a .lua file");
      }
    }
  };

  const handleDeobfuscate = async () => {
    if (!file) return;

    setIsProcessing(true);
    setResult(null);
    setLogs([]);
    addLog("Starting deobfuscation process...");

    try {
      const content = await file.text();
      addLog("Reading file content...");

      const vm = new LuaVM();
      addLog("Initializing Lua VM (Wasmoon)...");

      const resultRaw = await vm.run(content, (msg) => {
        addLog(msg);
      });

      addLog("Beautifying recovered source code...");
      const finalSource = beautifyLua(resultRaw);

      setResult(finalSource);
      addLog("Deobfuscation successful!");

      // Automatic download
      setTimeout(() => {
        addLog("Triggering automatic download...");
        const blob = new Blob([finalSource], { type: "text/plain" });
        const url = URL.createObjectURL(blob);
        const a = document.createElement("a");
        a.href = url;
        a.download = file ? `deobfuscated_${file.name}` : "deobfuscated.lua";
        document.body.appendChild(a);
        a.click();
        document.body.removeChild(a);
        URL.revokeObjectURL(url);
      }, 500);

    } catch (error) {
      addLog(`Error: ${error instanceof Error ? error.message : String(error)}`);
    } finally {
      setIsProcessing(false);
    }
  };

  const handleDownload = () => {
    if (!result) return;
    const blob = new Blob([result], { type: "text/plain" });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = file ? `deobfuscated_${file.name}` : "deobfuscated.lua";
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
  };

  return (
    <main className="min-h-screen p-4 md:p-8 flex flex-col items-center">
      <div className="max-w-4xl w-full">
        {/* Header */}
        <header className="mb-12 text-center">
          <h1 className="text-4xl md:text-6xl font-bold text-samurai-red mb-2 tracking-tighter flex items-center justify-center gap-3">
            <Shield className="w-10 h-10 md:w-14 md:h-14" />
            LUA DEOBFUSCATOR
          </h1>
          <p className="text-samurai-gold font-mono text-sm md:text-base">
            POWERFUL • SAMURAI EDITION • 100% DECRYPT
          </p>
        </header>

        <div className="grid grid-cols-1 md:grid-cols-2 gap-8">
          {/* Left Side: Upload & Control */}
          <div className="space-y-6">
            <div
              className={`samurai-border bg-samurai-black p-8 rounded-lg flex flex-col items-center justify-center cursor-pointer hover:bg-neutral-900 transition-colors ${!file ? "border-dashed" : "border-solid"}`}
              onClick={() => fileInputRef.current?.click()}
            >
              <input
                type="file"
                ref={fileInputRef}
                onChange={handleFileChange}
                accept=".lua"
                className="hidden"
              />
              {file ? (
                <div className="text-center">
                  <FileCode className="w-16 h-16 text-samurai-gold mx-auto mb-4" />
                  <p className="text-lg font-bold">{file.name}</p>
                  <p className="text-neutral-500 text-sm">{(file.size / 1024).toFixed(2)} KB</p>
                </div>
              ) : (
                <div className="text-center">
                  <Upload className="w-16 h-16 text-neutral-600 mx-auto mb-4" />
                  <p className="text-lg">Click to Upload Lua Script</p>
                  <p className="text-neutral-500 text-sm">Drag and drop supported</p>
                </div>
              )}
            </div>

            <button
              onClick={handleDeobfuscate}
              disabled={!file || isProcessing}
              className={`w-full samurai-button py-4 rounded-lg font-bold text-lg flex items-center justify-center gap-2 disabled:opacity-50 disabled:cursor-not-allowed`}
            >
              {isProcessing ? (
                <>
                  <Loader2 className="animate-spin" />
                  PROCESSING...
                </>
              ) : (
                <>
                  <Zap />
                  DEOBFUSCATE NOW
                </>
              )}
            </button>

            {/* Logs Area */}
            <div className="bg-black p-4 rounded-lg h-48 overflow-y-auto font-mono text-xs border border-neutral-800">
              <h3 className="text-samurai-gold mb-2 flex items-center gap-2">
                <Info className="w-4 h-4" /> SYSTEM LOGS
              </h3>
              {logs.map((log, i) => (
                <div key={i} className="text-neutral-400 mb-1">{log}</div>
              ))}
              {logs.length === 0 && <div className="text-neutral-700 italic">No activity yet...</div>}
            </div>
          </div>

          {/* Right Side: Preview/Result */}
          <div className="space-y-4">
            <div className="samurai-border bg-samurai-black rounded-lg h-[400px] flex flex-col">
              <div className="p-3 border-b border-samurai-red/30 flex justify-between items-center">
                <span className="text-sm font-bold text-samurai-gold flex items-center gap-2">
                  <FileCode className="w-4 h-4" /> OUTPUT PREVIEW
                </span>
                {result && (
                  <button
                    onClick={handleDownload}
                    className="text-xs samurai-button px-3 py-1 rounded flex items-center gap-1"
                  >
                    <Download className="w-3 h-3" /> DOWNLOAD
                  </button>
                )}
              </div>
              <div className="flex-1 p-4 overflow-auto font-mono text-sm bg-[#0a0a0a]">
                {result ? (
                  <pre className="text-green-500">{result}</pre>
                ) : (
                  <div className="h-full flex items-center justify-center text-neutral-700 italic">
                    Output will appear here after deobfuscation
                  </div>
                )}
              </div>
            </div>
          </div>
        </div>

        {/* Footer info */}
        <footer className="mt-16 pt-8 border-t border-neutral-800 text-center text-neutral-500 text-sm">
          <p>© 2024 Samurai Lua Decrypter. Developed for High-Performance Deobfuscation.</p>
        </footer>
      </div>
    </main>
  );
}

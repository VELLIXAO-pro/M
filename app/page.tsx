"use client";

import { useState, useRef, useEffect } from "react";
import { Upload, FileCode, Download, Shield, Zap, Info, Loader2, Layers, ChevronRight, AlertCircle } from "lucide-react";
import { LuaVM, CapturedChunk } from "@/lib/lua-vm";
import { beautifyLua } from "@/lib/beautify";

export default function Home() {
  const [file, setFile] = useState<File | null>(null);
  const [isProcessing, setIsProcessing] = useState(false);
  const [result, setResult] = useState<string | null>(null);
  const [layers, setLayers] = useState<CapturedChunk[]>([]);
  const [selectedLayer, setSelectedLayer] = useState<number>(-1);
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
        setLayers([]);
        setSelectedLayer(-1);
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
    setLayers([]);
    setLogs([]);
    addLog("Starting deobfuscation process...");

    try {
      const content = await file.text();
      addLog(`Reading file content (${content.length} bytes)...`);

      const vm = new LuaVM();
      addLog("Initializing Lua VM (Wasmoon)...");

      const captured = await vm.run(content, (msg) => {
        addLog(msg);
      });

      if (captured.length > 0) {
        setLayers(captured);
        addLog(`Found ${captured.length} deobfuscation layers.`);

        // Pick the best one: Deepest level, then longest
        const sorted = [...captured].sort((a, b) => {
          if (b.depth !== a.depth) return b.depth - a.depth;
          return b.code.length - a.code.length;
        });

        const bestIndex = captured.indexOf(sorted[0]);
        setSelectedLayer(bestIndex);

        const finalSource = beautifyLua(sorted[0].code);
        setResult(finalSource);
        addLog("Deobfuscation successful! Best layer selected.");

        // Automatic download
        triggerDownload(finalSource, file.name);
      } else {
        addLog("No hidden code captured. Script might not be obfuscated or uses an unsupported method.");
        setResult(beautifyLua(content));
        addLog("Showing original source (beautified).");
        triggerDownload(beautifyLua(content), file.name);
      }
    } catch (error) {
      addLog(`Error: ${error instanceof Error ? error.message : String(error)}`);
    } finally {
      setIsProcessing(false);
    }
  };

  const triggerDownload = (content: string, originalName: string) => {
    setTimeout(() => {
      addLog("Triggering automatic download...");
      const blob = new Blob([content], { type: "text/plain" });
      const url = URL.createObjectURL(blob);
      const a = document.createElement("a");
      a.href = url;
      a.download = `deobfuscated_${originalName}`;
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
      URL.revokeObjectURL(url);
    }, 1000);
  };

  const handleSelectLayer = (index: number) => {
    setSelectedLayer(index);
    setResult(beautifyLua(layers[index].code));
    addLog(`Switched to Layer ${layers[index].depth} (${layers[index].source})`);
  };

  return (
    <main className="min-h-screen p-4 md:p-8 flex flex-col items-center">
      <div className="max-w-6xl w-full">
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

        <div className="grid grid-cols-1 lg:grid-cols-12 gap-8">
          {/* Left Side: Upload & Control (Col 4) */}
          <div className="lg:col-span-4 space-y-6">
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
                  <p className="text-lg font-bold truncate max-w-[200px]">{file.name}</p>
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

            {/* Layers Selection */}
            {layers.length > 0 && (
              <div className="samurai-border bg-samurai-black p-4 rounded-lg">
                <h3 className="text-samurai-gold text-sm font-bold mb-3 flex items-center gap-2">
                  <Layers className="w-4 h-4" /> CAPTURED LAYERS
                </h3>
                <div className="space-y-2 max-h-40 overflow-y-auto pr-2">
                  {layers.map((layer, i) => (
                    <button
                      key={i}
                      onClick={() => handleSelectLayer(i)}
                      className={`w-full text-left p-2 rounded text-xs flex items-center justify-between transition-colors ${selectedLayer === i ? "bg-samurai-red text-white" : "bg-neutral-800 text-neutral-400 hover:bg-neutral-700"}`}
                    >
                      <span className="flex items-center gap-2">
                        <ChevronRight className="w-3 h-3" />
                        Layer {layer.depth} ({layer.source})
                      </span>
                      <span>{Math.round(layer.code.length / 1024)} KB</span>
                    </button>
                  ))}
                </div>
              </div>
            )}

            {/* Logs Area */}
            <div className="bg-black p-4 rounded-lg h-48 overflow-y-auto font-mono text-[10px] border border-neutral-800">
              <h3 className="text-samurai-gold mb-2 flex items-center gap-2 sticky top-0 bg-black pb-1">
                <Info className="w-3 h-3" /> SYSTEM LOGS
              </h3>
              {logs.map((log, i) => (
                <div key={i} className="text-neutral-400 mb-1 leading-tight">{log}</div>
              ))}
              {logs.length === 0 && <div className="text-neutral-700 italic">No activity yet...</div>}
            </div>
          </div>

          {/* Right Side: Preview/Result (Col 8) */}
          <div className="lg:col-span-8 space-y-4">
            <div className="samurai-border bg-samurai-black rounded-lg min-h-[500px] flex flex-col">
              <div className="p-3 border-b border-samurai-red/30 flex justify-between items-center bg-neutral-900/50">
                <div className="flex items-center gap-4">
                  <span className="text-sm font-bold text-samurai-gold flex items-center gap-2">
                    <FileCode className="w-4 h-4" /> SOURCE PREVIEW
                  </span>
                  {selectedLayer !== -1 && (
                    <span className="bg-samurai-red/20 text-samurai-red text-[10px] px-2 py-0.5 rounded-full border border-samurai-red/30">
                      Layer {layers[selectedLayer].depth}
                    </span>
                  )}
                </div>
                {result && (
                  <button
                    onClick={() => file && triggerDownload(result, file.name)}
                    className="text-xs samurai-button px-4 py-1.5 rounded flex items-center gap-2 font-bold"
                  >
                    <Download className="w-3 h-3" /> DOWNLOAD SOURCE
                  </button>
                )}
              </div>
              <div className="flex-1 p-4 overflow-auto font-mono text-xs bg-[#050505] relative">
                {result ? (
                  result.startsWith("\x1bLua") ? (
                    <div className="flex flex-col items-center justify-center h-full text-center space-y-4">
                      <AlertCircle className="w-12 h-12 text-samurai-gold" />
                      <div className="space-y-2">
                        <p className="text-samurai-gold font-bold text-lg">BYTECODE DETECTED</p>
                        <p className="text-neutral-500 max-w-md mx-auto">
                          The captured code is in Lua bytecode format. This tool can decrypt script layers but does not include a full bytecode decompiler yet.
                        </p>
                      </div>
                      <div className="bg-black p-4 rounded border border-neutral-800 text-neutral-600 text-left w-full overflow-hidden">
                         {result.substring(0, 500)}...
                      </div>
                    </div>
                  ) : (
                    <pre className="text-green-500 whitespace-pre-wrap">{result}</pre>
                  )
                ) : (
                  <div className="h-full flex flex-col items-center justify-center text-neutral-700 italic space-y-4">
                    <FileCode className="w-12 h-12 opacity-20" />
                    <p>Output will appear here after deobfuscation</p>
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

import { LuaFactory, LuaEngine } from "wasmoon";

export interface CapturedChunk {
  code: string;
  depth: number;
  timestamp: number;
  source: string; // 'load', 'loadstring', 'pcall', etc.
}

export class LuaVM {
  private factory: LuaFactory;
  private capturedChunks: CapturedChunk[] = [];
  private currentDepth: number = 0;
  private maxDepth: number = 10; // Prevent infinite loops

  constructor() {
    this.factory = new LuaFactory();
  }

  async run(sourceCode: string, onLog?: (msg: string) => void) {
    this.capturedChunks = [];
    this.currentDepth = 0;
    const lua = await this.factory.createEngine();

    try {
      this.setupHooks(lua, onLog);
      this.setupGGMocks(lua);
      this.setupAntiVMBypasses(lua);

      if (onLog) onLog("Starting execution...");

      try {
        await lua.doString(sourceCode);
      } catch (err) {
        if (onLog) onLog(`[VM Error] ${err}`);
      }

      if (onLog) onLog(`Execution finished. Captured ${this.capturedChunks.length} potential layers.`);

      return this.capturedChunks;
    } finally {
      lua.global.close();
    }
  }

  private setupHooks(lua: LuaEngine, onLog?: (msg: string) => void) {
    const self = this;

    const capture = (str: string, source: string) => {
      if (typeof str !== 'string' || str.length < 5) return null;

      // Check if already captured to avoid duplicates
      const exists = self.capturedChunks.some(c => c.code === str);
      if (!exists) {
        self.capturedChunks.push({
          code: str,
          depth: self.currentDepth,
          timestamp: Date.now(),
          source
        });

        if (onLog) {
          const preview = str.substring(0, 40).replace(/[\n\r]/g, " ").trim();
          const isBytecode = str.startsWith("\x1bLua");
          onLog(`[Layer ${self.currentDepth}] Captured from ${source}: ${isBytecode ? "[BYTECODE]" : preview}... (${str.length} bytes)`);
        }
      }

      if (self.currentDepth >= self.maxDepth) {
        if (onLog) onLog(`[Warning] Max nesting depth reached (${self.maxDepth}). Skipping execution of inner layer.`);
        return () => {};
      }

      // Return a function that executes the code
      return (...args: any[]) => {
        self.currentDepth++;
        try {
          // We use doStringSync because load/loadstring are expected to be synchronous
          const res = lua.doStringSync(str);
          self.currentDepth--;
          return res;
        } catch (e) {
          self.currentDepth--;
          // If execution fails, we still captured the code, which is what matters
          if (onLog) onLog(`[Layer ${self.currentDepth}] Inner execution failed, but code was captured.`);
          return null;
        }
      };
    };

    lua.global.set("loadstring", (str: string) => {
      return capture(str, "loadstring");
    });

    lua.global.set("load", (chunk: any) => {
      if (typeof chunk === 'string') {
        return capture(chunk, "load");
      } else if (typeof chunk === 'function') {
        let str = "";
        try {
          let part = chunk();
          while (part) {
            str += part;
            part = chunk();
          }
        } catch (e) {}
        if (str) return capture(str, "load(func)");
      }
      return null;
    });

    const originalPcall = lua.global.get("pcall");
    lua.global.set("pcall", (f: any, ...args: any[]) => {
      try {
        if (typeof f === 'function') {
          return [true, f(...args)];
        } else if (typeof f === 'string') {
          const exec = capture(f, "pcall");
          return [true, exec ? exec(...args) : null];
        }
      } catch (e) {
        return [false, String(e)];
      }
      return [false, "invalid pcall"];
    });

    lua.global.set("print", (...args: any[]) => {
      const msg = args.map(a => String(a)).join("\t");
      if (onLog) onLog(`[Script] ${msg}`);
    });
  }

  private setupGGMocks(lua: LuaEngine) {
    const gg: any = {
      alert: () => 1,
      toast: () => {},
      setVisible: () => {},
      searchNumber: () => {},
      getResultsCount: () => 100,
      getResults: (count: number) => {
        const results = [];
        for (let i = 0; i < Math.min(count, 100); i++) {
          results.push({ address: 0x1234000 + i * 4, value: 100, flags: 4 });
        }
        return results;
      },
      clearResults: () => {},
      addListItems: () => {},
      getValues: (items: any) => items,
      setValues: () => {},
      choice: () => 1,
      prompt: (items: any) => {
        if (Array.isArray(items)) return items.map(() => "1");
        return ["1"];
      },
      require: (mod: string) => {
        console.log("gg.require called for:", mod);
      },
      getFile: () => "script.lua",
      isVisible: () => true,
      sleep: () => {},
      copyText: () => {},
      getActiveTab: () => 1,
      multiChoice: (items: any) => {
          if (Array.isArray(items)) return items.map((_, i) => i === 0);
          return [true];
      },
      EXT_STORAGE: "/sdcard",
      PACKAGE: "com.example.game",
      REGION_JAVA_HEAP: 1,
      REGION_C_HEAP: 2,
      TYPE_DWORD: 4,
      TYPE_FLOAT: 16,
      BUILD: 16142,
      VERSION: "101.1"
    };
    lua.global.set("gg", gg);
  }

  private setupAntiVMBypasses(lua: LuaEngine) {
    const debug = {
      getinfo: (f: any) => {
        return {
          source: "=[C]",
          short_src: "[C]",
          what: "C",
          name: "unknown",
          currentline: -1,
          nups: 0,
          linedefined: -1,
          lastlinedefined: -1
        };
      },
      getupvalue: () => null,
      setupvalue: () => {},
      sethook: () => {},
    };
    lua.global.set("debug", debug);

    // Mock os.exit to prevent script from stopping the VM
    const os = lua.global.get("os");
    if (os) {
      os.exit = () => {
        console.log("os.exit called and ignored");
      };
    }
  }
}

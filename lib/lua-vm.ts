import { LuaFactory, LuaEngine } from "wasmoon";

export interface CapturedChunk {
  code: string;
  depth: number;
  timestamp: number;
  source: string;
}

export class LuaVM {
  private factory: LuaFactory;
  private capturedChunks: CapturedChunk[] = [];
  private currentDepth: number = 0;
  private maxDepth: number = 20;

  constructor() {
    this.factory = new LuaFactory();
  }

  async run(sourceCode: string, onLog?: (msg: string) => void) {
    this.capturedChunks = [];
    this.currentDepth = 0;
    const lua = await this.factory.createEngine();

    try {
      this.setupBaseMocks(lua, onLog);
      this.setupExploitMocks(lua, onLog);
      this.setupGGMocks(lua);
      this.setupAntiVMBypasses(lua);

      if (onLog) onLog("Initializing execution environment...");

      try {
        await lua.doString(sourceCode);
      } catch (err) {
        if (onLog) onLog(`[VM Error] ${err}`);
      }

      return this.capturedChunks;
    } finally {
      lua.global.close();
    }
  }

  private setupBaseMocks(lua: LuaEngine, onLog?: (msg: string) => void) {
    const self = this;

    const capture = (str: any, source: string) => {
      if (typeof str !== 'string' || str.length < 5) return null;

      const exists = self.capturedChunks.some(c => c.code === str);
      if (!exists) {
        self.capturedChunks.push({
          code: str,
          depth: self.currentDepth,
          timestamp: Date.now(),
          source
        });

        if (onLog) {
          const isBytecode = str.startsWith("\x1bLua");
          const preview = isBytecode ? "[BYTECODE]" : str.substring(0, 60).replace(/[\n\r\t]/g, " ").trim();
          onLog(`[Layer ${self.currentDepth}] Captured from ${source}: ${preview}... (${str.length} bytes)`);
        }
      }

      if (self.currentDepth >= self.maxDepth) {
        return () => {};
      }

      return (...args: any[]) => {
        self.currentDepth++;
        try {
          const res = lua.doStringSync(str);
          self.currentDepth--;
          return res;
        } catch (e) {
          self.currentDepth--;
          return null;
        }
      };
    };

    lua.global.set("loadstring", (str: string) => capture(str, "loadstring"));
    lua.global.set("load", (chunk: any) => {
      if (typeof chunk === 'string') return capture(chunk, "load");
      if (typeof chunk === 'function') {
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

    lua.global.set("print", (...args: any[]) => {
      const msg = args.map(a => String(a)).join("\t");
      if (onLog) onLog(`[Script Log] ${msg}`);
    });

    // Mock getfenv/setfenv for environment isolation bypass
    lua.global.set("getfenv", (f: any) => lua.global.get("_G"));
    lua.global.set("setfenv", (f: any, env: any) => f);

    // table.unpack/unpack
    const table = lua.global.get("table");
    lua.global.set("unpack", table.unpack);
  }

  private setupExploitMocks(lua: LuaEngine, onLog?: (msg: string) => void) {
    const self = this;

    // Mock 'game' object for Roblox/Exploit compatibility
    const game = {
      HttpGet: (url: string) => {
        if (onLog) onLog(`[Network] Blocked HttpGet to: ${url}`);
        return `print("Content from ${url} was blocked for safety.")`;
      },
      HttpGetAsync: (url: string) => {
        if (onLog) onLog(`[Network] Blocked HttpGetAsync to: ${url}`);
        return `print("Content from ${url} was blocked for safety.")`;
      },
      GetService: (name: string) => {
        if (onLog) onLog(`[System] GetService: ${name}`);
        return {
          JSONDecode: (data: string) => JSON.parse(data),
          JSONEncode: (data: any) => JSON.stringify(data),
          UserId: 12345678,
          LocalPlayer: {
            UserId: 12345678,
            Name: "SamuraiUser",
            Kick: (reason: string) => onLog?.(`[Script] Attempted to kick: ${reason}`),
            PlayerGui: {
                Interface: {
                    RoundOverStats: { Visible: false },
                    TeamSelection: { Visible: false, ["2"]: {} },
                    Game: { Visible: true }
                }
            },
            Character: {
                WaitForChild: () => ({
                    MoveTo: () => {},
                    Position: { X: 0, Y: 0, Z: 0 },
                    Magnitude: 0
                })
            }
          }
        };
      },
      Players: {
          LocalPlayer: { UserId: 12345678 }
      }
    };

    lua.global.set("game", game);
    lua.global.set("workspace", {
        Map: { BallNoCollide: { Positions: { ["2"]: { GetChildren: () => [] } }, Boundaries: { WaitForChild: () => ({}) } } },
        GetChildren: () => []
    });

    // Exploiter globals
    lua.global.set("isfile", () => false);
    lua.global.set("readfile", () => "");
    lua.global.set("writefile", () => {});
    lua.global.set("make_writeable", () => {});
    lua.global.set("getgenv", () => lua.global.get("_G"));
    lua.global.set("getreg", () => ({}));
    lua.global.set("getrenv", () => lua.global.get("_G"));
    lua.global.set("newproxy", () => ({}));

    // Task library
    lua.global.set("task", {
        wait: () => {},
        spawn: (f: any) => { if (typeof f === 'function') f(); },
        delay: () => {}
    });
  }

  private setupGGMocks(lua: LuaEngine) {
    const gg: any = {
      alert: () => 1,
      toast: () => {},
      setVisible: () => {},
      searchNumber: () => {},
      getResultsCount: () => 100,
      getResults: (count: number) => [],
      clearResults: () => {},
      addListItems: () => {},
      getValues: (items: any) => items,
      setValues: () => {},
      choice: () => 1,
      prompt: (items: any) => (Array.isArray(items) ? items.map(() => "1") : ["1"]),
      require: () => {},
      getFile: () => "script.lua",
      isVisible: () => true,
      sleep: () => {},
      copyText: () => {},
      BUILD: 16142,
      VERSION: "101.1",
      TYPE_DWORD: 4,
      REGION_JAVA_HEAP: 1
    };
    lua.global.set("gg", gg);
  }

  private setupAntiVMBypasses(lua: LuaEngine) {
    const debug = {
      getinfo: () => ({
        source: "=[C]",
        short_src: "[C]",
        what: "C",
        name: "unknown",
        currentline: -1,
        nups: 0,
        linedefined: -1,
        lastlinedefined: -1
      }),
      getupvalue: () => null,
      setupvalue: () => {},
      sethook: () => {},
    };
    lua.global.set("debug", debug);

    const os = lua.global.get("os");
    if (os) {
      os.exit = () => console.log("os.exit bypass");
      os.execute = () => 0;
    }
  }
}

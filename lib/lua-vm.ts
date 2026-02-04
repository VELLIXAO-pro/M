import { LuaFactory, LuaEngine } from "wasmoon";

export class LuaVM {
  private factory: LuaFactory;
  private capturedCode: Set<string> = new Set();

  constructor() {
    this.factory = new LuaFactory();
  }

  private addCaptured(code: string) {
    if (typeof code === 'string' && code.length > 10) {
      // Avoid capturing extremely common short strings
      this.capturedCode.add(code);
    }
  }

  async run(sourceCode: string, onLog?: (msg: string) => void) {
    this.capturedCode = new Set();
    const lua = await this.factory.createEngine();

    try {
      this.setupHooks(lua, onLog);
      this.setupGGMocks(lua);

      try {
        await lua.doString(sourceCode);
      } catch (err) {
        if (onLog) onLog(`[VM Error] ${err}`);
      }

      const captured = Array.from(this.capturedCode);
      if (captured.length > 0) {
        // Return the most complex looking piece (longest string that isn't the original)
        return captured.sort((a, b) => b.length - a.length)[0];
      }

      return sourceCode;
    } finally {
      lua.global.close();
    }
  }

  private setupHooks(lua: LuaEngine, onLog?: (msg: string) => void) {
    const self = this;

    lua.global.set("print", (...args: any[]) => {
      const msg = args.map(a => String(a)).join("\t");
      if (onLog) onLog(`[Lua Print] ${msg}`);
    });

    // Correctly hook loadstring: must return a function
    lua.global.set("loadstring", (str: string) => {
      self.addCaptured(str);
      if (onLog) onLog(`[Hook] loadstring intercepted (${str.length} bytes)`);
      // Return a function that executes the string when called
      return () => {
        return lua.doStringSync(str);
      };
    });

    // Correctly hook load
    lua.global.set("load", (chunk: any) => {
      let str = "";
      if (typeof chunk === 'string') {
        str = chunk;
      } else if (typeof chunk === 'function') {
        try {
          let part = chunk();
          while (part) {
            str += part;
            part = chunk();
          }
        } catch (e) {}
      }

      if (str) {
        self.addCaptured(str);
        if (onLog) onLog(`[Hook] load intercepted (${str.length} bytes)`);
        return () => {
          return lua.doStringSync(str);
        };
      }
      return null;
    });

    lua.global.set("pcall", (f: any, ...args: any[]) => {
      try {
        if (typeof f === 'function') {
          const res = f(...args);
          return [true, res];
        } else if (typeof f === 'string') {
          self.addCaptured(f);
          const res = lua.doStringSync(f);
          return [true, res];
        }
      } catch (e) {
        return [false, String(e)];
      }
      return [false, "Invalid pcall target"];
    });
  }

  private setupGGMocks(lua: LuaEngine) {
    const gg: any = {
      alert: (msg: string) => {},
      toast: (msg: string) => {},
      setVisible: () => {},
      searchNumber: () => {},
      getResults: () => [],
      clearResults: () => {},
      addListItems: () => {},
      getValues: (items: any) => items,
      setValues: () => {},
      choice: () => 1,
      prompt: (items: string[]) => items.map(() => ""),
      require: () => {},
      getFile: () => "script.lua",
      EXT_STORAGE: "/sdcard",
      PACKAGE: "com.example.game",
      REGION_JAVA_HEAP: 1,
      REGION_C_HEAP: 2,
      TYPE_DWORD: 4,
      TYPE_FLOAT: 16,
    };
    lua.global.set("gg", gg);
  }
}

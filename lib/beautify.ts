export function beautifyLua(code: string): string {
  if (!code) return "";
  if (code.startsWith("\x1bLua")) return code; // Don't beautify bytecode

  // Step 1: Decode escape sequences
  let decoded = code;

  // 1.1: Decode decimal escape sequences like \104\101\108\108\111
  decoded = decoded.replace(/\\(\d{1,3})/g, (match, p1) => {
    const charCode = parseInt(p1, 10);
    if (charCode >= 32 && charCode <= 126) {
      return String.fromCharCode(charCode);
    }
    return match;
  });

  // 1.2: Decode hex escape sequences like \x68\x65\x6c\x6c\x6f
  decoded = decoded.replace(/\\x([0-9a-fA-F]{2})/g, (match, p1) => {
    const charCode = parseInt(p1, 16);
    if (charCode >= 32 && charCode <= 126) {
      return String.fromCharCode(charCode);
    }
    return match;
  });

  // 1.3: Simplify common string concatenations like "a" .. "b"
  // Only handle empty-looking or redundant quotes
  decoded = decoded.replace(/"\s*\.\.\s*"/g, "");
  decoded = decoded.replace(/'\s*\.\.\s*'/g, "");

  // 1.4: Handle escaped newlines and tabs
  decoded = decoded.replace(/\\n/g, "\n");
  decoded = decoded.replace(/\\t/g, "\t");

  // Step 2: Basic indentation and formatting
  let indent = 0;
  const lines = decoded.split(/\r?\n/);
  const result = lines.map(line => {
    let trimmed = line.trim();
    if (!trimmed) return "";

    // Decrease indent for closing keywords
    // Keywords: end, else, elseif, until, }, )
    if (trimmed.match(/^(end|else|elseif|\}|until|\))/)) {
      indent = Math.max(0, indent - 1);
    }

    const indentedLine = '  '.repeat(indent) + trimmed;

    // Increase indent for opening keywords
    // Keywords: if, while, for, function, repeat, do, else, elseif, {, (
    // We check if it's the start of a block and NOT followed by 'end' on the same line
    const isOpener = trimmed.match(/^(if|while|for|function|repeat|local\s+function|do|else|elseif|\{|\()/);
    const isClosedOnSameLine = trimmed.match(/\s+end\s*;?$/) || trimmed.match(/until\s+/) || (trimmed.includes("{") && trimmed.includes("}"));

    if (isOpener && !isClosedOnSameLine) {
      indent++;
    }

    return indentedLine;
  });

  // Step 3: Cleanup excessive newlines
  return result.filter((l, i, arr) => !(l === "" && arr[i-1] === "")).join('\n');
}

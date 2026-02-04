export function beautifyLua(code: string): string {
  // Step 1: Decode escape sequences like \104\101\108\108\111
  let decoded = code.replace(/\\(\d{1,3})/g, (match, p1) => {
    const charCode = parseInt(p1, 10);
    if (charCode >= 32 && charCode <= 126) {
      return String.fromCharCode(charCode);
    }
    return match;
  });

  // Step 2: Basic indentation
  let indent = 0;
  const lines = decoded.split('\n');
  const result = lines.map(line => {
    let trimmed = line.trim();

    // Decrease indent for closing keywords
    if (trimmed.match(/^(end|else|elseif|\}|until)/)) {
      indent = Math.max(0, indent - 1);
    }

    const indentedLine = '  '.repeat(indent) + trimmed;

    // Increase indent for opening keywords
    // We avoid incrementing if the line also ends the block (e.g. function() end)
    if (trimmed.match(/^(if|while|for|function|repeat|local\s+function|do|else|elseif|\{)/) && !trimmed.match(/end\s*;?$/) && !trimmed.match(/until/)) {
      indent++;
    }

    return indentedLine;
  });

  return result.join('\n');
}

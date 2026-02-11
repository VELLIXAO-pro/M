export const fancyStyles = {
  doubleStruck: "𝔸𝔹ℂ𝔻𝔼𝔽𝔾ℍ𝕀𝕁𝕂𝕃𝕄ℕ𝕆ℙℚℝ𝕊𝕋𝕌𝕍𝕎𝕏𝕐ℤ𝕒𝕓𝕔𝕕𝕖𝕗𝕘𝕙𝕚𝕛𝕜𝕝𝕞𝕟𝕠𝕡𝕢𝕣𝕤𝕥𝕦𝕧𝕨𝔵𝕪𝕫",
  script: "𝓐𝓑𝓒𝓓𝓔𝓕𝓖𝓗𝓘𝓙𝓚𝓛𝓜𝓝𝓞𝓟𝓠𝓡𝓢𝓣𝓤𝓥𝓦𝓧𝓨𝓩𝓪𝓫𝓬𝓭𝓮𝓯𝓰𝓱𝓲𝓳𝓴𝓵𝓶𝓷𝓸𝓹𝓺𝓻𝓼𝓽𝓾𝓿𝔀𝔁𝔂𝔃",
  bold: "𝐀𝐁𝐂𝐃𝐄𝐅𝐆𝐇𝐈𝐉𝐊𝐋𝐌𝐍𝐎𝐏𝐐𝐑𝐒𝐓𝐔𝐕𝐖𝐗𝐘𝐙𝐚𝐛𝐜𝐝𝐞𝐟𝐠𝐡𝐢𝐣𝐤𝐥𝐦𝐧𝐨𝐩𝐪𝐫𝐬𝐭𝐮𝐯𝐰𝐱𝐲𝐳",
  monospace: "𝙰𝙱𝙲𝙳𝙴𝙵𝙶𝙷𝙸𝙹𝙺𝙻𝙼𝙽𝙾𝙿𝚀𝚁𝚂𝚃𝚄𝚅𝚆𝚇𝚈𝚉𝚊𝚋𝚌𝚍𝚎𝚏𝚐𝚑𝚒𝚓𝚔𝚕𝕞𝚗𝚘𝚙𝚚𝚛𝚜𝚝𝚞𝚟𝚠𝚡𝚢𝚣",
  fraktur: "𝔄𝔅ℭ𝔇𝔈𝔉𝔊ℌℑ𝔍𝔎𝔏𝔐𝔑𝔒𝔓𝔔ℜ𝔖𝔗𝔘𝔙𝔚𝔛𝔜ℨ𝔞𝔟𝔠𝔡𝔢𝔣𝔤𝔥𝔦𝔧𝔨𝔩𝔪𝔫𝔬𝔭𝔮𝔯𝔰𝔱𝔲𝔳𝔴𝔵𝔶𝔷",
};

const normalChars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";

export function convertToFancy(text: string, style: keyof typeof fancyStyles) {
  const mapping = fancyStyles[style];
  if (!mapping) return text;

  const mappingArray = Array.from(mapping);
  return Array.from(text)
    .map((char) => {
      const index = normalChars.indexOf(char);
      return index !== -1 ? mappingArray[index] : char;
    })
    .join("");
}

export function decorateText(text: string, emoji: string, mode: 'interleave' | 'wrap' | 'border') {
  if (!emoji) return text;
  const textArray = Array.from(text);
  if (mode === 'interleave') {
    return textArray.join(emoji);
  } else if (mode === 'wrap') {
    return textArray.map(c => `${emoji}${c}${emoji}`).join("");
  } else {
    return `${emoji} ${text} ${emoji}`;
  }
}

export function mixEmojis(text: string, emoji1: string, emoji2: string) {
  if (!emoji1 && !emoji2) return text;
  if (!emoji1) return decorateText(text, emoji2, 'interleave');
  if (!emoji2) return decorateText(text, emoji1, 'interleave');

  return Array.from(text).map((char, i) => `${char}${i % 2 === 0 ? emoji1 : emoji2}`).join("");
}

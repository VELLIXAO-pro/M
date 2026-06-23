"use strict";

export const BYPASS_SERVICES = [
  { name: "Work.ink", pattern: /work\.ink/ },
  { name: "Lootlabs", pattern: /lootdest\.org|links\.lootlabs\.gg|loot-links\.com|loot-link\.com/ },
  { name: "Linkvertise", pattern: /linkvertise\.com/ },
  { name: "Cuty", pattern: /cuttlinks\.com/ },
  { name: "Lockr", pattern: /lockr\.so/ },
  { name: "Rekonise", pattern: /rekonise\.com/ },
  { name: "Shortfly", pattern: /shrtslug\.biz|biovetro\.net|technons\.com|yrtourguide\.com|tournguide\.com/ },
];

export function identifyService(url: string) {
  for (const service of BYPASS_SERVICES) {
    if (service.pattern.test(url)) {
      return service.name;
    }
  }
  return "Unknown";
}

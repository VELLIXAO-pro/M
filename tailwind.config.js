/** @type {import('tailwindcss').Config} */
module.exports = {
  content: [
    "./pages/**/*.{js,ts,jsx,tsx,mdx}",
    "./components/**/*.{js,ts,jsx,tsx,mdx}",
    "./app/**/*.{js,ts,jsx,tsx,mdx}",
  ],
  theme: {
    extend: {
      colors: {
        samurai: {
          black: "#1a1a1a",
          red: "#dc143c",
          gold: "#ffd700",
        },
      },
    },
  },
  plugins: [],
};

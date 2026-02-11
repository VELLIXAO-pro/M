import type { Metadata } from "next";
import { Sawarabi_Mincho } from "next/font/google";
import "./globals.css";

const sawarabiMincho = Sawarabi_Mincho({
  weight: "400",
  subsets: ["latin"],
  variable: "--font-samurai",
});

export const metadata: Metadata = {
  title: "Samurai Emoji Mixer",
  description: "Generate custom emoji text and fonts with Samurai style",
};

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
  return (
    <html lang="id">
      <body
        className={`${sawarabiMincho.variable} font-samurai antialiased`}
      >
        {children}
      </body>
    </html>
  );
}

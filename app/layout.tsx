import type { Metadata } from "next";
import { Sawarabi_Mincho, Permanent_Marker } from "next/font/google";
import "./globals.css";

const sawarabiMincho = Sawarabi_Mincho({
  weight: "400",
  variable: "--font-sawarabi",
  subsets: ["latin"],
});

const permanentMarker = Permanent_Marker({
  weight: "400",
  variable: "--font-marker",
  subsets: ["latin"],
});

export const metadata: Metadata = {
  title: "VELLTOOLS BYPASSER",
  description: "Advanced link bypasser with Samurai theme",
};

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
  return (
    <html
      lang="en"
      className={`${sawarabiMincho.variable} ${permanentMarker.variable} h-full antialiased dark`}
    >
      <body className="min-h-full flex flex-col bg-[#1a1a1a] text-white">
        {children}
      </body>
    </html>
  );
}

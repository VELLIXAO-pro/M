import type { Metadata } from "next";
import { Sawarabi_Mincho, Permanent_Marker } from "next/font/google";
import "./globals.css";

const sawarabiMincho = Sawarabi_Mincho({
  weight: "400",
  subsets: ["latin"],
  variable: "--font-sawarabi",
});

const permanentMarker = Permanent_Marker({
  weight: "400",
  subsets: ["latin"],
  variable: "--font-marker",
});

export const metadata: Metadata = {
  title: "Samurai Tools - GG Script Hub",
  description: "Professional Game Guardian Tools and Scripts",
};

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
  return (
    <html lang="en">
      <body
        className={`${sawarabiMincho.variable} ${permanentMarker.variable} antialiased bg-samurai-black text-white font-sawarabi`}
      >
        {children}
      </body>
    </html>
  );
}

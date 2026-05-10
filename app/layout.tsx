import type { Metadata } from "next";
import "./globals.css";

export const metadata: Metadata = {
  title: "VELL RAW DOWNLOADER",
  description: "Download raw content from restricted links",
};

export default function RootLayout({
  children,
}: Readonly<{
  children: React.ReactNode;
}>) {
  return (
    <html lang="en">
      <head>
        <link
          href="https://fonts.googleapis.com/css2?family=Sawarabi+Mincho&display=swap"
          rel="stylesheet"
        />
      </head>
      <body className="antialiased overflow-x-hidden">{children}</body>
    </html>
  );
}

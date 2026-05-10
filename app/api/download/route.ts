import { NextRequest, NextResponse } from "next/server";

export async function GET(request: NextRequest) {
  const searchParams = request.nextUrl.searchParams;
  const url = searchParams.get("url");

  if (!url) {
    return NextResponse.json({ error: "URL is required" }, { status: 400 });
  }

  // Basic SSRF protection and protocol validation
  try {
    const parsedUrl = new URL(url);
    if (!["http:", "https:"].includes(parsedUrl.protocol)) {
      return NextResponse.json({ error: "Invalid protocol" }, { status: 400 });
    }

    // Check if the hostname is an IP address (rudimentary SSRF protection for local network)
    const hostname = parsedUrl.hostname;
    if (/^(127\.|10\.|172\.(1[6-9]|2[0-9]|3[0-1])\.|192\.168\.)/.test(hostname) || hostname === 'localhost') {
      return NextResponse.json({ error: "Access to local network is restricted" }, { status: 403 });
    }
  } catch (e) {
    return NextResponse.json({ error: "Invalid URL" }, { status: 400 });
  }

  try {
    // We use a non-browser User-Agent to bypass Luarmor's browser-targeted redirects/404s.
    // Confirmed via curl that empty or generic UAs work.
    const response = await fetch(url, {
      headers: {
        "User-Agent": "GameGuardian/101.1",
      },
    });

    if (!response.ok) {
      return NextResponse.json(
        { error: `Failed to fetch: ${response.statusText}` },
        { status: response.status }
      );
    }

    // Stream the response for efficiency
    const { body } = response;
    const filename = url.split("/").pop() || "script.lua";

    return new NextResponse(body, {
      status: 200,
      headers: {
        "Content-Type": "text/plain",
        "Content-Disposition": `attachment; filename="${filename}"`,
      },
    });
  } catch (error: any) {
    return NextResponse.json(
      { error: error.message || "Internal Server Error" },
      { status: 500 }
    );
  }
}

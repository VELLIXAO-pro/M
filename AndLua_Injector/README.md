# AndLua+ Samurai Injector (Non-Root Debuggable)

This project is an injector for AndLua+ designed to search and modify memory of other Android applications in a non-root environment using the `debuggable` feature.

## Features
- **Auto Start Game**: Automatically launches the target package using Android Intents.
- **Java Heap Search**: Specifically targets Java Heap (dalvik-main) regions for memory searching.
- **GG-Style UI**: Familiar Game Guardian-like interface with search and write capabilities.
- **Non-Root Support**: Leverages `run-as` for access to debuggable applications.

## Requirements
1. **AndLua+ IDE**: Must be installed on your Android device.
2. **Debuggable Target**: The target application must have `android:debuggable="true"` in its `AndroidManifest.xml`.
3. **Same UID / Shizuku**: On some Android versions, you may need to run this within a Virtual Space or use a shell wrapper (like Shizuku) to allow `run-as` to work from within an app.

## Project Structure
- `main.lua`: The entry point and main logic.
- `layout.aly`: The UI definition (Samurai Theme).
- `MemoryTools.lua`: Core memory manipulation library using shell commands.

## How to Use
1. Copy the `AndLua_Injector` folder to your AndLua+ project directory (usually `/sdcard/AndLua/project/`).
2. Open the project in AndLua+.
3. Enter the package name (e.g., `com.asobimo.aurcusonline.wx`).
4. Click **START GAME**.
5. Once the game is running, enter a value and click **SEARCH**.
6. Select results from the list and use **WRITE ALL** to modify them.

## Technical Details
The injector uses `/proc/[pid]/maps` to identify memory regions and `/proc/[pid]/mem` for reading/writing. In non-root mode, it wraps calls using `run-as <package>` to gain the necessary permissions for debuggable targets.

---
*Created by Jules for HAISE39*

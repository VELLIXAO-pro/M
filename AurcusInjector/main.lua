require "import"
import "android.widget.*"
import "android.view.*"
import "android.content.*"
import "android.net.Uri"
import "android.provider.Settings"
import "android.app.Activity"
import "android.os.Build"

-- Layout file
layout = import "layout"

activity.setContentView(loadlayout(layout))

-- Function to check and request Overlay Permission
function checkOverlayPermission()
  if Build.VERSION.SDK_INT >= 23 then
    if not Settings.canDrawOverlays(activity) then
      local intent = Intent(Settings.ACTION_MANAGE_OVERLAY_PERMISSION)
      intent.setData(Uri.parse("package:" .. activity.getPackageName()))
      activity.startActivityForResult(intent, 123)
      Toast.makeText(activity, "Izinkan Overlay untuk Mod Menu", Toast.LENGTH_SHORT).show()
      return false
    end
  end
  return true
end

-- Start Floating Window
function startModMenu()
  if checkOverlayPermission() then
    -- Start service or floating window logic
    -- In AndLua+, usually we use a service to maintain the float
    activity.startService(Intent(activity, LuaService).putExtra("luaPath", activity.getLuaDir() .. "/float.lua"))
    Toast.makeText(activity, "Mod Menu Dimulai", Toast.LENGTH_SHORT).show()
  end
end

-- Button Listeners (Assuming buttons are in layout.aly)
btn_start.onClick = function()
  startModMenu()
end

btn_launch_game.onClick = function()
  local packagename = "com.asobimo.aurcusonline.wx"
  local intent = activity.getPackageManager().getLaunchIntentForPackage(packagename)
  if intent then
    activity.startActivity(intent)
  else
    Toast.makeText(activity, "Game tidak ditemukan!", Toast.LENGTH_SHORT).show()
  end
end

require "import"
import "android.app.*"
import "android.os.*"
import "android.widget.*"
import "android.view.*"
import "android.content.*"
import "android.net.Uri"
import "android.provider.Settings"

-- Theme and title
activity.setTheme(android.R.style.Theme_DeviceDefault_NoActionBar)

function checkPermission()
  if Build.VERSION.SDK_INT >= 23 then
    if not Settings.canDrawOverlays(this) then
      local intent = Intent(Settings.ACTION_MANAGE_OVERLAY_PERMISSION)
      intent.setData(Uri.parse("package:" .. activity.getPackageName()))
      activity.startActivityForResult(intent, 0)
      return false
    end
  end
  return true
end

function onActivityResult(requestCode, resultCode, data)
  if checkPermission() then
    startFloat()
  end
end

function startFloat()
  local luaPath = activity.getLuaPath():gsub("main.lua", "float.lua")
  local intent = Intent()
  intent.setClassName(activity.getPackageName(), "com.androlua.LuaService")
  intent.putExtra("luaPath", luaPath)
  activity.startService(intent)
  -- activity.finish() -- Keep activity for now to ensure service starts
  print("Service started successfully")
end

if checkPermission() then
  startFloat()
else
  print("Mohon izinkan overlay permission untuk menjalankan script ini.")
end

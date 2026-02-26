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
  -- Using 'arg' with filename is the most compatible way in AndLua+
  local intent = Intent()
  intent.setClassName(activity.getPackageName(), "com.androlua.LuaService")
  intent.putExtra("arg", "service.lua")
  activity.startService(intent)

  -- We can finish the activity now that the service is started
  activity.finish()
  print("Metasploit service started.")
end

if checkPermission() then
  startFloat()
else
  print("Mohon izinkan overlay permission untuk menjalankan script ini.")
end

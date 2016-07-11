
package net.sourceforge.czt.circus2zcsp;

public class Debug
{
  private static boolean debug_ = true;
  
  public static void turnOffDebug() 
  {
    debug_ = false;
  }
  
  public static boolean isDebugMode()
  {
    return debug_;
  }
  
  public static void debug_print(String str)
  {
    if (debug_) {
      System.out.println("[DEBUG] " + str);
    }
  }
  
  public static void debug_format_print(String fmt, Object... args)
  {
    if (debug_) {
      String str = String.format(fmt, args);
      debug_print(str);
    }
  }
}

/*
 * A definition used in map to identify which part of data is maintained
 * 
 * map is a type of Hashmap(Pair<String, String, Type>, String) 
 *     (Pair<sectionname, procname, CMT_PROCNAME>, procname) 
 *      - e.g. (Pair<"Fuel_Pump", "Pump", CMT_PROCNAME>, "Pump")
 *     (Pair<procname, stateparaname, CMT_STATENAME>, stateparaname) 
 *      - e.g. (Pair<"Pump", "PState", CMT_STATENAME>, "PState")
 *     (Pair<procname, varname, CMT_STATEVAR>, varname) 
 *      - e.g. (Pair<"Pump", "fuleQ", CMT_STATEVAR>, "fuelQ")
 *     (Pair<procname, "", CMT_GANUMBER>, "num") 
 *      - e.g. (Pair<"Pump", "", CMT_GANUMBER>, "0")
 *     (Pair<procname, original var or schema name or action name, CMT_NAMEREP>, repname) 
 *      - e.g. (Pair<"Pump", "PState", CMT_NAMEREP>, "Pump_PState")
 *      - e.g. (Pair<"Pump", "fuelQ", CMT_NAMEREP>, "Pump_fuelQ")
 *      - e.g. (Pair<"Pump", "PumpIdle", CMT_NAMEREP>, "Pump_PumpIdle")
 *     (Pair<"", "", CMT_VARNUMBER>, "num")
 *      - e.g. (Pair<"", "", CMT_VARNUMBER>, "0")
 *     (Pair<"", chnname, CMT_CHNDECL>, "exp")
 *      - e.g. (Pair<"", "c", CMT_CHNDECL>, "{1,3}.{green,red}")
 *     (Pair<schtype_name, varname, CMT_SCHTYPE>, "exp")
 *      - e.g. (Pair<"Tsch", "x", CMT_SCHTYPE>, "{1,3}")
 *      - e.g. (Pair<"Tsch", "y", CMT_SCHTYPE>, "{green}")
 */
package net.sourceforge.czt.circus2zcsp.data;

public enum CircusMapType {
  CMT_PROCNAME,         // This is process name
  CMT_STATENAME,        // This is state paragraph name
  CMT_STATEVAR,         // State variables name within a process
  CMT_GANUMBER,         // the number to count the schema name for guarded action, 
                        // from 0
  CMT_VARNUMBER,        // the number to count the Var processes from 0. It is global number 
                        // and doesn't restrict in process
  CMT_NAMEREP,          // Name map used to replace the state variable and 
                        // paragraph name by prefixing process name 
  CMT_NAMESET,          // NameSet paragraph 
  CMT_CHNDECL,          // channel declaration
  CMT_FREETYPE,         // a free type T
  CMT_FREETYPE_CONST,   // a free type constant
  CMT_FREETYPE_CONSTRUCTOR, // a free type constructor
  CMT_GIVENTYPE,         // a free type T
  CMT_SCHTYPE;          // global schema type
  
  public String toString()
  {
    //only capitalize the first letter
    String s = super.toString();
    return s.substring(0, 1) + s.substring(1).toLowerCase();
  }
}

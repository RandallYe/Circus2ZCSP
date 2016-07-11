
package net.sourceforge.czt.circus2zcsp.data;

public enum VariableRenameSchema {
  VRS_APPEND_INSTROKE,  // append a ? after the name
  VRS_APPEND_OUTSTROKE,  // append a ! after the name
  VRS_NEXT_OUTSTROKE,  // nextstroke is replaced by outstroke. For example, in specification, lv' in post => lv!
  VRS_APPEND_NEXTSTROKE,  // append a prime (') after the name
  VRS_ACTION_RENAME,    // action rename schema A[a:=b] - 'a' event in A will be renamed to 'b'
  VRS_NAME_REPLACE,     // replace all names
  VRS_CHN_RENAME,       // channel renaming such as c to c_i.i
  VRS_RWT_RENAME,       // renaming in the rewrite of Circus BasicProcess 
  VRS_V_TO_EXP_RENAME,  // rename a variable to an expression (used in rewriting of parametrised action invocation (x:T@A)(e)).
  VRS_ZNAME_RENAME,     // replace by ZName instead of String
  VRS_UNKNOWN;

  public static final String VRS_APPEND_INSTROKE_PATTERN = "{0}?";
  
  public String toString()
  {
    // only capitalize the first letter
    String s = super.toString();
    return s.substring(0, 1) + s.substring(1).toLowerCase();
  }
}


package net.sourceforge.czt.circus2zcsp.data;

import net.sourceforge.czt.base.ast.Term;

/**
 * A local variable entry in the context
 * 
 * (variable name, its type, from variable block or input prefix, its corresponding numbering)
 * @author rye
 *
 */
public class LocalVariableEntry
{
  private final String name_;
  private final Term type_;
  private final boolean varblock_;
  private final String n_;
  
  public LocalVariableEntry(String name, Term t, boolean varblock, String n)
  {
    name_ = name;
    type_ = t;
    varblock_ = varblock;
    n_ = n;
  }
  
  public boolean isFromVarBlock()
  {
    return varblock_;
  }
  
  public String getName()
  {
    return name_;
  }
  
  public Term getType()
  {
    return type_;
  }
  
  public String getNumber()
  {
    return n_;
  }
  
  public boolean name_equals(Object other)
  {
    if (other == null || ! (other instanceof LocalVariableEntry))
      return false;
    LocalVariableEntry p = (LocalVariableEntry) other;
    return name_.equals(p.getName());
  }
  
  public boolean name_equals(String var)
  {
    return name_.equals(var);
  }
  
  @Override
  public int hashCode()
  {
    return name_.hashCode() + type_.hashCode() + n_.hashCode();
  }

  @Override
  public boolean equals(Object other)
  {
    if (other == null || ! (other instanceof LocalVariableEntry))
      return false;
    LocalVariableEntry p = (LocalVariableEntry) other;
    return name_.equals(p.getName()) && 
        type_.equals(p.getType()) && 
        varblock_ == p.isFromVarBlock() &&
        n_.equals(p.getNumber());
  }

  @Override
  public String toString()
  {
    return "(" + name_ + "," + type_.toString() + "," + 
        (varblock_?"Variable Block":"Input Prefix") + "," + n_ + ")";
  }
}

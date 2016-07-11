/*
 * VariableRenamingVisitor.java
 * A visitor for the variable and schema name replacing in basic process
 * to avoid name conflict according to the map between original name and the
 * name prefixed by process name
 */

package net.sourceforge.czt.circus2zcsp.visitor;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus2zcsp.data.CircusSpecMap;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.visitor.NameVisitor;
import net.sourceforge.czt.z.visitor.ZNameVisitor;

public class VariableRenamingVisitor
    implements
      TermVisitor<Object>,
      NameVisitor<Object>,
      ZNameVisitor<Object>
{
  private final boolean debug_ = false;

  // a map from original variable or schema name to replaced new name
  private CircusSpecMap map_ = null;

  private String proname_ = null;

  public VariableRenamingVisitor(String proName, CircusSpecMap map)
  {
    map_ = map;
    proname_ = proName;
  }

  public void debug_print(String str)
  {
    if (debug_) {
      System.out.println(str);
    }
  }

  @Override
  public Object visitName(Name term)
  {
    debug_print(term.toString());
    return null;
  }

  /**
   * Traverse the whole tree under this term
   */
  @Override
  public Object visitTerm(Term zedObject)
  {
//		System.out.println("visitTerm: " + zedObject.toString());
    Object[] args = zedObject.getChildren();
    for (int i = 0; i < args.length; i++) {
      if (args[i] instanceof Term) {
        args[i] = ((Term) args[i]).accept(this);
      }
    }
    return null;
  }

  /**
   * replace name in ZName according to the map in map_
   */
  @Override
  public Object visitZName(ZName term)
  {
    String oldname = term.getWord();
    debug_print("visitZName in Circus2z: " + oldname);

    // One case is the name equal to the name to be replaced

    Pair<String, Term> p = map_.getRep(proname_, oldname);
    String newname = p == null?null:p.getFirst();
    if (newname != null) {
      debug_print("New Name for [" + oldname + "]: " + newname);
      term.setWord(newname);
    }
    else {
      // Another case is the name including the name to be replaced
      // For example, \Delta State will have the \Delta in first index and state name in the
      // following
      char dec = term.getWord().charAt(0);
      // ZChar.DELTA
      char delta = new Character('\u0394');
//       ZChar.XI
      char xi = new Character('\u039E');
      if (dec == delta || dec == xi) {
        p = map_.getRep(proname_, oldname.substring(1));
        newname = p.getFirst();
        if (newname != null) {
          term.setWord(oldname.replaceFirst(oldname.substring(1), newname));
          debug_print("New Name for [" + oldname + "]: " + term.getWord());
        }
      }
    }

    return null;
  }
}

/*
 * This visitor is to get the ZName list in a term. It can be used to 
 * get a set of local variables or state variables for a term
 */
package net.sourceforge.czt.circus2zcsp.visitor;

import java.util.HashSet;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.visitor.ZNameVisitor;

/**
 * 
 * @author rye
 *
 */
public class ZNameSetVisitor implements TermVisitor<Object>, ZNameVisitor<Object>
{
  // default initial capacity is 128
  private final Set<String> sstr_ = new HashSet<String>(/*128*/);
  
  @Override
  public Object visitZName(ZName term)
  {
    // exclude the operators
    OperatorName on = term.getOperatorName();
    if(on != null) {
      String result = Circus2ZCSPUtils.getOperator(on);
      if(Circus2ZCSPUtils.hasOpArg(term) || result != "") {
        return null;
      }
    }
    
    // this name is with strokes
    String name = Circus2ZCSPUtils.termToString(term); //term.toString();
    sstr_.add(name);
    
    // we also add the name without strokes
    sstr_.add(term.getWord());
    
    return null;
  }

  @Override
  public Object visitTerm(Term zedObject)
  {
    // System.out.println("visitTerm: " + zedObject.toString());
    Object[] args = zedObject.getChildren();
    for (int i = 0; i < args.length; i++) {
      if (args[i] instanceof Term) {
        args[i] = ((Term) args[i]).accept(this);
      }
    }
    return null;
  }

  /**
   * Get a set of name
   * @return Set<String>
   */
  public Set<String> getStrSet() {
    return sstr_;
  }
  
  public void clear() {
    sstr_.clear();
  }
  
  public String toString() {
    return sstr_.toString();
  }
}

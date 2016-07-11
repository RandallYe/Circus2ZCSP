/*
 * Return an expression string in which each expression is separated
 * by dot and input expressions are put in ahead and outputs in tail
 *
 * For example, 
 *      o!:\nat in Read = [\Delta S; o!:\nat | pred]
 *    to
 *      Nat
 * For example,
 *      i?:\nat; o!:\nat in Write = [\Delta S; i?:\nat; o!:\nat | pred]
 *    to
 *      Nat.Nat
 */

package net.sourceforge.czt.circus2zcsp.visitor;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.NumStroke;
import net.sourceforge.czt.z.ast.OutStroke;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;

public class InOutVisitor implements TermVisitor<String>, VarDeclVisitor<String>
{
  private String channel_expr_;
  private PrintCircusZToCSPVisitor cspvisitor_ = new PrintCircusZToCSPVisitor();

  public InOutVisitor()
  {
    channel_expr_ = new String();
  }

  @Override
  public String visitTerm(Term zedObject)
  {
    Object[] args = zedObject.getChildren();
    for (int i = 0; i < args.length; i++) {
      if (args[i] instanceof Term) {
        args[i] = ((Term) args[i]).accept(this);
      }
    }
    return channel_expr_;
  }

  @Override
  public String visitVarDecl(VarDecl term)
  {
    for (Name zn : term.getZNameList()) {
      if (zn instanceof ZName) {
        for (net.sourceforge.czt.z.ast.Stroke sk : ((ZName) zn).getZStrokeList()) {
          // ? input parameters
          // TODO: how to deal with the type of variable (expr, such as \nat since in CSP, there
          // is not this integer type)
          if (sk instanceof InStroke) {
            cspvisitor_.clear();
            term.getExpr().accept(cspvisitor_);
            if (channel_expr_.equals("") || channel_expr_ == null)
              channel_expr_ += cspvisitor_.toString();
            else
              channel_expr_ += "." + cspvisitor_.toString();
          }
          // !
          else if (sk instanceof OutStroke) {
            cspvisitor_.clear();
            term.getExpr().accept(cspvisitor_);
            if (channel_expr_.equals("") || channel_expr_ == null)
              channel_expr_ += cspvisitor_.toString();
            else
              channel_expr_ += "." + cspvisitor_.toString();
          }
          // '
          else if (sk instanceof NextStroke) {

          }
          //
          else if (sk instanceof NumStroke) {

          }
        }
      }
    }
    return channel_expr_;
  }

}

package net.sourceforge.czt.circus2zcsp.visitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Stack;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circus.ast.CircusNameSet;
import net.sourceforge.czt.circus.ast.Communication;
import net.sourceforge.czt.circus.ast.DotField;
import net.sourceforge.czt.circus.ast.InputField;
import net.sourceforge.czt.circus.ast.QualifiedDecl;
import net.sourceforge.czt.circus.ast.SigmaExpr;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.circus2zcsp.util.RefExprKind;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.CondExpr;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Expr0N;
import net.sourceforge.czt.z.ast.Expr1;
import net.sourceforge.czt.z.ast.Expr2;
import net.sourceforge.czt.z.ast.ExprPred;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.QntExpr;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.visitor.RefExprVisitor;
import net.sourceforge.czt.zpatt.ast.JokerExpr;

/**
 * Substitute variables by an expr 
 *      used in P[ex,ey,.../x,y,...] or A[ex,ey,.../x,y,...]
 * @author rye
 *
 */
public class SubstVariableToExpVisitor
  implements
  TermVisitor<Object>,
  RefExprVisitor<Object>
{
  private Visitor<Object> visitor_ = this;
  private List<ZName> lst_name_ = new ArrayList<ZName>();
  private List<Expr> lst_expr_ = new ArrayList<Expr>();
  private Stack<Term> stack_parent_ = new Stack<Term>();
  
  public SubstVariableToExpVisitor(ZName name, Expr expr)
  {
    lst_name_.add(name);
    lst_expr_.add(expr);
  }
  
  public SubstVariableToExpVisitor(List<ZName> lstName, List<Expr> lstExpr) 
  {
    lst_name_.addAll(lstName);
    lst_expr_.addAll(lstExpr);
  }
  
  @Override
  public Object visitTerm(Term zedObject)
  {
    Object[] args = zedObject.getChildren();
    for (int i = 0; i < args.length; i++) {
      if (args[i] instanceof Term) {
        stack_parent_.push((Term)args[i]);
        args[i] = ((Term) args[i]).accept(this);
        stack_parent_.pop();
      }
    }
    return null;
  }

  @Override
  public Object visitRefExpr(RefExpr term)
  {
    // only substitute variable references
    RefExprKind kind = Circus2ZCSPUtils.getRefExprKind(term);
    switch (kind) {
      case REF: 
        {
          for(int i = 0; i < lst_name_.size(); i++) {
            if(Circus2ZCSPUtils.isEquals(lst_name_.get(i), term.getZName())) {
              Expr e = lst_expr_.get(i);
              Circus2ZCSPUtils.updateParentRef(stack_parent_, term, e);
            }
          }
        }
        break;
      case GEN_REF:
        {
          visitTerm(term);
        }
        break;
      case GEN_OP_APPL:
        break;
      case OP_APPL:
        break;
    }
    
    return null;
  }
  
  protected Object visit(Term t)
  {
    if (t != null) {
      stack_parent_.push(t);
      Object o = t.accept(visitor_);
      stack_parent_.pop();
      return o;
    }
    return null;
  }

//  /**
//   * update a RefExpr (r) in its parent by an expression (e)
//   * @param t - RefExpr to be replaced
//   * @param e - expression
//   */
//  private void updateParentRef(Expr r, Expr e)
//  {
//    Term parent;
//    if(stack_parent_.size() >= 2) {
//      parent = stack_parent_.get(stack_parent_.size() - 2);
//    }
//    else {
//      throw new CztException(Circus2ZCSPUtils.termToString(r) + " has no parent!");
//    }
//    
//    // if a RefExpr's parent is an expression as well,
//    if(parent instanceof Expr) {
//      if(parent instanceof Expr0N) {
//        ZExprList zel = ((Expr0N)parent).getZExprList();
//        for(int i = 0; i < zel.size(); i++) {
//          // replace r by e
//          if(zel.get(i).equals(r)) {
//            zel.remove(i);
//            zel.add(i, e);
//          }
//        }
//        ((Expr0N)parent).setExprList(zel);
//      }
//      else if(parent instanceof Expr1) {
//        if(((Expr1)parent).getExpr().equals(r)) {
//          ((Expr1)parent).setExpr(e);
//        }
//      }
//      else if(parent instanceof Expr2) {
//        if(((Expr2)parent).getLeftExpr().equals(r)) {
//          ((Expr2)parent).setLeftExpr(e);
//        }
//        
//        if(((Expr2)parent).getRightExpr().equals(r)) {
//          ((Expr2)parent).setRightExpr(e);
//        }
//      }
//      else if(parent instanceof CondExpr) {
////        Term pparent;
////        if(stack_parent_.size() >= 3) {
////          pparent = stack_parent_.get(stack_parent_.size() - 3);
////        }
////        else {
////          throw new CztException(Circus2ZCSPUtils.termToString(r) + "'s parent " + Circus2ZCSPUtils.termToString(parent) + "has no parent!");
////        }
//        
//        Expr le = ((CondExpr)parent).getLeftExpr();
//        Expr re = ((CondExpr)parent).getRightExpr();
//        // for CondExpr (if p then e1 else e2), there is no setExpr operations.
//        if(((CondExpr)parent).getLeftExpr().equals(r)) {
//          le = e;
//        }
//        
//        if(((CondExpr)parent).getRightExpr().equals(r)) {
//          re = e;
//        }
//        
//        CircusFactory fac = new net.sourceforge.czt.circus.impl.CircusFactoryImpl();
//        List<Expr> lstExpr = new ArrayList<Expr>();
//        lstExpr.add(le);
//        lstExpr.add(re);
//        CondExpr ce = fac.createCondExpr(((CondExpr)parent).getPred(), lstExpr);
//        // recursively to replace [e/r]
//        Term p = stack_parent_.pop();
//        updateParentRef((CondExpr)parent, ce);
//        // restore
//        stack_parent_.push(p);
//      }
//      else if(parent instanceof JokerExpr) {
//        throw new CztException(Circus2ZCSPUtils.termToString(r) + "'s parent should not be JokerExpr!");
//      }
//      else if(parent instanceof QntExpr) {
//        if (((QntExpr)parent).getExpr().equals(r)) {
//          ((QntExpr)parent).setExpr(e);
//        }
//      }
//      else if(parent instanceof SigmaExpr) {
//        if (((SigmaExpr)parent).getValue().equals(r)) {
//          ((SigmaExpr)parent).setValue(e);
//        }
//      }
//    }
//    else if(parent instanceof ZExprList) {
//      ZExprList zel = ((ZExprList)parent);
//      for(int i = 0; i < zel.size(); i++) {
//        if(zel.get(i).equals(r)) {
//          zel.remove(i);
//          zel.add(i, e);
//        }
//      }
//    }
//    else if(parent instanceof Decl) {
//      if(parent instanceof InclDecl) {
//        if(((InclDecl)parent).getExpr().equals(r)) {
//          ((InclDecl)parent).setExpr(e);
//        }
//      }
//      else if(parent instanceof QualifiedDecl) {
//        if(((QualifiedDecl)parent).getExpr().equals(r)) {
//          ((QualifiedDecl)parent).setExpr(e);
//        }
//      }
//      else if(parent instanceof VarDecl) {
//        if(((VarDecl)parent).getExpr().equals(r)) {
//          ((VarDecl)parent).setExpr(e);
//        }
//      }
//    }
//    else if(parent instanceof Communication) {
//      
//    }
//    else if(parent instanceof DotField) {
//      if(((DotField)parent).getExpr().equals(r)) {
//        ((DotField)parent).setExpr(e);
//      }
//    }
//    else if(parent instanceof InputField) {
//      throw new CztException(Circus2ZCSPUtils.termToString(r) + "'s parent should not be InputField!");
//    }
//    else if(parent instanceof Pred) {
//      if(parent instanceof ExprPred) {
//        if(((ExprPred)parent).getExpr().equals(r)) {
//          ((ExprPred)parent).setExpr(e);
//        }
//      }
//      else if(parent instanceof MemPred) {
//        if(((MemPred)parent).getLeftExpr().equals(r)) {
//          ((MemPred)parent).setLeftExpr(e);
//        }
//        
//        if(((MemPred)parent).getRightExpr().equals(r)) {
//          ((MemPred)parent).setRightExpr(e);
//        }
//      }
//    }
//    else if(parent instanceof CircusNameSet) {
//      throw new CztException(Circus2ZCSPUtils.termToString(r) + "'s parent should not be CircusNameSet!");
//    }
//    else {
//      throw new CztException(Circus2ZCSPUtils.termToString(r) + 
//          "'s parent should not be [" + parent.getClass()+ "] !");
//    }
//  }
}

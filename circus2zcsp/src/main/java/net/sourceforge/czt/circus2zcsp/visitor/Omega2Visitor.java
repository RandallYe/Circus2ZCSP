package net.sourceforge.czt.circus2zcsp.visitor;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.circus2zcsp.util.RefExprKind;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.ApplExprVisitor;
import net.sourceforge.czt.z.visitor.AxParaVisitor;

public class Omega2Visitor
  implements TermVisitor<Object>,
    ApplExprVisitor<Object>,
    AxParaVisitor<Object>
{

  private ZFactory fac_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
  /**
   * a list of schema names
   */
  private List<ZName> lstSchNames = new ArrayList<ZName>();
  
  @Override
  public Object visitTerm(Term zedObject)
  {
    Object[] args = zedObject.getChildren();
    for (int i = 0; i < args.length; i++) {
      if (args[i] instanceof Term) {
        args[i] = ((Term) args[i]).accept(this);
      }
    }
    return null;
  }

  /**
   * Transform e1 \symdiff e2 => (e1 \setminus e2) \cup (e2 \setminus e1)
   */
  @Override
  public Object visitApplExpr(ApplExpr term)
  {
    if(term.getMixfix()) {
      Expr opExpr = term.getLeftExpr();
      Expr expr = term.getRightExpr();
      if(opExpr instanceof RefExpr) {
        RefExpr re = (RefExpr) opExpr;
        // check operator
        if(Circus2ZCSPUtils.getRefExprKind(re) == RefExprKind.GEN_REF) {
          ZName zn = re.getZName();
          OperatorName on = zn.getOperatorName();
          String op = Circus2ZCSPUtils.getOperator(on);
          if(op.equals(ZString.SYMDIFF)) {
            // get expressions e1 and e2
            if(expr instanceof TupleExpr && ((TupleExpr) expr).getZExprList().size() == 2) {
              TupleExpr te = (TupleExpr) expr;
              Expr e1 = te.getZExprList().get(0);
              Expr e2 = te.getZExprList().get(1);
              
              List<Expr> lstExpr12 = new ArrayList<Expr>();
              lstExpr12.add(e1); 
              lstExpr12.add(e2);
              List<Expr> lstExpr21 = new ArrayList<Expr>();
              lstExpr21.add(e2);
              lstExpr21.add(e1); 
              
              // construct e1 \setminus e2
              List<Expr> lstExpr1 = new ArrayList<Expr>();
              RefExpr reOpSetMinus = ZUtils.cloneTerm(re);
              ZName znOpSetMinus = reOpSetMinus.getZName();
              znOpSetMinus.setWord(znOpSetMinus.getWord().replace(ZString.SYMDIFF, ZString.SETMINUS));
              lstExpr1.add(reOpSetMinus);
              
              ZExprList zel1 = fac_.createZExprList(lstExpr12);
              lstExpr1.add(fac_.createTupleExpr(zel1));
              ApplExpr ae1 = fac_.createApplExpr(lstExpr1, true);
              
              // construct e2 \setminus e1
              List<Expr> lstExpr2 = new ArrayList<Expr>();
              lstExpr2.add(reOpSetMinus);
              
              ZExprList zel2 = fac_.createZExprList(lstExpr21);
              lstExpr2.add(fac_.createTupleExpr(zel2));
              ApplExpr ae2 = fac_.createApplExpr(lstExpr2, true);
              
              // construct (e1 \setminus e2) \cup (e2 \setminus e1)
              List<Expr> lstExpr3 = new ArrayList<Expr>();
              RefExpr reOpUnion = ZUtils.cloneTerm(re);
              ZName znOpUnion = reOpUnion.getZName();
              znOpUnion.setWord(znOpUnion.getWord().replace(ZString.SYMDIFF, ZString.CUP));
              lstExpr3.add(reOpUnion);
              
              List<Expr> lstExprUnion = new ArrayList<Expr>();
              lstExprUnion.add(ae1);
              lstExprUnion.add(ae2);
              ZExprList zel3 = fac_.createZExprList(lstExprUnion);
              
              term.setLeftExpr(reOpUnion);
              term.setRightExpr(fac_.createTupleExpr(zel3));
            }
          }
        }
      }
      
    }
    return null;
  }

  @Override
  public Object visitAxPara(AxPara term)
  {
    Name name = ZUtils.getAxParaSchOrAbbrName((Term)term);
    if(name != null) {
      lstSchNames.add((ZName) name);
    }
    
    visitTerm(term);
    return null;
  }
  
  public List<ZName> getLstSchNames()
  {
    return lstSchNames;
  }
}

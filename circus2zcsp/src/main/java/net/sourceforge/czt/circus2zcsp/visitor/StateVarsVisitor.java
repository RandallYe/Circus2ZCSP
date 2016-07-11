
package net.sourceforge.czt.circus2zcsp.visitor;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.CallAction;
import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circus.ast.SchExprAction;
import net.sourceforge.czt.circus.visitor.CallActionVisitor;
import net.sourceforge.czt.circus.visitor.SchExprActionVisitor;
import net.sourceforge.czt.circus2zcsp.data.CircusSpecMap;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.ZNameVisitor;

public class StateVarsVisitor
    implements
      TermVisitor<Object>,
      ZNameVisitor<Object>,
      SchExprActionVisitor<Object>,
      CallActionVisitor<Object>
{
  // a map from original variable or schema name to replaced new name
  private CircusSpecMap map_ = null;

  private String proname_ = null;

  /**
   * list for all state variables
   */
  private List<Pair<String, Term>> lst_;

  /**
   * list to store parsed states
   */
  private List<Pair<String, Term>> lstV_;

  private ZFactory fac_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();

  private CircusFactory cfac_ = new net.sourceforge.czt.circus.impl.CircusFactoryImpl();

  public StateVarsVisitor(CircusSpecMap map, String proname)
  {
    this.map_ = map;
    this.proname_ = proname;
    lst_ = map_.getStatListWithExp(proname_);
    lstV_ = new ArrayList<Pair<String, Term>>();
  }

  @Override
  public Object visitSchExprAction(SchExprAction term)
  {
    Expr expr = term.getExpr();

    String name = "";
    if (expr instanceof RefExpr) {
      name = ((RefExpr) expr).getZName().getWord();
    }

    Pair<String, Term> pp = map_.getRepByNewName(proname_, name);

    if (pp != null) {
      if (pp.getSecond() instanceof AxPara) {
        ConstDecl cd = (ConstDecl) (((AxPara) pp.getSecond()).getZSchText().getZDeclList().get(0));
        if (cd.getExpr() instanceof SchExpr) {
          visit(((SchExpr) (cd.getExpr())).getZSchText().getPred());
        }
      }
    }
    return null;
  }

  @Override
  public Object visitZName(ZName term)
  {
//    String name = term.accept(new PrintVisitor());
    String name = term.getWord();
    for (Pair<String, Term> p : lst_) {
      if (p.getFirst().equals(name)) {
        lstV_.add(p);
      }
    }
    return null;
  }

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

  protected Object visit(Term t)
  {
    Object[] args = t.getChildren();
    for (int i = 0; i < args.length; i++) {
      if (args[i] instanceof Term) {
        args[i] = ((Term) args[i]).accept(this);
      }
    }
    return null;
  }

  @Override
  public Object visitCallAction(CallAction term)
  {
    String name = term.getZName().getWord();
    /*
     * the name containing _Action_ is regarded as Action and it doesn't need to append SKIP. Only
     * Schema Express will
     * But action invocation (reference) need to unfold/expand it
     */
    if (name.contains("_Action_")) {
      /** For action name */
      String act = "";
      Pair<String, Term> p = map_.getRepByNewName(proname_, name);
      if (p != null) {
        Term action = null;
        if (p.getSecond() instanceof ActionPara) {
          action = ZUtils.cloneTerm(((ActionPara) p.getSecond()).getCircusAction());
          act += visit(action);
        }
      }
    }
    // not action invocation, it should be schema expression as action
    else {
      // even for schema expression as action without bracket, we will take it as schema expression
      // as action
      RefExpr re = fac_.createRefExpr(term.getZName(), fac_.createZExprList(), false, false);
      SchExprAction sea = cfac_.createSchExprAction(re);
      visit(sea);
    }

    return null;
  }

  public List<Pair<String, Term>> getVarList()
  {
    return lstV_;
  }

}

package net.sourceforge.czt.circus2zcsp.visitor;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.ChannelDecl;
import net.sourceforge.czt.circus.ast.ChannelPara;
import net.sourceforge.czt.circus.ast.CircusAction;
import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circus.ast.DotField;
import net.sourceforge.czt.circus.ast.Field;
import net.sourceforge.czt.circus.ast.GuardedAction;
import net.sourceforge.czt.circus.ast.IfGuardedCommand;
import net.sourceforge.czt.circus.ast.PrefixingAction;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.visitor.BasicProcessVisitor;
import net.sourceforge.czt.circus.visitor.ChannelParaVisitor;
import net.sourceforge.czt.circus.visitor.GuardedActionVisitor;
import net.sourceforge.czt.circus.visitor.IfGuardedCommandVisitor;
import net.sourceforge.czt.circus.visitor.PrefixingActionVisitor;
import net.sourceforge.czt.circus.visitor.ProcessParaVisitor;
import net.sourceforge.czt.circus2zcsp.Debug;
import net.sourceforge.czt.circus2zcsp.data.CSPPredExpPattern;
import net.sourceforge.czt.circus2zcsp.data.PredExpPattern;
import net.sourceforge.czt.circus2zcsp.util.AxParaKind;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.circus2zcsp.util.RefExprKind;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.And;
import net.sourceforge.czt.z.ast.AndExpr;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.CondExpr;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ExprPred;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NegExpr;
import net.sourceforge.czt.z.ast.NegPred;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ProdExpr;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.ExprPredVisitor;
import net.sourceforge.czt.z.visitor.RefExprVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;

/**
 * Rewrite schemas that are used in CSP as predicates
 *   <ul>
 *      <li> rewrite to their predicates directly </li>
 *      <li> Only very limited predicate contexts support</li>
 *              <ul>
 *              <li> guarded conditions </li>
 *              <li> channel output expression </li>
 *              </ul>
 *      <li>  </li>
 *   </ul>
 * @author rye
 *
 */
public class CircusSchemasAsPredicateVisitor
  implements RefExprVisitor<Object>,
  ExprPredVisitor<Object>,
  TermVisitor<Object>,
  ZSectVisitor<Object>,
  PrefixingActionVisitor<Object>,
  ProcessParaVisitor<Object>,
  ChannelParaVisitor<Object>,
//  PredVisitor<Object>
  BasicProcessVisitor<Object>,
  GuardedActionVisitor<Object>,
  IfGuardedCommandVisitor<Object>
{
  private final Visitor<Object> visitor_ = this;
  private ZSect zs_ = null;
  private ProcessPara process_para_ = null;
  /**
   * if it is in the predicate context in the CSP part. Ignore the Z part
   */
  private boolean predicate_context_ = false;
  private final Set<Pair<ZName, Expr>> set_channel_name_expr_pair_ = new HashSet<Pair<ZName, Expr>>();
  private final CircusFactory cfac_ = new net.sourceforge.czt.circus.impl.CircusFactoryImpl();

  private final Stack<Term> stack_parent_ = new Stack<Term>();
  
  private final Stack<Pred> stack_pred_ = new Stack<Pred>();
  
  private RefExpr reTrue = cfac_.createRefExpr(
      cfac_.createZName("True", cfac_.createZStrokeList(), null), 
      cfac_.createZExprList(), false, false);

  private RefExpr reFalse = cfac_.createRefExpr(
      cfac_.createZName("False", cfac_.createZStrokeList(), null), 
      cfac_.createZExprList(), false, false);

  private SectionManager manager_ = null;
  
  // normalisation doesn't work as expected. So just for debug
  private static boolean normalisation_ = false;

  public CircusSchemasAsPredicateVisitor(SectionManager manager)
  {
    manager_ = manager;
  }
  private void enterPredicateContext() 
  {
    predicate_context_ = true;
  }
  
  private void leavePredicateContext()
  {
    predicate_context_ = false;
  }
  
  private boolean isPreidateContext()
  {
    return predicate_context_;
  }
  
  protected Object visit(Term t)
  {
    if (t != null) {
      stack_parent_.push(t);
      Object o = t.accept(visitor_);
      stack_parent_.pop();
    }
    return null;
  }
  
  private Pred recursiveVisitExprPred(Expr expr) 
  {
    Pred pred = null;
    if(expr instanceof NegExpr) {
      NegExpr ne = (NegExpr)expr;
      pred = recursiveVisitExprPred(ne.getExpr());
      pred = cfac_.createNegPred(pred);
    }
    else if(expr instanceof AndExpr) {
      Pred pred1 = null;
      Pred pred2 = null;
      
      AndExpr ae = (AndExpr)expr;
      pred1 = recursiveVisitExprPred(ae.getLeftExpr());
      
      pred2 = recursiveVisitExprPred(ae.getRightExpr());

      List<Pred> lstPred = new ArrayList<Pred>();
      lstPred.add(pred1);
      lstPred.add(pred2);
      
      pred = cfac_.createAndPred(lstPred, And.Wedge);
    }
    else if(expr instanceof RefExpr) {
      visit(expr);
      if(Circus2ZCSPUtils.isSchemaExpr(expr, zs_, process_para_)) {
        pred = stack_pred_.pop();
      }
    }
    
    return pred;
  }
  
  public Pred normaliseRefExpr(RefExpr ref) 
  {
    Pred pred = null;
    boolean found = false;
    Expr apref = null;
    
    for(Para p: zs_.getZParaList()) {
      if(p instanceof AxPara) {
        AxPara ap = (AxPara)p;
        AxParaKind apkind = Circus2ZCSPUtils.getAxParaKind(ap);
        ZName apname = null;
        switch(apkind) {
          case ABBR:
            apname = (ZName) ZUtils.getAbbreviationName(ap);
            if(Circus2ZCSPUtils.isEquals(ref.getZName(), apname)) {
              found = true;
              apref = ZUtils.getAbbreviationExpr(ap);
            }
            
            break;
          case BOXED_SCHEMA:
          case HORIZON_SCHEMA:
            apname = (ZName) ZUtils.getSchemaName(ap);
            if(Circus2ZCSPUtils.isEquals(ref.getZName(), apname)) {
              found = true;
              apref = ZUtils.getSchemaDefExpr(ap);
            }

            break;
          default:
            break;
        }
      }
    }
    
    if(!found && process_para_.getCircusProcess() instanceof BasicProcess) {
      for(Para p: process_para_.getCircusBasicProcess().getZParaList()) {
        if(p instanceof AxPara) {
          AxPara ap = (AxPara)p;
          AxParaKind apkind = Circus2ZCSPUtils.getAxParaKind(ap);
          ZName apname = null;
          switch(apkind) {
            case ABBR:
              apname = (ZName) ZUtils.getAbbreviationName(ap);
              if(Circus2ZCSPUtils.isEquals(ref.getZName(), apname)) {
                found = true;
                apref = ZUtils.getAbbreviationExpr(ap);
              }
              
              break;
            case BOXED_SCHEMA:
            case HORIZON_SCHEMA:
              apname = (ZName) ZUtils.getSchemaName(ap);
              if(Circus2ZCSPUtils.isEquals(ref.getZName(), apname)) {
                found = true;
                apref = ZUtils.getSchemaDefExpr(ap);
              }

              break;
            default:
              break;
          }
        }
      }
    }
    
    if(apref != null) {
      // try to normalize the expression to get its predicate
      SchExpr schExpr = null;
      schExpr = Circus2ZCSPUtils.expansionSchema(apref, zs_.getName(), manager_);

      // if normalization works, then get the normalized predicate
      if(schExpr != null) {
        pred = schExpr.getZSchText().getPred();
      } 
    }
    
    return pred;
  }
    
  @Override
  public Object visitExprPred(ExprPred term)
  {
    // prefer to use PredicateListExpandVisitor to get predicate instead of 
    // implementation in this class
    boolean usePredicateListExpand = true;
    Expr expr = term.getExpr();
    Debug.debug_print(
        Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
        Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
        Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
        "ExprPred: " + expr.accept(new PrintVisitor()));

    Pred pred = null;
    // 
    if(normalisation_) {
      if(expr instanceof RefExpr) {
        pred = normaliseRefExpr((RefExpr)expr);
      } 
      else {
        // try to normalize the expression to get its predicate
        SchExpr schExpr = null;
        schExpr = Circus2ZCSPUtils.expansionSchema(expr, zs_.getName(), manager_);
        // if normalization works, then get the normalized predicate
        if(schExpr != null) {
          pred = schExpr.getZSchText().getPred();
        } 
      }
    } // normalisation_
    else {
      if(usePredicateListExpand) {
        pred = getPredByExpand(term);
      } else {
        pred = recursiveVisitExprPred(expr);
      }
    }

    if(pred == null) {
      
    }
    
//    if(expr instanceof NegExpr) {
//      visit(expr);
//      pred = stack_pred_.pop();
//      pred = cfac_.createNegPred(pred);
//    }
//    else if(expr instanceof AndExpr) {
//      Pred pred1 = null;
//      Pred pred2 = null;
//      
//      AndExpr ae = (AndExpr)expr;
//      visit(ae.getLeftExpr());
//      pred1 = stack_pred_.pop();
//      
//      visit(ae.getRightExpr());
//      pred2 = stack_pred_.pop();
//
//      List<Pred> lstPred = new ArrayList<Pred>();
//      lstPred.add(pred1);
//      lstPred.add(pred2);
//      
//      pred = cfac_.createAndPred(lstPred, And.Wedge);
//    }
//    else if(expr instanceof RefExpr) {
//      visit(expr);
//      pred = stack_pred_.pop();
//    }

    if(pred != null) {
      Circus2ZCSPUtils.updateParentRef(stack_parent_, term, pred);
    }
    
    return null;
  }

  private boolean updateRefExprToAxPara(Para p, RefExpr term)
  {
    boolean found = false;
    ZName name = null;
    
    RefExprKind kind = Circus2ZCSPUtils.getRefExprKind(term);
    switch(kind) {
      case REF:
        name = term.getZName();
        break;
      default:
        break;
    }

    if(name != null) {
      if(p instanceof AxPara) {
        AxPara ap = (AxPara)p;
        AxParaKind apkind = Circus2ZCSPUtils.getAxParaKind(ap);
        ZName apname = null;
        Expr expr = null;
        switch(apkind) {
          case ABBR:
            apname = (ZName) ZUtils.getAbbreviationName(ap);
            if(Circus2ZCSPUtils.isEquals(name, apname)) {
              found = true;
              expr = ZUtils.getAbbreviationExpr(ap);
              Pred pred = recursiveVisitExprPred(expr);
              if(pred != null) {
                stack_pred_.push(ZUtils.cloneTerm(pred));
              }
//              visit(expr);
//              Circus2ZCSPUtils.updateParentRef(stack_parent_, term, expr);
            }
            break;
          case BOXED_SCHEMA:
          case HORIZON_SCHEMA:
            apname = (ZName) ZUtils.getSchemaName(ap);
            if(Circus2ZCSPUtils.isEquals(name, apname)) {
              found = true;
              expr = ZUtils.getSchemaDefExpr(ap);
              
              // for schema, only its predicate when in predicate context
              if(expr instanceof SchExpr) {
                Pred pred = ((SchExpr)expr).getZSchText().getPred();
                // a temporary NegPred to contain the pred
                NegPred np = cfac_.createNegPred(pred);
                stack_parent_.push(np);
                visit(pred);
                stack_parent_.pop();
                // the pred might be updated in visit
                stack_pred_.push(ZUtils.cloneTerm(np.getPred()));
//                Circus2ZCSPUtils.updateParentRef(stack_parent_, term, pred);
              }
              else {
                visit(expr);
//                Circus2ZCSPUtils.updateParentRef(stack_parent_, term, expr);
              }
            }
            break;
          default:
            break;
        }
      }
    }
    
    return found;
  }
  
  @Override
  public Object visitRefExpr(RefExpr term)
  {
    // if it is in the predicate context
    if(isPreidateContext()) {
      boolean found = false;
      for(Para p: zs_.getZParaList()) {
        if(updateRefExprToAxPara(p, term)) {
          found = true;
          break;
        }
      }
      
      if(!found && process_para_.getCircusProcess() instanceof BasicProcess) {
        for(Para p: process_para_.getCircusBasicProcess().getZParaList()) {
          if(updateRefExprToAxPara(p, term)) {
            found = true;
            break;
          }
        }
      }
    }
    
    return null;
  }

  @Override
  public Object visitTerm(Term zedObject)
  {
    stack_parent_.push(zedObject);
    Object[] args = zedObject.getChildren();
    for (int i = 0; i < args.length; i++) {
      if (args[i] instanceof Term) {
        args[i] = ((Term) args[i]).accept(this);
      }
    }
    stack_parent_.pop();

    return null;
  }

  @Override
  public Object visitZSect(ZSect term)
  {
    zs_ = term;
    
    for(Para p: term.getZParaList()) {
      if(p instanceof ProcessPara) {
        visit(p);
      }
      else if(p instanceof ChannelPara) {
        visit(p);
      }
    }
    
    return null;
  }

  @Override
  public Object visitPrefixingAction(PrefixingAction term)
  {
    stack_parent_.push(term);
    RefExpr re = term.getCommunication().getChannelExpr();
    
    ZName chnName = null;
    
    RefExprKind kind = Circus2ZCSPUtils.getRefExprKind(re);
    switch(kind) {
      case REF:
        chnName = re.getZName();
        break;
      default:
        break;
    }
    
    // get the channel declaration
    boolean found = false;
    Expr expr = null;
    if(chnName != null) {
      for(Pair<ZName, Expr> p: set_channel_name_expr_pair_) {
        if(Circus2ZCSPUtils.isEquals(p.getFirst(), chnName)) {
          expr = p.getSecond();
          found = true;
          break;
        }
      }
    }
    
    List<Expr> te = new ArrayList<Expr>();
    if(found && expr != null) {
      if(expr instanceof ProdExpr) {
        te.addAll(((ProdExpr)expr).getZExprList());
      }
      else {
        te.add(expr);
      }
    }
    
    int cnt = 0;
    for(Field f: term.getCommunication().getCircusFieldList()) {
      boolean boolExpr = false;

      if(f instanceof DotField) {
        if(te.get(cnt) instanceof RefExpr) {
          re = (RefExpr) te.get(cnt);
          // boolean
          if(Circus2ZCSPUtils.isEquals(re.getZName(), 
              cfac_.createZName(CSPPredExpPattern.getPattern(PredExpPattern.BOOLEAN), 
                  cfac_.createZStrokeList(), null))) {
            // check if it is a reference to a schema or abbreviation, etc
            if(Circus2ZCSPUtils.isSchemaExpr(((DotField)f).getExpr(), zs_, process_para_)) {
              // here use CondExpr to contain the output of fields' expression (true, false).
              // and the expression is put in the predicate of CondExpr
              ExprPred pred = cfac_.createExprPred(((DotField)f).getExpr());
              List<Expr> lstExpr = new ArrayList<Expr>();
              lstExpr.add(reTrue);
              lstExpr.add(reFalse);
              CondExpr ce = cfac_.createCondExpr(pred, lstExpr);
              
              ((DotField)f).setExpr(ce);
              boolExpr = true;
              enterPredicateContext();
              stack_parent_.push(ce);
              visit(pred);
              stack_parent_.pop();
              leavePredicateContext();
            }
          }
        }
      }
      
      if(!boolExpr) {
        visit(f);
      }
      
      cnt++;
    }
    
    stack_parent_.pop();
    return null;
  }

  @Override
  public Object visitProcessPara(ProcessPara term)
  {
    process_para_ = term;
    
    visit(term.getCircusProcess());
    process_para_ = null;
    return null;
  }

  @Override
  public Object visitChannelPara(ChannelPara term)
  {
    for(Decl decl: term.getZDeclList()) {
      if(decl instanceof ChannelDecl) {
        for(Name n: ((ChannelDecl)decl).getZChannelNameList()) {
          set_channel_name_expr_pair_.add(new Pair<ZName, Expr>((ZName) n, ((ChannelDecl)decl).getExpr()));
        }
      }
    }

    visit(term.getZDeclList());
    
    return null;
  }

  @Override
  public Object visitBasicProcess(BasicProcess term)
  {
    for(Para p: term.getZParaList()) {
      // only visit the action part, and the main action has been visited as ActionPara, so ignore it 
      if(p instanceof ActionPara && !p.equals(term.getMainAction())) {
        visit(p);
      }
    }
    return null;
  }

  @Override
  public Object visitIfGuardedCommand(IfGuardedCommand term)
  {
    stack_parent_.push(term);
    for(CircusAction ca: term.getGuardedActionList()) {
      if(ca instanceof GuardedAction) {
        visit(ca);
      }
    }
    stack_parent_.pop();
    return null;
  }

  @Override
  public Object visitGuardedAction(GuardedAction term)
  {
    stack_parent_.push(term);
    enterPredicateContext();
    visit(term.getPred());
    leavePredicateContext();
    stack_parent_.pop();
    return null;
  }

  private Pred getPredByExpand(Pred pred) 
  {
    PredicateListExpansionVisitor plev;
    if(process_para_ == null) {
      plev = new PredicateListExpansionVisitor(zs_, manager_, zs_.getName());
    }
    else {
      plev = new PredicateListExpansionVisitor(process_para_.getCircusBasicProcess(), 
          zs_, manager_, zs_.getName());
    }
    pred.accept(plev);
    
    Pred pred1 = plev.getPred();
    return pred1;
  }

}

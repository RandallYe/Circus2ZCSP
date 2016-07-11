package net.sourceforge.czt.circus2zcsp.visitor;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circus2zcsp.data.CSPPredExpPattern;
import net.sourceforge.czt.circus2zcsp.data.PredExpPattern;
import net.sourceforge.czt.circus2zcsp.data.VariableRenameSchema;
import net.sourceforge.czt.circus2zcsp.util.AxParaKind;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.And;
import net.sourceforge.czt.z.ast.AndExpr;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.CompExpr;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.DecorExpr;
import net.sourceforge.czt.z.ast.Exists1Expr;
import net.sourceforge.czt.z.ast.ExistsExpr;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ExprPred;
import net.sourceforge.czt.z.ast.ForallExpr;
import net.sourceforge.czt.z.ast.HideExpr;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NegExpr;
import net.sourceforge.czt.z.ast.NegPred;
import net.sourceforge.czt.z.ast.NewOldPair;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.OrExpr;
import net.sourceforge.czt.z.ast.OutStroke;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.PipeExpr;
import net.sourceforge.czt.z.ast.PreExpr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Pred2;
import net.sourceforge.czt.z.ast.ProjExpr;
import net.sourceforge.czt.z.ast.QntExpr;
import net.sourceforge.czt.z.ast.QntPred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.RenameExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.ast.ZStrokeList;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.AndExprVisitor;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.CompExprVisitor;
import net.sourceforge.czt.z.visitor.DecorExprVisitor;
import net.sourceforge.czt.z.visitor.ExprPredVisitor;
import net.sourceforge.czt.z.visitor.HideExprVisitor;
import net.sourceforge.czt.z.visitor.MemPredVisitor;
import net.sourceforge.czt.z.visitor.NegExprVisitor;
import net.sourceforge.czt.z.visitor.NegPredVisitor;
import net.sourceforge.czt.z.visitor.OrExprVisitor;
import net.sourceforge.czt.z.visitor.PipeExprVisitor;
import net.sourceforge.czt.z.visitor.PreExprVisitor;
import net.sourceforge.czt.z.visitor.Pred2Visitor;
import net.sourceforge.czt.z.visitor.ProjExprVisitor;
import net.sourceforge.czt.z.visitor.QntExprVisitor;
import net.sourceforge.czt.z.visitor.QntPredVisitor;
import net.sourceforge.czt.z.visitor.RefExprVisitor;
import net.sourceforge.czt.z.visitor.RenameExprVisitor;
import net.sourceforge.czt.z.visitor.SchExprVisitor;

/**
 * A visitor to get the predicate part of a schema without normalization (because state components etc, have been
 * renamed before, normalization would not give the expected result). 
 * <ul>
 * <li> In order to get the right predicate part, we need to include the constraints from variable declartion as well </li>
 *      <ul>
 *      <li> input "[ [x : 1..3 | x >= 2] | x == 2]", should not be (x >= 2) and (x == 2) </li>
 *      <li> input "[ [x : 1..3 | x >= 2] | x == 2]", right result: (x \in 1..3) and (x >= 2) and (x == 2) </li>
 *      </ul>
 * <li> Problems and Limitations </li>
 *      <ul>
 *      <li> We assume all types of variables in declarations aren't carrier set. Otherwise, 
 *      it is too heavy to put in the predicate part. Our solution in this class turns a VarDecl (x:T) into a
 *      MemPred (x \in T) directly. </li>
 *      </ul>
 * </ul>
 * 
 * @author rye
 *
 */

public class PredicateListExpansionVisitor
  implements 
  TermVisitor<Object>, 
  RefExprVisitor<Object>,
  AxParaVisitor<Object>,
  SchExprVisitor<Object>,
  RenameExprVisitor<Object>,
  DecorExprVisitor<Object>,
  QntExprVisitor<Object>,
  HideExprVisitor<Object>,
  ProjExprVisitor<Object>,
  PreExprVisitor<Object>,
  CompExprVisitor<Object>,
  PipeExprVisitor<Object>,
  AndExprVisitor<Object>,
  OrExprVisitor<Object>,
  ExprPredVisitor<Object>,
  NegExprVisitor<Object>,
  NegPredVisitor<Object>,
  MemPredVisitor<Object>,
  QntPredVisitor<Object>,
  Pred2Visitor<Object>
{
  private BasicProcess bp_ = null;
  private ZSect zs_ = null;
  private SectionManager manager_ = null;
  private String sectname_ = null;
  private Visitor<Object> visitor_ = this;
  private Pred pred_ = null;
  private final CircusFactory cfac_ = new net.sourceforge.czt.circus.impl.CircusFactoryImpl();
  
  public PredicateListExpansionVisitor(BasicProcess bp, ZSect zs, SectionManager manager, String sectname)
  {
    bp_                 = ZUtils.cloneTerm(bp);
    zs_                 = ZUtils.cloneTerm(zs);
    manager_            = manager;
    sectname_           = sectname;
  }
  
  public PredicateListExpansionVisitor(ZSect zs, SectionManager manager, String sectname)
  {
    zs_                 = ZUtils.cloneTerm(zs);
    manager_            = manager;
    sectname_           = sectname;
  }
  
  public void clear()
  {
    pred_ = null;
  }
  
  public Pred getPred() 
  {
    return pred_;
  }
  
  protected Object visit(Term t)
  {    
    if (t != null) {
      return t.accept(visitor_);
    }
    return null;
  }
  
  @Override
  public Object visitRefExpr(RefExpr term)
  {
    /*
     * 1. For a RefExpr to a global or local AxPara, then visit this AxPara to get the declaration.
     * 2. For a Delta/Xi RefExpr, visit its AxPara referred, but add additional dashed variable copy as well
     */
    ZName refName = ZUtils.cloneTerm(term.getZName());
    boolean found = false;
    
    // for reference, just remove prefixing Delta or Xi
    if(ZUtils.isDeltaXi(term.getZName())) {
      
    }
    
    String str = Circus2ZCSPUtils.termToString(term.getZName());
    assert(term.getZExprList().isEmpty());
    
    if(bp_ != null) {
      ZParaList pl = bp_.getZParaList();
      for(Para p: pl) {
        if(p instanceof AxPara) {
          AxPara ap = (AxPara)p;
          AxParaKind kind = Circus2ZCSPUtils.getAxParaKind(ap);
          ZName name = null;
          
          switch(kind) {
            case ABBR:
              name = (ZName) ZUtils.getAbbreviationName(ap);
              break;
            case AXDEF:
              break;
            case BOXED_SCHEMA:
            case HORIZON_SCHEMA:
              name = (ZName) ZUtils.getAxParaSchOrAbbrName(ap);
              break;
            default:
                break;
          }
          
          if(name != null) {
            if(Circus2ZCSPUtils.isEquals(refName, (ZName) name)) {
              visit(ap);
              found = true;
              break;
            }
          }
        }
      }
    }
    
    // if fail to find the AxPara reference within the process, then search global
    if(!found) {
      for(Para p: zs_.getZParaList()) {
        if(p instanceof AxPara) {
          AxPara ap = (AxPara)p;
          AxParaKind kind = Circus2ZCSPUtils.getAxParaKind(ap);
          ZName name = null;
          
          switch(kind) {
            case ABBR:
              name = (ZName) ZUtils.getAbbreviationName(ap);
              break;
            case AXDEF:
              break;
            case BOXED_SCHEMA:
            case HORIZON_SCHEMA:
              name = (ZName) ZUtils.getAxParaSchOrAbbrName(ap);
              break;
            default:
                break;
          }
          
          if(name != null) {
            if(Circus2ZCSPUtils.isEquals(refName, (ZName) name)) {
              visit(ap);
              break;
            }
          }
        }
      }
    }
    
    if(ZUtils.isDeltaXi(term.getZName())) {}
    return null;
  }

  @Override
  public Object visitAxPara(AxPara term)
  {
    AxParaKind kind = Circus2ZCSPUtils.getAxParaKind(term);
    Expr expr;

    switch(kind) {
      case ABBR:
        expr = ZUtils.getAbbreviationExpr(term);
        visit(expr);
        break;
      case HORIZON_SCHEMA:
      case BOXED_SCHEMA:
        expr = ZUtils.getSchemaDefExpr(term);
        visit(expr);
        break;
      default:
        throw new CztException("Only a schema or schema abbreviation can be expanded, but it is " + kind.toString());
    }

    return null;
  }
  
  @Override
  public Object visitTerm(Term t)
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
  public Object visitSchExpr(SchExpr term)
  {
    for(Decl decl: term.getZSchText().getZDeclList()) {
      if(decl instanceof VarDecl) {
        VarDecl vd = (VarDecl)decl;
        // it should be converted to membership in the predicate part
        for(Name n: vd.getZNameList()) {
          RefExpr re = cfac_.createRefExpr(n, cfac_.createZExprList(), false, false);
          List<Expr> lstExpr = new ArrayList<Expr>();
          lstExpr.add(re);
          lstExpr.add(vd.getExpr());
          MemPred mp = cfac_.createMemPred(lstExpr, false);
          
          if(pred_ instanceof TruePred || pred_ == null) {
            pred_ = mp;
          }
          else {
            pred_ = createNewPred(mp, pred_, true);
          }
        }
      }
      else if(decl instanceof InclDecl) {
        // for InclDecl, its predicate is a conjunction
        Pred backup = pred_;
        pred_ = null;
        visit(decl);
        if(pred_ instanceof TruePred || pred_ == null) {
          pred_ = backup;
        }
        else {
          if(backup != null) {
            pred_ = createNewPred(backup, pred_, true);
          }
        }
      }
      else {
        
      }
    }
    
    Pred backup = pred_;
    
    Pred pred = term.getZSchText().getPred();
    if(pred != null) {
      pred_ = null;
      visit(pred);
      if(pred_ == null) {
        pred_ = backup;
      }
      else {
        pred_ = createNewPred(backup, pred_, true);
      }
    }
    else {
      // if pred == null, just keep pred_ the same as backup
//      pred_ = createNewPred(cfac_.createTruePred(), pred_, true);
    }
    return null;
  }

  @Override
  public Object visitRenameExpr(RenameExpr term)
  {
//    Pred backup = pred_;
    pred_ = null;
    visit(term.getExpr());
    
    if(pred_ == null || pred_ instanceof TruePred) {
      return null;
    }
    
    List<Pair<String, String>> lstRenamePair = new ArrayList<Pair<String, String>>();
    // rename it
    for(NewOldPair p: term.getZRenameList()) {
      lstRenamePair.add(new Pair<String, String>(
          Circus2ZCSPUtils.termToString(p.getOldName()),
          Circus2ZCSPUtils.termToString(p.getNewName())));
    }
    
    VariableRenamingSchemaVisitor vrsv = 
        new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_NAME_REPLACE, lstRenamePair);
    
    pred_.accept(vrsv);
    
    return null;
  }

  /**
   * Decorated Schema S' == [ a': Ta; b': Tb | P[a'/a,b'/b] ]
   */
  @Override
  public Object visitDecorExpr(DecorExpr term)
  {
    pred_ = null;
    visit(term.getExpr());

    if(pred_ == null || pred_ instanceof TruePred) {
      return null;
    }
    
    // get the declaration list [a, b, ...]
    DeclListExpansionVisitor dlevisitor;
    if(bp_ == null) {
      dlevisitor = new DeclListExpansionVisitor(zs_, manager_, sectname_);
    }
    else {
      dlevisitor = new DeclListExpansionVisitor(bp_, zs_, manager_, sectname_);
    }
    
    dlevisitor.disableNormalisation();
    term.getExpr().accept(dlevisitor);
    List<Pair<ZName, Expr>> lstZNameExpr = dlevisitor.getNameExprPairAsList();

    /**
     * a, b, ...
     */
    List<String> slst = new ArrayList<String>();
    for(Pair<ZName, Expr> p: lstZNameExpr) {
      slst.add(Circus2ZCSPUtils.termToString(p.getFirst()));
    }
    
    // a -> a', b -> b'
    pred_.accept(
        new VariableRenamingSchemaVisitor(slst, VariableRenameSchema.VRS_APPEND_NEXTSTROKE));
    
    return null;
  }

  /**
   * Sch\(a, b) => \exists a:Ta; b:Tb @ P
   */
  @Override
  public Object visitHideExpr(HideExpr term)
  {
    pred_ = null;
    visit(term.getExpr());

    if(pred_ == null || pred_ instanceof TruePred) {
      return null;
    }
    
    // get the declaration list [a, b, ...]
    DeclListExpansionVisitor dlevisitor;
    if(bp_ == null) {
      dlevisitor = new DeclListExpansionVisitor(zs_, manager_, sectname_);
    }
    else {
      dlevisitor = new DeclListExpansionVisitor(bp_, zs_, manager_, sectname_);
    }
    
    term.getExpr().accept(dlevisitor);
    List<Pair<ZName, Expr>> lstZNameExpr = dlevisitor.getNameExprPairAsList();

    /**
     * a, b, ...
     */
    List<Decl> lstDecl = new ArrayList<Decl>();
    
    for(Pair<ZName, Expr> p: lstZNameExpr) {
      for(Name name: term.getZNameList()) {
        if(Circus2ZCSPUtils.isEquals(p.getFirst(), (ZName)name)) {
          List<ZName> lstName = new ArrayList<ZName>();
          lstName.add(p.getFirst());
          ZNameList znl = cfac_.createZNameList(lstName);
          VarDecl vd = cfac_.createVarDecl(znl, p.getSecond());
          lstDecl.add(vd);
        }
      }
    }

    if(!lstDecl.isEmpty()) {
      ZDeclList declList = cfac_.createZDeclList(lstDecl);
      ZSchText schText = cfac_.createZSchText(declList, cfac_.createTruePred());
      pred_ = cfac_.createExistsPred(schText, pred_);
    }

    return null;
  }

  @Override
  public Object visitQntExpr(QntExpr term)
  {
    if(term instanceof Exists1Expr || 
        term instanceof ExistsExpr || 
        term instanceof ForallExpr) {
      
      pred_ = null;
      visit(term.getExpr());

      if(pred_ == null || pred_ instanceof TruePred) {
        return null;
      }
      
      if(term instanceof Exists1Expr) {
        pred_ = cfac_.createExists1Pred(term.getZSchText(), pred_);
      }
      else if(term instanceof ExistsExpr) {
        pred_ = cfac_.createExistsPred(term.getZSchText(), pred_);
      }
      else if(term instanceof ForallExpr) {
        pred_ = cfac_.createForallPred(term.getZSchText(), pred_);
      }
      else {
        
      }
    }
    else {
      // TODO: how about MuExpr, SetCompExpr, Lambda and LetExpr
    }
    
    return null;
  }

  /**
   * S \proj T = (S \land T) \hide (s1, s2, ..., sn)
   */
  @Override
  public Object visitProjExpr(ProjExpr term)
  {
    pred_ = null;
    
    visit(term.getLeftExpr());
    Pred left = pred_;

    visit(term.getRightExpr());
    Pred right = pred_;
    
    // get the declaration list [a, b, ...]
    DeclListExpansionVisitor dlevisitor;
    if(bp_ == null) {
      dlevisitor = new DeclListExpansionVisitor(zs_, manager_, sectname_);
    }
    else {
      dlevisitor = new DeclListExpansionVisitor(bp_, zs_, manager_, sectname_);
    }
    
    term.getLeftExpr().accept(dlevisitor);
    List<Pair<ZName, Expr>> lstZNameExpr = dlevisitor.getNameExprPairAsList();

    List<Decl> lstDecl = new ArrayList<Decl>();
    
    for(Pair<ZName, Expr> p: lstZNameExpr) {
      List<ZName> lstName = new ArrayList<ZName>();
      lstName.add(p.getFirst());
      ZNameList znl = cfac_.createZNameList(lstName);
      VarDecl vd = cfac_.createVarDecl(znl, p.getSecond());
      lstDecl.add(vd);
    }
    
    if(!lstDecl.isEmpty()) {
      ZDeclList declList = cfac_.createZDeclList(lstDecl);
      ZSchText schText = cfac_.createZSchText(declList, cfac_.createTruePred());
      List<Pred> lstPred = new ArrayList<Pred>();
      lstPred.add(left);
      lstPred.add(right);
      pred_ = cfac_.createExistsPred(schText, cfac_.createAndPred(lstPred, And.Wedge));
    }

    return null;
  }

  /**
   * pre S = S \hide (s1', s2', ..., sn', o1!, o2!, ..., on!)
   */
  @Override
  public Object visitPreExpr(PreExpr term)
  {
    pred_ = null;
    visit(term.getExpr());

    if(pred_ == null || pred_ instanceof TruePred) {
      return null;
    }
    
    // get the declaration list [a, b, ...]
    DeclListExpansionVisitor dlevisitor;
    if(bp_ == null) {
      dlevisitor = new DeclListExpansionVisitor(zs_, manager_, sectname_);
    }
    else {
      dlevisitor = new DeclListExpansionVisitor(bp_, zs_, manager_, sectname_);
    }
    
    dlevisitor.disableNormalisation();
    term.getExpr().accept(dlevisitor);
    List<Pair<ZName, Expr>> lstZNameExpr = dlevisitor.getNameExprPairAsList();

    List<Decl> lstDecl = new ArrayList<Decl>();

    for(Pair<ZName, Expr> p: lstZNameExpr) {
      ZStrokeList zsl = p.getFirst().getZStrokeList();
      
      if(!zsl.isEmpty() && 
          (zsl.get(zsl.size() - 1) instanceof NextStroke || 
           zsl.get(zsl.size() - 1) instanceof OutStroke)) {
        List<ZName> lstName = new ArrayList<ZName>();
        lstName.add(p.getFirst());
        ZNameList znl = cfac_.createZNameList(lstName);
        VarDecl vd = cfac_.createVarDecl(znl, p.getSecond());
        lstDecl.add(vd);
      }
    }

    if(!lstDecl.isEmpty()) {
      ZDeclList declList = cfac_.createZDeclList(lstDecl);
      ZSchText schText = cfac_.createZSchText(declList, cfac_.createTruePred());
      pred_ = cfac_.createExistsPred(schText, pred_);
    }
    
    return null;
  }

  /**
   * S \comp T = \exists x1', x2', ... @ Ps[x1'/s1', ..., xn'/sn'] \land Qt[x1'/t1,...,xn'/tn]
   */
  @Override
  public Object visitCompExpr(CompExpr term)
  {
    pred_ = null;
    visit(term.getLeftExpr());
    Pred left = pred_;

    pred_ = null;
    visit(term.getRightExpr());
    Pred right = pred_;

    // get the declaration list [a, b, ...]
    DeclListExpansionVisitor dlevisitor;
    if(bp_ == null) {
      dlevisitor = new DeclListExpansionVisitor(zs_, manager_, sectname_);
    }
    else {
      dlevisitor = new DeclListExpansionVisitor(bp_, zs_, manager_, sectname_);
    }
    
    term.getLeftExpr().accept(dlevisitor);
    List<Pair<ZName, Expr>> lstZNameExprLeft = new ArrayList<Pair<ZName, Expr>>();
    lstZNameExprLeft.addAll(dlevisitor.getNameExprPairAsList());

    dlevisitor.clear();
    term.getLeftExpr().accept(dlevisitor);
    List<Pair<ZName, Expr>> lstZNameExprRight = new ArrayList<Pair<ZName, Expr>>();
    lstZNameExprRight.addAll(dlevisitor.getNameExprPairAsList());

    
    List<Decl> lstDecl = new ArrayList<Decl>();
    Set<Pair<ZName, ZName>> setRenamePairLeft = new HashSet<Pair<ZName, ZName>>();
    Set<Pair<ZName, ZName>> setRenamePairRight = new HashSet<Pair<ZName, ZName>>();

    for(Pair<ZName, Expr> p1: lstZNameExprLeft) {
      ZStrokeList zsl = p1.getFirst().getZStrokeList();
      if(!zsl.isEmpty() && (zsl.get(zsl.size() - 1) instanceof NextStroke)) {
        for(Pair<ZName, Expr> p2: lstZNameExprRight) {
          if(p2.getFirst().getZStrokeList().isEmpty() && 
              p1.getFirst().getWord().equals(p2.getFirst().getWord())) {
            // Temporary variable
            // \exists x1', ..., xn' @ S[x1'/s1',...,xn'/sn'] \land T[x1'/t1,...,xn'/tn]
            String strVName =  MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.SCHEMA_COMP_INTERMEDIATE_VAR_PATT), 
                p2.getFirst().getWord());
            ZName name = cfac_.createZName(strVName, cfac_.createZStrokeList(), null);
            setRenamePairLeft.add(new Pair<ZName, ZName>(p1.getFirst(), name));
            setRenamePairRight.add(new Pair<ZName, ZName>(p2.getFirst(), name));
            
            List<ZName> lstName = new ArrayList<ZName>();
            lstName.add(name);
            lstDecl.add(cfac_.createVarDecl(cfac_.createZNameList(lstName), p1.getSecond()));
          }
        }
      }
    }

    if(!lstDecl.isEmpty()) {
      ZDeclList declList = cfac_.createZDeclList(lstDecl);
      ZSchText schText = cfac_.createZSchText(declList, cfac_.createTruePred());
      
      left.accept(
          new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_ZNAME_RENAME, setRenamePairLeft));
      right.accept(
          new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_ZNAME_RENAME, setRenamePairRight));

      List<Pred> lstPred = new ArrayList<Pred>();
      lstPred.add(left);
      lstPred.add(right);
      pred_ = cfac_.createExistsPred(schText, cfac_.createAndPred(lstPred, And.Wedge));
    }
    
    return null;
  }

  @Override
  public Object visitPipeExpr(PipeExpr term)
  {
    return null;
  }

  @Override
  public Object visitAndExpr(AndExpr term)
  {
    Pred left = null;
    Pred right = null;
    
    pred_ = null;
    visit(term.getLeftExpr());
    left = pred_;

    pred_ = null;
    visit(term.getRightExpr());
    right = pred_;

    pred_ = createNewPred(left, right, true);
    return null;
  }

  @Override
  public Object visitOrExpr(OrExpr term)
  {
    Pred left = null;
    Pred right = null;
    
    pred_ = null;
    visit(term.getLeftExpr());
    left = pred_;

    pred_ = null;
    visit(term.getRightExpr());
    right = pred_;

    pred_ = createNewPred(left, right, false);
    return null;
  }
  
  /**
   * Create a new predicate from two input predicates and the mode
   * @param pred1
   * @param pred2
   * @param and - AndPred or OrPred
   * @return
   */
  private Pred createNewPred(Pred pred1, Pred pred2, boolean and)
  {
    Pred ret = null;
    
    if(pred1 == null && pred2 == null) {
      ret = null;
    }
    else if(pred1 != null && pred2 == null) {
      ret = pred1;
    }
    else if(pred1 == null && pred2 != null) {
      ret = pred2;
    }
    else {
      List<Pred> lstPred = new ArrayList<Pred>();
      lstPred.add(pred1);
      lstPred.add(pred2);
      
      if(and) {
        ret = cfac_.createAndPred(lstPred, And.Wedge);
      }
      else {
        ret = cfac_.createOrPred(lstPred);
      }
    }

    return ret;
  }

  @Override
  public Object visitExprPred(ExprPred term)
  {
    Expr e = term.getExpr();
//    Circus2ZCSPUtils.isSchemaExpr(e);
    pred_ = null;
    visit(e);
    
    return null;
  }

  @Override
  public Object visitNegExpr(NegExpr term)
  {
    pred_ = null;
    visit(term.getExpr());
    
    if(pred_ == null || pred_ instanceof TruePred) {
      return null;
    }
    
    pred_ = cfac_.createNegPred(pred_);
    return null;
  }

  @Override
  public Object visitPred2(Pred2 term)
  {
//    Pred backup = pred_;
    pred_ = null;
    visit(term.getLeftPred());
    Pred left = pred_;
    visit(term.getRightPred());
    Pred right = pred_;
    term.setLeftPred(left);
    term.setRightPred(right);
    pred_ = term;
//    pred_ = backup;
    return null;
  }

  @Override
  public Object visitQntPred(QntPred term)
  {
//    Pred backup = pred_;
    pred_ = null;
    visit(term.getPred());
    Pred pred = pred_;
    term.setPred(pred);
//    pred_ = backup;
    pred_ = term;
    return null;
  }

  @Override
  public Object visitMemPred(MemPred term)
  {
    pred_ = term;
    return null;
  }

  @Override
  public Object visitNegPred(NegPred term)
  {
//    Pred backup = pred_;
    pred_ = null;
    visit(term.getPred());
    Pred pred = pred_;
    term.setPred(pred);
    pred_ = term;
//    pred_ = backup;
    return null;
  }
}

package net.sourceforge.czt.circus2zcsp.visitor;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus2zcsp.Debug;
import net.sourceforge.czt.circus2zcsp.util.AxParaKind;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.CompExpr;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.DecorExpr;
import net.sourceforge.czt.z.ast.Exists1Expr;
import net.sourceforge.czt.z.ast.ExistsExpr;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ForallExpr;
import net.sourceforge.czt.z.ast.HideExpr;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.LambdaExpr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NewOldPair;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.OutStroke;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.PipeExpr;
import net.sourceforge.czt.z.ast.PreExpr;
import net.sourceforge.czt.z.ast.ProjExpr;
import net.sourceforge.czt.z.ast.QntExpr;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.RenameExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.ast.ZStrokeList;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.CompExprVisitor;
import net.sourceforge.czt.z.visitor.DecorExprVisitor;
import net.sourceforge.czt.z.visitor.HideExprVisitor;
import net.sourceforge.czt.z.visitor.PipeExprVisitor;
import net.sourceforge.czt.z.visitor.PreExprVisitor;
import net.sourceforge.czt.z.visitor.ProjExprVisitor;
import net.sourceforge.czt.z.visitor.QntExprVisitor;
import net.sourceforge.czt.z.visitor.RefExprVisitor;
import net.sourceforge.czt.z.visitor.RenameExprVisitor;
import net.sourceforge.czt.z.visitor.SchExprVisitor;

/**
 * A visitor to get a list of variables declared in this schema, along with their type 
 * (not carrier set and just keep its original type [such as 1..3 instead of Z])
 * It might be not always right without normalization, especially for NegExpr and OrExpr 
 * (see an example????: https://sourceforge.net/p/czt/mailman/message/26924502/)
 * <ul>
 * <li> Solution </li>
 *      <ul>
 *      <li> normalize (only used to check if all lists are got) the schema to find a list of variables at first. </li>
 *        <ul>
 *            <li> normalisation_ = true </li>
 *            <li> set_state_comp_ contains a list of variables </li>
 *        </ul>
 *      <li> search the schema (for schema reference in the declaration part, just recursively search them), and  <br> 
 *           check their VarDecl in the declaration part. </li>
 *        <ul>
 *            <li> normalisation_ = false </li>
 *            <li> if the variable in VarDecl is a state component (set_state_comp_ contains this variable), <br>
 *            then make this variable's type as the type of this component. </li>
 *        </ul>
 *      <li> however, for schema rename expression, </li>
 *        <ul>
 *            <li> backup the set_name_expr_, and then clear it. </li>
 *            <li> visit the schema at first, but don't check if the variables are in set_state_comp_ (check_state_comp_ = false) <br>
 *            when adding them to set_name_expr_ because they might be renamed later. </li>
 *            <li> for each variable added to set_name_expr_, check if it is renamed (in rename list). If so, <br>
 *            check if its new name is in set_state_comp_. If its new name is in set_state_comp_, then this variable's new name <br>
 *            and its type are regarded as the pair added to the final set_name_expr_. </li>
 *            <li> restore the set_name_expr_ from the backup, and pend the pairs found in the previous step. </li> 
 *        </ul>
 *      </ul>
 * </ul>
 * 
 * @author rye
 *
 */
public class DeclListExpansionVisitor
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
    PipeExprVisitor<Object>
{
  private BasicProcess bp_ = null;
  private ZSect zs_ = null;
  private SectionManager manager_ = null;
  private String sectname_ = null;
  private Visitor<Object> visitor_ = this;
  /**
   * A set of all variables found in the schema and their corresponding type
   */
  private List<Pair<ZName, Expr>> set_name_expr_ = null;
  
  /**
   * A set of all variables found by normalisation
   */
  private Set<ZName> set_state_comp_ = null;
  
  /**
   * A flag to mark it is in normalisation or not
   * normalization always is applied once in the first entry of this Visitor in AxPara
   */
  private boolean normalisation_ = true;
  
  /**
   * A flag to mark if a variable should be checked in state components or not when adding it to set_name_expr_
   */
  private boolean check_state_comp_ = false;
  
  public DeclListExpansionVisitor(BasicProcess bp, ZSect zs, SectionManager manager, String sectname)
  {
    bp_                 = ZUtils.cloneTerm(bp);
    zs_                 = ZUtils.cloneTerm(zs);
    manager_            = manager;
    sectname_           = sectname;
    set_name_expr_      = new ArrayList<Pair<ZName, Expr>>();
    set_state_comp_     = new HashSet<ZName>(); 
  }
  
  public DeclListExpansionVisitor(ZSect zs, SectionManager manager, String sectname)
  {
    zs_                 = ZUtils.cloneTerm(zs);
    manager_            = manager;
    sectname_           = sectname;
    set_name_expr_      = new ArrayList<Pair<ZName, Expr>>();
    set_state_comp_     = new HashSet<ZName>();
  }
  
  public void disableNormalisation()
  {
    normalisation_ = false;
  }
  
  public void enableNormalisation()
  {
    normalisation_ = true;
  }
  
  public void clear()
  {
    set_name_expr_.clear();
    set_state_comp_.clear();
  }
  
  /**
   * Check if set_name_expr_ contains the pair given by (name, expr)
   * @param name
   * @param expr
   * @return
   *    true - set_name_expr_ contains this pair</br>
   *    false - set_name_expr_ doesn't contain this pair</br>
   */
  private boolean isSetContains(ZName name, Expr expr)
  {
    for(Pair<ZName, Expr> p : set_name_expr_) {
      if(Circus2ZCSPUtils.isEquals(p.getFirst(), name)) {
        if(Circus2ZCSPUtils.isEquals(p.getSecond(), expr)) {
          return true;
        }
      }
    }
    
    return false;
  }
  
  /**
   * Check if 'set' contains a pair which name is given by name
   * @param set - a set of pairs
   * @param name
   * @return
   *    true - set_name_expr_ contains this pair</br>
   *    false - set_name_expr_ doesn't contain this pair
   */
  private boolean isSetContains(Set<Pair<ZName, Expr>> set, ZName name)
  {
    for(Pair<ZName, Expr> p : set) {
      if(Circus2ZCSPUtils.isEquals(p.getFirst(), name)) {
        return true;
      }
    }
    
    return false;
  }
  
  /**
   * Check if 'set' contains the pair given by name
   * @param set - a set of pairs
   * @param name
   * @param expr
   * @return
   *    true - set_name_expr_ contains this pair</br>
   *    false - set_name_expr_ doesn't contain this pair
   */
  private boolean isSetContains(Set<Pair<ZName, Expr>> set, ZName name, Expr expr)
  {
    for(Pair<ZName, Expr> p : set) {
      if(Circus2ZCSPUtils.isEquals(p.getFirst(), name) &&
          p.getSecond().equals(expr)) {
        return true;
      }
    }
    
    return false;
  }
  
  /**
   * Check if a name is in set_state_comp_ or not 
   * @param name
   * @return
   *    true - set_state_comp_ contains this name</br>
   *    false - set_state_comp_ doesn't contain this name
   */
  private boolean isStateComps(ZName name) 
  {
    for(ZName n : set_state_comp_) {
      if(Circus2ZCSPUtils.isEquals(n, name)) {
        return true;
      }
    }
    
    return false;
  
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
    Set<Pair<ZName, Expr>> backup = new HashSet<Pair<ZName, Expr>>();
    
    // for reference, just remove prefixing Delta or Xi
    if(ZUtils.isDeltaXi(term.getZName())) {
      backup.addAll(set_name_expr_);
      set_name_expr_.clear();

      refName.setWord(refName.getWord().replace(ZString.DELTA, "").replace(ZString.XI, ""));
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
    //          Debug.debug_print("Found " + str);
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
    //          Debug.debug_print("Found " + str);
              visit(ap);
              break;
            }
          }
        }
      }
    }
    
    if(ZUtils.isDeltaXi(term.getZName())) {
      // for Delta or Xi, another copy of dashed variables (v') is added. 
      ZFactory fac = new net.sourceforge.czt.z.impl.ZFactoryImpl();
      for(Pair<ZName, Expr> p: set_name_expr_) {
        ZName n = ZUtils.cloneTerm(p.getFirst());
        n.getZStrokeList().add(fac.createNextStroke());
        if(!isSetContains(backup, n, p.getSecond())) {
          backup.add(new Pair<ZName, Expr>(n, p.getSecond()));
        }
        // also along with itself
        if(!isSetContains(backup, p.getFirst(), p.getSecond())) {
          backup.add(p);
        }
      }
      set_name_expr_.clear();
      set_name_expr_.addAll(backup);
    }
    return null;
  }

  @Override
  public Object visitAxPara(AxPara term)
  {
    AxParaKind kind = Circus2ZCSPUtils.getAxParaKind(term);
    Expr expr;
    boolean firstentry = false;
    
    // use normalisation to check if all declarations are identified
    if(normalisation_) {
      firstentry = true;
      SchExpr schExpr = null;
      
      switch(kind) {
        case ABBR:
          expr = ZUtils.getAbbreviationExpr(term);
          schExpr = Circus2ZCSPUtils.expansionSchema(expr, sectname_, manager_);
          break;
        case HORIZON_SCHEMA:
        case BOXED_SCHEMA:
          expr = ZUtils.getSchemaDefExpr(term);
          schExpr = Circus2ZCSPUtils.expansionSchema(expr, sectname_, manager_);
          break;
        default:
          throw new CztException("Only a schema or schema abbreviation can be expanded, but it is " + kind.toString());
      }
      
      if(schExpr != null) {
        visit(schExpr);
      }
    }
    
    normalisation_ = false;
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

    // only check the first entry of AxPara since that is the time to apply normalization
    if(firstentry) {
      Set<String> list = new HashSet<String>();
      for(ZName n: set_state_comp_) {
        list.add(Circus2ZCSPUtils.termToString(n));
      }
      
      // double check if the declaration list we are is the same as the normalization
      for(Pair<ZName, Expr> p : set_name_expr_) {
        String name = Circus2ZCSPUtils.termToString(p.getFirst());
        if(!list.contains(name)) {
          throw new CztException("The variable [" + Circus2ZCSPUtils.termToString(p.getFirst()) + 
              "] is not expected in the normalisation list! \n"
              + "The implementation of DeclListExpansionVisitor might have problems!" );
//          Debug.debug_print("The variable [" + Circus2ZCSPUtils.termToString(p.getFirst()) + 
//              "] is not expected in the normalisation list! \n"
//              + "The implementation of DeclListExpansionVisitor might have problems!");
        } else {
          list.remove(name);
        }
      }
      
      if(!list.isEmpty()) {
        throw new CztException("The variables in [" + list.toString() + "] are not correctly identified!\n "
            + "The implementation of DeclListExpansionVisitor might have problems!");
//        Debug.debug_print("The variables in [" + list.toString() + "] are not correctly identified!\n "
//            + "The implementation of DeclListExpansionVisitor might have problems!");
      }
    }
    
    return null;
  }
  
  public Set<Pair<ZName, Expr>> getNameExprPair()
  {
    Set<Pair<ZName, Expr>> ret = new HashSet<Pair<ZName, Expr>>();
    ret.addAll(set_name_expr_);
    return ret;
  }
  
  public List<Pair<ZName, Expr>> getNameExprPairAsList()
  {
    return set_name_expr_;
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
        for(Name name: vd.getZNameList()) {
          if(normalisation_) {
            if(!isStateComps((ZName) name)) {
              // add state components name 
              set_state_comp_.add((ZName) name);
            }
          }
          else {
            if(check_state_comp_) {
              if(isStateComps((ZName) name)) {
                ((ZName)name).setId(null); // to avoid duplicate entries
                if(!isSetContains((ZName) name, vd.getExpr())) {
//                  Debug.debug_print("Add " + name.toString() + ", " + vd.getExpr().toString());
                  set_name_expr_.add(new Pair<ZName, Expr>((ZName)name, vd.getExpr()));
                }
              }
            }
            else {
              ((ZName)name).setId(null); // to avoid duplicate entries
              if(!isSetContains((ZName) name, vd.getExpr())) {
//                Debug.debug_print("Add " + name.toString() + ", " + vd.getExpr().toString());
                set_name_expr_.add(new Pair<ZName, Expr>((ZName)name, vd.getExpr()));
              }
            }
          }
        }
      }
      else {
        visit(decl);
      }
    }
        
    return null;
  }

  @Override
  public Object visitRenameExpr(RenameExpr term)
  {
    Set<Pair<ZName, Expr>> backup = new HashSet<Pair<ZName, Expr>>();
    
    backup.addAll(set_name_expr_);
    set_name_expr_.clear();
    check_state_comp_ = false;
    
    visit(term.getExpr());
  
    // difference
    for(Pair<ZName, Expr> p: set_name_expr_) {
      for(NewOldPair np: term.getZRenameList()) {
        if(Circus2ZCSPUtils.isEquals((ZName) np.getOldName(), p.getFirst())) {
          if(!isSetContains(backup, (ZName) np.getNewName(), p.getSecond())) {
            backup.add(new Pair<ZName, Expr>((ZName) np.getNewName(), p.getSecond()));
//            Debug.debug_print("Add in Rename: " + np.getNewName().toString() + ", " + p.getSecond().toString());
          }
        }
      }
    }

    check_state_comp_ = false;
    set_name_expr_.clear();
    set_name_expr_.addAll(backup);
    return null;
  }

  @Override
  public Object visitDecorExpr(DecorExpr term)
  {
    /*
     * 1. For a DecorExpr, visit its expression. After that, all declared variables will append a corresponding stroke
     */

    Set<Pair<ZName, Expr>> backup = new HashSet<Pair<ZName, Expr>>();
    backup.addAll(set_name_expr_);
    set_name_expr_.clear();
    check_state_comp_ = false;
    
    visit(term.getExpr());
    
    // difference
    for(Pair<ZName, Expr> p: set_name_expr_) {
      ZName n = ZUtils.cloneTerm(p.getFirst());
      n.getZStrokeList().add(term.getStroke());
      if(!isSetContains(backup, n, p.getSecond())) {
        backup.add(new Pair<ZName, Expr>(n, p.getSecond()));
//            Debug.debug_print("Add in Rename: " + np.getNewName().toString() + ", " + p.getSecond().toString());
      }
    }

    check_state_comp_ = false;
    set_name_expr_.clear();
    set_name_expr_.addAll(backup);
    return null;
  }

  @Override
  public Object visitHideExpr(HideExpr term)
  {
    Set<Pair<ZName, Expr>> backup = new HashSet<Pair<ZName, Expr>>();
    backup.addAll(set_name_expr_);
    set_name_expr_.clear();
    check_state_comp_ = false;

    visit(term.getExpr());
    
    // take all variables in its hiding name list out of set_name_expr_
    boolean found = false;
    for(Pair<ZName, Expr> p: set_name_expr_) {
      found = false;
      for(Name n: term.getZNameList()) {
        if(Circus2ZCSPUtils.isEquals(p.getFirst(), (ZName)n)) {
          found = true;
          break;
        }
      }
      if(!found) {
        // not in the hide list, then add it
        if(!isSetContains(backup, p.getFirst(), p.getSecond())) {
          backup.add(p);
        }
      }
    }

    check_state_comp_ = false;
    set_name_expr_.clear();
    set_name_expr_.addAll(backup);

    return null;
  }

  @Override
  public Object visitQntExpr(QntExpr term)
  {
    Set<Pair<ZName, Expr>> setDecl = new HashSet<Pair<ZName, Expr>>();
    Set<Pair<ZName, Expr>> backup = new HashSet<Pair<ZName, Expr>>();
    backup.addAll(set_name_expr_);
    set_name_expr_.clear();
    check_state_comp_ = false;
    
    // Get all variables declared
    for(Decl decl: term.getZSchText().getZDeclList()) {
      if(decl instanceof VarDecl) {
        for(Name n: ((VarDecl)decl).getZNameList()) {
          setDecl.add(new Pair<ZName, Expr>((ZName) n, ((VarDecl)decl).getExpr()));
        }
      }
      else if(decl instanceof InclDecl) {
        visit(((InclDecl)decl).getExpr());
      }
    }
    
    for(Pair<ZName, Expr> p: set_name_expr_) {
      if(!isSetContains(setDecl, p.getFirst(), p.getSecond())) {
        setDecl.add(p);
      }
    }

    if(term instanceof Exists1Expr || 
       term instanceof ExistsExpr ||
       term instanceof ForallExpr) {
      // Quantifier over schema expression
      set_name_expr_.clear();
      visit(term.getExpr());
      
      // take all variables in setDecl out of set_name_expr_
      for(Pair<ZName, Expr> p: set_name_expr_) {
        // only check the variable name and not its type
        if(!isSetContains(setDecl, p.getFirst())) {
          backup.add(new Pair<ZName, Expr>(p.getFirst(), p.getSecond()));
//              Debug.debug_print("Add in Rename: " + np.getNewName().toString() + ", " + p.getSecond().toString());
        }
      }

      check_state_comp_ = false;
      set_name_expr_.clear();
      set_name_expr_.addAll(backup);
    }
    else if(term instanceof LambdaExpr) {
      // A schema in LambdaExpr only keep its declaration used locally and so skip it
    }
    else {
      // ignore others
    }
    return null;
  }

  @Override
  public Object visitProjExpr(ProjExpr term)
  {
    // the signaure of S \proj T is equal to that of T
    visit(term.getRightExpr());
    return null;
  }

  @Override
  public Object visitPreExpr(PreExpr term)
  {
    Set<Pair<ZName, Expr>> backup = new HashSet<Pair<ZName, Expr>>();
    backup.addAll(set_name_expr_);
    set_name_expr_.clear();
    check_state_comp_ = false;

    visit(term.getExpr());
    
    // take all variables in its hiding name list out of set_name_expr_
    for(Pair<ZName, Expr> p: set_name_expr_) {
      ZStrokeList zsl = p.getFirst().getZStrokeList();
      // not a v' or v!, then add it since they are hidden.
      if(!(zsl.size() > 0 && 
          (zsl.get(zsl.size() - 1) instanceof NextStroke || 
          zsl.get(zsl.size() - 1) instanceof OutStroke)
         )) {
        if(!isSetContains(backup, p.getFirst(), p.getSecond())) {
          backup.add(p);
        }        
      }
    }

    check_state_comp_ = false;
    set_name_expr_.clear();
    set_name_expr_.addAll(backup);

    return null;
  }

  @Override
  public Object visitCompExpr(CompExpr term)
  {
    Set<Pair<ZName, Expr>> backup = new HashSet<Pair<ZName, Expr>>();
    backup.addAll(set_name_expr_);
    set_name_expr_.clear();
    check_state_comp_ = false;

    Set<Pair<ZName, Expr>> setExpr1 = new HashSet<Pair<ZName, Expr>>();
    visit(term.getLeftExpr());
    setExpr1.addAll(set_name_expr_);
    set_name_expr_.clear();
    
    Set<Pair<ZName, Expr>> setExpr2 = new HashSet<Pair<ZName, Expr>>();
    visit(term.getRightExpr());
    setExpr2.addAll(set_name_expr_);
    set_name_expr_.clear();
    
    // if setExpr1 contains (s, s') and setExpr2 contains (v, v'), and (s and v must refer to the same variable)
    // finally, only (s, v') will be kept
    for(Pair<ZName, Expr> p1: setExpr1) {
      ZStrokeList zsl1 = p1.getFirst().getZStrokeList();
      // s'
      if(zsl1.size() > 1 && zsl1.get(zsl1.size() - 1) instanceof NextStroke) {
        boolean found = false;
        Pair<ZName, Expr> p = null;
        for(Pair<ZName, Expr> p2: setExpr2) {
          ZStrokeList zsl2 = p2.getFirst().getZStrokeList();
          // if they have the same name
          if(p2.getFirst().getWord().equals(p1.getFirst().getWord())) {
            // if the second one has no stroke, or last stroke is not '
            if(zsl2.size() == 0 || 
                (zsl2.size() > 0 && !(zsl2.get(zsl2.size() - 1) instanceof NextStroke))) {
              found = true;
              p = p2;
              break;
            }
          }
        }
        // remove v from setExpr2
        if(found) {
          setExpr2.remove(p);
        }
      }
      else {
        if(!isSetContains(backup, p1.getFirst(), p1.getSecond())) {
          backup.add(p1);
        } 
      }
    }

    // add v' as well
    for(Pair<ZName, Expr> p: setExpr2) {
      if(!isSetContains(backup, p.getFirst(), p.getSecond())) {
        backup.add(p);
      } 
    }
    
    check_state_comp_ = false;
    set_name_expr_.clear();
    set_name_expr_.addAll(backup);

    return null;
  }

  @Override
  public Object visitPipeExpr(PipeExpr term)
  {
    Set<Pair<ZName, Expr>> backup = new HashSet<Pair<ZName, Expr>>();
    backup.addAll(set_name_expr_);
    set_name_expr_.clear();
    check_state_comp_ = false;

    Set<Pair<ZName, Expr>> setExpr1 = new HashSet<Pair<ZName, Expr>>();
    visit(term.getLeftExpr());
    setExpr1.addAll(set_name_expr_);
    set_name_expr_.clear();
    
    Set<Pair<ZName, Expr>> setExpr2 = new HashSet<Pair<ZName, Expr>>();
    visit(term.getRightExpr());
    setExpr2.addAll(set_name_expr_);
    set_name_expr_.clear();
    
    // if setExpr1 contains (s, s', x?, y!) and setExpr2 contains (v, v', y?, z!), 
    // then y! and y? will be hidden.
    for(Pair<ZName, Expr> p1: setExpr1) {
      ZStrokeList zsl1 = p1.getFirst().getZStrokeList();
      // y!
      if(zsl1.size() > 1 && zsl1.get(zsl1.size() - 1) instanceof OutStroke) {
        boolean found = false;
        Pair<ZName, Expr> p = null;
        for(Pair<ZName, Expr> p2: setExpr2) {
          ZStrokeList zsl2 = p2.getFirst().getZStrokeList();
          // if they have the same name, y?
          if(p2.getFirst().getWord().equals(p1.getFirst().getWord())) {
            // if the second one has no stroke, or last stroke is not '
            if(zsl2.get(zsl2.size() - 1) instanceof InStroke) {
              found = true;
              p = p2;
              break;
            }
          }
        }
        // remove v from setExpr2
        if(found) {
          setExpr2.remove(p);
        }
      }
      else {
        if(!isSetContains(backup, p1.getFirst(), p1.getSecond())) {
          backup.add(p1);
        } 
      }
    }

    // add v' as well
    for(Pair<ZName, Expr> p: setExpr2) {
      if(!isSetContains(backup, p.getFirst(), p.getSecond())) {
        backup.add(p);
      } 
    }
    
    check_state_comp_ = false;
    set_name_expr_.clear();
    set_name_expr_.addAll(backup);

    return null;
  }
}

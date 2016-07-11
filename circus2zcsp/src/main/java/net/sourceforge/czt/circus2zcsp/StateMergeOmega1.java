package net.sourceforge.czt.circus2zcsp;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.ChannelPara;
import net.sourceforge.czt.circus.ast.ChannelSetPara;
import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus2zcsp.data.CircusSpecMap;
import net.sourceforge.czt.circus2zcsp.data.FormatPattern;
import net.sourceforge.czt.circus2zcsp.util.AxParaKind;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.circus2zcsp.visitor.DeclListExpansionVisitor;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.And;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.DecorExpr;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.OptempPara;
import net.sourceforge.czt.z.ast.OutStroke;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SchText;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.ast.ZStrokeList;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;

/**
 * This class is to implement the Omega_1 function
 *      The function Ω1 translates the state part in 
 *      a rewritten Circus program to a Z specification 
 *      in ISO Standard Z.
 * @author rye
 *
 */
public class StateMergeOmega1
{
  // a Z Section
  private ZSect zsect_;
  private ZParaList paraList_;
  private Parent parent_;
  
  private final SectionManager manager_;
  private final CircusSpecMap map_;
  private final ZSect zs_;
  
  private ZFactory fac_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
  private CircusFactory cfac_ = new net.sourceforge.czt.circus.impl.CircusFactoryImpl();
  
  /**
   * A set of state variables
   */
  private final Set<ZName> set_state_ = new HashSet<ZName>();
  
  public ZSect getZSect() 
  {
    zsect_.setParaList(paraList_);
    zsect_.getParent().add(parent_);
    return zsect_;
  }
  
  /**
   * 
   * @param zs - a rewritten Circus section
   * @param map_ - 
   */
  public StateMergeOmega1(ZSect zs, CircusSpecMap map, SectionManager manager, List<Pred> initpreds) 
  {
    manager_ = manager;
    map_ = map;
    zs_ = zs;
    
    parent_ = fac_.createParent("standard_toolkit");
    paraList_ = fac_.createZParaList();
    zsect_ = fac_.createZSect();// section, parents, paraList);
    
    // a list of basic processes
    List<BasicProcess> lstBscProc = new ArrayList<BasicProcess>();
    
    // a list of corresponding state schema's name
    List<ZName> lstStName = new ArrayList<ZName>();
    
    // a list of corresponding initialisation schema's predicate
    List<Pred> lstInitPred = new ArrayList<Pred>();
    
    lstInitPred.addAll(initpreds);
    
    ZParaList paralist = zs.getZParaList();
    for (net.sourceforge.czt.z.ast.Para para : paralist) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          BasicProcess bp = (BasicProcess) ((ProcessPara)para).getCircusProcess();
          lstBscProc.add(bp);
          lstStName.add((ZName) bp.getStateParaName());
//          lstInitPred.add(Circus2ZCSPUtils.extractInitSchema(fac_, bp, ((ProcessPara)para).getZName()));
          paraList_.add(bp.getStatePara());
        }
        else {
          // skip
        }
      }
      else if (para instanceof NarrPara) {
        // skip
      }
      else if (para instanceof ChannelPara) {
        // skip
      }
      else if (para instanceof ChannelSetPara) {
        // skip
      }
      else if (para instanceof LatexMarkupPara) {
        // skip
      }
      else if (para instanceof AxPara) // Axiom Definition
      {
        // For Abbreviation, add it to paraList and also CSP
        paraList_.add(para);
      }
      else if (para instanceof FreePara) {
        paraList_.add(para);
      }
      else if (para instanceof GivenPara) {
        paraList_.add(para);
      }
      else if (para instanceof OptempPara) {
        paraList_.add(para);
      }
    }
    
    // construct state schema
    paraList_.add(assembleZStatePara(lstStName));
    
    // construct initialisation schema
    paraList_.add(assembleZInitPara(lstInitPred));
    
    // construct other schemas
    handleOtherSchemas(lstBscProc, lstStName);
  }
  
  public AxPara assembleZStatePara(List<ZName> lstStName)
  {
    // 0. State retrieve paragraph OP_x
    String paraName = FormatPattern.STATE_PARA_NAME_PATT;
    ZName paraname = fac_.createZName(paraName, fac_.createZStrokeList(), null);
//    ZName dummyState = fac_.createZName(FormatPattern.EMPTY_STATE_PARA_NAME_PATT,
//        fac_.createZStrokeList(), null);
    Expr expr = null;
    if(lstStName.size() == 0) {
      throw new CztException("There is no state schemas specified!");
    }
    else if(lstStName.size() == 1) {
      expr = fac_.createRefExpr(lstStName.get(0), fac_.createZExprList(), false, false);
    } else {
      for(int i = 0; i < lstStName.size(); i++) {
        List<Expr> lstExpr = new ArrayList<Expr>();
        if(expr == null) {
          lstExpr.add(fac_.createRefExpr(lstStName.get(0), fac_.createZExprList(), false, false));
          lstExpr.add(fac_.createRefExpr(lstStName.get(1), fac_.createZExprList(), false, false));
          expr = fac_.createAndExpr(lstExpr);
          i++;
        } else {
          lstExpr.add(expr);
          lstExpr.add(fac_.createRefExpr(lstStName.get(i), fac_.createZExprList(), false, false));
          expr = fac_.createAndExpr(lstExpr);
        }
      }
    }
    
    ConstDecl cd = fac_.createConstDecl(paraname, expr);
  
    ZDeclList declList0 = fac_.createZDeclList();
    declList0.add(cd);
    
    SchText schtext = fac_.createZSchText(declList0, null);
  
    ZNameList fp = fac_.createZNameList();
    AxPara axpara = fac_.createAxPara(fp, schtext, Box.OmitBox);
  
    return axpara;
  }
  
  public AxPara assembleZInitPara(List<Pred> lstInitPred)
  {
    // 0. State retrieve paragraph OP_x
    String paraName = FormatPattern.INIT_SCHEMA_NAME;
    ZName paraname = fac_.createZName(paraName, fac_.createZStrokeList(), null);
    ZName stname = fac_.createZName(FormatPattern.STATE_PARA_NAME_PATT, fac_.createZStrokeList(), null);
    
    Pred pred = null;
    if(lstInitPred.size() == 0) {
      throw new CztException("There is no predicate of the initialisation schema specified!");
    }
    else if(lstInitPred.size() == 1) {
      pred = lstInitPred.get(0);
    } else {
      for(int i = 0; i < lstInitPred.size(); i++) {
        List<Pred> lstPred = new ArrayList<Pred>();
        if(pred == null) {
          lstPred.add(lstInitPred.get(0));
          lstPred.add(lstInitPred.get(1));
          pred = fac_.createAndPred(lstPred, And.Wedge);
          i++;
        } else {
          lstPred.add(pred);
          lstPred.add(lstInitPred.get(i));
          pred = fac_.createAndPred(lstPred, And.Wedge);
        }
      }
    }
    
    RefExpr re = fac_.createRefExpr(stname, fac_.createZExprList(), false, false);
    DecorExpr dExpr = fac_.createDecorExpr(re, fac_.createNextStroke());
    InclDecl inclDecl = fac_.createInclDecl(dExpr);
    List<Decl> lstDecl = new ArrayList<Decl>();
    lstDecl.add(inclDecl);
    ZDeclList zdl = fac_.createZDeclList(lstDecl);
    SchText schText = fac_.createZSchText(zdl, pred);
    SchExpr se = fac_.createSchExpr(schText);
    ConstDecl cd = fac_.createConstDecl(paraname, se);
  
    ZDeclList declList0 = fac_.createZDeclList();
    declList0.add(cd);
    
    SchText schtext = fac_.createZSchText(declList0, null);
  
    ZNameList fp = fac_.createZNameList();
    AxPara axpara = fac_.createAxPara(fp, schtext, Box.OmitBox);
  
    return axpara;
  }
  
  /**
   * Get the index of State paragraph in the paraList_
   * @return
   */
  private int getIndexOfStatePara(BasicProcess bp) 
  {
    int ret = 0;
    for(Para p: paraList_) {
      if(p instanceof AxPara) {
        if(ZUtils.isAxParaSchemaOrHorizDefValid((AxPara)p)) {
          Name name = ZUtils.getAxParaSchOrAbbrName(p);
          if(name != null && (p.equals(bp.getStatePara()) ||
              Circus2ZCSPUtils.termToString(name).equals(FormatPattern.STATE_PARA_NAME_PATT))) {
            break;
          }
        }
      }
      
      ret++;
    }
    return ret;
  }
  
  private void handleOtherSchemas(List<BasicProcess> lstBscProc, List<ZName> lstStName)
  {
    if(lstBscProc.size() == 0) {
      throw new CztException("There is no BasicProcess specified!");
    }
    
    for(int i = 0; i < lstBscProc.size(); i++) {
      BasicProcess bp = lstBscProc.get(i);
      
      // get a set of state components
      AxPara stateAP = bp.getStatePara();
      DeclListExpansionVisitor dlevisitor = new DeclListExpansionVisitor(bp, zs_, manager_, zs_.getName());
      // after renaming, normalisation might not work properly, so disable it
      dlevisitor.disableNormalisation();
      stateAP.accept(dlevisitor);
      Set<Pair<ZName, Expr>> lstStateNameExpr = dlevisitor.getNameExprPair();
      set_state_.clear();
      
      ZStrokeList zsl = fac_.createZStrokeList();
      zsl.add(fac_.createNextStroke());
      for(Pair<ZName, Expr> p: lstStateNameExpr) {
        set_state_.add(p.getFirst()); // v
        set_state_.add(fac_.createZName(p.getFirst().getWord(), zsl, null)); //v'
      }

      // is current paragraph before state paragraph of this BasicProcess?
      boolean beforeState = true;
      
      for(Para p: bp.getZParaList()) {
        if(p instanceof AxPara) {
          // Check if it is an operational schema or not. Only operational schema will 
          // include Xi of other state schemas
          if(p.equals(bp.getStatePara())) {
            beforeState = false;
            continue;
          }
          
          if(!isOperationalSchema((AxPara)p, bp)) {
            if(beforeState) {
              int indexOfState = getIndexOfStatePara(bp);
              paraList_.add(indexOfState, p);
            }
            else {
              paraList_.add(p);
            }
            continue;
          }
          
          if(ZUtils.isAxParaSchemaOrHorizDefValid((AxPara)p)) {
//            ZName paraName = (ZName) ZUtils.getAxParaSchOrAbbrName(p);
            if(ZUtils.isSimpleSchema(p)) {
              AxPara ap = (AxPara) ZUtils.cloneTerm(p);
              SchExpr expr = (SchExpr) ZUtils.getSchemaDefExpr(p);
              ZDeclList zdl = expr.getZSchText().getZDeclList();
              for(int j = 0; j < lstStName.size(); j++) {
                if(j != i) {
                  ZName stname = fac_.createZName(ZString.XI + lstStName.get(j), fac_.createZStrokeList(), null);
                  RefExpr re = fac_.createRefExpr(stname, fac_.createZExprList(), false, false);
                  zdl.add(fac_.createInclDecl(re));
                }
              }
              ((SchExpr)(((ConstDecl)ap.getZSchText().getZDeclList().get(0)).getExpr())).getZSchText().setDeclList(zdl);
              // add before or after state paragraph
              /*if(beforeState) {
                int indexOfState = getIndexOfStatePara(bp);
                paraList_.add(indexOfState, ap);
              }
              else*/ {
                paraList_.add(ap);
              }
            }
            else if(ZUtils.isAbbreviation(p)) {
              Expr expr = ZUtils.getAbbreviationExpr(p);
              for(int j = 0; j < lstStName.size(); j++) {
                if(j != i) {
                  ZName stname = fac_.createZName(ZString.XI + lstStName.get(j), fac_.createZStrokeList(), null);
                  RefExpr re = fac_.createRefExpr(stname, fac_.createZExprList(), false, false);
                  List<Expr> lstExpr = new ArrayList<Expr>();
                  lstExpr.add(expr);
                  lstExpr.add(re);
                  expr = fac_.createAndExpr(lstExpr);
                }
              }
              
              ((ConstDecl)((AxPara)p).getZSchText().getZDeclList().get(0)).setExpr(expr);
              
              /*if(beforeState) {
                int indexOfState = getIndexOfStatePara(bp);
                paraList_.add(indexOfState, p);
              }
              else*/ {
                paraList_.add(p);
              }
            }
            else {
              throw new CztException("An invalid AxPara. We only convert simple schema and abbreviation!");
            }
          }
          else {
            paraList_.add(p);
          }
        }
      }
    }
  }
  
  private boolean isOperationalSchema(AxPara ap, BasicProcess bp)
  {
    AxParaKind apk = Circus2ZCSPUtils.getAxParaKind(ap);
    if(apk == AxParaKind.AXDEF || apk == AxParaKind.GEN_AXDEF) {
      return false;
    }

    ZName name = null;
    if(apk == AxParaKind.ABBR || apk == AxParaKind.GEN_ABBR) {
      name = (ZName) ZUtils.getAbbreviationName(ap);
    }
    else if(apk == AxParaKind.BOXED_SCHEMA || apk == AxParaKind.HORIZON_SCHEMA || 
        apk == AxParaKind.GEN_BOXED_SCHEMA || apk == AxParaKind.GEN_HORIZON_SCHEMA) {
      name = (ZName) ZUtils.getSchemaName(ap);
    }
    
    DeclListExpansionVisitor dlevisitor2 = new DeclListExpansionVisitor(bp, zs_, manager_, zs_.getName());
    // after renaming, normalisation might not work properly, so disable it
    dlevisitor2.disableNormalisation();
    ap.accept(dlevisitor2);
    Set<Pair<ZName, Expr>> lstStateNameExpr2 = dlevisitor2.getNameExprPair();
    
    Set<ZName> setVars = new HashSet<ZName>();
    Debug.debug_print(
        Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
        Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
        Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
        "=============== isOperationalSchema [" + name.toString() + "] =====================");
    Debug.debug_print(
        Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
        Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
        Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
        "Variables found: " + lstStateNameExpr2.size());
    for(Pair<ZName, Expr> p: lstStateNameExpr2) {
      Debug.debug_print(
          Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
              Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
              Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
              Circus2ZCSPUtils.termToString(p.getFirst()) + "," + 
              Circus2ZCSPUtils.termToString(p.getSecond()));
      setVars.add(p.getFirst());
    }
    Debug.debug_print(
        Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
        Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
        Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
        "Variables added: " + setVars.size());
    
    /**
     * for each variables declared in ap (to be an operation) it might be
     *   state variable (v)
     *   dashed state variable (v')
     *   input variable (v?)
     *   output variable (v!)
     * and it should include
     *   all state variables and their dashed copy as well
     */
    Set<ZName> setState = new HashSet<ZName>();
    setState.addAll(set_state_);
    
    for(ZName v: setVars) {
      boolean valid = false;
      // 1. is in setState and then delete it from setState
      for(ZName st: setState) {
        if(Circus2ZCSPUtils.isEquals(v, st)) {
          valid = true;
          setState.remove(st);
          break;
        }
      }
      
      if(!valid) {
        if(v.getZStrokeList().size() == 1 && v.getZStrokeList().get(0) instanceof OutStroke) {
          continue;
        }
        else if(v.getZStrokeList().size() == 1 && v.getZStrokeList().get(0) instanceof InStroke) {
          continue;
        }
        else {
          return false;
        }
      }
    }
    
    if(!setState.isEmpty()) {
      return false;
    }
    
    // TODO: should check the reference as well to determine if it is an operation
    // an operation is not referred in other schemas, except \pre expression.
    return true;
  }
}

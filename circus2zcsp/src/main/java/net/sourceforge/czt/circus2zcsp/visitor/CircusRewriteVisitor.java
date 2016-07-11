/**
 * 
 */
package net.sourceforge.czt.circus2zcsp.visitor;

import java.math.BigInteger;
import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;
import java.util.TreeSet;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.ListTermVisitor;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus.ast.*;
import net.sourceforge.czt.circus.util.CircusString;
import net.sourceforge.czt.circus.visitor.CircusVisitor;
import net.sourceforge.czt.circus2zcsp.Debug;
import net.sourceforge.czt.circus2zcsp.ast.CSPSpec;
import net.sourceforge.czt.circus2zcsp.conf.Config;
import net.sourceforge.czt.circus2zcsp.data.CSPPredExpPattern;
import net.sourceforge.czt.circus2zcsp.data.CircusSpecMap;
import net.sourceforge.czt.circus2zcsp.data.FormatPattern;
import net.sourceforge.czt.circus2zcsp.data.PredExpPattern;
import net.sourceforge.czt.circus2zcsp.data.Triple;
import net.sourceforge.czt.circus2zcsp.data.VariableRenameSchema;
import net.sourceforge.czt.circus2zcsp.data.VersionInfo;
import net.sourceforge.czt.circus2zcsp.util.AxParaKind;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.circus2zcsp.util.MemPredKind;
import net.sourceforge.czt.circus2zcsp.util.RefExprKind;
import net.sourceforge.czt.circus2zcsp.util.SpecStmtKind;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.parser.util.DefinitionType;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.RuleTable.RuleTableException;
import net.sourceforge.czt.rules.UnboundJokerException;
import net.sourceforge.czt.rules.rewriter.RewriteUtils;
import net.sourceforge.czt.rules.rewriter.Strategies;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfoException;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.ZVisitor;

/**
 * CircusRewriteVisitor: the visitor to implement the rewrite of Circus, including
 *      1) process rewrite (rewrite_stage_ = 1)
 *      2) Z schema paragraphs and action paragraphs rewrite (rewrite_stage_ = 2..4)
 * @author rye
 *
 */
public class CircusRewriteVisitor
    implements
      TermVisitor<Object>,
      ListTermVisitor<Object>,
      ZVisitor<Object>,
      CircusVisitor<Object>
{

  // a map from original variable or schema name to replaced new name
  private CircusSpecMap map_ = null;

  //  private String proname_ = null;

  private ZFactory fac_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();

  private CircusFactory cfac_ = new net.sourceforge.czt.circus.impl.CircusFactoryImpl();

  private Visitor<Object> visitor_ = this;

  private SectionManager manager_ = null;

  private DefinitionTable deftable_ = null;

  private String sectname_ = null;
  private ZSect zsect_ = null;
  
  // original para list
  private ZParaList paralist_ = null;
  
  // new para list after rewritten
  private ZParaList new_paralist_ = null;
  
  // temporary paragraph name
  private String para_name_ = null;
  
  // temporary paragraph name
  private List<Object> list_ann_ = null;

  /**
   * a stack of CircusProcess
   *    basically it is for the current term to find its direct parent (it's useful when rewriting parametrised invocation)
   */
  private final Stack<CircusProcess> circus_process_stack_;
  
  /**
   * Current processpara in processing
   */
  private ProcessPara process_para_ = null;
  
  /**
   * a stack of CircusAction
   *    basically it is for the current term to find its direct parent (it's useful when rewriting action)
   */
  private final Stack<CircusAction> circus_action_stack_;
  
  /**
   * a stack of declaration in MuAction
   *    basically it is used to check if a CallAction is a reference to an Action or to MuAction
   */
  private final Stack<ZName> circus_muaction_stack_;
  
  /**
   * Rewrite stage:
   *    1 - Process
   *    2 - Additional State Components Retrieve Schemas (BasicProcess)
   *    3 - Renaming of State Components, Schemas, Actions and their Refereneces (BasicProcess)
   *    4 - Action Rewriting
   */
  private int rewrite_stage_ = 1;
  
  /**
   * context or environment to maintain local variables in scope (a map from the variable name to its type) 
   * 1. from input channel, such as c?x, c!y?x?z 
   * 2. from variable block
   */
  private final Stack<Pair<String, Term>> loc_vars_stack_;
  
  private final Config config_;
  
  private final CSPSpec cspspec_;
  
  private final Stack<Term> stack_parent_;
  
  /**
   * A list of generic AxPara within a process
   */
  private final List<AxPara> generic_axpara_global_ = new ArrayList<AxPara>();
  
  /**
   * A list of generic channel declaration
   */
  private final List<ChannelDecl> generic_channel_decl_ = new ArrayList<ChannelDecl>();

  /**
   * A list of generic AxPara within a process
   */
  private final List<AxPara> generic_axpara_in_proc_ = new ArrayList<AxPara>();

  /**
   * A list of generic processes
   */
  private final List<ProcessPara> generic_process_para_ = new ArrayList<ProcessPara>();
  
  /**
   * A map from generic instantiation of RefExpr to its new rewritten RefExpr
   */
  private final Map<RefExpr, RefExpr> map_generic_refexpr_ = new HashMap<RefExpr, RefExpr>();
  
  /**
   * A set of terms that are visited before for action rewrite in stage 4
   * So it's no need to rewrite again
   * For example, if we have 
   *    out!s1!s2 -> SKIP [] out!s1!s2 -> SKIP
   * and both actions refer to the same term, then rewrite once it will become
   *    Op_s1?s1 -> Op_s2?s2 -> out!s1!s2 -> SKIP [] Op_s1?s1 -> Op_s2?s2 -> out!s1!s2 -> SKIP
   * If no check of visited term, it will visit twice and lead to 
   *    Op_s1?s1 -> Op_s2?s2 -> Op_s1?s1 -> Op_s2?s2 -> out!s1!s2 -> SKIP 
   *    [] Op_s1?s1 -> Op_s2?s2 -> Op_s1?s1 -> Op_s2?s2 -> out!s1!s2 -> SKIP
   * It is not desired.
   */
  private final Set<Term> visited_terms_ = new HashSet<Term>();
  
  /**
   * A set of P_OP_x channel events that are visited before for state retrieving in CSP
   * Use this set to add only used channel events in CSP and not all state retrieving channels are declared in CSP
   * 
   * such {(P_OP_x, Tx, true)} where boolean is used to mark if it has been added to CSP.
   */
  private final Map<String, Pair<Expr, Boolean>> visited_state_op_ = new HashMap<String, Pair<Expr, Boolean>>();
  
  /**
   * A set of initial pred and one for each basic process
   */
  private final List<Pred> set_init_pred_ = new ArrayList<Pred>();
  
  public CircusRewriteVisitor()
  {
    map_ = new CircusSpecMap();
    paralist_ = cfac_.createZParaList();
    new_paralist_ = cfac_.createZParaList();
    circus_process_stack_ = new Stack<CircusProcess>();
    circus_action_stack_ = new Stack<CircusAction>();
    circus_muaction_stack_ = new Stack<ZName>();
    loc_vars_stack_ = new Stack<Pair<String, Term>>();
    // use the default config.properties
    config_ = new Config(null);
    cspspec_ = new CSPSpec();
    stack_parent_ = new Stack<Term>();
  }

  public CircusRewriteVisitor(CircusSpecMap map, SectionManager manager, CSPSpec cspspec)
  {
    map_ = map;
    manager_ = manager;
    paralist_ = cfac_.createZParaList();
    new_paralist_ = cfac_.createZParaList();
    circus_process_stack_ = new Stack<CircusProcess>();
    circus_action_stack_ = new Stack<CircusAction>();
    circus_muaction_stack_ = new Stack<ZName>();
    loc_vars_stack_ = new Stack<Pair<String, Term>>();
    cspspec_ = cspspec;
    stack_parent_ = new Stack<Term>();
    
    // use the default config.properties
    String path = manager.getProperty("czt.path");
    config_ = new Config(path + "/" + Config.file_name_);
    UpdateDefTable();
  }

  /**
   * Update definition table
   */
  private void UpdateDefTable()
  {
    assert (manager_ != null);

    Spec spec;
    try {
      spec = manager_.get(new Key<Spec>("spec", Spec.class));
      for (Sect sect : spec.getSect()) {
        // If the section is a ZSection
        if (sect instanceof ZSect) {
          sectname_ = ((ZSect) sect).getName();

          deftable_ = manager_.get(new Key<DefinitionTable>(sectname_, DefinitionTable.class));
        }
      }
    }
    catch (SectionInfoException e) {
      CztException ex = new CztException("Unable to get definition table for the section ", e);
      throw ex;
    }
    catch (CommandException e) {
      CztException ex = new CztException("Unable to get definition table for the section ", e);
      throw ex;
    }
  }

  public void setManager(SectionManager manager)
  {
    manager_ = manager;
    UpdateDefTable();
  }
  
  public SectionManager getManager()
  {
    return manager_;
  }

  public void setCircusSpecMap(CircusSpecMap map)
  {
    map_ = map;
  }
  
  public CircusSpecMap getCircusSpecMap()
  {
    return map_;
  }

  public void setRewriteStage(int rewrite_stage)
  {
    rewrite_stage_ = rewrite_stage;
  }
  
  public void setSectName(String sectname)
  {
    sectname_ = sectname;
  }
  
  public List<Pred> getInitPredSet()
  {
    return set_init_pred_;
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

  @Override
  public Object visitParallelProcess(ParallelProcess term)
  {
    circus_process_stack_.push(term);
    visit(term.getLeftProcess());
    visit(term.getRightProcess());
    circus_process_stack_.pop();
    return null;
  }

  @Override
  public Object visitAlphabetisedParallelProcess(AlphabetisedParallelProcess term)
  {
    // Not support
    return null;
  }

  /**
   * add (v,v': Tv) to declaration list, and (v'=v) to pred 
   * @param vName - variable name
   * @param Tv - its type
   * @param apk - the AxParaKind of the original AxPara
   * @param zdl - declarations list
   * @param pred - the predicate of the original AxPara
   * @param needV - need to add v in declaration or not
   */
  private Pred createDeclListAndPred(String vName, Term Tv,
      AxParaKind apk, ZDeclList zdl, Pred pred, boolean needV)
  {
    Pred retPred = pred;
    
    String newv = vName;
    List<Stroke> ls = new ArrayList<Stroke>();
    Stroke next = fac_.createNextStroke();
    ls.add(next);
    ZStrokeList zsl = fac_.createZStrokeList(ls);
    // LHS (s')
    RefExpr lre = fac_.createRefExpr(fac_.createZName(newv, zsl, null), 
        fac_.createZExprList(), false, false);
    // RHS (s)
    RefExpr rre = fac_.createRefExpr(fac_.createZName(newv, fac_.createZStrokeList(), null),
        fac_.createZExprList(), false, false);
    
    // 1. VarDecl
    List<ZName> lstName = new ArrayList<ZName>();
    lstName.add(fac_.createZName(newv, zsl, null));
    if(needV) {
      lstName.add(fac_.createZName(newv, fac_.createZStrokeList(), null));
    }
    
    ZNameList znl = fac_.createZNameList(lstName);
    
    if(Tv instanceof Expr) {
      VarDecl vd = fac_.createVarDecl(znl, (Expr)Tv);
      zdl.add(vd);
    }
    else {
      throw new CztException("For a state variable, its term should be Expr but it is " + 
          Tv.getClass().getName());
    }
    
    // 2. Predicate
    List<Expr> le = new ArrayList<Expr>();
    le.add(rre);
    ZExprList zel = fac_.createZExprList(le);
    SetExpr se = fac_.createSetExpr(zel);

    // ExprList for MemPred
    List<Expr> le2 = new ArrayList<Expr>();
    le2.add(lre);
    le2.add(se);
    // for equality, mixfix is true
    MemPred mp = fac_.createMemPred(le2, true);

    if(retPred == null) {
      retPred = mp;
    } 
    else {
      List<Pred> lp = new ArrayList<Pred>();
      lp.add(retPred);
      lp.add(mp);
      if(apk == AxParaKind.BOXED_SCHEMA) {
        AndPred ap = fac_.createAndPred(lp, And.NL);
        retPred = ap;
      }
      else {
        AndPred ap = fac_.createAndPred(lp, And.Wedge);
        retPred = ap;
      }
    }
    
    return retPred;
  }
  
  @Override
  public Object visitSchExprAction(SchExprAction term)
  {
    if(!(term.getExpr() instanceof RefExpr)) {
      Expr expr = term.getExpr();
      if( expr instanceof SchExpr2 || 
          expr instanceof NegExpr || 
          expr instanceof ThetaExpr || 
          expr instanceof RenameExpr ||
          expr instanceof PreExpr
        ) {
        // in this case, we have to add additional schema abbr in Z and then this Schema Expression refers to it
        String strParaName = 
            MessageFormat.format(FormatPattern.TEMP_SCHEMA_NAMING_SCHEXPR, map_.getAndIncVarNum());
        ZName paraname = fac_.createZName(
            strParaName, fac_.createZStrokeList(), null);
        ConstDecl cd = fac_.createConstDecl(paraname, expr);

        ZDeclList declList0 = fac_.createZDeclList();
        declList0.add(cd);
        
        SchText schtext = fac_.createZSchText(declList0, null);

        ZNameList fp = fac_.createZNameList();
        AxPara axpara = fac_.createAxPara(fp, schtext, Box.OmitBox);
        
        assert(process_para_.getCircusProcess() instanceof BasicProcess);
        
        ZParaList zpl = process_para_.getCircusBasicProcess().getZParaList();
        zpl.add(axpara);
        process_para_.getCircusBasicProcess().setParaList(zpl);
        
        term.setExpr(fac_.createRefExpr(paraname, fac_.createZExprList(), false, false));
        
        visit(term);
        return null;
      }
      else {
        throw new CztException("Only RefExpr and schema expressions/operations is allowed fro SchExprAction, but this is " 
          + term.getExpr().getClass().getName());
      }
    }

    /*if(rewrite_stage_ == 1) */ {
      visit(term.getExpr());
    }
    
    if(rewrite_stage_ == 4) {
      // itself
//      String schName = Circus2ZCSPUtils.termToString(term.getExpr());
      ZName schName = null;
      if(term.getExpr() instanceof RefExpr) {
        schName = ((RefExpr)term.getExpr()).getZName();
      }
      else {
        throw new CztException("A SchExprAction should be a RefExpr but it is " + 
            term.getExpr().getClass().toString());
      }
      
      assert(process_para_.getCircusProcess() instanceof BasicProcess);
      
      AxPara schPara = null;
      int index = 0;
      for(Para para: process_para_.getCircusBasicProcess().getZParaList()) {
        index++;
        if(para instanceof AxPara && 
            Circus2ZCSPUtils.isEquals((ZName) ZUtils.getAxParaSchOrAbbrName((Term)para), schName)) {
          schPara = (AxPara) para;
          break;
        }
      }
      
      if(schPara != null) {
        String strAssignPattern = MessageFormat.format(
            CSPPredExpPattern.getPattern(PredExpPattern.ASSIGN_NAME_PATT), para_name_, "");
        String strSpecPattern = MessageFormat.format(
            CSPPredExpPattern.getPattern(PredExpPattern.SPEC_NAME_PATT), para_name_, "");
        String strAssumpPattern = MessageFormat.format(
            CSPPredExpPattern.getPattern(PredExpPattern.ASSUMP_NAME_PATT), para_name_, "");
        String strCoercionPattern = MessageFormat.format(
            CSPPredExpPattern.getPattern(PredExpPattern.COERC_NAME_PATT), para_name_, "");

        // for new added assignment schema, we don't need to add additional NegPreconditionSchema
        if(!Circus2ZCSPUtils.termToString(schName).startsWith(strAssignPattern) && 
           !Circus2ZCSPUtils.termToString(schName).startsWith(strSpecPattern) &&
           !Circus2ZCSPUtils.termToString(schName).startsWith(strAssumpPattern) &&
           !Circus2ZCSPUtils.termToString(schName).startsWith(strCoercionPattern)
           ) {
          // but add another negative precondition schema in the process
          // check if there has been a AxPara named this one
          AxPara apNeg = Circus2ZCSPUtils.NegPreconditionSchema(para_name_, schPara, map_, 
              process_para_.getCircusBasicProcess(), zsect_, manager_, sectname_);
          if(apNeg != null) {
            process_para_.getCircusBasicProcess().getZParaList().add(apNeg);
          }
          
          // add additional u'=u (where u - variables not in the frame)
          // 1. if only v' included and v not, then add v in the declaration part
          // 2. if only v included but v' not, then add v' in the declaration part and v'=v in predicate
          // 3. if both not included, then add v and v' in the declaration part and v'=v in predicate
          
          // find out all variables declared in this schema
          DeclListExpansionVisitor dlevisitor = new DeclListExpansionVisitor(
              (BasicProcess)process_para_.getCircusProcess(), zsect_, manager_, sectname_);
          // after renaming, normalisation might not work properly, so disable it
          dlevisitor.disableNormalisation();
          schPara.accept(dlevisitor);
          Set<Pair<ZName, Expr>> lstZNameExpr = dlevisitor.getNameExprPair();
          
          List<Pair<String, Term>> lstState = map_.getStatListWithExp(para_name_);

          // a map from v to (its type, is v in the decl, is v' in the decl)
          // this is for no. 1 and no. 2 above
          Map<String, Triple<Expr, Boolean, Boolean>> setStateNoV = 
              new HashMap<String, Triple<Expr, Boolean, Boolean>>();
          
          for(Pair<ZName, Expr> p: lstZNameExpr) {
            int size = p.getFirst().getZStrokeList().size();
            String declVName = "";
            
            if(size > 0) {
              Stroke s = p.getFirst().getZStrokeList().get(size - 1);
              // for input and output variables, just ignore it
              if (s instanceof InStroke || s instanceof OutStroke) {
                continue;
              }
              // for v', if it is a state variable, just get its name
              else if(s instanceof NextStroke) {
                declVName = p.getFirst().getWord();
                // if v', we think v might be not included
                Triple<Expr, Boolean, Boolean> triple = setStateNoV.get(declVName);
                if(triple == null) {
                  setStateNoV.put(declVName, new Triple<Expr, Boolean, Boolean>(null, Boolean.FALSE, Boolean.TRUE));
                }
                else {
                  setStateNoV.put(declVName, new Triple<Expr, Boolean, Boolean>(triple.getFirst(), triple.getSecond(), Boolean.TRUE));
                }
              }
              else {
                continue;
              }
            }
            else {
              // v
              declVName = p.getFirst().getWord();
              Triple<Expr, Boolean, Boolean> triple = setStateNoV.get(declVName); 
              if( triple == null) {
                setStateNoV.put(declVName, 
                    new Triple<Expr, Boolean, Boolean>(null, Boolean.TRUE, Boolean.FALSE));
              }
              else {
                setStateNoV.put(declVName, 
                    new Triple<Expr, Boolean, Boolean>(triple.getFirst(), Boolean.TRUE, triple.getThird()));
              }
            }
          
            List<Pair<String, Term>> lstState2Remove = new ArrayList<Pair<String, Term>>();
            for (Pair<String, Term> ps: lstState) {
              String vnameWithProc = MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_, ps.getFirst());
              if (vnameWithProc.equals(declVName)) {
//                lstState.remove(ps);
                lstState2Remove.add(ps);
                Triple<Expr, Boolean, Boolean> triple = setStateNoV.get(declVName);
                setStateNoV.put(declVName, 
                    new Triple<Expr, Boolean, Boolean>((Expr)ps.getSecond(), triple.getSecond(), triple.getThird()));
              }
            }
            lstState.removeAll(lstState2Remove);
          }
          
          // a set of variables whose dashed counterparts are not in the declartion list of this schema
          Set<String> setNoInclDashedV = new HashSet<String>();
          
          // add all v which has v' in the paragraph but no v
          for (Entry<String, Triple<Expr, Boolean, Boolean>> entry : setStateNoV.entrySet()) {
              if(entry.getValue().getThird().equals(Boolean.FALSE)) {
              // no v'
              setNoInclDashedV.add(entry.getKey());
            }
          }

          // Check if all v' are included in this schema expression, 
          // an operational schema requires at least all v' in its declaration list
          if(!setNoInclDashedV.isEmpty()) {
            throw new CztException("The schema [" + Circus2ZCSPUtils.termToString(schName) + 
                "] as an operation shall include all dashed variables in its declaration list, \n\tbut these " +
                "varaibles " + setNoInclDashedV.toString() + " do not have dashed counterparts!");
          }

          // 
          AxParaKind apk = Circus2ZCSPUtils.getAxParaKind(schPara);
          if(apk == AxParaKind.HORIZON_SCHEMA || apk == AxParaKind.BOXED_SCHEMA) {
            Expr e = ZUtils.getSchemaDefExpr(schPara);
            if(e instanceof SchExpr) {
              SchExpr schExpr = (SchExpr)e;
              ZDeclList zdl = schExpr.getZSchText().getZDeclList();
              Pred pred = schExpr.getZSchText().getPred();
              
              // add all v which has v' in the paragraph but no v
              for (Entry<String, Triple<Expr, Boolean, Boolean>> entry : setStateNoV.entrySet()) {
                if(entry.getValue().getSecond().equals(Boolean.FALSE)) {
                  // no v, just add v to declaration list
                  List<ZName> lstName = new ArrayList<ZName>();
                  lstName.add(fac_.createZName(entry.getKey(), fac_.createZStrokeList(), null));
                  
                  ZNameList znl = fac_.createZNameList(lstName);
                  VarDecl vd = fac_.createVarDecl(znl, entry.getValue().getFirst());
                  zdl.add(vd);
                }
                else if(entry.getValue().getThird().equals(Boolean.FALSE)) {
                  // no v', add v' to declaration list, and v'=v to predicate
                  pred = createDeclListAndPred(entry.getKey(), entry.getValue().getFirst(),
                      apk, zdl, pred, false);
                }
              }
              
              //
              for (Pair<String, Term> p : lstState) {
                String vname = MessageFormat.format(FormatPattern.RENAMING_IN_PROC, 
                    para_name_, p.getFirst());
                pred = createDeclListAndPred(vname, p.getSecond(),
                    apk, zdl, pred, true);
//                String newv = MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_, p.getFirst());
//                List<Stroke> ls = new ArrayList<Stroke>();
//                Stroke next = fac_.createNextStroke();
//                ls.add(next);
//                ZStrokeList zsl = fac_.createZStrokeList(ls);
//                // LHS (s')
//                RefExpr lre = fac_.createRefExpr(fac_.createZName(newv, zsl, null), fac_.createZExprList(),
//                    false, false);
//                // RHS (s)
//                RefExpr rre = fac_.createRefExpr(fac_.createZName(newv, fac_.createZStrokeList(), null),
//                    fac_.createZExprList(), false, false);
//                
//                // 1. VarDecl
//                List<ZName> lstName = new ArrayList<ZName>();
//                lstName.add(fac_.createZName(newv, zsl, null));
//                lstName.add(fac_.createZName(newv, fac_.createZStrokeList(), null));
//                
//                ZNameList znl = fac_.createZNameList(lstName);
//                
//                if(p.getSecond() instanceof Expr) {
//                  VarDecl vd = fac_.createVarDecl(znl, (Expr)p.getSecond());
//                  zdl.add(vd);
//                }
//                else {
//                  throw new CztException("For a state variable, its term should be Expr but it is " + 
//                      p.getSecond().getClass().getName());
//                }
//                
//                // 2. Predicate
//                List<Expr> le = new ArrayList<Expr>();
//                le.add(rre);
//                ZExprList zel = fac_.createZExprList(le);
//                SetExpr se = fac_.createSetExpr(zel);
//          
//                // ExprList for MemPred
//                List<Expr> le2 = new ArrayList<Expr>();
//                le2.add(lre);
//                le2.add(se);
//                // for equality, mixfix is true
//                MemPred mp = fac_.createMemPred(le2, true);
//          
//                List<Pred> lp = new ArrayList<Pred>();
//                lp.add(pred);
//                lp.add(mp);
//                if(apk == AxParaKind.BOXED_SCHEMA) {
//                  AndPred ap = fac_.createAndPred(lp, And.NL);
//                  pred = ap;
//                }
//                else {
//                  AndPred ap = fac_.createAndPred(lp, And.Wedge);
//                  pred = ap;
//                }
              }
              
              schExpr.getZSchText().setPred(pred);
            }
            else {
              throw new CztException("For a schema, its expression should be SchExpr but it is " + e.getClass().getName());
            }
          }
          else if(apk == AxParaKind.ABBR) {
            Expr e = ZUtils.getAbbreviationExpr(schPara);
            /*if(e instanceof SchExpr2)*/ {
              ZDeclList zdl = fac_.createZDeclList();
              Pred pred = null;
              
              // add all v which has v' in the paragraph but no v
              for (Entry<String, Triple<Expr, Boolean, Boolean>> entry : setStateNoV.entrySet()) {
                if(entry.getValue().getSecond().equals(Boolean.FALSE)) {
                  // no v, just add v to declaration list
                  List<ZName> lstName = new ArrayList<ZName>();
                  lstName.add(fac_.createZName(entry.getKey(), fac_.createZStrokeList(), null));
                  
                  ZNameList znl = fac_.createZNameList(lstName);
                  VarDecl vd = fac_.createVarDecl(znl, entry.getValue().getFirst());
                  zdl.add(vd);
                }
                else if(entry.getValue().getThird().equals(Boolean.FALSE)) {
                  // no v', add v' to declaration list, and v'=v to predicate
                  pred = createDeclListAndPred(entry.getKey(), entry.getValue().getFirst(),
                      apk, zdl, pred, true);
                }
              }
              
              for (Pair<String, Term> p : lstState) {
                String newv = MessageFormat.format(FormatPattern.RENAMING_IN_PROC, 
                    para_name_, p.getFirst());
                pred = createDeclListAndPred(newv, p.getSecond(),
                    apk, zdl, pred, true);
//                List<Stroke> ls = new ArrayList<Stroke>();
//                Stroke next = fac_.createNextStroke();
//                ls.add(next);
//                ZStrokeList zsl = fac_.createZStrokeList(ls);
//                // LHS (s')
//                RefExpr lre = fac_.createRefExpr(
//                    fac_.createZName(newv, zsl, null), fac_.createZExprList(),
//                    false, false);
//                // RHS (s)
//                RefExpr rre = fac_.createRefExpr(
//                    fac_.createZName(newv, fac_.createZStrokeList(), null),
//                    fac_.createZExprList(), false, false);
//                
//                // 1. VarDecl
//                List<ZName> lstName = new ArrayList<ZName>();
//                lstName.add(fac_.createZName(newv, zsl, null));
//                lstName.add(fac_.createZName(newv, fac_.createZStrokeList(), null));
//                
//                ZNameList znl = fac_.createZNameList(lstName);
//                
//                if(p.getSecond() instanceof Expr) {
//                  VarDecl vd = fac_.createVarDecl(znl, (Expr)p.getSecond());
//                  zdl.add(vd);
//                }
//                else {
//                  throw new CztException("For a state variable, its term should be Expr but it is " + 
//                      p.getSecond().getClass().getName());
//                }
//                
//                // 2. Predicate
//                List<Expr> le = new ArrayList<Expr>();
//                le.add(rre);
//                ZExprList zel = fac_.createZExprList(le);
//                SetExpr se = fac_.createSetExpr(zel);
//          
//                // ExprList for MemPred
//                List<Expr> le2 = new ArrayList<Expr>();
//                le2.add(lre);
//                le2.add(se);
//                // for equality, mixfix is true
//                MemPred mp = fac_.createMemPred(le2, true);
//          
//                if(pred == null) {
//                  pred = mp;
//                } 
//                else {
//                  List<Pred> lp = new ArrayList<Pred>();
//                  lp.add(pred);
//                  lp.add(mp);
//                  AndPred ap = fac_.createAndPred(lp, And.Wedge);
//                  pred = ap;
//                }
              }
              
              if(!zdl.isEmpty()) {
                ZSchText schText = fac_.createZSchText(zdl, pred);
                SchExpr schExpr = fac_.createSchExpr(schText);
  
                String strParaName = 
                    MessageFormat.format(FormatPattern.TEMP_SCHEMA_NAMING_SCHEXPR, map_.getAndIncVarNum());
                
                ZName paraname = fac_.createZName(strParaName, fac_.createZStrokeList(), null);
                ConstDecl cd = fac_.createConstDecl(paraname, schExpr);
  
                ZDeclList declList0 = fac_.createZDeclList();
                declList0.add(cd);
                SchText st = fac_.createZSchText(declList0, null);
                AxPara ap = fac_.createAxPara(fac_.createZNameList(), st, Box.OmitBox);
                
                if(index > 0) {
                  process_para_.getCircusBasicProcess().getZParaList().add(index-1, ap);
                }
                else {
                  process_para_.getCircusBasicProcess().getZParaList().add(index, ap);
                }
                
                List<Expr> lstExpr = new ArrayList<Expr>();
                lstExpr.add(e);
                lstExpr.add(fac_.createRefExpr(paraname, fac_.createZExprList(), false, false));
                ((ConstDecl)schPara.getZSchText().getZDeclList().get(0)).setExpr(fac_.createAndExpr(lstExpr));
              }
            }
//            else {
//              throw new CztException("For a schema, its expression should be SchExpr but it is " + e.getClass().getName());
//            }
          }
          else {
            
          }
        }
      }
      else {
        throw new CztException("SchExprAction [" + Circus2ZCSPUtils.termToString(schName) + 
            "] can not be found!");
      }
    }
    return null;
  }

  @Override
  public Object visitQualifiedDecl(QualifiedDecl term)
  {
    /*if(rewrite_stage_ == 1) */ {
      visit(term.getZNameList());
      visit(term.getExpr());
    }
    return null;
  }

  @Override
  public Object visitCommunication(Communication term)
  {
    /*if(rewrite_stage_ == 1) */ {
      visit(term.getCircusFieldList());
      visit(term.getChannelExpr());
    }
    return null;
  }

  @Override
  public Object visitSubstitutionAction(SubstitutionAction term)
  {
    if(rewrite_stage_ == 4) {
      circus_action_stack_.push(term);
      visit(term.getCircusAction());
      circus_action_stack_.pop();
      
      CircusAction ca = term.getCircusAction();
      List<Pair<String, String>> lstPSubstPair = new ArrayList<Pair<String, String>>();
      for(NewOldPair zr: term.getZRenameList()) {
        lstPSubstPair.add(new Pair<String, String>(
            Circus2ZCSPUtils.termToString(zr.getOldName()),
            Circus2ZCSPUtils.termToString(zr.getNewName())));
      }
      ca.accept(new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_ACTION_RENAME, lstPSubstPair));
    }
    return null;
  }

  @Override
  public Object visitInterleaveActionIte(InterleaveActionIte term)
  {
    if(rewrite_stage_ == 4) {
      int nrOfVarDecl = 0;
      for(Decl decl: term.getZDeclList()) {
        if(decl instanceof VarDecl) {
          for(Name name: ((VarDecl)decl).getZNameList()) {
            loc_vars_stack_.push(
                new Pair<String, Term>(
                Circus2ZCSPUtils.termToString(name), ((VarDecl)decl).getExpr()
                ));
            nrOfVarDecl++;
          }
        }
      }

      circus_action_stack_.push(term);
      visit(term.getCircusAction());
      circus_action_stack_.pop();
      
      mergeAndUpdateRpreOfTerm(term);
      
      // update context by removing
      while(nrOfVarDecl > 0) {
        loc_vars_stack_.pop();
        nrOfVarDecl--;
      }
    }
    return null;
  }

  @Override
  public Object visitInterleaveProcessIte(InterleaveProcessIte term)
  {
    circus_process_stack_.push(term);
    visit(term.getCircusProcess());
    circus_process_stack_.pop();
    return null;
  }

  /**
   * rewrite parametrised or indexed process invocation to ((e1 = x1 \land e2 = y1) & P_1_1) [] ((e1 = x1 \land e2 = y2) & P_1_2)
   *    Since (e1 = x1) & P_1 is not a correct syntax for process in circus, here we use an additional assumption of RefExpr.
   *    Normally, P_1 should be CallProcess with its CallExpr is RefExpr. For this RefExpr,
   *            word: P_1; explicit: false; mixfix: false; explist: []
   *    In order to accommodate (e1 = x1), we treat it as an expr list [e1, x1]. So RefExpr becames
   *            word: P_1; explicit: false; mixfix: false; explist: [e1,x1] (might be [e1,x1,e2,y1,...] if there are multiple parameters)
   * When we link it later, we need to recover it to (e1 = x1) & P_1
   * 
   * @param pname - parametrised or indexed process name
   * @param term - original invocation
   * @return
   */
  private Object assembleParaAndIndexProcessInvocation(String pname, CallProcess term)
  {
    ZDeclList zdl = null;
    ZExprList zel = term.getZActuals();
    
    for(Para p: paralist_) {
      if(p instanceof ProcessPara) {
        if(Circus2ZCSPUtils.termToString(((ProcessPara)p).getZName()).equals(pname)) {
          if(((ProcessPara)p).getCircusProcess() instanceof ParamProcess) {
            // rewrite to ((x = x1) & P_1) [] ((x = x2) & P_2) ...
            ParamProcess pp = (ParamProcess)(((ProcessPara)p).getCircusProcess());
            zdl = pp.getZDeclList();
          }
          else if(((ProcessPara)p).getCircusProcess() instanceof IndexedProcess) {
            // rewrite to ((x = x1) & P_1) [] ((x = x2) & P_2) ...
            IndexedProcess ip = (IndexedProcess)(((ProcessPara)p).getCircusProcess());
            zdl = ip.getZDeclList();
          }
          else if (((ProcessPara)p).getCircusProcess() instanceof RenameProcess) {
            RenameProcess rp = (RenameProcess) ((ProcessPara)p).getCircusProcess();
            if(rp.getCircusProcess() instanceof IndexedProcess) {
              zdl = ((IndexedProcess)rp.getCircusProcess()).getZDeclList();
            }
          }
          
          if(zdl == null) {
            throw new CztException("Invalid Class [" + ((ProcessPara)p).getCircusProcess().getClass().getName() + 
                "] for parametrised or indexed process invocation. Expected ParamProcess, IndexedProcess or RenameProcess of an IndexedProcess!");
          }
          break;
        }
      }
    }
    
    List<CircusProcess> lst_proc = new ArrayList<CircusProcess>();
    if(zdl != null) {
      List<Pair<String, TreeSet<Pair<String, Expr>>>> ts = 
          new ArrayList<Pair<String, TreeSet<Pair<String, Expr>>>>();
      Set<List<Pair<String, Expr>>> sls = new HashSet<List<Pair<String, Expr>>>();
      
      expandDeclList2Set(zdl, ts, sls);
      
      for(List<Pair<String, Expr>> lstr: sls) {
        // new basic process name
        String new_pname = pname;
        Iterator<Pair<String, TreeSet<Pair<String, Expr>>>> ite = ts.iterator();

        int i = 0;
        // (e1 = x1) && (e2 = y1)
       
        // keep a list of expr for [e1,x1,e2,y1]
        List<Expr> lst_expr_special = new ArrayList<Expr>();
//        List<MemPred> lst_mp = new ArrayList<MemPred>();
        while(ite.hasNext()) {
          Pair<String, TreeSet<Pair<String, Expr>>> p = ite.next();
          new_pname = MessageFormat.format(FormatPattern.PARAM_PROCESS_RENAMING_PATT, new_pname, lstr.get(i).getFirst());
          // e1 = x1
          /*
          List<Expr> lst_expr = new ArrayList<Expr>();          
          lst_expr.add(zel.get(i));
          List<Expr> lst_temp_expr = new ArrayList<Expr>();
          lst_temp_expr.add(lstr.get(i).getSecond());
          lst_expr.add(fac_.createSetExpr(fac_.createZExprList(lst_temp_expr)));
          MemPred mp = fac_.createMemPred(lst_expr, true);
          assert(Circus2ZCSPUtils.getMemPredKind(mp) == MemPredKind.EQUALITY);
          lst_mp.add(mp);
          */
          
          // 
          lst_expr_special.add(zel.get(i));
          lst_expr_special.add(lstr.get(i).getSecond());
          i++;
        }
        // P\_1\_2...
        // Basically for RefExpr, both mixfix and explicit should be false, and expr list is empty for a CallProcess.
        /* RefExpr re = cfac_.createRefExpr(fac_.createZName(new_pname, fac_.createZStrokeList(), null), 
            fac_.createZExprList(), false, false);*/
        RefExpr re = cfac_.createRefExpr(fac_.createZName(new_pname, fac_.createZStrokeList(), null), 
            fac_.createZExprList(lst_expr_special), false, false);
        CallProcess cp = cfac_.createCallProcess(re, cfac_.createZExprList(), CallUsage.Parameterised);
        if(term.hasAnn()) {
          cp.getAnns().addAll(term.getAnns());
        }
        /*Pred pred = null;
        if(lst_mp.size() == 1) {
          pred = lst_mp.get(0);
        }
        else if(lst_mp.size() > 1) {
          pred = cfac_.createAndPred(lst_mp, And.Wedge);
        }
        else {
          // error and no predicate
        }*/
               
        // 
        lst_proc.add(cp);
      }
    }
    
    CircusProcess cp = null;
    
    if(!lst_proc.isEmpty()) {
      if (lst_proc.size() == 1) {
        cp = lst_proc.get(0);
      }
      else {
        List<CircusProcess> lstTemp = new ArrayList<CircusProcess>();
        cp = lst_proc.get(0);
        for(int i = 1; i < lst_proc.size(); i++) {
          lstTemp.clear();
          lstTemp.add(lst_proc.get(i));
          lstTemp.add(cp);
          cp = cfac_.createExtChoiceProcess(lstTemp);
        }
      }
      
      if(term.hasAnn()) {
        cp.getAnns().addAll(term.getAnns());
      }
    }
    return cp;
  }
  /**
   * CallProcess might be
   *    1) N, a reference to an explicitly defined process
   *    2) N(x), a reference to a parametrised process
   *    3) N[x], a reference to an indexed process
   *    4) N, others
   */
  @Override
  public Object visitCallProcess(CallProcess term)
  {
    Object ob = null;
    
    visit(term.getCallExpr());
    
    // 1. N
    if(term.getZActuals().isEmpty()) {
      // nothing changed
      return null;
    } 
    else {
      // 2. N(x)
      if(term.getCallUsage().equals(CallUsage.Parameterised)) {
        
        if(term.getCallExpr() instanceof RefExpr) {
          RefExpr re = term.getCallExpr();
          String ppname = Circus2ZCSPUtils.termToString(re);
          ob = assembleParaAndIndexProcessInvocation(ppname, term);
        }
        else {
          throw new CztException("Invalid Expr [" + term.getCallExpr().getClass().getName() + 
              "] for parametrised process invocation. Expected RefExpr!");
        }
      }
      // 3. N[x]
      else if (term.getCallUsage().equals(CallUsage.Indexed)) {
        if(term.getCallExpr() instanceof RefExpr) {
          RefExpr re = term.getCallExpr();
          String ppname = Circus2ZCSPUtils.termToString(re);
          ob = assembleParaAndIndexProcessInvocation(ppname, term);
        }
        else {
          throw new CztException("Invalid Expr [" + term.getCallExpr().getClass().getName() + 
              "] for indexed process invocation. Expected RefExpr!");
        }
      } 
      else {
        throw new CztException("Not a valid CallUsage [" + term.getCallUsage().toString() + "]!");
      }
    }
    
    // Replace CallProcess with an external choice of processes
    if(ob != null && ob instanceof CircusProcess) {
      if(circus_process_stack_.isEmpty()) {
        // its parent is not a CircusProcess and so it should be ProcessPara
        process_para_.setCircusProcess((CircusProcess)ob);
      } 
      else {
        // its parent is a CircusProcess
        CircusProcess cp = circus_process_stack_.peek();
      
        if(cp != null) {
          // Sequential
          if(cp instanceof SeqProcess) {
            if(((SeqProcess)cp).getLeftProcess().equals(term)) {
              ((SeqProcess)cp).setLeftProcess((CircusProcess)ob);
            } 
            else if(((SeqProcess)cp).getRightProcess().equals(term)) {
              ((SeqProcess)cp).setRightProcess((CircusProcess)ob);
            }
            else {
              throw new CztException("CallProcess [" + 
                  net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                  "] can not be found from its parent!");
            }
          }
          // ExtChoiceProcess
          else if(cp instanceof ExtChoiceProcess) {
            if(((ExtChoiceProcess)cp).getLeftProcess().equals(term)) {
              ((ExtChoiceProcess)cp).setLeftProcess((CircusProcess)ob);
            } 
            else if(((ExtChoiceProcess)cp).getRightProcess().equals(term)) {
              ((ExtChoiceProcess)cp).setRightProcess((CircusProcess)ob);
            }
            else {
              throw new CztException("CallProcess [" + 
                  net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                  "] can not be found from its parent!");
            }
          }
          // IntChoiceProcess
          else if(cp instanceof IntChoiceProcess) {
            if(((IntChoiceProcess)cp).getLeftProcess().equals(term)) {
              ((IntChoiceProcess)cp).setLeftProcess((CircusProcess)ob);
            } 
            else if(((IntChoiceProcess)cp).getRightProcess().equals(term)) {
              ((IntChoiceProcess)cp).setRightProcess((CircusProcess)ob);
            }
            else {
              throw new CztException("CallProcess [" + 
                  net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                  "] can not be found from its parent!");
            }
          }
          // ParallelProcess
          else if(cp instanceof ParallelProcess) {
            if(((ParallelProcess)cp).getLeftProcess().equals(term)) {
              ((ParallelProcess)cp).setLeftProcess((CircusProcess)ob);
            } 
            else if(((ParallelProcess)cp).getRightProcess().equals(term)) {
              ((ParallelProcess)cp).setRightProcess((CircusProcess)ob);
            }
            else {
              throw new CztException("CallProcess [" + 
                  net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                  "] can not be found from its parent!");
            }
          }
          // InterleaveProcess
          else if(cp instanceof InterleaveProcess) {
            if(((InterleaveProcess)cp).getLeftProcess().equals(term)) {
              ((InterleaveProcess)cp).setLeftProcess((CircusProcess)ob);
            } 
            else if(((InterleaveProcess)cp).getRightProcess().equals(term)) {
              ((InterleaveProcess)cp).setRightProcess((CircusProcess)ob);
            }
            else {
              throw new CztException("CallProcess [" + 
                  net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                  "] can not be found from its parent!");
            }
          }
          // HideProcess
          else if(cp instanceof HideProcess) {
            if(((HideProcess)cp).getCircusProcess().equals(term)) {
              ((HideProcess)cp).setCircusProcess((CircusProcess)ob);
            } 
            else {
              throw new CztException("CallProcess [" + 
                  net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                  "] can not be found from its parent!");
            }
          }
          // SeqProcessIte
          else if(cp instanceof SeqProcessIte) {
            if(((SeqProcessIte)cp).getCircusProcess().equals(term)) {
              ((SeqProcessIte)cp).setCircusProcess((CircusProcess)ob);
            }
            else {
              throw new CztException("CallProcess [" + 
                  net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                  "] can not be found from its parent!");
            }
          }
          // ExtChoiceProcessIte
          else if(cp instanceof SeqProcessIte) {
            if(((ExtChoiceProcessIte)cp).getCircusProcess().equals(term)) {
              ((ExtChoiceProcessIte)cp).setCircusProcess((CircusProcess)ob);
            }
            else {
              throw new CztException("CallProcess [" + 
                  net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                  "] can not be found from its parent!");
            }
          }
          // IntChoiceProcessIte
          else if(cp instanceof SeqProcessIte) {
            if(((IntChoiceProcessIte)cp).getCircusProcess().equals(term)) {
              ((IntChoiceProcessIte)cp).setCircusProcess((CircusProcess)ob);
            }
            else {
              throw new CztException("CallProcess [" + 
                  net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                  "] can not be found from its parent!");
            }
          }
          // ParallelProcessIte
          else if(cp instanceof ParallelProcessIte) {
            if(((ParallelProcessIte)cp).getCircusProcess().equals(term)) {
              ((ParallelProcessIte)cp).setCircusProcess((CircusProcess)ob);
            }
            else {
              throw new CztException("CallProcess [" + 
                  net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                  "] can not be found from its parent!");
            }
          }
          // InterleaveProcessIte
          else if(cp instanceof InterleaveProcessIte) {
            if(((InterleaveProcessIte)cp).getCircusProcess().equals(term)) {
              ((InterleaveProcessIte)cp).setCircusProcess((CircusProcess)ob);
            }
            else {
              throw new CztException("CallProcess [" + 
                  net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                  "] can not be found from its parent!");
            }
          }
        }
        else {
          throw new CztException("CallProcess [" + 
                net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                "]'s Parent should not be null!");
        }
      }
      return (CircusProcess)ob;
    }
    return null;
  }

  @Override
  public Object visitCircusStateAnn(CircusStateAnn term)
  {

    return null;
  }

  @Override
  public Object visitActionSignature(ActionSignature term)
  {

    return null;
  }

  @Override
  public Object visitTransformerPara(TransformerPara term)
  {

    return null;
  }

  @Override
  public Object visitMuAction(MuAction term)
  {
    if(rewrite_stage_ == 4) {
      circus_muaction_stack_.add(term.getZName());
      circus_action_stack_.push(term);
      visit(term.getCircusAction());
      circus_action_stack_.pop();
      circus_muaction_stack_.pop();
    }
    return null;
  }

  @Override
  public Object visitProcessPara(ProcessPara term)
  {
    // generic process
    if(!term.getZGenFormals().isEmpty()) {
      new_paralist_.remove(term);
      generic_process_para_.add(term);
      return null;
    }
    
    String pname = net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term
        .getZName());
    para_name_ = pname;
    process_para_ = term;
    
    if(term.hasAnn()) {
      list_ann_ = term.getAnns();
    }
    
    if(rewrite_stage_ == 1) {
      // check if it is a parametrised process or a basic process
  
      /**
       * the parametrised process is rewritten to a set of basic processes.
       */
      if (term.getCircusProcess() instanceof ParamProcess) {
        visit(term.getCircusProcess());
        new_paralist_.remove(term);
        return null;
      } 
      else if(term.getCircusProcess() instanceof BasicProcess) {
        // basic process
        visit(term.getCircusBasicProcess());
      } 
      else if(term.getCircusProcess() instanceof IndexedProcess) {
        visit(term.getCircusProcess());
        new_paralist_.remove(term);
      }
      else if(term.getCircusProcess() instanceof RenameProcess) {
        visit(term.getCircusProcess());
        new_paralist_.remove(term);
      }
      else {
        visit(term.getCircusProcess());
      }
    }
    else if(rewrite_stage_ == 2) {
      // stage 2: rewrite a BasicProcess
      if(!(term.getCircusProcess() instanceof BasicProcess)) {
        throw new CztException("Stage 2 of rewrite expects a BasicProcess but it is " +
            term.getCircusProcess().getClass().getName() + "!");
      }
      
      // add process to the map
      map_.addProc(sectname_, para_name_);
      
      visit(term.getCircusBasicProcess());
    }
    else if(rewrite_stage_ == 3) {
      // stage 3: renaming
      visit(term.getCircusBasicProcess());
    }
    else if(rewrite_stage_ == 4) {
      // stage 4: Action Rewrite
      visit(term.getCircusBasicProcess());
    }
    
    process_para_ = null;
    para_name_ = null;
    list_ann_ = null;
    
    return null;
  }

  @Override
  public Object visitIfGuardedCommand(IfGuardedCommand term)
  {
    if(rewrite_stage_ == 4) {
      IfGuardedCommand term2 = ZUtils.cloneTerm(term);
      /**
       * 1. calculate negation of guarded condition and add to a list
       */
  
      // Triple: original true pred, negation of pred (not pred), original CircusAction
      List<Triple<Pred, Pred, CircusAction>> lstPPCGA = new ArrayList<Triple<Pred, Pred, CircusAction>>();
  
      for (CircusAction ga : term2.getGuardedActionList()) {
        if (ga instanceof GuardedAction) {
          NegPred np = fac_.createNegPred(((GuardedAction) ga).getPred());
          lstPPCGA.add(new Triple<Pred, Pred, CircusAction>(((GuardedAction) ga).getPred(), np,
              ((GuardedAction) ga).getCircusAction()));
        }
      }
  
      /**
       * 2. Construct a table for all possible combinations of guarded conditions
       * The size of table is 2^(nr_of_GA)
       * For example, assume G1,G2 - non-state, and G3,G4 - state involved condition
       * | Cond Comb |
       * |-----------|
       * No | G1G2G3G4 | Action
       * --------------------------------------------
       * 15 TTTT | A1|~|A2|~|A3|~|A4
       * 14 TTTF | A1|~|A2|~|A3
       * 13 TTFT | A1|~|A2|~|A4
       * 12 TTFF | A1|~|A2
       * 11 TFTT | A1|~|A3|~|A4
       * 10 TFTF | A1|~|A3
       * 9 TFFT | A1|~|A4
       * 8 TFFF | A1
       * 7 FTTT | A2|~|A3|~|A4
       * 6 FTTF | A2|~|A3
       * 5 FTFT | A2|~|A4
       * 4 FTFF | A2
       * 3 FFTT | A3|~|A4
       * 2 FFTF | A3
       * 1 FFFT | A4
       * 0 FFFF | DIV
       * Notes: each No is equal to binary bit value in G1G2G3G4. For example, 3 = 0011
       */
  
      int nr_of_comb = (int) Math.pow(2.0, (double) term2.getNumberOfGuards());
  
      // loop from 0 to 15
      List<Pair<Pred, CircusAction>> lstCombTable = new ArrayList<Pair<Pred, CircusAction>>();
  
      // combination of all guarded conditions into each case
      for (int i = 0; i < nr_of_comb; i++) {
        Pred pred = null;
        CircusAction ca = null;
  
        for (int j = 0; j < term2.getNumberOfGuards(); j++) {
          if ((i & (1 << j)) != 0) {
            // True
            if (pred == null) {
              pred = lstPPCGA.get(j).getFirst();
            }
            else {
              List<Pred> lstPred = new ArrayList<Pred>();
              lstPred.add(pred);
              lstPred.add(lstPPCGA.get(j).getFirst());
              pred = fac_.createAndPred(lstPred, And.Wedge);
            }
  
            if (ca == null) {
              ca = lstPPCGA.get(j).getThird();
            }
            else {
              List<CircusAction> lstCA = new ArrayList<CircusAction>();
              lstCA.add(ca);
              lstCA.add(lstPPCGA.get(j).getThird());
              ca = cfac_.createIntChoiceAction(lstCA);
            }
          }
          else {
            // False
            if (pred == null) {
              pred = lstPPCGA.get(j).getSecond();
            }
            else {
              List<Pred> lstPred = new ArrayList<Pred>();
              lstPred.add(pred);
              lstPred.add(lstPPCGA.get(j).getSecond());
              pred = fac_.createAndPred(lstPred, And.Wedge);
            }
          }
        }
  
        // for no.0 and in this case, ca is never assigned
        if(ca == null) {
          ca = cfac_.createChaosAction();
        }
        // add to table
        lstCombTable.add(new Pair<Pred, CircusAction>(pred, ca));
      }
  
      /**
       * 3. create external choice of guarded actions from lstCombTable
       */
      List<GuardedAction> lstGA = new ArrayList<GuardedAction>();
      for (Pair<Pred, CircusAction> tp : lstCombTable) {
        lstGA.add(cfac_.createGuardedAction(tp.getSecond(), tp.getFirst()));
      }
  
      CircusAction ca = null;
      for(int index = lstGA.size() - 1; index >= 0; index--) {
        List<CircusAction> lstCA = new ArrayList<CircusAction>();
        lstCA.add(lstGA.get(index));
        if(ca == null) {
          lstCA.add(lstGA.get(index - 1));
          index--;
        }
        else {
          lstCA.add(ca);
        }
        ca = cfac_.createExtChoiceAction(lstCA);
      }
      
      updateParentAction(term, ca);
      visit(ca);
    }
    
    return null;
  }

  @Override
  public Object visitCircusChannelSet(CircusChannelSet term)
  {
    /*if(rewrite_stage_ == 1) */ {
      visit(term.getExpr());
    }
    return null;
  }

  @Override
  public Object visitIndexedProcess(IndexedProcess term)
  {
 // a set for storing rewritten basic processes after rewritten.
    Set<ProcessPara> spp = new HashSet<ProcessPara>();
    
    // indexed process
    IndexedProcess ip = term;
    
    // 1. get all permutation of its variable declarations
//    TreeSet<Pair<String, TreeSet<Pair<String, Expr>>>> ts = 
//        new TreeSet<Pair<String, TreeSet<Pair<String, Expr>>>>(new pairStringTComparator<TreeSet<Pair<String, Expr>>>());
    List<Pair<String, TreeSet<Pair<String, Expr>>>> ts = 
        new ArrayList<Pair<String, TreeSet<Pair<String, Expr>>>>();
    
    Set<List<Pair<String, Expr>>> sls = new HashSet<List<Pair<String, Expr>>>();
    
    expandDeclList2Set(ip.getZDeclList(), ts, sls);
    
    // 2. expand the basic process or call process
    // the process can be a BasicProcess, a reference to defined Basic Process, or others???
    if (ip.getCircusProcess() instanceof CallProcess) {
      CallProcess cp = (CallProcess)ip.getCircusProcess();
//      assert(cp.getCallUsage().equals(CallUsage.Indexed));
      assert(cp.getCallExpr() instanceof RefExpr && ZUtils.isReferenceExpr(cp.getCallExpr()));
      String cname = Circus2ZCSPUtils.termToString((RefExpr)cp.getCallExpr());
      
      // get the definition of basic process and it can not be got from definition table
      for(Para p: paralist_) {
        if(p instanceof ProcessPara) {
          if(Circus2ZCSPUtils.termToString(((ProcessPara)p).getZName()).equals(cname)) {
            if(((ProcessPara)p).getCircusProcess() instanceof BasicProcess) {
              BasicProcess bp1 = ZUtils.cloneTerm(((ProcessPara)p).getCircusBasicProcess());
              ip.setCircusProcess(bp1);
            }
            else {
              throw new CztException("Invalid Class " + ((ProcessPara)p).getCircusProcess().getClass().getName() + 
                  " for CallProcess of Indexed process. Expected BasicProcess!");
            }
            break;
          }
        }
      }
    } else if (ip.getCircusProcess() instanceof BasicProcess) {
      
    } else {
      throw new CztException("Invalid Class " + ip.getCircusProcess().getClass().getName() + 
          " for Indexed process. Expected BasicProcess or CallProcess");
    }
    
    // 3. find out all channels in its Basic Process
    
    for(List<Pair<String, Expr>> lstr: sls) {
      // new basic process name
      String new_pname = para_name_;
      Iterator<Pair<String, TreeSet<Pair<String, Expr>>>> ite = ts.iterator();
      Map<String,Pair<String, Expr>> lname_map = new HashMap<String,Pair<String, Expr>>();
      int i = 0;
      while(ite.hasNext()) {
        Pair<String, TreeSet<Pair<String, Expr>>> p = ite.next();
//        lname_map.add(new Pair<String,String>(p.getFirst(), lstr.get(i)));
        for(String chn: map_.getAllChannels()) {
          // actually the channel name in IP has been change to c_i when it is typechecked.
          lname_map.put(chn, 
              new Pair<String,Expr>(MessageFormat.format(FormatPattern.INDEXED_PROCESS_CHN_RENAMING_PATT, chn, p.getFirst(), lstr.get(i).getFirst()),
                  lstr.get(i).getSecond()));
        }
        new_pname = MessageFormat.format(FormatPattern.PARAM_PROCESS_RENAMING_PATT, new_pname, lstr.get(i).getFirst());
        i++;
      }
      
      // replace all channels (c) in the basic process to c_i.i
      BasicProcess bp = (BasicProcess)ZUtils.cloneTerm(ip.getCircusProcess());
      if(!lname_map.isEmpty()) {
        bp.accept(new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_CHN_RENAME, lname_map));
      }
      
      ProcessPara new_pp = cfac_.createProcessPara(
          fac_.createZName(new_pname, fac_.createZStrokeList(), null), 
          fac_.createZNameList(), 
          bp);
      
      List<Object> lo = new_pp.getAnns();
      if(list_ann_ != null) {
        lo.addAll(list_ann_);
      }
      spp.add(new_pp);
    }
    
    if(!spp.isEmpty()) {
        new_paralist_.addAll(spp);
        return spp;
    }
    else {
      return null;
    }
  }

  @Override
  public Object visitSeqProcessIte(SeqProcessIte term)
  {
    circus_process_stack_.push(term);
    visit(term.getCircusProcess());
    circus_process_stack_.pop();
    return null;
  }

  @Override
  public Object visitIntChoiceAction(IntChoiceAction term)
  {
    if(rewrite_stage_ == 4) {
      circus_action_stack_.push(term);
      visit(term.getLeftAction());
      visit(term.getRightAction());
      circus_action_stack_.pop();
      
      mergeAndUpdateRpreOfTerm(term);
    }
    return null;
  }

  @Override
  public Object visitDotField(DotField term)
  {
    /*if(rewrite_stage_ == 1) */ {
      visit(term.getExpr());
    }

    return null;
  }

  @Override
  public Object visitIntChoiceProcess(IntChoiceProcess term)
  {
    circus_process_stack_.push(term);
    visit(term.getLeftProcess());
    visit(term.getRightProcess());
    circus_process_stack_.pop();
    return null;
  }

  @Override
  public Object visitParallelAction(ParallelAction term)
  {
    if(rewrite_stage_ == 4) {
      circus_action_stack_.push(term);
      visit(term.getLeftAction());
      visit(term.getRightAction());
      circus_action_stack_.pop();
      
      mergeAndUpdateRpreOfTerm(term);
    }
    return null;
  }

  @Override
  public Object visitOutputFieldAnn(OutputFieldAnn term)
  {

    return null;
  }

  @Override
  public Object visitActionType(ActionType term)
  {

    return null;
  }

  @Override
  public Object visitInterleaveAction(InterleaveAction term)
  {
    if(rewrite_stage_ == 4) {
      circus_action_stack_.push(term);
      visit(term.getLeftAction());
      visit(term.getRightAction());
      circus_action_stack_.pop();
      
      mergeAndUpdateRpreOfTerm(term);
    }
    return null;
  }

  @Override
  public Object visitAlphabetisedParallelActionIte(AlphabetisedParallelActionIte term)
  {

    return null;
  }

  @Override
  public Object visitGuardedAction(GuardedAction term)
  {
    if(rewrite_stage_ == 4) {
      circus_action_stack_.push(term);
      
      // 1. get which state components are evaluated in guarded condition.
      
      ZNameSetVisitor znsv = new ZNameSetVisitor();
      
      // a set of state variables
      List<String> lst_stvar = map_.getStatList(para_name_);
      Set<String> set_stvar = new HashSet<String>();
      set_stvar.addAll(lst_stvar);
      
      // a set of state variables used in the channel expression
      Set<String> set_stvar_used = new HashSet<String>();
      
      term.getPred().accept(znsv);
      
      Set<String> nset = znsv.getStrSet();
      // intersection of nset and set_stvar to get all state variables used
      nset.retainAll(set_stvar);
      set_stvar_used.addAll(nset);
      
      Set<Communication> setCCond = new HashSet<Communication>();
      
      for(String v: set_stvar_used) {
        // P_OP_x
        String st_para = MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_,
            MessageFormat.format(FormatPattern.STATE_RETR_PARA_NAME_PATT, v));
        
        // check if it has been added to CSP or not. If not, just add it to CSP
        Pair<Expr, Boolean> p = visited_state_op_.get(st_para);
        if(p != null && p.getSecond().equals(Boolean.FALSE)) {
          addStateRetrieveEventToCSP(new Pair<String, Expr>(st_para, p.getFirst()));
        }
        
        // create Schema Expr
        RefExpr re = cfac_.createRefExpr(
            fac_.createZName(st_para, fac_.createZStrokeList(), null), 
            cfac_.createZExprList(), false, false);
        SchExprAction sea = cfac_.createSchExprAction(re);
        
        // (P_OP_x) is expressed as P_OP_x?x channel
        List<Field> lstField = new ArrayList<Field>();
        // ?x
        Field f = cfac_.createInputField(
            cfac_.createZName(v, cfac_.createZStrokeList(), null), 
            cfac_.createTruePred());
        lstField.add(f);
        CircusFieldList cFldList = cfac_.createCircusFieldList(lstField);
        Communication c = cfac_.createCommunication();
        c.setChannelExpr(re);
        c.setFieldList(cFldList);
        c.setCommUsage(CommUsage.Normal);
        c.setCommPattern(CommPattern.Input);
        c.setIndexed(false);
        c.setMultiSych(BigInteger.valueOf(0));
        setCCond.add(c);
      }
      
      // 2. visit its action
      visit(term.getCircusAction());
      circus_action_stack_.pop();
      
      // 3. get the prefix of its action (Rpre)
      CircusAction ca = term.getCircusAction();
      Set<Communication> setCAct = new HashSet<Communication>();
      
      if(ca instanceof PrefixingAction) {
        ca = removeRpreFromPrefixingAction((PrefixingAction)ca, setCAct);
      }

      term.setCircusAction(ca);
      
      // 3.1 merge
      setCAct.addAll(setCCond);
      
      // 3.2 add to the prefix of current action
      PrefixingAction pa = cfac_.createPrefixingAction();
      for(Communication c: setCAct) {
        if(pa.getCircusAction() == null) {
          pa.setCommunication(c);
          pa.setCircusAction(term);
        } 
        else {
          PrefixingAction tpa = cfac_.createPrefixingAction();
          tpa.setCommunication(c);
          tpa.setCircusAction(pa);
          pa = tpa;
        }
      }
      
      if(pa.getCircusAction() != null) {
        updateParentAction(term, pa);
      }
    }
    return null;
  }

  @Override
  public Object visitInputField(InputField term)
  {
    return null;
  }

  /**
   * empty channel set
   * {|c|}
   */
  @Override
  public Object visitBasicChannelSetExpr(BasicChannelSetExpr term)
  {
    visit(term.getCircusCommunicationList());
    return null;
  }

  @Override
  public Object visitActionPara(ActionPara term)
  {
    return null;
  }

  @Override
  public Object visitAlphabetisedParallelProcessIte(AlphabetisedParallelProcessIte term)
  {

    return null;
  }

  @Override
  public Object visitCircusCommunicationList(CircusCommunicationList term)
  {
    if (term.getCommunication().isEmpty()) {
      // empty communication list
    }

    for (Communication c : term.getCommunication()) {
      visit(c);
    }
    return null;
  }

  @Override
  public Object visitChannelDecl(ChannelDecl term)
  {
    visit(term.getExpr());

    // rewrite would not change
    for (Name zn : term.getZChannelNameList()) {
      visit(zn);
      // add each channel to the map_
      map_.addChnDecl(Circus2ZCSPUtils.termToString(zn), 
          Circus2ZCSPUtils.termToString(term.getExpr()), 
          term.getExpr());
    }

    return null;
  }

  @Override
  public Object visitActionSignatureList(ActionSignatureList term)
  {

    return null;
  }

  @Override
  public Object visitInterleaveProcessIdx(InterleaveProcessIdx term)
  {

    return null;
  }

  /*
   * (non-Javadoc)
   * @see net.sourceforge.czt.circus.visitor.ExtChoiceActionIteVisitor#visitExtChoiceActionIte(net.sourceforge.czt.circus.ast.ExtChoiceActionIte)
   * 
   * In this implementation, we don't expand iterated external choice but just visit its action and then move its prefix in the beginning of 
   * iterated external choice.
   */
  @Override
  public Object visitExtChoiceActionIte(ExtChoiceActionIte term)
  {
    if(rewrite_stage_ == 4) {
      int nrOfVarDecl = 0;
      for(Decl decl: term.getZDeclList()) {
        if(decl instanceof VarDecl) {
          for(Name name: ((VarDecl)decl).getZNameList()) {
            loc_vars_stack_.push(
                new Pair<String, Term>(
                Circus2ZCSPUtils.termToString(name), ((VarDecl)decl).getExpr()
                ));
            nrOfVarDecl++;
          }
        }
      }

      circus_action_stack_.push(term);
      visit(term.getCircusAction());
      circus_action_stack_.pop();
      
      mergeAndUpdateRpreOfTerm(term);
      
      // update context by removing
      while(nrOfVarDecl > 0) {
        loc_vars_stack_.pop();
        nrOfVarDecl--;
      }
    }
    return null;
  }

  @Override
  public Object visitParallelProcessIte(ParallelProcessIte term)
  {
    circus_process_stack_.push(term);
    visit(term.getCircusProcess());
    circus_process_stack_.pop();
    return null;
  }

  /**
   * rewrite prefixing action as well as update local variable stacks since c?x?y will introduce two variables (x and y)
   */
  @Override
  public Object visitPrefixingAction(PrefixingAction term)
  {
    if(rewrite_stage_ == 4) {
      if(visited_terms_.contains(term)) {
        return null;
      }
      // the fileds counting, used to get the right type for each field
      // For example,
      // channel c: A \cross B \cross C
      // c?x!y?z -> SKIP
      // there are three fields and with this number we can get the type
      // for x is A, for y is B, and for z is C
      int fieldCnt = 0;
      
      // Number of input variables
      int inVarsCnt = 0;
      
      visit(term.getCommunication());
      
      Pair<String, Term> chnexpr = map_.getChnDecl(
          Circus2ZCSPUtils.termToString(term.getCommunication().getChannelExpr()));
      
      // Get the type for nth input/output in the channel
      // For example, channel c:A \cross B \cross C.
      // For c?x!y?z, if varname is x, then we get the type A.
      // If varname is z, then we get the type C.
      List<Term> te = new ArrayList<Term>();
      if (chnexpr != null) {
        // Product express
        if (chnexpr.getSecond() instanceof ProdExpr) {
          Term t = null;
          t = chnexpr.getSecond();
          te.addAll(((ProdExpr) t).getZExprList());
        }
        else {
          te.add(chnexpr.getSecond());
        }
      }
      
      switch(term.getCommunication().getCommPattern()) {
        case Synch:
          // no change
          break;
        case Input:
          // no change
          for (Field field : term.getCommunication().getCircusFieldList()) {
            if (field instanceof InputField) {
              Pred r = ((InputField)field).getRestriction();
              // c?x:{true}
              if((r != null) && (r instanceof TruePred)) {
                ZName n = ((InputField)field).getVariableZName();
                // add <VarName, Tvar>
                loc_vars_stack_.push(new Pair<String, Term>(
                    Circus2ZCSPUtils.termToString(n), 
                    te.get(fieldCnt)));
                inVarsCnt++;
              }
              // c?x:{y:T | p}
            }
            fieldCnt++;
          }
          break;
        case Output:
        case Mixed:
          // find out which state components are evaluated in the expression of output channel
          // TODO: how to find out?
          CircusFieldList cfl = term.getCommunication().getCircusFieldList();
          ZNameSetVisitor znsv = new ZNameSetVisitor();
          
          // a set of state variables
          List<String> lst_stvar = map_.getStatList(para_name_);
          Set<String> set_stvar = new HashSet<String>();
          set_stvar.addAll(lst_stvar);
          
          // a set of state variables used in the channel expression
          Set<String> set_stvar_used = new HashSet<String>();
          
          for (Field field : cfl) {
            if (field instanceof DotField) {
              ((DotField) field).getExpr().accept(znsv);
            }
            else if (field instanceof InputField) {
              Pred r = ((InputField)field).getRestriction();
              if((r != null) && (r instanceof TruePred)) {
                ZName n = ((InputField)field).getVariableZName();
                // add <VarName, Tvar>
                loc_vars_stack_.push(new Pair<String, Term>(
                    Circus2ZCSPUtils.termToString(n), 
                    te.get(fieldCnt)));
                inVarsCnt++;
              }            
            }
            fieldCnt++;
          }
          
          Set<String> nset = znsv.getStrSet();
          // intersection of nset and set_stvar to get all state variables used
          nset.retainAll(set_stvar);
          set_stvar_used.addAll(nset);
          
          PrefixingAction pa = term;

          for(String v: set_stvar_used) {
            // P_OP_x
            String st_para = MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_,
                MessageFormat.format(FormatPattern.STATE_RETR_PARA_NAME_PATT, v));
            
            // check if it has been added to CSP or not
            Pair<Expr, Boolean> p = visited_state_op_.get(st_para);
            if(p != null && p.getSecond().equals(Boolean.FALSE)) {
              addStateRetrieveEventToCSP(new Pair<String, Expr>(st_para, p.getFirst()));
            }

            // create Schema Expr
            RefExpr re = cfac_.createRefExpr(
                fac_.createZName(st_para, fac_.createZStrokeList(), null), 
                cfac_.createZExprList(), false, false);
            SchExprAction sea = cfac_.createSchExprAction(re);
            
            // (P_OP_x) is expressed as P_OP_x?x channel
            List<Field> lstField = new ArrayList<Field>();
            // ?x
            Field f = cfac_.createInputField(
                cfac_.createZName(v, cfac_.createZStrokeList(), null), 
                cfac_.createTruePred());
            lstField.add(f);
            CircusFieldList cFldList = cfac_.createCircusFieldList(lstField);
//            Communication c = cfac_.createCommunication(re, cFldList, CommUsage.Normal, CommPattern.Input, 0, false);
            Communication c = cfac_.createCommunication();
            c.setChannelExpr(re);
            c.setFieldList(cFldList);
            c.setCommUsage(CommUsage.Normal);
            c.setCommPattern(CommPattern.Input);
            c.setIndexed(false);
            c.setMultiSych(BigInteger.valueOf(0));

            PrefixingAction tpa = cfac_.createPrefixingAction();
            tpa.setCommunication(c);
            tpa.setCircusAction(pa);
            pa = tpa;
          }
          
          if(!pa.equals(term)) {
            updateParentAction(term, pa);
          }
          
          break;
        case ChannelSet:
          break;
        default:
          throw new CztException("Undefined communication pattern [" + term.getCommunication().getCommPattern() + "] for PrefixingAction!");
//          break;
      }
      
      // Rwrt(A)
      circus_action_stack_.push(term);
      visit(term.getCircusAction());
      circus_action_stack_.pop();
      
      for(int i = 0; i < inVarsCnt; i++) {
        loc_vars_stack_.pop();
      }
      
      visited_terms_.add(term);
    }
    return null;
  }

  /**
   * When expr is originally in the action, when we put it back to Z part, such as
   *    assignment: (LHS := RHS) => Z == [\Delta State | P_s' = RHS [P_s/s]]
   *    specification statement: ...
   * @param expr
   */
  private void renameStateComp(Term expr)
  {
    List<String> lstState = map_.getStatList(para_name_);

    // a list of pairs from original state name to renamed name
    List<Pair<String, String>> lstStRenPair = new ArrayList<Pair<String, String>>();
    for(String v: lstState) {
      // (v, P_v)
      lstStRenPair.add(new Pair<String, String>(v,
          MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_, v)));
    }
    // s => P_s
    expr.accept(
        new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_RWT_RENAME, lstStRenPair));
  }
  
  @Override
  public Object visitAssignmentCommand(AssignmentCommand term)
  {
    if(rewrite_stage_ == 4) {
      AssignmentCommand term2 = ZUtils.cloneTerm(term);
  
      // paraName
      String paraName = MessageFormat.format(CSPPredExpPattern.getPattern(
          PredExpPattern.ASSIGN_NAME_PATT), para_name_, map_.incn());
  
      //
      // 1. for assemble of assOp paragraph
      //
      ZDeclList declList = fac_.createZDeclList();
  
      Pred pred = null;
  
      ZNameList nl = term2.getAssignmentPairs().getZLHS();
      ZExprList el = term2.getAssignmentPairs().getZRHS();
  
      // input variables list <variable name, decl>
      // for assembling of VarDecl in assOp
      // l?
      Set<Pair<String, Decl>> ilpsd = new HashSet<Pair<String, Decl>>();
  
      // output variables list <variable name, decl>
      // for assembling of VarDecl in assOp
      // l!
      Set<Pair<String, Decl>> olpsd = new HashSet<Pair<String, Decl>>();
  
      /**
       * A list of variable name
       */
      List<String> slst = new ArrayList<String>();
  
      /**
       * A list of state variables in LHS (would be updated)
       */
      List<String> lstStL = new ArrayList<String>();
      
      /**
       * A list of local variable name and its type in this predicate. Type is used to construct the Z
       * schema
       */
      List<Pair<String, Term>> lllst = new ArrayList<Pair<String, Term>>();
  
      List<String> lstState = map_.getStatList(para_name_);
      
//      // a list of pairs from original state name to renamed name
//      List<Pair<String, String>> lstStRenPair = new ArrayList<Pair<String, String>>();
//      for(String v: lstState) {
//        // (v, P_v)
//        lstStRenPair.add(new Pair<String, String>(v,
//            MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_, v)));
//      }
      
      for (int i = 0; i < nl.size(); i++) {
        // LHS
        // only one variable is possible
        Name n = nl.get(i);
        String lhs = Circus2ZCSPUtils.termToString(n);
        if (lstState.contains(lhs)) {
          slst.clear();
          slst.add(lhs);
          lstStL.add(lhs);
          // s => s'
          nl.get(i).accept(
              new VariableRenamingSchemaVisitor(slst, VariableRenameSchema.VRS_APPEND_NEXTSTROKE));
          // s => P_s
//          nl.get(i).accept(
//              new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_RWT_RENAME, lstStRenPair));
          renameStateComp(nl.get(i));
        }
        else if (isLocVar(n, lllst)) {
          // Only one variable in each separate assignment
          slst.clear();
          slst.add(lhs);
          // l => l!
          nl.get(i).accept(
              new VariableRenamingSchemaVisitor(slst, VariableRenameSchema.VRS_APPEND_OUTSTROKE));
  
          List<String> lst = Circus2ZCSPUtils.extractFirstfromListPair(olpsd);
          if(!lst.contains(lllst.get(0).getFirst())) {
            // VarDecl
            // create OutStroke !
            List<Stroke> ls = new ArrayList<Stroke>();
            Stroke ot = fac_.createOutStroke();
            ls.add(ot);
            // create Name List with InStroke
            List<Name> ln = new ArrayList<Name>();
            Name name = fac_.createZName(lhs, fac_.createZStrokeList(ls), null);
            ln.add(name);
    
            // create Namelist
            NameList nl1 = fac_.createZNameList(ln);
            VarDecl vd = fac_.createVarDecl(nl1, (Expr) (lllst.get(0).getSecond()));
    
            olpsd.add(new Pair<String, Decl>(lllst.get(0).getFirst(), vd));
          }
        }
  
        // RHS
        Expr e = el.get(i);
        renameStateComp(e);
        
        lllst.clear();
        if (isLocVar(e, lllst)) {
          slst.clear();
          for (Pair<String, Term> pst : lllst) {
            slst.add(pst.getFirst());
            List<String> lst = Circus2ZCSPUtils.extractFirstfromListPair(ilpsd);
            if(!lst.contains(pst.getFirst()))
            {  
              // VarDecl
              // create InStroke ?
              List<Stroke> ls = new ArrayList<Stroke>();
              Stroke it = fac_.createInStroke();
              ls.add(it);
              // create Name List with InStroke
              List<Name> ln = new ArrayList<Name>();
              Name name = fac_.createZName(pst.getFirst(), fac_.createZStrokeList(ls), null);
              ln.add(name);
    
              // create Namelist
              NameList nl1 = fac_.createZNameList(ln);
              VarDecl vd = fac_.createVarDecl(nl1, (Expr) (pst.getSecond()));
              ilpsd.add(new Pair<String, Decl>(pst.getFirst(), vd));
            }
          }
          // l => l?
          el.get(i).accept(
              new VariableRenamingSchemaVisitor(slst, VariableRenameSchema.VRS_APPEND_INSTROKE));
//          // s => P_s
//          el.get(i).accept(
//              new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_RWT_RENAME, lstStRenPair));
        }
  
        // 1st Expr
        RefExpr re = fac_.createRefExpr(nl.get(i), fac_.createZExprList(), false, false);
        // 2nd Expr
        List<Expr> le = new ArrayList<Expr>();
        le.add(el.get(i));
        ZExprList zel = fac_.createZExprList(le);
        SetExpr se = fac_.createSetExpr(zel);
  
        // ExprList for MemPred
        List<Expr> le2 = new ArrayList<Expr>();
        le2.add(re);
        le2.add(se);
        // for equality, mixfix is true
        MemPred mp = fac_.createMemPred(le2, true);
  
        if (pred == null) {
          pred = mp;
        }
        else {
          List<Pred> lp = new ArrayList<Pred>();
          lp.add(pred);
          lp.add(mp);
          AndPred ap = fac_.createAndPred(lp, And.Wedge);
          pred = ap;
        }
      }
  
      /**
       * For pred, add other state variables' equality spec in pred
       * For example, if there are three state variables (s1, s2, s3) in this process
       * and s1' is updated by assignment. Then we should add s2'=s2 and s3'=s3 in pred
       * lstStL - state variables name in LHS
       */
  
      // remove state variables which are occurred in LHS of assignment
      lstState.removeAll(lstStL);
  
      for (String v : lstState) {
        String newv = MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_, v);
        List<Stroke> ls = new ArrayList<Stroke>();
        Stroke next = fac_.createNextStroke();
        ls.add(next);
        ZStrokeList zsl = fac_.createZStrokeList(ls);
        // LHS (s')
        RefExpr lre = fac_.createRefExpr(fac_.createZName(newv, zsl, null), fac_.createZExprList(),
            false, false);
        // RHS (s)
        RefExpr rre = fac_.createRefExpr(fac_.createZName(newv, fac_.createZStrokeList(), null),
            fac_.createZExprList(), false, false);
        List<Expr> le = new ArrayList<Expr>();
        le.add(rre);
        ZExprList zel = fac_.createZExprList(le);
        SetExpr se = fac_.createSetExpr(zel);
  
        // ExprList for MemPred
        List<Expr> le2 = new ArrayList<Expr>();
        le2.add(lre);
        le2.add(se);
        // for equality, mixfix is true
        MemPred mp = fac_.createMemPred(le2, true);
  
        List<Pred> lp = new ArrayList<Pred>();
        lp.add(pred);
        lp.add(mp);
        AndPred ap = fac_.createAndPred(lp, And.Wedge);
        pred = ap;
      }
  
      // input variables of assOp paragraph will get values from CSP output
      // for each variable, we need to use getn?v to get the value of local variable
      // v first
      for (Pair<String, Decl> p : ilpsd) {
        declList.add(p.getSecond());
      }
  
      // output variables of assOp paragraph will update values in CSP
      for (Pair<String, Decl> p : olpsd) {
        declList.add(p.getSecond());
      }
  
      AxPara axpara = assembleZPara(paraName, pred, declList);
      
      assert(process_para_.getCircusProcess() instanceof BasicProcess);
      
      process_para_.getCircusBasicProcess().getZParaList().add(axpara);
      
      // create Schema Expr
      RefExpr re = cfac_.createRefExpr(
          fac_.createZName(paraName, fac_.createZStrokeList(), null), 
          cfac_.createZExprList(), false, false);
      SchExprAction sea = cfac_.createSchExprAction(re);
      
      updateParentAction(term, sea);
    }
    return null;
  }

  @Override
  public Object visitParamProcess(ParamProcess term)
  {
    // a set for storing rewritten basic processes after rewritten.
    Set<ProcessPara> spp = new HashSet<ProcessPara>();
    
    // parametrised process
    ParamProcess pp = term;
    
//    TreeSet<Pair<String, TreeSet<Pair<String, Expr>>>> ts = 
//        new TreeSet<Pair<String, TreeSet<Pair<String, Expr>>>>(new pairStringTComparator<TreeSet<Pair<String, Expr>>>());
    List<Pair<String, TreeSet<Pair<String, Expr>>>> ts = 
        new ArrayList<Pair<String, TreeSet<Pair<String, Expr>>>>();
    Set<List<Pair<String, Expr>>> sls = new HashSet<List<Pair<String, Expr>>>();
    
    expandDeclList2Set(pp.getZDeclList(), ts, sls);
    
    // the process can be a BasicProcess, a reference to defined Basic Process, or others???
    if (pp.getCircusProcess() instanceof CallProcess) {
      CallProcess cp = (CallProcess)pp.getCircusProcess();
      assert(cp.getCallUsage().equals(CallUsage.Parameterised));
      assert(cp.getCallExpr() instanceof RefExpr && ZUtils.isReferenceExpr(cp.getCallExpr()));
      String cname = Circus2ZCSPUtils.termToString((RefExpr)cp.getCallExpr());
      
      // get the definition of basic process and it can not be got from definition table
      for(Para p: paralist_) {
        if(p instanceof ProcessPara) {
          if(Circus2ZCSPUtils.termToString(((ProcessPara)p).getZName()).equals(cname)) {
            if(((ProcessPara)p).getCircusProcess() instanceof BasicProcess) {
              BasicProcess bp1 = ZUtils.cloneTerm(((ProcessPara)p).getCircusBasicProcess());
              pp.setCircusProcess(bp1);
            }
            else {
              throw new CztException("Invalid Class " + ((ProcessPara)p).getCircusProcess().getClass().getName() + 
                  " for CallProcess of Parametrised process. Expected BasicProcess!");
            }
            break;
          }
        }
      }
    } else if (pp.getCircusProcess() instanceof BasicProcess) {
      
    } else if (pp.getCircusProcess() instanceof ParallelProcessIte || 
        pp.getCircusProcess() instanceof InterleaveProcessIte) {
      
    } else {
      throw new CztException("Invalid Class " + pp.getCircusProcess().getClass().getName() + 
          " for Parametrised process. Expected BasicProcess or CallProcess");
    }
    
    for(List<Pair<String, Expr>> lstr: sls) {
      // new basic process name
      String new_pname = para_name_;
      Iterator<Pair<String, TreeSet<Pair<String, Expr>>>> ite = ts.iterator();
      Map<String,Pair<String, Expr>> lname_map = new HashMap<String,Pair<String, Expr>>();
      List<Pair<String, String>> lname_list = new ArrayList<Pair<String, String>>();
      int i = 0;
      while(ite.hasNext()) {
        Pair<String, TreeSet<Pair<String, Expr>>> p = ite.next();
        lname_map.put(p.getFirst(), new Pair<String,Expr>(lstr.get(i).getFirst(), lstr.get(i).getSecond()));
        lname_list.add(new Pair<String,String>(p.getFirst(), lstr.get(i).getFirst()));
        new_pname = MessageFormat.format(FormatPattern.PARAM_PROCESS_RENAMING_PATT, new_pname, lstr.get(i).getFirst());
        i++;
      }
      
      // replace all parameter variables (x) in the basic process to its corresponding value
//      BasicProcess bp = (BasicProcess)ZUtils.cloneTerm(pp.getCircusProcess());
      CircusProcess bp = ZUtils.cloneTerm(pp.getCircusProcess());
      bp.accept(new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_NAME_REPLACE, lname_map));
      bp.accept(new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_RWT_RENAME, lname_list));
      
      ProcessPara new_pp = cfac_.createProcessPara(
          fac_.createZName(new_pname, fac_.createZStrokeList(), null), 
          fac_.createZNameList(), 
          bp);
      
      List<Object> lo = new_pp.getAnns();
      if(list_ann_ != null) {
        lo.addAll(list_ann_);
      }
      
      spp.add(new_pp);
    }
    
    if(!spp.isEmpty()) {
        new_paralist_.addAll(spp);
        
        for(ProcessPara p: spp) {
          if(p.getCircusProcess() instanceof BasicProcess) {
            visit(p.getCircusBasicProcess());
          }
          else {
            visit(p.getCircusProcess());
          }
        }
        return spp;
    } 
    else {
      return null;
    }
  }

  @Override
  public Object visitAlphabetisedParallelProcessIdx(AlphabetisedParallelProcessIdx term)
  {

    return null;
  }
  
  @Override
  public Object visitCallAction(CallAction term)
  {
    if(rewrite_stage_ == 4) {
      // 0. A reference to (X) in MuAction (\mu X)
      if (circus_muaction_stack_.contains(term.getZName())) {
        // nothing changed and just return
        return null;
      }
      
      // 1. A reference to an action definition
      if(term.getZExprList().isEmpty()) {
        // action definition
        CircusAction cca = null;
        
        assert(process_para_.getCircusProcess() instanceof BasicProcess);
        for(Para p: process_para_.getCircusBasicProcess().getZParaList()) {
          if(p instanceof ActionPara) {
            if(Circus2ZCSPUtils.isEquals(((ActionPara) p).getZName(), term.getZName())) {
               cca = ((ActionPara) p).getCircusAction();
               // we also need to identify if this action is a recursion definition of action
               // X \circdef ...X => \mu X @ X = ...X
               boolean muaction = isAPossibleMutualRecursion(term.getZName(), cca);
               if(muaction) {
                 MuAction maction = cfac_.createMuAction(cca, ((ActionPara) p).getName());
                 cca = maction;
               }
//               ZNameSetVisitor znsv = new ZNameSetVisitor();
//               cca.accept(znsv);
//               Set<String> setName = znsv.getStrSet();
//               String actionName = Circus2ZCSPUtils.termToString(((ActionPara)p).getZName());
//               if(setName.contains(actionName)) {
//                 MuAction maction = cfac_.createMuAction(cca, ((ActionPara) p).getName());
//                 cca = maction;
//               }
               break;
            }
          }
          else if((p instanceof AxPara)) {
            // it is still possible that a schema expression but missing \lcircschexp ... \rcircschexp
            AxParaKind kind = Circus2ZCSPUtils.getAxParaKind((AxPara)p);
            switch(kind) {
              case ABBR:
              case HORIZON_SCHEMA:
              case BOXED_SCHEMA:
                ZName name = (ZName) ZUtils.getAxParaSchOrAbbrName(p);
                if(Circus2ZCSPUtils.isEquals(name, term.getZName())) {
                  // create Schema Expr
                  RefExpr re = cfac_.createRefExpr(
                      term.getZName(), 
                      cfac_.createZExprList(), false, false);
                  cca = cfac_.createSchExprAction(re);
                }
                break;
              default:
                break;
            }
          }
        }
        
        if(cca == null) {
          throw new CztException("The definition of the action [" + Circus2ZCSPUtils.termToString(term.getZName()) + "] is not found!");
        }
        
        // update term to cca in its parent
        updateParentAction(term, cca);
        
        visit(cca);
      } 
      // 2. Parametrised action invocation
      else {
        // action definition
        CircusAction cca = null;
        
        // true - parametrised action
        // false - parametrised action by value, result, and value-result
        boolean isParamAction = true;
        
        assert(process_para_.getCircusProcess() instanceof BasicProcess);
        for(Para p: process_para_.getCircusBasicProcess().getZParaList()) {
          if(p instanceof ActionPara) {
            if(((ActionPara) p).getZName().equals(term.getZName())) {
               cca = ((ActionPara) p).getCircusAction();
               break;
            }
          }
        }
        
        if(cca == null) {
          throw new CztException("The definition of the action [" + 
              Circus2ZCSPUtils.termToString(term.getZName()) + "] is not found!");
        }
        
        if(!(cca instanceof ParamAction)) {
          throw new CztException("The definition of the action [" + 
              Circus2ZCSPUtils.termToString(term.getZName()) + "] is not a parametrised action!");       
        }
        
        ZExprList zel = term.getZExprList();
        
        // can be parametrised action, ... by value, by result, and by value-result
        ParamAction pa = (ParamAction)cca;
        
        // TODO: might not be true since x,y:T is treated one VarDecl but two expressions.
//        if(zel.size() != pa.getZDeclList().size()) {
//          throw new CztException("The number of parameters [" + pa.getZDeclList().size() + "]" + "for the action [" + 
//              Circus2ZCSPUtils.termToString(term.getZName()) + "] is not equal to the number of actual expression list [" + zel.size() + "]!");
//        }
        
        // replace x by e to get a new action
        // 1. we have to replace x by e here since e may evaluate state components and in this case, we need rewrite rule 
        // to retrieve the value of state components
        // 2. we can not delay it to later stage
        List<ZName> lstName = new ArrayList<ZName>();
        List<Expr> lstExpr = new ArrayList<Expr>();
        
        // number of variables consumed
        int var_no = 0;
        // a list of decl for Val, Res and VRes
        List<Decl> lstDecl = new ArrayList<Decl>();

        // a list of ZName and Expr for constructing Assignment Command in front of Action A (Val and
        // VRes)
        List<ZName> lstFrtZName = new ArrayList<ZName>();
        List<Expr> lstFrtExpr = new ArrayList<Expr>();

        // a list of ZName and Expr for constructing Assignment Command in rear of Action A (Res and
        // VRes)
        List<ZName> lstBhdZName = new ArrayList<ZName>();
        List<Expr> lstBhdExpr = new ArrayList<Expr>();

        for(Decl decl: pa.getZDeclList()) {
          // for parametrised action
          if(decl instanceof VarDecl) {
            isParamAction = true;
            for(Name n: ((VarDecl)decl).getZNameList()) {
              lstName.add((ZName)n);
            }
          }
          // for parametrised action by value, result and value-result
          else if(decl instanceof QualifiedDecl) {
            isParamAction = false;
            // Variable Declaration
            VarDecl vdecl = fac_.createVarDecl(((QualifiedDecl) decl).getZNameList(),
                ((QualifiedDecl) decl).getExpr());
            lstDecl.add(vdecl);

            ParamQualifier pq = ((QualifiedDecl) decl).getParamQualifier();
            switch (pq) {
              case Value :
                // action A is modified to (x := e; A)
                // assemble variable block
                // create an assignment
                // get a list of parameter exprs for variables
                for (Name name : ((QualifiedDecl) decl).getZNameList()) {
                  lstFrtZName.add((ZName) name);
                  lstFrtExpr.add(zel.get(var_no++));
                }
                break;
              case Result :
                for (Name name : ((QualifiedDecl) decl).getZNameList()) {
                  if (zel.get(var_no) instanceof RefExpr) {
                    lstBhdZName.add(((RefExpr) zel.get(var_no++)).getZName());
                    RefExpr re = fac_.createRefExpr(name, fac_.createZExprList(), false, false);
                    lstBhdExpr.add(re);
                  }
                  else {
                    throw new CztException("Unvalid Expression Parameter [" + var_no
                        + "] for parameterisation by result");
                  }
                }
                break;
              case ValueResult :
                for (Name name : ((QualifiedDecl) decl).getZNameList()) {
                  lstFrtZName.add((ZName) name);
                  lstFrtExpr.add(zel.get(var_no));

                  if (zel.get(var_no) instanceof RefExpr) {
                    lstBhdZName.add(((RefExpr) zel.get(var_no++)).getZName());
                    RefExpr re = fac_.createRefExpr(name, fac_.createZExprList(), false, false);
                    lstBhdExpr.add(re);
                  }
                  else {
                    throw new CztException("Unvalid Expression Parameter [" + var_no
                        + "] for parameterisation by result");
                  }
                }
                break;
              default :
                throw new CztException("Invalid Parameter Qualifier" + pq.toString());
            }
          }
        }
        
        if(isParamAction) {
          lstExpr.addAll(zel.getExpr());
          
          SubstVariableToExpVisitor svte = new SubstVariableToExpVisitor(lstName, lstExpr);
          CircusAction ca = ZUtils.cloneTerm(pa.getCircusAction());
          ca.accept(svte);
          
          // update term to cca in its parent
          updateParentAction(term, ca);
          
          visit(ca);
        }
        else {
          if (!lstDecl.isEmpty()) {
            CircusAction ca = ZUtils.cloneTerm(pa.getCircusAction());
            
            ZDeclList lstZDecl = fac_.createZDeclList(lstDecl);

            if (!lstFrtZName.isEmpty() && !lstFrtExpr.isEmpty()) {
              // AssignmentCommand
              ZExprList lstZExpr = fac_.createZExprList(lstFrtExpr);
              AssignmentPairs assPair = cfac_.createAssignmentPairs(fac_.createZNameList(lstFrtZName),
                  lstZExpr);
              AssignmentCommand assCmd = cfac_.createAssignmentCommand(assPair);

              // SeqAction
              List<CircusAction> lstCAction = new ArrayList<CircusAction>();
              lstCAction.add(assCmd);
              lstCAction.add(ca);
              ca = cfac_.createSeqAction(lstCAction);
            }

            if (!lstBhdZName.isEmpty() && !lstBhdExpr.isEmpty()) {
              // AssignmentCommand
              ZExprList lstZExpr = fac_.createZExprList(lstBhdExpr);
              AssignmentPairs assPair = cfac_.createAssignmentPairs(fac_.createZNameList(lstBhdZName),
                  lstZExpr);
              AssignmentCommand assCmd = cfac_.createAssignmentCommand(assPair);

              // SeqAction
              List<CircusAction> lstCAction = new ArrayList<CircusAction>();
              lstCAction.add(ca);
              lstCAction.add(assCmd);
              ca = cfac_.createSeqAction(lstCAction);
            }

            ca = cfac_.createVarDeclCommand(lstZDecl, ca);
            
            // update term to cca in its parent
            updateParentAction(term, ca);
            
            visit(ca);
          }
        }
      } // end of isEmpty()
      
    }
    return null;
  }

  @Override
  public Object visitExtChoiceProcessIte(ExtChoiceProcessIte term)
  {
    circus_process_stack_.push(term);
    visit(term.getCircusProcess());
    circus_process_stack_.pop();
    return null;
  }

  @Override
  public Object visitVarDeclCommand(VarDeclCommand term)
  {
    if(rewrite_stage_ == 4) {
      // update context by adding variable declarations
      int nrOfVarDecl = 0;
      for(Decl decl: term.getZDeclList()) {
        if(decl instanceof VarDecl) {
          for(Name name: ((VarDecl)decl).getZNameList()) {
            loc_vars_stack_.push(
                new Pair<String, Term>(
                Circus2ZCSPUtils.termToString(name), ((VarDecl)decl).getExpr()
                ));
            nrOfVarDecl++;
          }
        }
      }
      
      circus_action_stack_.push(term);
      visit(term.getCircusAction());
      circus_action_stack_.pop();
      
      mergeAndUpdateRpreOfTerm(term);
      
      // update context by removing
      while(nrOfVarDecl > 0) {
        loc_vars_stack_.pop();
        nrOfVarDecl--;
      }
    }
    return null;
  }

  @Override
  public Object visitImplicitChannelAnn(ImplicitChannelAnn term)
  {

    return null;
  }

  @Override
  public Object visitStopAction(StopAction term)
  {
    if(rewrite_stage_ == 4) {
      
    }
    return null;
  }

  @Override
  public Object visitSeqProcessIdx(SeqProcessIdx term)
  {

    return null;
  }

  @Override
  public Object visitCircusNameSetList(CircusNameSetList term)
  {
    for(NameSet c: term.getNameSet()) {
      visit(c);
    }
    return null;
  }

  @Override
  public Object visitInterleaveProcess(InterleaveProcess term)
  {
    circus_process_stack_.push(term);
    visit(term.getLeftProcess());
    visit(term.getRightProcess());
    circus_process_stack_.pop();
    return null;
  }

  @Override
  public Object visitSkipAction(SkipAction term)
  {
    if(rewrite_stage_ == 4) {
      
    }
    return null;
  }

  @Override
  public Object visitCircusFieldList(CircusFieldList term)
  {
    for(Field c: term.getField()) {
      visit(c);
    }
    return null;
  }

  @Override
  public Object visitParamAction(ParamAction term)
  {
    // for parameterised action, parameterisation by value, parameterisation by result
    // and parameterisation by value and result, the parameter expr list is not null
    return null;
  }

  @Override
  public Object visitStateUpdate(StateUpdate term)
  {

    return null;
  }

  @Override
  public Object visitChannelType(ChannelType term)
  {

    return null;
  }

  @Override
  public Object visitHideAction(HideAction term)
  {
    if(rewrite_stage_ == 4) {
      circus_action_stack_.push(term);
      visit(term.getCircusAction());
      circus_action_stack_.pop();
      
      mergeAndUpdateRpreOfTerm(term);
    }
    return null;
  }

  /**
   * channelset N == CSRef
   */
  @Override
  public Object visitChannelSetPara(ChannelSetPara term)
  {
    visit(term.getZName());
    visit(term.getChannelSet());
    return null;
  }

  /*
   * (non-Javadoc)
   * @see net.sourceforge.czt.circus.visitor.SpecStmtCommandVisitor#visitSpecStmtCommand(net.sourceforge.czt.circus.ast.SpecStmtCommand)
   * 
   * from (where x,y,z are state components and l is a local variable
   *    (x,l \prefixcolon [~ x > 0 \land y \leq 5 \land l = 1, x' = 0 \land l' = 0 \land y' = z - 3 \land z' \geq 8 ~])
   * to
   *    SpecOp == [ \Delta State; l?:Tl; l!:Tl | 
   *            x > 0 \land 
   *            y \leq 5 \land
   *            l? = 1 \land
   *            \exists y':Ty,z':Tz (
   *                    x' = 0 \land
   *                    l! = 0 \land
   *                    y' = z - 3 \land
   *                    z' \geq 8
   *            )
   *       ]
   *            
   */
  @Override
  public Object visitSpecStmtCommand(SpecStmtCommand term)
  {
    if(rewrite_stage_ == 4) {
      SpecStmtKind kind = Circus2ZCSPUtils.getSpecStmtKind(term);
      ZNameList znl = term.getZFrame();
      Pred pre = term.getPre();
      Pred post = term.getPost();
      
      // a set of local variables l? for assembling a Z schema
      Set<Pair<ZName, Term>> setPLocIn = new HashSet<Pair<ZName, Term>>();
      
      // a set of local variables l! for assembling a Z schema
      Set<Pair<ZName, Term>> setPLocOut = new HashSet<Pair<ZName, Term>>();

      
      /**
       * a list of state variables
       */
      List<Pair<String, Term>> lstPState = map_.getStatListWithExp(para_name_);
      
      List<String> lstState = Circus2ZCSPUtils.extractFirstfromListPair(lstPState);
      
      /**
       * a list of state variables in post
       */
      List<Pair<String, Term>> lstPStatePost = new ArrayList<Pair<String, Term>>();
      
      /**
       * a list of state variables in pre
       */
      List<Pair<String, Term>> lstPStatePre = new ArrayList<Pair<String, Term>>();

  
      /**
       * A list of local variable name and its type in pre predicate. Type is used to construct the Z
       * schema
       */
      List<Pair<String, Term>> lstPLocPre = new ArrayList<Pair<String, Term>>();
      
      /**
       * A list of local variable name and its type in post predicate. Type is used to construct the Z
       * schema
       */
      List<Pair<String, Term>> lstPLocPost = new ArrayList<Pair<String, Term>>();
  
      // 1. get local variables used in pre and post
      isLocVar(pre, lstPLocPre);
      isLocVar(post, lstPLocPost);
      
      // 2. get state variables used in post
      isStateVar(post, lstPStatePost);
      
      // 3. find out what variables are updated in post but not included in the frame
      // a set of variables that are not in the frame
      Set<Pair<String, Term>> setPNotInFrame = new HashSet<Pair<String, Term>>();
      
      // a set of variables that are used in the post
      Set<Pair<String, Term>> setPAllVinPost = new HashSet<Pair<String, Term>>();
      
      // get all ZName set used in post
      ZNameSetVisitor znsv = new ZNameSetVisitor();
      post.accept(znsv);
      Set<String> setName = znsv.getStrSet();
      
      // a set of variables in frame
      Set<String> setFrame = new HashSet<String>();

      for(Name zn: znl) {
        setFrame.add(Circus2ZCSPUtils.termToString(zn));
      }
      
      setPAllVinPost.addAll(lstPLocPost);
      setPAllVinPost.addAll(lstPStatePost);
      for(Pair<String, Term> pv: setPAllVinPost) {
        // not in the frame
        if(!setFrame.contains(pv.getFirst())) {
          // but it is used in post
//          if(setName.contains(pv.getFirst())) {
//            setPNotInFrame.add(pv);
//          }
          // if its after version (v') is used in post
          if(setName.contains(pv.getFirst() + ZString.PRIME)) {
            if(lstState.contains(pv.getFirst())) {
              // state variables s' then it would be 
              setPNotInFrame.add(new Pair<String,Term>(
                  MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_, pv.getFirst() + ZString.PRIME), 
                  pv.getSecond()));              
            }
            else { // local variable v'
              setPNotInFrame.add(new Pair<String,Term>(pv.getFirst() + ZString.PRIME, pv.getSecond()));
            }
          }
        }
      }
      
      // 4. replace s by P_s and l by l? in pre
      // 4.1. get state variables used in pre
      isStateVar(pre, lstPStatePre);
      // a list of pairs from original state name to renamed name
      List<Pair<String, String>> lstStRenPair = new ArrayList<Pair<String, String>>();
      for(Pair<String, Term> p: lstPStatePre) {
        // (v, P_v)
        lstStRenPair.add(new Pair<String, String>(p.getFirst(),
            MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_, p.getFirst())));
      }
      // s => P_s
      pre.accept(new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_RWT_RENAME, lstStRenPair));
      
      List<String> lstTemp = new ArrayList<String>();
      for(Pair<String, Term> p: lstPLocPre) {
        lstTemp.add(p.getFirst());
        // l?:T
        Stroke sk = fac_.createInStroke();
        List<Stroke> lstSk = new ArrayList<Stroke>();
        lstSk.add(sk);
        StrokeList sl = fac_.createZStrokeList(lstSk);
        ZName zn = fac_.createZName(p.getFirst(), sl, null);
        setPLocIn.add(new Pair<ZName, Term>(zn, p.getSecond()));
      }
      // l => l?
      pre.accept(
              new VariableRenamingSchemaVisitor(lstTemp, VariableRenameSchema.VRS_APPEND_INSTROKE));
      
      // 5. replace s by P_s, l by l? and l' by l! in post when l is in the frame. 
      lstStRenPair.clear();
      for(Pair<String, Term> p: lstPStatePost) {
        // (v, P_v)
        // this state is in the frame
//        if(setFrame.contains(p.getFirst())) {
        {
          lstStRenPair.add(new Pair<String, String>(p.getFirst(),
              MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_, p.getFirst())));
        }
      }
      // s => P_s, s' => P_s'
      post.accept(new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_RWT_RENAME, lstStRenPair));
      
      lstTemp.clear();
      for(Pair<String, Term> p: lstPLocPost) {
        lstTemp.add(p.getFirst());
        // l?:T
        Stroke sk = fac_.createInStroke();
        List<Stroke> lstSk = new ArrayList<Stroke>();
        lstSk.add(sk);
        StrokeList sl = fac_.createZStrokeList(lstSk);
        ZName zn = fac_.createZName(p.getFirst(), sl, null);
        
        boolean b = false;
        for(Pair<ZName, Term> pp: setPLocIn) {
          if(pp.getFirst().equals(zn)) {
            b = true;
            break;
          }
        }
        if(b == false) {
          setPLocIn.add(new Pair<ZName, Term>(zn, p.getSecond()));
        }
      }
      // l => l?, l' will not to l?'
      post.accept(
              new VariableRenamingSchemaVisitor(lstTemp, VariableRenameSchema.VRS_APPEND_INSTROKE));

      lstTemp.clear();
      for(Pair<String, Term> p: lstPLocPost) {
        // it is a local variable in the frame, and its after version (v') in used in post
        if(setFrame.contains(p.getFirst()) && setName.contains(p.getFirst() + ZString.PRIME)) {
          lstTemp.add(p.getFirst());
          // l!:T
          Stroke sk = fac_.createOutStroke();
          List<Stroke> lstSk = new ArrayList<Stroke>();
          lstSk.add(sk);
          StrokeList sl = fac_.createZStrokeList(lstSk);
          ZName zn = fac_.createZName(p.getFirst(), sl, null);
          setPLocOut.add(new Pair<ZName, Term>(zn, p.getSecond()));
        }
      }
      
      // l' => l!
      post.accept(
              new VariableRenamingSchemaVisitor(lstTemp, VariableRenameSchema.VRS_NEXT_OUTSTROKE));
      
      // assemble the Z schema
      ZDeclList lstDecl = fac_.createZDeclList();
      // l?:Tl and l!:Tl
      // merge setPLocOut into setPLocIn
      for(Pair<ZName, Term> p: setPLocOut) {
        boolean b = false;
        for(Pair<ZName, Term> pp: setPLocIn) {
          if(p.getFirst().equals(pp.getFirst())) {
            b = true;
            break;
          }
        }
        
        if(b == false) {
          setPLocIn.add(p);
        }
      }
      
      // 
      for(Pair<ZName, Term> p: setPLocIn) {
        // VarDecl
        // create Name List with InStroke
        List<Name> ln = new ArrayList<Name>();
        ln.add(p.getFirst());

        // create Namelist
        NameList nl1 = fac_.createZNameList(ln);
        VarDecl vd = fac_.createVarDecl(nl1, (Expr) (p.getSecond()));
        lstDecl.add(vd);
      }
      
      Pred post2 = post;
      // decl list for exists predicate
      ZDeclList lstDeclEP = fac_.createZDeclList();
      for(Pair<String, Term> p: setPNotInFrame) {
        if(p.getFirst().endsWith(ZString.PRIME)) {
          // VarDecl
          Stroke sk = fac_.createNextStroke();
          List<Stroke> lstSk = new ArrayList<Stroke>();
          lstSk.add(sk);
          StrokeList sl = fac_.createZStrokeList(lstSk);
          ZName zn = fac_.createZName(p.getFirst().replace(ZString.PRIME, ""), sl, null);
          
          // create Name List with InStroke
          List<Name> ln = new ArrayList<Name>();
          ln.add(zn);
  
          // create Namelist
          NameList nl1 = fac_.createZNameList(ln);
          VarDecl vd = fac_.createVarDecl(nl1, (Expr) (p.getSecond()));
          lstDeclEP.add(vd);
        }
      }
      
      if(!lstDeclEP.isEmpty()) {
        DeclList dl = fac_.createZDeclList(lstDeclEP);
        SchText st = fac_.createZSchText(dl, null);
        post2 = fac_.createExistsPred(st, post);
      }
      
      List<Pred> lstPred = new ArrayList<Pred>();
      lstPred.add(pre);
      lstPred.add(post2);
      
      Pred pred = fac_.createAndPred(lstPred, And.Wedge);
      
      // paraName
      String paraName = null;
      AxPara axpara = null;
      if(kind == SpecStmtKind.SPECIFICATION) {
        paraName = MessageFormat.format(
            CSPPredExpPattern.getPattern(PredExpPattern.SPEC_NAME_PATT), para_name_,
            map_.incn());
        
        axpara = assembleZPara(paraName, pred, lstDecl);
        
        // but add another negative precondition schema in the process
        AxPara ap = Circus2ZCSPUtils.NegPreconditionSchema(para_name_, axpara, map_,
            process_para_.getCircusBasicProcess(), zsect_, manager_, sectname_);
        process_para_.getCircusBasicProcess().getZParaList().add(ap);
      }
      else if(kind == SpecStmtKind.ASSUMPTION) {
        paraName = MessageFormat.format(
            CSPPredExpPattern.getPattern(PredExpPattern.ASSUMP_NAME_PATT), para_name_,
            map_.incn());
        axpara = assembleZPara(paraName, pred, lstDecl, false);
        
        // but add another negative precondition schema in the process
        AxPara ap = Circus2ZCSPUtils.NegPreconditionSchema(para_name_, axpara, map_,
            process_para_.getCircusBasicProcess(), zsect_, manager_, sectname_);
        process_para_.getCircusBasicProcess().getZParaList().add(ap);
      }
      else if(kind == SpecStmtKind.COERCION) {
        paraName = MessageFormat.format(
            CSPPredExpPattern.getPattern(PredExpPattern.COERC_NAME_PATT), para_name_,
            map_.incn());
        axpara = assembleZPara(paraName, pred, lstDecl, false);
      }
      
      assert(process_para_.getCircusProcess() instanceof BasicProcess);
      
      process_para_.getCircusBasicProcess().getZParaList().add(axpara);
      
      // create Schema Expr
      RefExpr re = cfac_.createRefExpr(
          fac_.createZName(paraName, fac_.createZStrokeList(), null), 
          cfac_.createZExprList(), false, false);
      SchExprAction sea = cfac_.createSchExprAction(re);
      
      updateParentAction(term, sea);
    }

    return null;
  }

  @Override
  public Object visitIntChoiceProcessIdx(IntChoiceProcessIdx term)
  {

    return null;
  }

  @Override
  public Object visitIntChoiceProcessIte(IntChoiceProcessIte term)
  {
    circus_process_stack_.push(term);
    visit(term.getCircusProcess());
    circus_process_stack_.pop();
    return null;
  }

  @Override
  public Object visitCommunicationType(CommunicationType term)
  {

    return null;
  }

  @Override
  public Object visitAlphabetisedParallelAction(AlphabetisedParallelAction term)
  {

    return null;
  }

  @Override
  public Object visitExtChoiceAction(ExtChoiceAction term)
  {
    if(rewrite_stage_ == 4) {
      if(term.getLeftAction() instanceof MuAction || term.getRightAction() instanceof MuAction) {
        throw new CztException("Recursion as an action in external choice is not supported yet!");
      }
      circus_action_stack_.push(term);
      visit(term.getLeftAction());
      visit(term.getRightAction());
      circus_action_stack_.pop();
      
      mergeAndUpdateRpreOfTerm(term);
    } // end of if(rewrite_stage_ == 4)
    return null;
  }

  @Override
  public Object visitSeqActionIte(SeqActionIte term)
  {
    if(rewrite_stage_ == 4) {
      int nrOfVarDecl = 0;
      for(Decl decl: term.getZDeclList()) {
        if(decl instanceof VarDecl) {
          for(Name name: ((VarDecl)decl).getZNameList()) {
            loc_vars_stack_.push(
                new Pair<String, Term>(
                Circus2ZCSPUtils.termToString(name), ((VarDecl)decl).getExpr()
                ));
            nrOfVarDecl++;
          }
        }
      }

      circus_action_stack_.push(term);
      visit(term.getCircusAction());
      circus_action_stack_.pop();
      
      mergeAndUpdateRpreOfTerm(term);
      
      // update context by removing
      while(nrOfVarDecl > 0) {
        loc_vars_stack_.pop();
        nrOfVarDecl--;
      }
    }
    return null;
  }

  @Override
  public Object visitProcessTransformerPred(ProcessTransformerPred term)
  {

    return null;
  }

  /**
   * 
   * @param p - variable name and its type expression
   */
  private void addStateRetrieveEventToCSP(Pair<String, Expr> p)
  {
    // add additional channel named P_Op_x to new_paralist_
    // Op_x
//    String opName = MessageFormat.format(FormatPattern.STATE_RETR_PARA_NAME_PATT,
//        Circus2ZCSPUtils.termToString(p.getFirst()));
//    // P_Op_x
//    String fullOpName = MessageFormat.format(FormatPattern.RENAMING_IN_PROC,
//        para_name_, opName);
    String fullOpName = p.getFirst();
    List<ZName> lstName = new ArrayList<ZName>();
    lstName.add(fac_.createZName(fullOpName, fac_.createZStrokeList(), null));
    NameList nameList = cfac_.createZNameList(lstName);
    List<NameList> lstNameList = new ArrayList<NameList>();
    lstNameList.add(cfac_.createZNameList());
    lstNameList.add(nameList);
    ChannelDecl cd = cfac_.createChannelDecl(lstNameList, p.getSecond());
    List<Decl> lstDecl = new ArrayList<Decl>();
    lstDecl.add(cd);
    DeclList declList = fac_.createZDeclList(lstDecl);
    ChannelPara cp = cfac_.createChannelPara(declList);
    new_paralist_.add(cp);
    // and visit it to add it to the map_
    visit(cp);
    
    // and it should be hidden from communication
    cspspec_.addHideCSPB(fullOpName);
  }
  
  @Override
  public Object visitBasicProcess(BasicProcess term)
  {
    ZParaList zpl = term.getZParaList();
    switch(rewrite_stage_) {
      case 1:
        for(Para p: zpl) {
          visit(p);
        }
        // remove empty AxPara entries that are marked in visitAxPara
        List<AxPara> lstP = (new ArrayList<AxPara>());
        lstP.add(fac_.createAxPara());
        zpl.removeAll(lstP);
        generic_axpara_in_proc_.clear();
        
        // get initial pred
        set_init_pred_.add(Circus2ZCSPUtils.extractInitSchema(fac_, term, process_para_.getZName()));
        break;
      case 2:
      {
//        visited_state_op_.clear();
        // Start 2nd stage of rewriting: rewrite a basic process
        // add additional state retrieve schemas
        AxPara ap = term.getStatePara();
        
        ZName zn = term.getStateParaZName();
        zn.setWord(zn.getWord().replace("$$", ""));
        // add state paragraph to the map
        map_.addStatPara(para_name_, Circus2ZCSPUtils.termToString(term.getStateParaZName()));
        
        DeclListExpansionVisitor dlevisitor = new DeclListExpansionVisitor(term, zsect_, manager_, sectname_);
        ap.accept(dlevisitor);
        Set<Pair<ZName, Expr>> lstZNameExpr = dlevisitor.getNameExprPair();
        ZName name = term.getStateParaZName();
        
        for(Pair<ZName, Expr> p: lstZNameExpr) {
          AxPara stPara = assembleZStateRetrPara(Circus2ZCSPUtils.termToString(name), p);
          // annotations of new paragraph is a copy of state paragraph.
          Circus2ZCSPUtils.cloneAnns(ap, stPara);
          zpl.add(stPara);
          
          // add additional channel named P_Op_x to new_paralist_
          // Op_x
          String opName = MessageFormat.format(FormatPattern.STATE_RETR_PARA_NAME_PATT,
              Circus2ZCSPUtils.termToString(p.getFirst()));
          // P_Op_x
          String fullOpName = MessageFormat.format(FormatPattern.RENAMING_IN_PROC,
              para_name_, opName);
          visited_state_op_.put(fullOpName, new Pair<Expr, Boolean>(p.getSecond(), Boolean.FALSE));

//          List<ZName> lstName = new ArrayList<ZName>();
//          lstName.add(fac_.createZName(fullOpName, fac_.createZStrokeList(), null));
//          NameList nameList = cfac_.createZNameList(lstName);
//          List<NameList> lstNameList = new ArrayList<NameList>();
//          lstNameList.add(cfac_.createZNameList());
//          lstNameList.add(nameList);
//          ChannelDecl cd = cfac_.createChannelDecl(lstNameList, p.getSecond());
//          List<Decl> lstDecl = new ArrayList<Decl>();
//          lstDecl.add(cd);
//          DeclList declList = fac_.createZDeclList(lstDecl);
//          ChannelPara cp = cfac_.createChannelPara(declList);
//          new_paralist_.add(cp);
//          // and visit it to add it to the map_
//          visit(cp);
//          
//          // and it should be hidden from communication
//          cspspec_.addHideCSPB(fullOpName);
          
          // add to map
          map_.addStat(para_name_, Circus2ZCSPUtils.termToString(p.getFirst()), p.getSecond());
        }
        
        term.setParaList(zpl);
        // simple schema or schema calculus?
  /*      if(ZUtils.isSimpleSchema(ap)) {
          Expr expr = ZUtils.getSchemaDefExpr(ap);
          assert(expr instanceof SchExpr);
          
  //        ZDeclList zdl = ((SchExpr)expr).getZSchText().getZDeclList();
          // a list of pair from variable name to its type expression 
          List<Pair<ZName, Expr>> lstZNameExpr = getDeclList(ap);
          ZName name = term.getStateParaZName();
          
          for(Pair<ZName, Expr> p: lstZNameExpr) {
            AxPara stPara = assembleZStateRetrPara(Circus2ZCSPUtils.termToString(name), p);
            zpl.add(stPara);
          }
          
          term.setParaList(zpl);
        }
        else if(ZUtils.isAbbreviation(ap)){
  //        Expr expr = ((ConstDecl)ap.getZSchText().getZDeclList().get(0)).getExpr();
  //        SchExpr schExpr = expansionSchema(expr);
  //        if(expr instanceof AndExpr) {
  //          Term t = TestUtils.unfold(manager_, sectname_, expr);
  //        }
          DeclListExpansionVisitor dlevisitor = new DeclListExpansionVisitor(term, manager_, sectname_);
          ap.accept(dlevisitor);
          List<Pair<ZName, Expr>> lstZNameExpr = dlevisitor.getNameExprPair();
          ZName name = term.getStateParaZName();
          
          for(Pair<ZName, Expr> p: lstZNameExpr) {
            AxPara stPara = assembleZStateRetrPara(Circus2ZCSPUtils.termToString(name), p);
            zpl.add(stPara);
          }
          
          term.setParaList(zpl);
        }*/
        }
        break;
      case 3:
        // Stage 3: renaming
        // get all state components within BasicProcess
        AxPara ap = term.getStatePara();
        DeclListExpansionVisitor dlevisitor = new DeclListExpansionVisitor(term, zsect_, manager_, sectname_);
        ap.accept(dlevisitor);
        Set<Pair<ZName, Expr>> lstZNameExpr = dlevisitor.getNameExprPair();
        
        // if a state paragraph has no state component, it is possibly that it is a On-the-fly paragraph.
        // so we rename it to state paragraph and add a dummy state [v:\{0\} | true]
        ZName zn = term.getStateParaZName();
        String stName = Circus2ZCSPUtils.termToString(zn);
//        if(stName.contains("$$default")) {
          if(lstZNameExpr.isEmpty()) {
            if(ZUtils.isAxParaSchemaOrHorizDefValid(ap)) {
              ConstDecl cdecl = (ConstDecl)ap.getZSchText().getZDeclList().get(0);
              cdecl.setName(fac_.createZName(FormatPattern.DUMMY_STATE_PARA_NAME_PATT,
                 fac_.createZStrokeList(), null));
              // construct a dummy state paragraph
              ZDeclList declList = fac_.createZDeclList();
              List<ZName> lstZName = new ArrayList<ZName>();
              ZName dummyStName = fac_.createZName(FormatPattern.DUMMY_STATE_COMP_PATT, 
                  fac_.createZStrokeList(), null);
              lstZName.add(dummyStName);
              ZNameList znl = fac_.createZNameList(lstZName);
              NumExpr ne = fac_.createNumExpr(fac_.createZNumeral(BigInteger.ZERO));
              List<Expr> lstExpr = new ArrayList<Expr>(); lstExpr.add(ne);
              SetExpr se = fac_.createSetExpr(fac_.createZExprList(lstExpr));
              VarDecl vd = fac_.createVarDecl(znl, se); declList.add(vd);
              ZSchText schText = fac_.createZSchText(declList, fac_.createTruePred());
              SchExpr schExpr = fac_.createSchExpr(schText);
              cdecl.setExpr(schExpr);
              
              lstZNameExpr.add(new Pair<ZName, Expr>(dummyStName, se));
            }
//          }
//          else {
////            term.getStatePara();
//            zn.setWord(stName.replace("$$", ""));
//          }
        }
        
        // a list map for state components
        List<Pair<String, String>> vlist = new ArrayList<Pair<String, String>>();
        for(Pair<ZName, Expr> p: lstZNameExpr) {
          String name = Circus2ZCSPUtils.termToString(p.getFirst());
          // (v, P_v)
          vlist.add(new Pair<String, String>(name, 
              MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_, name)));
        }
        
        // a list map for paragraphs [(state, P_state), (Init, P_Init), ...]
        List<Pair<String, String>> plist = new ArrayList<Pair<String, String>>();
        for(Para p: zpl) {
          Name pname = null;
          if(p instanceof AxPara) {
            // P == P1 \land P2
            if(ZUtils.isAbbreviation(p)) {
              pname = ZUtils.getAbbreviationName(p);
            }
            // is simple schema
            // horizontal or boxed schema
            else if(ZUtils.isSimpleSchema(p)) {
              pname = ZUtils.getSchemaName(p);
            }
  //          ZUtils.getSpecialSchemaBaseName();
          }
          else if(p instanceof ActionPara) {
            pname = ((ActionPara)p).getName();
          }
          
          if(pname != null) {
            String name = Circus2ZCSPUtils.termToString(pname);
            plist.add(new Pair<String, String>(name, 
                MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_, name)));
          }
        }
        
        List<Pair<String, String>> pvlist = new ArrayList<Pair<String, String>>();
        pvlist.addAll(vlist);
        pvlist.addAll(plist);
        for(Para p: zpl) {
          if(p instanceof AxPara) {
            VariableRenamingSchemaVisitor vrsv = 
                new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_RWT_RENAME, pvlist);
            p.accept(vrsv);
          }
          else if(p instanceof ActionPara) {
            // state components are not renamed
            VariableRenamingSchemaVisitor vrsv = 
                new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_RWT_RENAME, plist);
            // for the main action, just rename the action itself and not the ActionPara
            if(((ActionPara) p).getCircusAction().equals(term.getMainAction())) {
              term.getMainAction().accept(vrsv);
            } 
            else {
              p.accept(vrsv);
            }
          }
        }
        break;
      case 4:
        // Stage 4: action rewrite
        // add additional Negative precondition schema for each operational schema in the process
        visit(term.getMainAction());
        break;
      default:
        break;
    }
    return null;
  }

  @Override
  public Object visitZSignatureList(ZSignatureList term)
  {

    return null;
  }

  @Override
  public Object visitLetVarAction(LetVarAction term)
  {
    visit(term.getZDeclList());
    visit(term.getZExprList());
    visit(term.getCircusAction());
    return null;
  }

  @Override
  public Object visitAssignmentPairs(AssignmentPairs term)
  {
    visit(term.getZLHS());
    visit(term.getZRHS());
    return null;
  }

  @Override
  public Object visitOnTheFlyDefAnn(OnTheFlyDefAnn term)
  {

    return null;
  }

  @Override
  public Object visitNameSetType(NameSetType term)
  {

    return null;
  }

  @Override
  public Object visitParallelProcessIdx(ParallelProcessIdx term)
  {

    return null;
  }

  @Override
  public Object visitLetMuAction(LetMuAction term)
  {

    return null;
  }

  @Override
  public Object visitChannelPara(ChannelPara term)
  {
    ZDeclList dl = term.getZDeclList();

    // declaration list after rewrite
    ZDeclList dl2 = fac_.createZDeclList();
//    dl2.addAll(dl);
    
    // 1. for schema grouped channel, we rewrite it first.
    for(Decl decl: dl) {
      if (decl instanceof ChannelDecl) {
        ChannelDecl cd = (ChannelDecl) decl;
        /*
         * For schema: channelfrom, the namelist is empty
         * It is rewritten to general channel declaration
         */
        if (cd.getZChannelNameList().isEmpty()) {
          /* the expr should be RefExpr */
          if (cd.getExpr() instanceof RefExpr) {
            /* get the schema expr referred by this RefExpr and expand it */
            RefExpr re = (RefExpr) cd.getExpr();
            String sch_name = re.getZName().accept(new net.sourceforge.czt.z.util.PrintVisitor());
            // get the definition of sch_name
            DefinitionTable.Definition def = deftable_.lookup(sch_name);
            // Added distinction with CONSTDECL, for compatibility with old DefinitionTable (Leo)
            if (def == null || !def.getDefinitionType().equals(DefinitionType.CONSTDECL)) {
              CztException ex = new CztException("Cannot find the definition of schema name: "
                  + sch_name);
              throw ex;
            }

            // get the schema expression of sch_name
            Expr expr_sch = def.getExpr();
            if (expr_sch == null) {
              CztException ex = new CztException("Invalid expression for schema: " + sch_name);
              throw ex;
            }

            if (!(expr_sch instanceof SchExpr)) {
              CztException ex = new CztException("Invalid expression for schema: " + sch_name
                  + ". Expect SchExpr but it's " + expr_sch.getClass().getName());
              throw ex;
            }

            // Unfold this schema (including normalisation and expansion)
            assert (expr_sch instanceof SchExpr);
            // TODO: actually we expect no normalisation
            SchExpr rewritten_sch = unfold((SchExpr) expr_sch);

            ZDeclList zdl = rewritten_sch.getZSchText().getZDeclList();

            for (Decl del : zdl) {
              if (del instanceof VarDecl) {
                ZNameList znl = ((VarDecl) del).getZNameList();
                Expr e = ((VarDecl) del).getExpr();
                ChannelDecl cdecl;
                if (e == null) {
                  cdecl = assembleChannelDecl(znl);
                }
                else {
                  cdecl = assembleChannelDecl(znl, e);
                }
                List<Object> lo = cdecl.getAnns();
                if(term.hasAnn()) {
                  lo.addAll(cd.getAnns());
                }
                dl.add(cdecl);
                dl2.add(cdecl);
              }
              else {
                CztException ex = new CztException(
                    "The variable declaration in a schema that groups channel declarations should be VarDecl but it is "
                        + del.getClass().getName());
                throw ex;
              }
            }
          }
          // remove original channelfrom
          dl.remove(decl);
        }
        /* a common channel declaration*/
        else {
          ZNameList channels = cd.getZChannelNameList();
          // generic parameters
          ZNameList formals = cd.getZGenFormals();
          if(!formals.isEmpty()) {
            // generic channels
            // add to the global list and remove from the final paragraph list
            generic_channel_decl_.add(cd);
            if(new_paralist_.contains(term)) {
              new_paralist_.remove(term);
            }
            
            dl2.remove(decl);
          }
          else {
            dl2.add(decl);
          }
        }
      }
    }

    // 2. visit all channel declarations
    for (Decl decl : dl2) {
      assert (decl instanceof ChannelDecl);
      visit(decl);
    }

    return null;
  }

  /**
   * assemble a channel declaration (SYNC type)
   * 
   * @param chnname
   * @param type
   * @return
   */
  private ChannelDecl assembleChannelDecl(String chnname)
  {

    java.util.List<net.sourceforge.czt.z.ast.NameList> nameList = new java.util.Vector<net.sourceforge.czt.z.ast.NameList>();
    // add a dummy namelist, otherwise error reported
    NameList nl1 = fac_.createZNameList();
    nameList.add(nl1);
    //
    List<Name> ln = new ArrayList<Name>();
    Name name = fac_.createZName(chnname, fac_.createZStrokeList(), null);
    ln.add(name);
    NameList nl2 = fac_.createZNameList(ln);
    nameList.add(nl2);

    Expr expr = fac_.createRefExpr(
        fac_.createZName(CircusString.CIRCUSSYNCH, fac_.createZStrokeList(), null),
        fac_.createZExprList(), false, false);
    ChannelDecl cd = cfac_.createChannelDecl(nameList, expr);
    return cd;
  }

  /**
   * assemble a channel declaration (SYNC type)
   * 
   * @param chnname
   * @param type
   * @return
   */
  private ChannelDecl assembleChannelDecl(ZNameList znl)
  {

    java.util.List<net.sourceforge.czt.z.ast.NameList> nameList = new java.util.Vector<net.sourceforge.czt.z.ast.NameList>();
    // add a dummy namelist, otherwise error reported
    NameList nl1 = fac_.createZNameList();
    nameList.add(nl1);
    //
    nameList.add(znl);

    Expr expr = fac_.createRefExpr(
        fac_.createZName(CircusString.CIRCUSSYNCH, fac_.createZStrokeList(), null),
        fac_.createZExprList(), false, false);
    ChannelDecl cd = cfac_.createChannelDecl(nameList, expr);
    return cd;
  }

  /**
   * assemble a channel declaration
   * 
   * @param chnname
   * @param type
   * @return
   */
  private ChannelDecl assembleChannelDecl(String chnname, Term type)
  {
    assert (type != null);

    java.util.List<net.sourceforge.czt.z.ast.NameList> nameList = new java.util.Vector<net.sourceforge.czt.z.ast.NameList>();
    // add a dummy namelist, otherwise error reported
    NameList nl1 = fac_.createZNameList();
    nameList.add(nl1);
    //
    List<Name> ln = new ArrayList<Name>();
    Name name = fac_.createZName(chnname, fac_.createZStrokeList(), null);
    ln.add(name);
    NameList nl2 = fac_.createZNameList(ln);
    nameList.add(nl2);
    ChannelDecl cd = cfac_.createChannelDecl(nameList, (Expr) type);
    return cd;
  }

  /**
   * assemble a channel declaration
   * 
   * @param chnname
   * @param type
   * @return
   */
  private ChannelDecl assembleChannelDecl(ZNameList znl, Term type)
  {
    assert (type != null);

    java.util.List<net.sourceforge.czt.z.ast.NameList> nameList = new java.util.Vector<net.sourceforge.czt.z.ast.NameList>();
    // add a dummy namelist, otherwise error reported
    NameList nl1 = fac_.createZNameList();
    nameList.add(nl1);
    //
    nameList.add(znl);
    ChannelDecl cd = cfac_.createChannelDecl(nameList, (Expr) type);
    return cd;
  }

  @Override
  public Object visitNameSetPara(NameSetPara term)
  {
    visit(term.getZName());
    visit(term.getNameSet());
    return null;
  }

  @Override
  public Object visitDoGuardedCommand(DoGuardedCommand term)
  {

    return null;
  }

  @Override
  public Object visitCircusNameSet(CircusNameSet term)
  {
    visit(term.getExpr());
    return null;
  }

  @Override
  public Object visitExtChoiceProcessIdx(ExtChoiceProcessIdx term)
  {

    return null;
  }

  @Override
  public Object visitParallelActionIte(ParallelActionIte term)
  {
    if(rewrite_stage_ == 4) {
      int nrOfVarDecl = 0;
      for(Decl decl: term.getZDeclList()) {
        if(decl instanceof VarDecl) {
          for(Name name: ((VarDecl)decl).getZNameList()) {
            loc_vars_stack_.push(
                new Pair<String, Term>(
                Circus2ZCSPUtils.termToString(name), ((VarDecl)decl).getExpr()
                ));
            nrOfVarDecl++;
          }
        }
      }

      circus_action_stack_.push(term);
      visit(term.getCircusAction());
      circus_action_stack_.pop();
      
      mergeAndUpdateRpreOfTerm(term);
      
      // update context by removing
      while(nrOfVarDecl > 0) {
        loc_vars_stack_.pop();
        nrOfVarDecl--;
      }
    }
    return null;
  }

  @Override
  public Object visitProcessType(ProcessType term)
  {

    return null;
  }

  @Override
  public Object visitChannelSetType(ChannelSetType term)
  {

    return null;
  }

  @Override
  public Object visitChaosAction(ChaosAction term)
  {
    if(rewrite_stage_ == 4) {
      
    }
    return null;
  }

  @Override
  public Object visitProcessSignature(ProcessSignature term)
  {

    return null;
  }

  @Override
  public Object visitRenameAction(RenameAction term)
  {
    visit(term.getAssignmentPairs());
    visit(term.getCircusAction());
    return null;
  }

  @Override
  public Object visitProofObligationAnn(ProofObligationAnn term)
  {

    return null;
  }

  @Override
  public Object visitHideProcess(HideProcess term)
  {
    circus_process_stack_.push(term);
    visit(term.getCircusProcess());
    visit(term.getChannelSet());
    circus_process_stack_.pop();
    return null;
  }

  @Override
  public Object visitSeqProcess(SeqProcess term)
  {
    circus_process_stack_.push(term);
    visit(term.getLeftProcess());
    visit(term.getRightProcess());
    circus_process_stack_.pop();
    return null;
  }

  @Override
  public Object visitCircusChannelSetList(CircusChannelSetList term)
  {
    for(ChannelSet c: term.getChannelSet()) {
      visit(c);
    }
    return null;
  }

  @Override
  public Object visitIntChoiceActionIte(IntChoiceActionIte term)
  {
    if(rewrite_stage_ == 4) {
      int nrOfVarDecl = 0;
      for(Decl decl: term.getZDeclList()) {
        if(decl instanceof VarDecl) {
          for(Name name: ((VarDecl)decl).getZNameList()) {
            loc_vars_stack_.push(
                new Pair<String, Term>(
                Circus2ZCSPUtils.termToString(name), ((VarDecl)decl).getExpr()
                ));
            nrOfVarDecl++;
          }
        }
      }

      circus_action_stack_.push(term);
      visit(term.getCircusAction());
      circus_action_stack_.pop();
      
      mergeAndUpdateRpreOfTerm(term);
      
      // update context by removing
      while(nrOfVarDecl > 0) {
        loc_vars_stack_.pop();
        nrOfVarDecl--;
      }

    }
    return null;
  }

  @Override
  public Object visitProcessSignatureAnn(ProcessSignatureAnn term)
  {

    return null;
  }

  @Override
  public Object visitActionTransformerPred(ActionTransformerPred term)
  {

    return null;
  }

  @Override
  public Object visitSigmaExpr(SigmaExpr term)
  {

    return null;
  }

  @Override
  public Object visitExtChoiceProcess(ExtChoiceProcess term)
  {
    circus_process_stack_.push(term);
    visit(term.getLeftProcess());
    visit(term.getRightProcess());
    circus_process_stack_.pop();
    return null;
  }

  @Override
  public Object visitStateUpdateAnn(StateUpdateAnn term)
  {

    return null;
  }

  @Override
  public Object visitSeqAction(SeqAction term)
  {
    if(rewrite_stage_ == 4) {
      circus_action_stack_.push(term);
      visit(term.getLeftAction());
      visit(term.getRightAction());
      circus_action_stack_.pop();
    }
    return null;
  }

  @Override
  public Object visitRenameProcess(RenameProcess term)
  {
    // For rename process, we limit it to
    // 1. P[c:=d] where P is BasicProcess (EDP)
    // 2. (i:T \circindex P)[c := d] -- indexed process where P is EDP
    // 3. possibly parametrised process???
    RenameProcess rp = term;

    AssignmentPairs ap = rp.getAssignmentPairs();
    List<Pair<String, String>> lps = new ArrayList<Pair<String, String>>();
    
    for(int i = 0; i < ap.getZLHS().size(); i++) {
      Name zn = ap.getZLHS().get(i);
      Expr expr = ap.getZRHS().get(i);
      lps.add(new Pair<String, String>(Circus2ZCSPUtils.termToString(zn), Circus2ZCSPUtils.termToString(expr)));
    }
    
    // 1. 
    if (rp.getCircusProcess() instanceof CallProcess) {
      CallProcess cp = (CallProcess)rp.getCircusProcess();
      // 
      if (cp.getZActuals().isEmpty()) {
        if (cp.getCallExpr() instanceof RefExpr) {
          String cname = Circus2ZCSPUtils.termToString((RefExpr)cp.getCallExpr());
          
          // get the definition of basic process and it can not be got from definition table
          for(Para p: paralist_) {
            if(p instanceof ProcessPara) {
              if(Circus2ZCSPUtils.termToString(((ProcessPara)p).getZName()).equals(cname)) {
                if(((ProcessPara)p).getCircusProcess() instanceof BasicProcess) {
                  BasicProcess bp = ZUtils.cloneTerm(((ProcessPara)p).getCircusBasicProcess());
//                  rp.setCircusProcess(bp1);
                  if(!lps.isEmpty()) {
                    bp.accept(new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_NAME_REPLACE, lps));
                  }
                  
                  ProcessPara new_pp = cfac_.createProcessPara(
                      fac_.createZName(para_name_, fac_.createZStrokeList(), null), 
                      fac_.createZNameList(), 
                      bp);
                  
                  List<Object> lo = new_pp.getAnns();
                  if(list_ann_ != null) {
                    lo.addAll(list_ann_);
                  }
                  new_paralist_.add(new_pp);
                }
                else {
                  throw new CztException("Invalid Class [" + ((ProcessPara)p).getCircusProcess().getClass().getName() + 
                      "] for CallProcess of Renamed process. Expected BasicProcess!");
                }
                break;
              }
            }
          }
        } 
        else {
          throw new CztException("Invalid Expr [" + cp.getCallExpr().getClass().getName() + 
              "] for CallProcess of Renamed process. Expected RefExpr!");
        }
      }
      else {
        throw new CztException("Invalid number of parameters [" + cp.getZActuals().size() +
            "] for CallProcess of Renamed process. Expected 0!");
      }
    } else if (rp.getCircusProcess() instanceof BasicProcess) {
      BasicProcess bp = (BasicProcess)ZUtils.cloneTerm(rp.getCircusProcess());
      if(!lps.isEmpty()) {
        bp.accept(new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_NAME_REPLACE, lps));
      }
      
      ProcessPara new_pp = cfac_.createProcessPara(
          fac_.createZName(para_name_, fac_.createZStrokeList(), null), 
          fac_.createZNameList(), 
          bp);
      
      List<Object> lo = new_pp.getAnns();
      if(list_ann_ != null) {
        lo.addAll(list_ann_);
      }
      new_paralist_.add(new_pp);
    }
    // 2. 
    else if (rp.getCircusProcess() instanceof IndexedProcess) {
      // If it is an anonymous indexed process
      // it is rewritten to a set of ParaProcess name with index
      Object ob = visit(rp.getCircusProcess());
      if(ob != null && ob instanceof Set<?>) {
        Set<ProcessPara> spp = (Set<ProcessPara>)ob;
        for(ProcessPara pp: spp) {
          if(! (pp.getCircusProcess() instanceof BasicProcess)) {
            throw new CztException("Invalid Class " + pp.getCircusProcess().getClass().getName() + 
                " for indexed process. Expected BasicProcess!");
          }
          
          if(!lps.isEmpty()) {
            pp.getCircusProcess().accept(new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_NAME_REPLACE, lps));
          }
        }
      }
    } 
    else {
      throw new CztException("Invalid Class [" + rp.getCircusProcess().getClass().getName() + 
          "] for Renamed process. Expected BasicProcess or CallProcess or IndexProcess");
    }

    return null;
  }

  @Override
  public Object visitActionSignatureAnn(ActionSignatureAnn term)
  {

    return null;
  }

  @Override
  public Object visitProcessSignatureList(ProcessSignatureList term)
  {

    return null;
  }

  @Override
  public Object visitCircusActionList(CircusActionList term)
  {
    /*if(rewrite_stage_ == 1) */ {
      for(CircusAction ca: term) {
        visit(ca);
      }
    }

    return null;
  }

  @Override
  public Object visitInterruptAction(InterruptAction term)
  {

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

  @Override
  public Object visitListTerm(ListTerm<?> listTerm)
  {
    for (Object o : listTerm) {
      if (o instanceof Term) {
        visit((Term) o);
      }
    }
    return null;
  }

  @Override
  public Object visitOrPred(OrPred term)
  {
    visit(term.getLeftPred());
    visit(term.getRightPred());
    return null;
  }

  @Override
  public Object visitPowerType(PowerType term)
  {

    return null;
  }

  @Override
  public Object visitConstDecl(ConstDecl term)
  {
    visit(term.getZName());
    visit(term.getExpr());
    return null;
  }

  @Override
  public Object visitOperator(Operator term)
  {

    return null;
  }

  @Override
  public Object visitTupleSelExpr(TupleSelExpr term)
  {
    visit(term.getExpr());
    return null;
  }

  @Override
  public Object visitUnparsedZSect(UnparsedZSect term)
  {

    return null;
  }

  @Override
  public Object visitInclDecl(InclDecl term)
  {
    visit(term.getExpr());
    return null;
  }

  @Override
  public Object visitImpliesPred(ImpliesPred term)
  {
    visit(term.getLeftPred());
    visit(term.getRightPred());

    return null;
  }

  @Override
  public Object visitExistsPred(ExistsPred term)
  {
    visit(term.getPred());
    visit(term.getZSchText());
    return null;
  }

  @Override
  public Object visitZNumeral(ZNumeral term)
  {

    return null;
  }

  @Override
  public Object visitZFreetypeList(ZFreetypeList term)
  {

    return null;
  }

  @Override
  public Object visitAndPred(AndPred term)
  {
    visit(term.getLeftPred());
    visit(term.getRightPred());

    return null;
  }

  @Override
  public Object visitParent(Parent term)
  {

    return null;
  }

  @Override
  public Object visitAxPara(AxPara term)
  {
    switch(rewrite_stage_) {
      case 1:
        ZNameList znl = ZUtils.getAxParaZGenFormals(term);
        if(znl != null && !znl.isEmpty()) {
          // Generic definition
          // just remove it from the paraList_
          String formals = "";
          for(Name n: znl) {
            // the generic formals
            formals += Circus2ZCSPUtils.termToString(n) + ", ";
          }
          
          if(ZUtils.isAxParaSchemaOrHorizDefValid(term)) {
            Debug.debug_print(
                Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
                Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
                Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
                "Generic definition of " + 
                Circus2ZCSPUtils.termToString(ZUtils.getAxParaSchOrAbbrName(term)) +
                " has formals: [" + formals + "].");
          }
          else if(ZUtils.getAxBoxDecls(term) != null) {
            ZDeclList zdl = ZUtils.getAxBoxDecls(term);
            String var = "";
            for(Decl decl: zdl) {
              if(decl instanceof VarDecl) {
                for(Name n: ((VarDecl)decl).getZNameList()) {
                  var += Circus2ZCSPUtils.termToString(n) + ", ";
                }
              }
            }
            Debug.debug_print(
                Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
                Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
                Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
                "Generic definition of Axiomatic (" + var +
                ") has formals: [" + formals + "].");
          }
          
          // in case it is a global AxPara
          if(process_para_ == null) {
            if(new_paralist_.contains(term)) {
              new_paralist_.remove(term);
            }
            generic_axpara_global_.add(term);
          }
          else {
            // in case it is a AxPara in a process
            // get current basic processes
            assert(process_para_.getCircusProcess() instanceof BasicProcess);
            
            ZParaList zpl = process_para_.getCircusBasicProcess().getZParaList();
            if(zpl.contains(term)) {
              generic_axpara_in_proc_.add(term);
              // don't remove but just mark it as empty AxPara
              int ind = zpl.indexOf(term);
              zpl.set(ind, fac_.createAxPara());
    //          zpl.remove(term);
            }
          }
          
          return null;
        }
    
        // for Axiomatic definition, if there is a constant configured in configuration file
        // we add additional constrain on it
        if(ZUtils.getAxBoxDecls(term) != null) {
          // Axiomatic definition
          ZDeclList zdl = ZUtils.getAxBoxDecls(term);
          Pred pred = ZUtils.getAxBoxPred(term);
    
          for(Decl decl: zdl) {
            if(decl instanceof VarDecl) {
              for(Name n: ((VarDecl)decl).getZNameList()) {
                String name = Circus2ZCSPUtils.termToString(n);
                String value = config_.getConfig(name);
                if(((VarDecl)decl).getExpr() instanceof RefExpr) {
                  String expr = Circus2ZCSPUtils.termToString(((VarDecl)decl).getExpr());
                  // TODO: how to check if the given value is valid or not
                  // here we only support axiomatic definition of number
                  if(/*(expr.equals(ZString.NAT + ZString.SUB1) || expr.equals(ZString.NAT)) &&*/ 
                      (value != null && value.matches("[0-9]+"))) {
                    RefExpr re = fac_.createRefExpr(n, fac_.createZExprList(), false, false);
                    NumExpr ne = fac_.createNumExpr(fac_.createZNumeral(new BigInteger(value)));
                    List<Expr> lstExpr = new ArrayList<Expr>();
                    lstExpr.add(ne);
                    SetExpr se = fac_.createSetExpr(fac_.createZExprList(lstExpr));
                    lstExpr.clear();
                    lstExpr.add(re);
                    lstExpr.add(se);
                    // name = value
                    MemPred mp = fac_.createMemPred(lstExpr, true);
                    if(pred == null) {
                      pred = mp;
                    }
                    else {
                      List<Pred> lstPred = new ArrayList<Pred>();
                      lstPred.add(pred);
                      lstPred.add(mp);
                      pred = fac_.createAndPred(lstPred, And.NL);
                    }
                  }
                }
              }
            }
          }
          
          if(pred != null && !pred.equals(ZUtils.getAxBoxPred(term))) {
            term.getZSchText().setPred(pred);
          }
          
          visit(zdl);
          visit(pred);
        }
        else if(ZUtils.isAbbreviation(term)){
          // Normal definition
          Name name = ZUtils.getAbbreviationName(term);
          visit(name);
          Expr expr = ZUtils.getAbbreviationExpr(term);
          visit(expr);
        }
        else if(ZUtils.isSimpleSchema(term)) {
          Name name = ZUtils.getSchemaName(term);
          visit(name);
          Expr expr = ZUtils.getSchemaDefExpr(term);
          visit(expr);
        }
        else {
          throw new CztException("Unknow AxPara: " + term.getClass().getName());
        }
        break;
      case 2:
      case 3:
      case 4:
      default:
        break;
    }
    
    return null;
  }

  @Override
  public Object visitTypeAnn(TypeAnn term)
  {

    return null;
  }

  @Override
  public Object visitFalsePred(FalsePred term)
  {

    return null;
  }

  @Override
  public Object visitOrExpr(OrExpr term)
  {
    visit(term.getLeftExpr());
    visit(term.getRightExpr());

    return null;
  }

  @Override
  public Object visitZBranchList(ZBranchList term)
  {
    for(Branch b: term.getBranch()) {
      visit(b);
    }
    return null;
  }

  @Override
  public Object visitParenAnn(ParenAnn term)
  {

    return null;
  }

  @Override
  public Object visitZName(ZName term)
  {
    return null;
  }

  @Override
  public Object visitNarrSect(NarrSect term)
  {
    return null;
  }

  @Override
  public Object visitBranch(Branch term)
  {
    term.getZName();
    term.getExpr();
    return null;
  }

  @Override
  public Object visitExistsExpr(ExistsExpr term)
  {
    visit(term.getExpr());
    visit(term.getZSchText());
    return null;
  }

  @Override
  public Object visitDecorExpr(DecorExpr term)
  {
    visit(term.getExpr());
    visit(term.getStroke());
    return null;
  }

  @Override
  public Object visitPowerExpr(PowerExpr term)
  {
    visit(term.getExpr());
    return null;
  }

  @Override
  public Object visitZRenameList(ZRenameList term)
  {
    for(NewOldPair n: term.getNewOldPair()) {
      visit(n);
    }
    return null;
  }

  @Override
  public Object visitFreePara(FreePara term)
  {
    if(rewrite_stage_ == 1) {
      for(Freetype fp: (ZFreetypeList)(term.getFreetypeList())) {
        String fpName = Circus2ZCSPUtils.termToString(fp.getZName());
        
        // add this freetype to map_
        map_.addFreeType(fpName, 
            Circus2ZCSPUtils.termToString(fp.getBranchList()), 
            fp.getBranchList());
      }
    }
    return null;
  }

  @Override
  public Object visitAndExpr(AndExpr term)
  {
    visit(term.getLeftExpr());
    visit(term.getRightExpr());
    return null;
  }

  @Override
  public Object visitTruePred(TruePred term)
  {

    return null;
  }

  @Override
  public Object visitUnparsedPara(UnparsedPara term)
  {

    return null;
  }

  @Override
  public Object visitNameTypePair(NameTypePair term)
  {

    return null;
  }

  @Override
  public Object visitOperand(Operand term)
  {

    return null;
  }

  @Override
  public Object visitRefExpr(RefExpr term)
  {
    ZExprList zel = term.getZExprList();
    ZName name = term.getZName();
    String delxi = null;
    
    RefExprKind kind = Circus2ZCSPUtils.getRefExprKind(term);
    switch(kind) {
      case GEN_OP_APPL:
        break;
      case OP_APPL:
        break;
      case GEN_REF:
        // At first, we check if there is a '\Delta Name[Paras]' or '\Xi Name[Paras]'
        if(ZUtils.isDeltaXi(name)) {
          if(ZUtils.isDelta(name)) {
            // remove Delta or Xi from the term
            name.setWord(name.getWord().replace(ZString.DELTA, ""));
            term.setName(name);
            delxi = ZString.DELTA;
          }
          else {
            // remove Delta or Xi from the term
            name.setWord(name.getWord().replace(ZString.XI, ""));
            term.setName(name);
            delxi = ZString.XI;
          }
        }
        
        // try to get from the map at first
        Iterator<Map.Entry<RefExpr, RefExpr>> it = map_generic_refexpr_.entrySet().iterator();
        while (it.hasNext()) {
            Map.Entry<RefExpr, RefExpr> pair = (Map.Entry<RefExpr, RefExpr>)it.next();
            // we should ignore the check of id in ZName of RefExpr
            RefExpr re1 = ZUtils.cloneTerm(term);
            re1.getZName().setId(null);
            
            RefExpr re2 = ZUtils.cloneTerm(pair.getKey());
            re2.getZName().setId(null);
            
            if(re1.equals(re2)) {
              Circus2ZCSPUtils.updateParentRef(stack_parent_, term, (Expr) pair.getValue());
              return null;
            }
            it.remove(); // avoids a ConcurrentModificationException
        }
//        if(map_generic_refexpr_.get(term) != null) {
//          updateParentRef(term, map_generic_refexpr_.get(term));
//          return null;
//        }
        
        // generic reference
        /*
         * 1. generic definition: axdef and schema
         */
        ZNameList znl = fac_.createZNameList();
        
        List<AxPara> tempAxPara = new ArrayList<AxPara>();
        tempAxPara.addAll(generic_axpara_global_);
        tempAxPara.addAll(generic_axpara_in_proc_);
        
        // 1. check global and local AxPara at first
        for(AxPara ap: tempAxPara) {
          AxParaKind apkind = Circus2ZCSPUtils.getAxParaKind(ap);
          ZNameList formals = ap.getZNameList();
          List<ZName> lstName = new ArrayList<ZName>();
          List<Expr> lstExpr = new ArrayList<Expr>();

          switch(apkind) {
//            case AXDEF:
            case GEN_AXDEF: //
              ZDeclList zdl = ZUtils.getAxBoxDecls(ap);
              Pred pred = ZUtils.getAxBoxPred(ap);
              boolean found = false;
              
              for(Decl decl: zdl) {
                if(decl instanceof VarDecl) {
                  VarDecl vd = (VarDecl)decl;
                  for(Name vn: vd.getZNameList()) {
                    if(vn.equals(name)) {
                      // found the AxBox definition
                      found = true;
                      break;
                    }
                  }
                }
              }
              
              // if we find the global variable or constant in ap
              if(found) {
                for(int i = 0; i < formals.size(); i++) {
                  lstName.add((ZName) formals.get(i));
                  lstExpr.add(zel.get(i));
                }
  
                // replace the formals by its parameters
                AxPara tempAp = ZUtils.cloneTerm(ap);
                // set formals to empty
                tempAp.setNameList(fac_.createZNameList());
                SubstVariableToExpVisitor svte = new SubstVariableToExpVisitor(lstName, lstExpr);
                tempAp.accept(svte);
                
                String n = map_.getAndIncVarNum();
                // rename the global variable name from name to "name + global numbering"
                List<Pair<String, String>> lstRenamePair = new ArrayList<Pair<String, String>>();
                
                for(Decl decl: zdl) {
                  if(decl instanceof VarDecl) {
                    VarDecl vd = (VarDecl)decl;
                    for(Name vn: vd.getZNameList()) {
                      String strVn = Circus2ZCSPUtils.termToString(vn);
                      lstRenamePair.add(new Pair<String, String>(strVn, strVn + n));
                    }
                  }
                }
                
                VariableRenamingSchemaVisitor visitor = 
                    new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_NAME_REPLACE, lstRenamePair);
                
                tempAp.accept(visitor);
                
                // if ap is a global definition, then add this new AxPara to global as well
//                if(generic_axpara_global_.contains(ap)) {
//                  new_paralist_.add(tempAp);
//                }
                if(process_para_ != null) {
                  // if this instantiation happens within the process, we add it in the process
                  assert(process_para_.getCircusProcess() instanceof BasicProcess);
                  
                  // get the index of current AxPara or ActionPara
                  int index = 0;
                  for(int i = stack_parent_.size(); i > 0; i--) {
                    Term t = stack_parent_.get(i - 1); 
                    if(t instanceof AxPara || t instanceof ActionPara) {
                      index = process_para_.getCircusBasicProcess().getZParaList().indexOf(t);
                    }
                  }
                   
                  // Add tempAp just before this index
                  process_para_.getCircusBasicProcess().getZParaList().add(index, tempAp);
                }
                else {
                  if(generic_axpara_global_.contains(ap)) {
                    new_paralist_.add(tempAp);
                  }
                }
                
                // replace RefExpr by RefExpr of its new name
                RefExpr newName = fac_.createRefExpr(
                    fac_.createZName(Circus2ZCSPUtils.termToString(name) + n, fac_.createZStrokeList(), null), 
                    fac_.createZExprList(), false, false);
                
                map_generic_refexpr_.put(term, newName);
                
                // for other global variables or constants defined in this AxPara, we need to add them as well
                for(Pair<String, String> p: lstRenamePair) {
                  RefExpr re = ZUtils.cloneTerm(term);
                  re.getZName().setWord(p.getFirst());
                  RefExpr newRe = fac_.createRefExpr(
                      fac_.createZName(p.getSecond(), fac_.createZStrokeList(), null), 
                      fac_.createZExprList(), false, false);
                  map_generic_refexpr_.put(re, newRe);
                }
                
                // add this map to the map list
                Circus2ZCSPUtils.updateParentRef(stack_parent_, term, newName);
                return null;
              }
              
              break;
//            case ABBR: 
            case GEN_ABBR:
              if(Circus2ZCSPUtils.isEquals((ZName) ZUtils.getAbbreviationName(ap), name)) {
                // get a map between generic formals and actual formals
                for(int i = 0; i < formals.size(); i++) {
                  lstName.add((ZName) formals.get(i));
                  lstExpr.add(zel.get(i));
                }
                
                // don't change the original
                Expr se = ZUtils.cloneTerm(ZUtils.getAbbreviationExpr(ap));
                SubstVariableToExpVisitor svte = new SubstVariableToExpVisitor(lstName, lstExpr);
                se.accept(svte);
                
                if(delxi != null) {
                  // it's a reference to Delta or Xi
                  if(se instanceof RefExpr) {
                    // we just put back the prefix Delta or Xi
                    RefExpr re = (RefExpr)se;
                    re.getZName().setWord(delxi + re.getZName().getWord());
                    Circus2ZCSPUtils.updateParentRef(stack_parent_, term, re);
                  }
                  else if (se instanceof SchExpr) {
                    // in this case, we have to add additional schema definition and refer \Delta to this
                    // new definition
                    String strParaName = 
                        MessageFormat.format(FormatPattern.TEMP_SCHEMA_NAMING_GENERIC_INST, 
                            map_.getAndIncVarNum());
                    ZName paraname = fac_.createZName(
                        strParaName, fac_.createZStrokeList(), null);
                    ConstDecl cd = fac_.createConstDecl(paraname, (SchExpr)se);

                    ZDeclList declList0 = fac_.createZDeclList();
                    declList0.add(cd);
                    
                    SchText schtext = fac_.createZSchText(declList0, null);

                    ZNameList fp = fac_.createZNameList();
                    AxPara axpara = fac_.createAxPara(fp, schtext, Box.OmitBox);
                    
                    // globally
                    if(process_para_ == null) {
                      // should add this axpara just in front of the AxPara in visiting
                      Term tInVisit = null;
                      for(Term t: stack_parent_) {
                        // assume the term in visit is an Axpara
                        if(t instanceof AxPara) {
                          tInVisit = t;
                          break;
                        }
                      }
                      if(tInVisit != null) {
                        int index = new_paralist_.indexOf(tInVisit);
                        new_paralist_.add(index, axpara);
                      }
                      else {
                        new_paralist_.add(axpara);
                      }
                    }
                    else {
                      // locally within a process
                      // in case it is a AxPara in a process
                      // get current basic processes
                      assert(process_para_.getCircusProcess() instanceof BasicProcess);
                      
                      // should add this axpara just in front of the AxPara in visiting
                      Term tInVisit = null;
                      for(Term t: stack_parent_) {
                        // assume the term in visit is an Axpara
                        if(t instanceof AxPara) {
                          tInVisit = t;
                          break;
                        }
                      }
                      
                      ZParaList zpl = process_para_.getCircusBasicProcess().getZParaList();
                      if(tInVisit != null) {
                        int index = zpl.indexOf(tInVisit);
                        zpl.add(index, axpara);
                      }
                      else {
                        zpl.add(axpara);
                      }
                      process_para_.getCircusBasicProcess().setParaList(zpl);
                    }
                      
                    RefExpr re = fac_.createRefExpr(fac_.createZName((delxi + paraname.getWord()), 
                        fac_.createZStrokeList(), null), fac_.createZExprList(), false, false);
                    Circus2ZCSPUtils.updateParentRef(stack_parent_, term, re);
                  }
                } else {
                  Circus2ZCSPUtils.updateParentRef(stack_parent_, term, se);
                }
                return null;
              }
              break;
//            case BOXED_SCHEMA: 
            case GEN_BOXED_SCHEMA: // possible
//            case HORIZON_SCHEMA: 
            case GEN_HORIZON_SCHEMA: // possible
              if(Circus2ZCSPUtils.isEquals((ZName)ZUtils.getSchemaName(ap), name)) {
                // get a map between generic formals and actual formals
                for(int i = 0; i < formals.size(); i++) {
                  lstName.add((ZName) formals.get(i));
                  lstExpr.add(zel.get(i));
                }
                // don't change the generic_process_para_
                Expr se = ZUtils.cloneTerm(ZUtils.getSchemaDefExpr(ap));
                SubstVariableToExpVisitor svte = new SubstVariableToExpVisitor(lstName, lstExpr);
                se.accept(svte);
                
                if(delxi != null) {
                  // it's a reference to Delta or Xi
                  if(se instanceof RefExpr) {
                    // we just put back the prefix Delta or Xi
                    RefExpr re = (RefExpr)se;
                    re.getZName().setWord(delxi + re.getZName().getWord());
                    Circus2ZCSPUtils.updateParentRef(stack_parent_, term, re);
                  }
                  else if (se instanceof SchExpr) {
                    // in this case, we have to add additional schema definition and refer \Delta to this
                    // new definition
                    String strParaName = 
                        MessageFormat.format(FormatPattern.TEMP_SCHEMA_NAMING_GENERIC_INST, 
                            map_.getAndIncVarNum());
                    ZName paraname = fac_.createZName(
                        strParaName, fac_.createZStrokeList(), null);
                    ConstDecl cd = fac_.createConstDecl(paraname, (SchExpr)se);

                    ZDeclList declList0 = fac_.createZDeclList();
                    declList0.add(cd);
                    
                    SchText schtext = fac_.createZSchText(declList0, null);

                    ZNameList fp = fac_.createZNameList();
                    AxPara axpara = fac_.createAxPara(fp, schtext, Box.OmitBox);
                    
                    // globally
                    if(process_para_ == null) {
                      // should add this axpara just in front of the AxPara in visiting
                      Term tInVisit = null;
                      for(Term t: stack_parent_) {
                        // assume the term in visit is an Axpara
                        if(t instanceof AxPara) {
                          tInVisit = t;
                          break;
                        }
                      }
                      if(tInVisit != null) {
                        int index = new_paralist_.indexOf(tInVisit);
                        new_paralist_.add(index, axpara);
                      }
                      else {
                        new_paralist_.add(axpara);
                      }
                    }
                    else {
                      // locally within a process
                      // in case it is a AxPara in a process
                      // get current basic processes
                      assert(process_para_.getCircusProcess() instanceof BasicProcess);
                      
                      // should add this axpara just in front of the AxPara in visiting
                      Term tInVisit = null;
                      for(Term t: stack_parent_) {
                        // assume the term in visit is an Axpara
                        if(t instanceof AxPara) {
                          tInVisit = t;
                          break;
                        }
                      }
                      
                      ZParaList zpl = process_para_.getCircusBasicProcess().getZParaList();
                      if(tInVisit != null) {
                        int index = zpl.indexOf(tInVisit);
                        zpl.add(index, axpara);
                      }
                      else {
                        zpl.add(axpara);
                      }
                      process_para_.getCircusBasicProcess().setParaList(zpl);
                    }
                      
                    RefExpr re = fac_.createRefExpr(fac_.createZName((delxi + paraname.getWord()), 
                        fac_.createZStrokeList(), null), fac_.createZExprList(), false, false);
                    Circus2ZCSPUtils.updateParentRef(stack_parent_, term, re);
                  }
                } else {
                  Circus2ZCSPUtils.updateParentRef(stack_parent_, term, se);
                }
                return null;
              }
              break;
            default:
              break;
          }

        }
        
        /*
         * 2. generic channel
         */
        for(ChannelDecl cd: generic_channel_decl_) {
          for(Name n: cd.getZChannelNameList()) {
            if(Circus2ZCSPUtils.isEquals((ZName) n, name)) {
              ZNameList formals = cd.getZGenFormals();
              List<ZName> lstName = new ArrayList<ZName>();
              List<Expr> lstExpr = new ArrayList<Expr>();
              // get a map between generic formals and actual formals
              for(int i = 0; i < formals.size(); i++) {
                lstName.add((ZName) formals.get(i));
                lstExpr.add(zel.get(i));
              }
              // don't change the generic_channel_decl_
              Expr chnExpr = ZUtils.cloneTerm(cd.getExpr());
              SubstVariableToExpVisitor svte = new SubstVariableToExpVisitor(lstName, lstExpr);
              chnExpr.accept(svte);
              // add additional channel declaration
              // 
              String chnName = Circus2ZCSPUtils.termToString(name);
              String chnStrExpr = Circus2ZCSPUtils.termToString(chnExpr);
              // is the channel declared before or not
              boolean isChnDecl = false;
              
              Set<String> declChnSet = map_.getAllChannels();
              for(String chn: declChnSet) {
                Pair<String, Term> p = map_.getChnDecl(chn);
                String patt = MessageFormat.format(FormatPattern.GENERIC_CHANNEL_PATT,
                    chnName, "");
                if(chn.startsWith(patt) && p.getFirst().equals(chnStrExpr) && 
                    p.getSecond().equals(chnExpr)) {
                  isChnDecl = true;
                  chnName = chn;
                  break;
                }
              }
              
              // not declared before
              if(!isChnDecl) {
                chnName = MessageFormat.format(FormatPattern.GENERIC_CHANNEL_PATT,
                    chnName, map_.getAndIncVarNum());
                List<ZName> lstName1 = new ArrayList<ZName>();
                lstName1.add(fac_.createZName(chnName, fac_.createZStrokeList(), null));
                NameList nameList = cfac_.createZNameList(lstName1);
                List<NameList> lstNameList = new ArrayList<NameList>();
                lstNameList.add(cfac_.createZNameList());
                lstNameList.add(nameList);
                ChannelDecl chnDecl = cfac_.createChannelDecl(lstNameList, chnExpr);
                List<Decl> lstDecl = new ArrayList<Decl>();
                lstDecl.add(chnDecl);
                DeclList declList = fac_.createZDeclList(lstDecl);
                ChannelPara cp = cfac_.createChannelPara(declList);
                new_paralist_.add(cp);
                visit(chnDecl);
              }
              
              RefExpr re = fac_.createRefExpr(
                  fac_.createZName(chnName, fac_.createZStrokeList(), null),
                  fac_.createZExprList(), false, false);
              
              // replace RefExpr by RefExpr of its new channel name
              Circus2ZCSPUtils.updateParentRef(stack_parent_, term, re);
              
              // we check the map at first
              map_generic_refexpr_.put(term, re);
              break;
            }
          }
        }
        
        /*
         * 3. or generic process
         */
        for(ProcessPara p: generic_process_para_) {
          if(p.getZName().equals(name)) {
            ZNameList formals = p.getZGenFormals();
            List<ZName> lstName = new ArrayList<ZName>();
            List<Expr> lstExpr = new ArrayList<Expr>();
            // get a map between generic formals and actual formals
            for(int i = 0; i < formals.size(); i++) {
              lstName.add((ZName) formals.get(i));
              lstExpr.add(zel.get(i));
            }
            // don't change the generic_process_para_
            CircusProcess cp = ZUtils.cloneTerm(p.getCircusProcess());
            SubstVariableToExpVisitor svte = new SubstVariableToExpVisitor(lstName, lstExpr);
            cp.accept(svte);
            // add additional channel declaration
            // 
            String procName = Circus2ZCSPUtils.termToString(name);
            
            // create and add an additional BasicProcess
            procName = MessageFormat.format(FormatPattern.GENERIC_PROCESS_PATT,
                procName, map_.getAndIncVarNum());
            
            ProcessPara pp = cfac_.createProcessPara(
                fac_.createZName(procName, fac_.createZStrokeList(), null), 
                fac_.createZNameList(), cp);
            new_paralist_.add(pp);
            
            // update current process reference
            RefExpr re = fac_.createRefExpr(
                fac_.createZName(procName, fac_.createZStrokeList(), null),
                fac_.createZExprList(), false, false);
            
            // replace RefExpr by RefExpr of its new channel name
            Circus2ZCSPUtils.updateParentRef(stack_parent_, term, re);
            break;
          }
        }
          
        break;
      case REF:
        break;
      default:
        throw new CztException("Unknown ref expr kind");
    }
    
    return null;
  }

  /**
   * Given Para is rewritten to a number of free types
   */
  @Override
  public Object visitGivenPara(GivenPara term)
  {
    if(rewrite_stage_ != 1) {
      return null;
    }

    int ind = new_paralist_.indexOf(term);

    String value = config_.getConfig(Config.CONF_GIVEN_SET_INST_NO);
    int n = Integer.parseInt(value);

    for (Name name: term.getZNameList()) {
      String strName = Circus2ZCSPUtils.termToString(name);
      map_.addGivenSet(strName);
      List<Branch> lstBranch = new ArrayList<Branch>();
      
      for (int i = 1; i <= n; i++) {
        String strBranchName = MessageFormat.format(FormatPattern.GIVEN_SET_NAME_PATT, strName, i);
        Name branchName = fac_.createZName(strBranchName, fac_.createZStrokeList(), null);
        Branch b = fac_.createBranch(branchName, null);
        lstBranch.add(b);
      }
      
      BranchList branchList = fac_.createZBranchList(lstBranch);
      Freetype fp = fac_.createFreetype(name, branchList);
      ZFreetypeList freetypeList = fac_.createZFreetypeList();
      freetypeList.add(fp);

      new_paralist_.add(ind, fac_.createFreePara(freetypeList));
    }
    
    return null;
  }

  @Override
  public Object visitFreetype(Freetype term)
  {

    return null;
  }

  @Override
  public Object visitNumStroke(NumStroke term)
  {

    return null;
  }

  @Override
  public Object visitHideExpr(HideExpr term)
  {
    visit(term.getZNameList());
    visit(term.getExpr());
    return null;
  }

  @Override
  public Object visitLatexMarkupPara(LatexMarkupPara term)
  {

    return null;
  }

  @Override
  public Object visitNextStroke(NextStroke term)
  {

    return null;
  }

  @Override
  public Object visitSectTypeEnvAnn(SectTypeEnvAnn term)
  {

    return null;
  }

  @Override
  public Object visitZStrokeList(ZStrokeList term)
  {
    for(Stroke s: term) {
      visit(s);
    }
    return null;
  }

  @Override
  public Object visitZDeclList(ZDeclList term)
  {
    for(Decl d: term) {
      visit(d);
    }
    return null;
  }

  @Override
  public Object visitMuExpr(MuExpr term)
  {
    visit(term.getZSchText());
    visit(term.getExpr());
    return null;
  }

  @Override
  public Object visitSetCompExpr(SetCompExpr term)
  {
    visit(term.getExpr());
    visit(term.getZSchText());
    return null;
  }

  @Override
  public Object visitSetExpr(SetExpr term)
  {
    visit(term.getZExprList());
    return null;
  }

  @Override
  public Object visitZNameList(ZNameList term)
  {
    for(Name n: term) {
      visit(n);
    }
    return null;
  }

  @Override
  public Object visitLambdaExpr(LambdaExpr term)
  {
    visit(term.getExpr());
    visit(term.getZSchText());
    return null;
  }

  @Override
  public Object visitOutStroke(OutStroke term)
  {

    return null;
  }

  @Override
  public Object visitCompExpr(CompExpr term)
  {
    visit(term.getLeftExpr());
    visit(term.getRightExpr());
    return null;
  }

  @Override
  public Object visitForallExpr(ForallExpr term)
  {
    visit(term.getExpr());
    visit(term.getZSchText());
    return null;
  }

  @Override
  public Object visitPipeExpr(PipeExpr term)
  {
    return null;
  }

  @Override
  public Object visitBindExpr(BindExpr term)
  {

    return null;
  }

  @Override
  public Object visitGenParamType(GenParamType term)
  {

    return null;
  }

  @Override
  public Object visitConjPara(ConjPara term)
  {

    return null;
  }

  @Override
  public Object visitVarDecl(VarDecl term)
  {
    visit(term.getZNameList());
    visit(term.getExpr());
    return null;
  }

  @Override
  public Object visitZParaList(ZParaList term)
  {

    return null;
  }

  @Override
  public Object visitSchExpr(SchExpr term)
  {
    visit(term.getZSchText());
    return null;
  }

  @Override
  public Object visitSignatureAnn(SignatureAnn term)
  {

    return null;
  }

  @Override
  public Object visitMemPred(MemPred term)
  {
    visit(term.getLeftExpr());
    visit(term.getRightExpr());
    return null;
  }

  /**
   * Schema Rename
   */
  @Override
  public Object visitRenameExpr(RenameExpr term)
  {
    visit(term.getExpr());
//    visit(term.getZRenameList());
    
    // TODO: do we need to rewrite the schema renaming? might be not
//    ZRenameList list = term.getZRenameList();
//    List<Pair<String, String>> lstRenamePair = new ArrayList<Pair<String, String>>();
//    for(NewOldPair p: list) {
//      lstRenamePair.add(new Pair<String, String>(
//          Circus2ZCSPUtils.termToString(p.getOldName()),
//          Circus2ZCSPUtils.termToString(p.getNewName())));
//    }
//    
//    VariableRenamingSchemaVisitor visitor = 
//        new VariableRenamingSchemaVisitor(VariableRenameSchema.VRS_NAME_REPLACE, lstRenamePair);
//    
//    term.getExpr().accept(visitor);
//    
//    Circus2ZCSPUtils.updateParentRef(stack_parent_, term, term.getExpr());
    
    return null;
  }

  @Override
  public Object visitExists1Pred(Exists1Pred term)
  {
    visit(term.getPred());
    visit(term.getZSchText());
    return null;
  }

  @Override
  public Object visitForallPred(ForallPred term)
  {
    visit(term.getPred());
    visit(term.getZSchText());
    return null;
  }

  @Override
  public Object visitApplExpr(ApplExpr term)
  {
    visit(term.getLeftExpr());
    visit(term.getRightExpr());
    return null;
  }

  @Override
  public Object visitExprPred(ExprPred term)
  {
    visit(term.getExpr());
    return null;
  }

  @Override
  public Object visitZSect(ZSect term)
  {
    String sectionName = term.getName();
    zsect_ = term;
    sectname_ = sectionName;
    
    ZParaList paralist = term.getZParaList();
    paralist_.addAll(paralist);
    new_paralist_.addAll(paralist);
    
    /**
     *  TODO: 1. to rewrite the indexed process, we need the information about all channels declared from map_.getAllChannels();
     *          But channel declaration paragraph may be put after the indexed process, so map_.getAllChannels may not get actual all channels.
     *          ???
     */
    for (net.sourceforge.czt.z.ast.Para para : paralist) {
      if (para instanceof ProcessPara) {
    	  visit(para);
      }
      else if (para instanceof NarrPara) {
        // skip
        new_paralist_.remove(para);
      }
      else if (para instanceof GivenPara) {
        visit(para);
        new_paralist_.remove(para);
      }
      else if (para instanceof ChannelPara) {
        ChannelPara cp = (ChannelPara) para;
        visit(cp);
      }
      else if (para instanceof ChannelSetPara) {
        visit(para);
      }
      else if (para instanceof LatexMarkupPara) {
        // skip
        new_paralist_.remove(para);
      }
      else if (para instanceof AxPara) 
      {
        AxPara ap = (AxPara) para;
        // For Abbreviation, add it to paraList and also CSP
        if (ZUtils.isAbbreviation(para)) {
        }
        else if (ZUtils.isSimpleSchema(para)) {
        }
        else {
        }
        
        visit(para);
      }
      else if (para instanceof FreePara) {
        visit(para);
      }
      else if (para instanceof OptempPara){
        
      }
    }
    
    term.setParaList(new_paralist_);
//    zsect_ = null;
    return null;
  }

  @Override
  public Object visitZExprList(ZExprList term)
  {
    for(Expr e: term) {
      visit(e);
    }
    return null;
  }

  @Override
  public Object visitTupleExpr(TupleExpr term)
  {
    visit(term.getZExprList());
    return null;
  }

  @Override
  public Object visitSchemaType(SchemaType term)
  {
    return null;
  }

  @Override
  public Object visitImpliesExpr(ImpliesExpr term)
  {
    visit(term.getLeftExpr());
    visit(term.getRightExpr());
    return null;
  }

  @Override
  public Object visitGenericType(GenericType term)
  {

    return null;
  }

  @Override
  public Object visitNewOldPair(NewOldPair term)
  {
    visit(term.getNewName());
    visit(term.getOldName());
    return null;
  }

  @Override
  public Object visitNarrPara(NarrPara term)
  {

    return null;
  }

  @Override
  public Object visitIffPred(IffPred term)
  {
    visit(term.getLeftPred());
    visit(term.getRightPred());
    return null;
  }

  @Override
  public Object visitLocAnn(LocAnn term)
  {

    return null;
  }

  @Override
  public Object visitExists1Expr(Exists1Expr term)
  {
    visit(term.getExpr());
    visit(term.getZSchText());
    return null;
  }

  @Override
  public Object visitGivenType(GivenType term)
  {

    return null;
  }

  @Override
  public Object visitSignature(Signature term)
  {

    return null;
  }

  @Override
  public Object visitNegPred(NegPred term)
  {
    visit(term.getPred());
    return null;
  }

  @Override
  public Object visitZSchText(ZSchText term)
  {
    visit(term.getZDeclList());
    visit(term.getPred());
    return null;
  }

  @Override
  public Object visitProjExpr(ProjExpr term)
  {
    visit(term.getLeftExpr());
    visit(term.getRightExpr());
    return null;
  }

  @Override
  public Object visitDirective(Directive term)
  {

    return null;
  }

  @Override
  public Object visitThetaExpr(ThetaExpr term)
  {
    visit(term.getExpr());
    visit(term.getZStrokeList());
    return null;
  }

  @Override
  public Object visitNumExpr(NumExpr term)
  {
    visit(term.getZNumeral());
    return null;
  }

  @Override
  public Object visitCondExpr(CondExpr term)
  {
    visit(term.getLeftExpr());
    visit(term.getRightExpr());
    return null;
  }

  @Override
  public Object visitLetExpr(LetExpr term)
  {
    visit(term.getExpr());
    visit(term.getZSchText());
    return null;
  }

  @Override
  public Object visitSpec(Spec term)
  {

    return null;
  }

  @Override
  public Object visitOptempPara(OptempPara term)
  {

    return null;
  }

  @Override
  public Object visitBindSelExpr(BindSelExpr term)
  {

    return null;
  }

  @Override
  public Object visitProdExpr(ProdExpr term)
  {
    visit(term.getZExprList());
    return null;
  }

  @Override
  public Object visitPreExpr(PreExpr term)
  {
    visit(term.getExpr());
    return null;
  }

  @Override
  public Object visitProdType(ProdType term)
  {

    return null;
  }

  @Override
  public Object visitNegExpr(NegExpr term)
  {
    visit(term.getExpr());
    return null;
  }

  @Override
  public Object visitNameSectTypeTriple(NameSectTypeTriple term)
  {

    return null;
  }

  @Override
  public Object visitInStroke(InStroke term)
  {
    return null;
  }

  @Override
  public Object visitIffExpr(IffExpr term)
  {
    visit(term.getLeftExpr());
    visit(term.getRightExpr());
    return null;
  }

  /**
   * unfold a schema expression
   * 
   * @param sch
   * @return
   */
//  private Term unfold(SchExpr sch)
//  {
//    Term t = ZUtils.cloneTerm(sch);
//    return t;
//  }

  /**
   * unfold a schema expression
   * 
   * @param sch
   * @return
   */
  private SchExpr unfold(SchExpr sch)
  {
    // Now we can not unfold a schema without normalisation, that what we want during expansion.
    // so just clone it
    SchExpr t = ZUtils.cloneTerm(sch);
    
//    t = expansionSchema(sch);
    return t;
  }
    
  /**
   * Expand a schema expression
   * @param sch
   * @return
   */
  private SchExpr expansionSchema(Expr expr)
  {
    SchExpr ret = null;
    
    RuleTable rules = null;
    try {
      SectionManager managerz = new SectionManager(Dialect.ZPATT);
      rules = managerz.get(new Key<RuleTable>(Section.EXPANSION_RULES.getName(), RuleTable.class));
      RuleTable simplificationRules = managerz.get(new Key<RuleTable>(Section.SIMPLIFICATION_RULES.getName(), RuleTable.class));
      rules.addRuleParas(simplificationRules);
    }
    catch (SectionInfoException e) {
      throw new CztException("Expand schema expression: ", e);
    }
    catch (CommandException e) {
      throw new CztException("Expand schema expression: ", e);
    }
    catch (RuleTableException e) {
      throw new CztException("Expand schema expression: ", e);
    }
        
    try {
      Spec spec = manager_.get(new Key<Spec>("spec", Spec.class));
      String sectionName = ((ZSect)spec.getSect().get(0)).getName();
      
      Expr applExpr = RewriteUtils.createNormalizeAppl(expr);
      
      Debug.debug_print(
          Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
          Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
          Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
          "Before expansion: " + Circus2ZCSPUtils.printToString(applExpr, sectionName, manager_));
      Term rew_term = Strategies.innermost(applExpr, rules, manager_, sectionName);
      if(rew_term instanceof SchExpr) {
        ret = (SchExpr)rew_term;
      }
      Debug.debug_print(
          Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
          Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
          Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
          "After expansion: " + Circus2ZCSPUtils.printToString(rew_term, sectionName, manager_));
    }
    catch (UnboundJokerException e) {
      throw new CztException("Expand schema expression: ", e);
    }
    catch (CommandException e) {
      throw new CztException("Expand schema expression: ", e);
    }

    return ret;
  }
  
  /**
   * Get decl list from a simple schema
   * 
   * @param para
   * @return
   */
  public List<Pair<ZName, Expr>> getDeclList(AxPara para)
  {
    List<Pair<ZName, Expr>> lstZNameExpr = null;
    
    // horizontal or box schema, but not include schema operators, such as S == S1 \land S2
    // but includes [S1 | p]
    if(ZUtils.isSimpleSchema(para)) {
      Expr expr = ZUtils.getSchemaDefExpr(para);
      assert(expr instanceof SchExpr);
      SchExpr t = expansionSchema((SchExpr)expr);
      
      // How to cope with rewritten schema expression (normalized)?
      // Before unfold: normalize [ x , y : T ; z : \nat | z > 5 ]
      // After unfold: [ x : \arithmos ; y : \arithmos ; z : \arithmos | ( x \in T \land y \in T \land z \in \nat ) \land z > 5 ]
      ZDeclList zdl = ((SchExpr)t).getZSchText().getZDeclList();
      lstZNameExpr = Circus2ZCSPUtils.getDeclList(zdl);
    }
    return lstZNameExpr;
  }
  
  /**
   * Get the definition of term in deftable_, and generic parameters are not returned
   * @param term - the term
   * @param genList - return generic formal list
   * @return
   *    null if not found
   */
  private Expr getExprFromDefTable(Term term, ZNameList genList)
  {
    Expr expr = null;
        
    // T here T is a type defined other places
    String strName = Circus2ZCSPUtils.termToString(term);
    DefinitionTable.Definition def = deftable_.lookup(strName);
    
    // Added distinction with CONSTDECL, for compatibility with old DefinitionTable
    if (def != null) {
//      if (def.getDefinitionType().equals(DefinitionType.VARDECL)) {
//        
//      }
//      
//      if (!def.getDefinitionType().equals(DefinitionType.CONSTDECL)) {
//        throw new CztException("Cannot find the definition of " + strName);
//      }

      // get the expression of str_t
      expr = def.getExpr();
      if(genList != null) {
        genList.clear();
        genList.addAll(def.getDeclNames());
      }
      
//      if (expr == null) {
//        throw new CztException("Invalid expression for " + strName);
//      }
    }
    else {
//      throw new CztException("Can not find the defintion of " + strName + " in definition table!");
      Debug.debug_print(
          Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
          Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
          Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
          "Can not find the defintion of " + strName + " in definition table!");
    }

    return expr;
  }
  
  /**
   * Expand an applExpr (1..3) to a list of string [1,2,3]
   * @param ae
   * @return
   */
  public Set<Pair<String, Expr>> expandApplExpr(ApplExpr ae)
  {
    Set<Pair<String, Expr>> ls = new HashSet<Pair<String, Expr>>();
    ZFactory fac = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    
    // such as 1..2
    if(ZUtils.isFcnOpApplExpr(ae)) {
      Expr le = ae.getLeftExpr();
      Expr re = ae.getRightExpr();
      assert(le instanceof RefExpr);
      OperatorName os = ((RefExpr)le).getZName().getOperatorName();
      assert os != null;
      assert ZUtils.isTupleExpr(re);
      String rel = Circus2ZCSPUtils.getOperator(os);
      
      if(rel.equals("..")) {
        // it is also possible for x..y
        Expr expr1 = ((TupleExpr)re).getZExprList().get(0);
        Expr expr2 = ((TupleExpr)re).getZExprList().get(1);
        
        // we only support NumExpr or RefExpr for e1 .. e2
        // if it is not the case, throw an exception
        if(!((expr1 instanceof NumExpr || expr1 instanceof RefExpr) &&
            (expr2 instanceof NumExpr || expr2 instanceof RefExpr))) {
          throw new CztException("The expansion of number range .. only supports NumExpr and RefExpr but they are " +
            expr1.getClass().getName() + " and " + expr2.getClass().getName() + "!");
        }
        
        String first = null;
        String second = null;
        
        Expr e1 = null;
        Expr e2 = null;
        
        String strExpr1 = Circus2ZCSPUtils.termToString(expr1);
        String strExpr2 = Circus2ZCSPUtils.termToString(expr2);
        
        if(expr1 instanceof RefExpr) {
          // first to check configuration file to see if it is defined
          String value = config_.getConfig(strExpr1);
          if(value == null) {
            // it might not be possible to get their value from deftable_
            // i.e. for axiomatic definition maxbuff, it only returns its type Nat_1
            e1 = getExprFromDefTable(expr1, null);
          }
          else {
            first = value;
          }
        }
        else {
          first = strExpr1;
        }

        if(expr2 instanceof RefExpr) {
          // first to check configuration file to see if it is defined
          String value = config_.getConfig(strExpr2);
          if(value == null) {
            e2 = getExprFromDefTable(expr2, null);
          }
          else {
            second = value;
          }
        }
        else {
          second = strExpr2;
        }
        
        if (first != null && second != null) {
          for(int i = Integer.parseInt(first); i <= Integer.parseInt(second); i++) {
            NumExpr er = (NumExpr)ZUtils.cloneTerm(((TupleExpr)re).getZExprList().get(0));
            Numeral nl = fac.createZNumeral(BigInteger.valueOf(i));
            er.setNumeral(nl);
            ls.add(new Pair<String, Expr>(Integer.toString(i), er));
          }
        }
        else {
          throw new CztException("Faild to expand [" + strExpr1 + ".." + strExpr2 + 
              "]. You can set them in config.properties file.");
        }
      }
      else {
        throw new CztException("Expand of " + Circus2ZCSPUtils.termToString(ae) + "is not supported yet!");
      }
    }
    else {
      throw new CztException("Expand of " + Circus2ZCSPUtils.termToString(ae) + "is not supported yet!");
    }
    
    return ls;
  }
  
  /**
   * Expand an applExpr (1..3) to a list of string [1,2,3]
   * @param ae
   * @return
   */
  public Set<Pair<String, Expr>> expandGivenSet(String gname)
  {
    Set<Pair<String, Expr>> ls = new HashSet<Pair<String, Expr>>();
    // If we can not find it in the deftable_, regard it is a given type
    String value = config_.getConfig(Config.CONF_GIVEN_SET_INST_NO);
    int n = Integer.parseInt(value);
    
    for (int i = 1; i <= n; i++) {
      // TODO: what's the expression of the element of a given set
      // just use RefExpr at this moment
      String name = MessageFormat.format(FormatPattern.GIVEN_SET_NAME_PATT, gname, i);
      RefExpr expr = fac_.createRefExpr(
          fac_.createZName(name, fac_.createZStrokeList(), null),
          fac_.createZExprList(), false, false);
      ls.add(new Pair<String, Expr>(name, expr));
    }

    return ls;
  }
  
  /**
   * Expand a freetype definition to a set, for example
   *    const | d <<1..3>>  => {const, d~1, d~2, d~3}
   * @param zbl
   * @return
   */
  public Set<Pair<String, Expr>> expandFreetypeToSet(ZBranchList zbl)
  {
    Set<Pair<String, Expr>> ls = new HashSet<Pair<String, Expr>>();
    for(Branch b: zbl) {
      String name = Circus2ZCSPUtils.termToString(b.getZName());
      if(b.getExpr() == null) {
        // const        
        RefExpr expr = fac_.createRefExpr(
            fac_.createZName(name, fac_.createZStrokeList(), null),
            fac_.createZExprList(), false, false);
        ls.add(new Pair<String, Expr>(name, expr));
      }
      else {
        Set<Pair<String, Expr>> ts = expandExprToSet(b.getExpr());
        for(Pair<String, Expr> p: ts) {
          RefExpr re = fac_.createRefExpr(
              b.getZName(), fac_.createZExprList(), false, false);
          
          List<Expr> lstExpr = new ArrayList<Expr>();
          lstExpr.add(re);
          lstExpr.add(p.getSecond());
          ApplExpr ae = fac_.createApplExpr(lstExpr, false);
          ls.add(new Pair<String, Expr>(name + p.getFirst(), ae));
        }
      }
    }
    return ls;
  }
  
  /**
   * Expand an expression to a set of string
   * @param e - SetExpr ({1,3,4}), ApplExpr (1..3), 
   * @return
   */
  private TreeSet<Pair<String, Expr>> expandExprToSet(Expr e)
  {
    TreeSet<Pair<String, Expr>> s = new TreeSet<Pair<String, Expr>>(new pairStringTComparator<Expr>());
    
    if(e instanceof SetExpr) {
      for(Expr ex: ((SetExpr)e).getZExprList()) {
        // assume it is a simple expression like NumExpr, RefExpr
        s.add(new Pair<String, Expr>(Circus2ZCSPUtils.termToString(ex), ex));
      }
    } else if (e instanceof ApplExpr) {
      // 1..3
      ApplExpr ae = (ApplExpr)e;
      // s.addAll(Circus2ZCSPUtils.expandApplExpr(ae));
      s.addAll(expandApplExpr(ae));
    } else if (e instanceof RefExpr) {
//      // T here T is a type defined other places
      String str_t = Circus2ZCSPUtils.termToString(e);
//      DefinitionTable.Definition def = deftable_.lookup(str_t);
//      // Added distinction with CONSTDECL, for compatibility with old DefinitionTable (Leo)
//      
//      if (def != null) {
//        if (!def.getDefinitionType().equals(DefinitionType.CONSTDECL)) {
//          CztException ex = new CztException("Cannot find the definition of type: " + str_t);
//          throw ex;
//        }
//
//        // get the expression of str_t
//        Expr expr_t = def.getExpr();
//        if (expr_t == null) {
//          CztException ex = new CztException("Invalid expression for type: " + str_t);
//          throw ex;
//        }

      Expr ex = getExprFromDefTable(e, null);
      if(ex != null) {
        s = expandExprToSet(ex);
      }
      else {
        // check if it is given set
        List<String> allGiven = map_.getGivenSetName();
        if(allGiven.contains(str_t)) {
          s.addAll(expandGivenSet(str_t));
        }
        else {
          // check if it is freetype
          List<Triple<String, String, Term>> allFreetypes = map_.getAllFreeTypes();
          for(Triple<String, String, Term> t: allFreetypes) {
            if(t.getFirst().equals(str_t)) {
              if(t.getThird() instanceof ZBranchList) {
                s.addAll(expandFreetypeToSet((ZBranchList)t.getT3()));
              }
              else {
                throw new CztException("expandExpToSet: " + e.toString() + " can not be expanded to a set because " + 
                    t.getT3().toString() + " is an invalid freetype branchlist.");
              }
            }
          }
        }
      }
      
      if(s.isEmpty()) {
        throw new CztException("expandExpToSet: " + e.toString() + " can not be expanded to a set.");
      }

    }
    else {
      throw new CztException("expandExpToSet: " + e.toString() + " can not be expanded to a set.");
    }
    return s;
  }
  
  /**
   * A comparator according to the first string in the pair
   * @author ykf_2001
   *
   */
  public class pairStringTComparator<T> implements Comparator<Pair<String, T>>
  {
    @Override
    public int compare(Pair<String, T> x, Pair<String, T> y)
    {
      // x > y
      if (x.getFirst().compareTo(y.getFirst()) > 0) {
        return 1;
      } else if (x.getFirst().compareTo(y.getFirst()) < 0) {
        return -1;
      }
      return 0;
    }
  }
  
//  /**
//   * A comparator according to the first string in the pair
//   * @author ykf_2001
//   *
//   */
//  public class pairStringExprComparator implements Comparator<Pair<String, Expr>>
//  {
//    @Override
//    public int compare(Pair<String, Expr> x, Pair<String, Expr> y)
//    {
//      // x > y
//      if (x.getFirst().compareTo(y.getFirst()) > 0) {
//        return 1;
//      } else if (x.getFirst().compareTo(y.getFirst()) < 0) {
//        return -1;
//      }
//      return 0;
//    }
//  }
  
  /**
   * A comparator according to string order
   * @author ykf_2001
   *
   */
  class StringComparator implements Comparator<String>
  {
    @Override
    public int compare(String x, String y)
    {
      // x > y
      if (x.compareTo(y) > 0) {
        return 1;
      } else if (x.compareTo(y) < 0) {
        return -1;
      }
      return 0;
    }
  }
  
  /**
   * permutate the input TreeSet and then output a list of 
   * 
   * @param ts - a set of map from variable name to its type set
   *           - {{x, {1,2,3}}, {y, {OPEN, CLOSE}}}
   * @param sls - Output result set
   *           - {[1,OPEN],[1,CLOSE],[2,OPEN],[2,CLOSE],[3,OPEN],[3,CLOSE]}
   * @param ls - temporary list
   */
  private void permutateParaProcess(TreeSet<Pair<String, TreeSet<Pair<String, Expr>>>> ts, Set<List<Pair<String, Expr>>> sls, List<Pair<String, Expr>> ls) 
  {
    Iterator<Pair<String, TreeSet<Pair<String, Expr>>>> ite = ts.iterator();
    if(!ite.hasNext()) {
//      Debug.debug_print("=========" + ls);
      List<Pair<String, Expr>> tls = new ArrayList<Pair<String, Expr>>(ls);
      sls.add(tls);
      return;
    }
    
    Pair<String, TreeSet<Pair<String, Expr>>> p = ite.next();
    // ----- for debug
    TreeSet<Pair<String, Expr>> p2 = p.getSecond();
    Set<String> temp_set = new HashSet<String>();
    for(Pair<String, Expr> tp: p2) {
      temp_set.add(tp.getFirst());
    }
    // ---
    for(Pair<String, Expr> pse: p.getSecond()) {
      List<Pair<String, Expr>> tls = new ArrayList<Pair<String, Expr>>(ls);
      tls.add(pse);
      Debug.debug_print(
          Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
          Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
          Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
          "Permutate " + p.getFirst() + " " + pse.getFirst() + " in " + temp_set);
      TreeSet<Pair<String, TreeSet<Pair<String, Expr>>>> tts = new TreeSet<Pair<String, TreeSet<Pair<String, Expr>>>>(ts);
      tts.remove(p);
      permutateParaProcess(tts, sls, tls);
    }
  }
  
  /**
   * permutate the input TreeSet and then output a list of 
   * 
   * @param ts - a set of map from variable name to its type set and ordered by the order (ZDeclList)
   *           - {{x, {1,2,3}}, {y, {OPEN, CLOSE}}}
   * @param sls - Output result set
   *           - {[1,OPEN],[1,CLOSE],[2,OPEN],[2,CLOSE],[3,OPEN],[3,CLOSE]}
   * @param ls - temporary list
   */
  private void permutateParaProcess(List<Pair<String, TreeSet<Pair<String, Expr>>>> ts, Set<List<Pair<String, Expr>>> sls, List<Pair<String, Expr>> ls) 
  {
    Iterator<Pair<String, TreeSet<Pair<String, Expr>>>> ite = ts.iterator();
    if(!ite.hasNext()) {
//      Debug.debug_print("=========" + ls);
      List<Pair<String, Expr>> tls = new ArrayList<Pair<String, Expr>>(ls);
      sls.add(tls);
      return;
    }
    
    Pair<String, TreeSet<Pair<String, Expr>>> p = ite.next();
    // ----- for debug
    TreeSet<Pair<String, Expr>> p2 = p.getSecond();
    Set<String> temp_set = new HashSet<String>();
    for(Pair<String, Expr> tp: p2) {
      temp_set.add(tp.getFirst());
    }
    // ---
    for(Pair<String, Expr> pse: p.getSecond()) {
      List<Pair<String, Expr>> tls = new ArrayList<Pair<String, Expr>>(ls);
      tls.add(pse);
      Debug.debug_print(
          Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
          Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
          Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
          "Permutate " + p.getFirst() + " " + pse.getFirst() + " in " + temp_set);
      List<Pair<String, TreeSet<Pair<String, Expr>>>> tts = new ArrayList<Pair<String, TreeSet<Pair<String, Expr>>>>(ts);
      tts.remove(p);
      permutateParaProcess(tts, sls, tls);
    }
  }
  
  /**
   * Expand a DeclList to a set of ...
   *  
   * @param zdl - a list of VarDecl in the parametrised process and indexed process.
   *            - example: x:{2,3}, y:0..1
   * @param ts  - an ordered set of map from variable name to its type set
   *            - example: {{x, {2,3}}, {y, {0, 1}}}
   * @param sls - a set of permutation of variable values. besides, the order in list is the same as the variable name order in ts
   *            - example: {[2,0], [2,1], [3,0], [3,1]}
   */
  private void expandDeclList2Set(ZDeclList zdl, TreeSet<Pair<String, TreeSet<Pair<String, Expr>>>> ts, Set<List<Pair<String, Expr>>> sls)
  {
    // get a list vardecl (x:Tx; y:Ty)
    // expand it to a map
    //        var -> {a set of possible values}      
    // actually the order in ls does matter. so order this set by the name of variable

    for(Decl decl: zdl) {
      assert(decl instanceof VarDecl);
      VarDecl vd = (VarDecl)decl;
      
      // the type of variables, and return a TreeSet of elements
      Expr e = vd.getExpr();
      TreeSet<Pair<String, Expr>> str_e = expandExprToSet(e);
      
      // variable name list
      for(Name name: vd.getZNameList()) {
        String str_name = Circus2ZCSPUtils.termToString(name);
        ts.add(new Pair<String, TreeSet<Pair<String, Expr>>>(str_name, str_e));
      }
    }
    
    List<Pair<String, Expr>> ls = new ArrayList<Pair<String, Expr>>();
    // a set of list of string and this list has n elements and each element is an expression of the element from the variable's type
    // this set is a permutation of 
    // for example, if x:{1,2}, y:0..1, then this set is
    //        {[1,0], [1,1], [2,0], [2,1]}
    
    permutateParaProcess(ts, sls, ls);
  }
  
  /**
   * Expand a DeclList to a set of ...
   *  
   * @param zdl - a list of VarDecl in the parametrised process and indexed process.
   *            - example: x:{2,3}, y:0..1
   * @param ts  - an ordered set of map from variable name to its type set (the order is the same as the order of ZDecList
   *            - example: {{x, {2,3}}, {y, {0, 1}}}
   * @param sls - a set of permutation of variable values. besides, the order in list is the same as the variable name order in ts
   *            - example: {[2,0], [2,1], [3,0], [3,1]}
   */
  private void expandDeclList2Set(ZDeclList zdl, List<Pair<String, TreeSet<Pair<String, Expr>>>> ts, Set<List<Pair<String, Expr>>> sls)
  {
    // get a list vardecl (x:Tx; y:Ty)
    // expand it to a map
    //        var -> {a set of possible values}      
    // actually the order in ls does matter. so order this set by the name of variable

    for(Decl decl: zdl) {
      assert(decl instanceof VarDecl);
      VarDecl vd = (VarDecl)decl;
      
      // the type of variables, and return a TreeSet of elements
      Expr e = vd.getExpr();
      TreeSet<Pair<String, Expr>> str_e = expandExprToSet(e);
      
      // variable name list
      for(Name name: vd.getZNameList()) {
        String str_name = Circus2ZCSPUtils.termToString(name);
        ts.add(new Pair<String, TreeSet<Pair<String, Expr>>>(str_name, str_e));
      }
    }
    
    List<Pair<String, Expr>> ls = new ArrayList<Pair<String, Expr>>();
    // a set of list of string and this list has n elements and each element is an expression of the element from the variable's type
    // this set is a permutation of 
    // for example, if x:{1,2}, y:0..1, then this set is
    //        {[1,0], [1,1], [2,0], [2,1]}
    
    permutateParaProcess(ts, sls, ls);
  }
  
  /**
   * Assemble a Z paragraph (\Xi) to retrieve state component 
   *  
   * @param stParaName - state paragraph name
   * @param pNameExpr - state component name and its type (<x, Tx>)
   * @return
   */
  public AxPara assembleZStateRetrPara(String stParaName, Pair<ZName, Expr> pNameExpr)
  {
    // 0. State retrieve paragraph OP_x
    String paraName = MessageFormat.format(FormatPattern.STATE_RETR_PARA_NAME_PATT,
        Circus2ZCSPUtils.termToString(pNameExpr.getFirst()));
    ZName paraname = fac_.createZName(paraName, fac_.createZStrokeList(), null);
    
    // 1. declaration list
    ZDeclList declList = fac_.createZDeclList();
    
    // 1.1 State Paragraph Name and \Xi State Paragraph (Xi State)
    ZName stname = fac_.createZName(ZString.XI + stParaName, fac_.createZStrokeList(), null);
    RefExpr expr = fac_.createRefExpr(stname, fac_.createZExprList(), false, false);

    // insert InclDecl in the beginning of declList and shift current to right
    InclDecl inclDecl = fac_.createInclDecl(expr);
    declList.add(0, inclDecl);

    // 1.2 VarDecl (x!:Tx)
    ZNameList znl = fac_.createZNameList();
    
    List<Stroke> lstStroke = new ArrayList<Stroke>();
    lstStroke.add(fac_.createOutStroke());
    
    StrokeList st = fac_.createZStrokeList(lstStroke);
    ZName zn = ZUtils.cloneTerm(pNameExpr.getFirst());
    zn.setStrokeList(st);
    znl.add(zn);
    
    VarDecl vdecl = fac_.createVarDecl(znl, pNameExpr.getSecond());
    declList.add(vdecl);
    
    // 2 predicates (x! = x)
    List<Expr> lstExpr = new ArrayList<Expr>();          
    lstExpr.add(fac_.createRefExpr(zn, fac_.createZExprList(), false, false));
    List<Expr> lstTempExpr = new ArrayList<Expr>();
    lstTempExpr.add(
        fac_.createRefExpr(pNameExpr.getFirst(), fac_.createZExprList(), false, false));
    lstExpr.add(fac_.createSetExpr(fac_.createZExprList(lstTempExpr)));
    // [x!, {x}]
    MemPred mp = fac_.createMemPred(lstExpr, true);
    assert(Circus2ZCSPUtils.getMemPredKind(mp) == MemPredKind.EQUALITY);
    
    ZSchText schText = fac_.createZSchText(declList, mp);
    SchExpr schExpr = fac_.createSchExpr(schText);

    ConstDecl cd = fac_.createConstDecl(paraname, schExpr);

    ZDeclList declList0 = fac_.createZDeclList();
    declList0.add(cd);
    
    SchText schtext = fac_.createZSchText(declList0, null);

    ZNameList fp = fac_.createZNameList();
    AxPara axpara = fac_.createAxPara(fp, schtext, Box.OmitBox);

    return axpara;
  }
  
  /**
   * Update current action to a new action (to) in its parent and it is used in rewrite of actions
   * @param current
   * @param to
   */
  private void updateParentAction(CircusAction current, CircusAction to)
  {
    CircusAction term = current;
    CircusAction cca = to;
    
    if(circus_action_stack_.isEmpty()) {
      // no parent, so the main action is a CallAction
      // set the action of OnTheFly main action to its action definition
      for(Para p: process_para_.getCircusBasicProcess().getOnTheFlyPara()) {
        if(p instanceof ActionPara) {
          if(process_para_.getCircusBasicProcess().getMainAction().equals(((ActionPara) p).getCircusAction())) {
            ((ActionPara) p).setCircusAction(cca);
          }
        }
      }
    } 
    else {
      // its parent is a CircusAction
      CircusAction ca = circus_action_stack_.peek();
    
      if(ca != null) {
        // Sequential
        if(ca instanceof SeqAction) {
          if(((SeqAction)ca).getLeftAction().equals(term)) {
            ((SeqAction)ca).setLeftAction(cca);
          } 
          else if(((SeqAction)ca).getRightAction().equals(term)) {
            ((SeqAction)ca).setRightAction(cca);
          }
          else {
            throw new CztException("CallAction [" + 
                net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                "] can not be found from its parent!");
          }
        }
        // external choice
        else if(ca instanceof ExtChoiceAction) {
          if(((ExtChoiceAction)ca).getLeftAction().equals(term)) {
            ((ExtChoiceAction)ca).setLeftAction(cca);
          } 
          else if(((ExtChoiceAction)ca).getRightAction().equals(term)) {
            ((ExtChoiceAction)ca).setRightAction(cca);
          }
          else {
            throw new CztException("CallAction [" + 
                net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                "] can not be found from its parent!");
          }
        }
        // internal choice
        else if(ca instanceof IntChoiceAction) {
          if(((IntChoiceAction)ca).getLeftAction().equals(term)) {
            ((IntChoiceAction)ca).setLeftAction(cca);
          } 
          else if(((IntChoiceAction)ca).getRightAction().equals(term)) {
            ((IntChoiceAction)ca).setRightAction(cca);
          }
          else {
            throw new CztException("CallAction [" + 
                net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                "] can not be found from its parent!");
          }
        }
        // Parallel and interleave actions
        else if(ca instanceof ParAction) {
          if(((ParAction)ca).getLeftAction().equals(term)) {
            ((ParAction)ca).setLeftAction(cca);
          } 
          else if(((ParAction)ca).getRightAction().equals(term)) {
            ((ParAction)ca).setRightAction(cca);
          }
          else {
            throw new CztException("CallAction [" + 
                net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                "] can not be found from its parent!");
          }
        }
        // Iterated parallel and interleave actions
        else if(ca instanceof ParActionIte ||
            ca instanceof SeqActionIte ||
            ca instanceof ExtChoiceActionIte || 
            ca instanceof IntChoiceActionIte
            ) {
          ActionIte pa = (ActionIte)ca;
          if(pa.getCircusAction().equals(term)) {
            pa.setCircusAction(cca);
          } 
          else {
            throw new CztException("CallAction [" + 
                net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                "] can not be found from its parent!");
          }
        }
        // Guarded Action
        else if(ca instanceof GuardedAction) {
          if(((GuardedAction)ca).getCircusAction().equals(term)) {
            ((GuardedAction)ca).setCircusAction(cca);
          } 
          else {
            throw new CztException("CallAction [" + 
                net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                "] can not be found from its parent!");
          }
        }
        // Hide Action
        else if(ca instanceof HideAction) {
          if(((HideAction)ca).getCircusAction().equals(term)) {
            ((HideAction)ca).setCircusAction(cca);
          } 
          else {
            throw new CztException("CallAction [" + 
                net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                "] can not be found from its parent!");
          }
        }
        // Mu Action
        else if(ca instanceof MuAction) {
          if(((MuAction)ca).getCircusAction().equals(term)) {
            ((MuAction)ca).setCircusAction(cca);
          } 
          else {
            throw new CztException("CallAction [" + 
                net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                "] can not be found from its parent!");
          }
        }
        // Prefixing action
        else if(ca instanceof PrefixingAction) {
          if(((PrefixingAction)ca).getCircusAction().equals(term)) {
            ((PrefixingAction)ca).setCircusAction(cca);
          } 
          else {
            throw new CztException("CallAction [" + 
                net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                "] can not be found from its parent!");
          }
        }
        // Rename action
        else if(ca instanceof SubstitutionAction) {
          if(((SubstitutionAction)ca).getCircusAction().equals(term)) {
            ((SubstitutionAction)ca).setCircusAction(cca);
          } 
          else {
            throw new CztException("CallAction [" + 
                net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                "] can not be found from its parent!");
          }
        }
        // assignment
        else if(ca instanceof AssignmentCommand) {
          // an assignment command should not be a parent
        }
        // CircusGuardedCommand 
        // possibly there are more than one same CallAction in IfGuardedCommand
        // i.e. if g1 & A1 | g2 & A1 fi
        // how can we treat it
        else if(ca instanceof IfGuardedCommand) {
          // an assignment command should not be a parent
          CircusActionList cal = ((IfGuardedCommand)ca).getGuardedActionList();
          for(CircusAction c: cal) {
            if(c.equals(term)) {
              cal.remove(c);
              cal.add(cca);
            }
          }
          ((IfGuardedCommand)ca).setActionList(cal);
        }
        // SpecStmtCommand
        else if(ca instanceof SpecStmtCommand) {
          // a SpecStmtCommand command should not be a parent
        }
        // VarDeclCommand
        else if(ca instanceof VarDeclCommand) {
          if(((VarDeclCommand)ca).getCircusAction().equals(term)) {
            ((VarDeclCommand)ca).setCircusAction(cca);
          } 
          else {
            throw new CztException("CallAction [" + 
                net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
                "] can not be found from its parent!");
          }
        }
        else {
          throw new CztException("CallAction [" + 
              net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils.termToString(term) +
              "] can not be found from its parent!");
        }
      } // end of ca != null
    } // end of else
  } // end of function
  
  /**
   * Check if a communication is for state retrieve purpose, such as (P_OP_x)
   * 
   * @param c - the communication
   * @return
   */
  private boolean isCommsForStateRetrieve(Communication c)
  {
    boolean ret = false;
    
    if(c.getCommPattern() == CommPattern.Input) {
      if(c.getCircusFieldList().size() == 1 && c.getChannelExpr().getZExprList().isEmpty()) {        
        // a set of state variables
        List<String> lst_stvar = map_.getStatList(para_name_);
        Set<String> set_stvar = new HashSet<String>();
        
        for(String v: lst_stvar) {
          // P_OP_v
          String st_para = MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_,
              MessageFormat.format(FormatPattern.STATE_RETR_PARA_NAME_PATT, v));
          set_stvar.add(st_para);
        }
        
        if(set_stvar.contains(
            Circus2ZCSPUtils.termToString(c.getChannelExpr().getZName())
            )
          ) {
          ret = true;
        }
      }
     
    }
    return ret;
  }
  
  /**
   * Remove the prefix communications (Rpre) for state retrieve purpose (P_OP_x, P_OP_y ...) from 
   * the prefixing action, return the action after and a set of removed communications
   * @param pa  - prefixing action
   * @param sc  - [OUT] a set of communication removed from pa
   * @return
   */
  private CircusAction removeRpreFromPrefixingAction(PrefixingAction pa, Set<Communication> sc)
  {
    CircusAction ca = pa;
    
    while(ca instanceof PrefixingAction) {
      if (isCommsForStateRetrieve(((PrefixingAction)ca).getCommunication())) {
        sc.add(((PrefixingAction)ca).getCommunication());
        ca = ((PrefixingAction)ca).getCircusAction();
      }
      else {
        break;
      }
    }

    return ca;
  }
  
  /**
   * This function aims to merge and/or update Rpre and Rpost of the rewrite of actions
   * @param term - [IN/OUT] 
   *            IN: the rewritten actions in its left/right actions or its action
   *            OUT: its parent is updated to have the form
   *                    Rmrg(Rpre(A1), Rpre(A2)) -> (Rpost(A1) op Rpost(A2))
   *                 or
   *                    Rpre(A) -> (Rpost(A))
   */
  private void mergeAndUpdateRpreOfTerm(CircusAction term)
  {
    // 1. implement the rewrite of the form (A1 op A2)
    //  Rmrg(Rpre(A1), Rpre(A2)) -> (Rpost(A1) op Rpost(A2))
    // it is for Action2 (
    //          ExtChoiceAction, 
    //          IntChoiceAction,
    //          ParallelAction,
    //          InterleaveAction,
    //  not for 
    //          SeqAction
    //  )
    if(term instanceof Action2) {
      if(term instanceof SeqAction) {
        return;
      }
      
      // if term is not one of these action
      if(!((term instanceof ExtChoiceAction) || 
          (term instanceof IntChoiceAction) ||
          (term instanceof ParallelAction) ||
          (term instanceof InterleaveAction))
        ) {
        return;
      }
      
      // merge the Rpre of A1 and A2
      // 1. remove from current actions
      CircusAction left = ((Action2)term).getLeftAction();
      CircusAction right = ((Action2)term).getRightAction();
      Set<Communication> setCLeft = new HashSet<Communication>();
      Set<Communication> setCRight = new HashSet<Communication>();
      
      // if it is a prefix, remove its Rpre
      // if it is a sequence but the first action is prefix
      if(left instanceof PrefixingAction) {
        left = removeRpreFromPrefixingAction((PrefixingAction)left, setCLeft);
      }
      else if(left instanceof SeqAction) {
        SeqAction seqLeft = (SeqAction)left;
        CircusAction lleft = null;
        if(seqLeft.getLeftAction() instanceof PrefixingAction) {
          lleft = removeRpreFromPrefixingAction((PrefixingAction)seqLeft.getLeftAction(), setCLeft);
          seqLeft.setLeftAction(lleft);
        }
      }
      
      // if it is a prefix, remove its Rpre
      if(right instanceof PrefixingAction) {
        right = removeRpreFromPrefixingAction((PrefixingAction)right, setCRight);
      }
      // if it is a sequence but the first action is prefix
      else if(right instanceof SeqAction) {
        SeqAction seqRight = (SeqAction)right;
        CircusAction lright = null;
        if(seqRight.getLeftAction() instanceof PrefixingAction) {
          lright = removeRpreFromPrefixingAction((PrefixingAction)seqRight.getLeftAction(), setCRight);
          seqRight.setLeftAction(lright);
        }
      }
      
      ((Action2)term).setLeftAction(left);
      ((Action2)term).setRightAction(right);
      
      // 2. merge
      setCLeft.addAll(setCRight);
      
      // 3. add to the prefix of current external choice
      PrefixingAction pa = cfac_.createPrefixingAction();
      for(Communication c: setCLeft) {
        if(pa.getCircusAction() == null) {
          pa.setCommunication(c);
          pa.setCircusAction(term);
        } 
        else {
          PrefixingAction tpa = cfac_.createPrefixingAction();
          tpa.setCommunication(c);
          tpa.setCircusAction(pa);
          pa = tpa;
        }
      }
      
      if(pa.getCircusAction() != null) {
        updateParentAction(term, pa);
      }
    }
    else if(term instanceof Action1) {
      // 2. implement the rewrite of the form (A)
      //  Rpre(A1) -> (Rpost(A))
      // it is for Action1 (
      //          HideAction,
      //          ExtChoiceActionIte,
      //          IntChoiceActionIte,
      //          SeqActionIte,
      //          ParallelActionIte,
      //          InterleaveActionIte,
      //  not for 
      //          GuardedAction
      //          MuAction
      //          ParamAction
      //          PrefixingAction
      //          RenameAction
      //          SubstitutionAction
      //  )
      
      // if term is not one of these action
      if(!((term instanceof HideAction) || 
          (term instanceof ExtChoiceActionIte) ||
          (term instanceof IntChoiceActionIte) ||
          (term instanceof SeqActionIte) ||
          (term instanceof ParActionIte))
        ) {
        return;
      }
      
      Set<Communication> setCommsInDecl = new HashSet<Communication>();

      // their declaration may also have state variables, such as
      // [] x: (\dom~s1) @ A    ---- where its type contains access of s1
      if(((term instanceof ExtChoiceActionIte) ||
          (term instanceof IntChoiceActionIte) ||
          (term instanceof SeqActionIte) ||
          (term instanceof ParActionIte))
        ) 
      {
        // 1. get which state components are evaluated in guarded condition.
        ZNameSetVisitor znsv = new ZNameSetVisitor();
        
        // a set of state variables
        List<String> lst_stvar = map_.getStatList(para_name_);
        Set<String> set_stvar = new HashSet<String>();
        set_stvar.addAll(lst_stvar);
        
        // a set of state variables used in the channel expression
        Set<String> set_stvar_used = new HashSet<String>();
        
        ActionIte act = (ActionIte)term;
        for(Decl decl: act.getZDeclList()) {
          if(decl instanceof VarDecl) {
            znsv.clear();
            ((VarDecl)decl).getExpr().accept(znsv);
            Set<String> nset = znsv.getStrSet();
            // intersection of nset and set_stvar to get all state variables used
            nset.retainAll(set_stvar);
            set_stvar_used.addAll(nset);
          }
        }
        
        for(String v: set_stvar_used) {
          // P_OP_x
          String st_para = MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_,
              MessageFormat.format(FormatPattern.STATE_RETR_PARA_NAME_PATT, v));
          
          // check if it has been added to CSP or not. If not, just add it to CSP
          Pair<Expr, Boolean> p = visited_state_op_.get(st_para);
          if(p != null && p.getSecond().equals(Boolean.FALSE)) {
            addStateRetrieveEventToCSP(new Pair<String, Expr>(st_para, p.getFirst()));
          }
          
          // create Schema Expr
          RefExpr re = cfac_.createRefExpr(
              fac_.createZName(st_para, fac_.createZStrokeList(), null), 
              cfac_.createZExprList(), false, false);
          SchExprAction sea = cfac_.createSchExprAction(re);
          
          // (P_OP_x) is expressed as P_OP_x?x channel
          List<Field> lstField = new ArrayList<Field>();
          // ?x
          Field f = cfac_.createInputField(
              cfac_.createZName(v, cfac_.createZStrokeList(), null), 
              cfac_.createTruePred());
          lstField.add(f);
          CircusFieldList cFldList = cfac_.createCircusFieldList(lstField);
          Communication c = cfac_.createCommunication();
          c.setChannelExpr(re);
          c.setFieldList(cFldList);
          c.setCommUsage(CommUsage.Normal);
          c.setCommPattern(CommPattern.Input);
          c.setIndexed(false);
          c.setMultiSych(BigInteger.valueOf(0));
          setCommsInDecl.add(c);
        }
      }
      
      CircusAction ca = ((Action1)term).getCircusAction();
      Set<Communication> setC = new HashSet<Communication>();
      
      if(ca instanceof PrefixingAction) {
        ca = removeRpreFromPrefixingAction((PrefixingAction)ca, setC);
      }
      
      ((Action1)term).setCircusAction(ca);
      
      setC.addAll(setCommsInDecl);
      
      // add to the prefix of current external choice
      PrefixingAction pa = cfac_.createPrefixingAction();
      for(Communication c: setC) {
        if(pa.getCircusAction() == null) {
          pa.setCommunication(c);
          pa.setCircusAction(term);
        } 
        else {
          PrefixingAction tpa = cfac_.createPrefixingAction();
          tpa.setCommunication(c);
          tpa.setCircusAction(pa);
          pa = tpa;
        }
      }
      
      if(pa.getCircusAction() != null) {
        updateParentAction(term, pa);
      }
    }
    else if(term instanceof CircusCommand) { 
      // 2. implement the rewrite of the form (A)
      //  Rpre(A1) -> (Rpost(A))
      // it is for CircusCommand (
      //          VarDeclCommand,
      //  not for 
      //          Assignment
      //          CircusGuardedCommand
      //          SpecStmtCommand
      //  )
      
      if(! (term instanceof VarDeclCommand)) {
        return;
      }
      
      CircusAction ca = ((VarDeclCommand)term).getCircusAction();
      Set<Communication> setC = new HashSet<Communication>();
      
      if(ca instanceof PrefixingAction) {
        ca = removeRpreFromPrefixingAction((PrefixingAction)ca, setC);
      }
      
      ((VarDeclCommand)term).setCircusAction(ca);
      
      // add to the prefix of current external choice
      PrefixingAction pa = cfac_.createPrefixingAction();
      for(Communication c: setC) {
        if(pa.getCircusAction() == null) {
          pa.setCommunication(c);
          pa.setCircusAction(term);
        } 
        else {
          PrefixingAction tpa = cfac_.createPrefixingAction();
          tpa.setCommunication(c);
          tpa.setCircusAction(pa);
          pa = tpa;
        }
      }
      
      if(pa.getCircusAction() != null) {
        updateParentAction(term, pa);
      }
    }
  }
  
  /**
   * Check if the variable n is a local variable or not
   * @param n
   * @return
   */
  private boolean isLocVar(ZName n)
  {
    int size = loc_vars_stack_.size();
    String v = Circus2ZCSPUtils.termToString(n);
    
    for(int i = 0; i < size; i++) {
      Pair<String, Term> p = loc_vars_stack_.get(i);
      if(p.getFirst().equals(v)) {
        return true;
      }
    }
    return false;
  }
  
  /**
   * Check if the variable v is a local variable or not
   * @param v
   * @return
   */
  private boolean isLocVar(String v)
  {
    int size = loc_vars_stack_.size();
    
    for(int i = 0; i < size; i++) {
      Pair<String, Term> p = loc_vars_stack_.get(i);
      if(p.getFirst().equals(v)) {
        return true;
      }
    }
    return false;
  }
  
  /**
   * Check if there is local variables in the term. If so, return a list of variables' name and its type
   * @param term - term
   * @param lstp - a list of pairs from variable name to its type
   * @return
   */
  private boolean isLocVar(Term term, List<Pair<String, Term>> lstp)
  {
    boolean ret = false;
    int size = loc_vars_stack_.size();
    
    ZNameSetVisitor znsv = new ZNameSetVisitor();
    term.accept(znsv);
    Set<String> nameset = znsv.getStrSet();
    
    lstp.clear();
    for(int i = 0; i < size; i++) {
      Pair<String, Term> p = loc_vars_stack_.get(i);
      if(nameset.contains(p.getFirst())) {
        lstp.add(new Pair<String, Term>(p.getFirst(), p.getSecond()));
        ret = true;
      }
    }
    return ret;
  }
  
  /**
   * Check if there is state variables in the term. If so, return a list of variables' name and its type
   * @param term - term
   * @param lstp - a list of pairs from variable name to its type
   * @return
   */
  private boolean isStateVar(Term term, List<Pair<String, Term>> lstp)
  {
    boolean ret = false;
    
    /**
     * a list of state variables
     */
    List<Pair<String, Term>> lstPState = map_.getStatListWithExp(para_name_);
    
    ZNameSetVisitor znsv = new ZNameSetVisitor();
    term.accept(znsv);
    Set<String> nameset = znsv.getStrSet();
    
    lstp.clear();
    for(Pair<String, Term> p: lstPState) {
      if(nameset.contains(p.getFirst())) {
        lstp.add(p);
        ret = true;
      }
    }
    return ret;
  }
  
  public AxPara assembleZPara(String paraName, Pred pred, ZDeclList declList)
  {
    return assembleZPara(paraName, pred, declList, true);
  }
  
  /**
   * Assemble a Z paragraph (\Delta) according to inputs (with Input and output variables)
   * 
   * @param paraName - paragraph name
   * @param pred - predicate
   * @param declList - ZDeclList (input and output Decl list)
   * @return
   */
  public AxPara assembleZPara(String paraName, Pred pred, ZDeclList declList, boolean delta)
  {
    ZNameList fp = fac_.createZNameList();
    // ZName
    ZName paraname = fac_.createZName(paraName, fac_.createZStrokeList(), null);

    // State Paragraph Name and \Delta State Paragraph
    String stName = map_.getStatPara(para_name_);
    String newStName = MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_, stName);
    ZName stname;
    if(delta) {
      stname = fac_.createZName(ZString.DELTA + newStName, fac_.createZStrokeList(), null);
    }
    else {
      stname = fac_.createZName(ZString.XI + newStName, fac_.createZStrokeList(), null);
    }
    
    RefExpr expr = fac_.createRefExpr(stname, fac_.createZExprList(), false, false);

    // insert InclDecl in the beginning of declList and shift current to right
    InclDecl inclDecl = fac_.createInclDecl(expr);
    declList.add(0, inclDecl);

    ZSchText schText = fac_.createZSchText(declList, pred);
    SchExpr schExpr = fac_.createSchExpr(schText);

    ConstDecl cd = fac_.createConstDecl(paraname, schExpr);

    ZDeclList declList0 = fac_.createZDeclList();
    declList0.add(cd);
    SchText st = fac_.createZSchText(declList0, null);

    AxPara axpara = fac_.createAxPara(fp, st, Box.OmitBox);

    return axpara;
  }
   
  /**
   * Recursively search if in a CircusAction, it contains its ownname as well.
   * @param nameOfActionDef - name of action definition
   * @param ca - circus action to search
   * @return
   *    true - if there is implicitly defined recursion
   */
  private boolean isAPossibleMutualRecursion(ZName nameOfActionDef, CircusAction ca)
  {
    boolean ret = false;
    if(ca instanceof CallAction) {
      if(Circus2ZCSPUtils.isEquals(((CallAction)ca).getZName(), nameOfActionDef)) {
        return true;
      }
      else {
        return false;
      }
    }
    else {
      Object[] args = ca.getChildren();
      for(Object o: args) {
        if(o instanceof CircusAction) {
          if(o instanceof CallAction) {
            if(Circus2ZCSPUtils.isEquals(((CallAction)o).getZName(), nameOfActionDef)) {
              ret = true;
              return ret;
            }
            else {
              // another CallAction, then expand it
              for(Para p: process_para_.getCircusBasicProcess().getZParaList()) {
                if(p instanceof ActionPara) {
                  if(Circus2ZCSPUtils.isEquals(((ActionPara) p).getZName(), ((CallAction)o).getZName())) {
                     ret = isAPossibleMutualRecursion(nameOfActionDef, ((ActionPara) p).getCircusAction());
                     if(ret) {
                       return ret;
                     }
                  }
                }
              }
            }
          }
          else {
            ret = isAPossibleMutualRecursion(nameOfActionDef, (CircusAction) o);
            if(ret) {
              return true;
            }
          }
        }
        else if(o instanceof ListTerm) {
          for(Object in: ((ListTerm)o)) {
            if(in instanceof CircusAction) {
              ret = isAPossibleMutualRecursion(nameOfActionDef, (CircusAction) in);
              if(ret) {
                return true;
              }
            }
          }
        }
      }
    }
    
    return ret;
  }
}




package net.sourceforge.czt.circus2zcsp.visitor;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus.ast.ActionIte;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.ChannelDecl;
import net.sourceforge.czt.circus.ast.ChannelPara;
import net.sourceforge.czt.circus.ast.ChannelSetPara;
import net.sourceforge.czt.circus.ast.Field;
import net.sourceforge.czt.circus.ast.InputField;
import net.sourceforge.czt.circus.ast.MuAction;
import net.sourceforge.czt.circus.ast.NameSetPara;
import net.sourceforge.czt.circus.ast.PrefixingAction;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.ast.SchExprAction;
import net.sourceforge.czt.circus.visitor.ActionIteVisitor;
import net.sourceforge.czt.circus.visitor.BasicProcessVisitor;
import net.sourceforge.czt.circus.visitor.ChannelParaVisitor;
import net.sourceforge.czt.circus.visitor.ChannelSetParaVisitor;
import net.sourceforge.czt.circus.visitor.MuActionVisitor;
import net.sourceforge.czt.circus.visitor.PrefixingActionVisitor;
import net.sourceforge.czt.circus.visitor.ProcessParaVisitor;
import net.sourceforge.czt.circus.visitor.SchExprActionVisitor;
import net.sourceforge.czt.circus2zcsp.Debug;
import net.sourceforge.czt.circus2zcsp.data.CSPPredExpPattern;
import net.sourceforge.czt.circus2zcsp.data.CircusSpecMap;
import net.sourceforge.czt.circus2zcsp.data.Node;
import net.sourceforge.czt.circus2zcsp.data.PredExpPattern;
import net.sourceforge.czt.circus2zcsp.util.AxParaKind;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Freetype;
import net.sourceforge.czt.z.ast.FreetypeList;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NewOldPair;
import net.sourceforge.czt.z.ast.OutStroke;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.QntExpr;
import net.sourceforge.czt.z.ast.QntPred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.RenameExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZBranchList;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZFreetypeList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.WarningManager;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.QntExprVisitor;
import net.sourceforge.czt.z.visitor.QntPredVisitor;
import net.sourceforge.czt.z.visitor.RenameExprVisitor;
import net.sourceforge.czt.z.visitor.SchExprVisitor;
import net.sourceforge.czt.z.visitor.ZNameVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;

/**
 * A visitor to generate a map of definition in whole Circus program
 * <ul>
 * <li> Element in map is composed of (DefName, the process belonging) with the type (ZName, Process). </li>
 *      <ul>
 *      <li> Process is null if DefName is globally defined.</li>
 *      </ul>
 * <li> A map between an element and a set of elements that the element refers in its definition. </li>
 *      <ul>
 *      <li> if the set of elements is null, it means the element is a leaf in the tree.</li>
 *      <li> if the set of elements is empty, it means the element is a leaf in the tree.</li>
 *      </ul>
 * </ul>
 *  
 * @author rye
 *
 */
public class DefinitionReferencesMapVisitor
  implements
  TermVisitor<Object>,
  ZSectVisitor<Object>,
  GivenParaVisitor<Object>,
  FreeParaVisitor<Object>,
  ProcessParaVisitor<Object>,
  ZNameVisitor<Object>,
  ChannelParaVisitor<Object>,
  BasicProcessVisitor<Object>,
  AxParaVisitor<Object>,
  SchExprActionVisitor<Object>,
  MuActionVisitor<Object>,
  SchExprVisitor<Object>,
  PrefixingActionVisitor<Object>,
//  ForallPredVisitor<Object>,
//  ForallExprVisitor<Object>,
//  ExistsPredVisitor<Object>,
//  Exists1PredVisitor<Object>,
//  ExistsExprVisitor<Object>,
//  Exists1ExprVisitor<Object>,
//  SetCompExprVisitor<Object>
  QntExprVisitor<Object>,
  QntPredVisitor<Object>,
  ChannelSetParaVisitor<Object>,
  RenameExprVisitor<Object>,
  ActionIteVisitor<Object>
{
  private final Visitor<Object> visitor_ = this;
  WarningManager warning_manager_ = new WarningManager();
  
  /**
   * A reference map
   */
  private final Map<Node, Set<Node>> refmap_;
  
  /**
   * Current process paragraph in processing
   */
  private ProcessPara process_para_;
  
  /**
   * mu action name stack  
   */
  private Stack<ZName> muaction_name_stack_ = new Stack<ZName>();
  
  /**
   * Local variable name stack
   */
  private Stack<ZName> loc_var_stack_ = new Stack<ZName>();
  
  /**
   * These are predefined name and should not be regarded as reference
   */
  private final static String[] predefine_name_ = new String[] {
    ZString.NUM,
    ZString.NUM + ZString.SUB1,
    ZString.NAT, 
    ZString.NAT + ZString.SUB1, 
    ZString.TRUE, "True",
    ZString.FALSE, "False",
    CSPPredExpPattern.getPattern(PredExpPattern.BOOLEAN),
    ZString.ARITHMOS,
    ZString.EMPTYSET,
    "$$SYNCH"
  };
  /**
   * For predefined names, we just ignore it when referring
   */
  private static final Set<String> predefine_name1_ = new HashSet<String>(Arrays.asList(predefine_name_));
  
  /**
   * a set of Node in
   */
  private Set<Node> set_node_;
  
  private CircusSpecMap map_ = null;
  
  private final SectionManager manager_;
  
  private String section_name_;
  private ZSect zsect_;
  
  /**
   * Old and new name pair stack for RenameExpr  
   */
  private Stack<NewOldPair> rename_oldnew_stack_ = new Stack<NewOldPair>();
  
  public DefinitionReferencesMapVisitor(CircusSpecMap map, SectionManager manager, String section_name) 
  {
    map_          = map;
    refmap_       = new TreeMap<Node, Set<Node>>();
    process_para_ = null;
    set_node_     = new HashSet<Node>();
    manager_      = manager;
    section_name_ = section_name;
  }
  
  private void clearSetNode()
  {
    set_node_.clear();
  }
  
  private Set<Node> safe_visit(Term t) 
  {
    clearSetNode();
    visit(t);
    Set<Node> setNode = new HashSet<Node>();
    setNode.addAll(set_node_);
    return setNode;
  }
  
  /**
   * Add an entry with empty Set<Node> to node
   * @param node
   */
  private void addToRefMap(Node node)
  {
    addToRefMap(node, new HashSet<Node>());
  }
  
  /**
   * Add entry to the refmap_
   * @param node
   * @param setNode
   */
  private void addToRefMap(Node node, Set<Node> setNode)
  {
    refmap_.put(node, setNode);
    
    String strSet = "[";
    
    if(setNode != null) {      
      for(Node n: setNode) {
        strSet += "(" + n.getName().toString() + ", " + 
            ((n.getProcess() == null)? "null": n.getProcess().toString()) + ") ";
      }
    }
    else {
      strSet += "null";
    }
    strSet += "]";
    
    Debug.debug_print(
        Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
        Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
        Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
        "Put [" + node.getName().toString() + ", " + 
        ((node.getProcess() == null)? "null": node.getProcess().toString()) +
        "]: " + strSet);
  }
  
  private void addToLocVarStack(ZName name) 
  {
    name.setId(null);
    loc_var_stack_.push(name);
  }
  
  private boolean isLocVarStackContain(ZName name) 
  {
    for(ZName zn: loc_var_stack_) {
      if(Circus2ZCSPUtils.isEquals(zn, name)) {
        return true;
      }
    }
    return false;
  }
  
  private void addToMuActionStack(ZName name) 
  {
    name.setId(null);
    muaction_name_stack_.push(name);
  }
  
  private boolean isMuActionStackContain(ZName name) 
  {
    for(ZName zn: muaction_name_stack_) {
      if(Circus2ZCSPUtils.isEquals(zn, name)) {
        return true;
      }
    }
    return false;
  }
  
  public Map<Node, Set<Node>> getRefMap()
  {
    Circus2ZCSPUtils.printRefMap(refmap_);
    return refmap_;
  }
  
  protected Object visit(Term t)
  {
    if (t != null) {
      return t.accept(visitor_);
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

  @Override
  public Object visitZSect(ZSect term)
  {
    section_name_ = term.getName();
    zsect_ = term;
    
    for(Para p: term.getZParaList()) {
      if(p instanceof ProcessPara) {
        visit(p);
      }
      else if(p instanceof AxPara) {
        visit(p);
      }
      else if(p instanceof ChannelPara) {
        visit(p);
      }
      else if(p instanceof ChannelSetPara) {
        visit(p);
      }
      else if(p instanceof FreePara) {
        visit(p);
      }
      else if(p instanceof GivenPara) {
        visit(p);
      }
      else if(p instanceof NameSetPara) {
        visit(p);
      }
      else {
        // skip
      }
//      Circus2ZCSPUtils.printRefMap(refmap_);
    }
    return null;
  }

  @Override
  public Object visitFreePara(FreePara term)
  {
    FreetypeList ftl = term.getFreetypeList();
    
    for(Freetype ft: (ZFreetypeList)ftl) {
      ZName name = ft.getZName();
      // a set of nodes that only include this freetype name
      Set<Node> setNode = new HashSet<Node>();
      // set of nodes that this free type relies on
      Set<Node> setNodeFT = new HashSet<Node>();
      Node ftNode = new Node(name, process_para_);
      setNode.add(ftNode);
      
      for(Branch b: (ZBranchList)ft.getBranchList()) {
        if(b.getExpr() == null) {
          // basic
          Node n = new Node(b.getZName(), process_para_);
          addToRefMap(n, setNode);
//          setNode.add(n);
        }
        else {
          Node n = new Node(b.getZName(), process_para_);
          Set<Node> setNode2 = safe_visit(b.getExpr());
          setNodeFT.addAll(setNode2);
          setNode2.addAll(setNode);
          addToRefMap(n, setNode2);
//          setNode.add(n);
        }
      }
      
      addToRefMap(ftNode, setNodeFT);
//      addToRefMap(new Node(name, process_para_), setNode);
    }
    
    return null;
  }

  @Override
  public Object visitGivenPara(GivenPara term)
  {
    for(Name n: term.getZNameList()) {
      // a leaf for given set
      addToRefMap(new Node((ZName) n, process_para_));
    }
    return null;
  }

  @Override
  public Object visitProcessPara(ProcessPara term)
  {
    process_para_ = term;
    
    // add a process paragraph to the map
    addToRefMap(new Node(term.getZName(), (ZName)null), safe_visit(term.getCircusProcess()));
    
    process_para_ = null;
    return null;
  }

  @Override
  public Object visitZName(ZName term)
  {
    if(term.getOperatorName() != null) {
      // for operator, just ignore it
      return null;
    }

    // remove Delta or Xi
    if(ZUtils.isDeltaXi(term)) {
      term = ZUtils.getSpecialSchemaBaseName(term);
    }
    
    // ignore local variable name
    if(isMuActionStackContain(term)) {
      return null;
    }
    
    if(isLocVarStackContain(term)) {
      return null;
    }

    StringBuilder result = new StringBuilder(Circus2ZCSPUtils.termToString(term));
    // TODO: is it necessary to include strokes?
    
//    result.append(Circus2ZCSPUtils.getStrokes(term.getZStrokeList()));
    
    if(predefine_name1_.contains(result.toString())) {
      // ignore it
      return null;
    }
        
    // ignore channel name
    Set<String> channels = map_.getAllChannels();
    if(channels.contains(result.toString())) {
      // ignore it
      return null;
    }
    
    // ignore state component names
    List<String> stVars = map_.getStatListWithProName();
    if(stVars.contains(result.toString())) {
      // ignore it
      return null;
    }
    
    // check if it is old name in rename_oldnew_stack_
    for(NewOldPair p: rename_oldnew_stack_) {
      if(Circus2ZCSPUtils.isEquals(p.getOldName(), term)) {
        visit(p.getNewName());
        return null;
      }
    }
    
    // search from existing map at first
    Set<Node> setNode = new HashSet<Node>();
    Node n = Circus2ZCSPUtils.getADefFromMap(refmap_, term, process_para_, setNode);
    
    if(n == null) {
//      warning_manager_.warn("The definition of [" + result.toString() + "] is not found!");
    }
    else {
      // remove duplicate entry
      if(!set_node_.contains(n)) {
        set_node_.add(n);
      }
    }
    
    return null;
  }

  @Override
  public Object visitChannelPara(ChannelPara term)
  {
    for(Decl decl: term.getZDeclList()) {
      if(decl instanceof ChannelDecl) {
        ChannelDecl cd = (ChannelDecl)decl;
        for(Name n: cd.getZChannelNameList()) {
          addToRefMap(new Node((ZName)n, process_para_), safe_visit(cd.getExpr()));
        }
      }
    }
    
    return null;
  }

  @Override
  public Object visitBasicProcess(BasicProcess term)
  {
    ZParaList zpl = term.getZParaList();
    List<Para> lstParaToRemove = new ArrayList<Para>();
    
    for(Para p: zpl) {
      if(p instanceof AxPara) {
        visit(p);
      }
      else if(p instanceof ActionPara) {
        if(!((ActionPara)p).getCircusAction().equals(term.getMainAction())) {
          lstParaToRemove.add(p);
        }
      }
    }
    
    // only keep its main action visit to the process name
    safe_visit(term.getMainAction());

    zpl.removeAll(lstParaToRemove);
    term.setParaList(zpl);

    return null;
  }

  @Override
  public Object visitAxPara(AxPara term)
  {
    AxParaKind kind = Circus2ZCSPUtils.getAxParaKind(term);
    ZName name;
    Expr expr;
    SchExpr schExpr = null;
    
    int cnt = 0;
    DeclListExpansionVisitor dlevisitor = null;
    Set<Pair<ZName, Expr>> lstZNameExpr = null;

    
    switch(kind) {
      case ABBR:
        name = (ZName) ZUtils.getAbbreviationName(term);
        expr = ZUtils.getAbbreviationExpr(term);
        
        if(process_para_ != null) {
          BasicProcess bp = process_para_.getCircusBasicProcess();
          dlevisitor = new DeclListExpansionVisitor(bp, zsect_, manager_, section_name_);
        }
        else {
          dlevisitor = new DeclListExpansionVisitor(zsect_, manager_, section_name_);
        }

     // after renaming, normalisation might not work properly, so disable it
        dlevisitor.disableNormalisation();
        term.accept(dlevisitor);
        lstZNameExpr = dlevisitor.getNameExprPair();
        for(Pair<ZName, Expr> p: lstZNameExpr) {
          addToLocVarStack(p.getFirst());
          cnt++;
        }

//        schExpr = Circus2ZCSPUtils.expansionSchema(expr, section_name_, manager_);
//
        addToRefMap(new Node(name, process_para_), safe_visit(expr));
        
        for(int i = 0; i < cnt; i++) {
          loc_var_stack_.pop();
        }
        
        break;
      case AXDEF:
        ZDeclList list = ZUtils.getAxBoxDecls(term);
        Pred pred = ZUtils.getAxBoxPred(term);
        Set<Node> setPred = new HashSet<Node>();
        
        for(Decl decl: list) {
          if(decl instanceof VarDecl) {
            VarDecl vd = (VarDecl)decl;
            for(Name n: vd.getZNameList()) {
              addToLocVarStack((ZName) n);
              cnt++;
            }
          }
        }
        
        setPred.addAll(safe_visit(pred));
        
        for(Decl decl: list) {
          if(decl instanceof VarDecl) {
            VarDecl vd = (VarDecl)decl;
            Set<Node> setExpr = safe_visit(vd.getExpr());
            setPred.addAll(setExpr);
            for(Name n: vd.getZNameList()) {
              // for each variable, we add the references to its expression and predicate as well.
              addToRefMap(new Node((ZName)n, process_para_), setPred);
            }
          }
        }
        
        for(int i = 0; i < cnt; i++) {
          loc_var_stack_.pop();
        }
        
        break;
      case BOXED_SCHEMA:
      case HORIZON_SCHEMA:
        name = (ZName) ZUtils.getAxParaSchOrAbbrName(term);
        expr = ZUtils.getSchemaDefExpr(term);
//        schExpr = Circus2ZCSPUtils.expansionSchema(expr, section_name_, manager_);
//        addToRefMap(new Node(name, process_para_), safe_visit((schExpr != null)? schExpr: expr));
        
        dlevisitor = null;
        if(process_para_ != null) {
          BasicProcess bp = process_para_.getCircusBasicProcess();
          dlevisitor = new DeclListExpansionVisitor(bp, zsect_, manager_, section_name_);
        }
        else {
          dlevisitor = new DeclListExpansionVisitor(zsect_, manager_, section_name_);
        }

        // after renaming, normalisation might not work properly, so disable it
        dlevisitor.disableNormalisation();
        term.accept(dlevisitor);
        lstZNameExpr = dlevisitor.getNameExprPair();
        for(Pair<ZName, Expr> p: lstZNameExpr) {
          addToLocVarStack(p.getFirst());
          cnt++;
        }

//        schExpr = Circus2ZCSPUtils.expansionSchema(expr, section_name_, manager_);
//
        addToRefMap(new Node(name, process_para_), safe_visit(expr));
        
        for(int i = 0; i < cnt; i++) {
          loc_var_stack_.pop();
        }

        break;
      default:
          break;
    }
    return null;
  }

  @Override
  public Object visitSchExprAction(SchExprAction term)
  {
    // for reference, we ignore SchExprAction since it will become a part of channel declaration in the later stage when linked to CSP
    ZName name = null;
    
    if(term.getExpr() instanceof RefExpr) {
      name = ((RefExpr)term.getExpr()).getZName();
    }
    else {
      throw new CztException("Only RefExpr is allowed fro SchExprAction, but this is " 
          + term.getExpr().getClass().getName());
    }
    
    AxPara schPara = null;
    
    for(Para para: process_para_.getCircusBasicProcess().getZParaList()) {   
      boolean found = false;
      if(para instanceof AxPara) {
        switch(Circus2ZCSPUtils.getAxParaKind((AxPara) para)) {
          case AXDEF:
            break;
          case ABBR:
          case BOXED_SCHEMA:
          case HORIZON_SCHEMA:
            ZName pname = (ZName) ZUtils.getAxParaSchOrAbbrName((Term)para);
            if(Circus2ZCSPUtils.isEquals(pname, name)) {
              schPara = (AxPara) para;
              found = true;
            }
            break;
          default:
            throw new CztException("AxPara after rewritting can not be a " + Circus2ZCSPUtils.getAxParaKind((AxPara) para).toString());
        }
      }
      if (found) break;
    }
    
    // TODO: 
    // get declaration list
    DeclListExpansionVisitor dlevisitor = 
        new DeclListExpansionVisitor(process_para_.getCircusBasicProcess(), zsect_, manager_, section_name_);
    // after renaming, normalisation might not work properly, so disable it
    dlevisitor.disableNormalisation();
    schPara.accept(dlevisitor);
    List<Pair<ZName, Expr>> lstZNameExpr = dlevisitor.getNameExprPairAsList();
    
    for(Pair<ZName, Expr> p: lstZNameExpr) {
      // check if it is input variable (v?)
      if(p.getFirst().getZStrokeList().size() > 0 && 
          p.getFirst().getZStrokeList().get(p.getFirst().getZStrokeList().size() - 1) instanceof InStroke) {
        visit(p.getSecond());
      }

      // check if it is input variable (v!)
      if(p.getFirst().getZStrokeList().size() > 0 && 
          p.getFirst().getZStrokeList().get(p.getFirst().getZStrokeList().size() - 1) instanceof OutStroke) {
        visit(p.getSecond());
      }
    }

//    SchemaExprInOutsVisitor visitor = new SchemaExprInOutsVisitor(section_name_, manager_);
//    if(schPara != null) {
//      schPara.accept(visitor);
//    }
//    else{
//      throw new CztException("Can not find the corresponding schema [" + 
//          Circus2ZCSPUtils.termToString(name) + "] in " + 
//          Circus2ZCSPUtils.termToString(process_para_.getZName()));
//    }
//    
//    List<Pair<String, Term>> lstPInOut = visitor.getInOutExpr();
//    
//    for(Pair<String, Term> p: lstPInOut) {
//      visit(p.getSecond());
//    }
    
//    visit(term.getExpr());
//    
//    assert(process_para_.getCircusProcess() instanceof BasicProcess);
//    
//    for(Para p: process_para_.getCircusBasicProcess().getZParaList()) {
//      if(p instanceof AxPara) {
//        AxParaKind kind = Circus2ZCSPUtils.getAxParaKind((AxPara)p);
//        if(!(kind == AxParaKind.ABBR || 
//            kind == AxParaKind.BOXED_SCHEMA || 
//            kind == AxParaKind.HORIZON_SCHEMA)) {
//          continue;
//        }
//        
//        ZName apName = (ZName) ZUtils.getAxParaSchOrAbbrName(p);
//        apName.setId(null); 
//        name.setId(null);
//        if(apName.equals(name)) {
//          SchExpr schExpr;
//          if(kind == AxParaKind.ABBR) {
//            schExpr = Circus2ZCSPUtils.expansionSchema(ZUtils.getAbbreviationExpr((AxPara)p), section_name_, manager_);
//          }
//          else {
//            schExpr = Circus2ZCSPUtils.expansionSchema(ZUtils.getSchemaDefExpr((AxPara)p), section_name_, manager_);
//          }
//          
//          if(schExpr == null) {
//            // we can not expand this schema
//          }
//          else {
//            
//          }
//        }
//      }
//    }
    return null;
  }

  @Override
  public Object visitMuAction(MuAction term)
  {
    addToMuActionStack(term.getZName());
    
    visit(term.getCircusAction());
    
    muaction_name_stack_.pop();
    return null;
  }

  @Override
  public Object visitSchExpr(SchExpr term)
  {
    int cnt = 0;
    
    for(Decl decl: term.getZSchText().getZDeclList()) {
      if(decl instanceof VarDecl) {
        VarDecl vd = (VarDecl)decl;
        for(Name n: vd.getZNameList()) {
          addToLocVarStack((ZName) n);
          cnt++;
        }
        visit(vd.getExpr());
      }
      else if(decl instanceof InclDecl) {
        visit(((InclDecl)decl).getExpr());
      }
      else {
      }
    }
    
    visit(term.getZSchText().getPred());
    
    for(int i = 0; i < cnt; i++) {
      loc_var_stack_.pop();
    }
    return null;
  }

  @Override
  public Object visitPrefixingAction(PrefixingAction term)
  {
    int cnt = 0;
    visit(term.getCommunication().getChannelExpr());
    
    for(Field f: term.getCommunication().getCircusFieldList()) {
      if (f instanceof InputField) {
        addToLocVarStack(((InputField)f).getVariableZName());
        cnt++;
      }
      else {
        visit(f);
      }
    }
    
    visit(term.getCircusAction());
    
    for(int i = 0; i < cnt; i++) {
      loc_var_stack_.pop();
    }
    
    return null;
  }

  @Override
  public Object visitQntExpr(QntExpr term)
  {
    int cnt = 0;
    for(Decl decl: term.getZSchText().getZDeclList()) {
      if(decl instanceof VarDecl) {
        for(Name n: ((VarDecl)decl).getZNameList()) {
          addToLocVarStack((ZName) n);
          cnt++;
        }
        
        visit(((VarDecl)decl).getExpr());
      }
      else if(decl instanceof InclDecl) {
        visit(((InclDecl)decl).getExpr());
      }
    }
    
    term.getExpr();
    for(int i = 0; i < cnt; i++) {
      loc_var_stack_.pop();
    }
    return null;
  }

  @Override
  public Object visitQntPred(QntPred term)
  {
    int cnt = 0;
    for(Decl decl: term.getZSchText().getZDeclList()) {
      if(decl instanceof VarDecl) {
        for(Name n: ((VarDecl)decl).getZNameList()) {
          addToLocVarStack((ZName) n);
          cnt++;
        }
        
        visit(((VarDecl)decl).getExpr());
      }
      else if(decl instanceof InclDecl) {
        visit(((InclDecl)decl).getExpr());
      }
    }
    
    term.getPred();
    for(int i = 0; i < cnt; i++) {
      loc_var_stack_.pop();
    }
    return null;
  }

  @Override
  public Object visitChannelSetPara(ChannelSetPara term)
  {
    ZName name = term.getZName();
    addToRefMap(new Node(name, process_para_), safe_visit(term.getChannelSet()));
    
    return null;
  }

  @Override
  public Object visitRenameExpr(RenameExpr term)
  {
    int cnt = 0;
    for(NewOldPair p: term.getZRenameList()) {
      rename_oldnew_stack_.push(p);
      cnt++;
    }
    // for schema renaming, we should not visit the original variable name. Instead, we should visit its new name.
    
    visit(term.getExpr());
    
    for(int i = 0; i < cnt; i++) {
      rename_oldnew_stack_.pop();
    }
    return null;
  }

  @Override
  public Object visitActionIte(ActionIte term)
  {
    int cnt = 0;
    
    for(Decl decl: term.getZDeclList()) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          addToLocVarStack((ZName) name);
          cnt++;
        }
      }
    }
    
    visit(term.getCircusAction());
    
    for(int i = 0; i < cnt; i++) {
      loc_var_stack_.pop();
    }

    return null;
  }

}

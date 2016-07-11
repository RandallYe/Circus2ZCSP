package net.sourceforge.czt.circus2zcsp.visitor;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.ListTermVisitor;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus.ast.*;
import net.sourceforge.czt.circus.visitor.CircusVisitor;
import net.sourceforge.czt.circus2zcsp.Debug;
import net.sourceforge.czt.circus2zcsp.ast.CSPSpec;
import net.sourceforge.czt.circus2zcsp.conf.Config;
import net.sourceforge.czt.circus2zcsp.data.CSPPredExpPattern;
import net.sourceforge.czt.circus2zcsp.data.CircusSpecMap;
import net.sourceforge.czt.circus2zcsp.data.FormatPattern;
import net.sourceforge.czt.circus2zcsp.data.LocalVariableEntry;
import net.sourceforge.czt.circus2zcsp.data.Node;
import net.sourceforge.czt.circus2zcsp.data.PredExpPattern;
import net.sourceforge.czt.circus2zcsp.data.Triple;
import net.sourceforge.czt.circus2zcsp.util.AxParaKind;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.circus2zcsp.util.MemPredKind;
import net.sourceforge.czt.circus2zcsp.util.RefExprKind;
import net.sourceforge.czt.circus2zcsp.visitor.CircusRewriteVisitor.pairStringTComparator;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Fixity;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.WarningManager;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.ZVisitor;

/**
 * Visitor for the translation from Circus to CSP
 * @author rye
 *
 */
public class CircusToCSPVisitor
    implements
    TermVisitor<Object>,
    ListTermVisitor<Object>,
    ZVisitor<Object>,
    CircusVisitor<Object>
{
  private final Visitor<Object> visitor_ = this;

  /**
   * for CSP program
   */
  private String str_ = "";
  
  // a map from original variable or schema name to replaced new name
  private CircusSpecMap map_ = null;

  // temporary paragraph name
  private String para_name_ = null;
  
  /**
   * Current processpara in processing
   */
  private ProcessPara process_para_ = null;
  
  private ZSect zsect_ = null;
  
  private String zsectname_ = null;
  
  private CSPSpec cspspec_ = null;
  
  private final ZFactory fac_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();

  private final CircusFactory cfac_ = new net.sourceforge.czt.circus.impl.CircusFactoryImpl();
  
  /**
   * context or environment to maintain local variables in scope (a map from the variable name to its type) 
   * 1. from input channel, such as c?x, c!y?x?z 
   * 2. from variable block
   * format:
   *    (var name, var type, corresponding numbering)
   * such as
   *    (x, Tx, n)
   */
//  private final Stack<Triple<String, Term, String>> loc_vars_stack_;
  private final Stack<LocalVariableEntry> loc_vars_stack_;
  
  /**
   * store the str_ temporarily and used for later recovery of str_
   */
  private final Stack<String> str_tmp_stack_;
  
  /**
   * store the process_para_ temporarily and used for later recovery of process_para_
   */
  private final Stack<ProcessPara> process_para_tmp_stack_;
  
  /**
   * How many levels into the main action
   */
  private int levels_ = 0;
  
  /**
   * if it is a visit of expression in channel declaration
   */
  private boolean channel_decl_ = false;
  
  /**
   * a stack of declaration in MuAction
   *    basically it is used to check if a CallAction is a reference to an Action or to MuAction
   */
  private final Stack<ZName> circus_muaction_stack_;
  
  /**
   * The main process
   *    is a process without reference to it
   *    processes \setminus referred_processes_
   */
  private final Set<String> processes_;
  
  /**
   * The process
   *    is a process without reference to it
   */
  private final Set<String> referred_processes_;
  
  /**
   * Configuration
   */
  private final Config config_;
  
  /**
   * 
   */
  private final SectionManager manager_;
  
  private final Map<Node, Set<Node>> refmap_;
  
  /**
   * Warning Manager
   */
  WarningManager warningManager_ = new WarningManager();
  
  /**
   * A set of terms that have been linked to CSP and don't need to translate them again to
   * improve performance
   */
  private final Set<Pair<Node, String>> set_visited_constructs = new HashSet<Pair<Node, String>>();
  
  public CircusToCSPVisitor(CircusSpecMap map, CSPSpec cspspec, SectionManager manager, Map<Node, Set<Node>> refmap)
  {
    this.map_ = map;
    this.cspspec_ = cspspec;
    
    loc_vars_stack_ = new Stack<LocalVariableEntry>();
    str_tmp_stack_ = new Stack<String>();
    process_para_tmp_stack_ = new Stack<ProcessPara>();
    circus_muaction_stack_ = new Stack<ZName>();
    processes_ = new HashSet<String>();
    referred_processes_ = new HashSet<String>();
    manager_ = manager;
    
    // use the default config.properties
    String path = manager.getProperty("czt.path");
    config_ = new Config(path + "/" + Config.file_name_);
    // config csp library path
    cspspec.addHeader(config_.getConfig(Config.CSPLIBSPATH),
        config_.getConfig(Config.CONF_MININT),
        config_.getConfig(Config.CONF_MAXINT),
        config_.getConfig(Config.CONF_MAXINS));
    
    refmap_ = refmap;
  }
  
  public void clear()
  {
    str_ = "";
  }

  public void crln()
  {
    str_ += "\n";
  }
  
  void save_str()
  {
    str_tmp_stack_.push(str_);
  }

  void restore_str()
  {
    str_ = str_tmp_stack_.pop();
  }
  
  void save_process(ProcessPara p)
  {
    process_para_tmp_stack_.push(process_para_);
    process_para_ = p;
  }
  
  void restore_process()
  {
    process_para_ = process_para_tmp_stack_.pop();
  }
  
  /**
   * Remove the head string from str and return the remaining string
   * For example,
   * subStr("abcde", "abc") will reutrn "de"
   * subStr("abcde", "bc") will reutrn "abcde"
   * 
   * @param str
   * @param headstr
   * @return
   */
  public String subStr(String str, String headstr)
  {
    if (str.length() >= headstr.length()) {
      String sstr = str.substring(0, headstr.length());
      if (sstr.equals(headstr)) {
        return str.substring(headstr.length());
      }
    }
    return str;
  }
  
  /**
   * visit the term and return the translated string but do not change str_
   * In particular, Z specification also is not change (means no schema added in Z) 
   * 
   * @param term
   * @return
   */
  public String safe_visit(Term term)
  {
    String str;

    // save str_
    save_str();
    str = "" + visit(term);
    // restore str_
    restore_str();

    return str;
  }
  
  protected Object visit(Term t)
  {
    if (t != null) {
      return t.accept(visitor_);
    }
    return null;
  }
  
  protected void unsupported(Term t) 
  {
    throw new CztException("Term [" + t.getClass().toString() + "] is not supported in current link rules!");
  }
  
  /**
   * Translate a schema to CSP
   * 
   * @param ap - AxPara
   *    
   */
  private void translateSchemaToCSP(AxPara ap)
  {
    AxParaKind kind = Circus2ZCSPUtils.getAxParaKind(ap);
    ZName apName = null;
    String ret = "";
    if(!(kind == AxParaKind.BOXED_SCHEMA || 
        kind == AxParaKind.HORIZON_SCHEMA || 
        kind == AxParaKind.ABBR)) {
      return;
    }
    
    apName = (ZName) ZUtils.getAxParaSchOrAbbrName(ap);
    
    // normalization or expand the schema
    DeclListExpansionVisitor dlevisitor;
    if(process_para_ == null) {
      dlevisitor = new DeclListExpansionVisitor(zsect_, manager_, zsectname_);
    }
    else {
      dlevisitor = new DeclListExpansionVisitor(process_para_.getCircusBasicProcess(), zsect_, manager_, zsectname_);
    }
    // after renaming, normalisation might not work properly, so disable it
    dlevisitor.disableNormalisation();
    ap.accept(dlevisitor);
    List<Pair<ZName, Expr>> lstZNameExpr = dlevisitor.getNameExprPairAsList();
    TreeSet<Pair<ZName, Expr>> orderedZNameExpr = new TreeSet<Pair<ZName, Expr>>(new pairNameTComparator<Expr>());
    orderedZNameExpr.addAll(lstZNameExpr);

    Expr expr = ZUtils.getSchemaDefExpr(ap);
    if(expr == null) {
      expr = ZUtils.getAbbreviationExpr(ap);
    }
    
    Pred pred = null;
    if(expr instanceof SchExpr && ((SchExpr)expr).getZSchText().getPred() == null) {
       pred = null;
    }
    else {
//      SchExpr schexpr = Circus2ZCSPUtils.expansionSchema(expr, zsectname_, manager_);
//      if(schexpr != null) {
//        pred = schexpr.getZSchText().getPred();
//      }
      
      PredicateListExpansionVisitor plev;
      if(process_para_ == null) {
        plev = new PredicateListExpansionVisitor(zsect_, manager_, zsectname_);
      }
      else {
        plev = new PredicateListExpansionVisitor(process_para_.getCircusBasicProcess(), 
            zsect_, manager_, zsectname_);
      }
      ap.accept(plev);
      
      pred = plev.getPred();
    }
    
    // CSP
    String schName = Circus2ZCSPUtils.termToString(apName);
    String fieldDatatype = "datatype " + 
        MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.SCHEMA_TO_DATATYPE_PATT), schName) + " = ";
    String schType = schName + " = {(";
    String temp = "";
    boolean first = true;
    List<String> lstField = new ArrayList<String>();
    
    for(Pair<ZName, Expr> p: orderedZNameExpr) {
      String name = Circus2ZCSPUtils.termToString(p.getFirst());
      String type = safe_visit(p.getSecond());
      if(first) {
        first = false;
      }
      else {
        fieldDatatype += " | ";
        schType += ", ";
        temp += ", ";
      }
      fieldDatatype += MessageFormat.format(
          CSPPredExpPattern.getPattern(PredExpPattern.SCHEMA_TO_DATATYPE_FIELD_PATT), schName, name) + "." + type;
      schType += MessageFormat.format(
          CSPPredExpPattern.getPattern(PredExpPattern.SCHEMA_TO_DATATYPE_FIELD_PATT), schName, name) + "." + name;
      temp += name + " <- " + type;
      lstField.add(MessageFormat.format(
          CSPPredExpPattern.getPattern(PredExpPattern.SCHEMA_TO_DATATYPE_FIELD_PATT), schName, name));
    }
    
    schType += ") | " + temp + ", ";
    String strPred;
    
    if(pred != null) {
      strPred = safe_visit(pred);
    }
    else {
      strPred = "true";
    }
    
    schType += strPred + "}";

    cspspec_.addDatatype(fieldDatatype);
    cspspec_.addNametype(schType);
    
    // add a select_TS function definition
    for(int i = 0; i < lstField.size(); i++) {
      String func = "select_field_" + schName + "((";
      String field = "";
      for(int j = 0; j < lstField.size(); j++) {
        if(j != 0) {
          func += ", ";
        }
        if(i == j) {
          func += lstField.get(i) + ".x";
          field = lstField.get(i);
        }
        else {
          func += "_";
        }
      }
      func += "), " + field + ") = x";
      
      cspspec_.addFunctions(func);
    }
    
    return;
  }
  
  /**
   * Find and visit a reference given by n, and also visit its corresponding references
   * @param n
   */
  private void findAParaByARefName(Node n, boolean skipSchemas)
  {
    if(n.getProcess() == null) {
      save_process(null);
      // global definition
      for(Para p: zsect_.getZParaList()) {
        
        if(p instanceof ChannelPara) {
          // all Channels will be translated and so ignore here
        }
        else if(p instanceof GivenPara) {
          for(Name name: ((GivenPara)p).getZNameList()) {
            if(Circus2ZCSPUtils.isEquals(n.getName(), (ZName) name)) {
              String str = isVisited((ZName)name, null);
              if(str == null) {
                // found and it's a GivenName
//                str = str_;
                List<Name> lstName = new ArrayList<Name>();
                lstName.add(name);
                visit(fac_.createGivenPara(fac_.createZNameList(lstName)));
//                markAsVisited(new Node((ZName)name, (ZName)null), subStr(str_, str));
                markAsVisited(new Node((ZName)name, (ZName)null), "");
              }
              else {
                str_ += str;
              }
            }
          }
        }
        else if(p instanceof AxPara) {
          AxParaKind kind = Circus2ZCSPUtils.getAxParaKind((AxPara)p);
          ZName apName = null;
          switch(kind) {
            case AXDEF:
              for(Decl decl: ZUtils.getAxBoxDecls(p)) {
                if(decl instanceof VarDecl) {
                  VarDecl vd = (VarDecl)decl;
                  for(Name axname: vd.getZNameList()) {
                    if(Circus2ZCSPUtils.isEquals(n.getName(), (ZName) axname)) {
                      String str = isVisited((ZName)n.getName(), null);
                      if(str == null) {
//                        str = str_;
                        // found
                        visit(p);
                        // recursively visit the reference
                        visitReferenceOfZName((ZName) axname, null, false);
//                        markAsVisited(new Node(n.getName(), (ZName)null), subStr(str_, str));
                        markAsVisited(new Node(n.getName(), (ZName)null), "");
                      }
                      else {
                        str_ += str;
                      }
                    }
                  }
                }
                else {
                  throw new CztException("Only VarDecl is supported in Axiomatic defintion now but it is a " + decl.getClass().getName());
                }
              }
//              Pred pred = ZUtils.getAxBoxPred(p);
              break;
            case ABBR:
              apName = (ZName) ZUtils.getAbbreviationName(p);
              if(Circus2ZCSPUtils.isEquals(apName, n.getName())) {
                String str = isVisited((ZName)n.getName(), null);
                if(str == null) {
                  // found
//                  str = str_;
                  if(Circus2ZCSPUtils.isSchemaExpr(ZUtils.getAbbreviationExpr(p))) {
                    if(!skipSchemas) {
                      translateSchemaToCSP((AxPara)p);
                    }
                    // recursively visit the reference
                    visitReferenceOfZName((ZName) apName, null, true);
                  }
                  else {
                    visit(p);
                    // recursively visit the reference
                    visitReferenceOfZName((ZName) apName, null, false);
                  }
//                  markAsVisited(new Node(n.getName(), (ZName)null), subStr(str_, str));
                  markAsVisited(new Node(n.getName(), (ZName)null), "");
                }
                else {
                  str_ += str;
                }
              }
              break;
            case BOXED_SCHEMA:
            case HORIZON_SCHEMA:
              // for schema, it is not supported by now 
              apName = (ZName) ZUtils.getSchemaName(p);
              if(Circus2ZCSPUtils.isEquals(apName, n.getName())) {
                String str = isVisited((ZName)n.getName(), null);
                if(str == null) {
                  if(!skipSchemas) {
                    translateSchemaToCSP((AxPara)p);
                  }
  //                Debug.debug_print("The translation of Schema Expression [" + 
  //                  ZUtils.getSchemaName(p).toString() + "] is not supported!");
                  visitReferenceOfZName((ZName) apName, null, true);
                  markAsVisited(new Node(n.getName(), (ZName)null), "");
                }
              }
              break;
            default:
              break;
          }
        }
        else if(p instanceof FreePara) {
          for(Freetype ft: (ZFreetypeList) ((FreePara)p).getFreetypeList()) {
            if(Circus2ZCSPUtils.isEquals(ft.getZName(), n.getName())) {
              String str = isVisited((ZName)n.getName(), null);
              if(str == null) {
//                str = str_;
                visit(p);
                visitReferenceOfZName(ft.getZName(), null, false);
//                markAsVisited(new Node(n.getName(), (ZName)null), subStr(str_, str));
                markAsVisited(new Node(n.getName(), (ZName)null), "");
                break;
              }
              else {
                str_ += str;
              }
            }
            for(Branch b: (ZBranchList)ft.getBranchList()) {
              if(Circus2ZCSPUtils.isEquals(b.getZName(), n.getName())) {
                String str = isVisited((ZName)n.getName(), null);
                if(str == null) {
//                  str = str_;
                  // found it
                  visit(p);
                  visitReferenceOfZName(b.getZName(), null, false);
//                  markAsVisited(new Node(n.getName(), (ZName)null), subStr(str_, str));
                  markAsVisited(new Node(n.getName(), (ZName)null), "");
                  break;
                }
                else {
                  str_ += str;
                }
              }
            }
          }
        }
        else if(p instanceof ChannelSetPara) {
          
        }
        else {
          // ignore
        }
      }
      restore_process();
    }
    else {
      // local definition only searches from a process
      for(Para p: zsect_.getZParaList()) {
        if((p instanceof ProcessPara)) {
          // For BasicProcess
          if(((ProcessPara)p).getCircusProcess() instanceof BasicProcess) {
            BasicProcess bp = (BasicProcess) ((ProcessPara)p).getCircusProcess();
            for(Para para: bp.getZParaList()) {
              if(para instanceof AxPara) {
                AxParaKind kind = Circus2ZCSPUtils.getAxParaKind((AxPara) para);
                ZName name;
                switch(kind) {
                  case ABBR:
                    name = (ZName) ZUtils.getAbbreviationName(para);
                    if(Circus2ZCSPUtils.isEquals(name, n.getName())) {
                      String str = isVisited((ZName)n.getName(), null);
                      if(str == null) {
                        save_process((ProcessPara)p);
//                        str = str_;
                        if(Circus2ZCSPUtils.isSchemaExpr(ZUtils.getAbbreviationExpr(para))) {
                          if(!skipSchemas) {
                            translateSchemaToCSP((AxPara)para);
                          }
                          visitReferenceOfZName(name, (ProcessPara)p, true);
                        }
                        else {
                          visit(para);
                          visitReferenceOfZName(name, (ProcessPara)p, false);
                        }

                        restore_process();
//                        markAsVisited(new Node(n.getName(), ((ProcessPara)p).getZName()), subStr(str_, str));
                        markAsVisited(new Node(n.getName(), ((ProcessPara)p).getZName()), "");
                        return;
                      }
                      else {
                        str_ = str;
                      }
                    }
                    break;
                  case AXDEF:
                    boolean found = false;
                    for(Decl decl: ZUtils.getAxBoxDecls(para)) {
                      if(decl instanceof VarDecl) {
                        for(Name aname: ((VarDecl)decl).getZNameList()) {
                          if(Circus2ZCSPUtils.isEquals((ZName) aname, n.getName())) {
                            found = true;
                          }
                        }
                      }
                    }
                    
                    // if a variable is found in this axdef, then add it to CSP
                    if(found) {
                      String str = isVisited((ZName)n.getName(), null);
                      if(str == null) {
                        save_process((ProcessPara)p);
//                        str = str_;
                        visitReferenceOfZName(n.getName(), (ProcessPara)p, false);
                        visit(para);
                        restore_process();
//                        markAsVisited(new Node(n.getName(), ((ProcessPara)p).getZName()), subStr(str_, str));
                        markAsVisited(new Node(n.getName(), ((ProcessPara)p).getZName()), "");
                      }
                      else {
                        str_ += str;
                      }
                      return;
                    }
                    break;
                  case BOXED_SCHEMA:
                  case HORIZON_SCHEMA:
                    // for schema, it is not supported by now 
                    name = (ZName) ZUtils.getSchemaName(para);
                    if(Circus2ZCSPUtils.isEquals(name, n.getName())) {
//                      throw new CztException("The translation of Schema Expression [" + 
//                          ZUtils.getSchemaName(para).toString() + "] is not supported!");
//                      Debug.debug_print("The translation of Schema Expression [" + 
//                        ZUtils.getSchemaName(para).toString() + "] is not supported!");
                      String str = isVisited((ZName)n.getName(), null);
                      if(str == null) {
                        save_process((ProcessPara)p);
                        if(!skipSchemas) {
                          translateSchemaToCSP((AxPara)para);
                        }
        //                Debug.debug_print("The translation of Schema Expression [" + 
        //                  ZUtils.getSchemaName(p).toString() + "] is not supported!");
                        visitReferenceOfZName((ZName) name, null, true);
//                        visitReferenceOfZName(name, (ProcessPara)p, true);
                        restore_process();
                        markAsVisited(new Node(n.getName(), (ZName)null), "");
//                        markAsVisited(new Node(n.getName(), ((ProcessPara)p).getZName()), "");
                      }
                    }
                    break;
                  default:
                    break;
                }
              }
            }
          }
        }
      }
    }
    
  }
  
  /**
   * visit the references of a term by its name and process
   * @param name
   * @param process
   * @param skipSchemas - skip schema references. For schema expression, if there're other schemas referred, since
   *    they are expanded by DeclList and PredList expansion, the recursive visit of them are ignored.
   */
  private void visitReferenceOfZName(ZName name, ProcessPara process, boolean skipSchemas)
  {
    Set<Node> setNode = new HashSet<Node>();
    
    Node nameNode = Circus2ZCSPUtils.getADefFromMap(refmap_, name, process, setNode);
    
    if(nameNode != null && !setNode.isEmpty()) {
      for(Node n: setNode) {
        findAParaByARefName(n, skipSchemas);
//        if(!skipSchemas) {
//          findAParaByARefName(n);
//        }
//        else {
//          if(!Circus2ZCSPUtils.isARefToSchema(n.getName(), zsect_, process_para_)) {
//            findAParaByARefName(n); 
//          }
//        }
      }
    }
  }
  
  /**
   * Mark this node as visited
   * @param n - a node composed of (ZName of construct, ZName of the process)
   * @param str - the linked CSP in String 
   */
  private void markAsVisited(Node n, String str)
  {
    set_visited_constructs.add(new Pair<Node, String>(n, str));
  }
  
  /**
   * Mark this node as visited
   * @param n - a node composed of (ZName of construct, ZName of the process) 
   */
  private String isVisited(ZName name, ZName process)
  {
    for(Pair<Node, String> p: set_visited_constructs) {
      if(Circus2ZCSPUtils.isEquals(p.getFirst().getName(), name)) {
        if(process == null && p.getFirst().getProcess() == null) {
          return p.getSecond();
        }
        else if(process != null && p.getFirst().getProcess() != null) {
          if(Circus2ZCSPUtils.isEquals(p.getFirst().getProcess(), process)) {
            return p.getSecond();
          }
        }
        else {
//          return false;
        }
      }
    }
    return null;
  }
  
  /**
   * The prefix string before each line to achieve structural align of constructs
   * @return
   */
  private String prefixAlignString()
  {
    return Circus2ZCSPUtils.repeatString(" ", levels_*2);
  }
  
  @Override
  public Object visitDecorExpr(DecorExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;

  }

  @Override
  public Object visitUnparsedPara(UnparsedPara term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZSchText(ZSchText term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNewOldPair(NewOldPair term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitVarDecl(VarDecl term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZName(ZName term)
  {
    String str = str_;
    str_ += Circus2ZCSPUtils.termToString(term);
    String tmp = subStr(str_, str);
    
    return tmp;
  }

  @Override
  public Object visitUnparsedZSect(UnparsedZSect term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitOptempPara(OptempPara term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitInclDecl(InclDecl term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNarrPara(NarrPara term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitTupleSelExpr(TupleSelExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitBindExpr(BindExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitMuExpr(MuExpr term)
  {
    String str = str_;
    
    ZSchText zst = term.getZSchText();
    ZDeclList zdl = zst.getZDeclList();
    Pred pred = zst.getPred();
    
    List<Pair<Name, Expr>> lstP = new ArrayList<Pair<Name, Expr>>();
    for(Decl decl: zdl) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          lstP.add(new Pair<Name, Expr>(name, ((VarDecl)decl).getExpr()));
        }
      }
    }
    
    if(lstP.size() > 1) {
      throw new CztException("For mu expression, we can support only one variable now.");
    }
    
    str_ += "(";
    boolean first = true;
    String tmpVar = "";
    String tmpVarSet = "";
    
    for(Pair<Name, Expr> p: lstP) {
      if(first) {
        first = false;
      } else {
        tmpVar += ", ";
        tmpVarSet += ", ";
      }

      tmpVar += safe_visit(p.getFirst());
      tmpVarSet += safe_visit(p.getSecond());
    }
    str_ += "mu(" + tmpVarSet + ", ";
    str_ += "(\\ " + tmpVar + " @ ";
    
    if(pred != null) {
      visit(pred);
    }
    else {
      str_ += "true";
    }

    str_ += "), (";
    str_ += "\\ " + tmpVar + " @ ";
    
    visit(term.getExpr());
    str_ += ")))";
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitTruePred(TruePred term)
  {
    String str = str_;
    str_ += "true";
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitIffExpr(IffExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSignatureAnn(SignatureAnn term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitGivenType(GivenType term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitPreExpr(PreExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSetCompExpr(SetCompExpr term)
  {
    String str = str_;
    
    ZSchText zst = term.getZSchText();
    ZDeclList zdl = zst.getZDeclList();
    Pred pred = zst.getPred();
    
    List<Pair<Name, Expr>> lstP = new ArrayList<Pair<Name, Expr>>();
    for(Decl decl: zdl) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          lstP.add(new Pair<Name, Expr>(name, ((VarDecl)decl).getExpr()));
        }
      }
    }
    
    str_ += "{ ";
    
    boolean first = true;
    String tmpVar = "";
    String tmpVarSet = "";
    
    for(Pair<Name, Expr> p: lstP) {
      if(first) {
        first = false;
      } else {
        tmpVar += ", ";
        tmpVarSet += ", ";
      }

      tmpVar += safe_visit(p.getFirst());
      tmpVarSet += safe_visit(p.getFirst()) + " <- " + safe_visit(p.getSecond());
    }
    
    if(term.getExpr() != null) {
      visit(term.getExpr());
    }
    else {
      str_ += tmpVar;
    }
    str_ += " | ";

    str_ += tmpVarSet;
    
    if(pred != null) {
      str_ += ", ";
      visit(pred);
    }

    str_ += "}";

    String tmp = subStr(str_, str);
    return tmp;  
  }

  @Override
  public Object visitApplExpr(ApplExpr term)
  {
    String str = str_;

    String left, right, rel;

    if (term.getMixfix()) {
      /**
       * C.6.21 (Function Operator Application). For example: S + T.
       * In this case, Mixfix=true, the first (left) expression is the
       * name, (" _ + _ "), (that is, a RefExpr with Mixfix=false!)
       * and the second (right) expression is (S,T).
       */      
    }
    else {
      /**
       * C.6.22 (Application). For example: (_ + _)(S, T).
       * In this case, Mixfix=false, and the rest is the same as above
       * (the first expression is the RefExpr with Mixfix=false and
       * name (" _ + _ "), and the second expression is (S,T)).
       * Another example: dom R.
       * In this case, Mixfix=false, the first (left) expression is the
       * function, dom, (again, a RefExpr with Mixfix=false)
       * and the second (right) expression is the argument R.
       */
    }
    
    if (ZUtils.isRefExpr(term.getLeftExpr()) /*&&
        Circus2ZCSPUtils.getRefExprKind((RefExpr) term.getLeftExpr()) == RefExprKind.REF*/) {
      OperatorName os = ((RefExpr) (term.getLeftExpr())).getZName().getOperatorName();
      
      if(os != null) {
        if (os.isInfix()) {
          assert ZUtils.isTupleExpr(term.getRightExpr());
          /** won't modify the str_ */
          rel = Circus2ZCSPUtils.getOperator(os);
          left = "" + safe_visit(term.getRightExpr());
          
          List<String> lstr = new ArrayList<String>();
          if (Circus2ZCSPUtils.split_a_tuple(left, lstr)) {
            left = lstr.get(0);
            right = lstr.get(1);
            str_ += Circus2ZCSPUtils.convertOp(left, right, rel);
          }
        }
        else if (os.isPrefix() && os.isUnary()) {
          rel = Circus2ZCSPUtils.getOperator(os);
          left = "";
          right = "" + safe_visit(term.getRightExpr());
          str_ += Circus2ZCSPUtils.convertOp(left, right, rel);
        }
        else if (os.isPostfix()) {
          rel = Circus2ZCSPUtils.getOperator(os);
          left = "";
          right = "" + safe_visit(term.getRightExpr());
          // iteration of relation: r^n
          if(rel.equals(ZString.NE + ZString.SW)) {
            assert ZUtils.isTupleExpr(term.getRightExpr());
            List<String> lstr = new ArrayList<String>();
            if (Circus2ZCSPUtils.split_a_tuple(right, lstr)) {
              left = lstr.get(0);
              right = lstr.get(1);
            }
          }
          else if(rel.equals(ZString.LIMG + ZString.RIMG)) {
            assert ZUtils.isTupleExpr(term.getRightExpr());
            List<String> lstr = new ArrayList<String>();
            if (Circus2ZCSPUtils.split_a_tuple(right, lstr)) {
              right = lstr.get(0);
              left = lstr.get(1);
            }            
          }
          str_ += Circus2ZCSPUtils.convertOp(left, right, rel);
        }
        else if (os.getFixity() == Fixity.NOFIX) {
          // For example, \langle \listarg \rangle
          rel = Circus2ZCSPUtils.getOperator(os);
          left = "";
          right = "" + safe_visit(term.getRightExpr());
          str_ += Circus2ZCSPUtils.convertOp(left, right, rel);
        }
      } // os != null
      else { // os == null
        // a function application
        /* the name of the 1st expression might be 
         *      1. a function name (such as func(a)), or 
         *      2. a freetype constructor name (tree(branch, branch), leaf(1) or leaf~1)
         */
        ZName funcName = ((RefExpr) (term.getLeftExpr())).getZName();
        String strFuncName = Circus2ZCSPUtils.termToString(funcName);
        boolean bConstructor = false;
        
        // check if it is a constructor of a free type or not
        List<Triple<String, String, Term>> lstFreeTypeConstructors = map_.getAllFreeTypeConstructors();
        for(Triple<String, String, Term> p: lstFreeTypeConstructors) {
          if(p.getFirst().equals(strFuncName)) {
            // it is a constructor
            bConstructor = true;
            // () is necessary in ProB for datatype comparison, such as (Tag.1) == (Tag.2)
            str_ += "(" + strFuncName + ".";
            visit(term.getRightExpr());
            str_ += ")";
            break;
          }
        }
        
        if(!bConstructor) {
          // first check if it is \bigcup or \bigcap
          if(strFuncName.equals(ZString.BIGCUP) || strFuncName.equals(ZString.BIGCAP)) {
            right = "" + safe_visit(term.getRightExpr());
            str_ += Circus2ZCSPUtils.convertOp("", right, strFuncName);
          }
          else if(strFuncName.equals("dom") || strFuncName.equals("ran") || 
              strFuncName.equals("first") || strFuncName.equals("second") || 
              strFuncName.equals("id")) {
            right = "" + safe_visit(term.getRightExpr());
            str_ += Circus2ZCSPUtils.convertOp("", right, strFuncName);
          }
          else if(strFuncName.equals("iter")) {
            left = "" + safe_visit(term.getRightExpr());
            str_ += Circus2ZCSPUtils.convertOp(left, "", strFuncName);
          }
          else if(strFuncName.equals("rev") || strFuncName.equals("head") || 
              strFuncName.equals("tail") || strFuncName.equals("front") || 
              strFuncName.equals("last") || strFuncName.equals("squash")) {
            right = "" + safe_visit(term.getRightExpr());
            str_ += Circus2ZCSPUtils.convertOp("", right, strFuncName);
          }
          else if(strFuncName.equals(CSPPredExpPattern.getPattern(PredExpPattern.OP_NAME_DIS_CONC))) {
            right = "" + safe_visit(term.getRightExpr());
            str_ += Circus2ZCSPUtils.convertOp("", right, strFuncName);
          }
          else {
            // function application
            str_ += "fa(" + strFuncName +", ";
            visit(term.getRightExpr());
            str_ += ")";
          }
        }
      }
    }
    
    if(term.getLeftExpr() instanceof LambdaExpr) {
      visit(term.getLeftExpr());
      str_ += "(";
      visit(term.getRightExpr());
      str_ += ")";
    }
    else if(term.getLeftExpr() instanceof ApplExpr) {
      // specifically for iter~n~r where LeftExpr is ApplExpr (iten~n), and RightExpr is r.
      rel = "" + safe_visit(term.getLeftExpr());
      right = "" + safe_visit(term.getRightExpr());
      
      // rel = itern(n, )
      // right = r
      // => itern(r, n)
      if(rel.startsWith("itern(")) {
        str_ += rel.replaceFirst("itern\\((.*),\\s*\\)", "itern(" + right + ", $1)");
      }
    }
    
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitNumStroke(NumStroke term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitConjPara(ConjPara term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitDirective(Directive term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitForallPred(ForallPred term)
  {
    String str = str_;
    
    ZSchText zst = term.getZSchText();
    ZDeclList zdl = zst.getZDeclList();

    String op = ZString.ALL;
    String rhs = safe_visit(term.getPred());

    List<Pair<Name, Expr>> lstP = new ArrayList<Pair<Name, Expr>>();
    for(Decl decl: zdl) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          lstP.add(new Pair<Name, Expr>(name, ((VarDecl)decl).getExpr()));
        }
      }
    }
    
    for(Pair<Name, Expr> p: lstP) {
      // it's type
      String lhs = safe_visit(p.getSecond());
      // "(\ x @ p)"
      rhs = "(\\ " + safe_visit(p.getFirst()) + " @ " + rhs + ")";
      rhs = Circus2ZCSPUtils.convertOp(lhs, rhs, op);
    }

    str_ += rhs;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZNumeral(ZNumeral term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitExists1Pred(Exists1Pred term)
  {
    String str = str_;
    
    ZSchText zst = term.getZSchText();
    ZDeclList zdl = zst.getZDeclList();

    String op = CSPPredExpPattern.getPattern(PredExpPattern.OP_NAME_EXISTS_1);
    String rhs = safe_visit(term.getPred());

    List<Pair<Name, Expr>> lstP = new ArrayList<Pair<Name, Expr>>();
    for(Decl decl: zdl) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          lstP.add(new Pair<Name, Expr>(name, ((VarDecl)decl).getExpr()));
        }
      }
    }
    
    for(Pair<Name, Expr> p: lstP) {
    // it's type
    String lhs = safe_visit(p.getSecond());
    // "(\ x @ p)"
    rhs = "(\\ " + safe_visit(p.getFirst()) + " @ " + rhs + ")";
    rhs = Circus2ZCSPUtils.convertOp(lhs, rhs, op);
    }

    str_ += rhs;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitOperand(Operand term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitRenameExpr(RenameExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCondExpr(CondExpr term)
  {
    String str = str_;
    
    RefExpr reTrue = cfac_.createRefExpr(
        cfac_.createZName("True", cfac_.createZStrokeList(), null), 
        cfac_.createZExprList(), false, false);

    RefExpr reFalse = cfac_.createRefExpr(
        cfac_.createZName("False", cfac_.createZStrokeList(), null), 
        cfac_.createZExprList(), false, false);

    // specific consideration for boolean expression
    if(term.getLeftExpr().equals(reTrue) && term.getRightExpr().equals(reFalse)) {
      visit(term.getPred());
    }
    else {
      str_ += "if ";
      visit(term.getPred());
      
      str_ += " then ";
      visit(term.getLeftExpr());
      
      str_ += " else ";
      visit(term.getRightExpr());
    }
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNextStroke(NextStroke term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitProjExpr(ProjExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZDeclList(ZDeclList term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitLocAnn(LocAnn term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitHideExpr(HideExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSchExpr(SchExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitGenericType(GenericType term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNameSectTypeTriple(NameSectTypeTriple term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitExists1Expr(Exists1Expr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitLatexMarkupPara(LatexMarkupPara term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZRenameList(ZRenameList term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNameTypePair(NameTypePair term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZStrokeList(ZStrokeList term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitPowerType(PowerType term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitParenAnn(ParenAnn term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitPipeExpr(PipeExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitTypeAnn(TypeAnn term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitAxPara(AxPara term)
  {
    save_str();

    if(ZUtils.isAbbreviation(term)) {
      String str = str_;
//      str_ += "nametype ";
      visit(ZUtils.getAbbreviationName(term));
      str_ += " = ";
      visit(ZUtils.getAbbreviationExpr(term));
      String tmp = subStr(str_, str);
      cspspec_.addNametype(tmp);
    }
    else if(ZUtils.getAxBoxDecls(term) != null) {
      // Axiomatic definition
      ZDeclList zdl = ZUtils.getAxBoxDecls(term);
      Pred pred = ZUtils.getAxBoxPred(term);
      if(pred != null) {
        String strPred = safe_visit(pred);        
        cspspec_.addAxiomaticDef("-- The variables defined below should meet the predicate below");
        cspspec_.addAxiomaticDef("--       " + strPred + "");
      }
      
      for(Decl decl: zdl) {
        if(decl instanceof VarDecl) {
          String strExpr = safe_visit(((VarDecl)decl).getExpr());
          for(Name name: ((VarDecl)decl).getZNameList()) {
            String strName = safe_visit(name);
            String value = config_.getConfig(strName);
            if(value == null) {
              cspspec_.addAxiomaticDef(strName + " = " + "-- must be choose from " + strExpr + "\n");
            }
            else {
              cspspec_.addAxiomaticDef(strName + " = " + value);
            }
          }
        }
      }
    }
    else if(ZUtils.isSimpleSchema(term)) {
      // TODO: schema is ignored
    }
    
    restore_str();
    return "";
  }

  @Override
  public Object visitInStroke(InStroke term)
  {
    return null;
  }

  @Override
  public Object visitAndExpr(AndExpr term)
  {
    String str = str_;
    
//    unsupported(term);
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitImpliesExpr(ImpliesExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZBranchList(ZBranchList term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSchemaType(SchemaType term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitOutStroke(OutStroke term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNumExpr(NumExpr term)
  {
    String str = str_;
    str_ += Circus2ZCSPUtils.termToString(term);
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitZExprList(ZExprList term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitExistsExpr(ExistsExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZSect(ZSect term)
  {
    zsectname_ = term.getName();
    zsect_ = term;
    
    for(Para para: term.getZParaList()) {
      // ChannelPara, ChannelSetPara and ProcessPara are linked to CSP definitely
      if(para instanceof ChannelPara) {
        visit(para);
      }
      else if(para instanceof ChannelSetPara) {
        visit(para);
      }
      else if(para instanceof ProcessPara) {
        visit(para);
      }
      else {
        // Whether other paragraphs are linked to CSP or not depends on if they are referred in 
        // ChannelPara, ChannelSetPara and ProcessPara
      }
    }
    
    // set main process
    processes_.removeAll(referred_processes_);
    
    if(processes_.size() == 0) {
      // maybe no process, or all processes are referred
    }
    else if(processes_.size() == 1) {
      Iterator<String> ite = processes_.iterator();
      String main = ite.next();
      if(! main.equals("MAIN")) {
        cspspec_.addProcess("MAIN = " + main);
      }
    }
    else {
      String main = config_.getConfig("MAIN");
      if(main != null && processes_.contains(main)) {
        cspspec_.addProcess("MAIN = " + main);
      }
      else {
//        throw new CztException("Main process can not be determined and "
//            + "please specify one in Circus by adding a MAIN process, or"
//            + "add MAIN = in configuration file!");
        warningManager_.warn("Main process can not be determined and "
            + "please specify one in Circus by adding a MAIN process, or"
            + " add MAIN = in configuration file!");
      }
    }
    
    cspspec_.addAssertion("assert MAIN :[ livelock free ]");
    cspspec_.addAssertion("assert MAIN :[ deadlock free [F] ]");
    cspspec_.addAssertion("assert MAIN :[ deadlock free [FD] ]");        

    return null;
  }

  @Override
  public Object visitLetExpr(LetExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitProdType(ProdType term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitLambdaExpr(LambdaExpr term)
  {
    String str = str_;
    
    ZSchText zst = term.getZSchText();
    ZDeclList zdl = zst.getZDeclList();
    Pred pred = zst.getPred();
    
    List<Pair<Name, Expr>> lstP = new ArrayList<Pair<Name, Expr>>();
    for(Decl decl: zdl) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          lstP.add(new Pair<Name, Expr>(name, ((VarDecl)decl).getExpr()));
        }
      }
    }
    
    str_ += "(\\ ";    
    boolean first = true;
    String tmpVar = "";
    String tmpVarSet = "";
    
    for(Pair<Name, Expr> p: lstP) {
      if(first) {
        first = false;
      } else {
        tmpVar += ", ";
        tmpVarSet += ", ";
      }

      tmpVar += safe_visit(p.getFirst());
      tmpVarSet += safe_visit(p.getFirst()) + " <- " + safe_visit(p.getSecond());
    }
    str_ += tmpVar + " @ if member((" + tmpVar + "), {" + tmpVar + " | " + tmpVarSet;
    
    if(pred != null) {
      str_ += ", ";
      visit(pred);
    }

    str_ += "}) then ";
    
    visit(term.getExpr());
    
    str_ += " else undefined)";
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitAndPred(AndPred term)
  {
    String str = str_;
    
    String op = ZString.AND;
    String lhs = safe_visit(term.getLeftPred());
    String rhs = safe_visit(term.getRightPred());
    
    str_ += Circus2ZCSPUtils.convertOp(lhs, rhs, op);
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitExistsPred(ExistsPred term)
  {
    String str = str_;
    
    ZSchText zst = term.getZSchText();
    ZDeclList zdl = zst.getZDeclList();

    String op = ZString.EXI;
    String rhs = safe_visit(term.getPred());

    List<Pair<Name, Expr>> lstP = new ArrayList<Pair<Name, Expr>>();
    for(Decl decl: zdl) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          lstP.add(new Pair<Name, Expr>(name, ((VarDecl)decl).getExpr()));
        }
      }
    }
    
    for(Pair<Name, Expr> p: lstP) {
    // it's type
    String lhs = safe_visit(p.getSecond());
    // "(\ x @ p)"
    rhs = "(\\ " + safe_visit(p.getFirst()) + " @ " + rhs + ")";
    rhs = Circus2ZCSPUtils.convertOp(lhs, rhs, op);
    }

    str_ += rhs;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitFreePara(FreePara term)
  {
    save_str();
    for(Freetype fp: (ZFreetypeList)(term.getFreetypeList())) {
      String str = str_;
      String fpName = Circus2ZCSPUtils.termToString(fp.getZName());
      str_ += "datatype " + fpName + " = ";
      
      // add this freetype to map_
      map_.addFreeType(fpName, 
          Circus2ZCSPUtils.termToString(fp.getBranchList()), 
          fp.getBranchList());
      ZBranchList bl = (ZBranchList)fp.getBranchList();
      int size = bl.getBranch().size();
      
      for(int i = 0; i < size; i++) {
        if(i != 0) {
          str_ += " | ";
        }
        Branch b = bl.get(i);
        if(b.getExpr() == null) {
          // simple constant only, such as c1
          visit(b.getZName());
          map_.addFreeTypeConst(fpName, Circus2ZCSPUtils.termToString(b.getZName()), b.getZName());
        }
        else {
          // constructor
          visit(b.getZName());
          str_ += ".";
          visit(b.getExpr());
          map_.addFreeTypeConstructor(fpName, Circus2ZCSPUtils.termToString(b.getZName()), 
              Circus2ZCSPUtils.termToString(b.getExpr()), b.getExpr());
        }
      }

      String t = subStr(str_, str);
      cspspec_.addDatatype(t);
      
      str_ += "\n";
    }
    restore_str();
    return null;
  }

  @Override
  public Object visitOrExpr(OrExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitTupleExpr(TupleExpr term)
  {
    String str = str_;
    str_ += "(";

    boolean first = true;
    for (Expr expr : term.getZExprList()) {
      if(first) {
        first = false;
      } else {
        str_ += ", ";
      }
      
      visit(expr);      
    }

    str_ += ")";
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitPowerExpr(PowerExpr term)
  {
    String str = str_;
   
    String rel = ZString.POWER;
    String rhs = safe_visit(term.getExpr());
    str_ += Circus2ZCSPUtils.convertOp("", rhs, rel);
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitConstDecl(ConstDecl term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZParaList(ZParaList term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitThetaExpr(ThetaExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitOperator(Operator term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitParent(Parent term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNegExpr(NegExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitMemPred(MemPred term)
  {
    String str = str_;

    MemPredKind kind = Circus2ZCSPUtils.getMemPredKind(term);
    String rel, left, right;
    Expr lhs, rhs;
    // for the various cases, push boolean to the fKeepOpArgs stack. If not empty and top=true, it
    // will keep, otherwise (empty or top=false) it won't.
    switch (kind) {
      // x \in y: e.g., (\_ \in \_)[x,y] is not allowed! So don't interfere with ARG
      case SET_MEMBERSHIP :
        lhs = term.getLeftExpr();
        rhs = term.getRightExpr();
        save_str();
        left = "" + safe_visit(lhs);
        right = "" + safe_visit(rhs);
        restore_str();
        str_ += "member(" + left + ", " + right + ")";
        break;
      // NARY/UNARY_RELOP_APPLICATION: x < y or disjoint x. In both cases we cannot have (_ < _)
      // (x,y). So remove the ARG(S)
      case NARY_RELOP_APPLICATION :
        ZExprList params = ((TupleExpr) term.getLeftExpr()).getZExprList();
        assert !params.isEmpty();
        if (params.size() != 2) {
          throw new CztException(
              "Current version only supports translation of binary relational operators.");
        }

        lhs = params.get(0);
        rhs = params.get(1);

        if (ZUtils.isRefExpr(term.getRightExpr())) {
          OperatorName os = ((RefExpr) (term.getRightExpr())).getZName().getOperatorName();
          assert os.isInfix();
          save_str();
          left = "" + safe_visit(lhs);
          rel = Circus2ZCSPUtils.getOperator(os);
          right = "" + safe_visit(rhs);
          restore_str();
          str_ += Circus2ZCSPUtils.convertOp(left, right, rel);
        }
        break;
      case UNARY_RELOP_APPLICATION :
        RefExpr refexpr = (RefExpr) term.getRightExpr();
        OperatorName on = refexpr.getZName().getOperatorName();
        assert on != null;
        Fixity fixity = on.getFixity();

        /*
         * NOTE:
         * The actual unary parameter comes from the left expression and is placed according to the
         * fixture.
         */
        lhs = term.getLeftExpr();
        if (fixity == Fixity.PREFIX) {
          // Prefix: left+rel+right = ""+rel+right
          left = "";
          save_str();
          right = "" + safe_visit(lhs);
          restore_str();
          rel = Circus2ZCSPUtils.getOperator(on);
          str_ += Circus2ZCSPUtils.convertOp(left, right, rel);
        }
        else if (fixity == Fixity.POSTFIX) {
          // Postfix: left+rel+right = left+rel+""
          right = "";
          save_str();
          left = "" + safe_visit(lhs);
          restore_str();
          rel = Circus2ZCSPUtils.getOperator(on);
          str_ += Circus2ZCSPUtils.convertOp(left, right, rel);
        }
        else {
          throw new CztException("Unsupported fixture for relational operator ("
              + fixity.toString() + ").");
        }
        break;
      // equality don't care about ARG
      case EQUALITY :
        /*
         * NOTE:
         * For equality, the left expression is a Expr, whereas the
         * right expression must be a SetExpr containing only one element
         */
        /**
         * Equality
         */
        visit(term.getLeftExpr());
        str_ += " == ";
//        save_str();
        String tmp = "";
        tmp += safe_visit(term.getRightExpr());
//        restore_str();
        // for SetExpr which only have one element, we should remove the { and }
        if (term.getRightExpr() instanceof SetExpr) {
          // make sure the outermost set has only one element
          SetExpr expr = (SetExpr) term.getRightExpr();
          if (expr.getZExprList().size() == 1) {
            // remove outermost bracket
            tmp = tmp.substring(1, tmp.length() - 1);
          }
        }
        str_ += tmp;

        break;
      default :
        throw new AssertionError("Invalid MemPredKind " + kind);
    }
    // String result = format(MEMPRED_PATTERN, left, rel, right);
    // assert result != null && !result.equals("");
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitCompExpr(CompExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitForallExpr(ForallExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSetExpr(SetExpr term)
  {
    String str = str_;
    str_ += "{";

    boolean first = true;
    for (Expr expr : term.getZExprList()) {
      if (!first) {
        str_ += ", ";
      }
      else {
        first = false;
      }
      visit(expr);
    }

    str_ += "}";
    String tmp = subStr(str_, str);

    return tmp;
  }

  /**
   * Get a schema type name for the expression that is used in BindSel
   * TODO: more expressions
   * @param expr
   * @return
   */
  private Term getSchemaTypeForExpr(Expr expr)
  {
    Term ret = null;
    if(expr instanceof RefExpr) {
      RefExpr re = (RefExpr)expr;
      List<Pair<String, Term>> lstStates = map_.getStatListWithExpProName(para_name_);
      for(Pair<String, Term> p: lstStates) {
        if(Circus2ZCSPUtils.termToString(re.getZName()).equals(p.getFirst())) {
          ret = p.getSecond();
          break;
        }
      }
      
      if(ret == null) {
        for(LocalVariableEntry e: loc_vars_stack_) {
          if(e.getName().equals(Circus2ZCSPUtils.termToString(re.getZName()))) {
            ret = e.getType();
            break;
          }
        }
      }
    }
    else if (expr instanceof ApplExpr) {
      ApplExpr ae = (ApplExpr)expr;
      if(ae.getLeftExpr() instanceof RefExpr) {
        OperatorName on = ((RefExpr)ae.getLeftExpr()).getZName().getOperatorName();
        if(on == null) {
          // function application
          Term t = getSchemaTypeForExpr(ae.getLeftExpr());
          if(t instanceof RefExpr) {
            OperatorName on1 = ((RefExpr)t).getZName().getOperatorName();
            String rel = Circus2ZCSPUtils.getOperator(on1);
            if(rel.equals(ZString.FUN) || rel.equals(ZString.PFUN) || rel.equals(ZString.PINJ) || 
                rel.equals(ZString.INJ) || rel.equals(ZString.PSURJ) || rel.equals(ZString.SURJ) ||
                rel.equals(ZString.BIJ) || rel.equals(ZString.FFUN)) {
              Object[] exprs = ((RefExpr)t).getZExprList().toArray();
              if(exprs.length >= 1) {
                ret = (Term) exprs[1];
              }
            }
            else {
              throw new CztException("For function application [" + expr.toString() + "], it must be function type!");
            }
          }
        }
      }
    }
    
//    if(ret != null) {
//      if(!Circus2ZCSPUtils.isSchemaExpr((Expr)ret, zsect_, process_para_)) {
//        ret = null;
//      }
//    }
    
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
    
    if(lstp != null) {
      lstp.clear();
    }
    for(Pair<String, Term> p: lstPState) {
      if(nameset.contains(p.getFirst())) {
        if(lstp != null) {
          lstp.add(p);
        }
        ret = true;
      }
    }
    return ret;
  }
  
  @Override
  public Object visitBindSelExpr(BindSelExpr term)
  {
    String str = str_;
    
    Expr expr = term.getExpr();
    String strExpr = safe_visit(expr);
    
    ZName vname = term.getZName();
    String name = safe_visit(vname);
    
    if(isStateVar(vname, null)) {
      name = MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_, name);
    }
    
    // get the schema name/type of the expr
    Term schName = getSchemaTypeForExpr(expr);
    if(schName != null) {
      if(!Circus2ZCSPUtils.isSchemaExpr((Expr)schName, zsect_, process_para_)) {
        schName = null;
      }
    }

    String strSchName = null;
    if(schName != null && schName instanceof RefExpr) {
      strSchName = Circus2ZCSPUtils.termToString(((RefExpr)schName).getZName());
    }
    
    if(strSchName != null) {
      // select_field_
      String select = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.SCHEMA_TO_DATATYPE_SELECT_FIELD_PATT), strSchName);
      String field = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.SCHEMA_TO_DATATYPE_FIELD_PATT), strSchName, name);
      str_ += select + "(" + strExpr + ", " + field + ")";
    }
    else {
      throw new CztException("Can not find the corresponding schema name for BindSelExpr: (" + strExpr + ")." + name);
    }
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitBranch(Branch term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitFalsePred(FalsePred term)
  {
    String str = str_;
    str_ += "false";
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitZNameList(ZNameList term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitRefExpr(RefExpr term)
  {
    String str = str_;
    if(term.getZName().getWord().equals("$$SYNCH")) {
      str_ += "$$SYNCH";
      return "$$SYNCH";
    }
    
    OperatorName on = term.getZName().getOperatorName();
    ZExprList exprlist = term.getZExprList();
    boolean args = exprlist != null && !exprlist.isEmpty();

    String refName = Circus2ZCSPUtils.getVarName(term.getZName());

    assert refName != null && !refName.isEmpty();

    RefExprKind rek = Circus2ZCSPUtils.getRefExprKind(term);
    switch(rek) {
      case GEN_OP_APPL:
        /** <li>C.6.21 (Generic Operator Application). For example: S \rel T. In this case, mixfix and
        * explicit are always true, and the list of instantiating expressions is non-empty (it contains
        * [S,T]).</li>
        */
        /**
         * Generic Operator Application. That is, a
         * RefExpr with mixfix and explicit true, and the list of
         * instantiating expressions is non-empty (it contains [S,T]). For
         * example: S \fun T; \power_1~{1,3,5}
         */
        if (on == null) {
          throw new CztException("CZT RefExpr (generic) operator application is not an operator name");
        }
        else if (!args && exprlist.size() > 2) {
          throw new CztException(
              "CZT RefExpr (generic) operator application failed. Circus2ZCSP only accepts [1..2] arguments");
        }
        
        assert args && on != null;
        
        String rel = Circus2ZCSPUtils.getOperator(on);
        Expr left = exprlist.get(0);
        String lhs = "";
        lhs += safe_visit(left);
        
        if (on.isInfix()) {
          String rhs = "";
          rhs += safe_visit(exprlist.get(1));
          str_ += Circus2ZCSPUtils.convertOp(lhs, rhs, rel);
        }
        else if (on.isPrefix()) {
          str_ += Circus2ZCSPUtils.convertOp("", lhs, rel);
        }
        else if (on.isPostfix()) {
          str_ += Circus2ZCSPUtils.convertOp(lhs, "", rel);
        }
        break;
      case OP_APPL:
        break;
      case GEN_REF:
        /** <li>C.6.29 (Generic Instantiation). For example: \emptyset[T]. In this case, mixfix is always
        * false and the list of instantiating expressions is non-empty (it contains [T]). The explicit
        * attribute indicates whether the instantiating expressions are explicitly given in the
        * specification (explicit is true) or whether they were inferred by the typechecker (explicit is
        * false).</li>
        * 
        */
        /**
         * Another less common example would be (\_ \fun \_)[S, T].
         * In this case,
         * RefExpr(ZName("_->_"), ZExprList(
         * RefExpr(ZName("S"), MF=F, EX=F),
         * RefExpr(ZName("T"), MF=F, EX=F)),
         * MF=F, EX=T)
         */
        str_ += refName;
        break;
      case REF:
        /**
         * C.6.28 (Reference). For example: \arithmos
         * In this case, mixfix and explicit are always false
         * and the list of instantiating expressions is empty.
         * Another example before typechecking is \emptyset.
         * The typechecker transforms \emptyset to a generic
         * instantiation and explicit remains false (see 13.2.3.3).
         */
        str_ += refName;
        break;
      default:
        throw new CztException("Unknown ref expr kind");
    }

    String tmp = subStr(str_, str);
    return tmp;
}

  @Override
  public Object visitGivenPara(GivenPara term)
  {
    save_str();
    for (Name name : term.getZNameList()) {
      String str = str_;

      str_ += "datatype ";
/*      String tmp = (String) visit(name);
      str_ += " = " + MessageFormat.format(FormatPattern.GIVEN_SET_NAME_PATT, tmp);
      str_ += ".{1..MAXINS}";
      */
      String tmp = (String) visit(name);
      str_ += " = ";
      String ins = config_.getConfig(Config.CONF_MAXINS);
      int n = Integer.parseInt(ins);
      
      for (int i = 1; i <= n; i++) {
        str_ += MessageFormat.format(FormatPattern.GIVEN_SET_NAME_PATT, tmp, i);
        if(i != n) {
          str_ += " | ";
        }
      }
      tmp = subStr(str_, str);
      cspspec_.addDatatype(tmp);
    }

    restore_str();
    return "";
  }

  @Override
  public Object visitNegPred(NegPred term)
  {
    String str = str_;
    
    String op = ZString.NOT;
    String lhs = "";
    String rhs = safe_visit(term.getPred());
    
    str_ += Circus2ZCSPUtils.convertOp(lhs, rhs, op);
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitGenParamType(GenParamType term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSectTypeEnvAnn(SectTypeEnvAnn term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitFreetype(Freetype term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitIffPred(IffPred term)
  {
    String str = str_;
    
    String op = ZString.IFF;
    String lhs = safe_visit(term.getLeftPred());
    String rhs = safe_visit(term.getRightPred());
    
    str_ += Circus2ZCSPUtils.convertOp(lhs, rhs, op);
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitImpliesPred(ImpliesPred term)
  {
    String str = str_;
    
    String op = ZString.IMP;
    String lhs = safe_visit(term.getLeftPred());
    String rhs = safe_visit(term.getRightPred());
    
    str_ += Circus2ZCSPUtils.convertOp(lhs, rhs, op);
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSignature(Signature term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNarrSect(NarrSect term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSpec(Spec term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitProdExpr(ProdExpr term)
  {
    String str = str_;

    if(!channel_decl_) {
      str_ += "(";
    }
    
    boolean first = true;
    for (Expr expr : term.getZExprList()) {
      if(first) {
        first = false;
      } else {
        if(!channel_decl_) {
          str_ += ", ";
        }
        else {
          str_ += ".";
        }
      }
      
      visit(expr);      
    }
    
    if(!channel_decl_) {
      str_ += ")";
    }

    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitExprPred(ExprPred term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZFreetypeList(ZFreetypeList term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitOrPred(OrPred term)
  {
    String str = str_;
    
    String op = ZString.OR;
    String lhs = safe_visit(term.getLeftPred());
    String rhs = safe_visit(term.getRightPred());
    
    str_ += Circus2ZCSPUtils.convertOp(lhs, rhs, op);
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitTransformerPara(TransformerPara term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitStateUpdate(StateUpdate term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitIndexedProcess(IndexedProcess term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitProofObligationAnn(ProofObligationAnn term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitChannelSetPara(ChannelSetPara term)
  {
    String str = str_;

    save_str();
    String name = "" + safe_visit(term.getZName());
    restore_str();

    str_ += name + " = ";
    ChannelSet cs = term.getChannelSet();
    visit(cs);

    String tmp = subStr(str_, str);
    cspspec_.addChannelSet(tmp);
    
    markAsVisited(new Node(term.getZName(), (ZName)null), tmp);
    return tmp;
  }

  @Override
  public Object visitSeqProcessIdx(SeqProcessIdx term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCircusCommunicationList(CircusCommunicationList term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCircusChannelSet(CircusChannelSet term)
  {
    String str = str_;
    
    visit(term.getExpr());
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitExtChoiceProcessIdx(ExtChoiceProcessIdx term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitActionSignatureAnn(ActionSignatureAnn term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitProcessSignatureList(ProcessSignatureList term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCircusChannelSetList(CircusChannelSetList term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitHideAction(HideAction term)
  {
    String str = str_;
    
    String action = safe_visit(term.getCircusAction());
    String[] removedAction = {""};
    String strPre = FVar(action, removedAction);

    str_ += strPre + "((" + removedAction[0];
    str_ += ") \\ ";
    visit(term.getChannelSet());
    str_ += ")";
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  /**
   * Get a list of state variables from the term
   * @param term - input term
   * @return
   *    a list of state variables in Term
   */
  private List<Pair<String, Term>> getStateVarListInTerm(Term term)
  {
    StateVarsVisitor svv = new StateVarsVisitor(map_, para_name_);
    term.accept(svv);
    return svv.getVarList();
  }
  
  /**
   * Get a set of state variables from input a set of names
   * @param set
   * @return
   */
  private Set<String> getStateVarInSet(Set<String> set) 
  {
    List<String> lstr = map_.getStatList(para_name_);
    Set<String> ret = new HashSet<String>();
    
    for (String v: set) {
      if (lstr.contains(v)) {
        ret.add(v);
      }
    }

    return ret;
  }
  
  /**
   * Return local variables and their type from input string
   * No duplicated items in returned llst
   * 
   * @param set
   * @return
   *    a set of LocalVariableEntry. If no found, it is empty.
   */
  public Set<LocalVariableEntry> getLocVar(Set<String> set)
  {
    Set<LocalVariableEntry> llst = new HashSet<LocalVariableEntry>();

    for(String v: set) {
      for (LocalVariableEntry p : loc_vars_stack_) {
        if(p.getName().equals(v)) {
          llst.add(p);
        }
      }
    }
    
    return llst;
  }
  
  /**
   * Check if it is a local variable. If so, return its triple (x, Tx, n).
   * @param lv - a variable name
   * @return
   *    a LocalVariableEntry if it is, or null
   */
  public LocalVariableEntry getLocVar(String lv)
  {
    for (LocalVariableEntry p : loc_vars_stack_) {
      if(p.getName().equals(lv)) {
        return p;
      }
    }
    
    return null;
  }
  
  /**
   * Return a list of variables (state and local variables) from input String
   * 
   * @param st - a string representing a set of variables, format "{x, y, z}"
   * @return
   *    a set of variable names
   */
  private Set<String> getAllVars(String st)
  {
    Set<String> ret = new HashSet<String>();

    String[] str = st.trim().replaceAll("\\{","").replaceAll("\\}", "").split(",");
    for(String s: str) {
      if(s.matches(".*\\w.*")) {
        ret.add(s.trim());
      }
    }
    
    return ret;
  }
  

  
  @Override
  public Object visitParallelAction(ParallelAction term)
  {
    List<Pair<String, Term>> lstSet = new ArrayList<Pair<String, Term>>();
    List<Pair<String, Term>> lstVScpLeft = getStateVarListInTerm(term.getLeftAction());
    List<Pair<String, Term>> lstVScpRight = getStateVarListInTerm(term.getRightAction());
    
    String str = str_;

    CircusNameSet nsLeft = (CircusNameSet) term.getLeftNameSet();
    CircusNameSet nsRight = (CircusNameSet) term.getRightNameSet();

    String strNSLeft = safe_visit(nsLeft);
    String strNSRight = safe_visit(nsRight);

    // if both ns1 and ns2 are empty
    if (strNSLeft.equals("{}") && strNSRight.equals("{}")) {
      visit(term.getLeftAction());
      str_ += " [| ";
      visit(term.getChannelSet());
      str_ += " |] ";
      visit(term.getRightAction());
    }
    else {
      /**
       * 1. Get all variables in scope (pv1 and pv2, sv1 and sv2, lv1 and lv2, ns1 and ns2)
       */

      Term leftTerm = term.getLeftAction();
      Term rightTerm = term.getRightAction();

      // get a set of term name in left and right action
      // TODO: how to identify the state variables from schema expressions
      ZNameSetVisitor lznsv = new ZNameSetVisitor();
      ZNameSetVisitor rznsv = new ZNameSetVisitor();
      leftTerm.accept(lznsv);
      rightTerm.accept(rznsv);

      Set<String> lstrNameSet = lznsv.getStrSet();
      Set<String> rstrNameSet = rznsv.getStrSet();
      
      // State variables in scope (sv1 and sv2)
      Set<String> svLeft = new HashSet<String>();
      Set<String> svRight = new HashSet<String>();
      
      svLeft = getStateVarInSet(lstrNameSet);
      svRight = getStateVarInSet(rstrNameSet);

      // Local variables in scope (lv1, lv2)
      List<String> lvLeft = new ArrayList<String>();
      List<String> lvRight = new ArrayList<String>();
      Set<LocalVariableEntry> lLocNameSet = new HashSet<LocalVariableEntry>();
      Set<LocalVariableEntry> rLocNameSet = new HashSet<LocalVariableEntry>();

      lLocNameSet = getLocVar(lstrNameSet);
      rLocNameSet = getLocVar(rstrNameSet);
      
      for (LocalVariableEntry p : lLocNameSet) {
        lvLeft.add(p.getName());
      }
      for (LocalVariableEntry p : rLocNameSet) {
        lvRight.add(p.getName());
      }

      // pv1 and pv2
      // pv1 = sv1 + lv1
      // pv2 = sv2 + lv2
      Set<String> pvLeft = new HashSet<String>();
      pvLeft.addAll(svLeft);
      pvLeft.addAll(lvLeft);

      Set<String> pvRight = new HashSet<String>();
      pvRight.addAll(svRight);
      pvRight.addAll(lvRight);

      // pv
      Set<String> pv = new HashSet<String>(pvLeft);
      pv.addAll(pvRight);

      // ns1 and ns2
      Set<String> lnsNameSet = new HashSet<String>();
      Set<String> rnsNameSet = new HashSet<String>();

      lnsNameSet = getAllVars(strNSLeft);
      rnsNameSet = getAllVars(strNSRight);

      // pv1 and pv2 must include ns1 and ns2.
      // In other word, ns1 and ns2 must be a subset of pv1 and pv2

      // TODO: disable the checking temporarily and should be enabled after the TODO above solved
/*      if (!lnsNameSet.isEmpty() && pvLeft.containsAll(lnsNameSet) == false) {
        throw new CztException("All elements in ns1 [" + lnsNameSet.toString() + "] must be in pv1 ["
            + pvLeft.toString() + "]");
      }

      if (!rnsNameSet.isEmpty() && pvRight.containsAll(rnsNameSet) == false) {
        throw new CztException("All elements in ns2 [" + rnsNameSet.toString() + "] must be in pv2 ["
            + pvRight.toString() + "]");
      }
*/
      /////////////////////////////////////////////////////////////////////////////////////////
      // Just return this simplified one
      /////////////////////////////////////////////////////////////////////////////////////////
      visit(term.getLeftAction());
      str_ += " [| ";
      visit(term.getChannelSet());
      str_ += " |] ";
      visit(term.getRightAction());
      /////////////////////////////////////////////////////////////////////////////////////////
      
//      /**
//       * 2. assemble variable block
//       */
//      // 2.1 determine type expr for all variables in pv
//      Set<Pair<String, Term>> setPv = new HashSet<Pair<String, Term>>();
//      List<Pair<String, Term>> temp = new ArrayList<Pair<String, Term>>();
//      isStateWithExpr(pv.toString(), temp);
//      setPv.addAll(temp);
//      isLocVar(pv.toString(), temp);
//      setPv.addAll(temp);
//
//      // 2.2 all variables in pv are renamed
//      // a table of <varname, <tvarname, expr>>
//      Map<String, Pair<String, Term>> mapPv = new HashMap<String, Pair<String, Term>>();
//      for (Pair<String, Term> p : setPv) {
//        mapPv.put(p.getFirst(),
//            new Pair<String, Term>(MessageFormat.format(FormatPattern.TEMP_VAR_PATT, p.getFirst()),
//                p.getSecond()));
//      }
//
//      // 2.3 renaming all variables in A1 and A2 to temporary variables
//      // rename variables to parameters in action ca
////      List<Pair<String, String>> lstOldNew = new ArrayList<Pair<String, String>>();
////      for(String s: pv) {
////        lstOldNew.add(new Pair<String, String>(s, MessageFormat.format(FormatPattern.TEMP_VAR_PATT, s)));
////      }
////      VariableRenamingSchemaVisitor vrsv = new VariableRenamingSchemaVisitor(
////          VariableRenameSchema.VRS_ACTION_RENAME, lstOldNew);
////      
////      // TODO: if action is CallAction (a reference to action), how can we rename variables to temporary variables
////      term2.getLeftAction().accept(vrsv);
////      term2.getRightAction().accept(vrsv);
//
//      ParallelAction pa = ZUtils.cloneTerm(term);
////      ((CircusNameSet)pa.getLeftNameSet())
//      pa.setLeftNameSet(cfac_.createCircusNameSet(fac_.createSetExpr(fac_.createZExprList())));
//      pa.setRightNameSet(cfac_.createCircusNameSet(fac_.createSetExpr(fac_.createZExprList())));
//      CircusAction ca = pa;
//
//      // 2.4 assemble variable block
//      // paraName
//      String paraName = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.PARA_ACTION_NAME_PATT), proname_,
//          map_.incn());
//      ZDeclList declList = fac_.createZDeclList();
//      Pred pred = null;
//
////      Map<String, Pair<String, Term>> mapPv
//      // assignment in the front of variable block
//      List<ZName> lstAssFrtZName = new ArrayList<ZName>();
//      List<Expr> lstAssFrtExpr = new ArrayList<Expr>();
//      
//      // assignment in the end of A1 to restore variables which are not in ns1
//      List<ZName> lstAssBhdZName1 = new ArrayList<ZName>();
//      List<Expr> lstAssBhdExpr1 = new ArrayList<Expr>();
//      
//      // assignment in the end of A2 to restore variables which are not in ns2
//      List<ZName> lstAssBhdZName2 = new ArrayList<ZName>();
//      List<Expr> lstAssBhdExpr2 = new ArrayList<Expr>();
//
//      Iterator<Entry<String, Pair<String, Term>>> it = mapPv.entrySet().iterator();
//      while (it.hasNext()) {
//        Map.Entry<String, Pair<String, Term>> pairs = (Map.Entry<String, Pair<String, Term>>) it
//            .next();
//
//        if (pairs != null) {
//          // VarDecl
//          // create Name List with Stroke
//          List<Name> ln = new ArrayList<Name>();
//          Name name = fac_.createZName(pairs.getValue().getFirst(), fac_.createZStrokeList(), null);
//          ln.add(name);
//          // create Namelist
//          NameList nl1 = fac_.createZNameList(ln);
//          VarDecl vd = fac_.createVarDecl(nl1, (Expr) (pairs.getValue().getSecond()));
//          declList.add(vd);
//
//          // Assignment
//          lstAssFrtZName.add((ZName) name);
//          lstAssFrtExpr.add(fac_.createRefExpr(
//              fac_.createZName(pairs.getKey(), fac_.createZStrokeList(), null),
//              fac_.createZExprList(), false, false));
//
//          // For the variables in pv1 but not in ns1, we need to restore
//          if (pv1.contains(pairs.getKey()) && !ns1.contains(pairs.getKey())) {
//            lstAssBhdZName1.add(fac_.createZName(pairs.getKey(), fac_.createZStrokeList(), null));
//            lstAssBhdExpr1.add(fac_.createRefExpr(
//                fac_.createZName(pairs.getValue().getFirst(), fac_.createZStrokeList(), null),
//                fac_.createZExprList(), false, false));
//          }
//          
//       // For the variables in pv2 but not in ns2, we need to restore
//          if (pv2.contains(pairs.getKey()) && !ns2.contains(pairs.getKey())) {
//            lstAssBhdZName2.add(fac_.createZName(pairs.getKey(), fac_.createZStrokeList(), null));
//            lstAssBhdExpr2.add(fac_.createRefExpr(
//                fac_.createZName(pairs.getValue().getFirst(), fac_.createZStrokeList(), null),
//                fac_.createZExprList(), false, false));
//          }
//        }
//      }
//
//      if(!lstAssBhdZName1.isEmpty()) {
//        // AssignmentCommand
//        ZExprList lstZExpr = fac_.createZExprList(lstAssBhdExpr1);
//        AssignmentPairs assPair = cfac_.createAssignmentPairs(fac_.createZNameList(lstAssBhdZName1),
//            lstZExpr);
//        AssignmentCommand assCmd = cfac_.createAssignmentCommand(assPair);
//        
//        // SeqAction
//        List<CircusAction> lstCAction = new ArrayList<CircusAction>();
//        lstCAction.add(((ParallelAction)ca).getLeftAction());
//        lstCAction.add(assCmd);
//        
//        ((ParallelAction)ca).setLeftAction(cfac_.createSeqAction(lstCAction));
//      }
//      
//      if(!lstAssBhdZName2.isEmpty()) {
//        // AssignmentCommand
//        ZExprList lstZExpr = fac_.createZExprList(lstAssBhdExpr2);
//        AssignmentPairs assPair = cfac_.createAssignmentPairs(fac_.createZNameList(lstAssBhdZName2),
//            lstZExpr);
//        AssignmentCommand assCmd = cfac_.createAssignmentCommand(assPair);
//        
//        // SeqAction
//        List<CircusAction> lstCAction = new ArrayList<CircusAction>();
//        lstCAction.add(((ParallelAction)ca).getRightAction());
//        lstCAction.add(assCmd);
//        
//        ((ParallelAction)ca).setRightAction(cfac_.createSeqAction(lstCAction));
//      }
//      
//      // assignment in the beginning of variable block
//      if (!lstAssFrtZName.isEmpty()) {
//        // AssignmentCommand
//        ZExprList lstZExpr = fac_.createZExprList(lstAssFrtExpr);
//        AssignmentPairs assPair = cfac_.createAssignmentPairs(fac_.createZNameList(lstAssFrtZName),
//            lstZExpr);
//        AssignmentCommand assCmd = cfac_.createAssignmentCommand(assPair);
//        
//        // SeqAction
//        List<CircusAction> lstCAction = new ArrayList<CircusAction>();
//        lstCAction.add(assCmd);
//        lstCAction.add(pa);
//        ca = cfac_.createSeqAction(lstCAction);
//      }
//
////      AxPara axpara = assembleZPara(paraName, pred, declList);
//      VarDeclCommand vdc = cfac_.createVarDeclCommand(declList, ca);
//      visit(vdc);
    }

    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitExtChoiceProcessIte(ExtChoiceProcessIte term)
  {
    String str = str_;
    
    str_ += " [] ";
    List<Pair<Name, Expr>> lstP = new ArrayList<Pair<Name, Expr>>();
    for(Decl decl: term.getZDeclList()) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          lstP.add(new Pair<Name, Expr>(name, ((VarDecl)decl).getExpr()));
        }
      }
    }
    
    boolean first = true;

    for(Pair<Name, Expr> p: lstP) {
      if(first) {
        first = false;
      } else {
        str_ += ", ";
      }

      visit(p.getFirst());
      str_ += ":";
      visit(p.getSecond());
    }
    
    str_ += " @ ";
    visit(term.getCircusProcess());

    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitParallelProcessIdx(ParallelProcessIdx term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitOutputFieldAnn(OutputFieldAnn term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitOnTheFlyDefAnn(OnTheFlyDefAnn term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitLetVarAction(LetVarAction term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitParamProcess(ParamProcess term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNameSetPara(NameSetPara term)
  {
    String str = str_;
    String nsName = Circus2ZCSPUtils.termToString(term.getZName());
    NameSet ns = term.getNameSet();
    String strNS = Circus2ZCSPUtils.termToString(ns);
    map_.addNameSet(para_name_, nsName, strNS, ns);
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSeqProcessIte(SeqProcessIte term)
  {
    String str = str_;
    
    str_ += " ; ";
    List<Pair<Name, Expr>> lstP = new ArrayList<Pair<Name, Expr>>();
    for(Decl decl: term.getZDeclList()) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          lstP.add(new Pair<Name, Expr>(name, ((VarDecl)decl).getExpr()));
        }
      }
    }
    
    boolean first = true;

    for(Pair<Name, Expr> p: lstP) {
      if(first) {
        first = false;
      } else {
        str_ += ", ";
      }

      visit(p.getFirst());
      str_ += ":";
      visit(p.getSecond());
    }
    
    str_ += " @ ";
    visit(term.getCircusProcess());

    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitParallelProcess(ParallelProcess term)
  {
    String str = str_;
    
    visit(term.getLeftProcess());
    str_ += " [| ";
    visit(term.getChannelSet());
    str_ += " |] ";
    visit(term.getRightProcess());
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSchExprAction(SchExprAction term)
  {
    String str = str_;

    Expr expr = term.getExpr();

    ZName name = ((RefExpr)expr).getZName();
    String strName = safe_visit(expr);

    // get the corresponding AxPara
    assert(process_para_.getCircusProcess() instanceof BasicProcess);
    
    // if this is visited before, just ignored it
    String strAct = isVisited(name, (process_para_.getZName()));
    if(strAct != null) {
      str_ += strAct;
      return strAct;
    }
    
    levels_++;
    String pre = prefixAlignString();

    AxPara schPara = null;
    /**
     * for the SchExpr from assignment, additional schema to retrieve state component, and coercion
     * there's no corresponding negative shcema precondition. 
     * So its translation is simple
     */
    boolean negSchFound = false;
    ZName negName = fac_.createZName(
        MessageFormat.format(FormatPattern.NEG_PRECONDITION_SCHEMA, strName), 
        fac_.createZStrokeList(), null);
    
    for(Para para: process_para_.getCircusBasicProcess().getZParaList()) {   
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
            }
            else if(Circus2ZCSPUtils.isEquals(pname, negName)) {
              negSchFound = true;
            }
            break;
          default:
            throw new CztException("AxPara after rewritting can not be a " + Circus2ZCSPUtils.getAxParaKind((AxPara) para).toString());
        }
      }
    }

    if(negSchFound) {
      if(Circus2ZCSPUtils.isASchemaWithPrecondAlwaysTrue(para_name_, schPara, map_)) {
        negSchFound = false;
      }
    }
    
    // channel expression
    String strSch = strName;
    String strSchOut = "";
    // channel declaration
    String strChnDecl = "channel " + strName;
    String strNegChnDecl = "channel " + Circus2ZCSPUtils.termToString(negName);
    
    if(schPara != null) {
      // Op!ins?outs
//      strSch = (String) schPara.accept(new SchemaExprInOutsVisitor(zsectname_, manager_));
    }
    else{
      throw new CztException("Can not find the corresponding schema [" + 
          Circus2ZCSPUtils.termToString(name) + "] in " + 
          Circus2ZCSPUtils.termToString(process_para_.getZName()));
    }
    
    // get declaration list
    DeclListExpansionVisitor dlevisitor = 
        new DeclListExpansionVisitor(process_para_.getCircusBasicProcess(), zsect_, manager_, zsectname_);
    // after renaming, normalisation might not work properly, so disable it
    dlevisitor.disableNormalisation();
    schPara.accept(dlevisitor);
    List<Pair<ZName, Expr>> lstZNameExpr = dlevisitor.getNameExprPairAsList();
    
    // get all input variables from the schema, but for this channel definition, they are 
    // output variables
    Set<LocalVariableEntry> setOutLocVar = new HashSet<LocalVariableEntry>();
    // get all output variables from the schema, but for this channel definition, they are 
    // input variables
    Set<LocalVariableEntry> setInsLocVar = new HashSet<LocalVariableEntry>();
  
    Set<String> setOuts = new HashSet<String>();
    Set<String> setIns = new HashSet<String>();
    
    String commentInOut = "";
    String commentNeg = "";

    // order the 
    TreeSet<Pair<ZName, Expr>> orderedZNameExpr = new TreeSet<Pair<ZName, Expr>>(new pairNameTComparator<Expr>());
    orderedZNameExpr.addAll(lstZNameExpr);
    String prefix = MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_, "");
    boolean firstChnType = true;
    boolean firstNegChnType = true;
    
    // debug
    String unsort = "Before sort [";
    String sorted = "After sort [";

    for(Pair<ZName, Expr> p: lstZNameExpr) {
      unsort += p.getFirst().toString() + " ";
    }

    Collections.sort(lstZNameExpr, new pairNameTComparator<Expr>());
    
    for(Pair<ZName, Expr> p: lstZNameExpr) {
      sorted += p.getFirst().toString() + " ";
    }
    unsort += "]";
    sorted += "]";
    Debug.debug_print(unsort);
    Debug.debug_print(sorted);
    
    for(Pair<ZName, Expr> p: orderedZNameExpr) {
      // check if it is input variable (v?)
      if(p.getFirst().getZStrokeList().size() > 0 && 
          p.getFirst().getZStrokeList().get(p.getFirst().getZStrokeList().size() - 1) instanceof InStroke) {
        ZName n = ZUtils.cloneTerm(p.getFirst());
        // remove stroke ?
        n.getZStrokeList().remove(n.getZStrokeList().size() - 1);
        String v = Circus2ZCSPUtils.termToString(n);
        // for the variables that has been renamed to 
        if(v.startsWith(prefix)) {
          v = v.replace(prefix, "");
        }
        
        setOuts.add(v); // v
        commentInOut = commentInOut + "!" + v;
        strSch += "!" + v;
        strSchOut += "!" + v;
        
        String type = safe_visit(p.getSecond());
        if(firstChnType || firstNegChnType) {
          strChnDecl += ": " + type;
          strNegChnDecl += ": " + type;
          firstChnType = false;
          firstNegChnType = false;
        }
        else {
          strChnDecl += "." + type;
          strNegChnDecl += "." + type;
        }
      }
    }
    
    commentNeg = commentInOut;
    
    for(Pair<ZName, Expr> p: orderedZNameExpr) {
      // check if it is output variable (v!)
      if(p.getFirst().getZStrokeList().size() > 0 && 
          p.getFirst().getZStrokeList().get(p.getFirst().getZStrokeList().size() - 1) instanceof OutStroke) {
        ZName n = ZUtils.cloneTerm(p.getFirst());
        // remove stroke !
        n.getZStrokeList().remove(n.getZStrokeList().size() - 1);
        String v = Circus2ZCSPUtils.termToString(n);
        // for the variables that has been renamed to 
        if(v.startsWith(prefix)) {
          v = v.replace(prefix, "");
        }

        setIns.add(v); // v
        commentInOut = commentInOut + "?" + v;
        strSch += "?" + v;
        
        String type = safe_visit(p.getSecond());
        if(firstChnType) {
          strChnDecl += ": " + type;
          firstChnType = false;
        }
        else {
          strChnDecl += "." + type;
        }
      }
    }
    
    setOutLocVar = getLocVar(setOuts);
    setInsLocVar = getLocVar(setIns);

//    // get all input variables from the schema, but for this channel definition, they are 
//    // output variables
//    Set<LocalVariableEntry> setOutLocVar = new HashSet<LocalVariableEntry>();
//    // get all output variables from the schema, but for this channel definition, they are 
//    // input variables
//    Set<LocalVariableEntry> setInsLocVar = new HashSet<LocalVariableEntry>();
//
//    Set<String> setOuts = new HashSet<String>();
//    Set<String> setIns = new HashSet<String>();
//    String prefix = MessageFormat.format(FormatPattern.RENAMING_IN_PROC, para_name_, "");
//    for(Pair<ZName, Expr> p: lstZNameExpr) {
//      // check if it is input variable (v?)
//      if(p.getFirst().getZStrokeList().size() > 0 && 
//          p.getFirst().getZStrokeList().get(p.getFirst().getZStrokeList().size() - 1) instanceof InStroke) {
//        ZName n = ZUtils.cloneTerm(p.getFirst());
//        // remove stroke ?
//        n.getZStrokeList().remove(n.getZStrokeList().size() - 1);
//        String v = Circus2ZCSPUtils.termToString(n);
//        // for the variables that has been renamed to 
//        if(v.startsWith(prefix)) {
//          v = v.replace(prefix, "");
//        }
//        setOuts.add(v); // v
//        
//        strSch += "!" + v;
//        strSchOut += "!" + v;
//      }
//
//      // check if it is input variable (v!)
//      if(p.getFirst().getZStrokeList().size() > 0 && 
//          p.getFirst().getZStrokeList().get(p.getFirst().getZStrokeList().size() - 1) instanceof OutStroke) {
//        ZName n = ZUtils.cloneTerm(p.getFirst());
//        // remove stroke !
//        n.getZStrokeList().remove(n.getZStrokeList().size() - 1);
//        String v = Circus2ZCSPUtils.termToString(n);
//        // for the variables that has been renamed to 
//        if(v.startsWith(prefix)) {
//          v = v.replace(prefix, "");
//        }
//
//        setIns.add(v); // v
//        strSch += "?" + v;
//      }
//    }
//
//    setOutLocVar = getLocVar(setOuts);
//    setInsLocVar = getLocVar(setIns);
//
////    // remove channel name and all input expression (?x) to leave "!x!y" left
////    String outs = strSch.replaceAll("\\A[^!]+", "").replaceAll("\\?[^!]*", "");
//    
////    // get input variables and output local variables from strSch
////    Set<LocalVariableEntry> setOutLocVar = new HashSet<LocalVariableEntry>();
//
////    if(!outs.equals("")) {
////      String[] insVar = outs.split("\\!");
////      Set<String> set = new HashSet<String>();
////      for(String s: insVar) {
////        if(!s.trim().equals("")) {
////          set.add(s);
////        }
////      }
////      setOutLocVar = getLocVar(set);
////    }
//
////    // remove channel name and all output expression (!x) to leave "?x?y" left
////    String ins = strSch.replaceAll("\\A[^?]+", "").replaceAll("![^?]*", "");
////    Set<LocalVariableEntry> setInsLocVar = new HashSet<LocalVariableEntry>();
////
////    if(!ins.equals("")) {
////      String[] outsVar = ins.split("\\?");
////      Set<String> set = new HashSet<String>();
////      for(String s: outsVar) {
////        if(!s.trim().equals("")) {
////          set.add(s);
////        }
////      }
////      setInsLocVar = getLocVar(set);
////    }
//    
    String strGet = "";
    String strSet = "";
    for(LocalVariableEntry p: setInsLocVar) {
      strSet += MessageFormat.format(
          CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_PUT), p.getNumber())
          + "!" + p.getName();
      strSet += " -> ";
    }
    
    for(LocalVariableEntry p: setOutLocVar) {
      if(p.isFromVarBlock()) {
        strGet += MessageFormat.format(
            CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_GET), p.getNumber())
            + "!" + p.getName();
        strGet += " -> ";
      }
    }

//    ChannelDeclVisitor cvisitor = new ChannelDeclVisitor();
//    schPara.accept(cvisitor);
//    Debug.debug_print("Channels: " + cvisitor.getChannels());
//    cspspec_.addChannel(cvisitor.getChannels());
//    cspspec_.addHideCSPB(strName);
    
    strChnDecl += "-- " + commentInOut;
    cspspec_.addChannel(strChnDecl);
    cspspec_.addHideCSPB(strName);

    if(negSchFound) {
      if(!strGet.isEmpty()) {
        str_ += strGet + "\n";
      }
      if(!str_.endsWith("\n")) {
        str_ += "\n";
      }
      str_ += pre + "(   " + strSch + " -> " + strSet + " SKIP" + "\n";
      str_ += pre + " [] " + MessageFormat.format(FormatPattern.NEG_PRECONDITION_SCHEMA, strName) 
          + strSchOut + " -> " + strSet + "DIV" + "\n";
      str_ += pre + ")";
      
//      PrecChannelDeclVisitor pcvisitor = new PrecChannelDeclVisitor();
//      schPara.accept(pcvisitor);
//      Debug.debug_print("Channels: " + pcvisitor.getChannels());
//      cspspec_.addChannel(pcvisitor.getChannels());      
//      cspspec_.addHideCSPB(Circus2ZCSPUtils.termToString(negName));
      strNegChnDecl += " -- " + commentNeg;
      cspspec_.addChannel(strNegChnDecl);
      cspspec_.addHideCSPB(Circus2ZCSPUtils.termToString(negName));
    }
    else {
      str_ += strGet + "(" + strSch + " -> " + strSet + " SKIP)";
    }
    
    levels_--;
    String tmp = subStr(str_, str);
    markAsVisited(new Node(name, process_para_.getZName()), tmp);

    return tmp;
  }

  @Override
  public Object visitStopAction(StopAction term)
  {
    String str = str_;
    
    str_ += "STOP";
    String tmp = subStr(str_, str);
    
    return tmp;  
  }

  @Override
  public Object visitQualifiedDecl(QualifiedDecl term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSigmaExpr(SigmaExpr term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitParallelProcessIte(ParallelProcessIte term)
  {
    String str = str_;
    
    str_ += " [| ";
    visit(term.getChannelSet());
    str_ += " |] ";
    
    List<Pair<Name, Expr>> lstP = new ArrayList<Pair<Name, Expr>>();
    for(Decl decl: term.getZDeclList()) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          lstP.add(new Pair<Name, Expr>(name, ((VarDecl)decl).getExpr()));
        }
      }
    }
    
    boolean first = true;

    for(Pair<Name, Expr> p: lstP) {
      if(first) {
        first = false;
      } else {
        str_ += ", ";
      }

      visit(p.getFirst());
      str_ += ":";
      visit(p.getSecond());
    }
    
    str_ += " @ ";
    visit(term.getCircusProcess());

    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCallProcess(CallProcess term)
  {
    String str = str_;
    
    CallUsage cu = term.getCallUsage();
    
    if(cu.equals(CallUsage.Parameterised)) {
      // It is a specially treated invocation of parametrised process, 
      // see CircusRewriteVisitor.assembleParaAndIndexProcessInvocation for more information
      RefExpr re = ZUtils.cloneTerm(term.getCallExpr());
      
      // clear the ZExprList in term
      term.getCallExpr().setExprList(fac_.createZExprList());
      
      if(re.getExprList() != null && !re.getZExprList().isEmpty()) {
        // construct AndPred (v1 = e1) \land (v2 = e2)
        // the format of zel is like [v1, e1, v2, e2]
        List<Pred> lstPred = new ArrayList<Pred>();
        ZExprList zel = re.getZExprList();
        // recover to a guarded command
        for(int i = 0; i < zel.size(); /*i += 2*/) {
          Expr v1 = zel.get(i++);
          Expr e1 = zel.get(i++);
          List<Expr> lstTempExpr = new ArrayList<Expr>();
          lstTempExpr.add(e1);
          SetExpr se = fac_.createSetExpr(fac_.createZExprList(lstTempExpr));
          
          lstTempExpr.clear();
          lstTempExpr.add(v1);
          lstTempExpr.add(se);
          // equality
          Pred p = fac_.createMemPred(lstTempExpr, true);
          lstPred.add(p);
        }
        
        Pred pred = null;
        if(lstPred.size() > 1) {
          pred = fac_.createAndPred(lstPred, And.Wedge);
        }
        else {
          pred = lstPred.get(0);
        }
        
        String strPred = safe_visit(pred);
        str_ += strPred + " & ";
      }
    }
    
    String call = safe_visit(term.getCallExpr());
    
    referred_processes_.add(call);
    
    str_ += call;
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitIntChoiceProcessIte(IntChoiceProcessIte term)
  {
    String str = str_;
    
    str_ += " |~| ";
    List<Pair<Name, Expr>> lstP = new ArrayList<Pair<Name, Expr>>();
    for(Decl decl: term.getZDeclList()) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          lstP.add(new Pair<Name, Expr>(name, ((VarDecl)decl).getExpr()));
        }
      }
    }
    
    boolean first = true;

    for(Pair<Name, Expr> p: lstP) {
      if(first) {
        first = false;
      } else {
        str_ += ", ";
      }

      visit(p.getFirst());
      str_ += ":";
      visit(p.getSecond());
    }
    
    str_ += " @ ";
    visit(term.getCircusProcess());

    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitProcessSignature(ProcessSignature term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitExtChoiceActionIte(ExtChoiceActionIte term)
  {
    String str = str_;
    
//    int nrOfVarDecl = 0;
    List<Pair<Name, Expr>> lstP = new ArrayList<Pair<Name, Expr>>();
    for(Decl decl: term.getZDeclList()) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          lstP.add(new Pair<Name, Expr>(name, ((VarDecl)decl).getExpr()));
//          LocalVariableEntry e = new LocalVariableEntry(
//              Circus2ZCSPUtils.termToString(name), 
//              ((VarDecl)decl).getExpr(), false,
//              map_.getAndIncVarNum());
//          loc_vars_stack_.push(e);
//          nrOfVarDecl++;
        }
      }
    }

    String action = safe_visit(term.getCircusAction());
    String[] removedAction = {""};
    String strPre = FVar(action, removedAction);

    str_ += strPre + "(";
    str_ += " [] ";
    
    boolean first = true;

    for(Pair<Name, Expr> p: lstP) {
      if(first) {
        first = false;
      } else {
        str_ += ", ";
      }

      visit(p.getFirst());
      str_ += ":";
      visit(p.getSecond());
    }
    
    str_ += " @ (";
    str_ += removedAction[0];
    str_ += "))";

    // update context by removing
//    while(nrOfVarDecl > 0) {
//      loc_vars_stack_.pop();
//      nrOfVarDecl--;
//    }

    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitIfGuardedCommand(IfGuardedCommand term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitProcessType(ProcessType term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitInterleaveAction(InterleaveAction term)
  {
    String str = str_;
    
    str_ += "(";
    visit(term.getLeftAction());
    str_ += " ||| ";
    visit(term.getRightAction());
    str_ += ")";
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitPrefixingAction(PrefixingAction term)
  {
    String str = str_;
    
    // the fileds counting, used to get the right type for each field
    // For example,
    // channel c: A \cross B \cross C
    // c?x!y?z -> SKIP
    // there are three fields and with this number we can get the type
    // for x is A, for y is B, and for z is C
    int fieldCnt = 0;
    
    // Number of input variables
    int inVarsCnt = 0;
    
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
    
    // channel name
    visit(term.getCommunication().getChannelExpr());
    
    // a set of local variables triple for getting their value
    // get1?x -> get2?y -> 
    Set<LocalVariableEntry> getEntrySet = new HashSet<LocalVariableEntry>();
    // a set of local variables triple for setting their value
    // set1!x -> set2!y -> 
 
    Set<LocalVariableEntry> setEntrySet = new HashSet<LocalVariableEntry>();
    
    switch(term.getCommunication().getCommPattern()) {
      case Synch:
        break;
      case Input:
      case Output:
      case Mixed:
        CircusFieldList cfl = term.getCommunication().getCircusFieldList();

        for (Field field : cfl) {
          if (field instanceof DotField) {
            str_ += ".("; 
            visit(((DotField)field).getExpr());
            str_ += ")";
            
            // find out which local variables are evaluated in the expression
            ZNameSetVisitor v = new ZNameSetVisitor();
            ((DotField)field).getExpr().accept(v);
            Set<String> nameset = v.getStrSet();
            Set<LocalVariableEntry> entry = getLocVar(nameset);
            getEntrySet.addAll(entry);
          }
          else if (field instanceof InputField) {
            Pred r = ((InputField)field).getRestriction();
            // c?x:{true}
            if((r != null)) {
              ZName n = ((InputField)field).getVariableZName();
              String nv = safe_visit(n);
              if (r instanceof TruePred) {
                str_ += "?" + nv;
              }
              else {
                str_ += "?" + nv + " : {" + nv + " | " + nv + " <- ";
                visit(te.get(fieldCnt));
                str_ += ", ";
                visit(r);
                str_ += "}";
              }
              
              // if nv is not a local variable declared in variable block, then add it to local variable stack
              LocalVariableEntry e = getLocVar(nv);
              if(e == null) {
                // add <VarName, Tvar>
                LocalVariableEntry p = new LocalVariableEntry(
                    Circus2ZCSPUtils.termToString(n), 
                    te.get(fieldCnt), false,
                    map_.getAndIncVarNum());
                loc_vars_stack_.push(p);
                inVarsCnt++;
              }
              else {
                if(e.isFromVarBlock()) {
                  setEntrySet.add(e);
                }
              }
            }
            // c?x:{y:T | p}
          }
          fieldCnt++;
        }
                
        break;
      case ChannelSet:
        break;
      default:
        throw new CztException("Undefined communication pattern [" + 
            term.getCommunication().getCommPattern() + "] for PrefixingAction!");
    }
    
    str_ += " -> ";
    
    for(LocalVariableEntry p: setEntrySet) {
      str_ += MessageFormat.format(
          CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_PUT), p.getNumber())
          + "!" + p.getName();
      str_ += " -> ";
    }
    
    visit(term.getCircusAction());
    
    for(int i = 0; i < inVarsCnt; i++) {
      loc_vars_stack_.pop();
    }
    
    String tmp = subStr(str_, str);
    
    for(LocalVariableEntry p: getEntrySet) {
      if(p.isFromVarBlock()) {
        tmp = MessageFormat.format(
            CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_GET), p.getNumber())
            + "?" + p.getName() + " -> " + tmp;
      }
    }
    
    str_ = str + tmp;
    return tmp;
  }

  @Override
  public Object visitProcessTransformerPred(ProcessTransformerPred term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCircusActionList(CircusActionList term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCommunication(Communication term)
  {
    String str = str_;

    String strBef = str_;
    save_str();

    // channel expression
    String chnname = "" + safe_visit(term.getChannelExpr());
    str_ += chnname;

    for (Field field : term.getCircusFieldList()) {
      if (field instanceof DotField) {
        if (((DotField) field).toString().startsWith(".", 0)) {
          str_ += ".";
        }
        else if (((DotField) field).toString().startsWith("!", 0)) {
          str_ += "!";
        }
        Expr expr = ((DotField) field).getExpr();
        visit(expr);
      }
      else if (field instanceof InputField) {
        str_ += "?";
        String varname = ((InputField) field).getVariableZName().getWord();
        str_ += varname;
        if ((((InputField) field).getRestriction() != null)
            && !(((InputField) field).getRestriction() instanceof TruePred) // not a true restrict
        ) {
          // input restriction
        }
      }
    }

    String strEvt = subStr(str_, strBef);
    restore_str();

    str_ += strEvt;
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitIntChoiceProcessIdx(IntChoiceProcessIdx term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitInputField(InputField term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitHideProcess(HideProcess term)
  {
    String str = str_;
    
    str_ += "( ";
    visit(term.getCircusProcess());
    str_ += " ) \\ ";
    visit(term.getChannelSet());
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitActionPara(ActionPara term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSeqAction(SeqAction term)
  {
    String str = str_;
    
//    levels_++;
//    String pre = prefixAlignString();
    
//    str_ += pre;
    str_ += " (";
    visit(term.getLeftAction());
    str_ += " ; ";
    visit(term.getRightAction());
    str_ += ") ";
    
//    levels_--;
    
    String tmp = subStr(str_, str);
    
    return tmp;
  }

  @Override
  public Object visitExtChoiceProcess(ExtChoiceProcess term)
  {
    String str = str_;
    
    str_ += "(";
    visit(term.getLeftProcess());
    str_ += " [] ";
    visit(term.getRightProcess());
    str_ += ")";
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitLetMuAction(LetMuAction term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZSignatureList(ZSignatureList term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitAssignmentCommand(AssignmentCommand term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitChannelType(ChannelType term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitActionType(ActionType term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSeqActionIte(SeqActionIte term)
  {
    String str = str_;
    
    String action = safe_visit(term.getCircusAction());
    String[] removedAction = {""};
    String strPre = FVar(action, removedAction);

    str_ += strPre + "(";
    str_ += " ; ";
    List<Pair<Name, Expr>> lstP = new ArrayList<Pair<Name, Expr>>();
    for(Decl decl: term.getZDeclList()) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          lstP.add(new Pair<Name, Expr>(name, ((VarDecl)decl).getExpr()));
        }
      }
    }
    
    boolean first = true;

    for(Pair<Name, Expr> p: lstP) {
      if(first) {
        first = false;
      } else {
        str_ += ", ";
      }

      visit(p.getFirst());
//      str_ += ":";
      str_ += ": seq(";
      // TODO? actually the type of variables in declaration should be sequence instead of set
      // However in CZT, it only parses the set correctly and error with sequence
      // here we convert it to sequence in CSP
      visit(p.getSecond());
      str_ += ")";
    }
    
    str_ += " @ (";
    str_ += removedAction[0];
    str_ += "))";
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitIntChoiceActionIte(IntChoiceActionIte term)
  {
    String str = str_;
    
    String action = safe_visit(term.getCircusAction());
    String[] removedAction = {""};
    String strPre = FVar(action, removedAction);

    str_ += strPre + "(";
    str_ += " |~| ";
    List<Pair<Name, Expr>> lstP = new ArrayList<Pair<Name, Expr>>();
    for(Decl decl: term.getZDeclList()) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          lstP.add(new Pair<Name, Expr>(name, ((VarDecl)decl).getExpr()));
        }
      }
    }
    
    boolean first = true;

    for(Pair<Name, Expr> p: lstP) {
      if(first) {
        first = false;
      } else {
        str_ += ", ";
      }

      visit(p.getFirst());
      str_ += ":";
      visit(p.getSecond());
    }
    
    str_ += " @ (";
    str_ += removedAction[0];
    str_ += "))";

    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCallAction(CallAction term)
  {
    String str = str_;
    
    if (circus_muaction_stack_.contains(term.getZName())) {
      // nothing changed and just return
      str_ += visit(term.getZName());
    }
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSpecStmtCommand(SpecStmtCommand term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitStateUpdateAnn(StateUpdateAnn term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitChannelDecl(ChannelDecl term)
  {
    save_str();
    String str = str_;
    
    str_ += "channel ";
    for(int i = 0; i < term.getZChannelNameList().size(); i++) {
      if(i != 0) {
        str_ += ",";
      }
      visit(term.getZChannelNameList().get(i));
      
      visitReferenceOfZName((ZName) term.getZChannelNameList().get(i), null, false);
    }

    str_ += " : ";
    channel_decl_ = true;
    visit(term.getExpr());
    channel_decl_ = false;
    
    if(str_.endsWith(" : $$SYNCH")) {
      str_ = str_.replace(" : $$SYNCH", "");
    }
    
    String tmp = subStr(str_, str);
    cspspec_.addChannel(tmp);

    restore_str();
    
    for(Name name: term.getZChannelNameList()) {
      markAsVisited(new Node((ZName) name, (ZName)null), tmp);
    }
    
    return "";
  }

  @Override
  public Object visitNameSetType(NameSetType term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitInterleaveProcessIdx(InterleaveProcessIdx term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitProcessSignatureAnn(ProcessSignatureAnn term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitMuAction(MuAction term)
  {
    String str = str_;
    
    levels_++;
    circus_muaction_stack_.add(term.getZName());
    String pre = prefixAlignString();

    String action = safe_visit(term.getCircusAction());

    str_ += "\n" + pre + "let ";
    visit(term.getZName());
    str_ += " = " + "\n";
    levels_++;
    str_ += prefixAlignString() + action + "\n";
    levels_--;
    str_ += pre + "within ";
    visit(term.getZName());
    
    circus_muaction_stack_.pop();
    
    levels_--;
    String tmp = subStr(str_, str);

    return tmp;
  }

  /**
   * Remove F_{VarPre} from the process in CSP and return them in the list
   * @param process - such as get0?x -> get1?y -> P
   * @param lstGet - a list of get events [get0?x, get1?y]
   * @return
   *    the process with the prefix get events are removed (P)
   */
  private String removeFVarPre(String process, List<String> lstGet)
  {
    String ret = process;
    
    lstGet.clear();

    // get the F_{VarPre}
    // pattern: ^(get[0-9]+?\w ->)
//    Pattern patt = Pattern.compile(
//        "\\A\\s*" + CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_GET).replace("{0}", "") + 
//        "[0-9]+\\?\\w\\s*\\Q->\\E\\s*");
    
    Pattern patt = Pattern.compile(
        "\\A(get[0-9]+\\?\\w+\\s*->\\s*)");
    
    do{
      Matcher matcher = patt.matcher(ret);
      StringBuffer sb = new StringBuffer();
    
      if(matcher.find()) {
        String tmp = matcher.group(1);
        matcher.appendReplacement(sb, "");
        matcher.appendTail(sb);
        ret = sb.toString();
        // remove ->
        lstGet.add(tmp.replaceAll("\\s*->\\s*", ""));
      }
      else {
        break;
      }
    }while(true);
    
    return ret;
  }
  
  /**
   * Remove prefixing get events, and return it
   * @param process - the original process with get[0-9]+?x event, such as get0?x -> get1?y -> P 
   * @param afterProcess - the process after removed get events
   * @return
   *    prefix get events (get0?x -> get1?y ->)
   */
  private String FVar(String process, String[] afterProcess) 
  {
    List<String> lstAction = new ArrayList<String>();
    String removed = removeFVarPre(process, lstAction);
    Set<String> pre = new HashSet<String>();
    pre.addAll(lstAction);
    List<String> sorted = new ArrayList<String>();
    sorted.addAll(pre);
    
    Collections.sort(sorted);
    
    String strPre = "";
    for(String s: sorted) {
      strPre += s + " -> ";
    }

    afterProcess[0] = removed;
    return strPre;
  }
  
  /**
   * Remove prefixing get events, and return it
   * @param process - the original process with get[0-9]+?x event, such as get0?x -> get1?y -> P 
   * @param afterProcess - the process after removed get events
   * @return
   *    prefix get events (get0?x -> get1?y ->)
   */
  private String FVar(String process1, String process2, String[] afterProcess) 
  {
    List<String> lstLeft = new ArrayList<String>();
    List<String> lstRight = new ArrayList<String>();
    afterProcess[0] = removeFVarPre(process1, lstLeft);
    afterProcess[1] = removeFVarPre(process2, lstRight);
    
    // remove duplicate "get[0-9]+?l" 
    Set<String> pre = new HashSet<String>();
    pre.addAll(lstLeft);
    pre.addAll(lstRight);

    // sort the get[0-9]+ channel according to their alphabet order
    List<String> sorted = new ArrayList<String>();
    sorted.addAll(pre);
    
    Collections.sort(sorted);
    
    String strPre = "";
    for(String s: sorted) {
      strPre += s + " -> ";
    }

    return strPre;
  }
  
  @Override
  public Object visitExtChoiceAction(ExtChoiceAction term)
  {
    String str = str_;
    levels_++;
    String pre = prefixAlignString();

    String left = safe_visit(term.getLeftAction());
    String right = safe_visit(term.getRightAction());
    
    String[] removedAction = {"", ""};
    String strPre = FVar(left, right, removedAction);
//    str_ += strPre + "(" + removedAction[0] + " [] " + removedAction[1] + ")";
    if(!strPre.isEmpty()) {
      str_ +=  pre + strPre + "\n";
    }
    if(!str_.endsWith("\n")) {
      str_ += "\n";
    }

    str_ +=     pre + "(   " + removedAction[0] + "\n" 
              + pre + " [] " + removedAction[1] + "\n"
              + pre + ")";
    levels_--;
    String tmp = subStr(str_, str);
    
    return tmp;
  }

  @Override
  public Object visitSkipAction(SkipAction term)
  {
    String str = str_;
    
    str_ += "SKIP";
    String tmp = subStr(str_, str);
    
    return tmp;  
  }

  @Override
  public Object visitSubstitutionAction(SubstitutionAction term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitChannelSetType(ChannelSetType term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  
  @Override
  public Object visitCircusNameSet(CircusNameSet term)
  {
    String str = str_;

    // if its expression is a reference name for another NameSet, then expand it
    if(term.getExpr() instanceof RefExpr) {
      String nsName = Circus2ZCSPUtils.termToString(term.getExpr());
      Pair<String, Term> p = map_.getNameSet(para_name_, nsName);
      
      /* if p is not null, and if its expression is a reference to another NameSet paragraph, then recursively to get it from map_
       */
      while(p != null && p.getSecond() instanceof CircusNameSet && 
          ((CircusNameSet)p.getSecond()).getExpr() instanceof RefExpr) {
        nsName = Circus2ZCSPUtils.termToString(((CircusNameSet)p.getSecond()).getExpr());
        p = map_.getNameSet(para_name_, nsName);
      }
      
      if(p!= null) {
        visit(p.getSecond());
      }
    }
    
    visit(term.getExpr());
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitIntChoiceAction(IntChoiceAction term)
  {
    String str = str_;
    levels_++;

    String pre = prefixAlignString();
    String left = safe_visit(term.getLeftAction());
    String right = safe_visit(term.getRightAction());
    
    String[] removedAction = {"", ""};
    String strPre = FVar(left, right, removedAction);
//    str_ += strPre + "(" + removedAction[0] + " |~| " + removedAction[1] + ")";
    if(!strPre.isEmpty()) {
      str_ +=     pre + strPre + "\n";
    }
    if(!str_.endsWith("\n")) {
      str_ += "\n";
    }

    str_ +=     pre + "(    " + removedAction[0] + "\n" 
              + pre + " |~| " + removedAction[1] + "\n"
              + pre + ")";
    levels_--;

    String tmp = subStr(str_, str);
    
    return tmp;  
  }

  @Override
  public Object visitParamAction(ParamAction term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCircusNameSetList(CircusNameSetList term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitProcessPara(ProcessPara term)
  {
    str_ = "";
    save_str();
    
    String str = str_;
    
    para_name_ = safe_visit(term.getZName());
    process_para_ = term;
    
    processes_.add(para_name_);

    // visit the references of this process
    visitReferenceOfZName(term.getZName(), null, false);
    
    visit(term.getZName());
    str_ += " = ";
    visit(term.getCircusProcess());
    
    String tmp = subStr(str_, str);
    // remove empty line
    // (?m) - enable MULTILINE mode
    tmp = tmp.replaceAll("(?m)^[ \t]*\r?\n", "");
    cspspec_.addProcess(tmp);
    
    para_name_ = null;
    process_para_ = null;
    
    restore_str();
    
    markAsVisited(new Node(term.getZName(), term.getZName()), tmp);
    return "";
  }

  @Override
  public Object visitAlphabetisedParallelAction(AlphabetisedParallelAction term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitBasicChannelSetExpr(BasicChannelSetExpr term)
  {
    String str = str_;
    
    CircusCommunicationList ccl = term.getCircusCommunicationList();
    if (ccl.size() == 0) {
      // empty set
      str_ += "{||}";
    }
    else {
      boolean first = true;
      str_ += "{| ";
      for (Communication c : ccl) {
        if (!first) {
          str_ += ", ";
        }
        else {
          first = false;
        }
        visit(c);
      }
      str_ += " |}";
    }

    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitInterleaveProcessIte(InterleaveProcessIte term)
  {
    String str = str_;
    
    str_ += " ||| ";
    List<Pair<Name, Expr>> lstP = new ArrayList<Pair<Name, Expr>>();
    for(Decl decl: term.getZDeclList()) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          lstP.add(new Pair<Name, Expr>(name, ((VarDecl)decl).getExpr()));
        }
      }
    }
    
    boolean first = true;

    for(Pair<Name, Expr> p: lstP) {
      if(first) {
        first = false;
      } else {
        str_ += ", ";
      }

      visit(p.getFirst());
      str_ += ":";
      visit(p.getSecond());
    }
    
    str_ += " @ ";
    visit(term.getCircusProcess());

    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitDoGuardedCommand(DoGuardedCommand term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitGuardedAction(GuardedAction term)
  {
    String str = str_;
    
 // a set of local variables triple for getting their value
    // get1?x -> get2?y -> 
    Set<LocalVariableEntry> getEntrySet = new HashSet<LocalVariableEntry>();

 // find out which local variables are evaluated in the expression
    ZNameSetVisitor v = new ZNameSetVisitor();
    term.getPred().accept(v);
    Set<String> nameset = v.getStrSet();
    Set<LocalVariableEntry> entry = getLocVar(nameset);
    getEntrySet.addAll(entry);
    
    String g = safe_visit(term.getPred());
    String action = safe_visit(term.getCircusAction());
    
    List<String> lstAction = new ArrayList<String>();
    action = removeFVarPre(action, lstAction);
    Set<String> pre = new HashSet<String>();
    pre.addAll(lstAction);
    
    for(LocalVariableEntry p: getEntrySet) {
      if(p.isFromVarBlock()) {
        pre.add(MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_GET), p.getNumber())
            + "?" + p.getName());
      }
    }

 // sort the get[0-9]+ channel according to their alphabet order
    List<String> sorted = new ArrayList<String>();
    sorted.addAll(pre);
    
    Collections.sort(sorted);
    
    String strPre = "";
    for(String s: sorted) {
      strPre += s + " -> ";
    }
    
    str_ += strPre + "(" + g + " & " + action + ")";
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSeqProcess(SeqProcess term)
  {
    String str = str_;
    
    visit(term.getLeftProcess());
    str_ += " ; ";
    visit(term.getRightProcess());
    String tmp = subStr(str_, str);
    return tmp;  }

  @Override
  public Object visitInterruptAction(InterruptAction term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitAlphabetisedParallelProcessIte(AlphabetisedParallelProcessIte term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitIntChoiceProcess(IntChoiceProcess term)
  {
    String str = str_;
    
    visit(term.getLeftProcess());
    str_ += " |~| ";
    visit(term.getRightProcess());
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCircusStateAnn(CircusStateAnn term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitParallelActionIte(ParallelActionIte term)
  {
    String str = str_;
    
  //  int nrOfVarDecl = 0;
    List<Pair<Name, Expr>> lstP = new ArrayList<Pair<Name, Expr>>();
    for(Decl decl: term.getZDeclList()) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          lstP.add(new Pair<Name, Expr>(name, ((VarDecl)decl).getExpr()));
  //        LocalVariableEntry e = new LocalVariableEntry(
  //            Circus2ZCSPUtils.termToString(name), 
  //            ((VarDecl)decl).getExpr(), false,
  //            map_.getAndIncVarNum());
  //        loc_vars_stack_.push(e);
  //        nrOfVarDecl++;
        }
      }
    }
  
    String action = safe_visit(term.getCircusAction());
    String[] removedAction = {""};
    String strPre = FVar(action, removedAction);
  
    str_ += strPre + "(";
    str_ += " [| ";
    visit(term.getChannelSet());
    str_ += " |] ";
    
    boolean first = true;
  
    for(Pair<Name, Expr> p: lstP) {
      if(first) {
        first = false;
      } else {
        str_ += ", ";
      }
  
      visit(p.getFirst());
      str_ += ":";
      visit(p.getSecond());
    }
    
    str_ += " @ (";
    str_ += removedAction[0];
    str_ += "))";
  
    // update context by removing
  //  while(nrOfVarDecl > 0) {
  //    loc_vars_stack_.pop();
  //    nrOfVarDecl--;
  //  }
  
    String tmp = subStr(str_, str);
    return tmp;

//    String str = str_;
//    
//    unsupported(term);
//    
//    String tmp = subStr(str_, str);
//    return tmp;
  }

  @Override
  public Object visitRenameProcess(RenameProcess term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitBasicProcess(BasicProcess term)
  {
    String str = str_;
    
    levels_ = 0;
    str_ += "\n" + "  ";
    visit(term.getMainAction());
    
    String tmp = subStr(str_, str);
    
    return tmp;
  }

  @Override
  public Object visitRenameAction(RenameAction term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitActionSignature(ActionSignature term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitChannelPara(ChannelPara term)
  {
    for(Decl decl: term.getZDeclList())
    {
      visit(decl);
    }
    return "";
  }

  @Override
  public Object visitActionTransformerPred(ActionTransformerPred term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCircusFieldList(CircusFieldList term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitImplicitChannelAnn(ImplicitChannelAnn term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  /**
   * Add a Mem process for a variable from variable block (x:T @)
   * @param n - the numbering
   * @param varExpr - the type of variable (x:T)
   */
  private void addAdditionalMemProcess(String n, String varExpr)
  {
    /**
     * Mem_i     = set_i?x -> CMem_i(x)
     * CMem_i(x) =    set_i?y -> CMem_i(y) 
     *             [] get_i!x -> CMem_i(x)
     *             [] end -> SKIP
     */
    String strMemProc = MessageFormat.format(
        CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_NAME), n);
    String strCMemProc = MessageFormat.format(
        CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_NAME1), n);
    String strSetChn = MessageFormat.format(
        CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_PUT), n);
    String strGetChn = MessageFormat.format(
        CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_GET), n);
    String strEndChn = MessageFormat.format(
        CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_END), n);
    cspspec_.addVarProcess(strMemProc + " = " + strSetChn + "?x -> " + strCMemProc + "(x)");
    cspspec_.addVarProcess(strCMemProc + "(x) = " + 
        strSetChn + "?y -> " + strCMemProc + "(y)" + " [] " + 
        strGetChn + "!x -> " + strCMemProc + "(x)" + " [] " + 
        strEndChn + " -> SKIP");
    cspspec_.addChannel("channel " + strSetChn + ": " + varExpr);
    cspspec_.addChannel("channel " + strGetChn + ": " + varExpr);
    cspspec_.addChannel("channel " + strEndChn);
    cspspec_.addHideCSPB(strSetChn);
    cspspec_.addHideCSPB(strGetChn);
    cspspec_.addHideCSPB(strEndChn);
  }
  
  @Override
  public Object visitVarDeclCommand(VarDeclCommand term)
  {
    String str = str_;
        
    str_ += "(|~| ";

    // a list of var decl from (variable name, its type)
    List<LocalVariableEntry> lstDecl = new ArrayList<LocalVariableEntry>();
    
    // update context by adding variable declarations
    int nrOfVarDecl = 0;
    for(Decl decl: term.getZDeclList()) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          LocalVariableEntry e = new LocalVariableEntry(
              Circus2ZCSPUtils.termToString(name), 
              ((VarDecl)decl).getExpr(), true,
              map_.getAndIncVarNum());
          lstDecl.add(e);
          loc_vars_stack_.push(e);
          nrOfVarDecl++;
        }
      }
    }
    
    // set1!x -> set2!y -> SKIP
    String strSet = "";
    // {| set1, get1, set2, get2 |}
    String strChnSet = "{| ";
    strChnSet += CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_END) + ", ";
    String strMemPara = "(";
    
    boolean first = true;
    for(LocalVariableEntry p: lstDecl) {
      if(first) {
        first = false;
      }
      else {
        strSet += " -> ";
        strChnSet += ", ";
        strMemPara += " [|{|" + MessageFormat.format(
            CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_END), p.getNumber()) + "|}|] ";
        str_ += ", ";
      }

      str_ += p.getName() + ": ";
      String exp = "" + visit(p.getType());
      addAdditionalMemProcess(p.getNumber(), exp);

      strSet += MessageFormat.format(
          CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_PUT), p.getNumber());
      strSet += "!" + p.getName();

      strChnSet += MessageFormat.format(
          CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_PUT), p.getNumber());
      strChnSet += ", ";
      strChnSet += MessageFormat.format(
          CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_GET), p.getNumber());
      
      strMemPara += MessageFormat.format(
          CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_NAME), p.getNumber());
    }
    strSet += " -> SKIP";
    strChnSet += " |}";
    strMemPara += ")";
    
    str_ += " @ (((";
    str_ += strSet;
    str_ += "; ";
    String act = safe_visit(term.getCircusAction());
    str_ += act;
    str_ += "; end -> SKIP";    
    str_ += ")";
    str_ += " [|" + strChnSet + "|] ";
    str_ += strMemPara;
    str_ += ") \\ " + strChnSet + ")";
    str_ += ")";
    // update context by removing
    while(nrOfVarDecl > 0) {
      loc_vars_stack_.pop();
      nrOfVarDecl--;
    }
    
    String tmp = subStr(str_, str);    
    return tmp;  
  }

  @Override
  public Object visitCommunicationType(CommunicationType term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitInterleaveActionIte(InterleaveActionIte term)
  {
    String str = str_;
    
  //  int nrOfVarDecl = 0;
    List<Pair<Name, Expr>> lstP = new ArrayList<Pair<Name, Expr>>();
    for(Decl decl: term.getZDeclList()) {
      if(decl instanceof VarDecl) {
        for(Name name: ((VarDecl)decl).getZNameList()) {
          lstP.add(new Pair<Name, Expr>(name, ((VarDecl)decl).getExpr()));
  //        LocalVariableEntry e = new LocalVariableEntry(
  //            Circus2ZCSPUtils.termToString(name), 
  //            ((VarDecl)decl).getExpr(), false,
  //            map_.getAndIncVarNum());
  //        loc_vars_stack_.push(e);
  //        nrOfVarDecl++;
        }
      }
    }
  
    String action = safe_visit(term.getCircusAction());
    String[] removedAction = {""};
    String strPre = FVar(action, removedAction);
  
    str_ += strPre + "(";
    str_ += " ||| ";
    
    boolean first = true;
  
    for(Pair<Name, Expr> p: lstP) {
      if(first) {
        first = false;
      } else {
        str_ += ", ";
      }
  
      visit(p.getFirst());
      str_ += ":";
      visit(p.getSecond());
    }
    
    str_ += " @ (";
    str_ += removedAction[0];
    str_ += "))";
  
    // update context by removing
  //  while(nrOfVarDecl > 0) {
  //    loc_vars_stack_.pop();
  //    nrOfVarDecl--;
  //  }
  
    String tmp = subStr(str_, str);
    return tmp;

//    String str = str_;
//    
//    unsupported(term);
//    
//    String tmp = subStr(str_, str);
//    return tmp;
  }

  @Override
  public Object visitDotField(DotField term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitAlphabetisedParallelProcessIdx(AlphabetisedParallelProcessIdx term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitChaosAction(ChaosAction term)
  {
    String str = str_;
    
    str_ += "DIV";
    String tmp = subStr(str_, str);
    
    return tmp;  
  }

  @Override
  public Object visitAlphabetisedParallelProcess(AlphabetisedParallelProcess term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitAlphabetisedParallelActionIte(AlphabetisedParallelActionIte term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitAssignmentPairs(AssignmentPairs term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitInterleaveProcess(InterleaveProcess term)
  {
    String str = str_;
    
    visit(term.getLeftProcess());
    str_ += " ||| ";
    visit(term.getRightProcess());
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitActionSignatureList(ActionSignatureList term)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitListTerm(ListTerm<?> zedObject)
  {
    String str = str_;
    
    String tmp = subStr(str_, str);
    return tmp;
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
 
  /**
   * A comparator according to the first string in the pair
   * @author ykf_2001
   *
   */
  public class pairNameTComparator<T> implements Comparator<Pair<ZName, T>>
  {
    @Override
    public int compare(Pair<ZName, T> x, Pair<ZName, T> y)
    {
      String str1 = Circus2ZCSPUtils.termToString(x.getFirst());
      String str2 = Circus2ZCSPUtils.termToString(y.getFirst());
      
//      boolean b1I = str1.contains("?");
//      boolean b1O = str1.contains("!");
//      boolean b1N = !b1I && !b1O;
//      boolean b2I = str2.contains("?");
//      boolean b2O = str2.contains("!");
//      boolean b2N = !b1I && !b1O;
//
//      // the order
//      // 1. v?
//      // 2. v!
//      // 3. v
//      if((b1I && (b2O || b2N)) || (b1O && b2N)) {
//        return 1;
//      }
//      else if(((b1O || b1N) && b2I) || (b1N && b2O)) {
//        return -1;
//      }

      return str1.compareTo(str2);
//      // x > y
//      if (str1.compareTo(str2) > 0) {
//        return 1;
//      } else if (str1.compareTo(str2) < 0) {
//        return -1;
//      }
//      return 0;
    }
  }

}

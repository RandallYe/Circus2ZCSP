package net.sourceforge.czt.circus2zcsp.util;

import static net.sourceforge.czt.rules.prover.ProverUtils.collectConjectures;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.StringWriter;
import java.io.Writer;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.ListTermVisitor;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.ChannelDecl;
import net.sourceforge.czt.circus.ast.ChannelPara;
import net.sourceforge.czt.circus.ast.ChannelSetPara;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.util.PrintVisitor;
import net.sourceforge.czt.circus.visitor.BasicProcessVisitor;
import net.sourceforge.czt.circus.visitor.CircusVisitor;
import net.sourceforge.czt.circus2zcsp.Debug;
import net.sourceforge.czt.circus2zcsp.TransformerTest;
import net.sourceforge.czt.circus2zcsp.data.Triple;
import net.sourceforge.czt.circus2zcsp.exception.UnfoldException;
import net.sourceforge.czt.circus2zcsp.visitor.CommsVisitor;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.parser.util.DefinitionType;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.print.circus.CircusPrintVisitor;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.RuleTable.RuleTableException;
import net.sourceforge.czt.rules.oldrewriter.Rewrite;
import net.sourceforge.czt.rules.RuleUtils;
import net.sourceforge.czt.rules.UnboundJokerException;
import net.sourceforge.czt.rules.prover.ProverUtils.GetZSectNameVisitor;
import net.sourceforge.czt.rules.rewriter.InnermostTest;
import net.sourceforge.czt.rules.rewriter.RewriteUtils;
import net.sourceforge.czt.rules.rewriter.RewriteVisitor;
import net.sourceforge.czt.rules.rewriter.Rewriter;
import net.sourceforge.czt.rules.rewriter.Strategies;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionInfoException;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.NumExprVisitor;
import net.sourceforge.czt.z.visitor.ZNameVisitor;
import net.sourceforge.czt.z.visitor.ZVisitor;

public class TestUtils
{
  protected final static String TEST_DIR = "/net/sourceforge/czt/circus2zcsp/tests/";
  protected final static String TESTOUT_DIR = "/net/sourceforge/czt/circus2zcsp/tests_output/";
  
  static public List<Term> strToTerm(String str)
  {
    List<Term> lt = new ArrayList<Term>();

    StringSource source = new StringSource(str, "circusTermTest");
    source.setMarkup(Markup.LATEX);
    source.setEncoding("Default");

    SectionManager manager = new SectionManager(Dialect.CIRCUS);
    String name = "spec";
    manager.put(new Key<Source>(name, Source.class), source);

    Spec spec = null;
    try {
      spec = manager.get(new Key<Spec>(name, Spec.class));
      String sectionName = "";
      for (Sect sect : spec.getSect()) {
        // If the section is a ZSection
        if (sect instanceof ZSect) {
          ZSect zSect = (ZSect) sect;
          sectionName = zSect.getName();

          // type check it
          manager.get(new Key<SectTypeEnvAnn>(sectionName, SectTypeEnvAnn.class));

          ZParaList paralist = zSect.getZParaList();
          for (net.sourceforge.czt.z.ast.Para para : paralist) {
            lt.add(para);
//            if (para instanceof ProcessPara) {
//
//            }
//            else if (para instanceof NarrPara) {
//               // skip
//            }
//            else if (para instanceof ChannelPara) {
//
//            }
//            else if (para instanceof LatexMarkupPara) {
//
//            }
//            else if (para instanceof AxPara) // Axiom Definition
//            {
//
//            }
//            else if (para instanceof FreePara) 
//            {
//            }
//            else
//            {
//              
//            }
          }
        }
      }
    }
    catch (SectionInfoException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    catch (CommandException e) {
      // TODO Auto-generated catch block
      System.out.println("------------------------ TEST ERROR START ------------------------");
      if (e instanceof ParseException) {
        System.out.println("" + ((ParseException) e).getMessage());
//        ((ParseException)e).printErrorList();
      }
      else {
        e.printStackTrace();
      }
      System.out.println("------------------------ TEST ERROR END --------------------------");
    }
//    catch (net.sourceforge.czt.parser.util.ParseException e)
//    {
//      
//    }

    return lt;
  }
  
  static public List<Term> strToTerm(String str, ZSect zs)
  {
    List<Term> lt = new ArrayList<Term>();

    StringSource source = new StringSource(str, "circusTermTest");
    source.setMarkup(Markup.LATEX);
    source.setEncoding("Default");

    SectionManager manager = new SectionManager(Dialect.CIRCUS);
    String name = "spec";
    manager.put(new Key<Source>(name, Source.class), source);

    Spec spec = null;
    try {
      spec = manager.get(new Key<Spec>(name, Spec.class));
      String sectionName = "";
      for (Sect sect : spec.getSect()) {
        // If the section is a ZSection
        if (sect instanceof ZSect) {
          ZSect zSect = (ZSect) sect;
          sectionName = zSect.getName();

          // type check it
          manager.get(new Key<SectTypeEnvAnn>(sectionName, SectTypeEnvAnn.class));

          ZParaList paralist = zSect.getZParaList();
          for (net.sourceforge.czt.z.ast.Para para : paralist) {
            lt.add(para);
          }
          
          zs.setParaList(zSect.getParaList());
          zs.setName(zSect.getName());
        }
      }
    }
    catch (SectionInfoException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    catch (CommandException e) {
      // TODO Auto-generated catch block
      System.out.println("------------------------ TEST ERROR START ------------------------");
      if (e instanceof ParseException) {
        System.out.println("" + ((ParseException) e).getMessage());
//        ((ParseException)e).printErrorList();
      }
      else {
        e.printStackTrace();
      }
      System.out.println("------------------------ TEST ERROR END --------------------------");
    }

    return lt;
  }
  
  static public SectionManager strToTerm(String str, List<Term> lt, ZSect zs)
  {
    StringSource source = new StringSource(str, "circusTermTest");
    source.setMarkup(Markup.LATEX);
    source.setEncoding("Default");

    SectionManager manager = new SectionManager(Dialect.CIRCUS);
    String name = "spec";
    manager.put(new Key<Source>(name, Source.class), source);

//    Source unfoldSource = new UrlSource(RuleUtils.getUnfoldRules());
//    manager.put(new Key<Source>("unfold", Source.class), unfoldSource);
    
    Spec spec = null;
    try {
      spec = manager.get(new Key<Spec>(name, Spec.class));
      
      String sectionName = "";
      for (Sect sect : spec.getSect()) {
        // If the section is a ZSection
        if (sect instanceof ZSect) {
          ZSect zSect = (ZSect) sect;
          sectionName = zSect.getName();

          // type check it
          manager.get(new Key<SectTypeEnvAnn>(sectionName, SectTypeEnvAnn.class));

          ZParaList paralist = zSect.getZParaList();
          for (net.sourceforge.czt.z.ast.Para para : paralist) {
            lt.add(para);
          }
          
          zs.setParaList(zSect.getParaList());
          zs.setName(zSect.getName());
        }
      }
    }
    catch (SectionInfoException e) {
      CztException ex = new CztException("Section Error!", e);
      throw ex;
    }
    catch (CommandException e) {
//      System.out.println("------------------------ TEST ERROR START ------------------------");
      if (e instanceof ParseException) {
        System.out.println("" + ((ParseException) e).getMessage());
        CztException ex = new CztException("Parse Error!", e);
        throw ex;
      }
      else {
        CztException ex = new CztException("Type Check Error!", e);
        throw ex;
      }
//      System.out.println("------------------------ TEST ERROR END --------------------------");
    }

    return manager;
  }
  
  static public SectionManager urlToTerm(URL url, List<Term> lt, ZSect zs)
  {
    UrlSource source = new UrlSource(url);
    source.setMarkup(Markup.LATEX);
    source.setEncoding("Default");

    SectionManager manager = new SectionManager(Dialect.CIRCUS);
    String name = "spec";
    manager.put(new Key<Source>(name, Source.class), source);

//    Source unfoldSource = new UrlSource(RuleUtils.getUnfoldRules());
//    manager.put(new Key<Source>("unfold", Source.class), unfoldSource);
    
    Spec spec = null;
    try {
      spec = manager.get(new Key<Spec>(name, Spec.class));
      
      String sectionName = "";
      for (Sect sect : spec.getSect()) {
        // If the section is a ZSection
        if (sect instanceof ZSect) {
          ZSect zSect = (ZSect) sect;
          sectionName = zSect.getName();

          // type check it
          manager.get(new Key<SectTypeEnvAnn>(sectionName, SectTypeEnvAnn.class));

          ZParaList paralist = zSect.getZParaList();
          for (net.sourceforge.czt.z.ast.Para para : paralist) {
            lt.add(para);
          }
          
          zs.setParaList(zSect.getParaList());
          zs.setName(zSect.getName());
        }
      }
    }
    catch (SectionInfoException e) {
      CztException ex = new CztException("Section Error!", e);
      throw ex;
    }
    catch (CommandException e) {
      System.out.println("------------------------ TEST ERROR START ------------------------");
      if (e instanceof ParseException) {
        System.out.println("" + ((ParseException) e).getMessage());
//        ((ParseException)e).printErrorList();
        CztException ex = new CztException("Parse Error!", e);
        throw ex;
      }
      else {
        CztException ex = new CztException("Type Check Error!", e);
        throw ex;
      }
//      System.out.println("------------------------ TEST ERROR END --------------------------");
    }

    return manager;
  }
  
  static public SectionManager strToSecManager(String str)
  {
    StringSource source = new StringSource(str, "circusTermTest");
    source.setMarkup(Markup.LATEX);
    source.setEncoding("Default");

    SectionManager manager = new SectionManager(Dialect.CIRCUS);
    String name = "spec";
    manager.put(new Key<Source>(name, Source.class), source);

    return manager;
  }
  
  static public void WriteSpecToFiles(String filename, String zstr, String cspstr)
  {

    FileOutputStream zstream, cspstream;
    try {
      // Originally under circus2zcsp/src/test/net/sourceforge/czt/circus2zcsp/tests/
      // After test running, it will be copied to
      // circus2zcsp/targets/classes/net/sourceforge/czt/circus2zcsp/tests/
//      assertNotNull("Test file missing", getClass().getResource(TEST_DIR + "small_register.tex"));
      // get path to circus2zcsp/targets/classes/net/sourceforge/czt/circus2zcsp/tests/
      String path = TransformerTest.class.getResource(TESTOUT_DIR).getPath();

      String zfilename = path + "/" + filename + "_z.tex";
      String cspfilename = path + "/" + filename + "_csp.csp";
      zstream = new FileOutputStream(zfilename);
      cspstream = new FileOutputStream(cspfilename);
      Writer zwriter = new OutputStreamWriter(zstream);
      Writer cspwriter = new OutputStreamWriter(cspstream);
      try {
        // zwriter.write(writer.toString());
        zwriter.write(zstr);
        zwriter.close();
        cspwriter.write(cspstr);
        cspwriter.close();
      }
      catch (IOException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
    catch (FileNotFoundException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
  }
  
  public static void test_print(String str)
  {
    if (true) {
      System.out.println(str);
    }
  }
  
  public static boolean testExpansion() throws UnfoldException
  {
    String str = "\\begin{zsection} \n \\SECTION\\ ChannelDeclTestSpec \\parents\\ circus\\_toolkit \n \\end{zsection}" 
        + "\\begin{zed} \n Tsch1 ~~==~~ [~ c1,c2:\\{1,3\\}; d1,d2:1..5 ~] \n \\end{zed} \n"
        + "\\begin{zed} \n Tsch2 ~~==~~ [~ Tsch1; cc:\\{1,3\\} ~] \n \\end{zed} \n"
        + "\\begin{circus}\n" + "\\circchannelfrom\\ Tsch2 \n" + "\\end{circus}";
    
    StringSource source = new StringSource(str, "circusUnfoldTest");
    source.setMarkup(Markup.LATEX);
    source.setEncoding("Default");

    SectionManager manager = new SectionManager(Dialect.CIRCUS);
    String name = "spec";
    manager.put(new Key<Source>(name, Source.class), source);

    RuleTable rules = null;
    try {
      SectionManager managerz = new SectionManager(Dialect.ZPATT);
      rules = managerz.get(new Key<RuleTable>(Section.EXPANSION_RULES.getName(), RuleTable.class));
      RuleTable simplificationRules = managerz.get(new Key<RuleTable>(Section.SIMPLIFICATION_RULES.getName(), RuleTable.class));
      rules.addRuleParas(simplificationRules);
    }
    catch (SectionInfoException e) {
      throw new UnfoldException(e);
    }
    catch (CommandException e) {
      throw new UnfoldException(e);
    }
    catch (RuleTableException e) {
      throw new UnfoldException(e);
    }

//    Source unfoldSource = new UrlSource(RuleUtils.getUnfoldRules());
//    manager.put(new Key<Source>("unfold", Source.class), unfoldSource);
    
    Spec spec = null;
    try {
      spec = manager.get(new Key<Spec>(name, Spec.class));
      String sectionName = "";
      for (Sect sect : spec.getSect()) {
        // If the section is a ZSection
        if (sect instanceof ZSect) {
          ZSect zSect = (ZSect) sect;
          sectionName = zSect.getName();

          // type check it
          manager.get(new Key<SectTypeEnvAnn>(sectionName, SectTypeEnvAnn.class));

          ZParaList paralist = zSect.getZParaList();
          for (net.sourceforge.czt.z.ast.Para para : paralist) {
            if (para instanceof ProcessPara) {
            }
            else if (para instanceof NarrPara) {
              // skip
            }
            else if (para instanceof ChannelPara) {
              ZDeclList dl = ((ChannelPara)para).getZDeclList();
              if (dl.size() == 1) {
                Decl decl = dl.get(0);
                if (decl instanceof ChannelDecl) {
                  ChannelDecl cd = (ChannelDecl) decl;
                  /* 
                   * For schema: channelfrom, the namelist is empty
                   * It is rewritten to general channel declaration
                   */
                  if (cd.getZChannelNameList().isEmpty()) {
                    /* the expr should be RefExpr */
                    if(cd.getExpr() instanceof RefExpr) {
                      /* get the schema expr referred by this RefExpr and expand it */
                      String strExpr = cd.getExpr().toString();
                      // strExpr is the schema name

                      DefinitionTable defTable = manager.get(new Key<DefinitionTable>(sectionName, DefinitionTable.class));
                      DefinitionTable.Definition def = defTable.lookup(strExpr);
                      // Added distinction with CONSTDECL, for compatibility with old DefinitionTable (Leo)      
                      if (def == null || !def.getDefinitionType().equals(DefinitionType.CONSTDECL))
                      {
                        CztException ex =new CztException("Cannot find name: "+strExpr);
                        throw ex;
                      }
                      
                      Expr expr_sch = def.getExpr();
                      if (expr_sch == null)
                      {
                        CztException ex = new CztException("Cannot find name: "+strExpr);
                        throw ex;
                      }
                      
//                      try {
//                        Debug.debug_print("Before unfold: " + printToString(expr_sch, sectionName, manager));
//                        Term t = RewriteUtils.rewrite(expr_sch, manager, sectionName);
//                        Debug.debug_print("Before unfold: " + printToString(t, sectionName, manager));
//                      }
//                      catch (UnboundJokerException e) {
//                        // TODO Auto-generated catch block
//                        e.printStackTrace();
//                      }
                      Expr applExpr = RewriteUtils.createNormalizeAppl(expr_sch);
                      try {
                        Debug.debug_print("Before expansion: " + printToString(applExpr, sectionName, manager));
                        Term rew_term = Strategies.innermost(applExpr, rules, manager, sectionName);
                        Debug.debug_print("After expansion: " + printToString(rew_term, sectionName, manager));
                      }
                      catch (UnboundJokerException e) {
                        // TODO Auto-generated catch block
                        e.printStackTrace();
                      }
                    }
                  }
                  /* a common channel declaration, we will not change anything */
                  else {
                    
                  }
                }
              }
            }
            else if (para instanceof ChannelSetPara) {
            }
            else if (para instanceof LatexMarkupPara) {
              // skip
            }
            else if (para instanceof AxPara) // Axiom Definition
            {
              AxPara ap = (AxPara)para;
              // For Abbreviation, add it to paraList and also CSP
              if (ZUtils.isAbbreviation(para)) {
              }
              else if (ZUtils.isSimpleSchema(para)) {
                // unfold it at first
              }
            }
            else if (para instanceof FreePara) {
            }
          }
        }
      }
    }
    catch (SectionInfoException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    catch (CommandException e) {
      // TODO Auto-generated catch block
      System.out.println("------------------------ TEST ERROR START ------------------------");
      if (e instanceof ParseException) {
        System.out.println("" + ((ParseException) e).getMessage());
//        ((ParseException)e).printErrorList();
      }
      else {
        e.printStackTrace();
      }
      System.out.println("------------------------ TEST ERROR END --------------------------");
    }

    return true;
  }
  
  public static Term unfold(SectionManager manager, String sectname, Term term)
  {
    SectionManager rmanager = new SectionManager(Dialect.ZPATT);
    rmanager.putCommands(Dialect.ZPATT);
    RuleTable rules;
    try {
      URL url = RuleUtils.getUnfoldRules();
      if (url == null) {
        throw new IOException("Cannot get unfold rules");
      }

      rmanager.put(new Key<Source>(url.toString(), Source.class), new UrlSource(url));
      
      //load the rules
      Term t = rmanager.get(new Key<Spec>(url.toString(), Spec.class));
      String sectName = t.accept(new GetZSectNameVisitor());
//      rmanager.get(new Key<SectTypeEnvAnn>(sectName, SectTypeEnvAnn.class)); 
      rules = rmanager.get(new Key<RuleTable>(sectName, RuleTable.class));
    }
    catch (Throwable e) {
      throw new CztException("\nUnexpected exception loading unfold rules\n" +
           "\n\tException: " + e.toString());
    }
    
    Term rewTerm = null;
    rewTerm = Rewrite.rewrite(manager, sectname, term, rules);
    
    return rewTerm;
  }
  
  protected static String printToString(Term term, String section, SectionManager manager) throws PrintException
  {
    StringWriter writer = new StringWriter();
    PrintUtils.print(term, writer, manager, section, Markup.LATEX);
    return writer.toString();
//    System.out.println(writer.toString());
  }
  
  /*
   * Statistics of a Z Section
   */
  public static void Stat_ZSection(ZSect zs, ZStat zst, SectionManager manager)
  {
    for(Para para: zs.getZParaList()) {
      zst.nr_of_paras_++;
      
      if (para instanceof ProcessPara) {
        zst.nr_of_processes_++;
        zst.lst_processes_.add(Circus2ZCSPUtils.termToString(((ProcessPara)para).getZName()));
        
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {          
          IdenVisitor idv = new IdenVisitor();
          para.accept(idv);
          zst.map_set_id_.put(Circus2ZCSPUtils.termToString(((ProcessPara)para).getZName()),
              idv.getIdSet());
          
          CommsVisitor cv = new CommsVisitor();
          para.accept(cv);
          zst.map_set_comms_.put(Circus2ZCSPUtils.termToString(((ProcessPara)para).getZName()), 
              cv.getCommsSet());
          
          ParaVisitor pv = new ParaVisitor();
          para.accept(pv);
          zst.map_set_schemas_.put(Circus2ZCSPUtils.termToString(((ProcessPara)para).getZName()), 
              pv.getSchemasSet());
          zst.map_set_actions_.put(Circus2ZCSPUtils.termToString(((ProcessPara)para).getZName()), 
              pv.getActionsSet());
        }
      }
      else if (para instanceof NarrPara) {
        // skip
      }
      else if (para instanceof GivenPara) {
      }
      else if (para instanceof ChannelPara) {
        ChannelPara cp = (ChannelPara) para;
      }
      else if (para instanceof ChannelSetPara) {
      }
      else if (para instanceof LatexMarkupPara) {
        // skip
      }
      else if (para instanceof AxPara) // Axiom Definition
      {
      }
      else if (para instanceof FreePara) {
      }
    }
    
//    try {
//      zst.str_spec_ = printToString(zs, zs.getName(), manager);
//    }
//    catch (PrintException e) {
//      // throw new CztException("Unable to print the section " + zs.getName() + " to String!");
//    }
    
    return;
  }
  
}

/**
 * IdenVisitor: the visitor to get a set of identifiers (ZName or NumExpr) in the term
 * @author rye
 *
 */
class IdenVisitor
implements
  TermVisitor<Object>,
  ZNameVisitor<Object>,
  NumExprVisitor<Object>
{
  private Set<String> set_id_ = new HashSet<String>();
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
  public Object visitZName(ZName term)
  {
    set_id_.add(Circus2ZCSPUtils.termToString(term));
    return null;
  }

  public Set<String> getIdSet()
  {
    return set_id_;
  }

  @Override
  public Object visitNumExpr(NumExpr term)
  {
    set_id_.add(Circus2ZCSPUtils.termToString(term));
    return null;
  }
}

/**
 * IdenVisitor: the visitor to get a set of identifiers (ZName or NumExpr) in the term
 * @author rye
 *
 */
class ParaVisitor
implements
  TermVisitor<Object>,
  BasicProcessVisitor<Object>
{
  private Set<String> set_schemas_ = new HashSet<String>();
  private Set<String> set_actions_ = new HashSet<String>();
  
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

  public Set<String> getSchemasSet()
  {
    return set_schemas_;
  }
  
  public Set<String> getActionsSet()
  {
    return set_actions_;
  }

  @Override
  public Object visitBasicProcess(BasicProcess term)
  {
    for(Para p: term.getZParaList()) {
      if(p instanceof AxPara) {
        Name pname = null;
        // P == P1 \land P2
        if(ZUtils.isAbbreviation(p)) {
          pname = ZUtils.getAbbreviationName(p);
        }
        // is simple schema
        // horizontal or boxed schema
        else if(ZUtils.isSimpleSchema(p)) {
          pname = ZUtils.getSchemaName(p);
        }
        
        set_schemas_.add(Circus2ZCSPUtils.termToString(pname));
      }
      else if(p instanceof ActionPara) {
        set_actions_.add(Circus2ZCSPUtils.termToString(((ActionPara)p).getZName()));
      }
    }
    return null;
  }
}

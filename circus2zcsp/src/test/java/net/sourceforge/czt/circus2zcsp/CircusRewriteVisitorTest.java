package net.sourceforge.czt.circus2zcsp;

import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Test;

import junit.framework.TestCase;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.BasicChannelSetExpr;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.ChannelDecl;
import net.sourceforge.czt.circus.ast.ChannelPara;
import net.sourceforge.czt.circus.ast.ChannelSetPara;
import net.sourceforge.czt.circus.ast.CircusChannelSet;
import net.sourceforge.czt.circus.ast.Communication;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus2zcsp.data.CircusSpecMap;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.circus2zcsp.util.TestUtils;
import net.sourceforge.czt.circus2zcsp.util.ZStat;
import net.sourceforge.czt.circus2zcsp.visitor.CircusRewriteVisitor;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfoException;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.ZSect;

public class CircusRewriteVisitorTest  extends TestCase
{

  private ZFactory zfac_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();

  private CircusRewriteVisitor crtv_ = new CircusRewriteVisitor();
  
  private CircusSpecMap map_ = null;
  
//  @Rule
//  public ExpectedException thrown = ExpectedException.none();
  
  public CircusRewriteVisitorTest()
  {
    // set up our debug log.
//    Handler handler;
//    try {
//      handler = new FileHandler("circus2zcsp_test.log");
//      handler.setLevel(Level.ALL);
//      handler.setEncoding("utf8");
//      Logger.getLogger("").addHandler(handler);
//      Logger circus2zcspLogger = Logger.getLogger("net.sourceforge.czt.circus2zcsp");
//      circus2zcspLogger.setLevel(Level.FINEST);
////      
////      for (Handler h : Logger.getLogger("").getHandlers()) {
////        h.setLevel(Level.FINEST);
////      }
//    }
//    catch (SecurityException e) {
//      // TODO Auto-generated catch block
//      e.printStackTrace();
//    }
//    catch (IOException e) {
//      // TODO Auto-generated catch block
//      e.printStackTrace();
//    }
//    System.out.println("JUnit version is: " + Version.id());
  }
  
  /**
   * Test parametrised process with only \Skip action and no state
   */
  @Test
  public void testAssign()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/Cell.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
  }
  
  /**
   * Test parametrised process with only \Skip action and no state
   * multiple parameters
   */
  @Test
  public void testParametrisedProcess0()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/param_process_0.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    ZStat zst = new ZStat();    
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 144);
    assertTrue(zst.lst_processes_.contains("P0_2_1_3_3_GSET_2"));
//    Set<String> set_id = zst.map_set_id_.get("P0_2_1_3_3_GSET_2");
//    assertTrue(set_id.contains(""));
  }
  
  /**
   * Test parametrised process with only \Skip action and no state
   * one parameter
   */
  @Test
  public void testParametrisedProcess00()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/param_process_00.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 2);
    assertTrue(zst.lst_processes_.contains("P0_1"));
    assertTrue(zst.lst_processes_.contains("P0_2"));
  }
  
  /**
   * Test parametrised process with one parameter and renaming
   */
  @Test
  public void testParametrisedProcess1()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/param_process_1.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 2);
    assertTrue(zst.lst_processes_.contains("P1_1"));
    assertTrue(zst.lst_processes_.contains("P1_2"));
    
    Set<String> set_id = zst.map_set_id_.get("P1_1");
    assertTrue(set_id.contains("1"));
    assertFalse(set_id.contains("v"));
    
    set_id = zst.map_set_id_.get("P1_2");
    assertTrue(set_id.contains("2"));
    assertFalse(set_id.contains("v"));
  }
  
  /**
   * Test parametrised process with one parameter and the process is a reference to a basic process
   */
  @Test
  public void testParametrisedProcess2()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/param_process_2.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 3);
    assertTrue(zst.lst_processes_.contains("P"));
    assertTrue(zst.lst_processes_.contains("P1_1"));
    assertTrue(zst.lst_processes_.contains("P1_2"));
  }
  
  /**
   * Test parametrised process invocation (1 parameter)
   */
  @Test
  public void testParametrisedProcessInvoc0()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/param_process_invoc_0.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 6);
    assertTrue(zst.lst_processes_.contains("P"));
    assertTrue(zst.lst_processes_.contains("PP_1"));
    assertTrue(zst.lst_processes_.contains("PP_2"));
    assertTrue(zst.lst_processes_.contains("PP_3"));
    assertTrue(zst.lst_processes_.contains("P1"));
    assertTrue(zst.lst_processes_.contains("P2"));
  }
  
  /**
   * Test parametrised process invocation (multiple parameters)
   */
  @Test
  public void testParametrisedProcessInvoc1()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/param_process_invoc_1.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 7);
    assertTrue(zst.lst_processes_.contains("P1"));
    assertTrue(zst.lst_processes_.contains("PP_1_1"));
    assertTrue(zst.lst_processes_.contains("PP_1_2"));
    assertTrue(zst.lst_processes_.contains("PP_2_1"));
    assertTrue(zst.lst_processes_.contains("PP_2_2"));
    assertTrue(zst.lst_processes_.contains("PP_3_1"));
    assertTrue(zst.lst_processes_.contains("PP_3_2"));
    
    Set<String> set_id = zst.map_set_id_.get("PP_1_1");
    assertTrue(set_id.contains("1"));
    assertFalse(set_id.contains("v"));
    assertFalse(set_id.contains("w"));
    
    set_id = zst.map_set_id_.get("PP_3_1");
    assertTrue(set_id.contains("3"));
    assertTrue(set_id.contains("1"));
    assertFalse(set_id.contains("v"));
    assertFalse(set_id.contains("w"));
  }
  
  /**
   * Test parametrised process invocation (anonymous parametrised process invocation)
   */
  @Test
  public void testParametrisedProcessInvoc2()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/param_process_invoc_2.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 10);
    assertTrue(zst.lst_processes_.contains("P1"));
    assertTrue(zst.lst_processes_.contains("$$implicitProc0_L6C55_1_1"));
    assertTrue(zst.lst_processes_.contains("$$implicitProc0_L6C55_2_1"));
    assertTrue(zst.lst_processes_.contains("$$implicitProc0_L6C55_3_1"));
    assertTrue(zst.lst_processes_.contains("$$implicitProc0_L6C55_1_2"));
    assertTrue(zst.lst_processes_.contains("$$implicitProc0_L6C55_2_2"));
    assertTrue(zst.lst_processes_.contains("$$implicitProc0_L6C55_3_2"));
    assertTrue(zst.lst_processes_.contains("$$implicitProc0_L13C17_1"));
    assertTrue(zst.lst_processes_.contains("$$implicitProc0_L13C17_2"));
    assertTrue(zst.lst_processes_.contains("$$implicitProc0_L13C17_3"));
  }
  
  /**
   * Test indexed process with only \Skip action and no state
   * one parameter
   */
  @Test
  public void testIndexedProcess0()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/indexed_process_0.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 2);
    assertTrue(zst.lst_processes_.contains("IP_1"));
    assertTrue(zst.lst_processes_.contains("IP_2"));
  }
  
  /**
   * Test indexed process with only c -> \Skip action and no state
   * one parameter
   */
  @Test
  public void testIndexedProcess1()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/indexed_process_1.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 2);
    assertTrue(zst.lst_processes_.contains("IP_1"));
    assertTrue(zst.lst_processes_.contains("IP_2"));
    
    Set<String> set_id = zst.map_set_id_.get("IP_1");
    assertTrue(set_id.contains("1"));
    assertTrue(set_id.contains("c_v"));
    assertFalse(set_id.contains("c"));
    
    set_id = zst.map_set_id_.get("IP_2");
    assertTrue(set_id.contains("2"));
    assertTrue(set_id.contains("c_v"));
    assertFalse(set_id.contains("c"));
  }
  
  
  /**
   * Test indexed process with state and normal actions, one parameter
   */
  @Test
  public void testIndexedProcess2()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/indexed_process_2.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 2);
    assertTrue(zst.lst_processes_.contains("IP_1"));
    assertTrue(zst.lst_processes_.contains("IP_2"));
 }
  
  /**
   * Test indexed process with state, a reference to a process
   */
  @Test
  public void testIndexedProcess3()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/indexed_process_3.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 3);
    assertTrue(zst.lst_processes_.contains("P"));
    assertTrue(zst.lst_processes_.contains("IP_1"));
    assertTrue(zst.lst_processes_.contains("IP_2"));
  }
  
  /**
   * Test indexed process invocation
   */
  @Test
  public void testIndexedProcessInvoc0()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/indexed_process_invoc_0.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 5);
    assertTrue(zst.lst_processes_.contains("P1"));
    assertTrue(zst.lst_processes_.contains("IP_1"));
    assertTrue(zst.lst_processes_.contains("IP_2"));
    assertTrue(zst.lst_processes_.contains("IP_3"));
    assertTrue(zst.lst_processes_.contains("P2"));
  }
  
  /**
   * Test indexed process invocation
   */
  @Test
  public void testIndexedProcessInvoc1()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/indexed_process_invoc_1.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 4);
    assertTrue(zst.lst_processes_.contains("P"));
    assertTrue(zst.lst_processes_.contains("$$implicitProc0_L20C41_1"));
    assertTrue(zst.lst_processes_.contains("$$implicitProc0_L20C41_2"));
    assertTrue(zst.lst_processes_.contains("$$implicitProc0_L20C41_3"));
  }
  
  /**
   * Test process renaming operator
   *    P[c:=d] where P is EDP
   */
  @Test
  public void testRenamingProcess0()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/rename_process_0.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 2);
    assertTrue(zst.lst_processes_.contains("P"));
    assertTrue(zst.lst_processes_.contains("RP"));
    
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("c"));
    assertTrue(set_id.contains("d"));
    assertFalse(set_id.contains("cc"));
    assertFalse(set_id.contains("dd"));
    
    set_id = zst.map_set_id_.get("RP");
    assertTrue(set_id.contains("cc"));
    assertTrue(set_id.contains("dd"));
    assertFalse(set_id.contains("c"));
    assertFalse(set_id.contains("d"));
  }
  
  /**
   * Test process renaming operator (should have type check error)
   *    IP[c:=d] where IP is a reference to Indexed Process
   */
  @Test
  public void testRenamingProcess1()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/rename_process_1.tex");
    assertFalse(url == null);
    
    try{
      SectionManager manager = TestUtils.urlToTerm(url, lt, zs);  
      crtv_.setManager(manager);
      zs.accept(crtv_);
    }
    catch(CztException e) {
      String str = e.getMessage();
      assertTrue("A CztException is thrown but detailed message \"" + str +"\" is not expected", 
         str.matches("Type Check Error!"));
    }
    
//    ZStat zst = new ZStat();
//    TestUtils.Stat_ZSection(zs, zst, manager);
//    
//    assertTrue(zst.nr_of_processes_ == 3);
//    assertTrue(zst.lst_processes_.contains("P"));
//    assertTrue(zst.lst_processes_.contains("IP_1"));
//    assertTrue(zst.lst_processes_.contains("IP_2"));
  }
  
  /**
   * Test process renaming operator
   *    (x:T \circindex P)[c:=d] where P is a reference to EDP
   */
  @Test
  public void testRenamingProcess2()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/rename_process_2.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 3);
    assertTrue(zst.lst_processes_.contains("P"));
    assertTrue(zst.lst_processes_.contains("RIP_1"));
    assertTrue(zst.lst_processes_.contains("RIP_2"));
  }
  
  /**
   * Test process renaming operator (should not have type check error)
   */
  @Test
  public void testRenamingProcess3()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/rename_process_3.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    try{
      zs.accept(crtv_);
    }
    catch(CztException e) {
      String str = e.getMessage();
      assertTrue("A CztException is thrown but detailed message \"" + str +"\" is not expected", 
         str.matches("Invalid Class.*for Renamed process.*"));
    }
    
//    ZStat zst = new ZStat();
//    TestUtils.Stat_ZSection(zs, zst, manager);
//    
//    assertTrue(zst.nr_of_processes_ == 3);
//    assertTrue(zst.lst_processes_.contains("P"));
//    assertTrue(zst.lst_processes_.contains("IP_1"));
//    assertTrue(zst.lst_processes_.contains("IP_2"));
  }
  
  /**
   * Test Channel Definition
   */
  @Test
  public void testChannelDecl()
  {
    boolean checked = false;
    
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    SectionManager manager = TestUtils.strToTerm(
        "\\begin{zsection} \n \\SECTION\\ ChannelDeclTestSpec \\parents\\ circus\\_toolkit \n \\end{zsection}" 
      + "\\begin{zed} \n Tsch1 ~~==~~ [~ c1,c2:\\{1,3\\}; d1,d2:1..5 ~] \n \\end{zed} \n"
      + "\\begin{zed} \n Tsch2 ~~==~~ [~ cc:\\{1,3\\} ~] \n \\end{zed} \n"
      + "\\begin{circus}\n" + "\\circchannelfrom\\ Tsch1 \n" + "\\end{circus}"
      , lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        if (term instanceof AxPara) {
          // TODO: should we remove the schema?
        }
        else if(term instanceof ChannelPara) {
          checked = true;
          // expanded to 4 channel declarations
          assertEquals(((ChannelPara)term).getZDeclList().size(), 2);
          Set<String> expected_set = new HashSet<String>();
          expected_set.add("c1");
          expected_set.add("c2");
          expected_set.add("d1");
          expected_set.add("d2");
          
          Set<String> real_set = new HashSet<String>();
          for(Decl decl: ((ChannelPara)term).getZDeclList()) {
            assertTrue(decl instanceof ChannelDecl);
            for(Name n: ((ChannelDecl)decl).getZChannelNameList()) {
              real_set.add(n.accept(new net.sourceforge.czt.z.util.PrintVisitor()));
            }
          }
          
          assertEquals(expected_set, real_set);
        }
      }
    }
    
    if (checked == false)
    {
      fail("No assert checked!");
    }
  }
  
  /**
   * Test Channel Definition
   */
  @Test
  public void testChannelDecl_schama_ref()
  {
    boolean checked = false;
    
    ZSect zs = zfac_.createZSect();
    String str = "\\begin{zsection} \n \\SECTION\\ ChannelDeclTestSpec \\parents\\ circus\\_toolkit \n \\end{zsection}" 
        + "\\begin{zed} \n Tsch1 ~~==~~ [~ c1,c2:\\{1,3\\}; d1,d2:1..5 ~] \n \\end{zed} \n"
        + "\\begin{zed} \n Tsch2 ~~==~~ [~ Tsch1; cc:\\{1,3\\} ~] \n \\end{zed} \n"
        + "\\begin{circus}\n" + "\\circchannelfrom\\ Tsch2 \n" + "\\end{circus}";

    List<Term> lt = new ArrayList<Term>();

    SectionManager manager = TestUtils.strToTerm(str, lt, zs);

    crtv_.setManager(manager);
    
    Spec spec;
    try {
      spec = manager.get(new Key<Spec>("spec", Spec.class));
      zs = (ZSect)spec.getSect().get(0);
      crtv_.setManager(manager);
      zs.accept(crtv_);
    }
    catch (SectionInfoException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    catch (CommandException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } 
    catch (CztException e) {
      String s = e.getMessage();
      assertTrue("A CztException is thrown but detailed message \"" + s +"\" is not expected", 
         s.matches(".*schema.*VarDecl but it is.*"));
    }
  }
  
  @Test
  public void testUnfold() // throws UnfoldException, SectionInfoException, CommandException, UnboundJokerException
  {
    List<Term> lt = new ArrayList<Term>();
    ZSect zs = zfac_.createZSect();
    
    String str = "\\begin{zsection} \n \\SECTION\\ ChannelDeclTestSpec \\parents\\ circus\\_toolkit \n \\end{zsection}" 
        + "\\begin{zed} \n Tsch1 ~~==~~ [~ c1,c2:\\{1,3\\}; d1,d2:1..5 ~] \n \\end{zed} \n"
        + "\\begin{zed} \n Tsch2 ~~==~~ [~ Tsch1; cc:\\{1,3\\} ~] \n \\end{zed} \n"
        + "\\begin{circus}\n" + "\\circchannelfrom\\ Tsch2 \n" + "\\end{circus}";
    
    SectionManager manager = TestUtils.strToTerm(str, lt, zs);
    
    Term t = TestUtils.unfold(manager, zs.getName(), zs);
  }
  
  /**
   * Test Channel Set (empty)
   */
  @Test
  public void testChannelSet1()
  {
    boolean checked = false;
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    SectionManager manager = TestUtils.strToTerm(
        "\\begin{circus}\n" + "\\circchannelset\\ C == \\emptyset \n" + "\\end{circus}"
        , lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        if(term instanceof ChannelSetPara) {
          checked = true;
          assertTrue(((ChannelSetPara)term).getZName().accept(new net.sourceforge.czt.z.util.PrintVisitor()).equals("C"));
          assertTrue(((ChannelSetPara)term).getChannelSet() instanceof CircusChannelSet);
          CircusChannelSet ccs = (CircusChannelSet)((ChannelSetPara)term).getChannelSet();
          assertTrue(ccs.getExpr() instanceof BasicChannelSetExpr);
          BasicChannelSetExpr bcse = (BasicChannelSetExpr)(ccs.getExpr());
          assertTrue(bcse.getCircusCommunicationList().isEmpty());
        }
      }
    }
    
    if (checked == false)
    {
      fail("No assert checked!");
    }
  }
  
  /**
   * Test Channel Set (empty)
   */
  @Test
  public void testChannelSet2()
  {
    boolean checked = false;
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    SectionManager manager = TestUtils.strToTerm(
        "\\begin{circus}\n" + "\\circchannelset\\ C == \\lchanset \\rchanset \n" + "\\end{circus}"
        , lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        if(term instanceof ChannelSetPara) {
          checked = true;
          assertTrue(((ChannelSetPara)term).getZName().accept(new net.sourceforge.czt.z.util.PrintVisitor()).equals("C"));
          assertTrue(((ChannelSetPara)term).getChannelSet() instanceof CircusChannelSet);
          CircusChannelSet ccs = (CircusChannelSet)((ChannelSetPara)term).getChannelSet();
          assertTrue(ccs.getExpr() instanceof BasicChannelSetExpr);
          BasicChannelSetExpr bcse = (BasicChannelSetExpr)(ccs.getExpr());
          assertTrue(bcse.getCircusCommunicationList().isEmpty());
        }
      }
    }
    
    if (checked == false)
    {
      fail("No assert checked!");
    }
  }
  
  /**
   * Test Channel Set (empty)
   */
  @Test
  public void testChannelSet3()
  {
    boolean checked = false;
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    SectionManager manager = TestUtils.strToTerm(
        "\\begin{circus}\n" 
        + "\\circchannel\\ c,d,e \\\\\n"
        + "\\circchannelset\\ C == \\lchanset c \\rchanset \n" 
        + "\\end{circus}"
        , lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        if(term instanceof ChannelSetPara) {
          checked = true;
          assertTrue(((ChannelSetPara)term).getZName().accept(new net.sourceforge.czt.z.util.PrintVisitor()).equals("C"));
          assertTrue(((ChannelSetPara)term).getChannelSet() instanceof CircusChannelSet);
          CircusChannelSet ccs = (CircusChannelSet)((ChannelSetPara)term).getChannelSet();
          assertTrue(ccs.getExpr() instanceof BasicChannelSetExpr);
          BasicChannelSetExpr bcse = (BasicChannelSetExpr)(ccs.getExpr());
          assertTrue(bcse.getCircusCommunicationList().size() == 1);
          Communication c = bcse.getCircusCommunicationList().get(0);
          assertTrue(c.getChannelExpr().getZName().accept(new net.sourceforge.czt.z.util.PrintVisitor()).equals("c"));
          assertTrue(c.getCircusFieldList().isEmpty());
        }
      }
    }
    
    if (checked == false)
    {
      fail("No assert checked!");
    }
  }
  
  /**
   * Test Channel Set (empty)
   */
  @Test
  public void testChannelSet4()
  {
    boolean checked = false;
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    SectionManager manager = TestUtils.strToTerm(
        "\\begin{circus}\n" 
            + "\\circchannel\\ c,d,e \\\\\n"
            + "\\circchannelset\\ C == \\lchanset c, d, e \\rchanset \n" 
            + "\\end{circus}"
        , lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        if(term instanceof ChannelSetPara) {
          checked = true;
          assertTrue(((ChannelSetPara)term).getZName().accept(new net.sourceforge.czt.z.util.PrintVisitor()).equals("C"));
          assertTrue(((ChannelSetPara)term).getChannelSet() instanceof CircusChannelSet);
          CircusChannelSet ccs = (CircusChannelSet)((ChannelSetPara)term).getChannelSet();
          assertTrue(ccs.getExpr() instanceof BasicChannelSetExpr);
          BasicChannelSetExpr bcse = (BasicChannelSetExpr)(ccs.getExpr());
          assertTrue(bcse.getCircusCommunicationList().size() == 3);
          
          Set<String> rel_set = new HashSet<String>();
          
          for(Communication c: bcse.getCircusCommunicationList()) {
            rel_set.add(c.getChannelExpr().getZName().accept(new net.sourceforge.czt.z.util.PrintVisitor()));
            assertTrue(c.getCircusFieldList().isEmpty());
          }
          
          assertEquals(rel_set, new HashSet<String>(Arrays.asList("c", "d", "e")));
        }
      }
    }
    
    if (checked == false)
    {
      fail("No assert checked!");
    }
  }
  
  /**
   * Test Channel Set (empty)
   */
  @Test
  public void testChannelSet5()
  {
    boolean checked = false;
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    try{
    SectionManager manager = TestUtils.strToTerm(
        "\\begin{circus}\n" 
        + "\\circchannel\\ c,d,e \n"
        + "\\circchannelset\\ C == \\lchanset c \\rchanset \n" 
        + "\\circchannelset\\ D == \\lchanset d,e \\rchanset \n"
        + "\\circchannelset\\ E == C \n" // that's not valid according to syntax in Parser.xml
//        + "\\circchannelset\\ E == (C \\cup D) \n"
        + "\\end{circus}"
        , lt, zs);
    }
    catch(CztException e) {
      String s = e.getMessage();
      assertTrue("A CztException is thrown but detailed message \"" + s +"\" is not expected", 
         s.matches("Parse Error!"));
    }

//    crtv_.setManager(manager);
//    
//    zs.accept(crtv_);
//    for (Term term : lt) {
//      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
//        if(term instanceof ChannelPara) {
//        }
//      }
//    }
//    
//    if (checked == false)
//    {
//      fail("No assert checked!");
//    }
//    
//    fail("Channel Set reference and operators are not supported yet!");
  }
  
  /**
   * Test Name Set Declaration
   */
  @Test
  public void testNameSetDecl()
  {
    boolean checked = false;
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    SectionManager manager = TestUtils.strToTerm(
        "\\begin{circus}\n"
            + "\\circchannel\\ c, d: \\nat \\\\ \n"
            + "\\circchannelset\\ CS == \\lchanset c, d \\rchanset \n"
            + "\\end{circus}\n"
            + "\\begin{circus}\n" 
            + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
            + "     \\t1 \\circstate St == [ a: \\nat; b: \\nat] \\\\\n"
            + "     \\t1 A \\circdef c.a \\then \\Skip\\\\\n"
            + "     \\t1 B \\circdef d.b \\then \\Skip\\\\\n"
            + "     \\t1 \\circnameset NS == \\{ a, b \\} \\\\\n"
            + "     \\t1 \\circspot A \\lpar NS | CS | \\{ \\} \\rpar B \\circend\n"
            + "\\end{circus}"
        , lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    fail("Not implemented yet!");
    
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        if(term instanceof ChannelPara) {
        }
      }
    }
    
    if (checked == false)
    {
      fail("No assert checked!");
    }
  }
  
  /**
   * Test compound process with 
   * 
   */
  @Test
  public void testCompoundProc0()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/compound_process_0.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    
    zs.accept(crtv_);
    
    ZStat zst = new ZStat();    
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 4);
    assertTrue(zst.lst_processes_.contains("P"));
    assertTrue(zst.lst_processes_.contains("Q"));
    assertTrue(zst.lst_processes_.contains("CMP0"));
    assertTrue(zst.lst_processes_.contains("CMP1"));
  }
  
  /**
   * Test rewrite of "Additional State Components Retrieve Schemas" in EDP
   * 
   */
  @Test
  public void testStateRetrieveSchema_EDP0()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/explicitly_defined_process_0.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);    
    zs.accept(crtv_);
    
    CircusRewriteVisitor crtv = crtv_; // new CircusRewriteVisitor();
    crtv.setManager(manager);
    crtv.setRewriteStage(2);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    ZStat zst = new ZStat();    
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 1);
    assertTrue(zst.lst_processes_.contains("P"));
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("x!"));
    assertTrue(set_id.contains("y!"));
    assertTrue(set_id.contains("z!"));
  }
  
  /**
   * Test rewrite of "Additional State Components Retrieve Schemas" in EDP with boxed schema
   * 
   */
  @Test
  public void testStateRetrieveSchema_EDP00()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/explicitly_defined_process_00.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    zs.accept(crtv_);
    
    CircusRewriteVisitor crtv = crtv_; // new CircusRewriteVisitor();
    crtv.setManager(manager);
    crtv.setRewriteStage(2);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    ZStat zst = new ZStat();    
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 1);
    assertTrue(zst.lst_processes_.contains("P"));
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("x!"));
    assertTrue(set_id.contains("y!"));
    assertTrue(set_id.contains("z!"));
  }
  
  /**
   * Test rewrite of "Additional State Components Retrieve Schemas" in EDP
   * 
   */
  @Test
  public void testStateRetrieveSchema_EDP1()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/explicitly_defined_process_1.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);    
    zs.accept(crtv_);
    
    CircusRewriteVisitor crtv = crtv_; // new CircusRewriteVisitor();
    crtv.setManager(manager);
    crtv.setRewriteStage(2);
    crtv.setSectName(zs.getName());
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 1);
    assertTrue(zst.lst_processes_.contains("P"));
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("OP_x"));
    assertTrue(set_id.contains("OP_y"));
    assertTrue(set_id.contains("OP_z"));
  }
  
  /**
   * Test rewrite of "Additional State Components Retrieve Schemas" in EDP
   * 
   */
  @Test
  public void testStateRetrieveSchema_EDP2()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/explicitly_defined_process_2.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    zs.accept(crtv_);
    
    CircusRewriteVisitor crtv = crtv_; // new CircusRewriteVisitor();
    crtv.setManager(manager);
    crtv.setRewriteStage(2);
    crtv.setSectName(zs.getName());
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 1);
    assertTrue(zst.lst_processes_.contains("P"));
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("OP_x"));
    assertTrue(set_id.contains("OP_y"));
    assertTrue(set_id.contains("OP_z"));
  }
  
  /**
   * Test rewrite of "renaming" in EDP
   * 
   */
  @Test
  public void testRenaming_EDP0()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/explicitly_defined_process_2.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);    
    zs.accept(crtv_);
    
    CircusRewriteVisitor crtv = crtv_; // new CircusRewriteVisitor();
    crtv.setManager(manager);
    crtv.setRewriteStage(2);
    crtv.setSectName(zs.getName());
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(3);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 1);
    assertTrue(zst.lst_processes_.contains("P"));
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("P_OP_x"));
    assertTrue(set_id.contains("P_OP_y"));
    assertTrue(set_id.contains("P_OP_z"));
    assertTrue(set_id.contains("P_x"));
    assertTrue(set_id.contains("P_x′"));
    assertTrue(set_id.contains("x?"));
    assertTrue(set_id.contains("x!"));
    assertFalse(set_id.contains("P_x!"));
    assertFalse(set_id.contains("P_x?"));
  }
  
  /**
   * Test rewrite of action in EDP
   *    Sequence, external choice, prefixing, recursion, schema expression
   * 
   */
  @Test
  public void testActionRewrite_EDP0()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/action_rewrite_0.tex");
    assertFalse(url == null);
    
    // parse the specification
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    // 1. rewrite processes
    zs.accept(crtv_);
    
    // 2. Additional State Components Retrieve Schemas 
    CircusRewriteVisitor crtv = crtv_;// new CircusRewriteVisitor();
    crtv.setManager(manager);
    crtv.setRewriteStage(2);
    crtv.setSectName(zs.getName());
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    // 3. Renaming
    crtv.setRewriteStage(3);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    // 4. Action rewrite
    crtv.setRewriteStage(4);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 1);
    assertTrue(zst.lst_processes_.contains("P"));
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("P_OP_x"));
    assertTrue(set_id.contains("P_OP_y"));
    assertTrue(set_id.contains("P_OP_z"));
    assertTrue(set_id.contains("P_x"));
    assertTrue(set_id.contains("P_x′"));
    assertTrue(set_id.contains("x?"));
    assertTrue(set_id.contains("x!"));
    assertFalse(set_id.contains("P_x!"));
    assertFalse(set_id.contains("P_x?"));
    
    Set<String> set_comms = zst.map_set_comms_.get("P");
    assertTrue(set_comms.contains("P_OP_x?x"));
    assertTrue(set_comms.contains("P_OP_y?y"));
    assertTrue(set_comms.contains("P_OP_z?z"));
  }
  
  /**
   * Test rewrite of action in EDP
   *    Sequence, external choice, prefixing, recursion, schema expression
   *    + guarded command
   */
  @Test
  public void testActionRewrite_EDP1()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/action_rewrite_1.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    zs.accept(crtv_);
    
    CircusRewriteVisitor crtv = crtv_; // new CircusRewriteVisitor();
    crtv.setManager(manager);
    crtv.setRewriteStage(2);
    crtv.setSectName(zs.getName());
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(3);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(4);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 1);
    assertTrue(zst.lst_processes_.contains("P"));
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("P_OP_x"));
    assertTrue(set_id.contains("P_OP_y"));
    assertTrue(set_id.contains("P_OP_z"));
    assertTrue(set_id.contains("P_x"));
    assertTrue(set_id.contains("P_x′"));
    assertTrue(set_id.contains("x?"));
    assertTrue(set_id.contains("x!"));
    assertFalse(set_id.contains("P_x!"));
    assertFalse(set_id.contains("P_x?"));
    
    Set<String> set_comms = zst.map_set_comms_.get("P");
    assertTrue(set_comms.contains("P_OP_x?x"));
    assertTrue(set_comms.contains("P_OP_y?y"));
    assertTrue(set_comms.contains("P_OP_z?z"));
  }
  
  /**
   * Test rewrite of action in EDP
   *    Sequence, external choice, prefixing, recursion, schema expression
   *    + guarded command
   */
  @Test
  public void testActionRewrite_EDP2()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/action_rewrite_2.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    zs.accept(crtv_);
    
    CircusRewriteVisitor crtv = crtv_; // new CircusRewriteVisitor();
    crtv.setManager(manager);
    crtv.setRewriteStage(2);
    crtv.setSectName(zs.getName());
    crtv.setCircusSpecMap(crtv_.getCircusSpecMap());
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(3);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(4);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 1);
    assertTrue(zst.lst_processes_.contains("P"));
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("P_OP_x"));
    assertTrue(set_id.contains("P_OP_y"));
    assertTrue(set_id.contains("P_OP_z"));
    assertTrue(set_id.contains("P_x"));
    assertTrue(set_id.contains("P_x′"));
    assertTrue(set_id.contains("x?"));
    assertTrue(set_id.contains("x!"));
    assertFalse(set_id.contains("P_x!"));
    assertFalse(set_id.contains("P_x?"));
    
    Set<String> set_comms = zst.map_set_comms_.get("P");
    assertTrue(set_comms.contains("P_OP_x?x"));
    assertTrue(set_comms.contains("P_OP_y?y"));
    assertTrue(set_comms.contains("P_OP_z?z"));
  }
  
  /**
   * Test rewrite of action in EDP
   *    Sequence, prefixing, recursion, schema expression
   *    + variable block + assignment
   */
  @Test
  public void testActionRewrite_EDP3()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/action_rewrite_3.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    zs.accept(crtv_);
    
    CircusRewriteVisitor crtv = crtv_; // new CircusRewriteVisitor();
    crtv.setManager(manager);
    crtv.setRewriteStage(2);
    crtv.setSectName(zs.getName());
    crtv.setCircusSpecMap(crtv_.getCircusSpecMap());
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(3);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(4);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 1);
    assertTrue(zst.lst_processes_.contains("P"));
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("P_OP_x"));
    assertTrue(set_id.contains("P_OP_y"));
    assertTrue(set_id.contains("P_OP_z"));
    assertTrue(set_id.contains("P_x"));
    assertTrue(set_id.contains("P_x′"));
    assertTrue(set_id.contains("x?"));
    assertTrue(set_id.contains("x!"));
    assertTrue(set_id.contains("P_AssgnOp0"));
    assertFalse(set_id.contains("P_x!"));
    assertFalse(set_id.contains("P_x?"));
    
//    Set<String> set_comms = zst.map_set_comms_.get("P");
  }
  
  /**
   * Test rewrite of action in EDP
   *    Sequence, prefixing, recursion, schema expression
   *    + parametrised action
   */
  @Test
  public void testActionRewrite_EDP4()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/action_rewrite_4.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    zs.accept(crtv_);
    
    CircusRewriteVisitor crtv = crtv_; // new CircusRewriteVisitor();
    crtv.setManager(manager);
    crtv.setRewriteStage(2);
    crtv.setSectName(zs.getName());
    crtv.setCircusSpecMap(crtv_.getCircusSpecMap());
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(3);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(4);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 1);
    assertTrue(zst.lst_processes_.contains("P"));
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("P_OP_x"));
    assertTrue(set_id.contains("P_OP_y"));
    assertTrue(set_id.contains("P_OP_z"));
    assertTrue(set_id.contains("P_x"));
    assertTrue(set_id.contains("P_x′"));
    assertTrue(set_id.contains("x?"));
    assertTrue(set_id.contains("x!"));
    assertFalse(set_id.contains("P_x!"));
    assertFalse(set_id.contains("P_x?"));
    
//    Set<String> set_comms = zst.map_set_comms_.get("P");
  }
  
  /**
   * Test rewrite of action in EDP
   *    Sequence, prefixing, recursion, schema expression
   *    + parametrised action by value, result, and value-result
   */
  @Test
  public void testActionRewrite_EDP5()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/action_rewrite_5.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    zs.accept(crtv_);
    
    CircusRewriteVisitor crtv = crtv_; // new CircusRewriteVisitor();
    crtv.setManager(manager);
    crtv.setRewriteStage(2);
    crtv.setSectName(zs.getName());
    crtv.setCircusSpecMap(crtv_.getCircusSpecMap());
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(3);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(4);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 1);
    assertTrue(zst.lst_processes_.contains("P"));
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("P_OP_x"));
    assertTrue(set_id.contains("P_OP_y"));
    assertTrue(set_id.contains("P_OP_z"));
    assertTrue(set_id.contains("P_x"));
    assertTrue(set_id.contains("P_x′"));
    assertTrue(set_id.contains("x?"));
    assertTrue(set_id.contains("x!"));
    assertTrue(set_id.contains("P_AssgnOp0"));
    assertTrue(set_id.contains("P_AssgnOp1"));
    assertTrue(set_id.contains("P_AssgnOp2"));
    assertTrue(set_id.contains("P_AssgnOp3"));
    assertTrue(set_id.contains("P_AssgnOp4"));
    assertTrue(set_id.contains("P_AssgnOp5"));
    assertTrue(set_id.contains("P_AssgnOp6"));
    assertFalse(set_id.contains("P_x!"));
    assertFalse(set_id.contains("P_x?"));
    
//    Set<String> set_comms = zst.map_set_comms_.get("P");
  }

  /**
   * Test rewrite of action in EDP
   *    prefixing, 
   *    + alternation
   */
  @Test
  public void testActionRewrite_EDP6()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/action_rewrite_6.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    zs.accept(crtv_);
    
    CircusRewriteVisitor crtv = crtv_; // new CircusRewriteVisitor();
    crtv.setManager(manager);
    crtv.setRewriteStage(2);
    crtv.setSectName(zs.getName());
    crtv.setCircusSpecMap(crtv_.getCircusSpecMap());
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(3);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(4);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 1);
    assertTrue(zst.lst_processes_.contains("P"));
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("P_OP_x"));
    assertTrue(set_id.contains("P_OP_y"));
    assertTrue(set_id.contains("P_OP_z"));
    assertTrue(set_id.contains("P_x"));
    assertTrue(set_id.contains("P_x′"));
    assertTrue(set_id.contains("x?"));
    assertTrue(set_id.contains("x!"));
    assertFalse(set_id.contains("P_x!"));
    assertFalse(set_id.contains("P_x?"));
    
    Set<String> set_comms = zst.map_set_comms_.get("P");
    Set<String> set_schemas = zst.map_set_schemas_.get("P");
    Set<String> set_actions = zst.map_set_actions_.get("P");
  }
  
  /**
   * Test rewrite of action in EDP
   *    prefixing, 
   *    + alternation
   */
  @Test
  public void testActionRewrite_EDP7()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/action_rewrite_7.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    zs.accept(crtv_);
    
    CircusRewriteVisitor crtv = crtv_; // new CircusRewriteVisitor();
    crtv.setManager(manager);
    crtv.setRewriteStage(2);
    crtv.setSectName(zs.getName());
    crtv.setCircusSpecMap(crtv_.getCircusSpecMap());
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(3);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(4);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
          String st = Circus2ZCSPUtils.termToString(((ProcessPara)para).getCircusProcess());
        }
      }
    }
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 1);
    assertTrue(zst.lst_processes_.contains("P"));
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("P_OP_x"));
    assertTrue(set_id.contains("P_OP_y"));
    assertTrue(set_id.contains("P_OP_z"));
    assertTrue(set_id.contains("P_x"));
    assertTrue(set_id.contains("P_x′"));
    assertTrue(set_id.contains("x?"));
    assertTrue(set_id.contains("x!"));
    assertFalse(set_id.contains("P_x!"));
    assertFalse(set_id.contains("P_x?"));
    
    Set<String> set_comms = zst.map_set_comms_.get("P");
    Set<String> set_schemas = zst.map_set_schemas_.get("P");
    Set<String> set_actions = zst.map_set_actions_.get("P");
  }
  
  /**
   * Test rewrite of action in EDP
   *    prefixing, 
   *    + specification statement + variable block
   */
  @Test
  public void testActionRewrite_EDP8()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/action_rewrite_8.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    zs.accept(crtv_);
    
    CircusRewriteVisitor crtv = crtv_; // new CircusRewriteVisitor();
    crtv.setManager(manager);
    crtv.setRewriteStage(2);
    crtv.setSectName(zs.getName());
    crtv.setCircusSpecMap(crtv_.getCircusSpecMap());
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(3);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(4);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
          String st = Circus2ZCSPUtils.termToString(((ProcessPara)para).getCircusProcess());
        }
      }
    }
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 1);
    assertTrue(zst.lst_processes_.contains("P"));
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("P_OP_x"));
    assertTrue(set_id.contains("P_OP_y"));
    assertTrue(set_id.contains("P_OP_z"));
    assertTrue(set_id.contains("P_x"));
    assertTrue(set_id.contains("P_x′"));
    assertTrue(set_id.contains("x?"));
    assertTrue(set_id.contains("x!"));
    assertFalse(set_id.contains("P_x!"));
    assertFalse(set_id.contains("P_x?"));
    
    Set<String> set_comms = zst.map_set_comms_.get("P");
    Set<String> set_schemas = zst.map_set_schemas_.get("P");
    Set<String> set_actions = zst.map_set_actions_.get("P");
  }
  
  /**
   * Test rewrite of action in EDP
   *    prefixing, 
   *    + assumption + coercion + variable block
   */
  @Test
  public void testActionRewrite_EDP9()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/action_rewrite_9.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    zs.accept(crtv_);
    
    CircusRewriteVisitor crtv = crtv_; // new CircusRewriteVisitor();
    crtv.setManager(manager);
    crtv.setRewriteStage(2);
    crtv.setSectName(zs.getName());
    crtv.setCircusSpecMap(crtv_.getCircusSpecMap());
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(3);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(4);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
          String st = Circus2ZCSPUtils.termToString(((ProcessPara)para).getCircusProcess());
        }
      }
    }
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 1);
    assertTrue(zst.lst_processes_.contains("P"));
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("P_OP_x"));
    assertTrue(set_id.contains("P_OP_y"));
    assertTrue(set_id.contains("P_OP_z"));
    assertTrue(set_id.contains("P_x"));
    assertTrue(set_id.contains("P_x′"));
    assertTrue(set_id.contains("x?"));
    assertTrue(set_id.contains("x!"));
    assertFalse(set_id.contains("P_x!"));
    assertFalse(set_id.contains("P_x?"));
    
    Set<String> set_comms = zst.map_set_comms_.get("P");
    Set<String> set_schemas = zst.map_set_schemas_.get("P");
    Set<String> set_actions = zst.map_set_actions_.get("P");
  }
  
  /**
   * Test rewrite of action in EDP
   *    prefixing, 
   *    + renaming + variable block
   */
  @Test
  public void testActionRewrite_EDP10()
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusRewriteVisitorTest.class.getResource("/UnitTest/action_rewrite_10.tex");
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setManager(manager);
    zs.accept(crtv_);
    
    CircusRewriteVisitor crtv = crtv_; // new CircusRewriteVisitor();
    crtv.setManager(manager);
    crtv.setRewriteStage(2);
    crtv.setSectName(zs.getName());
    crtv.setCircusSpecMap(crtv_.getCircusSpecMap());
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(3);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
        }
      }
    }
    
    crtv.setRewriteStage(4);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv);
          String st = Circus2ZCSPUtils.termToString(((ProcessPara)para).getCircusProcess());
        }
      }
    }
    
    ZStat zst = new ZStat();
    TestUtils.Stat_ZSection(zs, zst, manager);
    
    assertTrue(zst.nr_of_processes_ == 1);
    assertTrue(zst.lst_processes_.contains("P"));
    Set<String> set_id = zst.map_set_id_.get("P");
    assertTrue(set_id.contains("P_OP_x"));
    assertTrue(set_id.contains("P_OP_y"));
    assertTrue(set_id.contains("P_OP_z"));
    assertTrue(set_id.contains("P_x"));
    assertTrue(set_id.contains("P_x′"));
    assertTrue(set_id.contains("x?"));
    assertTrue(set_id.contains("x!"));
    assertFalse(set_id.contains("P_x!"));
    assertFalse(set_id.contains("P_x?"));
    
    Set<String> set_comms = zst.map_set_comms_.get("P");
    Set<String> set_schemas = zst.map_set_schemas_.get("P");
    Set<String> set_actions = zst.map_set_actions_.get("P");
  }

}

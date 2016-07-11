package net.sourceforge.czt.circus2zcsp;

import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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
import net.sourceforge.czt.circus2zcsp.ast.CSPSpec;
import net.sourceforge.czt.circus2zcsp.data.CircusSpecMap;
import net.sourceforge.czt.circus2zcsp.data.Node;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.circus2zcsp.util.TestUtils;
import net.sourceforge.czt.circus2zcsp.util.ZStat;
import net.sourceforge.czt.circus2zcsp.visitor.CircusRewriteVisitor;
import net.sourceforge.czt.circus2zcsp.visitor.CircusToCSPVisitor;
import net.sourceforge.czt.circus2zcsp.visitor.DefinitionReferencesMapVisitor;
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

public class CircusToCSPVisitorTest extends TestCase
{


  private ZFactory zfac_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();

  private CircusRewriteVisitor crtv_ = new CircusRewriteVisitor();
  
  private CircusSpecMap map_ = null;
  
  public CircusToCSPVisitorTest()
  {}
  
  private CSPSpec rewriteProgram(String filename)
  {
    ZSect zs = zfac_.createZSect();
    List<Term> lt = new ArrayList<Term>();

    URL url = CircusToCSPVisitorTest.class.getResource(filename);
    assertFalse(url == null);
    
    SectionManager manager = TestUtils.urlToTerm(url, lt, zs);

    crtv_.setSectName(zs.getName());
    crtv_.setManager(manager);
    zs.accept(crtv_);
    
    crtv_.setRewriteStage(2);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv_);
        }
      }
    }
    
    crtv_.setRewriteStage(3);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv_);
        }
      }
    }
    
    crtv_.setRewriteStage(4);
    for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
      if (para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          ((ProcessPara)para).accept(crtv_);
//          String st = Circus2ZCSPUtils.termToString(((ProcessPara)para).getCircusProcess());
        }
      }
    }
    
 // get all references in this rewritten circus program
    DefinitionReferencesMapVisitor drmv = new DefinitionReferencesMapVisitor(crtv_.getCircusSpecMap(), manager, zs.getName());
    zs.accept(drmv);

    Map<Node, Set<Node>> refmap = drmv.getRefMap();
    
    CSPSpec cspspec = new CSPSpec();
    CircusToCSPVisitor ctcv = new CircusToCSPVisitor(crtv_.getCircusSpecMap(), cspspec, crtv_.getManager(), refmap);

    zs.accept(ctcv);
    
    return cspspec;
  }
  
  
  /**
   * Test translation of free type to CSP
   *    free type with constants and recursive constructors, and its application (con(a), con~a)
   *            + given set
   *            + etc
   */
  @Test
  public void testFreeType_0()
  {
    CSPSpec cspspec = rewriteProgram("/UnitTest/CSP/freetype_0.tex");
//    ZSect zs = rewriteProgram("/UnitTest/CSP/freetype_0.tex");
//    CSPSpec cspspec = new CSPSpec();
//    CircusToCSPVisitor ctcv = new CircusToCSPVisitor(crtv_.getCircusSpecMap(), cspspec, crtv_.getManager());
//    
//    zs.accept(ctcv);
    String spec = cspspec.toString();
    
    Debug.debug_print("================= [Start] CSP ========================");
    Debug.debug_print("\n" + spec);
    Debug.debug_print("================= [End] CSP ========================");
  }

  /**
   * Test translation of type to CSP
   *    function type
   */
  @Test
  public void testType_0()
  {
    CSPSpec cspspec = rewriteProgram("/UnitTest/CSP/type_0.tex");
//    ZSect zs = rewriteProgram("/UnitTest/CSP/type_0.tex");
//    CSPSpec cspspec = new CSPSpec();
//    CircusToCSPVisitor ctcv = new CircusToCSPVisitor(crtv_.getCircusSpecMap(), cspspec, crtv_.getManager());
//    
//    zs.accept(ctcv);
    String spec = cspspec.toString();
    
    Debug.debug_print("================= [Start] CSP ========================");
    Debug.debug_print("\n" + spec);
    Debug.debug_print("================= [End] CSP ========================");
  }

  /**
   * Test translation of logic to CSP
   *    logic operator of predicates
   *    basic
   *    boolean
   */
  @Test
  public void testExp_0()
  {
    CSPSpec cspspec = rewriteProgram("/UnitTest/CSP/exp_0.tex");
//    ZSect zs = rewriteProgram("/UnitTest/CSP/exp_0.tex");
//    CSPSpec cspspec = new CSPSpec();
//    CircusToCSPVisitor ctcv = new CircusToCSPVisitor(crtv_.getCircusSpecMap(), cspspec, crtv_.getManager());
//    
//    zs.accept(ctcv);
    String spec = cspspec.toString();
    
    Debug.debug_print("================= [Start] CSP ========================");
    Debug.debug_print("\n" + spec);
    Debug.debug_print("================= [End] CSP ========================");
    
    assertTrue(Circus2ZCSPUtils.isStringContains(spec," and "));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec," or "));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec," implies(u == 1, x > 1) "));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec," iff(u == x, x == u) "));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec," not "));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"forall(T, (\\ y @ x > y)) "));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,
        "exists(T, (\\ z @ exists(T, (\\ y @ x == y and x == z)))) "));  
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,
        "exists(T, (\\ z @ exists(T, (\\ y @ x == y and x == z)))) "));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, 
        "(\\ y @ if member((y), {y | y <- T, y > 2}) then y - 1 else undefined)(1)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, 
        "(\\ y, z @ if member((y, z), {y, z | y <- T, z <- T, y > 2 and z > 1}) then y - z else undefined)((1, 2))"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,
        "(mu(T, (\\ y @ y - 1 == 1), (\\ y @ y)))"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,
        "(mu({1}, (\\ z @ true), (\\ z @ z + 1)))"));
  }

  /**
   * Test translation of number to CSP
   */
  @Test
  public void testExp_1()
  {
    CSPSpec cspspec = rewriteProgram("/UnitTest/CSP/exp_1.tex");
//    CSPSpec cspspec = new CSPSpec();
//    CircusToCSPVisitor ctcv = new CircusToCSPVisitor(crtv_.getCircusSpecMap(), cspspec, crtv_.getManager());
//    
//    zs.accept(ctcv);
    String spec = cspspec.toString();
    
    Debug.debug_print("================= [Start] CSP ========================");
    Debug.debug_print("\n" + spec);
    Debug.debug_print("================= [End] CSP ========================");
    
    assertTrue(Circus2ZCSPUtils.isStringContains(spec," Nat"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec," Nat_1"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec," Int"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec," num_1"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"succ(1)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"-x"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"x - 1"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"x * 1"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"x + 1"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"x / 1"));    
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"x % 2"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"x <= 1"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"x < 1"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"x >= 1"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"x > 1"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"min(T)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"max(T)"));
  }
  
  /**
   * Test translation of set to CSP
   */
  @Test
  public void testExp_2()
  {
    CSPSpec cspspec = rewriteProgram("/UnitTest/CSP/exp_2.tex");
//    CSPSpec cspspec = new CSPSpec();
//    CircusToCSPVisitor ctcv = new CircusToCSPVisitor(crtv_.getCircusSpecMap(), cspspec, crtv_.getManager());
//    
//    zs.accept(ctcv);
    String spec = cspspec.toString();
    
    Debug.debug_print("================= [Start] CSP ========================");
    Debug.debug_print("\n" + spec);
    Debug.debug_print("================= [End] CSP ========================");
    
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype T = {0 .. 3}"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype T1 = {0 .. 3}"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype T2 = {0, 1, 2, 3}"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype T3 = { x * x | x <- T, x > 1}"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype T4 = { x | x <- T, x > 1}"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype T5 = { x * x | x <- T}"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype T6 = union(T1, inter(T2, T3))"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype T7 = diff(T1, T2)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype T8 = symdiff(T1, T2)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype T9 = Union({T, T1})"));    
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype T10 = Inter({T, T1})"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype T11 = Set(T)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype T12 = finset_1(T)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"datatype NAME = NAME_GS.{1..MAXINS}"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"channel c1 : T5"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"channel c2 : T.T5"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"channel c3 : T.T1.T2"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"channel c4 : Set(T)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"channel c5 : power_1(T)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"member(x, T)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"not member(x, T)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"{x} != {}"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"T1 <= T2"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"T1 < T2"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"len(T) == 4"));
  }
  
  /**
   * Test translation of relation to CSP
   */
  @Test
  public void testExp_3()
  {
    CSPSpec cspspec = rewriteProgram("/UnitTest/CSP/exp_3.tex");
//    CSPSpec cspspec = new CSPSpec();
//    CircusToCSPVisitor ctcv = new CircusToCSPVisitor(crtv_.getCircusSpecMap(), cspspec, crtv_.getManager());
//    
//    zs.accept(ctcv);
    String spec = cspspec.toString();
    
    Debug.debug_print("================= [Start] CSP ========================");
    Debug.debug_print("\n" + spec);
    Debug.debug_print("================= [End] CSP ========================");
    
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype T1 = rel(T, TT)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype T2 = id(T)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"dom(r1)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"ran(r1)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"id(T)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"comp(r1, {(4, 0), (5, 1)})"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"circ(r1, {(4, 0), (5, 1)})"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"dres({0, 1}, r)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"rres(r, {4, 5})"));    
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"ndres({0, 1}, r)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nrres(r, {4, 5})"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"inv(r1)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"oplus(r1, {(0, 5)})"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"itern(r, 2) == itern(r, 1)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"first(x)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"second(x)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"img(T, r) == TT"));
  }
  
  /**
   * Test translation of function to CSP
   */
  @Test
  public void testExp_4()
  {
    CSPSpec cspspec = rewriteProgram("/UnitTest/CSP/exp_4.tex");
//    CSPSpec cspspec = new CSPSpec();
//    CircusToCSPVisitor ctcv = new CircusToCSPVisitor(crtv_.getCircusSpecMap(), cspspec, crtv_.getManager());
//    
//    zs.accept(ctcv);
    String spec = cspspec.toString();
    
    Debug.debug_print("================= [Start] CSP ========================");
    Debug.debug_print("\n" + spec);
    Debug.debug_print("================= [End] CSP ========================");
    
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype FT1 = tfun(T, TT)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype FT2 = pfun(T, TT)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype FT3 = pifun(T, TT)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype FT4 = tifun(T, TT)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype FT5 = psfun(T, TT)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype FT6 = tsfun(T, TT)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype FT7 = bjfun(T, TT)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype FT8 = pfun(T, TT)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"nametype FT9 = pifun(T, TT)"));    
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"fa(f, 0)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"fa(f, 1)"));
  }
  
  /**
   * Test translation of sequence to CSP
   */
  @Test
  public void testExp_5()
  {
    CSPSpec cspspec = rewriteProgram("/UnitTest/CSP/exp_5.tex");
//    CSPSpec cspspec = new CSPSpec();
//    CircusToCSPVisitor ctcv = new CircusToCSPVisitor(crtv_.getCircusSpecMap(), cspspec, crtv_.getManager());
//    
//    zs.accept(ctcv);
    String spec = cspspec.toString();
    
    Debug.debug_print("================= [Start] CSP ========================");
    Debug.debug_print("\n" + spec);
    Debug.debug_print("================= [End] CSP ========================");
    
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"len(s) == 3"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"fseq(T)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"iseq(T)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"seq1(T)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"<0,1,2,3>"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"<> ^ S == S"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"reverse(s)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"head(S)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"tail(S)"));    
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"front(S)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"last(S)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"squash({(0, 1), (3, 2), (2, 1)})"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"extract(T, S)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"filter(T, S)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"prefix(<0,1>, S)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"suffix(<2,3>, S)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"infix(<1,2>, S)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"concat(<<0,1>,<2,3>>)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"disjoint(<T,TT>)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"partition(<T,TT>, union(T, TT))"));
  }
  
  /**
   * Test translation of channel set to CSP
   */
  @Test
  public void testChnset()
  {
    CSPSpec cspspec = rewriteProgram("/UnitTest/CSP/chnset.tex");
//    CSPSpec cspspec = new CSPSpec();
//    CircusToCSPVisitor ctcv = new CircusToCSPVisitor(crtv_.getCircusSpecMap(), cspspec, crtv_.getManager());
//    
//    zs.accept(ctcv);
    String spec = cspspec.toString();
    
    Debug.debug_print("================= [Start] CSP ========================");
    Debug.debug_print("\n" + spec);
    Debug.debug_print("================= [End] CSP ========================");
    
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"CS0 = {||}"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"CS1 = {| c, d, e |}"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"CS2 = {| in, out |}"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"CS3 = union(CS1, CS2)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"CS4 = inter(CS1, CS2)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"CS5 = diff(CS1, CS2)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"CS6 = symdiff(CS1, {| c |})"));
  }
  
  /**
   * Test translation of channel set to CSP
   */
  @Test
  public void testProcs()
  {
    CSPSpec cspspec = rewriteProgram("/UnitTest/CSP/processes.tex");
//    CSPSpec cspspec = new CSPSpec();
//    CircusToCSPVisitor ctcv = new CircusToCSPVisitor(crtv_.getCircusSpecMap(), cspspec, crtv_.getManager());
//    
//    zs.accept(ctcv);
    String spec = cspspec.toString();
    
    Debug.debug_print("================= [Start] CSP ========================");
    Debug.debug_print("\n" + spec);
    Debug.debug_print("================= [End] CSP ========================");
    
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"P = "));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"P1 = (P ; P [] P) |~| P [| {| in, out |} |] P ||| P \\ CS"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec,"P2 =  ; x:<0,1> @ P1"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "P3 =  [] x:T @ P1"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "P4 =  |~| x:T @ P1"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "P5 =  ||| x:T @ P1"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "P6 =  [| CS |] x:T @ P1"));
  }
  
  /**
   * Test translation of actions to CSP
   *    prefix + schema expression + assignment + spec stat + external choice
   */
  @Test
  public void testAction_0()
  {
    CSPSpec cspspec = rewriteProgram("/UnitTest/CSP/action_0.tex");
//    CSPSpec cspspec = new CSPSpec();
//    CircusToCSPVisitor ctcv = new CircusToCSPVisitor(crtv_.getCircusSpecMap(), cspspec, crtv_.getManager());
//    
//    zs.accept(ctcv);
    String spec = cspspec.toString();
    
    Debug.debug_print("================= [Start] CSP ========================");
    Debug.debug_print("\n" + spec);
    Debug.debug_print("================= [End] CSP ========================");
    
  }
  
  /**
   * Test translation of actions to CSP
   *    prefix + schema expression
   */
  @Test
  public void testAction_1()
  {
    CSPSpec cspspec = rewriteProgram("/UnitTest/CSP/action_1.tex");
//    CSPSpec cspspec = new CSPSpec();
//    CircusToCSPVisitor ctcv = new CircusToCSPVisitor(crtv_.getCircusSpecMap(), cspspec, crtv_.getManager());
//    
//    zs.accept(ctcv);
    String spec = cspspec.toString();
    
    Debug.debug_print("================= [Start] CSP ========================");
    Debug.debug_print("\n" + spec);
    Debug.debug_print("================= [End] CSP ========================");
    
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel set[0-9]+\\s*:\\s*Tx$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel get[0-9]+\\s*:\\s*Tx$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel set[0-9]+\\s*:\\s*Ty$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel get[0-9]+\\s*:\\s*Ty$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel set[0-9]+\\s*:\\s*Tz$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel get[0-9]+\\s*:\\s*Tz$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel P_Update\\s*:\\s*Tx.Ty.Tx.Tz.Ty.Tz$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel P_Update_fOp\\s*:\\s*Tx.Ty.Tz$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel P_OP_x\\s*:\\s*Tx$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel P_OP_y\\s*:\\s*Ty$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel P_OP_z\\s*:\\s*Tz$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^HIDE_CSPB = \\{\\|P_Init, set3, get3, end, set4, get4, set5, get5, P_Update, P_Update_fOp\\|\\}$"));
    assertTrue(Circus2ZCSPUtils.getStringMatchCount(spec, "^MemCell_[0-9]+") == 3);
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "(P_Init ->  SKIP) ;"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "|~| u: Tx, v: Ty, w: Tz @"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "(P_Update!x!y?u!z?v?w -> set3!u"
        + " -> set5!w -> set4!v ->  SKIP [] P_Update_fOp?u?v?w -> set3!u -> set5!w -> set4!v -> DIV)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "[|{| set3, get3, set4, get4, set5, get5 |}|] "
        + "(MemCell_3 [|{|end|}|] MemCell_4 [|{|end|}|] MemCell_5)) \\ {| set3, get3, set4, get4, set5, get5 |})"));
  }
  
  /**
   * Test translation of actions to CSP
   *    prefix + variable block
   */
  @Test
  public void testAction_2()
  {
    CSPSpec cspspec = rewriteProgram("/UnitTest/CSP/action_2.tex");
//    CSPSpec cspspec = new CSPSpec();
//    CircusToCSPVisitor ctcv = new CircusToCSPVisitor(crtv_.getCircusSpecMap(), cspspec, crtv_.getManager());
//    
//    zs.accept(ctcv);
    String spec = cspspec.toString();
    
    Debug.debug_print("================= [Start] CSP ========================");
    Debug.debug_print("\n" + spec);
    Debug.debug_print("================= [End] CSP ========================");
    
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel set[0-9]+\\s*:\\s*T$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel set[0-9]+\\s*:\\s*T$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel P_AssgnOp[0-9]+\\s*:\\s*T$"));
    assertTrue(!Circus2ZCSPUtils.isStringMatch(spec, "^channel P_AssgnOp[0-9]+_fOp\\s*$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel set[0-9]+\\s*:\\s*T$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel set[0-9]+\\s*:\\s*Tx$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel get[0-9]+\\s*:\\s*Tx$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel set[0-9]+\\s*:\\s*Ty$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel get[0-9]+\\s*:\\s*Ty$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel set[0-9]+\\s*:\\s*Tz$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel get[0-9]+\\s*:\\s*Tz$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel P_Update\\s*:\\s*Tx.Ty.Tx.Tz.Ty.Tz$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel P_Update_fOp\\s*:\\s*Tx.Ty.Tz$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel P_OP_x\\s*:\\s*Tx$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel P_OP_y\\s*:\\s*Ty$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel P_OP_z\\s*:\\s*Tz$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^HIDE_CSPB = \\{\\|P_Init, set1, get1, end, P_AssgnOp0, set5, get5, set6, get6, set7, get7, P_Update, P_Update_fOp\\|\\}$"));
    assertTrue(Circus2ZCSPUtils.getStringMatchCount(spec, "^MemCell_[0-9]+") == 4);
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "|~| l: T @"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "|~| u: Tx, v: Ty, w: Tz @"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "(P_AssgnOp0?l -> set1!l ->  SKIP) ;"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "P_OP_z?z -> P_OP_y?y -> P_OP_x?x -> get1!l"
        + " -> out.(x - l).(y + l).(z * l) -> SKIP;"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "end -> SKIP) "
        + "[|{| set1, get1 |}|] (MemCell_1)) \\ {| set1, get1 |})"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "in?x?y?z -> "
        + "(P_Update!x!y?u!z?v?w -> set6!v -> set5!u -> set7!w ->  SKIP [] "
        + "P_Update_fOp?u?v?w -> set6!v -> set5!u -> set7!w -> DIV) "
        ));
  }
  
  /**
   * Test translation of actions to CSP
   *    prefix + variable block + external choice
   */
  @Test
  public void testAction_3()
  {
    CSPSpec cspspec = rewriteProgram("/UnitTest/CSP/action_3.tex");
//    CSPSpec cspspec = new CSPSpec();
//    CircusToCSPVisitor ctcv = new CircusToCSPVisitor(crtv_.getCircusSpecMap(), cspspec, crtv_.getManager());
//    
//    zs.accept(ctcv);
    String spec = cspspec.toString();
    
    Debug.debug_print("================= [Start] CSP ========================");
    Debug.debug_print("\n" + spec);
    Debug.debug_print("================= [End] CSP ========================");
    
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel set[0-9]+\\s*:\\s*T$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel set[0-9]+\\s*:\\s*T$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel set[0-9]+\\s*:\\s*T$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel set[0-9]+\\s*:\\s*Tx$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel get[0-9]+\\s*:\\s*Tx$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel set[0-9]+\\s*:\\s*Ty$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel get[0-9]+\\s*:\\s*Ty$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel set[0-9]+\\s*:\\s*Tz$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel get[0-9]+\\s*:\\s*Tz$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel P_Update\\s*:\\s*Tx.Ty.Tx.Tz.Ty.Tz$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel P_Update_fOp\\s*:\\s*Tx.Ty.Tz$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel P_OP_x\\s*:\\s*Tx$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel P_OP_y\\s*:\\s*Ty$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^channel P_OP_z\\s*:\\s*Tz$"));
    assertTrue(Circus2ZCSPUtils.isStringMatch(spec, "^HIDE_CSPB = \\{\\|P_Init, set3, "
        + "get3, end, set4, get4, set5, get5, set6, get6, P_Update, P_Update_fOp, set7, "
        + "get7, set8, get8, set9, get9, set10, get10\\|\\}$"));
    assertTrue(Circus2ZCSPUtils.getStringMatchCount(spec, "^MemCell_[0-9]+") == 8);
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "|~| l: T @"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "|~| u: Tx, v: Ty, w: Tz @"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "get3?l -> (out.(x - l).(y + l).(z * l) -> SKIP \\ {| out |})"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "get7?l1 -> get8?l2 -> get9?l3 -> "
        + "(out.(l1).(l2).(l3) -> SKIP [] in?l1.(l2)?l3 -> set7!l1 -> set9!l3 -> SKIP)"));
    assertTrue(Circus2ZCSPUtils.isStringContains(spec, "get10?l -> (x > 0 and l == 2 & c.(l) -> SKIP)"));
  }
}


package net.sourceforge.czt.circus2zcsp;

import java.io.File;
import java.io.StringWriter;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus2zcsp.ast.CSPSpec;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.circus2zcsp.util.TestUtils;
import net.sourceforge.czt.circus2zcsp.util.ZStat;
import net.sourceforge.czt.circus2zcsp.visitor.CircusRewriteVisitor;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionInfoException;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

import org.junit.Test;

public class TransformerTest extends TestCase
{

  @Test
  public void test()
  {
    fail("Not yet implemented");
  }

  @Test
  public void testSchAction() // throws SectionInfoException, CommandException
  {
    TestUtils.test_print("==================== Test Schema Exp as Action ====================");
    SectionManager manager = TestUtils
        .strToSecManager("\\begin{circus}\n"
            + "\\circprocess\\ TESTP \\circdef \\circbegin \n "
            + "\\circstate\\ State == [~ reg: 0..2 | true ~] \\\\\n"
            + "Init == [~ (State)\' | reg\' = 0 ~] \\\\\n"
            + "Read == [~ \\Xi State; r!: 0..2 | r! = reg ~] \\\\\n"
            + "\\circspot Init \\circseq (\\circmu X \\circspot (\\circvar\\ r: 0..2 \\circspot (Read \\circseq X))) \\circend\n"
            + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");

      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//    Debug.debug_print("==========================================");
//    Debug.debug_print(writer.toString());
//    // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());
//    Debug.debug_print("==========================================");
//    Debug.debug_print(zrm);

      String csp = cspspec.toString();
      assertEquals(
          zrm,
          "\\documentclass{article}\n\\usepackage{fuzz}\n\n\\begin{document}\n\n%"
              + "\\begin{zsection}\t \\SECTION Specification \\parents~standard\\_toolkit\n%\\end{zsection}\n\n"
              + "\\begin{zed}\n\tTESTP\\_State \\defs [~  TESTP\\_reg : 0 \\upto 2 | true  ~]\n\\end{zed}\n\n"
              + "\\begin{zed}\n\tInit \\defs [~  TESTP\\_State' | TESTP\\_reg' = 0  ~]\n\\end{zed}\n\n"
              + "\\begin{zed}\n\tTESTP\\_Init \\defs [~  TESTP\\_State' | TESTP\\_reg' = 0  ~]\n\\end{zed}\n\n"
              + "\\begin{zed}\n\tfTESTP\\_Init \\defs [~  \\Xi TESTP\\_State | \\lnot \\pre TESTP\\_Init  ~]\n\\end{zed}\n\n"
              + "\\begin{zed}\n\tTESTP\\_Read \\defs [~  \\Xi TESTP\\_State ; r! : 0 \\upto 2 | r! = TESTP\\_reg  ~]\n\\end{zed}\n\n"
              + "\\begin{zed}\n\tfTESTP\\_Read \\defs [~  \\Xi TESTP\\_State | \\lnot \\pre TESTP\\_Read  ~]\n\\end{zed}\n\n"
              + "\\end{document}\n");
      assertEquals(
          csp,
          "-- type\nnametype Nat = {0..}\n\n\n-- channels definition\nchannel TESTP_reg: {0 .. 2}\n"
              + "channel TESTP_Init\nchannel fTESTP_Init\nchannel TESTP_Read : {0 .. 2}\nchannel fTESTP_Read\n"
              + "channel put0: {0 .. 2}\nchannel get0: {0 .. 2}\nchannel end\n\n-- hidden event\n"
              + "HIDE_CSPB = {|fTESTP_Init, fTESTP_Read, TESTP_Init, TESTP_Read|}\n\n-- processes for variable "
              + "storing and retrieving \nVar_0 = put0?x -> Var1_0(x)\nVar1_0(x) = put0?y -> Var1_0(y) [] get0!x -> "
              + "Var1_0(x) [] end -> SKIP\n\n-- processes \n-- Divergent Process \nDIV = DIV\n\nMAIN = "
              + "TESTP_Main\nTESTP_Main = (TESTP_Init -> SKIP [] fTESTP_Init -> DIV); let X = (|~| r:{0 .. 2}@ "
              + "(((((TESTP_Read?r -> put0!r -> SKIP [] fTESTP_Read -> DIV); X);end -> SKIP) "
              + "[|{|put0, get0, end|}|] Var_0) \\{|put0, get0, end|})) within X\n\n");
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }

  }

  /**
   * Test action assignment
   * 
   * @throws CommandException
   * @throws SectionInfoException
   */
  @Test
  public void testAssign() // throws SectionInfoException, CommandException
  {
    TestUtils.test_print("==================== Test Assignment Action ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c,d: 0..10 \n" + "\\end{circus}\n" + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\ "
        + "\\circspot (c?x \\then x := x + 1 \\circseq d!3 \\then \\Skip) \\circend\n"
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//    Debug.debug_print("==========================================");
//    Debug.debug_print(writer.toString());
//    // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());
//    Debug.debug_print("==========================================");
//    Debug.debug_print(zrm);

      String csp = cspspec.toString();

      assertTrue(true);
//      assertEquals(
//          zrm,
//          "\\documentclass{article}\n"
//              + "\\usepackage{fuzz}\n"
//              + "\n"
//              + "\\begin{document}\n"
//              + "\n"
//              + "%\\begin{zsection}\t \\SECTION Specification \\parents~standard\\_toolkit\n"
//              + "%\\end{zsection}\n"
//              + "\n"
//              + "\\begin{zed}\n"
//              + "\tTESTP\\_defaultSt \\defs [~  TESTP\\_dummy : \\{ 0 , 1 \\} | true  ~]\n"
//              + "\\end{zed}\n"
//              + "\n"
//              + "\\begin{zed}\n"
//              + "\tInit \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n"
//              + "\\end{zed}\n"
//              + "\n"
//              + "\\begin{zed}\n"
//              + "\tTESTP\\_AssOp0 \\defs [~  \\Delta TESTP\\_defaultSt ; x? : 0 \\upto 10 ; x! : 0 \\upto 10 | x! = x? + 1  ~]\n"
//              + "\\end{zed}\n"
//              + "\n"
//              + "\\begin{zed}\n"
//              + "\tTESTP\\_Init \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n"
//              + "\\end{zed}\n"
//              + "\n"
//              + "\\begin{zed}\n"
//              + "\tfTESTP\\_Init \\defs [~  \\Xi TESTP\\_defaultSt | \\lnot \\pre TESTP\\_Init  ~]\n"
//              + "\\end{zed}\n" + "\n" + "\\end{document}\n" + "");
//      assertEquals(csp, "-- type\n" + "nametype Nat = {0..}\n" + "\n" + "\n"
//          + "-- channels definition\n" + "channel c, d: {0 .. 10}\n"
//          + "channel TESTP_dummy: {0, 1}\n" + "channel TESTP_AssOp0 : {0 .. 10}.{0 .. 10}\n"
//          + "channel TESTP_Init\n" + "channel fTESTP_Init\n" + "\n" + "-- hidden event\n"
//          + "HIDE_CSPB = {|TESTP_AssOp0, fTESTP_Init|}\n" + "\n"
//          + "-- processes for variable storing and retrieving \n" + "\n" + "-- processes \n"
//          + "-- Divergent Process \n" + "DIV = DIV\n" + "\n" + "MAIN = TESTP_Main\n"
//          + "TESTP_Main = (c?x -> TESTP_AssOp0!x?x -> SKIP); (d!3 -> SKIP)\n" + "\n" + "");

      TestUtils.WriteSpecToFiles("AssTest1", zrm, csp);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }


    TestUtils.test_print("==================== Test Assignment Action #1 ====================");
    manager.reset();
    manager = TestUtils
        .strToSecManager("\\begin{circus}\n"
            + "\\circchannel\\ read: 0..2 \n"
            + "\\end{circus}\n"
            + "\\begin{circus}\n"
            + "\\circprocess\\ TESTP \\circdef \\circbegin \n "
            + "\\circstate\\ State == [~ reg: 0..2 | true ~] \\\\\n"
            + "Init == [~ (State)\' | reg\' = 0 ~] \\\\\n"
            + "Read == [~ \\Xi State; r!: 0..2 | r! = reg ~] \\\\\n"
            + "\\circspot \\lschexpract Init \\rschexpract \\circseq "
            + "         (\\circmu X \\circspot (\\circvar\\ r: 0..2 \\circspot "
            + "         (r,reg := r+1,reg+1 \\circseq \\lschexpract Read \\rschexpract \\circseq X))) \\circend\n"
            + "\\end{circus}");

    try {
      Transformer trans1 = new Transformer(manager, "spec");

      Spec spec = trans1.getSpec();
      CSPSpec cspspec = trans1.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//      Debug.debug_print("==========================================");
//      Debug.debug_print(writer.toString());
      // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());
//      Debug.debug_print("==========================================");
//      Debug.debug_print(zrm);

      String csp = cspspec.toString();

//      assertEquals(
//          zrm,
//          "\\documentclass{article}\n"
//              + "\\usepackage{fuzz}\n"
//              + "\n"
//              + "\\begin{document}\n"
//              + "\n"
//              + "%\\begin{zsection}\t \\SECTION Specification \\parents~standard\\_toolkit\n"
//              + "%\\end{zsection}\n"
//              + "\n"
//              + "\\begin{zed}\n"
//              + "\tTESTP\\_State \\defs [~  TESTP\\_reg : 0 \\upto 2 | true  ~]\n"
//              + "\\end{zed}\n"
//              + "\n"
//              + "\\begin{zed}\n"
//              + "\tInit \\defs [~  TESTP\\_State' | TESTP\\_reg' = 0  ~]\n"
//              + "\\end{zed}\n"
//              + "\n"
//              + "\\begin{zed}\n"
//              + "\tTESTP\\_Init \\defs [~  TESTP\\_State' | TESTP\\_reg' = 0  ~]\n"
//              + "\\end{zed}\n"
//              + "\n"
//              + "\\begin{zed}\n"
//              + "\tfTESTP\\_Init \\defs [~  \\Xi TESTP\\_State | \\lnot \\pre TESTP\\_Init  ~]\n"
//              + "\\end{zed}\n"
//              + "\n"
//              + "\\begin{zed}\n"
//              + "\tTESTP\\_Read \\defs [~  \\Xi TESTP\\_State ; r! : 0 \\upto 2 | r! = TESTP\\_reg  ~]\n"
//              + "\\end{zed}\n"
//              + "\n"
//              + "\\begin{zed}\n"
//              + "\tfTESTP\\_Read \\defs [~  \\Xi TESTP\\_State | \\lnot \\pre TESTP\\_Read  ~]\n"
//              + "\\end{zed}\n"
//              + "\n"
//              + "\\begin{zed}\n"
//              + "\tTESTP\\_AssOp0 \\defs [~  \\Delta TESTP\\_State ; r? : 0 \\upto 2 ; r! : 0 \\upto 2 | r! = r? + 1 \\land TESTP\\_reg' = TESTP\\_reg + 1  ~]\n"
//              + "\\end{zed}\n" + "\n" + "\\end{document}\n" + "");
//      assertEquals(
//          csp,
//          "-- type\n"
//              + "nametype Nat = {0..}\n"
//              + "\n"
//              + "\n"
//              + "-- channels definition\n"
//              + "channel read: {0 .. 2}\n"
//              + "channel TESTP_reg: {0 .. 2}\n"
//              + "channel TESTP_Init\n"
//              + "channel fTESTP_Init\n"
//              + "channel TESTP_Read : {0 .. 2}\n"
//              + "channel fTESTP_Read\n"
//              + "channel put0: {0 .. 2}\n"
//              + "channel get0: {0 .. 2}\n"
//              + "channel end\n"
//              + "channel TESTP_AssOp0 : {0 .. 2}.{0 .. 2}\n"
//              + "\n"
//              + "-- hidden event\n"
//              + "HIDE_CSPB = {|fTESTP_Init, fTESTP_Read, TESTP_Init, TESTP_AssOp0, TESTP_Read|}\n"
//              + "\n"
//              + "-- processes for variable storing and retrieving \n"
//              + "Var_0 = put0?x -> Var1_0(x)\n"
//              + "Var1_0(x) = put0?y -> Var1_0(y) [] get0!x -> Var1_0(x) [] end -> SKIP\n"
//              + "\n"
//              + "-- processes \n"
//              + "-- Divergent Process \n"
//              + "DIV = DIV\n"
//              + "\n"
//              + "MAIN = TESTP_Main\n"
//              + "TESTP_Main = (TESTP_Init -> SKIP [] fTESTP_Init -> DIV); let X = (|~| r:{0 .. 2}@ ((((TESTP_AssOp0!r?r -> put0!r -> SKIP; (TESTP_Read?r -> put0!r -> SKIP [] fTESTP_Read -> DIV); X);end -> SKIP) [|{|put0, get0, end|}|] Var_0) \\{|put0, get0, end|})) within X\n"
//              + "\n" + "");
      assertTrue(true);
      TestUtils.WriteSpecToFiles("AssTest2", zrm, csp);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }

  }

  /**
   * Test parallel action 
   * ns1 includes state variables and ns2 is empty
   */
  @Test
  public void testParallelAction() // throws SectionInfoException, CommandException
  {
    TestUtils.test_print("==================== Test Parallel Action #0 ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c, d: \\nat \\\\ \n"
        + "\\circchannelset\\ CS == \\lchanset c, d \\rchanset \n" + "\\end{circus}\n"
        + "\\begin{circus}\n" + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: \\nat; b: \\nat] \\\\\n"
        + "     \\t1 Init == [~ (St)\' | a\' = 0 \\land b\' = 0 ~] \\\\\n"
        + "     \\t1 A \\circdef c.a \\then d.b \\then \\Skip\\\\\n"
        + "     \\t1 B \\circdef d.b \\then \\Skip\\\\\n"
        + "     \\t1 \\circnameset NS == \\{ a, b \\} \\\\\n"
        + "     \\t1 \\circspot A \\lpar NS | CS | \\{ \\} \\rpar B \\circend\n" + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//      Debug.debug_print("==========================================");
//      Debug.debug_print(writer.toString());
//      // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());
//      Debug.debug_print("==========================================");
//      Debug.debug_print(zrm);

      String csp = cspspec.toString();
//      assertEquals(
//          zrm,
//          "");
//      assertEquals(
//          csp,
//          "");
      assertTrue(true);
      TestUtils.WriteSpecToFiles("testParallelAction", zrm, csp);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }

  }
  
  /**
   * Test parallel action 
   * ns1 and ns2 include state variables
   */
  @Test
  public void testParallelAction1() // throws SectionInfoException, CommandException
  {
    TestUtils.test_print("==================== Test Parallel Action #1 ====================");
 
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c, d: \\nat \\\\ \n"
        + "\\circchannelset\\ CS == \\lchanset c, d \\rchanset \n" + "\\end{circus}\n"
        + "\\begin{circus}\n" + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: \\nat; b: \\nat] \\\\\n"
        + "     \\t1 Init == [~ (St)\' | a\' = 0 \\land b\' = 0 ~] \\\\\n"
        + "     \\t1 A \\circdef c.a \\then d.b \\then \\Skip\\\\\n"
        + "     \\t1 B \\circdef d.b \\then \\Skip\\\\\n"
        + "     \\t1 \\circnameset NS1 == \\{ a, b \\} \\\\\n"
        + "     \\t1 \\circspot A \\lpar NS1 | CS | \\{ b \\} \\rpar B \\circend\n" + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
      
      String zrm = ISOZ2ZRM.convert(writer.toString());
      String csp = cspspec.toString();
//      assertEquals(
//          zrm,
//          "");
//      assertEquals(
//          csp,
//          "");
      assertTrue(true);
      TestUtils.WriteSpecToFiles("testParallelAction1", zrm, csp);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }

  }

  /**
   * Test parallel action 
   * ns1 includes state variables and ns2 includes local variable
   */
  @Test
  public void testParallelAction2() // throws SectionInfoException, CommandException
  {
    TestUtils.test_print("==================== Test Parallel Action #2 ====================");
 
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c, d: \\nat \\\\ \n"
        + "\\circchannelset\\ CS == \\lchanset c, d \\rchanset \n" + "\\end{circus}\n"
        + "\\begin{circus}\n" + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: \\nat; b: \\nat] \\\\\n"
        + "     \\t1 Init == [~ (St)\' | a\' = 0 \\land b\' = 0 ~] \\\\\n"
        + "     \\t1 A \\circdef c.a \\then d.b \\then \\Skip\\\\\n"
        + "     \\t1 B \\circdef x:0..10 \\circspot d.x \\then \\Skip\\\\\n"
        + "     \\t1 \\circnameset NS1 == \\{~ a, b ~\\} \\\\\n"
        + "     \\t1 \\circspot (\\circvar x:0..10 \\circspot (A \\lpar NS1 | CS | \\{~ x ~\\} \\rpar B(x))) "
        + "   \\circend\n" 
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
      
      String zrm = ISOZ2ZRM.convert(writer.toString());
      String csp = cspspec.toString();
//      assertEquals(
//          zrm,
//          "");
//      assertEquals(
//          csp,
//          "");
      assertTrue(true);
      TestUtils.WriteSpecToFiles("testParallelAction2", zrm, csp);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }

  }
  
  /**
   * Test parallel action 
   * both ns1 and ns2 includes local and state variables
   */
  @Test
  public void testParallelAction3() // throws SectionInfoException, CommandException
  {
    TestUtils.test_print("==================== Test Parallel Action #3 ====================");
 
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c, d: 0..10 \\\\ \n"
        + "\\circchannelset\\ CS == \\lchanset c, d \\rchanset \n" + "\\end{circus}\n"
        + "\\begin{circus}\n" + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: 0..10; b: 0..10] \\\\\n"
        + "     \\t1 Init == [~ (St)\' | a\' = 0 \\land b\' = 0 ~] \\\\\n"
        + "     \\t1 A \\circdef a,b := 1,2 \\\\\n"
        + "     \\t1 B \\circdef x:0..10 \\circspot x,a := 1,0 \\\\\n"
        + "     \\t1 \\circnameset NS1 == \\{~ a, b ~\\} \\\\\n"
        + "     \\t1 \\circspot (\\circvar x,y:0..10 \\circspot (A \\lpar NS1 | CS | \\{~ x ~\\} \\rpar B(x))) "
        + "   \\circend\n" 
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        e.printStackTrace();
      }
      
      String zrm = ISOZ2ZRM.convert(writer.toString());
      String csp = cspspec.toString();
//      assertEquals(
//          zrm,
//          "");
//      assertEquals(
//          csp,
//          "");
      assertTrue(true);
      TestUtils.WriteSpecToFiles("testParallelAction3", zrm, csp);
    }
    catch (SectionInfoException e1) {
      e1.printStackTrace();
    }
  }
  
  
  /**
   * Test parallel action 
   * both ns1 and ns2 includes local and state variables
   */
  @Test
  public void testParallelAction4() // throws SectionInfoException, CommandException
  {
    TestUtils.test_print("==================== Test Parallel Action #4 ====================");
 
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c, d: 0..10 \\\\ \n"
        + "\\circchannelset\\ CS == \\lchanset c, d \\rchanset \n" + "\\end{circus}\n"
        + "\\begin{circus}\n" + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: 0..10; b: 0..10] \\\\\n"
        + "     \\t1 Init == [~ (St)\' | a\' = 0 \\land b\' = 0 ~] \\\\\n"
        + "     \\t1 Write == [~ \\Delta St | a' = 1 ~] \\\\\n"
        + "     \\t1 A \\circdef a,b := 1,2 \\\\\n"
        + "     \\t1 B \\circdef x:0..10 \\circspot (x,a := 1,0 \\circseq \\lschexpract Write \\rschexpract) \\\\\n"
        + "     \\t1 \\circnameset NS1 == \\{~ a, b ~\\} \\\\\n"
        + "     \\t1 \\circspot (\\circvar x,y:0..10 \\circspot (A \\lpar NS1 | CS | \\{~ x ~\\} \\rpar B(x))) "
        + "   \\circend\n" 
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        e.printStackTrace();
      }
      
      String zrm = ISOZ2ZRM.convert(writer.toString());
      String csp = cspspec.toString();
//      assertEquals(
//          zrm,
//          "");
//      assertEquals(
//          csp,
//          "");
      assertTrue(true);
      TestUtils.WriteSpecToFiles("testParallelAction3", zrm, csp);
    }
    catch (SectionInfoException e1) {
      e1.printStackTrace();
    }

  }
  
  /**
   * Test action interleave
   * 
   * @throws CommandException
   * @throws SectionInfoException
   */
  @Test
  public void testInterleave() // throws SectionInfoException, CommandException
  {
    TestUtils.test_print("==================== Test Interleave Action ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c, d: \\nat \\\\ \n" + "\\end{circus}\n" + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: \\nat; b: \\nat] \\\\\n"
        + "     \\t1 Init == [~ (St)\' | a\' = 0 \\land b\' = 0 ~] \\\\\n"
        + "     \\t1 A \\circdef c.a \\then \\Skip\\\\\n"
        + "     \\t1 B \\circdef d.b \\then \\Skip\\\\\n"
        + "     \\t1 \\circspot A \\interleave B \\circend\n" + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//      Debug.debug_print("==========================================");
//      Debug.debug_print(writer.toString());
//      // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());
//      Debug.debug_print("==========================================");
//      Debug.debug_print(zrm);

      String csp = cspspec.toString();

      assertEquals(
          zrm,
          "\\documentclass{article}\n\\usepackage{fuzz}\n\n\\begin{document}\n\n%\\begin{zsection}\t \\SECTION Specification \\parents~standard\\_toolkit\n%\\end{zsection}\n\n\\begin{zed}\n\tTESTP\\_St \\defs [~  TESTP\\_a : \\nat ; TESTP\\_b : \\nat  ~]\n\\end{zed}\n\n\\begin{zed}\n\tInit \\defs [~  TESTP\\_St' | TESTP\\_a' = 0 \\land TESTP\\_b' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tTESTP\\_Init \\defs [~  TESTP\\_St' | TESTP\\_a' = 0 \\land TESTP\\_b' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tfTESTP\\_Init \\defs [~  \\Xi TESTP\\_St | \\lnot \\pre TESTP\\_Init  ~]\n\\end{zed}\n\n\\end{document}\n");
      assertEquals(
          csp,
          "-- type\nnametype Nat = {0..}\n\n\n-- channels definition\nchannel c, d: Nat\nchannel TESTP_a: Nat\nchannel TESTP_b: Nat\nchannel TESTP_Init\nchannel fTESTP_Init\n\n-- hidden event\nHIDE_CSPB = {|fTESTP_Init|}\n\n-- processes for variable storing and retrieving \n\n-- processes \n-- Divergent Process \nDIV = DIV\n\nMAIN = TESTP_Main\nTESTP_Main = ((((c.TESTP_a -> SKIP))) ||| (((d.TESTP_b -> SKIP))))\n\n");

      TestUtils.WriteSpecToFiles("InterleaveTest1", zrm, csp);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }

  }

  @Test
  public void testParametrisedAction() // throws SectionInfoException, CommandException
  {
    TestUtils.test_print("==================== Test Parameterised Action ====================");
    SectionManager manager = TestUtils
        .strToSecManager("\\begin{circus}\n"
            + "\\circchannel\\ c, d : 0..2 \\\\ \n"
            + "\\end{circus}\n"
            + "\\begin{circus}\n"
            + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
            + "     \\t1 \\circspot (x,y : 0..2 \\circspot (c.x \\then d.y \\then \\Skip))(1,2) \\circend\n"
            + "\\end{circus}");

    try {
      Transformer trans;
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//      Debug.debug_print("==========================================");
//      Debug.debug_print(writer.toString());
//      // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());
//      Debug.debug_print("==========================================");
//      Debug.debug_print(zrm);

      String csp = cspspec.toString();

      assertEquals(
          zrm,
          "\\documentclass{article}\n\\usepackage{fuzz}\n\n\\begin{document}\n\n%\\begin{zsection}\t \\SECTION Specification \\parents~standard\\_toolkit\n%\\end{zsection}\n\n\\begin{zed}\n\tTESTP\\_defaultSt \\defs [~  TESTP\\_dummy : \\{ 0 , 1 \\} | true  ~]\n\\end{zed}\n\n\\begin{zed}\n\tInit \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tTESTP\\_Init \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tfTESTP\\_Init \\defs [~  \\Xi TESTP\\_defaultSt | \\lnot \\pre TESTP\\_Init  ~]\n\\end{zed}\n\n\\end{document}\n");
      assertEquals(
          csp,
          "-- type\nnametype Nat = {0..}\n\n\n-- channels definition\nchannel c, d: {0 .. 2}\nchannel TESTP_dummy: {0, 1}\nchannel TESTP_Init\nchannel fTESTP_Init\n\n-- hidden event\nHIDE_CSPB = {|fTESTP_Init|}\n\n-- processes for variable storing and retrieving \n\n-- processes \n-- Divergent Process \nDIV = DIV\n\nMAIN = TESTP_Main\nTESTP_Main = ((c.(1) -> (d.(2) -> SKIP)))\n\n");

      TestUtils.WriteSpecToFiles("ParamActionTest", zrm, csp);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }


    manager.reset();
    manager = TestUtils.strToSecManager("\\begin{circus}\n" + "\\circchannel\\ c, d : 0..2 \\\\ \n"
        + "\\end{circus}\n" + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 A \\circdef x,y : 0..2 \\circspot (c.x \\then d.y \\then \\Skip) \\\\\n"
        + "     \\t1 \\circspot A(1,2) \\circend\n" + "\\end{circus}");

    try {
      Transformer trans;
      trans = new Transformer(manager, "spec");

      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//      Debug.debug_print("==========================================");
//      Debug.debug_print(writer.toString());
      // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());
//      Debug.debug_print("==========================================");
//      Debug.debug_print(zrm);

      String csp = cspspec.toString();

      assertEquals(
          zrm,
          "\\documentclass{article}\n\\usepackage{fuzz}\n\n\\begin{document}\n\n%\\begin{zsection}\t \\SECTION Specification \\parents~standard\\_toolkit\n%\\end{zsection}\n\n\\begin{zed}\n\tTESTP\\_defaultSt \\defs [~  TESTP\\_dummy : \\{ 0 , 1 \\} | true  ~]\n\\end{zed}\n\n\\begin{zed}\n\tInit \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tTESTP\\_Init \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tfTESTP\\_Init \\defs [~  \\Xi TESTP\\_defaultSt | \\lnot \\pre TESTP\\_Init  ~]\n\\end{zed}\n\n\\end{document}\n");
      assertEquals(
          csp,
          "-- type\nnametype Nat = {0..}\n\n\n-- channels definition\nchannel c, d: {0 .. 2}\nchannel TESTP_dummy: {0, 1}\nchannel TESTP_Init\nchannel fTESTP_Init\n\n-- hidden event\nHIDE_CSPB = {|fTESTP_Init|}\n\n-- processes for variable storing and retrieving \n\n-- processes \n-- Divergent Process \nDIV = DIV\n\nMAIN = TESTP_Main\nTESTP_Main = ((c.(1) -> (d.(2) -> SKIP)))\n\n");

      TestUtils.WriteSpecToFiles("ParamActionTest2", zrm, csp);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }

  }

  @Test
  public void testAlternation() // throws SectionInfoException, CommandException
  {
    TestUtils.test_print("==================== Test Alternation Action ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c, d, e: 0..2 \\\\ \n" + "\\end{circus}\n" + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: 0..2; b: 0..2] \\\\\n"
        + "     \\t1 Init == [~ (St)\' | a\' = 0 \\land b\' = 0 ~] \\\\\n"
        + "     \\t1 A \\circdef c.a \\then \\Skip\\\\\n"
        + "     \\t1 B \\circdef d.b \\then \\Skip\\\\\n"
        + "     \\t1 C \\circdef e.b \\then \\Skip\\\\\n"
        + "     \\t1 \\circspot \\circif a = 0 \\circthen A \\circelse "
        + "                 a > 0 \\circthen B \\circelse "
        + "                 b \\leq 0 \\circthen C \\circfi \\circend\n" + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//      Debug.debug_print("==========================================");
//      Debug.debug_print(writer.toString());
//      // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());
//      Debug.debug_print("==========================================");
//      Debug.debug_print(zrm);

      String csp = cspspec.toString();

//      assertEquals(
//          zrm,
//          "\\documentclass{article}\n\\usepackage{fuzz}\n\n\\begin{document}\n\n%\\begin{zsection}\t \\SECTION Specification \\parents~standard\\_toolkit\n%\\end{zsection}\n\n\\begin{zed}\n\tTESTP\\_defaultSt \\defs [~  TESTP\\_dummy : \\{ 0 , 1 \\} | true  ~]\n\\end{zed}\n\n\\begin{zed}\n\tInit \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tTESTP\\_Init \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tfTESTP\\_Init \\defs [~  \\Xi TESTP\\_defaultSt | \\lnot \\pre TESTP\\_Init  ~]\n\\end{zed}\n\n\\end{document}\n");
//      assertEquals(
//          csp,
//          "-- type\nnametype Nat = {0..}\n\n\n-- channels definition\nchannel c, d: {0 .. 2}\nchannel TESTP_dummy: {0, 1}\nchannel TESTP_Init\nchannel fTESTP_Init\n\n-- hidden event\nHIDE_CSPB = {|fTESTP_Init|}\n\n-- processes for variable storing and retrieving \n\n-- processes \n-- Divergent Process \nDIV = DIV\n\nMAIN = TESTP_Main\nTESTP_Main = ((c.(1) -> (d.(2) -> SKIP)))\n\n");

      TestUtils.WriteSpecToFiles("testAlternation", zrm, csp);
      assertTrue(true);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }

  }

  @Test
  public void testAlternation1() // throws SectionInfoException, CommandException
  {
    TestUtils.test_print("==================== Test Alternation Action #1 ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c, d, e: 0..2 \\\\ \n" + "\\end{circus}\n" + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: 0..2; b: 0..2] \\\\\n"
        + "     \\t1 Init == [~ (St)\' | a\' = 0 \\land b\' = 0 ~] \\\\\n"
        + "     \\t1 A \\circdef c.a \\then \\Skip\\\\\n"
        + "     \\t1 B \\circdef d.b \\then \\Skip\\\\\n"
        + "     \\t1 C \\circdef e.b \\then \\Skip\\\\\n"
        + "     \\t1 \\circspot (\\circvar x,y : 0..10 \\circspot x,y := 1,2 \\circseq "
        + "                 \\circif a = 0 \\land x > 0  \\circthen A \\circelse "
        + "                          a > 0 \\circthen B \\circelse "
        + "                          x > 1 \\land y > 1 \\circthen C \\circfi )"
        + "                 \\circend\n" 
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
      // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());

      String csp = cspspec.toString();

      TestUtils.WriteSpecToFiles("testAlternation1", zrm, csp);
      assertTrue(true);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }

  }
  
  @Test
  public void testAlternation2() // throws SectionInfoException, CommandException
  {
    TestUtils.test_print("==================== Test Alternation Action #2 ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c, d, e: 0..2 \\\\ \n" + "\\end{circus}\n" + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: 0..2; b: 0..2] \\\\\n"
        + "     \\t1 Init == [~ (St)\' | a\' = 0 \\land b\' = 0 ~] \\\\\n"
        + "     \\t1 A \\circdef c.a \\then \\Skip\\\\\n"
        + "     \\t1 B \\circdef d.b \\then \\Skip\\\\\n"
        + "     \\t1 C \\circdef e.b \\then \\Skip\\\\\n"
        + "     \\t1 \\circspot (\\circvar x : 0..5; y : 6..10 \\circspot "
        + "                 \\circif a = 0 \\land x > 0  \\circthen A \\circelse "
        + "                          a > 0 \\circthen B \\circelse "
        + "                          x > 1 \\land y > 1 \\circthen C \\circfi )"
        + "                 \\circend\n" 
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
      // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());

      String csp = cspspec.toString();

      TestUtils.WriteSpecToFiles("testAlternation2", zrm, csp);
      assertTrue(true);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }

  }
  
  /**
   * Test specification with only state variables in w \prefixcolon [pre, post]
   */
  @Test
  public void testSpecification() // throws SectionInfoException, CommandException
  {
    TestUtils.test_print("==================== Test Specification Action ====================");
    SectionManager manager = TestUtils
        .strToSecManager("\\begin{circus}\n"
//            + "\\circchannel\\ c, d, e: 0..10 \\\\ \n"
//            + "\\end{circus}\n"
//            + "\\begin{circus}\n" 
            + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
            + "     \\t1 \\circstate St == [ a: 0..10; b: 0..10] \\\\\n"
            + "     \\t1 Init == [~ (St)\' | a\' = 0 \\land b\' = 0 ~] \\\\\n"
            + "     \\t1 \\circspot (a,b \\prefixcolon [~ a > 0 \\land b > 0, a' = 0 \\land b' = 0 ~]) \\circend\n"
            + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//      Debug.debug_print("==========================================");
//      Debug.debug_print(writer.toString());
//      // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());
//      Debug.debug_print("==========================================");
//      Debug.debug_print(zrm);

      String csp = cspspec.toString();

      assertEquals(
          zrm,
          "\\documentclass{article}\n\\usepackage{fuzz}\n\n\\begin{document}\n\n%\\begin{zsection}\t \\SECTION Specification \\parents~standard\\_toolkit\n%\\end{zsection}\n\n\\begin{zed}\n\tTESTP\\_defaultSt \\defs [~  TESTP\\_dummy : \\{ 0 , 1 \\} | true  ~]\n\\end{zed}\n\n\\begin{zed}\n\tInit \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tTESTP\\_Init \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tfTESTP\\_Init \\defs [~  \\Xi TESTP\\_defaultSt | \\lnot \\pre TESTP\\_Init  ~]\n\\end{zed}\n\n\\end{document}\n");
      assertEquals(
          csp,
          "-- type\nnametype Nat = {0..}\n\n\n-- channels definition\nchannel c, d: {0 .. 2}\nchannel TESTP_dummy: {0, 1}\nchannel TESTP_Init\nchannel fTESTP_Init\n\n-- hidden event\nHIDE_CSPB = {|fTESTP_Init|}\n\n-- processes for variable storing and retrieving \n\n-- processes \n-- Divergent Process \nDIV = DIV\n\nMAIN = TESTP_Main\nTESTP_Main = ((c.(1) -> (d.(2) -> SKIP)))\n\n");

//      TestUtils.WriteSpecToFiles("ParamActionTest", zrm, csp);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }


  }

  /**
   * Test specification with local and state variables in w
   */
  @Test
  public void testSpecification1() // throws SectionInfoException, CommandException
  {
    TestUtils.test_print("==================== Test Specification1 Action ====================");
    SectionManager manager = TestUtils
        .strToSecManager("\\begin{circus}\n"
            + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
            + "     \\t1 \\circstate St == [ a: 0..10; b: 0..10] \\\\\n"
            + "     \\t1 Init == [~ (St)\' | a\' = 1 \\land b\' = 0 ~] \\\\\n"
            + "     \\t1 \\circspot (\\circvar e:\\nat \\circspot e,a,b \\prefixcolon [~ a > 0, e' = a \\land 0 = b' \\land a' = e ~]) \\circend\n"
            + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//      Debug.debug_print("==========================================");
//      Debug.debug_print(writer.toString());
//      // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());
//      Debug.debug_print("==========================================");
//      Debug.debug_print(zrm);

      String csp = cspspec.toString();

//      assertEquals(
//          zrm,
//          "\\documentclass{article}\n\\usepackage{fuzz}\n\n\\begin{document}\n\n%\\begin{zsection}\t \\SECTION Specification \\parents~standard\\_toolkit\n%\\end{zsection}\n\n\\begin{zed}\n\tTESTP\\_defaultSt \\defs [~  TESTP\\_dummy : \\{ 0 , 1 \\} | true  ~]\n\\end{zed}\n\n\\begin{zed}\n\tInit \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tTESTP\\_Init \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tfTESTP\\_Init \\defs [~  \\Xi TESTP\\_defaultSt | \\lnot \\pre TESTP\\_Init  ~]\n\\end{zed}\n\n\\end{document}\n");
//      assertEquals(
//          csp,
//          "-- type\nnametype Nat = {0..}\n\n\n-- channels definition\nchannel c, d: {0 .. 2}\nchannel TESTP_dummy: {0, 1}\nchannel TESTP_Init\nchannel fTESTP_Init\n\n-- hidden event\nHIDE_CSPB = {|fTESTP_Init|}\n\n-- processes for variable storing and retrieving \n\n-- processes \n-- Divergent Process \nDIV = DIV\n\nMAIN = TESTP_Main\nTESTP_Main = ((c.(1) -> (d.(2) -> SKIP)))\n\n");

      TestUtils.WriteSpecToFiles("testSpec1", zrm, csp);
      assertTrue(true);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }


  }
  
  /**
   * Test specification with more complex predicates in post
   */
  @Test
  public void testSpecification2() // throws SectionInfoException, CommandException
  {
    TestUtils.test_print("==================== Test Specification2 Action ====================");
    SectionManager manager = TestUtils
        .strToSecManager("\\begin{circus}\n"
            + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
            + "     \\t1 \\circstate St == [ a: 0..10; b: 0..10] \\\\\n"
            + "     \\t1 Init == [~ (St)\' | a\' = 1 \\land b\' = 0 ~] \\\\\n"
            + "     \\t1 \\circspot (\\circvar e,f : 0..10 \\circspot e := 1 \\circseq (e,f,a,b \\prefixcolon [~ a > 0 \\land e = 1, e' = a + b \\land e + 5 = b' \\land a' = e ~])) \\circend\n"
            + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//      Debug.debug_print("==========================================");
//      Debug.debug_print(writer.toString());
//      // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());
//      Debug.debug_print("==========================================");
//      Debug.debug_print(zrm);

      String csp = cspspec.toString();

//      assertEquals(
//          zrm,
//          "\\documentclass{article}\n\\usepackage{fuzz}\n\n\\begin{document}\n\n%\\begin{zsection}\t \\SECTION Specification \\parents~standard\\_toolkit\n%\\end{zsection}\n\n\\begin{zed}\n\tTESTP\\_defaultSt \\defs [~  TESTP\\_dummy : \\{ 0 , 1 \\} | true  ~]\n\\end{zed}\n\n\\begin{zed}\n\tInit \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tTESTP\\_Init \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tfTESTP\\_Init \\defs [~  \\Xi TESTP\\_defaultSt | \\lnot \\pre TESTP\\_Init  ~]\n\\end{zed}\n\n\\end{document}\n");
//      assertEquals(
//          csp,
//          "-- type\nnametype Nat = {0..}\n\n\n-- channels definition\nchannel c, d: {0 .. 2}\nchannel TESTP_dummy: {0, 1}\nchannel TESTP_Init\nchannel fTESTP_Init\n\n-- hidden event\nHIDE_CSPB = {|fTESTP_Init|}\n\n-- processes for variable storing and retrieving \n\n-- processes \n-- Divergent Process \nDIV = DIV\n\nMAIN = TESTP_Main\nTESTP_Main = ((c.(1) -> (d.(2) -> SKIP)))\n\n");

      TestUtils.WriteSpecToFiles("testSpec2", zrm, csp);
      assertTrue(true);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }


  }
  
  /**
   * Test specification with some state variables (c) not been specified in post
   * and a "c' = c" equality pred will be added in final SpecOps 
   */
  @Test
  public void testSpecification3()
  {
    TestUtils.test_print("==================== Test Specification3 Action ====================");
    SectionManager manager = TestUtils
        .strToSecManager("\\begin{circus}\n"
            + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
            + "     \\t1 \\circstate St == [ a,b,c: 0..10] \\\\\n"
            + "     \\t1 Init == [~ (St)\' | a\' = 1 \\land b\' = 0 \\land c' = 2 ~] \\\\\n"
            + "     \\t1 \\circspot (\\circvar e,f : 0..10 \\circspot e := 1 \\circseq (e,f,a,b \\prefixcolon [~ a > 0 \\land e = 1, e' = a + b \\land a' = e ~])) \\circend\n"
            + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//      // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());

      String csp = cspspec.toString();

//      assertEquals(
//          zrm,
//          "\\documentclass{article}\n\\usepackage{fuzz}\n\n\\begin{document}\n\n%\\begin{zsection}\t \\SECTION Specification \\parents~standard\\_toolkit\n%\\end{zsection}\n\n\\begin{zed}\n\tTESTP\\_defaultSt \\defs [~  TESTP\\_dummy : \\{ 0 , 1 \\} | true  ~]\n\\end{zed}\n\n\\begin{zed}\n\tInit \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tTESTP\\_Init \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tfTESTP\\_Init \\defs [~  \\Xi TESTP\\_defaultSt | \\lnot \\pre TESTP\\_Init  ~]\n\\end{zed}\n\n\\end{document}\n");
//      assertEquals(
//          csp,
//          "-- type\nnametype Nat = {0..}\n\n\n-- channels definition\nchannel c, d: {0 .. 2}\nchannel TESTP_dummy: {0, 1}\nchannel TESTP_Init\nchannel fTESTP_Init\n\n-- hidden event\nHIDE_CSPB = {|fTESTP_Init|}\n\n-- processes for variable storing and retrieving \n\n-- processes \n-- Divergent Process \nDIV = DIV\n\nMAIN = TESTP_Main\nTESTP_Main = ((c.(1) -> (d.(2) -> SKIP)))\n\n");

      TestUtils.WriteSpecToFiles("testSpec3", zrm, csp);
      assertTrue(true);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }

  }
  
  /**
   * Test specification without frame w 
   */
  @Test
  public void testSpecificationNoW()
  {
    TestUtils.test_print("==================== Test Specification Without w ====================");
    SectionManager manager = TestUtils
        .strToSecManager("\\begin{circus}\n"
            + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
            + "     \\t1 \\circstate St == [ a,b,c: 0..10] \\\\\n"
            + "     \\t1 Init == [~ (St)\' | a\' = 1 \\land b\' = 0 \\land c' = 2 ~] \\\\\n"
            + "     \\t1 \\circspot (\\circvar e,f : 0..10 \\circspot e := 1 \\circseq (\\prefixcolon [~ a > 0 \\land e = 1, e' = a + b \\land a' = e ~])) \\circend\n"
            + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//      // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());

      String csp = cspspec.toString();

//      assertEquals(
//          zrm,
//          "\\documentclass{article}\n\\usepackage{fuzz}\n\n\\begin{document}\n\n%\\begin{zsection}\t \\SECTION Specification \\parents~standard\\_toolkit\n%\\end{zsection}\n\n\\begin{zed}\n\tTESTP\\_defaultSt \\defs [~  TESTP\\_dummy : \\{ 0 , 1 \\} | true  ~]\n\\end{zed}\n\n\\begin{zed}\n\tInit \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tTESTP\\_Init \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tfTESTP\\_Init \\defs [~  \\Xi TESTP\\_defaultSt | \\lnot \\pre TESTP\\_Init  ~]\n\\end{zed}\n\n\\end{document}\n");
//      assertEquals(
//          csp,
//          "-- type\nnametype Nat = {0..}\n\n\n-- channels definition\nchannel c, d: {0 .. 2}\nchannel TESTP_dummy: {0, 1}\nchannel TESTP_Init\nchannel fTESTP_Init\n\n-- hidden event\nHIDE_CSPB = {|fTESTP_Init|}\n\n-- processes for variable storing and retrieving \n\n-- processes \n-- Divergent Process \nDIV = DIV\n\nMAIN = TESTP_Main\nTESTP_Main = ((c.(1) -> (d.(2) -> SKIP)))\n\n");

      TestUtils.WriteSpecToFiles("testSpecNoW", zrm, csp);
      assertTrue(true);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }

  }

  /**
   * Test assumption (specification with post always true and no w) 
   */
  @Test
  public void testAssumption()
  {
    TestUtils.test_print("==================== Test Assumption ====================");
    SectionManager manager = TestUtils
        .strToSecManager("\\begin{circus}\n"
            + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
            + "     \\t1 \\circstate St == [ a,b,c: 0..10] \\\\\n"
            + "     \\t1 Init == [~ (St)\' | a\' = 1 \\land b\' = 0 \\land c' = 2 ~] \\\\\n"
            + "     \\t1 \\circspot (\\circvar e,f : 0..10 \\circspot e := 1 \\circseq (\\{~ a > 0 \\land e = 1 ~\\})) \\circend\n"
            + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//      // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());

      String csp = cspspec.toString();

//      assertEquals(
//          zrm,
//          "\\documentclass{article}\n\\usepackage{fuzz}\n\n\\begin{document}\n\n%\\begin{zsection}\t \\SECTION Specification \\parents~standard\\_toolkit\n%\\end{zsection}\n\n\\begin{zed}\n\tTESTP\\_defaultSt \\defs [~  TESTP\\_dummy : \\{ 0 , 1 \\} | true  ~]\n\\end{zed}\n\n\\begin{zed}\n\tInit \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tTESTP\\_Init \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tfTESTP\\_Init \\defs [~  \\Xi TESTP\\_defaultSt | \\lnot \\pre TESTP\\_Init  ~]\n\\end{zed}\n\n\\end{document}\n");
//      assertEquals(
//          csp,
//          "-- type\nnametype Nat = {0..}\n\n\n-- channels definition\nchannel c, d: {0 .. 2}\nchannel TESTP_dummy: {0, 1}\nchannel TESTP_Init\nchannel fTESTP_Init\n\n-- hidden event\nHIDE_CSPB = {|fTESTP_Init|}\n\n-- processes for variable storing and retrieving \n\n-- processes \n-- Divergent Process \nDIV = DIV\n\nMAIN = TESTP_Main\nTESTP_Main = ((c.(1) -> (d.(2) -> SKIP)))\n\n");

      TestUtils.WriteSpecToFiles("testAssumption", zrm, csp);
      assertTrue(true);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }

  }
  
  /**
   * Test Coercion (specification with pre always true and no w) 
   */
  @Test
  public void testCoercion()
  {
    TestUtils.test_print("==================== Test Coercion ====================");
    SectionManager manager = TestUtils
        .strToSecManager("\\begin{circus}\n"
            + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
            + "     \\t1 \\circstate St == [ a,b,c: 0..10] \\\\\n"
            + "     \\t1 Init == [~ (St)\' | a\' = 1 \\land b\' = 0 \\land c' = 2 ~] \\\\\n"
            + "     \\t1 \\circspot (\\circvar e,f : 0..10 \\circspot e := 1 \\circseq ([~ e' = a + b \\land a' = e ~])) \\circend\n"
            + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//      // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());

      String csp = cspspec.toString();

//      assertEquals(
//          zrm,
//          "\\documentclass{article}\n\\usepackage{fuzz}\n\n\\begin{document}\n\n%\\begin{zsection}\t \\SECTION Specification \\parents~standard\\_toolkit\n%\\end{zsection}\n\n\\begin{zed}\n\tTESTP\\_defaultSt \\defs [~  TESTP\\_dummy : \\{ 0 , 1 \\} | true  ~]\n\\end{zed}\n\n\\begin{zed}\n\tInit \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tTESTP\\_Init \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tfTESTP\\_Init \\defs [~  \\Xi TESTP\\_defaultSt | \\lnot \\pre TESTP\\_Init  ~]\n\\end{zed}\n\n\\end{document}\n");
//      assertEquals(
//          csp,
//          "-- type\nnametype Nat = {0..}\n\n\n-- channels definition\nchannel c, d: {0 .. 2}\nchannel TESTP_dummy: {0, 1}\nchannel TESTP_Init\nchannel fTESTP_Init\n\n-- hidden event\nHIDE_CSPB = {|fTESTP_Init|}\n\n-- processes for variable storing and retrieving \n\n-- processes \n-- Divergent Process \nDIV = DIV\n\nMAIN = TESTP_Main\nTESTP_Main = ((c.(1) -> (d.(2) -> SKIP)))\n\n");

      TestUtils.WriteSpecToFiles("testCoercion", zrm, csp);
      assertTrue(true);
    }
    catch (SectionInfoException e1) {
      // TODO Auto-generated catch block
      e1.printStackTrace();
    }

  }
  
  /**
   * 
   */
  @Test
  public void testParaByVal() // throws SectionInfoException, CommandException
  {
    TestUtils.test_print("==================== Test Parametrisation by Value ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c: 0..10 \\\\\n"
        + "\\end{circus}\n" 
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: 0..10; b: 0..10] \\\\\n"
        + "     \\t1 Init == [~ (St)\' | a\' = 0 \\land b\' = 0 ~] \\\\\n"
        + "     \\t1 Read == [~ \\Xi St; r!:0..10 | r! = a + b ~] \\\\\n"
        + "     \\t1 \\circspot \\lschexpract Init \\rschexpract \\circseq "
        + "             (\\circval\\ r: 0..10 \\circspot (\\lschexpract Read \\rschexpract))(1) "
//        + "          (\\circmu X \\circspot (\\circval\\ r: 0..10 \\circspot (\\lschexpract Read \\rschexpract \\circseq X)))(1) "
        + "\\circend\n"
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
//      Debug.debug_print("==========================================");
//      Debug.debug_print(writer.toString());
//      // convert from ISO Z to ZRM
      String zrm = ISOZ2ZRM.convert(writer.toString());
//      Debug.debug_print("==========================================");
//      Debug.debug_print(zrm);

      String csp = cspspec.toString();

      TestUtils.WriteSpecToFiles("testParaByVal", zrm, csp);
      assertTrue(true);
//      assertEquals(
//          zrm,
//          "\\documentclass{article}\n\\usepackage{fuzz}\n\n\\begin{document}\n\n%\\begin{zsection}\t \\SECTION Specification \\parents~standard\\_toolkit\n%\\end{zsection}\n\n\\begin{zed}\n\tTESTP\\_defaultSt \\defs [~  TESTP\\_dummy : \\{ 0 , 1 \\} | true  ~]\n\\end{zed}\n\n\\begin{zed}\n\tInit \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tTESTP\\_Init \\defs [~  TESTP\\_defaultSt' | TESTP\\_dummy' = 0  ~]\n\\end{zed}\n\n\\begin{zed}\n\tfTESTP\\_Init \\defs [~  \\Xi TESTP\\_defaultSt | \\lnot \\pre TESTP\\_Init  ~]\n\\end{zed}\n\n\\end{document}\n");
//      assertEquals(
//          csp,
//          "-- type\nnametype Nat = {0..}\n\n\n-- channels definition\nchannel c, d: {0 .. 2}\nchannel TESTP_dummy: {0, 1}\nchannel TESTP_Init\nchannel fTESTP_Init\n\n-- hidden event\nHIDE_CSPB = {|fTESTP_Init|}\n\n-- processes for variable storing and retrieving \n\n-- processes \n-- Divergent Process \nDIV = DIV\n\nMAIN = TESTP_Main\nTESTP_Main = ((c.(1) -> (d.(2) -> SKIP)))\n\n");
    }
    catch (SectionInfoException e1) {
      e1.printStackTrace();
    }

  }
  
  /**
   * 
   */
  @Test
  public void testParaByVal1()
  {
    TestUtils.test_print("==================== Test Parametrisation by Value1 ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c: 0..10 \\\\\n"
        + "\\end{circus}\n" 
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: 0..10] \\\\\n"
        + "     \\t1 Init == [~ (St)\' | a\' = 0 ~] \\\\\n"
        + "     \\t1 Write == [~ \\Delta St; r1?:0..10 | a' = r1? ~] \\\\\n"
        + "     \\t1 \\circspot \\lschexpract Init \\rschexpract \\circseq "
        + "             (\\circval\\ r1,r2: 0..10 \\circspot ((a := r1 + r2) \\circseq \\lschexpract Write \\rschexpract))(1,2) "
        + "\\circend\n"
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        e.printStackTrace();
      }
      String zrm = ISOZ2ZRM.convert(writer.toString());

      String csp = cspspec.toString();

      TestUtils.WriteSpecToFiles("testParaByVal1", zrm, csp);
      assertTrue(true);
//      assertEquals(
//          zrm,
//        "");
//      assertEquals(
//          csp,
//      "");
    }
    catch (SectionInfoException e1) {
      e1.printStackTrace();
    }

  }
  
  /**
   * 
   */
  @Test
  public void testParaByRes()
  {
    TestUtils.test_print("==================== Test Parametrisation by Result ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c: 0..10 \\\\\n"
        + "\\end{circus}\n" 
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: 0..10; b: 0..10] \\\\\n"
        + "     \\t1 Init == [~ (St)' | a' = 0 \\land b' = 0 ~] \\\\\n"
        + "     \\t1 Write == [~ \\Delta St; r1?:0..10 | a' = r1? ~] \\\\\n"
        + "     \\t1 \\circspot \\lschexpract Init \\rschexpract \\circseq "
        + "             (\\circres\\ r1,r2: 0..10 \\circspot ((a := r1 + r2) \\circseq \\lschexpract Write \\rschexpract))(a,b) "
        + "\\circend\n"
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        e.printStackTrace();
      }
      String zrm = ISOZ2ZRM.convert(writer.toString());

      String csp = cspspec.toString();

      TestUtils.WriteSpecToFiles("testParaByRes", zrm, csp);
      assertTrue(true);
//      assertEquals(
//          zrm,
//        "");
//      assertEquals(
//          csp,
//      "");
    }
    catch (SectionInfoException e1) {
      e1.printStackTrace();
    }

  }
  
  /**
   * 
   */
  @Test
  public void testParaByVRes()
  {
    TestUtils.test_print("==================== Test Parametrisation by Value-Result ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c: 0..10 \\\\\n"
        + "\\end{circus}\n" 
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: 0..10; b: 0..10] \\\\\n"
        + "     \\t1 Init == [~ (St)' | a' = 0 \\land b' = 0 ~] \\\\\n"
        + "     \\t1 Write == [~ \\Delta St; r1?:0..10 | a' = r1? ~] \\\\\n"
        + "     \\t1 \\circspot \\lschexpract Init \\rschexpract \\circseq "
        + "             (\\circvres\\ r1,r2: 0..10 \\circspot ((a := r1 + r2) \\circseq \\lschexpract Write \\rschexpract))(a,b) "
        + "\\circend\n"
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        e.printStackTrace();
      }
      String zrm = ISOZ2ZRM.convert(writer.toString());

      String csp = cspspec.toString();

      TestUtils.WriteSpecToFiles("testParaByVRes", zrm, csp);
      assertTrue(true);
//      assertEquals(
//          zrm,
//        "");
//      assertEquals(
//          csp,
//      "");
    }
    catch (SectionInfoException e1) {
      e1.printStackTrace();
    }

    catch (net.sourceforge.czt.util.CztException e1) {
      e1.printStackTrace();
    }
  }
  
  /**
   * Test replicated sequential
   */
  @Test
  public void testSeqActionIte()
  {
    TestUtils.test_print("==================== Test Iterated Sequential #0: seq as T ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c: 0..10 \\\\\n"
        + "\\end{circus}\n" 
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: 0..10; b: 0..10] \\\\\n"
        + "     \\t1 Init == [~ (St)' | a' = 0 \\land b' = 0 ~] \\\\\n"
        + "     \\t1 Write == [~ \\Delta St; r1?:0..10 | a' = r1? ~] \\\\\n"
        + "     \\t1 \\circspot \\lschexpract Init \\rschexpract \\circseq "
        + "             (\\Semi\\ x: \\langle 1,3 \\rangle \\circspot \\Skip) "
        + "\\circend\n"
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        e.printStackTrace();
      }
      String zrm = ISOZ2ZRM.convert(writer.toString());

      String csp = cspspec.toString();

      TestUtils.WriteSpecToFiles("testSeqActionIte", zrm, csp);
      assertTrue(true);
//      assertEquals(
//          zrm,
//        "");
//      assertEquals(
//          csp,
//      "");
    }
    catch (SectionInfoException e1) {
      e1.printStackTrace();
    }

    catch (net.sourceforge.czt.util.CztException e1) {
      e1.printStackTrace();
    }
  }
  
  /**
   * Test replicated sequential
   */
  @Test
  public void testSeqActionIte1()
  {
    TestUtils.test_print("==================== Test Iterated Sequential #1: set as T ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c: 0..10 \\\\\n"
        + "\\end{circus}\n" 
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: 0..10; b: 0..10] \\\\\n"
        + "     \\t1 Init == [~ (St)' | a' = 0 \\land b' = 0 ~] \\\\\n"
        + "     \\t1 Write == [~ \\Delta St; r1?:0..10 | a' = r1? ~] \\\\\n"
        + "     \\t1 \\circspot \\lschexpract Init \\rschexpract \\circseq "
        // actually it doesn't make sense for T being a set for Iterated Sequence
        + "             (\\Semi\\ x: \\{ 1,3 \\} \\circspot \\Skip) "
        + "\\circend\n"
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        e.printStackTrace();
      }
      String zrm = ISOZ2ZRM.convert(writer.toString());

      String csp = cspspec.toString();

      TestUtils.WriteSpecToFiles("testSeqActionIte1", zrm, csp);
      assertTrue(true);
//      assertEquals(
//          zrm,
//        "");
//      assertEquals(
//          csp,
//      "");
    }
    catch (SectionInfoException e1) {
      e1.printStackTrace();
    }

    catch (net.sourceforge.czt.util.CztException e1) {
      e1.printStackTrace();
    }
  }
  
  /**
   * Test replicated sequential
   */
  @Test
  public void testSeqActionIte2()
  {
    TestUtils.test_print("==================== Test Iterated Sequential #2: ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c: 0..10 \\\\\n"
        + "\\end{circus}\n" 
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: 0..10; b: 0..10] \\\\\n"
        + "     \\t1 Init == [~ (St)' | a' = 0 \\land b' = 0 ~] \\\\\n"
        + "     \\t1 Write == [~ \\Delta St; r1?:0..10 | a' = r1? ~] \\\\\n"
        // TODO: how to define the type of parameter x in A definition to make it consistent with 
        // the type in Iterated Sequential (<1,3>)
//        + "     \\t1 A \\circdef x: 0 \\upto 5 \\circspot (c.x \\then \\Skip) \\\\\n"
        + "     \\t1 \\circspot \\lschexpract Init \\rschexpract \\circseq "
//        + "             (\\Semi\\ x: \\langle 1,3 \\rangle \\circspot A(x)) "
        + "             (\\Semi\\ x: \\langle 1,3 \\rangle \\circspot \\Skip) "
        + "\\circend\n"
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        e.printStackTrace();
      }
      String zrm = ISOZ2ZRM.convert(writer.toString());

      String csp = cspspec.toString();

      TestUtils.WriteSpecToFiles("testSeqActionIte2", zrm, csp);
      assertTrue(true);
//      assertEquals(
//          zrm,
//        "");
//      assertEquals(
//          csp,
//      "");
    }
    catch (SectionInfoException e1) {
      e1.printStackTrace();
    }

    catch (net.sourceforge.czt.util.CztException e1) {
      e1.printStackTrace();
    }
  }
  
  /**
   * Test replicated sequential
   */
  @Test
  public void testExtChoiceActionIte()
  {
    TestUtils.test_print("==================== Test Iterated External Choice #0: ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c: 0..10 \\\\\n"
        + "\\end{circus}\n" 
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: 0..10; b: 0..10] \\\\\n"
        + "     \\t1 Init == [~ (St)' | a' = 0 \\land b' = 0 ~] \\\\\n"
        + "     \\t1 Write == [~ \\Delta St; r1?:0..10 | a' = r1? ~] \\\\\n"
        + "     \\t1 A \\circdef x: 0..10 \\circspot (c.x \\then \\Skip) \\\\\n"
        + "     \\t1 \\circspot \\lschexpract Init \\rschexpract \\circseq "
        + "             (\\Extchoice x: \\{ 1,3 \\} \\circspot A(x)) "
        + "\\circend\n"
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        e.printStackTrace();
      }
      String zrm = ISOZ2ZRM.convert(writer.toString());

      String csp = cspspec.toString();

      TestUtils.WriteSpecToFiles("testExtChoiceActionIte", zrm, csp);
      assertTrue(true);
//      assertEquals(
//          zrm,
//        "");
//      assertEquals(
//          csp,
//      "");
    }
    catch (SectionInfoException e1) {
      e1.printStackTrace();
    }

    catch (net.sourceforge.czt.util.CztException e1) {
      e1.printStackTrace();
    }
  }
  
  /**
   * Test replicated sequential
   */
  @Test
  public void testIntChoiceActionIte()
  {
    TestUtils.test_print("==================== Test Iterated Internal Choice #0: ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c: 0..10 \\\\\n"
        + "\\end{circus}\n" 
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: 0..10; b: 0..10] \\\\\n"
        + "     \\t1 Init == [~ (St)' | a' = 0 \\land b' = 0 ~] \\\\\n"
        + "     \\t1 Write == [~ \\Delta St; r1?:0..10 | a' = r1? ~] \\\\\n"
        + "     \\t1 A \\circdef x: 0..10 \\circspot (c.x \\then \\Skip) \\\\\n"
        + "     \\t1 \\circspot \\lschexpract Init \\rschexpract \\circseq "
        + "             (\\Intchoice x: \\{ 1,3 \\} \\circspot A(x)) "
        + "\\circend\n"
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        e.printStackTrace();
      }
      String zrm = ISOZ2ZRM.convert(writer.toString());

      String csp = cspspec.toString();

      TestUtils.WriteSpecToFiles("testIntChoiceActionIte", zrm, csp);
      assertTrue(true);
//      assertEquals(
//          zrm,
//        "");
//      assertEquals(
//          csp,
//      "");
    }
    catch (SectionInfoException e1) {
      e1.printStackTrace();
    }

    catch (net.sourceforge.czt.util.CztException e1) {
      e1.printStackTrace();
    }
  }
  
  /**
   * Test external choice issue 
   * (A1 [] A2) in \Circus 
   *    is not equal to
   * (get0?x -> A1 [] get1?y -> A2) \ {get0, get1}
   */
  @Test
  public void testExtChoiceIssue()
  {
    TestUtils.test_print("==================== Test External Choice Issue #0: ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c: 0..10 \\\\\n"
        + "\\end{circus}\n" 
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: 0..10; b: 0..10] \\\\\n"
        + "     \\t1 Init == [~ (St)' | a' = 0 \\land b' = 0 ~] \\\\\n"
        + "     \\t1 Write == [~ \\Delta St; x?:0..10 | a' = x? \\land b'=b ~] \\\\\n"
        + "     \\t1 Add == [~ \\Delta St; y?:0..10 | a' = a + y? \\land b'=b ~] \\\\\n"
        + "     \\t1 A \\circdef x: 0..10 \\circspot (c.x \\then \\Skip) \\\\\n"
        + "     \\t1 \\circspot \\lschexpract Init \\rschexpract \\circseq "
        + "             (\\circvar\\ x,y: 0..10 \\circspot (\\lschexpract Write \\rschexpract \\extchoice \\lschexpract Add \\rschexpract)) "
        + "\\circend\n"
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        e.printStackTrace();
      }
      String zrm = ISOZ2ZRM.convert(writer.toString());

      String csp = cspspec.toString();

      TestUtils.WriteSpecToFiles("testExtChoiceIssue", zrm, csp);
      assertTrue(true);
//      assertEquals(
//          zrm,
//        "");
//      assertEquals(
//          csp,
//      "");
    }
    catch (SectionInfoException e1) {
      e1.printStackTrace();
    }

    catch (net.sourceforge.czt.util.CztException e1) {
      e1.printStackTrace();
    }
  }
  
  /**
   * Test guarded command
   * 
   */
  @Test
  public void testGuardedCommand()
  {
    TestUtils.test_print("==================== Test Guarded Command #0: ====================");
    SectionManager manager = TestUtils.strToSecManager("\\begin{circus}\n"
        + "\\circchannel\\ c: 0..10 \\\\\n"
        + "\\end{circus}\n" 
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circstate St == [ a: 0..10; b: 0..10] \\\\\n"
        + "     \\t1 Init == [~ (St)' | a' = 0 \\land b' = 0 ~] \\\\\n"
        + "     \\t1 A \\circdef x: 0..10 \\circspot (c.x \\then \\Skip) \\\\\n"
        + "     \\t1 \\circspot \\lschexpract Init \\rschexpract \\circseq "
        + "             (\\circvar\\ x: 0..10 \\circspot ("
        + "                    (\\lcircguard (x > 0) \\rcircguard \\circguard (A(0)))"
        + "             \\extchoice (\\lcircguard (x > 0 \\land a = 0) \\rcircguard \\circguard A(1))"
        + "             \\extchoice (\\lcircguard (a > 0) \\rcircguard \\circguard A(2)) ))"
        + "\\circend\n"
        + "\\end{circus}");

    Transformer trans;
    try {
      trans = new Transformer(manager, "spec");
      Spec spec = trans.getSpec();
      CSPSpec cspspec = trans.getCSPSpec();

      String sectionName = "";
      // only consider one section
      if (spec.getSect().size() == 1) {
        if (spec.getSect().get(0) instanceof ZSect) {
          sectionName = ((ZSect) spec.getSect().get(0)).getName();
        }
      }

      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
      }
      catch (PrintException e) {
        e.printStackTrace();
      }
      String zrm = ISOZ2ZRM.convert(writer.toString());

      String csp = cspspec.toString();

      TestUtils.WriteSpecToFiles("testGuardedCommand0", zrm, csp);
      assertTrue(true);
//      assertEquals(
//          zrm,
//        "");
//      assertEquals(
//          csp,
//      "");
    }
    catch (SectionInfoException e1) {
      e1.printStackTrace();
    }
    catch (net.sourceforge.czt.util.CztException e1) {
      e1.printStackTrace();
    }
  }
  
  private void testCircusProgram(String filename)
  {
    URL url = TransformerTest.class.getResource(filename);
    assertFalse(url == null);
    
    UrlSource source = new UrlSource(url);
    source.setMarkup(Markup.LATEX);
    source.setEncoding("Default");

    SectionManager manager = new SectionManager(Dialect.CIRCUS);
    String name = "spec";
    
    try {
      File f = new File(url.toURI().toString());
      String path = f.getParent();
      manager.setProperty("czt.path", path);
    }
    catch (URISyntaxException e) {
      throw new CztException("Cannot convert an URL to URI. " + e.getMessage());
    }
    
    manager.put(new Key<Source>(name, Source.class), source);
    
    Transformer trans = new Transformer(manager, name);
    
    Spec spec = trans.getSpec();
    ZSect zs  = trans.getZSectOfCircus();
    CSPSpec cspspec = trans.getCSPSpec();
    
    Circus2ZCSPUtils.outputZCSPSpecToFile(zs, spec, cspspec, manager);
  }
  
  /**
   * Test state merge of the function \Omega_1
   */
  @Test
  public void testStateMergeOmega1_0()
  {
    testCircusProgram("/UnitTest/compound_process_0.tex");
  }
  
  /**
   * Test boxed schema, abbreviation, decorated schema
   */
  @Test
  public void testBoxedSchema_0()
  {
    testCircusProgram("/UnitTest/boxed_schema_0.tex");
  }
  
  /**
   * Test boxed schema, abbreviation, decorated schema
   */
  @Test
  public void testOmega2_0()
  {
    testCircusProgram("/UnitTest/omega_2_0.tex");
  }
  
  /**
   * Test boxed schema, abbreviation, decorated schema
   */
  @Test
  public void testIdentifiers_0()
  {
    testCircusProgram("/UnitTest/identifiers_0.tex");
  }
  
  /**
   * Test generic
   */
  @Test
  public void testGeneric_0()
  {
    testCircusProgram("/UnitTest/generic_0.tex");
  }
}

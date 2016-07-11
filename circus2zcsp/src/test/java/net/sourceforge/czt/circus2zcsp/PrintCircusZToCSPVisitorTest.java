
package net.sourceforge.czt.circus2zcsp;

import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circus2zcsp.ast.CSPSpec;
import net.sourceforge.czt.circus2zcsp.data.CircusSpecMap;
import net.sourceforge.czt.circus2zcsp.util.TestUtils;
import net.sourceforge.czt.circus2zcsp.visitor.PrintCircusZToCSPVisitor;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.NumStroke;
import net.sourceforge.czt.z.ast.OutStroke;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.ZName;

import org.junit.Test;

public class PrintCircusZToCSPVisitorTest extends TestCase
{
  private ZFactory zfac_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();

  private PrintCircusZToCSPVisitor aptv_ = new PrintCircusZToCSPVisitor();

  public PrintCircusZToCSPVisitorTest()
  {

  }

  /**
   * test ZName visit
   */
  @Test
  public void testZName()
  {
    // name only
    ZName zn = zfac_.createZName("zname", zfac_.createZStrokeList(), null);
    aptv_.clear();
    zn.accept(aptv_);
    String strname = aptv_.toString();
    Debug.debug_print("testZName[1]: " + strname);
    assertEquals(strname, "zname");

    // name and input stroke
    List<net.sourceforge.czt.z.ast.Stroke> lstroke = new ArrayList<net.sourceforge.czt.z.ast.Stroke>();
    InStroke instr = zfac_.createInStroke();
    lstroke.add(instr);
    net.sourceforge.czt.z.ast.StrokeList sl = zfac_.createZStrokeList(lstroke);
    ZName zn_in = zfac_.createZName("zname", sl, null);
    aptv_.clear();
    zn_in.accept(aptv_);
    strname = aptv_.toString();
    Debug.debug_print("testZName[2]: " + strname);
    assertEquals(strname, "zname?");

    // name, in and out strokes
    OutStroke outstr = zfac_.createOutStroke();
    lstroke.add(outstr);
    net.sourceforge.czt.z.ast.StrokeList sl2 = zfac_.createZStrokeList(lstroke);
    ZName zn_in_out = zfac_.createZName("zname", sl2, null);
    aptv_.clear();
    zn_in_out.accept(aptv_);
    strname = aptv_.toString();
    Debug.debug_print("testZName[3]: " + strname);
    assertEquals(strname, "zname?!");

    // name, in, out and next strokes
    NextStroke nextstr = zfac_.createNextStroke();
    lstroke.add(nextstr);
    net.sourceforge.czt.z.ast.StrokeList sl3 = zfac_.createZStrokeList(lstroke);
    ZName zn_in_out_next = zfac_.createZName("zname", sl3, null);
    aptv_.clear();
    zn_in_out_next.accept(aptv_);
    strname = aptv_.toString();
    Debug.debug_print("testZName[4]: " + strname);
    assertEquals(strname, "zname?!′");

    // name, in, out and next strokes
    NumStroke numstr = zfac_.createNumStroke(net.sourceforge.czt.base.ast.Digit.EIGHT);
    lstroke.add(numstr);
    net.sourceforge.czt.z.ast.StrokeList sl4 = zfac_.createZStrokeList(lstroke);
    ZName zn_in_out_next_num = zfac_.createZName("zname", sl4, null);
    aptv_.clear();
    zn_in_out_next_num.accept(aptv_);
    strname = aptv_.toString();
    Debug.debug_print("testZName[5]: " + strname);
    assertEquals(strname, "zname?!′↘8↖");
  }

  @Test
  public void testOrPred()
  {
  }

  @Test
  public void testAbbrPara()
  {
    List<Term> lt = TestUtils.strToTerm("\\begin{zed}\n REG == 0..5 \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      term.accept(aptv_);
    }
    String str = aptv_.toString();
    assertEquals(str, "nametype REG = {0 .. 5}");
  }

  @Test
  public void testMemPred()
  {
    // test membership
    List<Term> lt = TestUtils.strToTerm("\\begin{zed}\n " + "NREG == \\{~ x: \\num | x \\in \\nat ~\\}"
        + " \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "nametype NREG = {x | x <- Int, member(x, Nat)}");

    // test binary operator application, such as x < 256
    lt = TestUtils.strToTerm("\\begin{zed}\n " + "NREG == \\{~ x: \\num | x > 0 ~\\}" + " \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    str = aptv_.toString();
    assertEquals(str, "nametype NREG = {x | x <- Int, x > 0}");

    // unary application, such as -256, power x
    lt = TestUtils.strToTerm("\\begin{zed}\n " + "NREG == \\{~ x: \\num | x > \\negate 256 ~\\}"
        + " \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    str = aptv_.toString();
    assertEquals(str, "nametype NREG = {x | x <- Int, x > -256}");

    lt = TestUtils.strToTerm("\\begin{zed}\n " + "NREG == \\{~ x: \\power~\\num | true ~\\}"
        + " \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    str = aptv_.toString();
    assertEquals(str, "nametype NREG = {x | x <- Set(Int), true}");

    // power
    lt = TestUtils.strToTerm("\\begin{circus}\n " + "\\circchannel\\ read:\\power~\\nat\\\\\n"
        + "\n\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    str = aptv_.toString();
    assertEquals(str, "channel read: Set(Nat)");

    // equality
    lt = TestUtils.strToTerm("\\begin{zed}\n " + "NREG == \\{~ x: \\power~\\num | x = \\{1,2\\} ~\\}"
        + " \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    str = aptv_.toString();
    assertEquals(str, "nametype NREG = {x | x <- Set(Int), x == {1, 2}}");
  }

  @Test
  public void testUniqueExists()
  {
    List<Term> lt = TestUtils.strToTerm("\\begin{zed}\n REG == \\{~ x: 0..10 | \\exists_1 y:\\num @ x=y*y ~\\} \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "nametype REG = {x | x <- {0 .. 10}, exists_1(Int, \\y @ x == y * y)}");
  }

  @Test
  public void testExists()
  {
    List<Term> lt = TestUtils.strToTerm("\\begin{zed}\n REG == \\{~ x: 0..10 | \\exists y:\\num @ x=y*y ~\\} \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "nametype REG = {x | x <- {0 .. 10}, exists(Int, \\y @ x == y * y)}");
  }

  @Test
  public void testForall()
  {
    List<Term> lt = TestUtils.strToTerm("\\begin{zed}\n REG == \\{~ x: 0..10 | \\forall y: 1..3 @ x=y*y ~\\} \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "nametype REG = {x | x <- {0 .. 10}, forall({1 .. 3}, \\y @ x == y * y)}");
  }

  /**
   * test \boolean type
   */
  @Test
  public void testBoolean()
  {
    List<Term> lt = TestUtils.strToTerm("\\begin{circus}\n " + "\\circchannel\\ read:\\boolean\\\\\n"
        + "\n\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    // \boolean has raw hex: 0xf09d94b9 and unicode \u120121 or \\u0x1d539
//    str= strToHex(str);
    assertEquals(str, "channel read: Bool");
  }

  /**
   * test set enumeration
   */
  @Test
  public void testSetEnum()
  {
    List<Term> lt = TestUtils.strToTerm("\\begin{zed}\n REG == \\{~ 1,3,5 ~\\} \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "nametype REG = {1, 3, 5}");
  }

  /**
   * test non-empty power set
   */
  @Test
  public void testPower_1()
  {
    List<Term> lt = TestUtils.strToTerm("\\begin{zed}\n REG == \\power_1~\\{~ 1,3,5 ~\\} \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "nametype REG = power_1({1, 3, 5})");
  }

  /**
   * test relation <->
   */
  @Test
  public void testRel()
  {
    // \iter
    List<Term> lt = TestUtils.strToTerm("\\begin{zed}\n X == \\{~ 0,2 ~\\} \\rel \\{~ 1,3 ~\\} \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "nametype X = rel({0, 2}, {1, 3})");
  }

  /**
   * Test iteraton \iter
   * TODO: how to construct a good iter expression
   */
  @Test
  public void testIter()
  {
    fail("Not yet implemented");
    
    // \iter
    List<Term> lt = TestUtils.strToTerm("\\begin{zed}\n X == \\{~ 0,2 ~\\} \\rel \\{~ 1,3 ~\\} \n REG == X~^\\{~0~\\} \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "nametype X = rel({0, 2}, {1, 3})");
  }

  /**
   * Test \seq_1
   */
  @Test
  public void testUniqueFiniteSeq()
  {
    // \iter
    List<Term> lt = TestUtils.strToTerm("\\begin{zed}\n X == \\seq_1 \\{~ 0,2 ~\\} \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "nametype X = seq_1({0, 2})");
  }

  /**
   * Test sequence bracket
   * \langle a,b,c \rangle
   */
  @Test
  public void testSeqListarg()
  {
    fail("Not yet implemented");
    
    List<Term> lt = TestUtils.strToTerm("\\begin{zed}\n X == \\langle 1,2,3 \\rangle \n \\end{zed}");
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "nametype X = rel({0, 2}, {1, 3})");
  }

  /**
   * Test distributed concatenation
   * TODO:
   */
  @Test
  public void testDistConcat()
  {
    fail("Not yet implemented");
    
    List<Term> lt = TestUtils.strToTerm("\\begin{zed}\n X == \\dcat \\langle \\langle 1,2 \\rangle \\rangle \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "nametype X = rel({0, 2}, {1, 3})");
  }

  @Test
  public void testGivenSet()
  {
    List<Term> lt = TestUtils.strToTerm("\\begin{zed}\n [PERSON] \n \\end{zed}" + "\n" + "\\begin{circus}\n "
        + "\\circchannel\\ read:PERSON\n" + "\n\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "datatype PERSON_TYPE = PERSON_1 | PERSON_2 | PERSON_3\n"
        + "PERSON = {PERSON_1, PERSON_2, PERSON_3}\n" + "channel read: PERSON\n");
  }

  @Test
  public void testFreeType()
  {
    List<Term> lt = TestUtils.strToTerm("\\begin{zed}\n Colors ~~::=~~ Red | Gree | Blue\n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "datatype Colors = Red | Gree | Blue");

    lt = TestUtils.strToTerm("\\begin{zed}\n [X] \n \\also \n Colors ~~::=~~ Red | Gree | Blue | const \\ldata X \\rdata \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    str = aptv_.toString();
    assertEquals(str, "datatype X_TYPE = X_1 | X_2 | X_3\n" + "X = {X_1, X_2, X_3}\n"
        + "datatype Colors = Red | Gree | Blue | const.X\n");
  }

  @Test
  public void testIntchAction()
  {
    List<Term> lt = TestUtils.strToTerm("\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\circspot \\Skip \\intchoice \\Stop \\circend\n"
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "TESTP = \n\t(SKIP\n\t|~|\n\tSTOP\n\t)");
  }

  /**
   * Test Prefix action
   */
  @Test
  public void testPrefixAction()
  {
    // c->Skip
    List<Term> lt = TestUtils.strToTerm("\\begin{circus}\n" + "\\circchannel\\ c \n" + "\\end{circus}"
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\circspot c \\then \\Skip \\circend\n"
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "channel c\nTESTP = (c -> SKIP)\n");

    // c.e->Skip
    lt = TestUtils.strToTerm("\\begin{circus}\n" + "\\circchannel\\ c:\\{1,3\\} \n" + "\\end{circus}"
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\circspot c.1 \\then \\Skip \\circend\n"
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    str = aptv_.toString();
    assertEquals(str, "channel c: {1, 3}\nTESTP = (c.1 -> SKIP)\n");

    // c!e->Skip
    lt = TestUtils.strToTerm("\\begin{circus}\n" + "\\circchannel\\ c:\\{1,3\\} \n" + "\\end{circus}"
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\circspot c!1 \\then \\Skip \\circend\n"
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    str = aptv_.toString();
    assertEquals(str, "channel c: {1, 3}\nTESTP = (c!1 -> SKIP)\n");

    // c?x->Skip
    lt = TestUtils.strToTerm("\\begin{circus}\n" + "\\circchannel\\ c:\\{1,3\\} \n" + "\\end{circus}"
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\circspot c?x \\then \\Skip \\circend\n"
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    str = aptv_.toString();
    assertEquals(str, "channel c: {1, 3}\nTESTP = (c?x -> SKIP)\n");

    // complex prefixing action: c?x!y?z -> Skip
    lt = TestUtils.strToTerm("\\begin{circus}\n"
        + "\\circchannel\\ c:\\{1,3\\} \\cross \\{1,3\\} \\cross \\{2,4\\}\n"
        + "\\end{circus}"
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\circspot c?x!1?z \\then \\Skip \\circend\n"
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    str = aptv_.toString();
    // TODO: channel declaration
    assertEquals(str, "channel c: {1, 3}.{1, 3}.{2, 4}\nTESTP = (c?x!1?z -> SKIP)\n");

    // c?x:B -> Skip
    lt = TestUtils.strToTerm("\\begin{circus}\n"
        + "\\circchannel\\ c: \\{1,3\\} \n"
        + "\\end{circus}"
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\circspot c?x \\prefixcolon (x > 2) \\then \\Skip \\circend\n"
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    str = aptv_.toString();
    assertEquals(str, "channel c: {1, 3}\nTESTP = (c?x: {x | x <- {1, 3}, x > 2} -> SKIP)\n");
  }

  /**
   * Test Channel Definition
   */
  @Test
  public void testChannelDecl()
  {
    // Sync channel
    List<Term> lt = TestUtils.strToTerm("\\begin{circus}\n" + "\\circchannel\\ c \n" + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "channel c");

    // channel list
    lt = TestUtils.strToTerm("\\begin{circus}\n" + "\\circchannel\\ c,d \n" + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    str = aptv_.toString();
    assertEquals(str, "channel c, d");

    // Complex channel
    lt = TestUtils.strToTerm("\\begin{circus}\n"
        + "\\circchannel\\ c: \\{1,3\\} \\cross 0..10 \n"
        + "\\end{circus}"
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\circspot c?x \\prefixcolon (x > 2)!3 \\then \\Skip \\circend\n"
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    str = aptv_.toString();
    assertEquals(str,
        "channel c: {1, 3}.{0 .. 10}\nTESTP = (c?x: {x | x <- {1, 3}, x > 2}!3 -> SKIP)\n");

    // various channel names
//    lt = TestUtils.strToTerm(  "\\begin{circus}\n" + "\\circchannel\\ x\\_1~, r, q'~, y\\_2: \\num \n" + "\\end{circus}");
//    aptv_.clear();
//    for (Term term : lt) {
//      if(!(term instanceof LatexMarkupPara || term instanceof NarrPara))
//      {
//        term.accept(aptv_);
//      }
//    }
//    str = aptv_.toString();
//    assertEquals(str, "channel c, d");

    // schema type as expression
//    lt = TestUtils.strToTerm( "\\begin{zed} \n Tsch ~~==~~ [~ x,y:\\{1,3\\} | x > y ~] \n \\end{zed} \n" +
    lt = TestUtils.strToTerm("\\begin{zed} \n Tsch ~~==~~ [~ x,y:\\{1,3\\} ~] \n \\end{zed} \n"
        + "\\begin{circus}\n" + "\\circchannelfrom\\ Tsch \n" + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    str = aptv_.toString();
    assertEquals(str, "channel y: {1, 3}\nchannel x: {1, 3}");
  }

  @Test
  public void testCartesianProduct()
  {
    List<Term> lt = TestUtils.strToTerm("\\begin{zed}\n REG == 0..5 \\cross \\{1,3\\}  \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      term.accept(aptv_);
    }
    String str = aptv_.toString();
    assertEquals(str, "nametype REG = ({0 .. 5},{1, 3})");

    lt = TestUtils.strToTerm("\\begin{zed}\n REG == 0..5 \\cross \\{1,3\\} \\cross \\{0,4\\} \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      term.accept(aptv_);
    }
    str = aptv_.toString();
    assertEquals(str, "nametype REG = ({0 .. 5},{1, 3},{0, 4})");

    lt = TestUtils.strToTerm("\\begin{zed}\n REG == 0..5 \\cross (\\{1,3\\} \\cross \\{0,4\\}) \n \\end{zed}");
    aptv_.clear();
    for (Term term : lt) {
      term.accept(aptv_);
    }
    str = aptv_.toString();
    assertEquals(str, "nametype REG = ({0 .. 5},({1, 3},{0, 4}))");
  }

  

  static public String byteToHex(byte b)
  {
    // Returns hex String representation of byte b
    char hexDigit[] = {'0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e',
        'f'};
    char[] array = {hexDigit[(b >> 4) & 0x0f], hexDigit[b & 0x0f]};
    return new String(array);
  }

  static public String charToHex(char c)
  {
    // Returns hex String representation of char c
    byte hi = (byte) (c >>> 8);
    byte lo = (byte) (c & 0xff);
    return byteToHex(hi) + byteToHex(lo);
  }

  static public String strToHex(String str)
  {
    StringBuilder sb = new StringBuilder();
    byte[] arr = str.getBytes();
    for (byte c : arr) {
      sb.append(byteToHex(c));
    }
    return sb.toString();
  }

  @Test
  public void testFfun()
  {
    List<Term> lt = TestUtils.strToTerm("\\begin{circus}\n "
        + "\\circchannel\\ read: \\{~1,3~\\} \\fun 0..4\\\\\n" + "\n\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "channel read: fun({1, 3}, {0 .. 4})");
  }

  /**
   * Test guarded action
   */
  @Test
  public void testGuardedAction()
  {
    // guarded
    List<Term> lt = TestUtils.strToTerm("\\begin{circus}\n" + "\\circchannel\\ c \n" + "\\end{circus}"
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\circspot c \\then \\Skip \\circend\n"
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "channel c\nTESTP = (c -> SKIP)\n");
  }

  /**
   * Test hide action
   */
  @Test
  public void testHideAction()
  {
    // c->Skip
    List<Term> lt = TestUtils.strToTerm("\\begin{circus}\n"
        + "\\circchannel\\ c \n"
        + "\\end{circus}"
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\circspot (c \\then \\Skip) \\circhide \\lchanset c \\rchanset \\circend\n"
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "channel c\nTESTP = (c -> SKIP) \\ {| c |}\n");
  }

  /**
   * Test action renaming
   */
  @Test
  public void testActionRenaming()
  {
    List<Term> lt = TestUtils.strToTerm("\\begin{circus}\n" 
        + "\\circchannel\\ c,d,e \n" 
        + "\\end{circus}\n"
        + "\\begin{circus}\n" 
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\ "
        + "\\circspot (c \\then \\Skip) \\lcircrename c := e \\rcircrename \\circend\n"
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "channel c, d, e\nTESTP = (e -> SKIP)\n");
    
    lt = TestUtils.strToTerm("\\begin{circus}\n" 
        + "\\circchannel\\ c,d,e: 0..2 \n" 
        + "\\end{circus}\n"
        + "\\begin{circus}\n" 
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\ "
        + "\\circspot (c?x \\then d!x \\then \\Skip) \\lcircrename c,d := e,e \\rcircrename \\circend\n"
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    str = aptv_.toString();
    assertEquals(str, "channel c, d, e: {0 .. 2}\nTESTP = (e?x -> (e!x -> SKIP))\n");
  }
  
//  /**
//   * Test action renaming
//   */
//  @Test
//  public void testAssign()
//  {    
//    List<Term> lt = TestUtils.strToTerm("\\begin{circus}\n" 
//        + "\\circchannel\\ c,d: 0..10 \n"
//        + "\\end{circus}\n"
//        + "\\begin{circus}\n" 
//        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\ "
//        + "\\circspot (c?x \\then x := x + 1 \\circseq d!3 \\then \\Skip) \\circend\n"
//        + "\\end{circus}");
//    aptv_.clear();
//    for (Term term : lt) {
//      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
//        term.accept(aptv_);
//        aptv_.crln();
//      }
//    }
//    String str = aptv_.toString();
//    assertEquals(str, "channel c, d, e: {0 .. 2}\nTESTP = (e?x -> (e!x -> SKIP))\n");
//  }
  /**
   * Test Channel Set Declaration
   */
  @Test
  public void testChannelSetDecl()
  {
    // empty channet set
    List<Term> lt = TestUtils.strToTerm("\\begin{circus}\n" + "\\circchannelset\\ C == \\emptyset \n" + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "C = {||}");

    // empty channet set
    lt = TestUtils.strToTerm("\\begin{circus}\n" 
        + "\\circchannelset\\ C == \\lchanset \\rchanset \n" 
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
      }
    }
    str = aptv_.toString();
    assertEquals(str, "C = {||}");
    
    // channel set with one element
    lt = TestUtils.strToTerm("\\begin{circus}\n" 
        + "\\circchannel\\ c,d,e \\\\\n"
        + "\\circchannelset\\ C == \\lchanset c \\rchanset \n" 
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    str = aptv_.toString();
    assertEquals(str, "channel c, d, e\nC = {| c |}\n");
    
    // channel set with three elements
    lt = TestUtils.strToTerm("\\begin{circus}\n" 
        + "\\circchannel\\ c,d,e \\\\\n"
        + "\\circchannelset\\ C == \\lchanset c, d, e \\rchanset \n" 
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    str = aptv_.toString();
    assertEquals(str, "channel c, d, e\nC = {| c, d, e |}\n");
  }
  
  /**
   * Test Name Set Declaration
   */
  @Test
  public void testNameSetDecl()
  {
    // Sync channel
    List<Term> lt = TestUtils.strToTerm("\\begin{circus}\n"
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
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    String str = aptv_.toString();
    assertEquals(str, "C = {||}");
  }
  
  @Test
  public void testParallelAction() 
  {
    List<Term> lt = TestUtils.strToTerm("\\begin{circus}\n"
        + "\\circchannel\\ c, d \\\\ \n"
        + "\\circchannelset\\ CS == \\lchanset c, d \\rchanset \n"
        + "\\end{circus}\n"
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 \\circspot (c \\then d \\then \\Skip) \\lpar | \\lchanset c, d \\rchanset | \\rpar (c \\then d \\then \\Skip) \\circend\n"
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    
    String str = aptv_.toString();
    assertEquals(str,
        "channel c, d\nCS = {| c, d |}\nTESTP = (c -> (d -> SKIP)) [| {| c,d |} |] (c -> (d -> SKIP))\n");
    
    lt = TestUtils.strToTerm("\\begin{circus}\n"
        + "\\circchannel\\ c, d \\\\ \n"
        + "\\circchannelset\\ CS == \\lchanset c, d \\rchanset \n"
        + "\\end{circus}\n"
        + "\\begin{circus}\n"
        + "\\circprocess\\ TESTP \\circdef \\circbegin \\\\\n"
        + "     \\t1 A \\circdef c \\then \\Skip \\\\\n"
        + "     \\t1 B \\circdef c \\then d \\then \\Skip \\\\\n"
        // additional bar (|) is necessary to separate the
        + "     \\t1 \\circspot A \\lpar | CS | \\rpar B \\\\\n"
        + "\\circend\n"
        + "\\end{circus}");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    
    str = aptv_.toString();
//    assertEquals(str,
//        "channel c: {1, 3}.{0 .. 10}\nTESTP = (c?x: {x | x <- {1, 3}, x > 2}!3 -> SKIP)\n");
    
  }
  
  // TODO: how to construct PowerType
  @Test
  public void testPowerType() 
  {
    // TODO: how to construct PowerType
    List<Term> lt = TestUtils.strToTerm(
        "\\begin{zed}\n [REG] \n \\end{zed} \n"
        + "\\begin{circus}\n"
        + "\\circchannel\\ c: \\power REG \\\\ \n"
        + "\\end{circus}\n");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    
    String str = aptv_.toString();
//    assertEquals(str,
//        "channel c, d\nCS = {| c, d |}\nTESTP = (c -> (d -> SKIP)) [| {| c,d |} |] (c -> (d -> SKIP))\n");
  }
  
  @Test
  public void testConstDecl() 
  {
    List<Term> lt = TestUtils.strToTerm(
        "\\begin{zed}\n Tsch ~~==~~ [~ x==1 ~] \n \\end{zed} \n"
        + "\\begin{circus}\n"
        + "\\circchannel\\ c: Tsch \\\\ \n"
        + "\\end{circus}\n");
    aptv_.clear();
    for (Term term : lt) {
      if (!(term instanceof LatexMarkupPara || term instanceof NarrPara)) {
        term.accept(aptv_);
        aptv_.crln();
      }
    }
    
    String str = aptv_.toString();
//    assertEquals(str,
//        "channel c, d\nCS = {| c, d |}\nTESTP = (c -> (d -> SKIP)) [| {| c,d |} |] (c -> (d -> SKIP))\n");
  }
}

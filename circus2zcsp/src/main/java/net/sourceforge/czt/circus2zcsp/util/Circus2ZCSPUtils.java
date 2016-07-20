/**
 * Some useful functions for conversion between Circus and Z/CSP
 */

package net.sourceforge.czt.circus2zcsp.util;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.StringWriter;
import java.io.Writer;
import java.math.BigInteger;
import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import net.sourceforge.czt.base.ast.Digit;
import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.CallProcess;
import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circus.ast.CircusNameSet;
import net.sourceforge.czt.circus.ast.CommUsage;
import net.sourceforge.czt.circus.ast.Communication;
import net.sourceforge.czt.circus.ast.DotField;
import net.sourceforge.czt.circus.ast.GuardedAction;
import net.sourceforge.czt.circus.ast.InputField;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.ast.QualifiedDecl;
import net.sourceforge.czt.circus.ast.SigmaExpr;
import net.sourceforge.czt.circus.ast.SpecStmtCommand;
import net.sourceforge.czt.circus2zcsp.Debug;
import net.sourceforge.czt.circus2zcsp.ISOZ2ZRM;
import net.sourceforge.czt.circus2zcsp.ast.CSPSpec;
import net.sourceforge.czt.circus2zcsp.data.CSPPredExpPattern;
import net.sourceforge.czt.circus2zcsp.data.CircusSpecMap;
import net.sourceforge.czt.circus2zcsp.data.FormatPattern;
import net.sourceforge.czt.circus2zcsp.data.Node;
import net.sourceforge.czt.circus2zcsp.data.PredExpPattern;
import net.sourceforge.czt.circus2zcsp.data.VersionInfo;
import net.sourceforge.czt.circus2zcsp.visitor.DeclListExpansionVisitor;
import net.sourceforge.czt.circus2zcsp.visitor.Omega2Visitor;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.RuleTable.RuleTableException;
import net.sourceforge.czt.rules.UnboundJokerException;
import net.sourceforge.czt.rules.rewriter.RewriteUtils;
import net.sourceforge.czt.rules.rewriter.Strategies;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionInfoException;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.CondExpr;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.DecorExpr;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Expr0N;
import net.sourceforge.czt.z.ast.Expr1;
import net.sourceforge.czt.z.ast.Expr2;
import net.sourceforge.czt.z.ast.ExprPred;
import net.sourceforge.czt.z.ast.HideExpr;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.LambdaExpr;
import net.sourceforge.czt.z.ast.LetExpr;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.MuExpr;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NegExpr;
import net.sourceforge.czt.z.ast.NegPred;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.NumStroke;
import net.sourceforge.czt.z.ast.Numeral;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.PreExpr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Pred2;
import net.sourceforge.czt.z.ast.Qnt1Expr;
import net.sourceforge.czt.z.ast.QntExpr;
import net.sourceforge.czt.z.ast.QntPred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.RenameExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SchExpr2;
import net.sourceforge.czt.z.ast.SchText;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.StrokeList;
import net.sourceforge.czt.z.ast.ThetaExpr;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.ast.ZStrokeList;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.util.WarningManager;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.LambdaExprVisitor;
import net.sourceforge.czt.z.visitor.LetExprVisitor;
import net.sourceforge.czt.z.visitor.MuExprVisitor;
import net.sourceforge.czt.z.visitor.ZNameVisitor;
import net.sourceforge.czt.zpatt.ast.JokerExpr;

/**
 * Map table for operation conversion from Circus to CSP
 * op - original operation
 * lhs,rhs - LHS and RHS of original operation
 * op' - converted operation
 * patt - new operation pattern, for op', lhs and rhs
 * 
 * @author rye
 *         op op' patt
 *         -------------------------------------------------------------
 *         succ succ PRESET2_PATTERN
 *         ZString.NEG - PREFIX_PATTERN
 */

public class Circus2ZCSPUtils
{
  @SuppressWarnings("serial")
  public static final Map<String, Pair<String, PredExpPattern>> opmap_ = new HashMap<String, Pair<String, PredExpPattern>>()
  {
    {
      ///////////////////////////// Logic /////////////////////////
      // TODO: ampersand (\& used in mutually recursive free type). Restricted!
      put(ZString.AMP, new Pair<String, PredExpPattern>("", PredExpPattern.UNKNOWN));
      // and
      put(ZString.AND, new Pair<String, PredExpPattern>("and", PredExpPattern.INFIX_PATTERN));
      // or
      put(ZString.OR, new Pair<String, PredExpPattern>("or", PredExpPattern.INFIX_PATTERN));
      // implies
      put(ZString.IMP, new Pair<String, PredExpPattern>("implies", PredExpPattern.PRESET3_PATTERN));
      // iff
      put(ZString.IFF, new Pair<String, PredExpPattern>("iff", PredExpPattern.PRESET3_PATTERN));
      // not
      put(ZString.NOT, new Pair<String, PredExpPattern>("not", PredExpPattern.PRESET2_PATTERN_1));
      // forall
      put(ZString.ALL, new Pair<String, PredExpPattern>("forall", PredExpPattern.PRESET3_PATTERN));
      // exists
      put(ZString.EXI, new Pair<String, PredExpPattern>("exists", PredExpPattern.PRESET3_PATTERN));
      // unique exists
      put(CSPPredExpPattern.getPattern(PredExpPattern.OP_NAME_EXISTS_1), new Pair<String, PredExpPattern>("exists_1",
          PredExpPattern.PRESET3_PATTERN));
      // TODO: Schema hide...etc

      
      ///////////////////////////// Number /////////////////////////
      // successor
      put("succ", new Pair<String, PredExpPattern>("succ", PredExpPattern.PRESET2_PATTERN));
      // NEG is HYPHEN-MINUS. e.g. -10
      put(ZString.NEG, new Pair<String, PredExpPattern>("-", PredExpPattern.PREFIX_PATTERN));
      // for MINUS and NEG, just translate into normal minus
      // MINUS is MINUS SIGN. Used in infix minus sign, e.g. (a - b)
      put(ZString.MINUS, new Pair<String, PredExpPattern>("-", PredExpPattern.INFIX_PATTERN));
      // less than
      put(ZString.LESS, new Pair<String, PredExpPattern>("<", PredExpPattern.INFIX_PATTERN));
      // less than and equal
      put(ZString.LEQ, new Pair<String, PredExpPattern>("<=", PredExpPattern.INFIX_PATTERN));
      // greater than
      put(ZString.GREATER, new Pair<String, PredExpPattern>(">", PredExpPattern.INFIX_PATTERN));
      // less than and equal
      put(ZString.GEQ, new Pair<String, PredExpPattern>(">=", PredExpPattern.INFIX_PATTERN));
      // plus +
      put(ZString.PLUS, new Pair<String, PredExpPattern>("+", PredExpPattern.INFIX_PATTERN));
      // minus -
      put(ZString.MINUS, new Pair<String, PredExpPattern>("-", PredExpPattern.INFIX_PATTERN));
      // multiple
      put(ZString.MULT, new Pair<String, PredExpPattern>("*", PredExpPattern.INFIX_PATTERN));
      // divide
      put("div", new Pair<String, PredExpPattern>("/", PredExpPattern.INFIX_PATTERN));
      // mod
      put("mod", new Pair<String, PredExpPattern>("%", PredExpPattern.INFIX_PATTERN));

      ///////////////////////////// Relation /////////////////////////
      // first
      put("first", new Pair<String, PredExpPattern>("first", PredExpPattern.PRESET2_PATTERN));
      // second
      put("second", new Pair<String, PredExpPattern>("second", PredExpPattern.PRESET2_PATTERN));
      // |->
      put(ZString.MAPSTO, new Pair<String, PredExpPattern>("", PredExpPattern.TUPLE_PATTERN));
      // domain
      put("dom", new Pair<String, PredExpPattern>("dom", PredExpPattern.PRESET2_PATTERN));
      // range
      put("ran", new Pair<String, PredExpPattern>("ran", PredExpPattern.PRESET2_PATTERN));
      // id
      put("id", new Pair<String, PredExpPattern>("id", PredExpPattern.PRESET2_PATTERN));
      // composition
      put(ZString.COMP, new Pair<String, PredExpPattern>("comp", PredExpPattern.PRESET3_PATTERN));
      // Backward relational composition: _CIRC_ = (Y <-> Z) X (X <-> Y) --> (X <-> Z)
      // o
      put(ZString.CIRC, new Pair<String, PredExpPattern>("circ", PredExpPattern.PRESET3_PATTERN));
      // Domain restriction
      put(ZString.DRES, new Pair<String, PredExpPattern>("dres", PredExpPattern.PRESET3_PATTERN));
      // Domain anti-restriction
      put(ZString.NDRES, new Pair<String, PredExpPattern>("ndres", PredExpPattern.PRESET3_PATTERN));
      // Range restriction
      put(ZString.RRES, new Pair<String, PredExpPattern>("rres", PredExpPattern.PRESET3_PATTERN));
      // Range anti-restriction
      put(ZString.NRRES, new Pair<String, PredExpPattern>("nrres", PredExpPattern.PRESET3_PATTERN));
      // relation inversion
      put(ZString.TILDE, new Pair<String, PredExpPattern>("inv", PredExpPattern.PRESET2_PATTERN));
      // _ \limg _ \rimg
      put(ZString.LIMG + ZString.RIMG, new Pair<String, PredExpPattern>("img",
          PredExpPattern.PRESET3_PATTERN));
      // relational override
      put(ZString.OPLUS, new Pair<String, PredExpPattern>("oplus", PredExpPattern.PRESET3_PATTERN));
      // % ^+
      put(ZString.NE + ZString.PLUS + ZString.SW, new Pair<String, PredExpPattern>("plus",
          PredExpPattern.PRESET2_LHS_PATTERN));
      // % ^*
      put(ZString.NE + ZString.MULT + ZString.SW, new Pair<String, PredExpPattern>("star",
          PredExpPattern.PRESET2_LHS_PATTERN));
      
      
      ///////////////////////////// Function ///////////////////////// 
      // partial function
      put(ZString.PFUN, new Pair<String, PredExpPattern>("pfun", PredExpPattern.PRESET3_PATTERN));
      // partial injective function
      put(ZString.PINJ, new Pair<String, PredExpPattern>("pifun", PredExpPattern.PRESET3_PATTERN));
      // total injective function
      put(ZString.INJ, new Pair<String, PredExpPattern>("tifun", PredExpPattern.PRESET3_PATTERN));
      // partial surjective function
      put(ZString.PSURJ, new Pair<String, PredExpPattern>("psfun", PredExpPattern.PRESET3_PATTERN));
      // total surjective function
      put(ZString.SURJ, new Pair<String, PredExpPattern>("tsfun", PredExpPattern.PRESET3_PATTERN));
      // total surjective function
//      put(ZString.SURJ, new Pair<String, PredExpPattern>("tsfun", PredExpPattern.PRESET3_PATTERN));
      // bijective function
      put(ZString.BIJ, new Pair<String, PredExpPattern>("bjfun", PredExpPattern.PRESET3_PATTERN));
      // finite partial function
      put(ZString.FFUN, new Pair<String, PredExpPattern>("pfun", PredExpPattern.PRESET3_PATTERN));
      // finite partial injective function
      put(ZString.FINJ, new Pair<String, PredExpPattern>("pifun", PredExpPattern.PRESET3_PATTERN));
      // disjoint
      put("disjoint", new Pair<String, PredExpPattern>("disjoint", PredExpPattern.PRESET2_PATTERN));
      // partition
      put("partition", new Pair<String, PredExpPattern>("partition", PredExpPattern.PRESET3_PATTERN));
      
      ///////////////////////////// Set /////////////////////////     
      // Relations <-> == P(lhs X rhs)
      put(ZString.REL, new Pair<String, PredExpPattern>("rel", PredExpPattern.PRESET3_PATTERN));
      // Function \fun
      put(ZString.FUN, new Pair<String, PredExpPattern>("tfun", PredExpPattern.PRESET3_PATTERN));
      // Inequality
      put(ZString.NEQ, new Pair<String, PredExpPattern>("!=", PredExpPattern.INFIX_PATTERN));
      // SUBSETEQ
      put(ZString.SUBSETEQ, new Pair<String, PredExpPattern>("<=", PredExpPattern.INFIX_PATTERN));
      // SUBSET
      put(ZString.SUBSET, new Pair<String, PredExpPattern>("<", PredExpPattern.INFIX_PATTERN));
      // membership \in
      put(ZString.MEM, new Pair<String, PredExpPattern>("member", PredExpPattern.PRESET3_PATTERN));
      // not membership \notin
      put(ZString.NOTMEM, new Pair<String, PredExpPattern>("not member", PredExpPattern.PRESET3_PATTERN));
      // Cartesian Product X
      put(ZString.CROSS, new Pair<String, PredExpPattern>("", PredExpPattern.TUPLE_PATTERN));
      // powerset
      put(ZString.POWER, new Pair<String, PredExpPattern>("Set", PredExpPattern.PRESET2_PATTERN));
      // Non-empty power set
      // String for \power_1 operator is ℙ↘1↖
      put(CSPPredExpPattern.getPattern(PredExpPattern.OP_NAME_POWER_1), new Pair<String, PredExpPattern>("power_1", PredExpPattern.PRESET2_PATTERN));
      // Set cardinality
      put(ZString.NUMBER, new Pair<String, PredExpPattern>("len", PredExpPattern.PRESET2_PATTERN));
      // Set union
      put(ZString.CUP, new Pair<String, PredExpPattern>("union", PredExpPattern.PRESET3_PATTERN));
      // Set inter
      put(ZString.CAP, new Pair<String, PredExpPattern>("inter", PredExpPattern.PRESET3_PATTERN));
      // Set difference
      put(ZString.SETMINUS, new Pair<String, PredExpPattern>("diff", PredExpPattern.PRESET3_PATTERN));
      // Set symmetric difference
      put(ZString.SYMDIFF, new Pair<String, PredExpPattern>("symdiff", PredExpPattern.PRESET3_PATTERN));      
      // Generalised union
      put(ZString.BIGCUP, new Pair<String, PredExpPattern>("Union", PredExpPattern.PRESET2_PATTERN));      
      // Generalised intersection
      put(ZString.BIGCAP, new Pair<String, PredExpPattern>("Inter", PredExpPattern.PRESET2_PATTERN));      
      // finite sets 
      put(ZString.FINSET, new Pair<String, PredExpPattern>("Set", PredExpPattern.PRESET2_PATTERN));
      // non-empty finite sets:
      put(ZString.FINSET + ZString.SE + "1" + ZString.NW, new Pair<String, PredExpPattern>("finset_1", PredExpPattern.PRESET2_PATTERN));     

///////////////////////////// Sequence /////////////////////////
      // \\upto such as 0..255
      put("..", new Pair<String, PredExpPattern>("..", PredExpPattern.INFIX_PATTERN_WITH_BRACES));
      // iteration \iter
      put("iter", new Pair<String, PredExpPattern>("itern", PredExpPattern.PRESET3_PATTERN));
      // iteration _^n
      put(ZString.NE + ZString.SW, new Pair<String, PredExpPattern>("itern", PredExpPattern.PRESET3_PATTERN));
      // minimum for set and sequence
      put("min", new Pair<String, PredExpPattern>("min", PredExpPattern.PRESET2_PATTERN));      
      // maximum for set and sequence
      put("max", new Pair<String, PredExpPattern>("max", PredExpPattern.PRESET2_PATTERN));      
      // finite sequence
      // TODO: 
      // put("seq", new Pair<String, PredExpPattern>("Seq", PredExpPattern.PRESET2_PATTERN));
      put("seq", new Pair<String, PredExpPattern>("fseq", PredExpPattern.PRESET2_PATTERN));
      // non-empty finite sequence
      put(CSPPredExpPattern.getPattern(PredExpPattern.OP_NAME_SEQ_1), 
          new Pair<String, PredExpPattern>("seq1", PredExpPattern.PRESET2_PATTERN));
      // injective sequence
      put("iseq", new Pair<String, PredExpPattern>("iseq", PredExpPattern.PRESET2_PATTERN));
      // sequence bracket
      put(CSPPredExpPattern.getPattern(PredExpPattern.OP_NAME_SEQ_BRACKET), 
          new Pair<String, PredExpPattern>("", PredExpPattern.SEQ_BRACKETS_PATTERN));
      // concatenation
      put(ZString.CAT, new Pair<String, PredExpPattern>("^", PredExpPattern.INFIX_PATTERN));
      // reverse
      put("rev", new Pair<String, PredExpPattern>("reverse", PredExpPattern.PRESET2_PATTERN));
      // head
      put("head", new Pair<String, PredExpPattern>("head", PredExpPattern.PRESET2_PATTERN));
      // last
      put("last", new Pair<String, PredExpPattern>("last", PredExpPattern.PRESET2_PATTERN));
      // tail
      put("tail", new Pair<String, PredExpPattern>("tail", PredExpPattern.PRESET2_PATTERN));
      // reverse
      put("front", new Pair<String, PredExpPattern>("front", PredExpPattern.PRESET2_PATTERN));
      // squash/re-indexing
      put("squash", new Pair<String, PredExpPattern>("squash", PredExpPattern.PRESET2_PATTERN));
      // extract
      put(ZString.EXTRACT, new Pair<String, PredExpPattern>("extract", PredExpPattern.PRESET3_PATTERN));
      // filter
      put(ZString.FILTER, new Pair<String, PredExpPattern>("filter", PredExpPattern.PRESET3_PATTERN_RHS_LHS));
      // prefix
      put("prefix", new Pair<String, PredExpPattern>("prefix", PredExpPattern.PRESET3_PATTERN));
      // suffix
      put("suffix", new Pair<String, PredExpPattern>("suffix", PredExpPattern.PRESET3_PATTERN));
      // infix
      put("infix", new Pair<String, PredExpPattern>("infix", PredExpPattern.PRESET3_PATTERN));
      // distributed concatenation
      // {\cat}/
      put(CSPPredExpPattern.getPattern(PredExpPattern.OP_NAME_DIS_CONC), 
          new Pair<String, PredExpPattern>("concat", PredExpPattern.PRESET2_PATTERN));
    }
  };

  @SuppressWarnings("serial")
  public static final Map<String, String> wordmap_ = new HashMap<String, String>()
  {
    {
      put(ZString.TRUE, "true");
      put("True", "true");
      put("False", "false");
      put(ZString.FALSE, "false");
      // \boolean
      put(CSPPredExpPattern.getPattern(PredExpPattern.BOOLEAN), "Bool");
      put(ZString.NUM, "Int");
      put(ZString.NUM + ZString.SE + "1" + ZString.NW, "num_1");
      put(ZString.NAT, "Nat");
      put(ZString.NAT + ZString.SE + "1" + ZString.NW, "Nat_1");
      put(ZString.ARITHMOS, "Int"); // TODO: ???
      put(ZString.EMPTYSET, "{}");
      put("$$SYNCH", "");
    }
  };

  public Circus2ZCSPUtils()
  {
  }

  /**
   * Retrieves the kind of the given MemPred.
   * It deals with the four cases available for: set containment (ex: X isin Y),
   * n-ary and unary relational operator application (X < Y, disjoint~S), and
   * equality (X = Y). It throws a ZEvesIncompatibleASTException when none
   * of these cases can be identified.
   */
  public static MemPredKind getMemPredKind(MemPred term)
  {
    /*
     * NOTE (from CZT Z.xsd file):
     * A relation operator application (C.5.12).
     * The mixfix attribute is false iff the input has the form Expr1 in Expr2.
     * When mixfix=true, the second (right) Expr must be either a
     * relational operator and the first (left) Expr must be a tuple
     * containing the corresponding number of arguments (unless the
     * operator has one argument, then no tuple is required) or an
     * equality and the the second (right) Expr must be a set expression
     * containing exactly one expression.
     * For example, the input "m &lt; n" generates a MemPred element with
     * mixfix=true, left=(m,n) and right=" _ &lt; _ ", whereas
     * "(m,n) in (_ &lt; _)" has the same left and right expressions,
     * but mixfix=false.
     */
    /*
     * NOTE (MemPred cases):
     * case1: mixfix=false ex: E1 in E2
     * Left = any expr
     * Right = any expr
     * case2: mixfix=true
     * case2.1: Relational operator application
     * case2.1.1: More than one argument: ex X subseteq Y
     * Left = TupleExpr(RefExpr(X, false), RefExpr(Y,false)) &
     * Right = RefExpr("_subseteq_", false) (n-ary relOps).
     * case2.1.2: One argument exactly: ex disjoint X
     * Left = Any expr. ex: SetExpr, RefExpr(X, false), etc...
     * Right = RefExpr("disjoint_", false)! (unary relOps).
     * case2.2: Equality x = y
     * Left = RefExpr(x, false)
     * Right = SetExpr(RefExpr(y, false))
     */
    MemPredKind result;
    if (!term.getMixfix()) { // case 1
      result = MemPredKind.SET_MEMBERSHIP;
    }
    else {
      Expr right = term.getRightExpr();
      if (right instanceof RefExpr) { // case 2.1
        RefExpr r = (RefExpr) right;
        Expr left = term.getLeftExpr();

        OperatorName on = r.getZName().getOperatorName();
        // if there is an op and is unary, it's unary
        if (on != null && on.isUnary())
          result = MemPredKind.UNARY_RELOP_APPLICATION;
        // otherwise if it isn't an op and is a TupleExpr, then might still be a unary, but I cannot
        // know, so have it as nary
        else if (left instanceof TupleExpr)
          result = MemPredKind.NARY_RELOP_APPLICATION;
        // catch all...
        else
          result = MemPredKind.UNARY_RELOP_APPLICATION;
        // if (opTable_ != null)
        // {
        // // might be a unary relation still, even if LHS is a TupleExpr: ex. myUnRel~(x, y)!
        // OperatorTokenType ott = opTable_.getTokenType(r.getZName().getWord());
        // if (ott != null && ott.equals(OperatorTokenType.PREP))
        // result = MemPredKind.UNARY_RELOP_APPLICATION;
        // }
//        if (left instanceof TupleExpr) // case 2.1.1
//        {
//          result = MemPredKind.NARY_RELOP_APPLICATION;
//        }
//        else // case 2.1.2
//        {
//          result = MemPredKind.UNARY_RELOP_APPLICATION;
//        }
      }
      else if (right instanceof SetExpr) { // case 2.2
        result = MemPredKind.EQUALITY;
      }
      else {
        throw new CztException(
            "Invalid relational operator application, while trying to convert"
                + "CZT membership predicate to Z/EVES XML API. See throwable cause for details.",
            new IllegalArgumentException(
                "In CZT (and Z standard) relational operators can appear as predicates. "
                    + "There are two cases to consider: n-ary, and unary relational operators. For n-ary operators, the "
                    + "left expression must be a TupleExpr containing all the arguments for the relational operator. For "
                    + "instance, x~\\subseteq~y is represented as (mixfix=boolean values) \n\t "
                    + "MemPred(TupleExpr(RefExpr(\"x\", false), RefExpr(\"y\", false)), RefExpr(\"_~\\subseteq~_\", false), true)\n "
                    + "On ther other hand, for unary operators, the left expression can be the actual expression being applied"
                    + "for the relational operator in question. For instance, \\disjoint~{ s, t } is represeted as \n\t "
                    + "MemPred(SetExpr(RefExpr(\"s\", false), RefExpr(\"t\", false)), RefExpr(\"\\disjoint~_\"), true)"));
      }
    }
    return result;
  }

  /**
   * * A reference expression (C.6.21, C.6.28, C.6.29).
   * <ul>
   * <li>C.6.21 (Generic Operator Application). For example: S \rel T. In this case, mixfix and
   * explicit are always true, and the list of instantiating expressions is non-empty (it contains
   * [S,T]).</li>
   * <li>C.6.28 (Reference). For example: \arithmos In this case, mixfix and explicit are always
   * false and the list of instantiating expressions is empty. Another example before typechecking
   * is \emptyset. The typechecker transforms \emptyset to a generic instantiation and explicit
   * remains false (see 13.2.3.3).</li>
   * <li>C.6.29 (Generic Instantiation). For example: \emptyset[T]. In this case, mixfix is always
   * false and the list of instantiating expressions is non-empty (it contains [T]). The explicit
   * attribute indicates whether the instantiating expressions are explicitly given in the
   * specification (explicit is true) or whether they were inferred by the typechecker (explicit is
   * false).</li>
   * 
   * @param term
   * @return
   */
  public static RefExprKind getRefExprKind(RefExpr term)
  {
    Boolean mixfix = term.getMixfix();
    Boolean explicit = term.getExplicit();
    assert mixfix != null && explicit != null;
    boolean hasGenerics = !term.getZExprList().isEmpty();
    RefExprKind result;
    if (mixfix.booleanValue()) {
      if (hasGenerics || explicit.booleanValue())
        result = RefExprKind.GEN_OP_APPL;
      else
        result = RefExprKind.OP_APPL;
    }
    else {
      if (hasGenerics || explicit.booleanValue())
        result = RefExprKind.GEN_REF;
      else
        result = RefExprKind.REF;
    }
    return result;
  }

  /**
 * A (generic) axiomatic paragraph, (generic) schema definition,
        or (generic) horizontal definition
        <ul>
        <li>C.4.3 (Axiomatic description) and C.4.5 (Generic description).
          In this case, Box=AxBox.  NameList contains the generic parameters,
          so is empty for an axiomatic description.  For example,
          <code>\begin{axdef}     x,y: \nat \where x \neq y \end{axdef}</code>
          <code>\begin{gendef}[T] x,y: T \where x \neq y \end{gendef}</code>
          both translate into an AxPara with Box=AxBox and SchText containing
          the declaration of x and y, and the predicate x \neq y.  For the axdef
          example, NameList is empty, whereas for the gendef example it
          contains T.
        </li>        
        <li>C.4.4 (Schema definition) and C.4.6 (Generic schema definition).
          In this case, Box=SchBox.  For example,
          <code>\begin{schema}{S} x,y: \nat \where x \neq y \end{schema}</code>
          is translated into a nongeneric AxPara (see 12.2.3.1 or C.4.4.2)
          whose SchText contains a single ConstDecl, S == [x,y:\nat | x \neq y].
          A generic schema definition is similar but has a non empty NameList
          (see 12.2.3.2 or C.4.6.2).
        </li>                
        <li>C.4.7 (Horizontal definition) and
            C.4.8 (Generic horizontal definition).
          In this case, Box=OmitBox.  For example,
          <code>\begin{zed}S == [x,y: \nat | x \neq y]\end{zed}</code>
          is translated into a nongeneric AxPara (see 12.2.3.3 or C.4.7.2)
          whose SchText contains a single ConstDecl, S == [x,y:\nat | x \neq y].
          A generic horizontal definition is similar but has a non empty
          NameList (see 12.2.3.4 or C.4.8.2).
        </li>        
        </ul>
   * @param term
   * @return
   */
  public static AxParaKind getAxParaKind(AxPara term)
  {
    AxParaKind result;
    
    assert(term != null);    
    boolean generic = !term.getZNameList().isEmpty();
    
    if(term.getBox().equals(Box.AxBox)) {
        result = generic?AxParaKind.GEN_AXDEF : AxParaKind.AXDEF;
    }
    else if(term.getBox().equals(Box.OmitBox)) {
      ConstDecl cdecl = (ConstDecl)term.getZSchText().getZDeclList().get(0);
      if(cdecl.getExpr() instanceof SchExpr) {
        result = generic?AxParaKind.GEN_HORIZON_SCHEMA : AxParaKind.HORIZON_SCHEMA;
      }
      else {
        result = generic?AxParaKind.GEN_ABBR : AxParaKind.ABBR;
      }
    }
    else {//if(term.getBox().equals(Box.SchBox)) {
      result = generic?AxParaKind.GEN_BOXED_SCHEMA : AxParaKind.BOXED_SCHEMA;
    }
    
    return result;
  }
  
  /**
   * Check if the string contains an operator argument " _ "
   * 
   * @param name
   * @return
   */
  public static boolean hasOpArg(String name)
  {
    return (name.indexOf(ZString.ARG) != -1);
  }

  public static boolean hasOpArg(ZName name)
  {
    return hasOpArg(name.getWord());
  }

  public static String getOperator(OperatorName opname)
  {
    // We are concatenating the result. In almost all cases, one gets "THE" operator involved
    // since we are ignoring ARGs. On ocassional special cases (e.g., LANGLE, LIMG, LBLOT, user
    // defined
    // \\listarg op temp), we need to treat it specially, hence we send the whole load of symbols
    // involved.
    //
    String result = "";

    // See revision 3986 in the repository if this fails.
    // I used to use opname.iterator, for what now is getWords().
    Iterator<String> parts = Arrays.asList(opname.getWords()).iterator();// opname.iterator();

    while (parts.hasNext()) {
      String part = parts.next().toString();
      if ((!part.equals(ZString.ARG) /*&& !part.equals(ZString.LISTARG)*/)) {
        result += part;
      }
    }

    // get strokes
    assert !result.isEmpty();
    String strokes = getStrokes(opname.getStrokes());
    result += strokes;
    return result.trim(); // remove dangling spaces
  }

  /**
   * Returns a list of strokes simply concatenated as it appears.
   */
  public static String getStrokes(StrokeList strokes)
  {
    ZStrokeList zstrokes = ZUtils.assertZStrokeList(strokes);

    StringBuilder result = new StringBuilder("");
    for (Stroke stk : zstrokes) {
      result.append(stk.accept(new PrintVisitor()));
    }
    return result.toString();
  }

  /**
   * Convert Circus Predicate or Expression with operator to CSPM representation
   * e.g.
   * a = b => a == b
   * a leq b => a <= b
   * a \in b => member(a, b)
   * not a => not a
   * 
   * @param lhs - for prefix operator, it's empty
   * @param rhs - for postfix operator, it's empty
   * @param op - operator name
   */
  public static String convertOp(String lhs, String rhs, String op)
  {
    String result = "UnknownOp:" + op;

    Pair<String, PredExpPattern> pairOpPatt = opmap_.get(op);
    if(pairOpPatt == null) {
      throw new CztException("The operator: " + op + " is unknown or not supported!");
    }
    
    String strOp = pairOpPatt.getFirst();
    PredExpPattern patt = pairOpPatt.getSecond();
    String strPatt = CSPPredExpPattern.getPattern(patt);
    
    if (patt.equals(PredExpPattern.INFIX_PATTERN)) {
      result = MessageFormat.format(strPatt, lhs, strOp, rhs);
    }
    else if (patt.equals(PredExpPattern.INFIX_PATTERN_WITH_BRACES)) {
      result = MessageFormat.format(strPatt, lhs, strOp, rhs);
    }
    else if (patt.equals(PredExpPattern.PREFIX_PATTERN)) {
      result = MessageFormat.format(strPatt, strOp, rhs);
    }
    else if (patt.equals(PredExpPattern.PREFIX2_PATTERN)) {
      result = MessageFormat.format(strPatt, strOp, rhs);
    }
    else if (patt.equals(PredExpPattern.POSTFIX_PATTERN)) {
      result = MessageFormat.format(strPatt, lhs, strOp);
    }
    else if (patt.equals(PredExpPattern.PRESET3_PATTERN)) {
      result = MessageFormat.format(strPatt, strOp, lhs, rhs);
    }
    else if (patt.equals(PredExpPattern.PRESET3_PATTERN_RHS_LHS)) {
      result = MessageFormat.format(strPatt, strOp, rhs, lhs);
    }
    else if (patt.equals(PredExpPattern.PRESET2_PATTERN)) {
      result = MessageFormat.format(strPatt, strOp, rhs);
    }
    else if (patt.equals(PredExpPattern.PRESET2_PATTERN_1)) {
      result = MessageFormat.format(strPatt, strOp, rhs);
    }
    else if (patt.equals(PredExpPattern.PRESET2_LHS_PATTERN)) {
      result = MessageFormat.format(strPatt, strOp, lhs);
    }
    else if (patt.equals(PredExpPattern.TUPLE_PATTERN)) {
      result = MessageFormat.format(strPatt, lhs, rhs);
    }
    else if (patt.equals(PredExpPattern.SEQ_BRACKETS_PATTERN)) {
      /*
       * LHS - ""
       * RHS - {(1,2),(2,7),(3,10)}
       */

      rhs = rhs.replaceAll("\\{", "");
      rhs = rhs.replaceAll("\\}", "");
      rhs = rhs.replaceAll("\\([0-9]*,", "");
      rhs = rhs.replaceAll(" ", "");
      rhs = rhs.replaceAll("\\)", "");
//      String seqLst[] = rhs.split(",");
      result = MessageFormat.format(strPatt, rhs);
    }
    else {
      result = op;
    }
    return result;
  }

  /**
   * Converts a CZT ZName into a ZEves name. If isIdentOnly is true and ZName
   * is an operator (getOperatorName() != null), an exception is raised.
   * 
   * @param name
   * @param isDeclName add surround parenthesis to ZName that are operators or not
   * @param isIdentOnly consider opName or not from ZName.
   * @return
   */
  public static String getZEvesName(ZName name, boolean isDeclName, boolean isIdentOnly,
      Boolean keepOpArgs)
  {
    if (keepOpArgs != null) {
    }
    String result;
    OperatorName on = name.getOperatorName();
    if (on != null && !isIdentOnly) {
      result = getOperator(on);
      // if not a declname that is an operator, e.g., \_ \myop \_ not within AxDef declpart say
      // add parenthesis around it to become (\_ \myop \_) , eg., (\_\R\_) \comp (\_ \S \_)
      if (!isDeclName && hasOpArg(result))
        result = "(" + result + ")";
    }
    else {
      result = getIdent(name);
    }
    if (keepOpArgs != null) {

    }
    return result;
  }

  /**
   * Get a variable name, where it isn't a declname and ident/opname are allowed.
   * This does not influence the keep-op stack
   * 
   * @param name
   * @return
   */
  public static String getVarName(ZName name)
  {
    String result;
    OperatorName on = name.getOperatorName();
    if (on != null) {
      result = getOperator(on);
      // if not a declname that is an operator, e.g., \_ \myop \_ not within AxDef declpart say
      // add parenthesis around it to become (\_ \myop \_) , eg., (\_\R\_) \comp (\_ \S \_)
      if (hasOpArg(result))
        result = "(" + result + ")";
    }
    else {
      result = getIdent(name);
    }
    return result;
  }

  /**
   * Represents the ident production. It extracts the word and the decorations
   * (from strokes) from a given DeclName.
   */
  public static String getIdent(ZName name)
  {
    if (name.getOperatorName() != null)
      throw new CztException("CZT operator template is not a valid identifier " + name.toString());
    StringBuilder result = new StringBuilder(getWord(name));
    
    boolean appendStroke = true;
    
    // _1 stroke will not append after word since it has been handled in getWord()
    if(name.getZStrokeList().size() == 1) {
      if(name.getZStrokeList().get(0) instanceof NumStroke) {
        if(((NumStroke)name.getZStrokeList().get(0)).getDigit().equals(Digit.ONE)) {
          appendStroke = false;
        }
      }
    }
    
    if(appendStroke) {
      result.append(getStrokes(name.getZStrokeList()));
    }
    return result.toString();
  }

  /**
   * Returns the word part of a DeclName ensuring it is not empty.
   */
  public static String getWord(ZName name)
  {
    ZName zname = ZUtils.assertZName(name);
    assert zname != null && zname.getWord().length() > 0 : "A valid word can be neither null nor empty.";
    String result = zname.getWord();
    
    // if zname.stroke is _1 or ^1, then
    if(!zname.getZStrokeList().isEmpty()) {
      ZStrokeList zsl = zname.getZStrokeList();
      // check if is _1
      if(zsl.size() == 1 && zsl.get(0) instanceof NumStroke) {
        if(((NumStroke)zsl.get(0)).getDigit().equals(Digit.ONE)) {
          // _1
          result += ZString.SE + "1" + ZString.NW;
        }
      }
    }

    result = translateWord(result);
    return result;
  }

  /**
   * Translate Z word to CSP Word
   */
  private static String translateWord(String word)
  {
    String str = wordmap_.get(word);
    if(str == null)
    {
      str = word;
    }
//    if (word.equals(ZString.NUM)) {
//      word = "Int";
//    }
//    else if (word.equals(ZString.NAT)) {
//      word = "Nat";
//    }
//    else if (word.equals(ZString.ARITHMOS)) {
//      // if it appear from CZT, just use NUM instead.
//      word = "Int";
//    }
//    else if (word.equals(ZString.POWER)) {
//      word = "Set";
//    }
//    else if (word.equals(ZString.EMPTYSET)) {
//      word = "{}";
//    }
//    else if (word.equals(ZString.BIGCUP)) {
//      word = "Union";
//    }
//    else if (word.equals(ZString.BIGCAP)) {
//      word = "Inter";
//    }
//    else if (word.equals("$$SYNCH")) {
//      word = "";
//    }

    return str;
  }

//  /**
//   * Convert a schema into negation of its precondition, for schema as action rule
//   * 
//   * @param proname - the name of process
//   * @param axpara - the original schema
//   * @param cspspec - CSP Spec
//   * @param map - map data
//   */
//  @SuppressWarnings("unchecked")
//  public static AxPara NegPreconditionSchema(String proname, AxPara axpara,
//      CSPSpec cspspec, CircusSpecMap map)
//  {
//    assert(cspspec != null && map != null);
//    
//    ZFactory zfac_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
//
//    /*
//     * Channel definition
//     * channel fRead:Tins
//     */
//    Object ob = axpara.accept(new PrecChannelDeclVisitor());
//    if (ob instanceof List<?>) {
//      Debug.debug_print(
//          Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
//          Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
//          Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
//          "channel:" + (List<String>) ob);
//      cspspec.addChannel((List<String>) ob);
//    }
//
//    // original schema name
//    Name pName = ZUtils.getAxParaSchOrAbbrName((Term)axpara);
//    String paraName = Circus2ZCSPUtils.termToString(pName);
//
//    ZNameList fp = zfac_.createZNameList();
//    // ZName for new schema
//    ZName paraname = zfac_.createZName(
//        MessageFormat.format(FormatPattern.NEG_PRECONDITION_SCHEMA, paraName),
//        zfac_.createZStrokeList(), null);
//
//    cspspec.addHideCSPB(MessageFormat.format(FormatPattern.NEG_PRECONDITION_SCHEMA, paraName));
//    ZDeclList declList = zfac_.createZDeclList();
//
//    // State Paragraph Name and \Xi State Paragraph. It's an InclDecl
//    String stName = map.getStatPara(proname);
//    ZName stname = zfac_.createZName(ZString.XI + stName, zfac_.createZStrokeList(), null);
//    RefExpr expr = zfac_.createRefExpr(stname, zfac_.createZExprList(), false, false);
//
//    InclDecl inclDecl = zfac_.createInclDecl(expr);
//    declList.add(inclDecl);
//
//    // Add other inputs declarations
//    for (Decl decl : axpara.getZSchText().getZDeclList()) {
//      if (decl instanceof ConstDecl) {
//        Expr expr1 = ((ConstDecl) decl).getExpr();
//        if (expr1 instanceof SchExpr) {
//          for (Decl decl1 : ((SchExpr) expr1).getZSchText().getZDeclList()) {
//            if (decl1 instanceof VarDecl) {
//              for (Name zn : ((VarDecl) decl1).getZNameList()) {
//                if (zn instanceof ZName) {
//                  for (net.sourceforge.czt.z.ast.Stroke sk : ((ZName) zn).getZStrokeList()) {
//                    if (sk instanceof InStroke) {
//                      declList.add(decl1);
//                    }
//                  }
//                }
//              }
//            }
//          }
//        }
//      }
//    }
//
//    //
//    ZName axparaname = zfac_.createZName(paraName, zfac_.createZStrokeList(), null);
//    // RefExpr to schema
//    RefExpr refexpr = zfac_.createRefExpr(axparaname, zfac_.createZExprList(), false, false);
//    // Precondition expression
//    PreExpr preexpr = zfac_.createPreExpr(refexpr);
//    // Negation expression
//    NegExpr negexpr = zfac_.createNegExpr(preexpr);
//    //
//    ExprPred exprpred = zfac_.createExprPred(negexpr);
//    ZSchText schText = zfac_.createZSchText(declList, exprpred);
//    SchExpr schExpr = zfac_.createSchExpr(schText);
//
//    ConstDecl cd = zfac_.createConstDecl(paraname, schExpr);
//
//    ZDeclList declList0 = zfac_.createZDeclList();
//    declList0.add(cd);
//    SchText st = zfac_.createZSchText(declList0, null);
//
//    AxPara faxpara = zfac_.createAxPara(fp, st, Box.OmitBox);
//    return faxpara;
//  }
  
  /**
   * Convert a schema into negation of its precondition, for schema as action rule
   * 
   * @param proname - the name of process
   * @param axpara - the original schema
   * @param cspspec - CSP Spec
   * @param map - map data
   */
  public static AxPara NegPreconditionSchema(String proname, AxPara axpara,
      CircusSpecMap map, BasicProcess bp, ZSect zs, SectionManager manager, String sectname)
  {
    assert(map != null);
    ZFactory zfac_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
    
    // original schema name
    Name pName = ZUtils.getAxParaSchOrAbbrName((Term)axpara);
    String paraName = "";
    if(pName != null) {
      paraName = Circus2ZCSPUtils.termToString(pName);
    }

    // ZName for new schema
    ZName paraname = zfac_.createZName(
        MessageFormat.format(FormatPattern.NEG_PRECONDITION_SCHEMA, paraName),
        zfac_.createZStrokeList(), null);

    if(bp != null) {
      for(Para p: bp.getZParaList()) {
        if(p instanceof AxPara) {
          ZName n = (ZName) ZUtils.getAxParaSchOrAbbrName(p);
          if(n != null) {
            if(Circus2ZCSPUtils.isEquals(paraname, n)) {
              // found
              return null;
            }
          }
        }
      }
    }

    AxParaKind kind = getAxParaKind(axpara);
    switch(kind) {
      case ABBR:
      case BOXED_SCHEMA:
      case HORIZON_SCHEMA:
        break;
      case AXDEF:
      default:
        throw new CztException("AxPara in NegPreconditionSchema must be "
            + "Abbreviation or Schema but it is " + kind.toString() + "!");
    }
    
    ZNameList fp = zfac_.createZNameList();
//    // ZName for new schema
//    ZName paraname = zfac_.createZName(
//        MessageFormat.format(FormatPattern.NEG_PRECONDITION_SCHEMA, paraName),
//        zfac_.createZStrokeList(), null);

    ZDeclList declList = zfac_.createZDeclList();

    // State Paragraph Name and \Xi State Paragraph. It's an InclDecl
    String stName = MessageFormat.format(FormatPattern.RENAMING_IN_PROC, proname, map.getStatPara(proname));
    ZName stname = zfac_.createZName(ZString.XI + stName, zfac_.createZStrokeList(), null);
    RefExpr expr = zfac_.createRefExpr(stname, zfac_.createZExprList(), false, false);

    InclDecl inclDecl = zfac_.createInclDecl(expr);
    declList.add(inclDecl);

    // Get a list of variables declared in axpara
    DeclListExpansionVisitor dlevisitor = new DeclListExpansionVisitor(bp, zs, manager, sectname);
    // after renaming, normalisation might not work properly, so disable it
    dlevisitor.disableNormalisation();
    axpara.accept(dlevisitor);
    List<Pair<ZName, Expr>> lstZNameExpr = dlevisitor.getNameExprPairAsList();
    
    for(Pair<ZName, Expr> p: lstZNameExpr) {
      if(p.getFirst().getZStrokeList().size() == 1) {
        if(p.getFirst().getZStrokeList().get(0) instanceof InStroke) {
          // input variables, then add to declList
          List<ZName> lstName = new ArrayList<ZName>();
          lstName.add(p.getFirst());
          ZNameList znl = zfac_.createZNameList(lstName);
          declList.add(zfac_.createVarDecl(znl, p.getSecond()));
        }
      }
    }
    
//    // Add other inputs declarations
//    for (Decl decl : axpara.getZSchText().getZDeclList()) {
//      if (decl instanceof ConstDecl) {
//        Expr expr1 = ((ConstDecl) decl).getExpr();
//        if (expr1 instanceof SchExpr) {
//          for (Decl decl1 : ((SchExpr) expr1).getZSchText().getZDeclList()) {
//            if (decl1 instanceof VarDecl) {
//              for (Name zn : ((VarDecl) decl1).getZNameList()) {
//                if (zn instanceof ZName) {
//                  for (net.sourceforge.czt.z.ast.Stroke sk : ((ZName) zn).getZStrokeList()) {
//                    if (sk instanceof InStroke) {
//                      declList.add(decl1);
//                    }
//                  }
//                }
//              }
//            }
//          }
//        }
//      }
//    }

    //
    ZName axparaname = zfac_.createZName(paraName, zfac_.createZStrokeList(), null);
    // RefExpr to schema
    RefExpr refexpr = zfac_.createRefExpr(axparaname, zfac_.createZExprList(), false, false);
    // Precondition expression
    PreExpr preexpr = zfac_.createPreExpr(refexpr);
    // Negation expression
    NegExpr negexpr = zfac_.createNegExpr(preexpr);
    //
    ExprPred exprpred = zfac_.createExprPred(negexpr);
    ZSchText schText = zfac_.createZSchText(declList, exprpred);
    SchExpr schExpr = zfac_.createSchExpr(schText);

    ConstDecl cd = zfac_.createConstDecl(paraname, schExpr);

    ZDeclList declList0 = zfac_.createZDeclList();
    declList0.add(cd);
    SchText st = zfac_.createZSchText(declList0, null);

    AxPara faxpara = zfac_.createAxPara(fp, st, Box.OmitBox);
    return faxpara;
  }
  
  /**
   * Check if a given schema has its precondition always holds
   * @param proname - process name
   * @param axpara - a AxPara
   * @param map - map data
   * @return
   */
  public static boolean isASchemaWithPrecondAlwaysTrue(String proname, AxPara axpara,
      CircusSpecMap map)
  {
    boolean ret = false;

    if(!ZUtils.isSimpleSchema(axpara)) {
      return false;
    }
    
    ZName name = (ZName) ZUtils.getSchemaName(axpara);
    SchExpr expr = (SchExpr) ZUtils.getSchemaDefExpr(axpara);
    ZDeclList zdl = expr.getZSchText().getZDeclList();
    Pred pred = expr.getZSchText().getPred();
    
    // 1. if one schema only has State' as its declaration, then its precondition always holds   
    if(zdl.size() == 1 && zdl.get(0) instanceof InclDecl && 
        ((InclDecl)zdl.get(0)).getExpr() instanceof DecorExpr) {
      ret = true;
    }
    return ret;
  }
  
  
  /**
   * Get the paragraph name
   * 
   * @param para
   * @return
   */
  public static String getParaName(AxPara para)
  {
    ZSchText sch = ((ZSchText) para.getSchText());

    for (Decl decl : sch.getZDeclList()) {
      if (decl instanceof ConstDecl) {
        ConstDecl constdecl = ((ConstDecl) decl);
        return constdecl.getZName().getWord();
      }
    }
    return null;
  }
  
  /**
   * Get decl list from a simple schema
   * 
   * @param para
   * @return
   */
  public static List<Pair<ZName, Expr>> getDeclList(ZDeclList zdl)
  {
    List<Pair<ZName, Expr>> lstZNameExpr = new ArrayList<Pair<ZName, Expr>>();

    for(Decl decl: zdl) {
      if(decl instanceof VarDecl) {
        VarDecl vdecl = ((VarDecl)decl);
        Expr exp = vdecl.getExpr();
        for(Name name: vdecl.getZNameList()) {
          lstZNameExpr.add(new Pair<ZName, Expr>((ZName)name, exp));
        }
      } 
      else if(decl instanceof InclDecl) {
        InclDecl idecl = (InclDecl)decl;
      }
    }

    return lstZNameExpr;
  }
  
  public static String termToString(Term t)
  {
    String str = null;
    
    str = t.accept(new net.sourceforge.czt.circus.util.PrintVisitor());
    return str;
  }
  
  public static String printToString(Term term, String section, SectionManager manager) throws PrintException
  {
    StringWriter writer = new StringWriter();
    PrintUtils.print(term, writer, manager, section, Markup.LATEX);
    return writer.toString();
  }

  /**
   * Expand an applExpr (1..3) to a list of string [1,2,3]
   * @param ae
   * @return
   */
  public static Set<Pair<String, Expr>> expandApplExpr(ApplExpr ae)
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
        
        if (expr1 instanceof NumExpr && expr1 instanceof NumExpr) {
          String first = Circus2ZCSPUtils.termToString(expr1);
          String second = Circus2ZCSPUtils.termToString(expr2);
          for(int i = Integer.parseInt(first); i <= Integer.parseInt(second); i++) {
            NumExpr er = (NumExpr)ZUtils.cloneTerm(((TupleExpr)re).getZExprList().get(0));
            Numeral nl = fac.createZNumeral(BigInteger.valueOf(i));
            er.setNumeral(nl);
            ls.add(new Pair<String, Expr>(Integer.toString(i), er));
          }
        }
        else if (expr1 instanceof NumExpr && expr1 instanceof RefExpr) {
          
        }
        else if (expr1 instanceof RefExpr && expr1 instanceof NumExpr) {
          
        }
        else if (expr1 instanceof RefExpr && expr1 instanceof RefExpr) {
          
        }
        else {
          
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
  
  //copy the LocAnn and UndeclaredAnn from term1 to term2
  public static void cloneAnns(Term term1, Term term2)
  {
    if (term1.hasAnn())
    {
      for(Object obj : term1.getAnns())
      {
        if (obj instanceof Term)
        {
          Term ann = (Term)obj;
          Term cann = ZUtils.cloneTerm(ann);
          term2.getAnns().add(cann);
        }
        else
        {
          term2.getAnns().add(obj);
        }
      }
    }
  }
  
  public static <T1, T2>  List<T1> extractFirstfromListPair(List<Pair<T1, T2>> lstp)
  {
    List<T1> ret = new ArrayList<T1>();
    for(Pair<T1, T2> p: lstp) {
      ret.add(p.getFirst());
    }
    
    return ret;
  }
  
  public static <T1, T2>  List<T1> extractFirstfromListPair(Set<Pair<T1, T2>> lstp)
  {
    List<T1> ret = new ArrayList<T1>();
    for(Pair<T1, T2> p: lstp) {
      ret.add(p.getFirst());
    }
    
    return ret;
  }
  
  /**
   * Get the initialisation schema from a basicprocess
   *    an initialisation schema is a paragraph with the 
   *    name "Init", "P_Init", or its declaration only having
   *    the dashed state schema (S')
   * @param pp - a process paragraph
   * @return
   */
  public static Pred extractInitSchema(ZFactory fac, ProcessPara pp)
  {
    
    return extractInitSchema(fac, pp.getCircusBasicProcess(), pp.getZName());
  }
  
  /**
   * Get the initialisation schema from a basicprocess
   *    an initialisation schema is a paragraph with the 
   *    name "Init", "P_Init", or its declaration only having
   *    the dashed state schema (S')
   * TODO: how to support another forms of the initialisation schema, such as
   *    1. Init == schema expression or another_schema (where another_schema includes 
   *       dashed-state compoments)
   *    2. a simple schema but its declaration part includes partial dashed state components
   *       not all like S', but just s1',s2' and not mention s3' if S has three state components
   * @param bp - a basic process
   * @param pname - the process name
   * @return
   */
  public static Pred extractInitSchema(ZFactory fac, BasicProcess bp, ZName pname)
  {
    ZParaList zpl = bp.getZParaList();
    ZName stName = bp.getStateParaZName();
    
    for(Para p: zpl) {
      if(p instanceof AxPara) {
        if(ZUtils.isSimpleSchema(p)) {
          Expr e = ZUtils.getSchemaDefExpr(p);
          if(e != null && e instanceof SchExpr) {
            ZDeclList zdl = ((SchExpr)e).getZSchText().getZDeclList();
            if(zdl.size() == 1 && 
               zdl.get(0) instanceof InclDecl &&
               ((InclDecl)zdl.get(0)).getExpr() instanceof DecorExpr) {
              DecorExpr de = (DecorExpr) ((InclDecl)zdl.get(0)).getExpr();
              if(de.getExpr() instanceof RefExpr && 
                  ((RefExpr)de.getExpr()).getZExprList().isEmpty()) {
                if(Circus2ZCSPUtils.isEquals(((RefExpr)de.getExpr()).getZName(), stName)) {
                  return ((SchExpr)e).getZSchText().getPred();
                }
              }
            }
          }
        }
        else {
          // skip
        }
//        ZName paraName = (ZName) ZUtils.getAxParaSchOrAbbrName(p);
//        
//        if(paraName != null) {
//          String strName = Circus2ZCSPUtils.termToString(paraName);
//          // P_Init
//          String initName = MessageFormat.format(FormatPattern.PARAM_PROCESS_RENAMING_PATT,
//              Circus2ZCSPUtils.termToString(pname));
//          if(strName.equals(FormatPattern.Init_PARA_NAME_PATT) || 
//              strName.equals(initName)) {
//            return (AxPara)p;
//          }
//          
//          if(ZUtils.isSimpleSchema(p)) {
//            Expr e = ZUtils.getSchemaDefExpr(p);
//            if(e != null && e instanceof SchExpr) {
//              ZDeclList zdl = ((SchExpr)e).getZSchText().getZDeclList();
//            }
//          }
//        }
//        else {
//          // skip it
//        }
      } // end of if(p instanceof AxPara) 
    }
    
    return fac.createTruePred();
  }
  
  /**
   * type check a Z program
   * 
   * @param strSource - Z Specification by String
   */
  public static void typeCheck(String strSource)
  {
    SectionManager manager = new SectionManager(Dialect.Z);
    StringSource source = new StringSource(strSource, "resultantZSpec");
    source.setMarkup(Markup.LATEX);
    source.setEncoding("Default");
    
    manager.put(new Key<Source>("spec", Source.class), source);
    
    Spec spec;
    try {
      spec = manager.get(new Key<Spec>("spec", Spec.class));
      for (Sect sect : spec.getSect()) {
        // If the section is a ZSection
        if (sect instanceof ZSect) {
          ZSect zs = (ZSect) sect;
          String sectionName = zs.getName();

          manager.get(new Key<SectTypeEnvAnn>(sectionName, SectTypeEnvAnn.class));
        }
      }
    }
    catch (SectionInfoException e) {
      throw new CztException("Type check the resultant Z program failed. \n\t\t" + e.getMessage());
    }
    catch (CommandException e) {
      throw new CztException("Type check the resultant Z program failed. \n\t\t" + e.getMessage());
    }
  }
  
  /**
   * Output Z specification to file with default name and path in the manager.
   * @param circusSect - Circus section
   * @param zspec - Z specification in ISO
   * @param cspspec - CSP specification
   * @param manager - section manager
   */
  public static void outputZSpecToFile(ZSect circusSect, Spec zspec, SectionManager manager)
  {
    String path = manager.getProperty("czt.path");
    if(path == null) {
      path = "~/tmp/";
    }
    else if(path.startsWith("file:")) {
      path = path.substring(5);
    }
    String sectionName = ((ZSect)(zspec.getSect().get(0))).getName();
    String zfilename = path + "/" + sectionName + "_z.tex";
    outputZCSPSpecToFile(circusSect, manager, zspec, zfilename, null, null);
  }

  /**
   * Output Z and CSP specifications to files with default name and path in the manager.
   * @param circusSect - Circus section
   * @param zspec - Z specification in ISO
   * @param cspspec - CSP specification
   * @param manager - section manager
   */
  public static void outputZCSPSpecToFile(ZSect circusSect, Spec zspec, 
      CSPSpec cspspec, SectionManager manager)
  {
    String path = manager.getProperty("czt.path");
    if(path == null) {
      path = "~/tmp/";
    }
    else if(path.startsWith("file:")) {
      path = path.substring(5);
    }
    String sectionName = ((ZSect)(zspec.getSect().get(0))).getName();
    String zfilename = path + "/" + sectionName + "_z.tex";
    String cspfilename = path + "/" + sectionName + "_csp.csp";
    outputZCSPSpecToFile(circusSect, manager, zspec, zfilename, cspspec, cspfilename);
  }
  
  /**
   * Output Z and CSP specifications to files and terminal as well.
   * @param circusSect - Circus Section
   * @param manager - section manager
   * @param spec - Z specification in ISO
   * @param zfilename - filename for converted Z in ZRM
   * @param cspspec - CSP specification
   * @param cspfilename - filename for converted CSP
   */
  public static void outputZCSPSpecToFile(ZSect circusSect, SectionManager manager, Spec spec,  
      String zfilename, CSPSpec cspspec, String cspfilename)
  {
    String sectionName = "";
    StringWriter writer = new StringWriter();
    StringBuilder sbISO = new StringBuilder();
    StringBuilder sbZRM = new StringBuilder();
    
    String zheader = "% This file is automatically generated by the Circus2ZCSP Translator V" + VersionInfo.CUR_VERSION
            + "\n% on " + Calendar.getInstance().getTime() + "\n"
            + "% See https://github.com/RandallYe/Circus2ZCSP for more information.\n\n";
    String cspheader = "-- This file is automatically generated by the Circus2ZCSP Translator V" + VersionInfo.CUR_VERSION
            + "\n-- on " + Calendar.getInstance().getTime() + "\n"
            + "-- See https://github.com/RandallYe/Circus2ZCSP for more information.\n\n";

    for(Sect sect: spec.getSect()) {
      if (sect instanceof ZSect) {
        sectionName = ((ZSect) sect).getName();
        // Transform [ISO Z to ZRM: \Omega_2]
        Omega2Visitor o2visitor = new Omega2Visitor();
        sect.accept(o2visitor);
        
        List<ZName> lstSchNames = o2visitor.getLstSchNames();
        List<String> lstStrSchNames = new ArrayList<String>();
        
        // get all lambda/mu/let expressions
        LetMuLambdaVisitor lmlvisitor = new LetMuLambdaVisitor();
        sect.accept(lmlvisitor);
        List<Term> lstTerm = lmlvisitor.getListTerms();
        List<String> lstStr = new ArrayList<String>();
        
        try {
          PrintUtils.print(spec, writer, manager, sectionName, Markup.LATEX);
          for(Term t: lstTerm) {
            StringWriter w = new StringWriter();
            PrintUtils.print(t, w, manager, sectionName, Markup.LATEX);
            lstStr.add(w.toString());
          }
          
          for(ZName n: lstSchNames) {
            StringWriter w = new StringWriter();
            PrintUtils.print(n, w, manager, sectionName, Markup.LATEX);
            lstStrSchNames.add(w.toString());
          }
        }
        catch (PrintException e) {
          throw new CztException("Print a Z specification to a writer fail. \n\t\t" + e.getMessage());
        }
        
        Debug.debug_print("================= [Start] Section [" + sectionName + "] ===================");
        Debug.debug_print("================= [Start] Z in ISO Z ======================");
        Debug.debug_print(writer.toString());
        Debug.debug_print("================= [End] Z in ISO Z ========================");  
        
        String isoz = writer.toString();
        {
          Pattern regex = Pattern.compile("\\\\circif", Pattern.DOTALL | Pattern.MULTILINE);
          Matcher matcher = regex.matcher(isoz);
          isoz = matcher.replaceAll("\\\\IF");
        }
        
        if(isoz.contains("\\boolean")) {
          Pattern regex = Pattern.compile("\\\\end\\{zsection\\}", Pattern.DOTALL | Pattern.MULTILINE);
          Matcher matcher = regex.matcher(isoz);
          isoz = matcher.replaceAll("\\\\end\\{zsection\\} \n"
              + "\n"
              + "\\\\begin{zed}Boolean ::= True | False \n\\\\end{zed}");
          isoz = isoz.replaceAll("\\\\boolean", "Boolean").replaceAll("\\\\true", "True").replaceAll("\\\\false", "False");
        }

        Debug.debug_print("================= [Start] Z in ISO Z ======================");
        Debug.debug_print(isoz);
        FileOutputStream zstream;
        try {
          // isoz spec
          zstream = new FileOutputStream(zfilename + ".iso");
          Writer zwriter = new OutputStreamWriter(zstream);
          zwriter.write(zheader + isoz);
          zwriter.close();
        }
        catch (FileNotFoundException e) {
          throw new CztException("Create file fail. \n\t\t" + e.getMessage());
        }
        catch (IOException e) {
          throw new CztException("Write file fail. \n\t\t" + e.getMessage());
        }
        
        Debug.debug_print("================= [End] Z in ISO Z ========================");  

        Debug.debug_print("================= [Start] Type Check ======================");
        typeCheck(isoz);
        Debug.debug_print("================= [End] Type Check Done ===================");
        
        String strISO = isoz;
        
        // add additional parenthesis for let/mu/lambda expression
        for(String s: lstStr) {
          Pattern regex = Pattern.compile(s, Pattern.LITERAL | Pattern.MULTILINE);
          Matcher matcher = regex.matcher(strISO);
          strISO = matcher.replaceAll("(" + s.replace("\\", "\\\\") + ")");
        }
        
        // for singleton schema set, add additional parenthesis
        // { sch } => { (sch) }
        for(String s: lstStrSchNames) {
          Pattern regex = Pattern.compile("\\{ " + s + " \\}", Pattern.LITERAL | Pattern.MULTILINE);
          Matcher matcher = regex.matcher(strISO);
          strISO = matcher.replaceAll("\\\\{ ( " + s.replace("\\", "\\\\") + " ) \\\\}");
        }
        
        sbISO.append(strISO);
        
        // convert from ISO Z to ZRM
        String zrm = ISOZ2ZRM.convert(circusSect, (ZSect)sect, strISO);
        Debug.debug_print("================= [Start] Z in ZRM ========================");
        Debug.debug_print(zrm);
        Debug.debug_print("================= [End] Z in ZRM ========================");
        sbZRM.append(zrm);
      }
    }

    if(cspspec != null) {
      Debug.debug_print("================= [Start] CSP ========================");
      Debug.debug_print("\n" + cspspec.toString());
      Debug.debug_print("================= [End] CSP ========================");
    }
    
    FileOutputStream zstream,cspstream;
    try {
      // z spec
      zstream = new FileOutputStream(zfilename);
      Writer zwriter = new OutputStreamWriter(zstream);
      zwriter.write(zheader + sbZRM.toString());
      zwriter.close();
      
      if(cspspec != null) {
        cspstream = new FileOutputStream(cspfilename);
        Writer cspwriter = new OutputStreamWriter(cspstream);
        cspwriter.write(cspheader + cspspec.toString());
        cspwriter.close();
      }
    }
    catch (FileNotFoundException e) {
      throw new CztException("Create file fail. \n\t\t" + e.getMessage());
    }
    catch (IOException e) {
      throw new CztException("Write file fail. \n\t\t" + e.getMessage());
    }

//    Debug.debug_print("outputZCSPSpecToFile Done!");
    Debug.debug_print("outputZCSPSpecToFile Done!");
    System.out.println("Done!");
  }
  
  /**
   * split a tuple text "(a, b)" or "((a), (b)) into a list of "[a, b]" or "[(a), (b)]
   * @param istr
   * @param lstr
   * @return
   */
  public static boolean split_a_tuple(String istr, List<String> lstr)
  {
    
    /*
     * Regular expression is not able to handle nested structure like ((),[]) etc
     */
    // tuples like "(state, #A)" or "(state, Set(x))"
    // "[\\w\\p{Punct}]+" matches word or punctuation
    // \w - A word character: [a-zA-Z_0-9]
    // \p{Punct} - Punctuation: One of !"#$%&'()*+,-./:;<=>?@[\]^_`{|}~
/*    if (istr.matches("\\(([\\w\\p{Punct}]+), *([\\w\\p{Punct}]+)\\)")) {
      // tuple
      String str = istr.replaceAll("\\(([\\w\\p{Punct}]+), *([\\w\\p{Punct}]+)\\)", "$1,$2");
      String[] strs = str.split(",");

      if (strs.length == 2) {
        lstr.add(strs[0]);
        lstr.add(strs[1]);
        return true;
      }
      return false;
    }
*/
    /*
     * 1. remove white space
     */
    String inStr = istr.trim();
    char[] inChars = inStr.toCharArray();
    String[] strs = {"", ""};
    
    // counter for (), [], {}
    int openBracket = 0;
    
    if(!inStr.startsWith("(") || !inStr.endsWith(")")) {
      return false;
    }
    
    int j = 0;
    for(int i = 0; i < inChars.length; i++) {
      // open brackets
      if(inChars[i] == '(' || inChars[i] == '[' || inChars[i] == '{') {
        openBracket++;
        if(openBracket > 1) {
          strs[j] += inChars[i];
        }
      }
      // close brackets
      else if(inChars[i] == ')' || inChars[i] == ']' || inChars[i] == '}') {
        openBracket--;
        if(openBracket > 0) {
          strs[j] += inChars[i];
        }
      }
      else if(inChars[i] == ',') {
        // if openBracket is 1, then ',' is a split of the tuple
        if(openBracket == 1) {
          j++;
        }
        // otherwise, ',' belongs to one of element in tuple
        else {
          strs[j] += inChars[i];
        }
      }
      else {
        strs[j] += inChars[i];
      }
      
      if(i == inChars.length - 1 && openBracket == 0) {
        lstr.add(strs[0].trim());
        lstr.add(strs[1].trim());
        return true;
      }
    }

    return false;
  }
  
  /**
   * check if str contains substr but ignore all white spaces
   * @param str
   * @param substr
   * @return
   */
  public static boolean isStringContains(String str, String substr)
  {
    boolean ret = false;
    
    ret = str.replaceAll("\\s+", "").contains(substr.replaceAll("\\s+", ""));
    return ret;
  }
  
  /**
   * check if str matches regex
   * @param str
   * @param regex
   * @return
   */
  public static boolean isStringMatch(String str, String regex)
  {
    Pattern patt = Pattern.compile(regex, Pattern.DOTALL | Pattern.MULTILINE);
    Matcher matcher = patt.matcher(str);
    return matcher.find();
  }
  
  /**
   * get how many match substring found
   * @param str
   * @param regex
   * @return
   */
  public static int getStringMatchCount(String str, String regex)
  {
    int ret = 0;
    Pattern patt = Pattern.compile(regex, Pattern.DOTALL | Pattern.MULTILINE);
    Matcher matcher = patt.matcher(str);

    while(matcher.find()) {
      ret++;
    }
    return ret;
  }
  
  public static SpecStmtKind getSpecStmtKind(SpecStmtCommand spec)
  {
    if(spec.getZFrame().isEmpty()) {
      if(spec.getPre() instanceof TruePred) {
        return SpecStmtKind.ASSUMPTION;
      }
      else if(spec.getPost() instanceof TruePred) {
        return SpecStmtKind.COERCION;
      }
    }
    
    return SpecStmtKind.SPECIFICATION;
  }
  
  /**
   * Normalise a schema by EXPANSION_RULES
   * This does not work as expected since in the predicate part, the references are not solved, 
   * for example
   * [DEBUG] Before expansion: normalize [ AnalyserState | 
   *    stops \geq 3 \lor DangerZone \lor emergencyCond = 1 \lor transmissionFailure \in signals ]
   * [DEBUG] After expansion: [ qa\_ 1 : \arithmos ; qa\_ 2 : \arithmos ; qst : SState ; va\_ 1 : \arithmos ; 
   *    va\_ 2 : \arithmos ; vst : SState ; pumpctr : \power ( \arithmos \cross [ pa\_ 1 : \arithmos ; 
   *    pa\_ 2 : \arithmos ; pst : PState ; pcst : PCState | true ] ) ; pta\_ 1 : \arithmos ; pta\_ 2 : \arithmos ; 
   *    valve : VState ; qc\_ 1 : \arithmos ; qc\_ 2 : \arithmos ; vc\_ 1 : \arithmos ; vc\_ 2 : \arithmos ; 
   *    expectedp : \power ( \arithmos \cross PState ) ; expectedpc : \power ( \arithmos \cross PCState ) ; 
   *    failures : \power UnitFailure ; noacks : \power UnitFailure ; signals : \power InputSignal ; 
   *    pumpState : \power ( \arithmos \cross PState ) ; pumpCtrState : \power ( \arithmos \cross PCState ) ;
   *    q : \arithmos ; v : \arithmos ; failureacks : \power UnitFailure ; repairs : \power UnitFailure ; 
   *    stops : \arithmos ; signalhistory : \power InputSignal ; emergencyCond : \arithmos 
   *  | AnalyserState \land ( stops \geq 3 \lor DangerZone \lor emergencyCond = 1 \lor transmissionFailure \in signals ) ]
   *  
   * @param expr
   * @param sectName
   * @param manager
   * @return
   */
  public static SchExpr expansionSchema(Expr expr, String sectName, SectionManager manager)
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
//      Spec spec = manager_.get(new Key<Spec>("spec", Spec.class));
//      String sectionName = ((ZSect)spec.getSect().get(0)).getName();
      
      Expr applExpr = RewriteUtils.createNormalizeAppl(expr);
      
      Debug.debug_print("Before expansion: " + Circus2ZCSPUtils.printToString(applExpr, sectName, manager));
      Term rew_term = Strategies.innermost(applExpr, rules, manager, sectName);
      if(rew_term instanceof SchExpr) {
        ret = (SchExpr)rew_term;
      }
      else if(rew_term instanceof ApplExpr) {
        if(
            (((ApplExpr)rew_term).getLeftExpr() instanceof RefExpr) && 
            (((ApplExpr)rew_term).getRightExpr() instanceof SchExpr)) {
          if(((RefExpr)((ApplExpr)rew_term).getLeftExpr()).getZName().getWord().equals("normalize")) {
            ret = (SchExpr)((ApplExpr)rew_term).getRightExpr();
          }
        }
      }
      
      Debug.debug_print("After expansion: " + Circus2ZCSPUtils.printToString(rew_term, sectName, manager));
    }
    catch (UnboundJokerException e) {
      throw new CztException("Expand schema expression: ", e);
    }
    catch (CommandException e) {
      throw new CztException("Expand schema expression: ", e);
    }
    catch (Exception e) {
      WarningManager warning_manager = new WarningManager();
      warning_manager.warn("Failed to expand schema expression \n\t\t" + e.getMessage() + "\nand just ignored.");
    }

    return ret;
  }
  
  /**
   * Check if two ZNames are equal by ignoring their Id
   * @param name1
   * @param name2
   * @return
   */
  public static boolean isEquals(ZName name1, ZName name2) 
  {
    if(name1 != null) {
      name1.setId(null);
    }
    if(name2 != null) {
      name2.setId(null);
    }
    
    if(name1 != null){
      return name1.equals(name2);
    }
    else if (name2 != null){
      return name2.equals(name1);
    }
    else {
      return true;
    }
  }
  
  /**
   * Check if two terms are equal by ignoring their Id in all ZNames
   * @param t1 - term one
   * @param t2 - term two
   * @return
   */
  public static boolean isEquals(Term t1, Term t2) 
  {
    class ClearZNameIdVisitor
      implements ZNameVisitor<Object>, TermVisitor<Object>
    {
      @Override
      public Object visitZName(ZName term)
      {
        term.setId(null);
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
    }
    
    ClearZNameIdVisitor visitor = new ClearZNameIdVisitor();
    Term tempT1 = ZUtils.cloneTerm(t1);
    Term tempT2 = ZUtils.cloneTerm(t2);
    tempT1.accept(visitor);
    tempT2.accept(visitor);
    
    return tempT1.equals(tempT2);
  }
  
  /**
   * Get the definition of name from map and return its value (Set<Node>) if found. Otherwise, return null.
   * @param name - name to find
   * @param refmap - map to search
   * @param process_para - A process paragraph that this ZName belongs to
   * @param set_node - [OUT] its value (Set<Node>)
   * @return
   *    the key of entry with the specific name, return null if not found
   */
  public static Node getADefFromMap(Map<Node, Set<Node>> refmap, ZName name, 
      ProcessPara process_para, Set<Node> set_node)
  {
    set_node.clear();
    
    // global definition
    name.setId(null);
    Node globalNode = new Node(name, (ZName)null);
    Set<Node> setNode = refmap.get(globalNode);
    
    if(setNode != null && !setNode.isEmpty()) {
      // found
      set_node.addAll(setNode);
      return globalNode;
    }
    
    for(Map.Entry<Node, Set<Node>> entry: refmap.entrySet()) {
      Node n = entry.getKey();
      Set<Node> sn = entry.getValue();

      if(n.getName().equals(name)) {
        if(n.getProcess() == null) {
          // global name, found it
        }
        else {
          if(process_para == null) {
            // not found
            Debug.debug_print(
                Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
                Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
                Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
                "Found a " + name + " in " + n.getProcess() + " but current search scope is global!");
            // Additional check if a global definition depends on a local definition in Circus, but if this 
            // global definition (such as channel definition) and the n.getName found are from the same process,
            // even current search scope is globally, we still regard it is valid entry for the name to be searched.
            //
            // for example, if the search scope is channel declaration, but it is from the assignment in a process,
            // high possibly, the type of channel may come from the definition in the process.
            String procPrefix = MessageFormat.format(FormatPattern.RENAMING_IN_PROC, 
                Circus2ZCSPUtils.termToString(n.getProcess()),
                "");
            if(Circus2ZCSPUtils.termToString(name).startsWith(procPrefix)) {
              // found it
            }
            else {
              continue;
            }
          }
          else {
            if(n.getProcess().equals(process_para.getZName())) {
              // local name, found it
            }
            else {
              // no found
              continue;
            }
          }
        }
              
        set_node.addAll(sn);
        return n;
      }
    }
    
    return null;
  }
  
  public static String printANode(Node n)
  {
    String ret = "";
    ret += "(" + ((n.getName() == null)?"null": n.getName().toString()) + ", " + 
        (n.getProcess() == null? "null": n.getProcess().toString()) + ")";
    
    return ret;
  }
  
  public static void printRefMap(Map<Node, Set<Node>> refmap)
  {
    Debug.debug_print(          
        Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
        Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
        Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
        "###################### [Start] Ref Map #####################");
    for(Map.Entry<Node, Set<Node>> entry: refmap.entrySet()) {
      Node n = entry.getKey();
      Set<Node> sn = entry.getValue();
      String str = "";
      boolean first = false;
      
      for(Node node: sn) {
        if(!first) {
          first = true;
        }
        else {
          str += ", ";
        }
        str += printANode(node);
      }
      
      Debug.debug_print(
          Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
          Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
          Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
          "[" + printANode(n) + "]: " + str);
    }
    
    Debug.debug_print(
        Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
        Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
        Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
        "###################### [End] Ref Map #####################");
  }
  
  /**
   * Update r in its parent to e
   * @param stack_parent - a stack of the r's parent term
   * @param r - original expression
   * @param e - new expression 
   */
  public static void updateParentRef(Stack<Term> stack_parent, Expr r, Expr e)
  {
    Term parent;
    if(stack_parent.size() >= 2) {
      parent = stack_parent.get(stack_parent.size() - 2);
    }
    else {
      throw new CztException(Circus2ZCSPUtils.termToString(r) + " has no parent!");
    }
    
    // if a RefExpr's parent is an expression as well,
    if(parent instanceof Expr) {
      if(parent instanceof Expr0N) {
        ZExprList zel = ((Expr0N)parent).getZExprList();
        for(int i = 0; i < zel.size(); i++) {
          // replace r by e
          if(zel.get(i).equals(r)) {
            zel.remove(i);
            zel.add(i, e);
          }
        }
        ((Expr0N)parent).setExprList(zel);
      }
      else if(parent instanceof Expr1) {
        if(((Expr1)parent).getExpr().equals(r)) {
          ((Expr1)parent).setExpr(e);
        }
      }
      else if(parent instanceof Expr2) {
        if(((Expr2)parent).getLeftExpr().equals(r)) {
          ((Expr2)parent).setLeftExpr(e);
        }
        
        if(((Expr2)parent).getRightExpr().equals(r)) {
          ((Expr2)parent).setRightExpr(e);
        }
      }
      else if(parent instanceof CondExpr) {
//        Term pparent;
//        if(stack_parent_.size() >= 3) {
//          pparent = stack_parent_.get(stack_parent_.size() - 3);
//        }
//        else {
//          throw new CztException(Circus2ZCSPUtils.termToString(r) + "'s parent " + Circus2ZCSPUtils.termToString(parent) + "has no parent!");
//        }
        
        Expr le = ((CondExpr)parent).getLeftExpr();
        Expr re = ((CondExpr)parent).getRightExpr();
        // for CondExpr (if p then e1 else e2), there is no setExpr operations.
        if(((CondExpr)parent).getLeftExpr().equals(r)) {
          le = e;
        }
        
        if(((CondExpr)parent).getRightExpr().equals(r)) {
          re = e;
        }
        
        CircusFactory fac = new net.sourceforge.czt.circus.impl.CircusFactoryImpl();
        List<Expr> lstExpr = new ArrayList<Expr>();
        lstExpr.add(le);
        lstExpr.add(re);
        CondExpr ce = fac.createCondExpr(((CondExpr)parent).getPred(), lstExpr);
        // recursively to replace [e/r]
        Term p = stack_parent.pop();
        updateParentRef(stack_parent, (CondExpr)parent, ce);
        // restore
        stack_parent.push(p);
      }
      else if(parent instanceof JokerExpr) {
        throw new CztException(Circus2ZCSPUtils.termToString(r) + "'s parent should not be JokerExpr!");
      }
      else if(parent instanceof QntExpr) {
        if (((QntExpr)parent).getExpr().equals(r)) {
          ((QntExpr)parent).setExpr(e);
        }
      }
      else if(parent instanceof SigmaExpr) {
        if (((SigmaExpr)parent).getValue().equals(r)) {
          ((SigmaExpr)parent).setValue(e);
        }
      }
    }
    else if(parent instanceof Decl) {
      if(parent instanceof InclDecl) {
        if(((InclDecl)parent).getExpr().equals(r)) {
          ((InclDecl)parent).setExpr(e);
        }
      }
      else if(parent instanceof QualifiedDecl) {
        if(((QualifiedDecl)parent).getExpr().equals(r)) {
          ((QualifiedDecl)parent).setExpr(e);
        }
      }
      else if(parent instanceof VarDecl) {
        if(((VarDecl)parent).getExpr().equals(r)) {
          ((VarDecl)parent).setExpr(e);
        }
      }
    }
    else if(parent instanceof Communication) {
      if(((Communication)parent).getChannelExpr().equals(r)) {
        ((Communication)parent).setChannelExpr((RefExpr)e);
        if(e instanceof RefExpr) {
          RefExprKind kind = Circus2ZCSPUtils.getRefExprKind((RefExpr)r);
          switch(kind) {
            case GEN_OP_APPL:
              break;
            case OP_APPL:
              break;
            case GEN_REF:
              break;
            case REF:
              if(((Communication)parent).getCommUsage().equals(CommUsage.Generic)) {
                ((Communication)parent).setCommUsage(CommUsage.Normal);
              }
              break;
            default:
          }
        }
      }
    }
    else if(parent instanceof DotField) {
      if(((DotField)parent).getExpr().equals(r)) {
        ((DotField)parent).setExpr(e);
      }
    }
    else if(parent instanceof InputField) {
      throw new CztException(Circus2ZCSPUtils.termToString(r) + "'s parent should not be InputField!");
    }
    else if(parent instanceof Pred) {
      if(parent instanceof ExprPred) {
        if(((ExprPred)parent).getExpr().equals(r)) {
          ((ExprPred)parent).setExpr(e);
        }
      }
      else if(parent instanceof MemPred) {
        if(((MemPred)parent).getLeftExpr().equals(r)) {
          ((MemPred)parent).setLeftExpr(e);
        }
        
        if(((MemPred)parent).getRightExpr().equals(r)) {
          ((MemPred)parent).setRightExpr(e);
        }
      }
    }
    else if(parent instanceof CircusNameSet) {
      throw new CztException(Circus2ZCSPUtils.termToString(r) + "'s parent should not be CircusNameSet!");
    }
    else if(parent instanceof AxPara) {
      AxPara para = (AxPara)parent;
      if(null != ZUtils.getAxBoxDecls(para)) {
        // Axiomatic definition
      }
      else if(ZUtils.isAbbreviation(para)) {
        Expr ae = ZUtils.getAbbreviationExpr(para);
        if(ae.equals(r)) {
          ((ConstDecl)para.getZSchText().getZDeclList().get(0)).setExpr(e);
        }
      }
      else if(ZUtils.isSimpleSchema(para)) {
        Expr se = ZUtils.getSchemaDefExpr(para);
        if(se.equals(r)) {
          ((ConstDecl)para.getZSchText().getZDeclList().get(0)).setExpr(e);
        }
      }
    }
    else if(parent instanceof CallProcess) {
      if(((CallProcess)parent).getCallExpr().equals(r)) {
        ((CallProcess)parent).setCallExpr((RefExpr) e);
      }
    }
    else if(parent instanceof ZExprList) {
      for(int i = 0; i < ((ZExprList)parent).size(); i++) {
        if(((ZExprList)parent).get(i).equals(r)) {
          ((ZExprList)parent).set(i, e);
        }
      }
    }
    else if(parent instanceof ListTerm) {
      @SuppressWarnings("unchecked")
      ListTerm<Term> lst = (ListTerm<Term>)parent;
      for(int i = 0; i < lst.size(); i++) {
        if(lst.get(i).equals(r)) {
          lst.set(i, e);
        }
      }
    }
    else {
      throw new CztException(Circus2ZCSPUtils.termToString(r) + 
          "'s parent should not be [" + parent.getClass()+ "] !");
    }
  }
  
  /**
   * Update r in its parent to e
   * @param stack_parent - a stack of the r's parent term
   * @param r - original expression, should be RefExpr that contains a name of schema
   * @param e - new predicate 
   */
  public static void updateParentRef(Stack<Term> stack_parent, Expr r, Pred e)
  {
    Term parent;
    if(stack_parent.size() >= 2) {
      parent = stack_parent.get(stack_parent.size() - 2);
    }
    else {
      throw new CztException(Circus2ZCSPUtils.termToString(r) + " has no parent!");
    }
    
    Term grandparent = null;
    
    if(parent instanceof ListTerm) {
      ListTerm<Term> lst = (ListTerm)parent;
      for(int i = 0; i < lst.size(); i++) {
        if(lst.get(i) instanceof ExprPred) {
          if(((ExprPred)lst.get(i)).getExpr().equals(r)) {
            lst.set(i, e);
          }
        }
      }
    }
    if(parent instanceof ExprPred) {
      ExprPred ep = (ExprPred)parent;
      if(ep.getExpr().equals(r)) {
        // replace ExprPred by the predicate provide
        if(stack_parent.size() >= 3) {
          grandparent = stack_parent.get(stack_parent.size() - 3);
        }
      }
    }
  }
 
  /**
   * Update r in its parent to e
   * @param stack_parent - a stack of the r's parent term
   * @param r - original ExprPred
   * @param e - new predicate
   */
  public static void updateParentRef(Stack<Term> stack_parent, ExprPred r, Pred e)
  {
    Term parent;
    if(stack_parent.size() >= 2) {
      parent = stack_parent.get(stack_parent.size() - 2);
    }
    else {
      throw new CztException(Circus2ZCSPUtils.termToString(r) + " has no parent!");
    }
    
    if(parent instanceof ListTerm) {
      ListTerm<Term> lst = (ListTerm)parent;
      for(int i = 0; i < lst.size(); i++) {
        if(lst.get(i).equals(r)) {
          lst.set(i, e);
        }
      }
    }
    // Expr
    else if(parent instanceof CondExpr) {
      CondExpr ce = (CondExpr)parent;
      if(ce.getPred().equals(r)) {
        ce.setPred(e);
      }
    }
    else if(parent instanceof QntExpr) {
      QntExpr qe = (QntExpr)parent;
      if(qe.getZSchText().getPred().equals(r)) {
        qe.getZSchText().setPred(e);
      }
    }
    else if(parent instanceof SchExpr) {
      SchExpr qe = (SchExpr)parent;
      if(qe.getZSchText().getPred().equals(r)) {
        qe.getZSchText().setPred(e);
      }
    }
    // Pred
    else if(parent instanceof NegPred) {
      NegPred qe = (NegPred)parent;
      if(qe.getPred().equals(r)) {
        qe.setPred(e);
      }
    }
    else if(parent instanceof Pred2) {
      Pred2 qe = (Pred2)parent;
      if(qe.getLeftPred().equals(r)) {
        qe.setLeftPred(e);
      }

      if(qe.getRightPred().equals(r)) {
        qe.setRightPred(e);
      }
    }
    else if(parent instanceof QntPred) {
      QntPred qe = (QntPred)parent;
      if(qe.getPred().equals(r)) {
        qe.setPred(e);
      }
    }
    // others
    else if(parent instanceof GuardedAction) {
      GuardedAction qe = (GuardedAction)parent;
      if(qe.getPred().equals(r)) {
        qe.setPred(e);
      }
    }
    else {
      throw new CztException(Circus2ZCSPUtils.termToString(r) + 
          "'s parent should not be [" + parent.getClass()+ "] !");
    }
  }
  
  public static String printAxPara2String(AxPara ap)
  {
//    net.sourceforge.czt.z.ast.AxPara ap = this;
    net.sourceforge.czt.z.ast.Expr expr;
    net.sourceforge.czt.z.ast.ZName name;
    StringBuilder sb = new StringBuilder();
    boolean generic = !ap.getZNameList().isEmpty();
    String formals = "";
    boolean first = true;
    net.sourceforge.czt.z.util.PrintVisitor visitor = new net.sourceforge.czt.z.util.PrintVisitor();
    
    if(generic) {
      formals += "Generic formals: [";
      for(net.sourceforge.czt.z.ast.Name n: ap.getZNameList()) {
        if(first) {
          first = false;
        }
        else {
          formals += ", ";
        }
        formals += n.accept(visitor);
      }
      formals += "]\n";
    }
  
    sb.append(formals);
  
    if(ap.getBox().equals(net.sourceforge.czt.z.ast.Box.AxBox)) {
      net.sourceforge.czt.z.ast.ZDeclList list = net.sourceforge.czt.z.util.ZUtils.getAxBoxDecls(ap);
      net.sourceforge.czt.z.ast.Pred pred = net.sourceforge.czt.z.util.ZUtils.getAxBoxPred(ap);
      sb.append("Axdef: [");
  
      for(net.sourceforge.czt.z.ast.Decl decl: list) {
        if(decl instanceof net.sourceforge.czt.z.ast.VarDecl) {
          sb.append(decl.accept(visitor));
          sb.append(",");
        }
      }
      
      sb.append(" | ");
      sb.append(pred.accept(visitor));
      sb.append("]");
    }
    else if(ap.getBox().equals(net.sourceforge.czt.z.ast.Box.OmitBox)) {
      net.sourceforge.czt.z.ast.ConstDecl cdecl = (net.sourceforge.czt.z.ast.ConstDecl)ap.getZSchText().getZDeclList().get(0);
      if(cdecl.getExpr() instanceof net.sourceforge.czt.z.ast.SchExpr) {
        name = (net.sourceforge.czt.z.ast.ZName) net.sourceforge.czt.z.util.ZUtils.getAxParaSchOrAbbrName(ap);
        expr = net.sourceforge.czt.z.util.ZUtils.getSchemaDefExpr(ap);
        
        sb.append("Horizonal Schema: ");
        sb.append(name.accept(visitor));
        sb.append(" = ");
        sb.append(expr.accept(visitor));
      }
      else {
        name = (net.sourceforge.czt.z.ast.ZName) net.sourceforge.czt.z.util.ZUtils.getAbbreviationName(ap);
        expr = net.sourceforge.czt.z.util.ZUtils.getAbbreviationExpr(ap);
        sb.append("Abbreviation: ");
        sb.append(name.accept(visitor));
        sb.append(" == ");
        sb.append(expr.accept(visitor));
      }
    }
    else {//if(ap.getBox().equals(net.sourceforge.czt.z.ast.Box.SchBox)) {
      name = (net.sourceforge.czt.z.ast.ZName) net.sourceforge.czt.z.util.ZUtils.getAxParaSchOrAbbrName(ap);
      expr = net.sourceforge.czt.z.util.ZUtils.getSchemaDefExpr(ap);
      
      sb.append("Boxed Schema: ");
      sb.append(name.accept(visitor));
      sb.append(" = ");
      sb.append(expr.accept(visitor));
    }
    return sb.toString();
  }
//  {
//    AxParaKind kind = Circus2ZCSPUtils.getAxParaKind(ap);
//    Expr expr;
//    ZName name;
//    StringBuilder sb = new StringBuilder();
//    
//    switch(kind) {
//      case ABBR:
//        name = (ZName) ZUtils.getAbbreviationName(ap);
//        expr = ZUtils.getAbbreviationExpr(ap);
//        sb.append("Abbreviation: ");
//        sb.append(termToString(name));
//        sb.append(" == ");
//        sb.append(termToString(expr));
//        break;
//      case AXDEF:
//        ZDeclList list = ZUtils.getAxBoxDecls(ap);
//        Pred pred = ZUtils.getAxBoxPred(ap);
//        
//        sb.append("Axdef: [");
//
//        for(Decl decl: list) {
//          if(decl instanceof VarDecl) {
//            sb.append(termToString(decl));
//            sb.append(",");
//          }
//        }
//        
//        sb.append(" | ");
//        sb.append(termToString(pred));
//        break;
//      case BOXED_SCHEMA:
//      case HORIZON_SCHEMA:
//        name = (ZName) ZUtils.getAxParaSchOrAbbrName(ap);
//        expr = ZUtils.getSchemaDefExpr(ap);
//        
//        sb.append("Schema: ");
//        sb.append(termToString(name));
//        sb.append(" = ");
//        sb.append(termToString(expr));
//
//        break;
//      default:
//          break;
//    }
//    
//    return sb.toString();
//  }
  
  static public String repeatString(String str, int n)
  {
    return new String(new char[n]).replace("\0", str);
  }
  
  /**
   * Check if the given name is a reference to a schema name (Schema or Abbreviation)
   * @param name
   * @return
   */
  public static boolean isARefToSchema(ZName name, ZSect zs, ProcessPara process) 
  {
    boolean found = false;
    
    List<Para> lstPara = new ArrayList<Para>();

    if(zs != null) {
      lstPara.addAll(zs.getZParaList());
    }
    
    if(process != null && process.getCircusProcess() instanceof BasicProcess) {
      lstPara.addAll(process.getCircusBasicProcess().getZParaList());
    }
    
    for(Para p: lstPara) {
      if(p instanceof AxPara) {
        AxPara ap = (AxPara)p;
        AxParaKind apkind = Circus2ZCSPUtils.getAxParaKind(ap);
        ZName apname = null;
        Expr expr = null;
        
        switch(apkind) {
          case ABBR:
            apname = (ZName) ZUtils.getAbbreviationName(ap);
            if(Circus2ZCSPUtils.isEquals(name, apname)) {
              found = true;
              expr = ZUtils.getAbbreviationExpr(ap);
            }
            break;
          case BOXED_SCHEMA:
          case HORIZON_SCHEMA:
            apname = (ZName) ZUtils.getSchemaName(ap);
            if(Circus2ZCSPUtils.isEquals(name, apname)) {
              found = true;
              expr = ZUtils.getSchemaDefExpr(ap);
            }
            break;
          default:
            break;
        }
        
        if(found && expr != null) {
          if(isSchemaExpr(expr, zs, process)) {
            return true;
          }
        }
      }
      
      if(found) {
        break;
      }
    }
    
    return false;
  }
  
  /**
   * Check if an expression is a schema expression or not
   * @param expr
   * @param zs - Circus ZSect
   * @param process - process paragraph
   * @return
   *    true - a schema expression. Otherwise, not
   */
  public static boolean isSchemaExpr(Expr expr, ZSect zs, ProcessPara process) 
  {
    if(expr instanceof RefExpr) {
      return isARefToSchema(((RefExpr)expr).getZName(), zs, process);
    }
    
    if(expr instanceof SchExpr ||
        expr instanceof SchExpr2 || 
        expr instanceof NegExpr || 
        expr instanceof ThetaExpr || 
        expr instanceof HideExpr || 
        expr instanceof RenameExpr ||
        expr instanceof PreExpr ||
        expr instanceof DecorExpr) {
      return true;
    }
    else if(expr instanceof Qnt1Expr) {
      return isSchemaExpr(((Qnt1Expr)expr).getExpr(), zs, process);
    }
    
    return false;
  }
  
  /**
   * Check if an expression is a schema expression or not
   * @param expr
   * @return
   *    true - a schema expression. Otherwise, not
   */
  public static boolean isSchemaExpr(Expr expr) 
  {
    if(expr instanceof SchExpr ||
        expr instanceof SchExpr2 || 
        expr instanceof NegExpr || 
        expr instanceof ThetaExpr || 
        expr instanceof HideExpr || 
        expr instanceof RenameExpr ||
        expr instanceof PreExpr ||
        expr instanceof DecorExpr) {
      return true;
    }
    else if(expr instanceof Qnt1Expr) {
      return isSchemaExpr(((Qnt1Expr)expr).getExpr());
    }
    
    return false;
  }  
}

class LetMuLambdaVisitor
  implements
    TermVisitor<Object>,
    LetExprVisitor<Object>,
    MuExprVisitor<Object>,
    LambdaExprVisitor<Object>
{
  private List<Term> lst_term_ = new ArrayList<Term>();
  
  public List<Term> getListTerms() 
  {
    return lst_term_;
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
  public Object visitLambdaExpr(LambdaExpr term)
  {
    lst_term_.add(term);
    return null;
  }

  @Override
  public Object visitMuExpr(MuExpr term)
  {
    lst_term_.add(term);
    return null;
  }

  @Override
  public Object visitLetExpr(LetExpr term)
  {
    lst_term_.add(term);
    return null;
  }
}
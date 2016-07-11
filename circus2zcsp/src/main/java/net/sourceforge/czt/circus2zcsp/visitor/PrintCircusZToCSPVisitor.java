/*
 * 
 */

package net.sourceforge.czt.circus2zcsp.visitor;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Random;
import java.util.Set;
import java.util.Stack;
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
import net.sourceforge.czt.circus2zcsp.data.PredExpPattern;
import net.sourceforge.czt.circus2zcsp.data.Triple;
import net.sourceforge.czt.circus2zcsp.data.VariableRenameSchema;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.circus2zcsp.util.MemPredKind;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.print.ast.Application;
import net.sourceforge.czt.print.ast.ApplicationVisitor;
import net.sourceforge.czt.print.ast.OperatorApplication;
import net.sourceforge.czt.print.ast.OperatorApplicationVisitor;
import net.sourceforge.czt.print.ast.PrintExpression;
import net.sourceforge.czt.print.ast.PrintExpressionVisitor;
import net.sourceforge.czt.print.ast.PrintParagraph;
import net.sourceforge.czt.print.ast.PrintParagraphVisitor;
import net.sourceforge.czt.print.ast.PrintPredicate;
import net.sourceforge.czt.print.ast.PrintPredicateVisitor;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.z.util.Fixity;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.util.ZChar;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.ZVisitor;

/**
 * Print the Circus or Z term to the corresponding term in CSPm
 * 
 * @author rye
 */
public class PrintCircusZToCSPVisitor
    implements
      TermVisitor<Object>,
      ListTermVisitor<Object>,
      ZVisitor<Object>,
      CircusVisitor<Object>,
      ApplicationVisitor<Object>,
      OperatorApplicationVisitor<Object>,
      PrintParagraphVisitor<Object>,
      PrintPredicateVisitor<Object>,
      PrintExpressionVisitor<Object>,
      PrintPropertiesKeys
{
  private Visitor<Object> visitor_ = this;

  /**
   * expression string
   */
  private String str_ = "";

  // private String str_tmp_ = "";

  /**
   * store the str_ temporarily and used for later recovery of str_
   */
  private final Stack<String> str_tmp_stack_;

  // a map from original variable or schema name to replaced new name
  private CircusSpecMap map_ = null;

  private String proname_ = null;

  private CSPSpec cspspec_ = null;

  private ZFactory fac_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();

  private CircusFactory cfac_ = new net.sourceforge.czt.circus.impl.CircusFactoryImpl();

  private ZParaList paralist_ = null;

  /**
   * Record the declarations in a variable block command and it's used to check if
   * this expression or predicate or action is within a variable block or not
   * A list of declarations with map from variable name to expression in a variable block.
   * Because,
   * For example, for var x:T \circspot A(x), it records the (x, T, n)
   * n - the corresponding number for the variable
   * For example, for var x,y:T \circspot A(x), it records the (x, T, n) and (y, T, n)
   * For example, for var x:T1; y:T2 \circspot A(x), it records the (x, T1, n) and (y, T2, n)
   */
  private final Stack<List<Triple<String, Pair<String, Term>, String>>> varblock_var_;

  /**
   * local variable in scope from input channel, such as c?x, c!y?x?z (only x and z are in scope,
   * and y are not recorded here since only x and z are introduced in scope)
   * one variable is added when it is an input from a channel (input in prefix action)
   * one variable is removed after visiting the prefixed action)
   * 20140415: Term is the type of variable. It shall be from channel definition
   */
  private final Stack<Pair<String, Term>> loc_var_;

  /**
   * whether modify str_ or not
   * empty() - modify
   * true - modify
   * false - do not modify
   */
  // private final Stack<Boolean> mod_str_;

  // /**
  // * whether or not to check if a predicate contains a state variables or local variables
  // * empty() - not
  // * true - check
  // * false - not
  // */
  // private final Stack<Boolean> check_state_;

  /**
   * whether this is an action before seq ;
   * empty() - false
   * true - true
   * false - false
   */
  // private final Stack<Boolean> action_just_before_seq_;

  /**
   * whether a seq ; is necessary when output
   * empty() - need
   * true - true
   * false - false
   */
  // private final Stack<Boolean> need_seq_;
  
  /**
   * safe visit mode:
   *    str_ is not changed [CSP Spec]
   *    paralist_ is not changed [Z Spec]
   * if the size of safe_visit_ stack is larger than 0, it is safe_visit mode.
   */
  private final Stack<Boolean> safe_visit_;
  
  private final Stack<CSPSpec> safe_visit_cspspec_;

  private final Config config_;
  
  public PrintCircusZToCSPVisitor()
  {
    map_ = new CircusSpecMap();
    proname_ = new String();
    cspspec_ = new CSPSpec();
    paralist_ = fac_.createZParaList();
    // mod_str_ = new Stack<Boolean>();
    // action_just_before_seq_ = new Stack<Boolean>();
    // need_seq_ = new Stack<Boolean>();
    str_tmp_stack_ = new Stack<String>();
    varblock_var_ = new Stack<List<Triple<String, Pair<String, Term>, String>>>();
    loc_var_ = new Stack<Pair<String, Term>>();
    safe_visit_ = new Stack<Boolean>();
    safe_visit_cspspec_ = new Stack<CSPSpec>();
    config_ = new Config(null);
  }

  public PrintCircusZToCSPVisitor(CircusSpecMap map, String proname, CSPSpec cspspec)
  {
    this.map_ = map;
    this.proname_ = proname;
    this.cspspec_ = cspspec;
    paralist_ = fac_.createZParaList();
    // mod_str_ = new Stack<Boolean>();
    // action_just_before_seq_ = new Stack<Boolean>();
    // need_seq_ = new Stack<Boolean>();
    str_tmp_stack_ = new Stack<String>();
    varblock_var_ = new Stack<List<Triple<String, Pair<String, Term>, String>>>();
    loc_var_ = new Stack<Pair<String, Term>>();
    safe_visit_ = new Stack<Boolean>();
    safe_visit_cspspec_ = new Stack<CSPSpec>();
    config_ = new Config(null);
  }

  public ZParaList getParaList()
  {
    return paralist_;
  }

  public void clear()
  {
    str_ = "";
  }

  public void crln()
  {
    str_ += "\n";
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

  public String toString()
  {
    /**
     * $$SYNCH channel type is removed
     */
    str_ = str_.replace(": $$SYNCH", "");

    return str_;
  }

  protected Object visit(Term t)
  {
    if (t != null) {
      return t.accept(visitor_);
    }
    return null;
  }

  // private boolean shouldModifyStr()
  // {
  // return mod_str_.isEmpty() ? true : mod_str_.peek().booleanValue();
  // }

  // private boolean isNeedSeq()
  // {
  // return need_seq_.isEmpty() ? true : need_seq_.peek().booleanValue();
  // }

  // private boolean isActionJustBeforeSeq()
  // {
  // return action_just_before_seq_.isEmpty() ? false :
  // action_just_before_seq_.peek().booleanValue();
  // }

  @Override
  public Object visitOrPred(OrPred term)
  {
    String str = str_;

    visit(term.getLeftPred());
    str_ += " or ";
    visit(term.getRightPred());

    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitPowerType(PowerType term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitConstDecl(ConstDecl term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitOperator(Operator term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitTupleSelExpr(TupleSelExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitUnparsedZSect(UnparsedZSect term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitInclDecl(InclDecl term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitImpliesPred(ImpliesPred term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitExistsPred(ExistsPred term)
  {
    String str = str_;
    String strDecl = "";
    String strPred = "";
    String op = ZString.EXI;

    Pred pred = term.getPred();
    ZSchText schText = term.getZSchText();

//    save_str();
    strPred += safe_visit(pred);

    strDecl += safe_visit(schText.getZDeclList());
//    restore_str();

    // TODO: multiple variables in DeclList
    assert !strDecl.isEmpty();
    // comma separate decls
    String[] strs = strDecl.trim().split(",");
    for (String st : strs) {
      // : separate (var:T)
      String[] vars = st.trim().split(":");
      str_ += Circus2ZCSPUtils.convertOp(vars[1], "\\" + vars[0] + " @ " + strPred, op);
    }

    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitZNumeral(ZNumeral term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZFreetypeList(ZFreetypeList term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitAndPred(AndPred term)
  {
    String str = str_;
    visit(term.getLeftPred());
    str_ += " and ";
    visit(term.getRightPred());
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitParent(Parent term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitAxPara(AxPara term)
  {
    String str = str_;

    if (ZUtils.isAbbreviation(term)) {
      Debug.debug_print("visitAxPara:(IN) " + term.toString());
      Name name = ZUtils.getAbbreviationName(term);
      String strName = name.toString();
      str_ = "nametype " + strName + " = ";
      Expr expr = ZUtils.getAbbreviationExpr(term);
      visit(expr);
      Debug.debug_print("visitAxPara:(OUT) " + str_);
    }
    else if (ZUtils.isSimpleSchema(term)) {
      // there's no predicate
      if (term.getBox().equals(Box.OmitBox) && term.getZSchText().getPred() == null) {
        ConstDecl cdecl = (ConstDecl) term.getZSchText().getZDeclList().get(0);
//        save_str();
        String schName = "" + safe_visit(cdecl.getZName());
//        restore_str();
        Expr expr = cdecl.getExpr();
        if (expr instanceof SchExpr) {
          // no predicate, just schema type to group the declarations
          if (((SchExpr) expr).getZSchText().getPred() == null) {
//            visit(((SchExpr) expr).getZSchText().getZDeclList());
            for (Decl decl : ((SchExpr) expr).getZSchText().getZDeclList()) {
              if (decl instanceof VarDecl) {
                /** x,y,z:\nat */
                List<String> vlst = new ArrayList<String>();
                save_str();
                for (Name name : ((VarDecl) decl).getZNameList()) {
                  vlst.add("" + safe_visit(name));
                }
                String strExpr = "" + safe_visit(((VarDecl) decl).getExpr());
                restore_str();
                // the pair of variable name and expression with schema name together are added in
                // the global database
                for (String varname : vlst) {
                  map_.addSchType(schName, varname, strExpr, ((VarDecl) decl).getExpr());
                }
              }
              else if(decl instanceof ConstDecl) {
                /** such as x == 1 
                 * it is equal to x:{1}
                 */
                ConstDecl cd = (ConstDecl) decl;
                
                List<Expr> lstExpr = new ArrayList<Expr>();
                lstExpr.add(cd.getExpr());
                ZExprList el = fac_.createZExprList(lstExpr);
                SetExpr se = fac_.createSetExpr(el);
                String strExpr = safe_visit(se);
                // the pair of variable name and expression with schema name together are added in
                // the global database
                map_.addSchType(schName, cd.getZName().accept(new PrintVisitor()), 
                    strExpr, ((VarDecl) decl).getExpr());
              }
            }
          }
        }
      }
    }

    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitTypeAnn(TypeAnn term)
  {
    String str = str_;
    // TODO
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
  public Object visitOrExpr(OrExpr term)
  {
    String str = str_;
    visit(term.getLeftExpr());
    str_ += " or ";
    visit(term.getRightExpr());
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitZBranchList(ZBranchList term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitParenAnn(ParenAnn term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZName(ZName term)
  {
    String str = str_;
    str_ += term.toString();
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitNarrSect(NarrSect term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitBranch(Branch term)
  {
    String str = str_;

    if (term.getExpr() == null) {
      visit(term.getZName());
    }
    else {
      // List ::= leaf | const<<X>> | const1<<List>>
      // TODO: recursive definition is not supported yet
      save_str();
      String expr = "" + safe_visit(term.getExpr());
      String name = "" + safe_visit(term.getZName());
      restore_str();
      str_ += name + "." + expr;
    }

    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitExistsExpr(ExistsExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitDecorExpr(DecorExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitPowerExpr(PowerExpr term)
  {
    String str = str_;
    str_ += "Set(";
    visit(term.getExpr());
    str_ += ")";
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitZRenameList(ZRenameList term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitFreePara(FreePara term)
  {
    String str = str_;
    // return
    // datatype T = A1 | A2 | A3;
    str_ += "datatype ";
    String name;

    FreetypeList fl = term.getFreetypeList();
    if (fl instanceof ZFreetypeList) {
      for (Freetype fp : ((ZFreetypeList) fl).getFreetype()) {
        name = fp.getZName().getWord();
        str_ += name + " = ";
        BranchList bl = fp.getBranchList();
        if (bl instanceof ZBranchList) {
          int size = ((ZBranchList) bl).getBranch().size();
          if (size > 0) {
            visit(((ZBranchList) bl).getBranch().get(0));
//            str_ += ((ZBranchList) bl).getBranch().get(0).getZName().getWord();
          }

          for (int i = 1; i < size; i++) {
//            str_ += " | " + ((ZBranchList) bl).getBranch().get(i).getZName().getWord();
            str_ += " | ";
            visit(((ZBranchList) bl).getBranch().get(i));
          }
        }
      }
    }

    Debug.debug_print(str_);
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitAndExpr(AndExpr term)
  {
    String str = str_;
    visit(term.getLeftExpr());
    str_ += " and ";
    visit(term.getRightExpr());
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
  public Object visitUnparsedPara(UnparsedPara term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNameTypePair(NameTypePair term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitOperand(Operand term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitRefExpr(RefExpr term)
  {
    String str = str_;
    OperatorName on = term.getZName().getOperatorName();
    ZExprList exprlist = term.getZExprList();
    boolean args = exprlist != null && !exprlist.isEmpty();

    String refName = Circus2ZCSPUtils.getVarName(term.getZName());
    assert refName != null && !refName.isEmpty();

    if (ZUtils.isReferenceExpr(term)) {
      /**
       * C.6.28 (Reference). For example: \arithmos
       * In this case, mixfix and explicit are always false
       * and the list of instantiating expressions is empty.
       * Another example before typechecking is \emptyset.
       * The typechecker transforms \emptyset to a generic
       * instantiation and explicit remains false (see 13.2.3.3).
       */
      str_ += refName;
    }
    else if (ZUtils.isGenInstExpr(term)) {
      /**
       * a generic operator instantiation. That
       * is, a RefExpr with mixfix false and the list of instantiating
       * expressions is non-empty (it contains [T]). The explicit
       * attribute indicates whether the instantiating expressions are
       * explicitly given in the specification (explicit is true) or
       * whether they were inferred by the typechecker (explicit is
       * false). For example: \emptyset[T] or \emptyset.
       * For example: _ ≠ _ [ݔ¸] (mixfix=false, explicit=false,
       * size of expressions list is 1
       */
      str_ += refName;
    }
    else if (ZUtils.isExplicitGenInstExpr(term)) {
      /**
       * Another less common example would be (\_ \fun \_)[S, T].
       * In this case,
       * RefExpr(ZName("_->_"), ZExprList(
       * RefExpr(ZName("S"), MF=F, EX=F),
       * RefExpr(ZName("T"), MF=F, EX=F)),
       * MF=F, EX=T)
       */
    }
    else if (ZUtils.isGenOpApplExpr(term)) {
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
      Expr left = exprlist.get(0);
      String lhs = "";
      save_str();
      lhs += safe_visit(left);
      restore_str();

      if (on.isInfix()) {
        String rhs = "";
        save_str();
        rhs += safe_visit(exprlist.get(1));
        restore_str();
        str_ += Circus2ZCSPUtils.convertOp(lhs, rhs, refName);
      }
      else if (on.isPrefix()) {
        str_ += Circus2ZCSPUtils.convertOp("", lhs, refName);
      }
      else if (on.isPostfix()) {
        str_ += Circus2ZCSPUtils.convertOp(lhs, "", refName);
      }
    }
    else {
      throw new CztException("Unknown ref expr kind");
    }

    // if(term.getMixfix())
    // {
    // if(term.getExplicit())
    // {
    // /**
    // * c.6.21 (Generic Operator Application). For example: S \rel T.
    // In this case, mixfix and explicit are always true,
    // and the list of instantiating expressions is non-empty
    // (it contains [S,T]).
    // */
    // }
    // }
    // else
    // {
    // // if(!term.getMixfix() && !term.getExplicit() && term.getZExprList().isEmpty())
    // if(term.getZExprList().isEmpty() && !term.getExplicit())
    // {
    // /**
    // * C.6.28 (Reference). For example: \arithmos
    // In this case, mixfix and explicit are always false
    // and the list of instantiating expressions is empty.
    // Another example before typechecking is \emptyset.
    // The typechecker transforms \emptyset to a generic
    // instantiation and explicit remains false (see 13.2.3.3).
    // */
    // str_ += term.getZName().toString();
    // }
    // else if(!term.getZExprList().isEmpty())
    // {
    // /**
    // * C.6.29 (Generic Instantiation). For example: \emptyset[T].
    // In this case, mixfix is always false and the list of
    // instantiating expressions is non-empty (it contains [T]).
    // The explicit attribute indicates whether the instantiating
    // expressions are explicitly given in the specification
    // (explicit is true) or whether they were inferred by the
    // typechecker (explicit is false).
    // */
    // if(term.getExplicit())
    // {
    //
    // }
    // else
    // {
    //
    // }
    // }
    // }

    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitGivenPara(GivenPara term)
  {
    String str = str_;
    String value = config_.getConfig(Config.CONF_GIVEN_SET_INST_NO);
    int n = Integer.parseInt(value);

    for (Name name : term.getZNameList()) {
      str_ += "datatype " + name.toString() + "_TYPE = " + name.toString() + "_1";
      for (int i = 1; i < n; i++) {
        str_ += " | " + name.toString() + "_" + (i + 1);
      }

      str_ += "\n" + name.toString() + " = {" + name.toString() + "_1";
      for (int i = 1; i < n; i++) {
        str_ += ", " + name.toString() + "_" + (i + 1);
      }
      str_ += "}";
    }

    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitFreetype(Freetype term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNumStroke(NumStroke term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitHideExpr(HideExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitLatexMarkupPara(LatexMarkupPara term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNextStroke(NextStroke term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSectTypeEnvAnn(SectTypeEnvAnn term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZStrokeList(ZStrokeList term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZDeclList(ZDeclList term)
  {
    String str = str_;
    int i = 0;

    for (Decl decl : term) {
      if (i > 0) {
        str_ += ", ";
      }
      visit(decl);
    }

    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitMuExpr(MuExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  /**
   * {x:\num | p}
   * {i1:e1; i2:e2; ... in:en \bullet e}
   * {i1:e1; i2:e2; ... in:en | p \bullet e}
   */
  @Override
  public Object visitSetCompExpr(SetCompExpr term)
  {
    String str = str_;
    str_ += "{";
    ZSchText sch = term.getZSchText();
    for (Decl decl : sch.getZDeclList()) {
      if (decl instanceof VarDecl) {
        /** x,y,z:\nat */
        /** TODO: how to deal with several variables */
        for (Name name : ((VarDecl) decl).getZNameList()) {
          str_ += name.toString();
          str_ += " | ";
          str_ += name.toString() + " <- ";
        }
        visit(((VarDecl) decl).getExpr());
        str_ += ", ";
      }
    }

    Pred pred = sch.getPred();
    visit(pred);
    str_ += "}";
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

//    str_ = str_.substring(0, str_.length() - 2);
    str_ += "}";
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitZNameList(ZNameList term)
  {
    String str = str_;

    for (Name zn : term) {
      visit(zn);
      str_ += ",";
    }
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitLambdaExpr(LambdaExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitOutStroke(OutStroke term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCompExpr(CompExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitForallExpr(ForallExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitPipeExpr(PipeExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitBindExpr(BindExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitGenParamType(GenParamType term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitConjPara(ConjPara term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitVarDecl(VarDecl term)
  {
    String str = str_;
    String text = " ";

    for (Name name : term.getZNameList()) {
      text += ((ZName) name).toString();
      text += ":";
      save_str();
      text += safe_visit(term.getExpr());
      restore_str();
      text += ", ";
    }
    // remove the last " , "
    if (text.contains(", ")) {
      text = text.substring(0, text.length() - 2);
    }

    str_ += text;

    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitZParaList(ZParaList term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSchExpr(SchExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSignatureAnn(SignatureAnn term)
  {
    String str = str_;
    // TODO
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
        // TODO:
        lhs = term.getLeftExpr();
        rhs = term.getRightExpr();
        save_str();
        left = "" + safe_visit(lhs);
        right = "" + safe_visit(rhs).toString();
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
        save_str();
        String tmp = "";
        tmp += safe_visit(term.getRightExpr());
        restore_str();
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

    // String str = str_;
    //
    // /**
    // * A relation operator application (C.5.12)
    // */
    // if(term.getMixfix())
    // {
    // if(ZUtils.isTupleExpr(term.getLeftExpr()))
    // {
    // /**
    // * Other operator application
    // * the first (left) expression is
    // usually a tuple containing the corresponding number of arguments,
    // and the second (right) expression is the operator name.
    // However, for a unary operator, the left expression does not have
    // to be a tuple.
    // For example, "n &lt; m" has left="(n,m)" and right=" _ &lt; _ ",
    // "disjoint s" has left="s" and right="disjoint _ ", and
    // if foo was declared as a unary postfix operator,
    // then "(2,3) foo" would have left= "(2,3)" and right=" _ foo".
    // */
    // visitOperOrFuncAppl(term.getLeftExpr(), term.getRightExpr());
    // }
    // else
    // {
    // /**
    // * Equality
    // */
    // visit(term.getLeftExpr());
    // str_ += " = ";
    // visit(term.getRightExpr());
    // }
    // }
    // else
    // {
    // /**
    // * Membership predicate.
    // * In this case, Mixfix=false, the first (left) expression is the
    // element, and the second (right) expression is the set.
    // For example, "n \in S" has left="n" and right="S".
    // */
    // }
    // String tmp = subStr(str_, str);
    // if(!shouldModifyStr())
    // {
    // str_= str;
    // }
    // return tmp;
  }

  @Override
  public Object visitRenameExpr(RenameExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitExists1Pred(Exists1Pred term)
  {
    // TODO Auto-generated method stub
    String str = str_;
    String strDecl = "";
    String strPred = "";
    String op = CSPPredExpPattern.getPattern(PredExpPattern.OP_NAME_EXISTS_1);

    Pred pred = term.getPred();
    ZSchText schText = term.getZSchText();

    save_str();
    strPred += safe_visit(pred);

    strDecl += safe_visit(schText.getZDeclList());
    restore_str();

    // TODO: multiple variables in DeclList
    assert !strDecl.isEmpty();
    // comma separate decls
    String[] strs = strDecl.trim().split(",");
    for (String st : strs) {
      // : separate (var:T)
      String[] vars = st.trim().split(":");
      str_ += Circus2ZCSPUtils.convertOp(vars[1], "\\" + vars[0] + " @ " + strPred, op);
    }

    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitForallPred(ForallPred term)
  {
    String str = str_;
    String strDecl = "";
    String strPred = "";
    String op = ZString.ALL;

    Pred pred = term.getPred();
    ZSchText schText = term.getZSchText();

    save_str();
    strPred += safe_visit(pred);

    strDecl += safe_visit(schText.getZDeclList());
    restore_str();

    // TODO: multiple variables in DeclList
    assert !strDecl.isEmpty();
    // comma separate decls
    String[] strs = strDecl.trim().split(",");
    for (String st : strs) {
      // : separate (var:T)
      String[] vars = st.trim().split(":");
      str_ += Circus2ZCSPUtils.convertOp(vars[1], "\\" + vars[0] + " @ " + strPred, op);
    }

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
      if (ZUtils.isRefExpr(term.getLeftExpr())) {
        OperatorName os = ((RefExpr) (term.getLeftExpr())).getZName().getOperatorName();
        assert os != null;
        if (os.isInfix()) {
          assert ZUtils.isTupleExpr(term.getRightExpr());
          /** won't modify the str_ */
          save_str();
          rel = Circus2ZCSPUtils.getOperator(os);
          left = "" + safe_visit(term.getRightExpr());

          List<String> lstr = new ArrayList<String>();
          if (split_tuple(left, lstr)) {
            left = lstr.get(0);
            right = lstr.get(1);
            restore_str();
            str_ += Circus2ZCSPUtils.convertOp(left, right, rel);
          }
          // right = "" + visit(term.getRightExpr());
        }
        else if (os.isPrefix() && os.isUnary()) {
          save_str();
          rel = Circus2ZCSPUtils.getOperator(os);
          left = "";
          right = "" + safe_visit(term.getRightExpr());
          restore_str();
          str_ += Circus2ZCSPUtils.convertOp(left, right, rel);
        }
        else if (os.isPostfix()) {
          // TODO
        }
        else if (os.getFixity() == Fixity.NOFIX) {
          // For example, \langle \listarg \rangle
          save_str();
          rel = Circus2ZCSPUtils.getOperator(os);
          left = "";
          right = "" + safe_visit(term.getRightExpr());
          restore_str();
          str_ += Circus2ZCSPUtils.convertOp(left, right, rel);
        }
      }
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
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitExprPred(ExprPred term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZSect(ZSect term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZExprList(ZExprList term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitTupleExpr(TupleExpr term)
  {
    String str = str_;
    str_ += "(";

    for (Expr expr : term.getZExprList()) {
      visit(expr);
      str_ += ", ";
    }

    // remove last ", "
    str_ = str_.substring(0, str_.length() - 2);
    str_ += ")";
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitSchemaType(SchemaType term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitImpliesExpr(ImpliesExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitGenericType(GenericType term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNewOldPair(NewOldPair term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNarrPara(NarrPara term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitIffPred(IffPred term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitLocAnn(LocAnn term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitExists1Expr(Exists1Expr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitGivenType(GivenType term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSignature(Signature term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNegPred(NegPred term)
  {
    String str = str_;

    str_ += "not (";
    visit(term.getPred());
    str_ += ")";

    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZSchText(ZSchText term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitProjExpr(ProjExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitDirective(Directive term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitThetaExpr(ThetaExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNumExpr(NumExpr term)
  {
    String str = str_;
    str_ += term.toString();
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitCondExpr(CondExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitLetExpr(LetExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSpec(Spec term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitOptempPara(OptempPara term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitBindSelExpr(BindSelExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  /**
   * Cartesian Product to CSP triple
   */
  @Override
  public Object visitProdExpr(ProdExpr term)
  {
    String str = str_;

    str_ += "(";

    for (Expr expr : term.getZExprList()) {
      visit(expr);
      str_ += ",";
    }
    str_ = str_.substring(0, str_.length() - 1);
    str_ += ")";

    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitPreExpr(PreExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitProdType(ProdType term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNegExpr(NegExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNameSectTypeTriple(NameSectTypeTriple term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitInStroke(InStroke term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitIffExpr(IffExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitPrintExpression(PrintExpression printExpression)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitPrintPredicate(PrintPredicate printPredicate)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitPrintParagraph(PrintParagraph printParagraph)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitOperatorApplication(OperatorApplication opApp)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitApplication(Application applicatio)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
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
  public Object visitParallelProcess(ParallelProcess term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitAlphabetisedParallelProcess(AlphabetisedParallelProcess term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  /*
   * (non-Javadoc)
   * @see
   * net.sourceforge.czt.circus.visitor.SchExprActionVisitor#visitSchExprAction(net.sourceforge.
   * czt.circus.ast.SchExprAction)
   * \lschexpract Op \rschexpract
   */
  @Override
  public Object visitSchExprAction(SchExprAction term)
  {
    String str = str_;

    Expr expr = term.getExpr();

    String name = "";
    if (expr instanceof RefExpr) {
      name = ((RefExpr) expr).getZName().getWord();
    }

    /** For schema name */
    // name is like the format: sch?x!y (the input and output are appended by SchemaExprVisitor
    // before)
    Pair<String, Term> pp = map_.getRepByNewName(proname_, name);
    if (pp != null) {
      ZFactoryImpl fac_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
      cspspec_.addHideCSPB(removeInOutVarFromSchemaName(name));
      {
        String opname = Fvar(name);

        String newname;
        {
          if (opname.startsWith(name)) {
            newname = "("
                + opname
                + " -> SKIP [] "
                + MessageFormat.format(FormatPattern.NEG_PRECONDITION_SCHEMA,
                    removeInVarFromSchemaName(name)) + " -> DIV)";
          }
          else {
            // move additional getn event out of schema expr
            // for example, from 
            //  (get0?i -> SExpr!i -> SKIP [] get0?i -> fSEepr!i -> SKIP)
            // to 
            //  (get0?i -> (SExpr!i -> SKIP [] fSEepr!i -> SKIP))
            opname = opname.replace(name, "(" + name);
            newname = "("
                + opname
                + " -> SKIP [] "
                + MessageFormat.format(FormatPattern.NEG_PRECONDITION_SCHEMA,
                    removeInVarFromSchemaName(name)) + " -> DIV))";
          }
        }
        str_ += newname;
        Debug.debug_print(name + " => " + newname);
      }
    }

    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitQualifiedDecl(QualifiedDecl term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCommunication(Communication term)
  {
    String str = str_;

    // the fileds counting, used to get the right type for each field
    // For example,
    // channel c: A \cross B \cross C
    // c?x!y?z -> SKIP
    // there are three fields and with this number we can get the type
    // for x is A, for y is B, and for z is C
    int fieldcnt = 0;

    /*
     * number of local variables introduced from this communication
     */
    int locVarCnt = 0;

    String strBef = str_;
    save_str();

    // channel expression
    String chnname = "" + safe_visit(term.getChannelExpr());
    str_ += chnname;

    // communication pattern
    if (term.getCommPattern().compareTo(CommPattern.Output) == 0) {
//      str_ += "!";
    }
    else if (term.getCommPattern().compareTo(CommPattern.Input) == 0) {
//      str_ += "?";
    }
    else if (term.getCommPattern().compareTo(CommPattern.Mixed) == 0) {
      str_ += "";
    }
    else if (term.getCommPattern().compareTo(CommPattern.ChannelSet) == 0) {
      str_ += "";
    }

    //
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

        // Get the channel expression from channel declaration
        // It's a pair of channel expression in CSP and Circus Term
        Pair<String, Term> chnexpr = map_.getChnDecl(chnname);

        // Get the type for nth input/output in the channel
        // For example, channel c:A \cross B \cross C.
        // For c?x!y?z, if varname is x, then we get the type A.
        // If varname is z, then we get the type C.
        Term tVar = null;
        if (chnexpr != null) {
          // Product express
          if (chnexpr.getSecond() instanceof ProdExpr) {
            tVar = chnexpr.getSecond();
            List<Expr> te = ((ProdExpr) tVar).getZExprList();
            tVar = te.get(fieldcnt);
          }
          else {
            tVar = chnexpr.getSecond();
          }
        }
        // a new local variable
        loc_var_.push(new Pair<String, Term>(varname, tVar));
        locVarCnt++;

        str_ += varname;
        if ((((InputField) field).getRestriction() != null)
            && !(((InputField) field).getRestriction() instanceof TruePred) // not a true restrict
        ) {
          // input restriction
          String[] achnexpr = chnexpr.getFirst().split("\\.");
          str_ += ": {" + varname + " | " + varname + " <- " + achnexpr[fieldcnt] + ", ";
          visit(((InputField) field).getRestriction());
          str_ += "}";
        }
      }
      fieldcnt++;
    }

    String strEvt = subStr(str_, strBef);
    restore_str();

    str_ += strEvt;
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitSubstitutionAction(SubstitutionAction term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitInterleaveActionIte(InterleaveActionIte term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitInterleaveProcessIte(InterleaveProcessIte term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCallProcess(CallProcess term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCircusStateAnn(CircusStateAnn term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitActionSignature(ActionSignature term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitTransformerPara(TransformerPara term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  /**
   * \Phi(\circmu X \circspot P(X)) \defs \B{let } MuX=\Phi(P(MuX)) \B{ within } MuX
   */
  @Override
  public Object visitMuAction(MuAction term)
  {
    String str = str_;
    str_ += "let " + term.getZName().toString() + " = ";
//    str_ += "\n";
//    String strPre = str_;
//    save_str();
//    str_ += term.getZName().toString() + " = ";
    visit(term.getCircusAction());
//    String strAft = subStr(str_, strPre);
//    restore_str();
//    cspspec_.addProcess(strAft);

    str_ += " within " + term.getZName().toString();
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitProcessPara(ProcessPara term)
  {
    String str = str_;

    if (term == null) {
      return "";
    }

    // get process name
    String proName = ((ProcessPara) term).getName().toString();
    str_ += proName + " = ";

    if (((ProcessPara) term).isBasicProcess()) {
      BasicProcess bp = ((ProcessPara) term).getCircusBasicProcess();

      // ZParaList in ProcessPara
      for (Para procPara : bp.getZParaList()) {
        if (procPara instanceof ActionPara) {
          if (((ActionPara) procPara).getZName().getWord().contains("$$mainAction_")) {
            visit(((ActionPara) procPara).getCircusAction());
          }
          else {
            visit(((ActionPara) procPara).getCircusAction());
            crln();
          }
        }
        else if (procPara instanceof AxPara) {

        }
        else if (procPara instanceof NameSetPara) {
          visit(procPara);
          crln();
        }
      }
    }

    String tmp = subStr(str_, str);

    return tmp;
  }

  /*
   * (non-Javadoc)
   * @see
   * net.sourceforge.czt.circus.visitor.IfGuardedCommandVisitor#visitIfGuardedCommand(net.sourceforge
   * .czt.circus.ast.IfGuardedCommand)
   * Alternation Action
   */
  @Override
  public Object visitIfGuardedCommand(IfGuardedCommand term)
  {
    String str = str_;

    IfGuardedCommand term2 = ZUtils.cloneTerm(term);
    /**
     * 1. calculate negation of guarded condition and add to a list
     */

    // Triple: original true pred, negation of pred (not pred), original CircusAction
    List<Triple<Pred, Pred, CircusAction>> lstPPCGA = new ArrayList<Triple<Pred, Pred, CircusAction>>();

    List<String> lstStr = new ArrayList<String>();
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

      // add to table
      lstCombTable.add(new Pair<Pred, CircusAction>(pred, ca));
    }

    /**
     * 3. Handle lstCombTable
     */
    /** csp spec */
    String cspStr = "(";
    /** prefix getn */
    String strPref = "";
    for (Pair<Pred, CircusAction> tp : lstCombTable) {
      /** csp spec for each entry */
      String strCSP = new String();

      // state/local variables
      if (tp.getFirst() != null) {
        // paraName
        String paraName = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.ALT_NAME_PATT), proname_,
            map_.incn());
        // channel definition
        String chnDecl = "channel " + paraName;
        // CSP event name, such as assOp!x!y?z
        String eventName = paraName;

        save_str();
        String strPred = "" + safe_visit(tp.getFirst());
        restore_str();
        List<Pair<String, Term>> llst = new ArrayList<Pair<String, Term>>();

        if (isLocVar(strPred, llst)) {
//          paralist_.add(assembleZPara(paraName, tp.getFirst(), llst));
          AddPara(assembleZPara(paraName, tp.getFirst(), llst));
        }
        else {
//          paralist_.add(assembleZPara(paraName, tp.getFirst()));
          AddPara(assembleZPara(paraName, tp.getFirst()));
        }

        cspspec_.addHideCSPB(paraName);
        for (Pair<String, Term> p : llst) {
          eventName += "!" + p.getFirst();
        }

        // for each local variable in eventName (such as x and y in assOp!x!y), get their value
        // first
        // for each local variable in eventName (such as y in assOp!x?y), update their value at last
        List<String> inVars = new ArrayList<String>();
        List<String> outVars = new ArrayList<String>();

        // get the in and out variables from the schema name
        getInOutVarFromSchemaName(eventName, inVars, outVars);

        String pre = Faccess_var(new HashSet<String>(outVars));
        String post = Fupdate_var(new HashSet<String>(inVars));

//        eventName = Fvar(eventName);
        strPref = pre;
        strCSP += "(" + eventName + post + " -> SKIP);";
      }

      strCSP += tp.getSecond() == null ? " DIV" : safe_visit(tp.getSecond());
      if (cspStr.equals("(")) {
        cspStr += "\n    (" + strCSP + ")";
      }
      else {
        cspStr += "\n [] (" + strCSP + ")";
      }
    }
    cspStr += "\n)";

    str_ += strPref + cspStr;
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
  public Object visitIndexedProcess(IndexedProcess term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSeqProcessIte(SeqProcessIte term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitIntChoiceAction(IntChoiceAction term)
  {
    String str = str_;
    str_ += "\n\t(";
    visit(term.getLeftAction());
    str_ += "\n\t|~|\n\t";
    visit(term.getRightAction());
    str_ += "\n\t)";
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitDotField(DotField term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitIntChoiceProcess(IntChoiceProcess term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  /*
   * (non-Javadoc)
   * @see
   * net.sourceforge.czt.circus.visitor.ParallelActionVisitor#visitParallelAction(net.sourceforge
   * .czt.circus.ast.ParallelAction)
   * A \lpar | \lchanset c \rchanset | \rpar B
   */
  @Override
  public Object visitParallelAction(ParallelAction term)
  {
    List<Pair<String, Term>> lstSet = new ArrayList<Pair<String, Term>>();
    isStateWithExpr(term.getRightAction(), lstSet);
    
    String str = str_;

    ParallelAction term2 = ZUtils.cloneTerm(term);

    assert (term2.getNameSet().get(0) instanceof CircusNameSet);
    assert (term2.getNameSet().get(1) instanceof CircusNameSet);

    CircusNameSet cns1 = (CircusNameSet) term2.getNameSet().get(0);
    CircusNameSet cns2 = (CircusNameSet) term2.getNameSet().get(1);

    save_str();
    String strns1 = "" + safe_visit(term2.getNameSet().get(0));
    String strns2 = "" + safe_visit(term2.getNameSet().get(1));
    restore_str();

    // if both ns1 and ns2 are empty
    if (strns1.equals("{}") && strns2.equals("{}")) {
      visit(term2.getLeftAction());

      str_ += " [| ";
      visit(term2.getChannelSet());
      str_ += " |] ";
      visit(term2.getRightAction());
    }
    else {
      /**
       * 1. Get all variables in scope (pv1 and pv2, sv1 and sv2, lv1 and lv2, ns1 and ns2)
       */

      Term leftTerm = null;
      Term rightTerm = null;

      // get a set of term name in left and right action
      ZNameSetVisitor lznsv = new ZNameSetVisitor();
      ZNameSetVisitor rznsv = new ZNameSetVisitor();
      if (term2.getLeftAction() instanceof CallAction) {
        // get its corresponding term if it is an action reference not schema name reference
        if ((((CallAction) term2.getLeftAction()).getZName()).toString().contains("_Action_")) {
          Pair<String, Term> p = map_.getRepByNewName(proname_,
              (((CallAction) term2.getLeftAction()).getZName()).toString());
          if (p != null) {
            leftTerm = p.getSecond();
          }
        }
      }
      else {
        leftTerm = term2.getLeftAction();
      }

      if (term2.getRightAction() instanceof CallAction) {
        // get its corresponding term if it is an action reference not schema name reference
        if ((((CallAction) term2.getRightAction()).getZName()).toString().contains("_Action_")) {
          Pair<String, Term> p = map_.getRepByNewName(proname_,
              (((CallAction) term2.getRightAction()).getZName()).toString());
          if (p != null) {
            rightTerm = p.getSecond();
          }
        }
      }
      else {
        rightTerm = term2.getRightAction();
      }

      assert leftTerm != null;
      assert rightTerm != null;
      leftTerm.accept(lznsv);
      rightTerm.accept(rznsv);

      Set<String> lstrNameSet = lznsv.getStrSet();
      Set<String> rstrNameSet = rznsv.getStrSet();
      // State variables in scope (sv1 and sv2)
      List<String> sv1 = new ArrayList<String>();
      List<String> sv2 = new ArrayList<String>();
      isState(lstrNameSet.toString(), sv1);
      isState(rstrNameSet.toString(), sv2);

      // Local variables in scope (lv1, lv2)
      List<String> lv1 = new ArrayList<String>();
      List<String> lv2 = new ArrayList<String>();
      List<Pair<String, Term>> lLocNameSet = new ArrayList<Pair<String, Term>>();
      List<Pair<String, Term>> rLocNameSet = new ArrayList<Pair<String, Term>>();

      isLocVar(lstrNameSet.toString(), lLocNameSet);
      isLocVar(rstrNameSet.toString(), rLocNameSet);
      for (Pair<String, Term> p : lLocNameSet) {
        lv1.add(p.getFirst());
      }
      for (Pair<String, Term> p : rLocNameSet) {
        lv2.add(p.getFirst());
      }

      // pv1 and pv2
      // pv1 = sv1 + lv1
      // pv2 = sv2 + lv2
      Set<String> pv1 = new HashSet<String>(sv1);
      pv1.addAll(new HashSet<String>(lv1));

      Set<String> pv2 = new HashSet<String>(sv2);
      pv2.addAll(new HashSet<String>(lv2));

      // pv
      Set<String> pv = new HashSet<String>(pv1);
      pv.addAll(pv2);

      // ns1 and ns2
      List<String> lnsNameSet = new ArrayList<String>();
      List<String> rnsNameSet = new ArrayList<String>();

      String lstrNs;
      String rstrNs;
      if (cns1.getExpr() instanceof RefExpr) {
        String nsname = cns1.getExpr().accept(new PrintVisitor());
        Pair<String, Term> pns1 = map_.getNameSet(proname_, nsname);
        lstrNs = pns1.getFirst();
      }
      else {
        lstrNs = safe_visit(cns1.getExpr());
      }

      if (cns2.getExpr() instanceof RefExpr) {
        String nsname = cns2.getExpr().accept(new PrintVisitor());
        Pair<String, Term> pns1 = map_.getNameSet(proname_, nsname);
        rstrNs = pns1.getFirst();
      }
      else {
        rstrNs = safe_visit(cns2.getExpr());
      }

      getAllVars(lstrNs, lnsNameSet);
      getAllVars(rstrNs, rnsNameSet);

      // pv1 and pv2 must include ns1 and ns2.
      // In other word, ns1 and ns2 must be a subset of pv1 and pv2
      Set<String> ns1 = new HashSet<String>(lnsNameSet);
      Set<String> ns2 = new HashSet<String>(rnsNameSet);

      if (pv1.containsAll(ns1) == false) {
        throw new CztException("All elements in ns1 [" + ns1.toString() + "] must be in pv1 ["
            + pv1.toString() + "]");
      }

      if (pv2.containsAll(ns2) == false) {
        throw new CztException("All elements in ns2 [" + ns2.toString() + "] must be in pv2 ["
            + pv2.toString() + "]");
      }

      /**
       * 2. assemble variable block
       */
      // 2.1 determine type expr for all variables in pv
      Set<Pair<String, Term>> setPv = new HashSet<Pair<String, Term>>();
      List<Pair<String, Term>> temp = new ArrayList<Pair<String, Term>>();
      isStateWithExpr(pv.toString(), temp);
      setPv.addAll(temp);
      isLocVar(pv.toString(), temp);
      setPv.addAll(temp);

      // 2.2 all variables in pv are renamed
      // a table of <varname, <tvarname, expr>>
      Map<String, Pair<String, Term>> mapPv = new HashMap<String, Pair<String, Term>>();
      for (Pair<String, Term> p : setPv) {
        mapPv.put(p.getFirst(),
            new Pair<String, Term>(MessageFormat.format(FormatPattern.TEMP_VAR_PATT, p.getFirst()),
                p.getSecond()));
      }

      // 2.3 renaming all variables in A1 and A2 to temporary variables
      // rename variables to parameters in action ca
//      List<Pair<String, String>> lstOldNew = new ArrayList<Pair<String, String>>();
//      for(String s: pv) {
//        lstOldNew.add(new Pair<String, String>(s, MessageFormat.format(FormatPattern.TEMP_VAR_PATT, s)));
//      }
//      VariableRenamingSchemaVisitor vrsv = new VariableRenamingSchemaVisitor(
//          VariableRenameSchema.VRS_ACTION_RENAME, lstOldNew);
//      
//      // TODO: if action is CallAction (a reference to action), how can we rename variables to temporary variables
//      term2.getLeftAction().accept(vrsv);
//      term2.getRightAction().accept(vrsv);

      ParallelAction pa = ZUtils.cloneTerm(term);
//      ((CircusNameSet)pa.getLeftNameSet())
      pa.setLeftNameSet(cfac_.createCircusNameSet(fac_.createSetExpr(fac_.createZExprList())));
      pa.setRightNameSet(cfac_.createCircusNameSet(fac_.createSetExpr(fac_.createZExprList())));
      CircusAction ca = pa;

      // 2.4 assemble variable block
      // paraName
      String paraName = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.PARA_ACTION_NAME_PATT), proname_,
          map_.incn());
      ZDeclList declList = fac_.createZDeclList();
      Pred pred = null;

//      Map<String, Pair<String, Term>> mapPv
      // assignment in the front of variable block
      List<ZName> lstAssFrtZName = new ArrayList<ZName>();
      List<Expr> lstAssFrtExpr = new ArrayList<Expr>();
      
      // assignment in the end of A1 to restore variables which are not in ns1
      List<ZName> lstAssBhdZName1 = new ArrayList<ZName>();
      List<Expr> lstAssBhdExpr1 = new ArrayList<Expr>();
      
      // assignment in the end of A2 to restore variables which are not in ns2
      List<ZName> lstAssBhdZName2 = new ArrayList<ZName>();
      List<Expr> lstAssBhdExpr2 = new ArrayList<Expr>();

      Iterator<Entry<String, Pair<String, Term>>> it = mapPv.entrySet().iterator();
      while (it.hasNext()) {
        Map.Entry<String, Pair<String, Term>> pairs = (Map.Entry<String, Pair<String, Term>>) it
            .next();

        if (pairs != null) {
          // VarDecl
          // create Name List with Stroke
          List<Name> ln = new ArrayList<Name>();
          Name name = fac_.createZName(pairs.getValue().getFirst(), fac_.createZStrokeList(), null);
          ln.add(name);
          // create Namelist
          NameList nl1 = fac_.createZNameList(ln);
          VarDecl vd = fac_.createVarDecl(nl1, (Expr) (pairs.getValue().getSecond()));
          declList.add(vd);

          // Assignment
          lstAssFrtZName.add((ZName) name);
          lstAssFrtExpr.add(fac_.createRefExpr(
              fac_.createZName(pairs.getKey(), fac_.createZStrokeList(), null),
              fac_.createZExprList(), false, false));

          // For the variables in pv1 but not in ns1, we need to restore
          if (pv1.contains(pairs.getKey()) && !ns1.contains(pairs.getKey())) {
            lstAssBhdZName1.add(fac_.createZName(pairs.getKey(), fac_.createZStrokeList(), null));
            lstAssBhdExpr1.add(fac_.createRefExpr(
                fac_.createZName(pairs.getValue().getFirst(), fac_.createZStrokeList(), null),
                fac_.createZExprList(), false, false));
          }
          
       // For the variables in pv2 but not in ns2, we need to restore
          if (pv2.contains(pairs.getKey()) && !ns2.contains(pairs.getKey())) {
            lstAssBhdZName2.add(fac_.createZName(pairs.getKey(), fac_.createZStrokeList(), null));
            lstAssBhdExpr2.add(fac_.createRefExpr(
                fac_.createZName(pairs.getValue().getFirst(), fac_.createZStrokeList(), null),
                fac_.createZExprList(), false, false));
          }
        }
      }

      if(!lstAssBhdZName1.isEmpty()) {
        // AssignmentCommand
        ZExprList lstZExpr = fac_.createZExprList(lstAssBhdExpr1);
        AssignmentPairs assPair = cfac_.createAssignmentPairs(fac_.createZNameList(lstAssBhdZName1),
            lstZExpr);
        AssignmentCommand assCmd = cfac_.createAssignmentCommand(assPair);
        
        // SeqAction
        List<CircusAction> lstCAction = new ArrayList<CircusAction>();
        lstCAction.add(((ParallelAction)ca).getLeftAction());
        lstCAction.add(assCmd);
        
        ((ParallelAction)ca).setLeftAction(cfac_.createSeqAction(lstCAction));
      }
      
      if(!lstAssBhdZName2.isEmpty()) {
        // AssignmentCommand
        ZExprList lstZExpr = fac_.createZExprList(lstAssBhdExpr2);
        AssignmentPairs assPair = cfac_.createAssignmentPairs(fac_.createZNameList(lstAssBhdZName2),
            lstZExpr);
        AssignmentCommand assCmd = cfac_.createAssignmentCommand(assPair);
        
        // SeqAction
        List<CircusAction> lstCAction = new ArrayList<CircusAction>();
        lstCAction.add(((ParallelAction)ca).getRightAction());
        lstCAction.add(assCmd);
        
        ((ParallelAction)ca).setRightAction(cfac_.createSeqAction(lstCAction));
      }
      
      // assignment in the beginning of variable block
      if (!lstAssFrtZName.isEmpty()) {
        // AssignmentCommand
        ZExprList lstZExpr = fac_.createZExprList(lstAssFrtExpr);
        AssignmentPairs assPair = cfac_.createAssignmentPairs(fac_.createZNameList(lstAssFrtZName),
            lstZExpr);
        AssignmentCommand assCmd = cfac_.createAssignmentCommand(assPair);
        
        // SeqAction
        List<CircusAction> lstCAction = new ArrayList<CircusAction>();
        lstCAction.add(assCmd);
        lstCAction.add(pa);
        ca = cfac_.createSeqAction(lstCAction);
      }

//      AxPara axpara = assembleZPara(paraName, pred, declList);
      VarDeclCommand vdc = cfac_.createVarDeclCommand(declList, ca);
      visit(vdc);
    }

    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitOutputFieldAnn(OutputFieldAnn term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitActionType(ActionType term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitInterleaveAction(InterleaveAction term)
  {
    String str = str_;

    save_str();
    String ns1 = "" + safe_visit(term.getNameSet().get(0));
    String ns2 = "" + safe_visit(term.getNameSet().get(1));
    restore_str();

    // if both ns1 and ns2 are empty
    if (ns1.equals("{}") && ns2.equals("{}")) {
      str_ += "((";
      visit(term.getLeftAction());
      str_ += ")";
      str_ += " ||| ";
      str_ += "(";
      visit(term.getRightAction());
      str_ += "))";
    }

    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitAlphabetisedParallelActionIte(AlphabetisedParallelActionIte term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  /*
   * (non-Javadoc)
   * @see
   * net.sourceforge.czt.circus.visitor.GuardedActionVisitor#visitGuardedAction(net.sourceforge.
   * czt.circus.ast.GuardedAction)
   * Guarded Command
   */
  @Override
  public Object visitGuardedAction(GuardedAction term)
  {
    String str = str_;

    Pred pred = term.getPred();
    str_ += "(";

//    if (pred instanceof MemPred) {
      save_str();
      String strpred = "" + visit(pred);
      restore_str();
//
//      // equality, mixfix = true, form: n = {m} or n \neq m
//      if (((MemPred) pred).getMixfix()) {
//        String lstr = new String();
//        String rstr = new String();
//        save_str();
//        lstr += visit(((MemPred) pred).getLeftExpr());
//        rstr += visit(((MemPred) pred).getRightExpr());
//        restore_str();
//
//        List<String> lst = new ArrayList<String>();
//        if ((isState(lstr, lst) || isState(rstr, lst)) && (!isLocVar(lstr) && !isLocVar(rstr))) {
//          // assembly a Z paragraph
//          String paraname;
//          if (map_.getGANum(proname_) != null) {
//            paraname = proname_ + "_GA" + map_.getGANum(proname_);
//            map_.incGANum(proname_);
//          }
//          else {
//            Random randomGenerator = new Random();
//            /** GA100 to GA200 for random use only */
//            paraname = proname_ + "_GA" + String.format("%d", randomGenerator.nextInt(100) + 100);
//          }
//          paralist_.add(assembleZPara(paraname, pred));
//          str_ += "(" + paraname + " -> SKIP);";
//        }
//        // only local variables
//        else if ((!isState(lstr, lst) && !isState(rstr, lst)) && (isLocVar(lstr) || isLocVar(rstr))) {
//          str_ += strpred + " & ";
//        }
//        // mixed local and state variables
//        else if ((isState(lstr, lst) || isState(rstr, lst)) && (isLocVar(lstr) || isLocVar(rstr))) {
//          // assembly a Z paragraph
//          String paraname;
//          if (map_.getGANum(proname_) != null) {
//            paraname = proname_ + "_GA" + map_.getGANum(proname_);
//            map_.incGANum(proname_);
//          }
//          else {
//            Random randomGenerator = new Random();
//            /** GA100 to GA200 for random use only */
//            paraname = proname_ + "_GA" + String.format("%d", randomGenerator.nextInt(100) + 100);
//          }
//          paralist_.add(assembleZPara(paraname, pred));
//          str_ += "(" + paraname + " -> SKIP);";
//        }
//      }
//    }
//    else {
//    save_str();
//    String strpred = "" + safe_visit(pred);
//    restore_str();

    /**
     * A list of state variable name in this predicate
     */
    List<String> slst = new ArrayList<String>();
    /**
     * A list of local variable name and its type in this predicate. Type is used to construct the Z
     * schema
     */
    List<Pair<String, Term>> llst = new ArrayList<Pair<String, Term>>();
//      if(isState(strpred, lst))
//      {
//        for (String v: lst) {
//          str_ += v + "?" + v +" -> ";
//        }
//      }
//      str_ += strpred;
//    // only state variables are involved ( var = 0)
//    if (isState(strpred, slst) && !isLocVar(strpred, llst)) {
//      // assembly a Z paragraph
//      String paraname;
//      if (map_.getGANum(proname_) != null) {
////        paraname = proname_ + "_GA" + map_.getGANum(proname_);
//        paraname = MessageFormat.format(CSPPredExpPattern.GA_NAME_PATT, proname_,
//            map_.getGANum(proname_));
//        map_.incGANum(proname_);
//      }
//      else {
//        Random randomGenerator = new Random();
//        /** GA100 to GA200 for random use only */
////        paraname = proname_ + "_GA" + String.format("%d", randomGenerator.nextInt(100) + 100);
//        paraname = MessageFormat.format(CSPPredExpPattern.GA_NAME_PATT, proname_,
//            String.format("%d", randomGenerator.nextInt(100) + 100));
//      }
////      paralist_.add(assembleZPara(paraname, pred));
//      AddPara(assembleZPara(paraname, pred));
//      cspspec_.addHideCSPB(paraname);
//      str_ += "(" + paraname + " -> SKIP);";
//    }
//    // only local variables
//    else if (!isState(strpred, slst) && isLocVar(strpred, llst)) {
//      str_ += "(" + strpred + ") & ";
//    }
//    // mixed local and state variables
//    else if (isState(strpred, slst) && isLocVar(strpred, llst)) {
//      // assembly a Z paragraph
//      String paraname;
//      if (map_.getGANum(proname_) != null) {
////        paraname = proname_ + "_GA" + map_.getGANum(proname_);
//        paraname = MessageFormat.format(CSPPredExpPattern.GA_NAME_PATT, proname_,
//            map_.getGANum(proname_));
//        map_.incGANum(proname_);
//      }
//      else {
//        Random randomGenerator = new Random();
//        /** GA100 to GA200 for random use only */
////        paraname = proname_ + "_GA" + String.format("%d", randomGenerator.nextInt(100) + 100);
//        paraname = MessageFormat.format(CSPPredExpPattern.GA_NAME_PATT, proname_,
//            String.format("%d", randomGenerator.nextInt(100) + 100));
//      }
////      paralist_.add(assembleZPara(paraname, pred, llst));
//      AddPara(assembleZPara(paraname, pred, llst));
//
//      cspspec_.addHideCSPB(paraname);
//      for (Pair<String, Term> p : llst) {
//        paraname += "!" + p.getFirst();
//      }
//      str_ += "(" + paraname + " -> SKIP);";
//    }
//    else {
//      // Invalid guard expression
//      throw new CztException("Invalid guard [" + strpred + "]");
//    }

    isLocVar(strpred, llst);
    // assembly a Z paragraph
    // paraName
    String paraname = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.GA_NAME_PATT), proname_,
        map_.incn());

  //  paralist_.add(assembleZPara(paraname, pred, llst));
    AddPara(assembleZPara(paraname, pred, llst));
  
    cspspec_.addHideCSPB(paraname);
    for (Pair<String, Term> p : llst) {
      paraname += "!" + p.getFirst();
    }
    str_ += "(" + paraname + " -> SKIP);";
    
    visit(term.getCircusAction());
    str_ += ")";
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitInputField(InputField term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitBasicChannelSetExpr(BasicChannelSetExpr term)
  {
    String str = str_;

    str_ += "{| ";
    visit(term.getCircusCommunicationList());
    str_ += " |}";
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitActionPara(ActionPara term)
  {
    String str = str_;
    str_ += term.getZName().toString() + " = ";
    visit(term.getCircusAction());
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitAlphabetisedParallelProcessIte(AlphabetisedParallelProcessIte term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCircusCommunicationList(CircusCommunicationList term)
  {
    String str = str_;

    save_str();
    String clist = "";
    boolean first = true;
    for (Communication c : term) {
      if (first) {
        clist += safe_visit(c);
        first = false;
      }
      else {
        clist += ",";
        clist += safe_visit(c);
      }
    }
    restore_str();
    str_ += clist;

    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitChannelDecl(ChannelDecl term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitActionSignatureList(ActionSignatureList term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitInterleaveProcessIdx(InterleaveProcessIdx term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitExtChoiceActionIte(ExtChoiceActionIte term)
  {
    String str = str_;
    ExtChoiceActionIte term2 = ZUtils.cloneTerm(term);

    str_ += "( []";
    visit(term2.getZDeclList());
    str_ += " @ ";
    visit(term2.getCircusAction());
    str_ += " )";
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitParallelProcessIte(ParallelProcessIte term)
  {
    String str = str_;
    // TODO
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
//    int fieldcnt = 0;

    /*
     * number of local variables introduced from this communication
     */
    int locVarCnt = 0;
    int locVarSize = loc_var_.size();

    str_ += "(";
    // visit(term.getCommunication().getChannelExpr());
    // str_ += term.getCommunication().toString();
    Communication comm = term.getCommunication();

    String strBef = str_;
    save_str();
    String strEvt = safe_visit(comm);

//    String strEvt = subStr(str_, strBef);
    restore_str();

    locVarCnt = loc_var_.size() - locVarSize;

    String opname = Fvar(strEvt);

    str_ += opname;
    str_ += " -> ";
    visit(term.getCircusAction());
    str_ += ")";

    /*
     * remove the variables from loc_var_
     */
    for (int i = 0; i < locVarCnt; i++)
      loc_var_.pop();
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitAssignmentCommand(AssignmentCommand term)
  {
//
    String str = str_;

    AssignmentCommand term2 = ZUtils.cloneTerm(term);

    // paraName
    String paraName = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.ASSIGN_NAME_PATT), proname_,
        map_.incn());
    // channel definition
    String chnDecl = "channel " + paraName;
    // CSP event name, such as assOp!x!y?z
    String eventName = paraName;

    //
    // 1. for assemble of assOp paragraph
    //
//    ZNameList fp = fac_.createZNameList();
//    // ZName
//    ZName paraname = fac_.createZName(paraName, fac_.createZStrokeList(), null);
//
    ZDeclList declList = fac_.createZDeclList();
//
//    // State Paragraph Name and \Delta State Paragraph
//    String stName = map_.getStatPara(proname_);
//    ZName stname = fac_.createZName(ZString.DELTA + stName, fac_.createZStrokeList(), null);
//    RefExpr expr = fac_.createRefExpr(stname, fac_.createZExprList(), false, false);
//
//    InclDecl inclDecl = fac_.createInclDecl(expr);
//    declList.add(inclDecl);

    Pred pred = null;
    //
//    List<String> vlist = new ArrayList<String>();

    // ///

//    List<Pair<String, String>> list = new ArrayList<Pair<String, String>>();
    ZNameList nl = term2.getAssignmentPairs().getZLHS();
    ZExprList el = term2.getAssignmentPairs().getZRHS();

    // input variables list <variable name, decl>
    // for assembling of VarDecl in assOp and eventname update as well
    List<Pair<String, Decl>> ilpsd = new ArrayList<Pair<String, Decl>>();

    // output variables list <variable name, decl>
    // for assembling of VarDecl in assOp and eventname update as well
    List<Pair<String, Decl>> olpsd = new ArrayList<Pair<String, Decl>>();

    String lhs = "";
    String rhs = "";

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

    save_str();
    for (int i = 0; i < nl.size(); i++) {
      // LHS
      // only one variable is possible
      lhs = "" + visit(nl.get(i));
      if (isState(lhs, slst)) {
        lstStL.addAll(slst);
        // s => s'
        nl.get(i).accept(
            new VariableRenamingSchemaVisitor(slst, VariableRenameSchema.VRS_APPEND_NEXTSTROKE));
      }
      else if (isLocVar(lhs, lllst)) {
        // Only one variable in each separate assignment
        slst.clear();
        slst.add(lllst.get(0).getFirst());
        // l => l!
        nl.get(i).accept(
            new VariableRenamingSchemaVisitor(slst, VariableRenameSchema.VRS_APPEND_OUTSTROKE));

        // VarDecl
        // create OutStroke !
        List<Stroke> ls = new ArrayList<Stroke>();
        Stroke ot = fac_.createOutStroke();
        ls.add(ot);
        // create Name List with InStroke
        List<Name> ln = new ArrayList<Name>();
        Name name = fac_.createZName(lllst.get(0).getFirst(), fac_.createZStrokeList(ls), null);
        ln.add(name);

        // create Namelist
        NameList nl1 = fac_.createZNameList(ln);
        VarDecl vd = fac_.createVarDecl(nl1, (Expr) (lllst.get(0).getSecond()));

        olpsd.add(new Pair<String, Decl>(lllst.get(0).getFirst(), vd));
//        declList.add(vd);
      }

      // RHS
      rhs = "" + visit(el.get(i));
      if (isLocVar(rhs, lllst)) {
        slst.clear();
        for (Pair<String, Term> pst : lllst) {
          slst.add(pst.getFirst());

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
//          declList.add(vd);
        }
        // l => l?
        el.get(i).accept(
            new VariableRenamingSchemaVisitor(slst, VariableRenameSchema.VRS_APPEND_INSTROKE));
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
    restore_str();

    /**
     * For pred, add other state variables' equality spec in pred
     * For example, if there are three state variables (s1, s2, s3) in this process
     * and s1' is updated by assignment. Then we should add s2'=s2 and s3'=s3 in pred
     * lstStL - state variables name in LHS
     */
    // get a list of state variables of this process
    List<String> lstr = map_.getStatListWithProName(proname_);
    // remove state variables which are occurred in LHS of assignment
    lstr.removeAll(lstStL);

    for (String v : lstr) {
      List<Stroke> ls = new ArrayList<Stroke>();
      Stroke next = fac_.createNextStroke();
      ls.add(next);
      ZStrokeList zsl = fac_.createZStrokeList(ls);
      // LHS (s')
      RefExpr lre = fac_.createRefExpr(fac_.createZName(v, zsl, null), fac_.createZExprList(),
          false, false);
      // RHS (s)
      RefExpr rre = fac_.createRefExpr(fac_.createZName(v, fac_.createZStrokeList(), null),
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

    save_str();
    // input variables of assOp paragraph will get values from CSP output
    // for each variable, we need to use getn?v to get the value of local variable
    // v first
    for (Pair<String, Decl> p : ilpsd) {
      if (chnDecl.equals("channel " + paraName)) {
        chnDecl += ": " + safe_visit(((VarDecl) p.getSecond()).getExpr());
      }
      else {
        chnDecl += "." + safe_visit(((VarDecl) p.getSecond()).getExpr());
      }

      eventName += "!" + p.getFirst();
      declList.add(p.getSecond());
    }

    // output variables of assOp paragraph will update values in CSP
    for (Pair<String, Decl> p : olpsd) {
      if (chnDecl.equals("channel " + paraName)) {
        chnDecl += ": " + safe_visit(((VarDecl) p.getSecond()).getExpr());
      }
      else {
        chnDecl += "." + safe_visit(((VarDecl) p.getSecond()).getExpr());
      }
      eventName += "?" + p.getFirst();
      declList.add(p.getSecond());
    }
    restore_str();

    // for each local variable in eventName (such as x and y in assOp!x!y), get their value first
    // for each local variable in eventName (such as y in assOp!x?y), update their value at last
    eventName = Fvar(eventName);

    AxPara axpara = assembleZPara(paraName, pred, declList);
//    ZSchText schText = fac_.createZSchText(declList, pred);
//    SchExpr schExpr = fac_.createSchExpr(schText);
//
//    ConstDecl cd = fac_.createConstDecl(paraname, schExpr);
//
//    ZDeclList declList0 = fac_.createZDeclList();
//    declList0.add(cd);
//    SchText st = fac_.createZSchText(declList0, null);
//
//    AxPara axpara = fac_.createAxPara(fp, st, Box.OmitBox);
//    paralist_.add(axpara);
    AddPara(axpara);

    // assOp!x!y?z -> putn!z -> SKIP
    str_ += eventName /* + updateVar */+ " -> SKIP";

    cspspec_.addHideCSPB(paraName);
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitParamProcess(ParamProcess term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitAlphabetisedParallelProcessIdx(AlphabetisedParallelProcessIdx term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  /*
   * Global ZExprList, used for parameterised action only to pass expr list to action
   */
  private ZExprList zel_ = null;

  /*
   * (non-Javadoc)
   * @see
   * net.sourceforge.czt.circus.visitor.CallActionVisitor#visitCallAction(net.sourceforge.czt.circus
   * .ast.CallAction)
   * Action Invocation (Action Reference will come here)
   * Schema Express as Action without \\lschexpract and \\rschexpract surrounded will come here as
   * well.
   * But chema Express as Action with \\lschexpract and \\rschexpract surrounded will come to
   * visitSchExprAction
   */
  @Override
  public Object visitCallAction(CallAction term)
  {
    /**
     * Circus action reference call. In other words, it permits a name to be an action.
     * That is, it contains a reference name to lookup the action definition.
     */
    String str = str_;

    String name = term.getZName().getWord();
    Debug.debug_print("visitCallAction:[IN] " + term.getZName().getWord());
    /*
     * the name containing _Action_ is regarded as Action and it doesn't need to append SKIP. Only
     * Schema Express will
     * But action invocation (reference) need to unfold/expand it
     */
    if (name.contains("_Action_")) {
      /** For action name */
      String act = "";
      Pair<String, Term> p = map_.getRepByNewName(proname_, name);
      if (p != null) {
        Term action = null;

        zel_ = term.getZExprList();

        save_str();
        if (p.getSecond() instanceof ActionPara) {
          action = ZUtils.cloneTerm(((ActionPara) p.getSecond()).getCircusAction());
          act += safe_visit(action);
        }
        restore_str();
        str_ += "(" + act + ")";
        zel_ = null;
      }

      String tmp = subStr(str_, str);
      return tmp;
    }
    // not action invocation, it should be schema expression as action
    else {
      // even for schema expression as action without bracket, we will take it as schema expression
      // as action
      RefExpr re = fac_.createRefExpr(term.getZName(), fac_.createZExprList(), false, false);
      SchExprAction sea = cfac_.createSchExprAction(re);
      visit(sea);
    }

    /** not action and not schema name */
    if (str.equals(str_)) {
      str_ += name;
    }

    Debug.debug_print("visitCallAction:[OUT] " + subStr(str_, str));
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitExtChoiceProcessIte(ExtChoiceProcessIte term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  /**
   * var x:T \circspot A => |~| x:T @ A
   */
  @Override
  public Object visitVarDeclCommand(VarDeclCommand term)
  {
    String str = str_;
    String text = "(|~|";
    str_ += text;

    List<Triple<String, Pair<String, Term>, String>> lst_decl = new ArrayList<Triple<String, Pair<String, Term>, String>>();
    List<String> lst_num = new ArrayList<String>();

    int declNum = 0;
    // multiple decl, such as var x:\nat; y:\num \circspot
    for (Decl decl : term.getZDeclList()) {
      if (declNum != 0) {
        str_ += ",";
      }
      String decl_str = "" + visit(decl);
      String[] strs = decl_str.trim().split("[,]"); // \s - [ \t\n\x0B\f\r]
      for (int i = 0; i < strs.length; i++) {
        String[] var_expr = strs[i].trim().split("[:]");
        // get the global number for Var process numbering
        String n = getandIncVarNum();
        lst_num.add(n);
        lst_decl.add(new Triple<String, Pair<String, Term>, String>(var_expr[0].trim(),
            new Pair<String, Term>(var_expr[1].trim(), ((VarDecl) decl).getExpr()), n));
        // Add an additional Var process to store and retrieve the variable
        addAdditionalVarProcess(n, var_expr[1].trim());
      }
      declNum++;
    }
    varblock_var_.add(lst_decl);

    str_ += "@ (";
    save_str();
    String act = "" + safe_visit(term.getCircusAction());
    restore_str();

    String strUpdateVar = "";
    for (Triple<String, Pair<String, Term>, String> p : lst_decl) {
      strUpdateVar += MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_PUT), p.getThird()) + "!"
          + p.getFirst() + " -> ";
    }

    // Fmem
    act = strUpdateVar + "SKIP; " + act;
    for (String n : lst_num) {
      String chnset = "{|" + MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_PUT), n) + ", "
          + MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_GET), n) + ", "
          + MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_END), n) + "|}";
      act = "(" + act + ");" + MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_END), n)
          + " -> SKIP";
      act = "((" + act + ") [|" + chnset + "|] "
          + MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_NAME), n) + ") \\" + chnset;
    }
    str_ += act;
    str_ += ")";
    str_ += ")";
    String tmp = subStr(str_, str);

    varblock_var_.pop();
    return tmp;
  }

  @Override
  public Object visitImplicitChannelAnn(ImplicitChannelAnn term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
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
  public Object visitSeqProcessIdx(SeqProcessIdx term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCircusNameSetList(CircusNameSetList term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitInterleaveProcess(InterleaveProcess term)
  {
    String str = str_;
    // TODO
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
  public Object visitCircusFieldList(CircusFieldList term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitParamAction(ParamAction term)
  {
    String str = str_;
    // number of variables consumed
    int var_no = 0;

    // for parameterised action, parameterisation by value, parameterisation by result
    // and parameterisation by value and result, the parameter expr list is not null
    assert (zel_ != null);

    ZDeclList zdl = term.getZDeclList();
    CircusAction ca = ZUtils.cloneTerm(term.getCircusAction());

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

    for (Decl decl : zdl) {
      // for parameterised action like (x:T•A)(e)
      // x in A is replaced by e
      if (decl instanceof VarDecl) {
        save_str();
        // x,y:T; z:Tz => x:T, y:T, z:Tz
        String strDecls = "" + safe_visit(decl);
        restore_str();

        // map from variable to its parameter
        List<Pair<String, String>> lstOldNew = new ArrayList<Pair<String, String>>();

        // {"x:T", "y:T", "z:Tz"} array
        String[] strVars = strDecls.trim().split(",");
        for (String strDecl : strVars) {
          // => {"x", "T"}
          String[] strVar = strDecl.trim().split(":");
          // actual parameter for this variable
          save_str();
          String expr = "" + safe_visit(zel_.get(var_no++));
          restore_str();
          // => {{"x", "e1"}, {"y", "e2"}, {"z", "e3"}}
//          lstOldNew.add(new Pair<String, String>(strVar[0].trim(), "(" + expr + ")"));
          lstOldNew.add(new Pair<String, String>(strVar[0].trim(), expr));
        }
        // rename variables to parameters in action ca
        VariableRenamingSchemaVisitor vrsv = new VariableRenamingSchemaVisitor(
            VariableRenameSchema.VRS_ACTION_RENAME, lstOldNew);
        ca.accept(vrsv);
      }
      // (\\circval\\ r: 0..10 \\circspot A)(1)
      else if (decl instanceof QualifiedDecl) {
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
              lstFrtExpr.add(zel_.get(var_no++));
            }
            break;
          case Result :
            for (Name name : ((QualifiedDecl) decl).getZNameList()) {
              if (zel_.get(var_no) instanceof RefExpr) {
                lstBhdZName.add(((RefExpr) zel_.get(var_no++)).getZName());
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
              lstFrtExpr.add(zel_.get(var_no));

              if (zel_.get(var_no) instanceof RefExpr) {
                lstBhdZName.add(((RefExpr) zel_.get(var_no++)).getZName());
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

    if (!lstDecl.isEmpty()) {
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
    }

    visit(ca);

    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitStateUpdate(StateUpdate term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitChannelType(ChannelType term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitHideAction(HideAction term)
  {
    String str = str_;
    visit(term.getCircusAction());
    str_ += " \\ ";
    visit(term.getChannelSet());

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

    str_ += name;

    ChannelSet cs = term.getChannelSet();
    if (cs instanceof CircusChannelSet) {
      if (((CircusChannelSet) cs).getExpr() instanceof BasicChannelSetExpr) {
        CircusCommunicationList ccl = ((BasicChannelSetExpr) ((CircusChannelSet) cs).getExpr())
            .getCircusCommunicationList();
        if (ccl.size() == 0) {
          // empty set
          str_ += " = {||}";
        }
        else {
          boolean first = true;
          str_ += " = {| ";
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
      }
    }

    String tmp = subStr(str_, str);

    return tmp;
  }

  /*
   * (non-Javadoc)
   * @see
   * net.sourceforge.czt.circus.visitor.SpecStmtCommandVisitor#visitSpecStmtCommand(net.sourceforge
   * .czt.circus.ast.SpecStmtCommand)
   * TODO:
   * limits:
   * dashed variables occurred in post should be included in frame (znl)
   */
  @Override
  public Object visitSpecStmtCommand(SpecStmtCommand term)
  {
    String str = str_;

    ZNameList znl = ZUtils.cloneTerm(term.getZFrame());
    Pred pre = ZUtils.cloneTerm(term.getPre());
    Pred post = ZUtils.cloneTerm(term.getPost());

    // paraName
    String paraName = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.SPEC_NAME_PATT), proname_, map_.incn());
    // channel definition
    String chnDecl = "channel " + paraName;
    // CSP event name, such as assOp!x!y?z
    String eventName = paraName;

    //
    // 1. for assemble of assOp paragraph
    //
//    ZNameList fp = fac_.createZNameList();
//    // ZName
//    ZName paraname = fac_.createZName(paraName, fac_.createZStrokeList(), null);
//
    ZDeclList declList = fac_.createZDeclList();
//
//    // State Paragraph Name and \Delta State Paragraph
//    String stName = map_.getStatPara(proname_);
//    ZName stname = fac_.createZName(ZString.DELTA + stName, fac_.createZStrokeList(), null);
//    RefExpr expr = fac_.createRefExpr(stname, fac_.createZExprList(), false, false);
//
//    InclDecl inclDecl = fac_.createInclDecl(expr);
//    declList.add(inclDecl);

    Pred pred = null;

    // input variables list <variable name, decl>
    // for assembling of VarDecl in assOp and eventname update as well
    List<Pair<String, Decl>> ilpsd = new ArrayList<Pair<String, Decl>>();

    // output variables list <variable name, decl>
    // for assembling of VarDecl in assOp and eventname update as well
    List<Pair<String, Decl>> olpsd = new ArrayList<Pair<String, Decl>>();

    // //////////////
    // specOp = [∆StatePar ; lv? : Tlv ; slv! : Tslv | pre ∧ post]
    // //////////////
    // 1. get the local variables (and their types) evaluated in pre and post

    save_str();
    String strPre = "" + safe_visit(pre);
    String strPost = "" + safe_visit(post);
    restore_str();

    // for each dash variable in post, it should be in frame
    List<String> lstDPost = new ArrayList<String>();
    // map to lstDPost, but just remove PRIME (') from each dash variables
    List<String> lstUDPost = new ArrayList<String>();
    getDashVar(strPost, lstDPost);

    List<String> lstName = new ArrayList<String>();
    for (Name n : znl) {
      lstName.add(n.toString());
    }

    for (String dv : lstDPost) {
      // remove the last PRIME (')
      String uds = dv.substring(0, dv.length() - 1);
      lstUDPost.add(uds);
      // if lstName is empty, it means frame is empty. It is mapped to ":[pre, post]" without frame
      if (!lstName.contains(uds) && !lstName.isEmpty()) {
        throw new CztException("Each dashed variable in post must be in frame of specification!");
      }
    }

    /**
     * A list of local variable name and its type in this predicate. Type is used to construct the Z
     * schema
     */
    List<Pair<String, Term>> llst = new ArrayList<Pair<String, Term>>();
    List<Pair<String, Term>> llstPre = new ArrayList<Pair<String, Term>>();
    List<Pair<String, Term>> llstPost = new ArrayList<Pair<String, Term>>();
    List<Pair<String, Term>> llstPostDashVar = new ArrayList<Pair<String, Term>>();

    // determine undashed local variables from pre and post
    isLocUndashVar(strPre, llstPre);
    isLocUndashVar(strPost, llstPost);
    llst.addAll(llstPre);
    llst.addAll(llstPost);

    isLocDashVar(strPost, llstPostDashVar);

    // 2. and replace local variables in pre and post by (lv => lv?)
    /**
     * A list of variable name
     */
    List<String> slst = new ArrayList<String>();
    for (Pair<String, Term> pst : llst) {
      if (slst.contains(pst.getFirst())) {
        continue;
      }

      slst.add(pst.getFirst());

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

    // l => l?
    pre.accept(new VariableRenamingSchemaVisitor(slst, VariableRenameSchema.VRS_APPEND_INSTROKE));
    post.accept(new VariableRenamingSchemaVisitor(slst, VariableRenameSchema.VRS_APPEND_INSTROKE));

    // 3. replace local variables in frame in post by (slv' => slv!)
    // p has format (lv', Tlv)
    slst.clear();
    for (Pair<String, Term> p : llstPostDashVar) {
      assert (p.getFirst().endsWith("" + ZChar.PRIME));

      slst.add(p.getFirst());

      // remove the last PRIME (')
      String uds = p.getFirst().substring(0, p.getFirst().length() - 1);

      // VarDecl
      // create OutStroke !
      List<Stroke> ls = new ArrayList<Stroke>();
      Stroke ot = fac_.createOutStroke();
      ls.add(ot);
      // create Name List with InStroke
      List<Name> ln = new ArrayList<Name>();
      Name name = fac_.createZName(uds, fac_.createZStrokeList(ls), null);
      ln.add(name);

      // create Namelist
      NameList nl1 = fac_.createZNameList(ln);
      VarDecl vd = fac_.createVarDecl(nl1, (Expr) (p.getSecond()));

      olpsd.add(new Pair<String, Decl>(uds, vd));
    }

    // Replace slv' by slv!ssh
    post.accept(new VariableRenamingSchemaVisitor(slst, VariableRenameSchema.VRS_NEXT_OUTSTROKE));

    // 4. Assemble the predicate by pre \land post
    /**
     * For pred, add other state variables' equality spec in pred
     * For example, if there are three state variables (s1, s2, s3) in this process
     * and s1' is updated by assignment. Then we should add s2'=s2 and s3'=s3 in pred
     * lstUDPost - the variable name corresponding to all dashed variables in post
     * lstStL - state variables name in LHS
     */
    // get a list of state variables of this process
    List<String> lstr = map_.getStatListWithProName(proname_);
    // remove state variables which are occurred in LHS of assignment
    lstr.removeAll(lstUDPost);

    pred = post;
    for (String v : lstr) {
      List<Stroke> ls = new ArrayList<Stroke>();
      Stroke next = fac_.createNextStroke();
      ls.add(next);
      ZStrokeList zsl = fac_.createZStrokeList(ls);
      // LHS (s')
      RefExpr lre = fac_.createRefExpr(fac_.createZName(v, zsl, null), fac_.createZExprList(),
          false, false);
      // RHS (s)
      RefExpr rre = fac_.createRefExpr(fac_.createZName(v, fac_.createZStrokeList(), null),
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

    List<Pred> lp = new ArrayList<Pred>();
    lp.add(pre);
    lp.add(pred);
    AndPred ap = fac_.createAndPred(lp, And.Wedge);
    pred = ap;

    // 5. Determine the type of slv which are local variables in Frame of specification

    // 6. VarDecl of specOp: \Delta StatePar, lv?, slv!
    save_str();
    // input variables of assOp paragraph will get values from CSP output
    // for each variable, we need to use getn?v to get the value of local variable
    // v first
    for (Pair<String, Decl> p : ilpsd) {
      if (chnDecl.equals("channel " + paraName)) {
        chnDecl += ": " + safe_visit(((VarDecl) p.getSecond()).getExpr());
      }
      else {
        chnDecl += "." + safe_visit(((VarDecl) p.getSecond()).getExpr());
      }

      eventName += "!" + p.getFirst();
      declList.add(p.getSecond());
    }

    // output variables of assOp paragraph will update values in CSP
    for (Pair<String, Decl> p : olpsd) {
      if (chnDecl.equals("channel " + paraName)) {
        chnDecl += ": " + safe_visit(((VarDecl) p.getSecond()).getExpr());
      }
      else {
        chnDecl += "." + safe_visit(((VarDecl) p.getSecond()).getExpr());
      }
      eventName += "?" + p.getFirst();
      declList.add(p.getSecond());
    }
    restore_str();

    AxPara axpara = assembleZPara(paraName, pred, declList);
//    ZSchText schText = fac_.createZSchText(declList, pred);
//    SchExpr schExpr = fac_.createSchExpr(schText);
//
//    ConstDecl cd = fac_.createConstDecl(paraname, schExpr);
//
//    ZDeclList declList0 = fac_.createZDeclList();
//    declList0.add(cd);
//    SchText st = fac_.createZSchText(declList0, null);
//
//    AxPara axpara = fac_.createAxPara(fp, st, Box.OmitBox);
//    paralist_.add(axpara);
    AddPara(axpara);

    // 7. CSP: (get?lv -> (specOp!lv?slv -> put!slv -> SKIP [] fspecOp!lv -> DIV))

    // for each local variable in eventName (such as x and y in assOp!x!y), get their value first
    // for each local variable in eventName (such as y in assOp!x?y), update their value at last
    String csp;
    // get0?x -> get1?y -> specOp!x!y?x -> put0!x
    csp = Fvar(eventName);

    csp = csp.replace(eventName, "(" + eventName);
    // assOp!x!y?z -> putn!z -> SKIP
    csp += " -> SKIP";

    cspspec_.addHideCSPB(paraName);

    // 8. assemble fSpecOp
    if (pre instanceof TruePred) {
      str_ += csp + ")";
    }
    else {
      AxPara fap = Circus2ZCSPUtils.NegPreconditionSchema(proname_, axpara, cspspec_, map_);
//      paralist_.add(fap);
      AddPara(fap);

      str_ += "("
          + csp
          + " [] "
          + MessageFormat.format(FormatPattern.NEG_PRECONDITION_SCHEMA,
              removeInVarFromSchemaName(eventName)) + " -> DIV))";
    }

    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitIntChoiceProcessIdx(IntChoiceProcessIdx term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitIntChoiceProcessIte(IntChoiceProcessIte term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCommunicationType(CommunicationType term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitAlphabetisedParallelAction(AlphabetisedParallelAction term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitExtChoiceAction(ExtChoiceAction term)
  {
    String str = str_;
    str_ += "\n\t(";
    String left = safe_visit(term.getLeftAction());
    str_ += "\n\t[]\n\t";
    String right = safe_visit(term.getRightAction());
    str_ += "\n\t)";
    
    // if left and right are prefixing with geti event, it should be taken from left and right to
    // the front of external choice
    // for example, if left="get0?x->get1?y->get2?z->A", and right="get1?y->get3?u->B"
    // => get0?x->get1?y->get2?z->get3?u-> (A [] B)
    List<String> lgets = new ArrayList<String>();
    List<String> rgets = new ArrayList<String>();
    
    Fvar_pre(left,lgets);
    Fvar_pre(right,rgets);
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitSeqActionIte(SeqActionIte term)
  {
    String str = str_;
    SeqActionIte term2 = ZUtils.cloneTerm(term);

    str_ += "( ;";
    visit(term2.getZDeclList());
    str_ += " @ ";
    visit(term2.getCircusAction());
    str_ += " )";
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitProcessTransformerPred(ProcessTransformerPred term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitBasicProcess(BasicProcess term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitZSignatureList(ZSignatureList term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitLetVarAction(LetVarAction term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitAssignmentPairs(AssignmentPairs term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitOnTheFlyDefAnn(OnTheFlyDefAnn term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitNameSetType(NameSetType term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitParallelProcessIdx(ParallelProcessIdx term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitLetMuAction(LetMuAction term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitChannelPara(ChannelPara term)
  {
    String str = str_;
//    str_ += "channel ";
    List<String> lChnDecl = new ArrayList<String>();
    List<String> lChnName = new ArrayList<String>();

    for (Decl decl : term.getZDeclList()) {
      if (decl instanceof ChannelDecl) {
        // indicate if it is a channelfrom schema style or common style
        // channelfrom Tsch - true
        // channel c:T - false
        boolean bChnSchema = false;
        int size = ((ChannelDecl) decl).getZChannelNameList().size();

        save_str();
        // The number of channel name is larger than 0
        if (size > 0) {
          lChnName.add("" + safe_visit(((ChannelDecl) decl).getZChannelNameList().get(0)));
          for (int i = 1; i < size; i++) {
            str_ += ", ";
            lChnName.add("" + safe_visit(((ChannelDecl) decl).getZChannelNameList().get(i)));
          }
        }
        else {
          // no channel name. It is a channelfrom with schema type style
          bChnSchema = true;
        }

        Expr dexpr = ((ChannelDecl) decl).getExpr();
        String strExpr = "";
        // for ProdExpr, such as A \cross B \cross C. We would not translate to (A, B, C),
        // instead we would translate to A.B.C for channel declaration
        if (dexpr instanceof ProdExpr) {
          for (Expr expr : ((ProdExpr) dexpr).getZExprList()) {
            if (strExpr.equals("")) {
              strExpr += safe_visit(expr);
            }
            else {
              strExpr += "." + safe_visit(expr);
            }
          }
        }
        else {
          strExpr = "" + safe_visit(dexpr);
        }
        restore_str();

        if (bChnSchema == true) {
          // strExpr is the schema name
          List<Triple<String, String, Term>> lst = map_.getSchType(strExpr);
          if (!lst.isEmpty()) {
            for (Triple<String, String, Term> vname : lst) {
              if (!vname.getSecond().isEmpty()) {
                lChnDecl.add("channel " + vname.getFirst() + ": " + vname.getSecond());
              }
              else {
                lChnDecl.add("channel " + vname.getFirst());
              }
              map_.addChnDecl(vname.getFirst(), vname.getSecond(), vname.getThird());
            }
          }
        }
        else {
          String lvar = "";
          boolean first = true;
          for (String chnname : lChnName) {
            map_.addChnDecl(chnname, strExpr, dexpr);
            if (first) {
              lvar += chnname;
              first = false;
            }
            else {
              lvar += ", " + chnname;
            }
          }
          // if it's an empty expression, we don't need ":"
          if (!strExpr.isEmpty()) {
            lChnDecl.add("channel " + lvar + ": " + strExpr);
          }
          else {
            lChnDecl.add("channel " + lvar);
          }
        }
      }
    }

    if (!lChnDecl.isEmpty()) {
      boolean first = true;
      for (String chn : lChnDecl) {
        if (first) {
          str_ += chn;
          first = false;
        }
        else {
          str_ += "\n" + chn;
        }
      }
    }
    Debug.debug_print(str_);
    String tmp = subStr(str_, str);

    if (lChnDecl.size() <= 1) {
      return tmp;
    }
    else {
      return lChnDecl;
    }
  }

  @Override
  public Object visitNameSetPara(NameSetPara term)
  {
    String str = str_;

    visit(term.getZName());
    // TODO:
    visit(term.getNameSet());
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitDoGuardedCommand(DoGuardedCommand term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCircusNameSet(CircusNameSet term)
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
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitParallelActionIte(ParallelActionIte term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitProcessType(ProcessType term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitChannelSetType(ChannelSetType term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitChaosAction(ChaosAction term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitProcessSignature(ProcessSignature term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitRenameAction(RenameAction term)
  {
    String str = str_;

    List<Pair<String, String>> list = new ArrayList<Pair<String, String>>();
    ZNameList nl = term.getAssignmentPairs().getZLHS();
    ZExprList el = term.getAssignmentPairs().getZRHS();

    save_str();
    for (int i = 0; i < nl.size(); i++) {
      String lhs = "" + safe_visit(nl.get(i));
      String rhs = "" + safe_visit(el.get(i));
      list.add(new Pair<String, String>(lhs, rhs));
    }
    restore_str();

    // Fren function to replace the variables
    VariableRenamingSchemaVisitor vrsv = new VariableRenamingSchemaVisitor(
        VariableRenameSchema.VRS_ACTION_RENAME, list);
    // use cloneTerm to make original Term intact
    CircusAction ca = ZUtils.cloneTerm(term.getCircusAction());
    ca.accept(vrsv);
    visit(ca);
    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitProofObligationAnn(ProofObligationAnn term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitHideProcess(HideProcess term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSeqProcess(SeqProcess term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCircusChannelSetList(CircusChannelSetList term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitIntChoiceActionIte(IntChoiceActionIte term)
  {
    String str = str_;
    IntChoiceActionIte term2 = ZUtils.cloneTerm(term);

    str_ += "( |~|";
    visit(term2.getZDeclList());
    str_ += " @ ";
    visit(term2.getCircusAction());
    str_ += " )";
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitProcessSignatureAnn(ProcessSignatureAnn term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitActionTransformerPred(ActionTransformerPred term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSigmaExpr(SigmaExpr term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitExtChoiceProcess(ExtChoiceProcess term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitStateUpdateAnn(StateUpdateAnn term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitSeqAction(SeqAction term)
  {
    String str = str_;
    // action_just_before_seq_.push(true);
    visit(term.getLeftAction());
    // action_just_before_seq_.pop();

    str_ += "; ";
    // if(isNeedSeq())
    // {
    // str_ += "; ";
    // }
    // else
    // {
    // need_seq_.pop();
    // }
    visit(term.getRightAction());

    String tmp = subStr(str_, str);

    return tmp;
  }

  @Override
  public Object visitRenameProcess(RenameProcess term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitActionSignatureAnn(ActionSignatureAnn term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitProcessSignatureList(ProcessSignatureList term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitCircusActionList(CircusActionList term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  @Override
  public Object visitInterruptAction(InterruptAction term)
  {
    String str = str_;
    // TODO
    String tmp = subStr(str_, str);
    return tmp;
  }

  /*
   * Check if there are state variables in st and return a list of state variables founded
   * @param - lst is empty initially, then new state variables in st will be added to lst
   */
  public boolean isState(String st, List<String> lst)
  {
    List<String> lstr = map_.getStatListWithProName(proname_);
    boolean ret = false;

    lst.clear();
    /*
     * an expression can be split into a list of variables or expression
     * as well according to punctuation
     * ^\w - except [a-zA-Z_0-9]
     */
    String[] strs = st.split("[^\\w]");
    for (int i = 0; i < strs.length; i++) {
      if (lstr.contains(strs[i])) {
        ret = true;
        if (!lst.contains(strs[i])) {
          lst.add(strs[i]);
        }
      }
    }

    return ret;

//    if (lstr.contains(st)) {
//      // st = proc_x, lstr = {"proc_x", "proc_y", ... }
//      return true;
//    }
    // tuples like "(state, #A)" or "(state, Set(x))"
    // "[\\w\\p{Punct}]+" matches word or punctuation
    // \w - A word character: [a-zA-Z_0-9]
    // \p{Punct} - Punctuation: One of !"#$%&'()*+,-./:;<=>?@[\]^_`{|}~
    // else if(st.matches("\\(([\\w\\p{Punct}]+), *([\\w\\p{Punct}]+)\\)"))
    // {
    // // tuple
    // String str = st.replaceAll("\\(([\\w\\p{Punct}]+), *([\\w\\p{Punct}]+)\\)", "$1,$2");
    // String[] strs = str.split(",");
    // for(int i = 0; i < strs.length; i++)
    // {
    // if(lstr.contains(strs[i]))
    // {
    // return true;
    // }
    // }
    // }
//    else {
//      String[] strs = st.split("[,\\s]");
//      for (int i = 0; i < strs.length; i++) {
//        if (lstr.contains(strs[i])) {
//          return true;
//        }
//      }
//    }
//    return false;
  }

  /*
   * Check if there are state variables in st and return a list of state variables founded
   * @param - lst is empty initially, then new state variables in st will be added to lst
   */
  public boolean isStateWithExpr(String st, List<Pair<String, Term>> lst)
  {
    List<Pair<String, Term>> lstr = map_.getStatListWithExpProName(proname_);
    boolean ret = false;

    lst.clear();
    /*
     * an expression can be split into a list of variables or expression
     * as well according to punctuation
     * ^\w - except [a-zA-Z_0-9]
     */
    String[] strs = st.split("[^\\w]");
    for (Pair<String, Term> p : lstr) {
      for (int i = 0; i < strs.length; i++) {
        if (p.getFirst().equals(strs[i])) {
          lst.add(p);
          ret = true;
        }
      }
    }

    return ret;
  }

  /*
   * Check if there are state variables in st and return a list of state variables founded
   * @param - lst is empty initially, then new state variables in st will be added to lst
   */
  public boolean isStateWithExpr(Term term, List<Pair<String, Term>> lst)
  {
    boolean ret = true;
    
    StateVarsVisitor svv = new StateVarsVisitor(map_, proname_);
    term.accept(svv);
    
    lst.clear();
    lst = svv.getVarList();
    return ret;
  }
  
  /**
   * Return local variabls and their type from input string
   * No duplicated items in returned llst
   * and the item in llst should be ordered by its original order
   * for example, var x:Tx;y:Ty @ A.
   * x should be earlier than y in llst
   * 
   * @param st
   * @param llst
   * @return
   */
  public boolean isLocVar(String st, List<Pair<String, Term>> llst)
  {
    boolean ret = false;
    /*
     * an expression can be split into a list of variables or expression
     * as well according to punctuation
     * ^\w - except [a-zA-Z_0-9]
     */
    llst.clear();
    String[] strs = st.split("[^\\w]");

//    Map<String, Term> map = new HashMap<String, Term>();

//    for (int i = 0; i < strs.length; i++) {
    /*
     * Check from loc_var_ first
     */
    for (Pair<String, Term> ve : loc_var_) {
      for (int i = 0; i < strs.length; i++) {
        if (ve.getFirst().equals(strs[i])) {
          ret = true;
//          map.put(ve.getFirst(), ve.getSecond());
          llst.add(ve);
        }
      }
    }

    /*
     * Check from varblock_var_
     */
    if (varblock_var_.size() > 0) {
      for (int j = varblock_var_.size() - 1; j >= 0; j--) {
        for (Triple<String, Pair<String, Term>, String> p : varblock_var_.get(j)) {
          for (int i = 0; i < strs.length; i++) {
            if (strs[i].equals(p.getT1())) {
              ret = true;
              llst.add(new Pair<String, Term>(strs[i], p.getT2().getSecond()));
              break;
              // map.put(strs[i], p.getT2().getSecond());
              // return true;
            }
          }
        }
      }
    }
//    }

    // map to llst
//
//    for (Map.Entry<String, Term> entry : map.entrySet()) {
//      llst.add(new Pair<String, Term>(entry.getKey(), entry.getValue()));
//    }

    return ret;
  }

  /**
   * Assemble a Z paragraph (\Xi) according to inputs (without Input and output variables)
   * 
   * @param paraName - paragraph name
   * @param pred - predicate
   * @return
   */
  // 2.9 AxParaImpl
  // Box: SchBox
  // nameList: null [ZNameListImpl]
  // schText: [ZSchTextImpl]
  // declList: [ZDeclListImpl]
  // list: ArrayList<E>
  // elementData[0]: [ConstDeclImpl]
  // expr: [SchExprImpl]
  // schText: [ZSchTextImpl]
  // declList: [ZDeclListImpl]
  // list: ArrayList<E>
  // elementData[0]: [InclDeclImpl]
  // expr: \Delta AState [RefExprImpl]
  // pred: [AndPredImpl]
  // name: IncSec [ZNameImpl]
  // pred: null []
  //
  // \begin{schema}{IncSec}
  // \Delta AState\\
  // \where
  // sec' = (sec + 1) \mod 60\\
  // minute' = minute
  // \end{schema}
  public AxPara assembleZPara(String paraName, Pred pred)
  {
    ZNameList fp = fac_.createZNameList();
    // ZName
    ZName paraname = fac_.createZName(paraName, fac_.createZStrokeList(), null);

    ZDeclList declList = fac_.createZDeclList();

    // State Paragraph Name and \Xi State Paragraph
    String stName = map_.getStatPara(proname_);
    ZName stname = fac_.createZName(new Character('\u039E') + stName, fac_.createZStrokeList(),
        null);
    RefExpr expr = fac_.createRefExpr(stname, fac_.createZExprList(), false, false);

    InclDecl inclDecl = fac_.createInclDecl(expr);
    declList.add(inclDecl);

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
   * Assemble a Z paragraph (\Xi) according to inputs (with Input and output variables)
   * 
   * @param paraName - paragraph name
   * @param pred - predicate
   * @param llst - a list of local variables and their corresponding type
   * @return
   */
  public AxPara assembleZPara(String paraName, Pred pred, List<Pair<String, Term>> llst)
  {
    ZNameList fp = fac_.createZNameList();
    // ZName
    ZName paraname = fac_.createZName(paraName, fac_.createZStrokeList(), null);

    ZDeclList declList = fac_.createZDeclList();

    // State Paragraph Name and \Xi State Paragraph
    String stName = map_.getStatPara(proname_);
    ZName stname = fac_.createZName(new Character('\u039E') + stName, fac_.createZStrokeList(),
        null);
    RefExpr expr = fac_.createRefExpr(stname, fac_.createZExprList(), false, false);

    InclDecl inclDecl = fac_.createInclDecl(expr);
    declList.add(inclDecl);

    List<String> vlist = new ArrayList<String>();

    // VarDecl for each local variable
    for (Pair<String, Term> p : llst) {
      // create InStroke ?
      List<Stroke> ls = new ArrayList<Stroke>();
      Stroke st = fac_.createInStroke();
      ls.add(st);
      // create Name List with InStroke
      List<Name> ln = new ArrayList<Name>();
      Name name = fac_.createZName(p.getFirst(), fac_.createZStrokeList(ls), null);
      ln.add(name);

      // create Namelist
      NameList nl = fac_.createZNameList(ln);
      VarDecl vd = fac_.createVarDecl(nl, (Expr) (p.getSecond()));
      declList.add(vd);

      // need to replace the variable in pred with InStroke
      // For example, (x > 0) in pred should be (x? > 0)
      vlist.add(p.getFirst());
    }
    Pred pred2 = ZUtils.cloneTerm(pred);
    pred2.accept(new VariableRenamingSchemaVisitor (vlist, VariableRenameSchema.VRS_APPEND_INSTROKE));
    ZSchText schText = fac_.createZSchText(declList, pred2);
    SchExpr schExpr = fac_.createSchExpr(schText);

    ConstDecl cd = fac_.createConstDecl(paraname, schExpr);

    ZDeclList declList0 = fac_.createZDeclList();
    declList0.add(cd);
    SchText st = fac_.createZSchText(declList0, null);

    AxPara axpara = fac_.createAxPara(fp, st, Box.OmitBox);
    return axpara;
  }

  /**
   * Assemble a Z paragraph (\Delta) according to inputs (with Input and output variables)
   * 
   * @param paraName - paragraph name
   * @param pred - predicate
   * @param declList - ZDeclList (input and output Decl list)
   * @return
   */
  public AxPara assembleZPara(String paraName, Pred pred, ZDeclList declList)
  {
    ZNameList fp = fac_.createZNameList();
    // ZName
    ZName paraname = fac_.createZName(paraName, fac_.createZStrokeList(), null);

    // State Paragraph Name and \Delta State Paragraph
    String stName = map_.getStatPara(proname_);
    ZName stname = fac_.createZName(ZString.DELTA + stName, fac_.createZStrokeList(), null);
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
   * Operator or function application (ApprExpr or MemPred)
   * For example,
   * 
   * @param lexpr - left expression
   * @param rexpr - right expression
   * @return
   */
  public String visitOperOrFuncAppl(Expr lexpr, Expr rexpr)
  {
    String lstr = "" + visit(lexpr);
    String rstr = "" + visit(rexpr);
    /**
     * MemPred
     */
    if (ZUtils.isTupleExpr(lexpr)) {
      // if it's a number range application, for example " _ .. _ (0,59) to {0..59}"
      if (lstr.matches("\\(([-\\w]+), *([-\\w]+)\\)")) {
        String str = lstr.replaceAll("\\(([-\\w]+), *([-\\w]+)\\)", "$1,$2");
        String alstr[] = str.split(",");
        if (rstr.equals(" _ > _ ")) {
          /**
           * _ > _
           */
          str_ = str_.replace(lstr + rstr, alstr[0] + " > " + alstr[1]);
        }
        else if (rstr.equals(" _ < _ ")) {
          /**
           * _ < _ operator
           */
          str_ = str_.replace(lstr + rstr, alstr[0] + " < " + alstr[1]);
        }
      }
    }

    /**
     * ApprExpr
     */
    if (ZUtils.isTupleExpr(rexpr)) {
      // if it's a number range application, for example " _ .. _ (0,59) to {0..59}"
      if (rstr.matches("\\(([-\\w]+), *([-\\w]+)\\)")) {
        String str = rstr.replaceAll("\\(([-\\w]+), *([-\\w]+)\\)", "$1,$2");
        String arstr[] = str.split(",");
        if (lstr.equals(" _ .. _ ")) {
          /**
           * _ > _
           */
          str_ = str_.replace(lstr + rstr, "{" + arstr[0] + ".." + arstr[1] + "}");
        }
        else if (lstr.equals(" _ + _ ")) {
          /**
           * _ < _ operator
           */
          str_ = str_.replace(lstr + rstr, arstr[0] + " + " + arstr[1]);
        }
      }
    }

    if (lstr.equals("- _ ")) {
      str_ = str_.replaceAll(lstr + rstr, "-" + rstr);
    }
    return null;
  }

  void save_str()
  {
    str_tmp_stack_.push(str_);
  }

  void restore_str()
  {
    str_ = str_tmp_stack_.pop();
  }

  boolean split_tuple(String istr, List<String> lstr)
  {
    // tuples like "(state, #A)" or "(state, Set(x))"
    // "[\\w\\p{Punct}]+" matches word or punctuation
    // \w - A word character: [a-zA-Z_0-9]
    // \p{Punct} - Punctuation: One of !"#$%&'()*+,-./:;<=>?@[\]^_`{|}~
    if (istr.matches("\\(([\\w\\p{Punct}]+), *([\\w\\p{Punct}]+)\\)")) {
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

    return false;
  }

  /**
   * get the input and output variables from schema name like (op!ous?ins)
   * 
   * @param sch - schema name with input and output variable, such as op?x, op!x, op!x?y, op?x!y,
   *          op!x.y?u.v
   * @param inVars - input variabl name list
   * @param outVars - output variabl name list
   */
  private void getInOutVarFromSchemaName(String sch, List<String> inVars, List<String> outVars)
  {
    // sch = "op!r!o!p?u?v?w "; // -ok
    // sch = "op!r.o.p?u.v.w "; // -ok
    // . is the same as !, so we replace all . with ! first
    sch = sch.replaceAll("\\.", "!");
    if (!sch.contains("!") && !sch.contains("?")) {
      inVars.clear();
      outVars.clear();
    }
    // inouts
    else if (sch.contains("!") && sch.contains("?")) {
      String ins = sch.replaceAll("!.*?[?]", "?");
      ins = ins.replaceAll("!.*", "");

      // ins only
      String strs[] = ins.split("[?.]");
      // the first one is schema name itself, and skip it
      for (int i = 1; i < strs.length; i++) {
        inVars.add(strs[i]);
      }

      // outs only
      String outs = sch.replaceAll("[?].*?!", "!");
      outs = outs.replaceAll("[?].*", "");

      String strs1[] = outs.split("[!.]");
      // the first one is schema name itself, and skip it
      for (int i = 1; i < strs1.length; i++) {
        outVars.add(strs1[i]);
      }
    }
    else if (sch.contains("!")) {
      // outs only
      String strs[] = sch.split("[!.]");
      // the first one is schema name itself, and skip it
      for (int i = 1; i < strs.length; i++) {
        outVars.add(strs[i]);
      }
    }
    else if (sch.contains("?")) {
      // ins only
      String strs[] = sch.split("[?.]");
      // the first one is schema name itself, and skip it
      for (int i = 1; i < strs.length; i++) {
        inVars.add(strs[i]);
      }
    }
  }

  private String removeInOutVarFromSchemaName(String sch)
  {
    String str = sch;
    if (str.contains("!")) {
      String strs[] = sch.split("[!.]");
      str = strs[0];
    }

    if (str.contains("?")) {
      String strs[] = sch.split("[?.]");
      str = strs[0];
    }

    return str;
  }

  private String removeInVarFromSchemaName(String sch)
  {
    String str = sch;

    if (str.contains("?")) {
      String strs[] = sch.split("[?.]");
      str = strs[0];
    }

    return str;
  }

  private void addAdditionalVarProcess(String n, String varExpr)
  {
    /**
     * Var_0 = put0?x -> Var1_0(x)
     * Var1_0(x) =
     * get0!x -> Var1_0(x)
     * []
     * put0?y -> Var1_0(y)
     * Var_n = putn?x -> Var1_n(x)
     * Var1_n(x) =
     * getn!x -> Var1_n(x)
     * []
     * putn?y -> Var1_n(y)
     */
    String strVarProc = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_NAME), n);
    String strVar1Proc = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_NAME1), n);
    String strPutChn = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_PUT), n);
    String strGetChn = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_GET), n);
    cspspec_.addVarProcess(strVarProc + " = " + strPutChn + "?x -> " + strVar1Proc + "(x)");
    cspspec_.addVarProcess(strVar1Proc + "(x) = " + strPutChn + "?y -> " + strVar1Proc + "(y)"
        + " [] " + strGetChn + "!x -> " + strVar1Proc + "(x)" + " [] "
        + MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_END), n) + " -> SKIP");
    cspspec_.addChannel("channel " + strPutChn + ": " + varExpr);
    cspspec_.addChannel("channel " + strGetChn + ": " + varExpr);
    cspspec_.addChannel("channel " + MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_END), n));
  }

  /**
   * Get the global number for variable storage process
   * 
   * @return
   */
  String getandIncVarNum()
  {
    String n = map_.getVarNum();
    if (n != null) {
      map_.incVarNum();
    }
    else {
      Random randomGenerator = new Random();
      /** 100 to 200 for random use only */
      n = String.format("%d", randomGenerator.nextInt(100) + 100);
    }

    return n;
  }

  /**
   * Return formatted CSP structure to access state variables in input set
   * 
   * @param comm - original communication (c!st)
   * @param lvs - a set of state variables to be accessed
   * @return a string like (st?tsv__st - c!tsv__st)
   */
  String Faccess_stVar(String comm, Set<String> lvs)
  {
    String str = comm;

    for (String v : lvs) {
      // check if an out variable is a state variable or not
      // if it is, we can use the same name channel to get variable from Z
      // for example, c.sv => sv?v_sv -> c.v_sv
      /**
       * A list of variable name
       */
      List<String> slst = new ArrayList<String>();
      if (isState(v, slst)) {
        String strVar = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.TEMP_VAR_RENAMING_PATT), v);
        str = v + "?" + strVar + " -> " + str.replaceAll(v, strVar);
      }
    }

    return str;
  }

  /**
   * Return formatted CSP structure to access the local variables in input set
   * 
   * @param lvs - a set of local variables to be accessed
   * @return a string like get0?x -> get2?z ->
   */
  String Faccess_var(Set<String> lvs)
  {
    String str = "";

    for (String v : lvs) {
      if (varblock_var_.size() > 0) {
        for (int i = varblock_var_.size() - 1; i >= 0; i--) {
          for (Triple<String, Pair<String, Term>, String> p : varblock_var_.get(i)) {
            if (v.equals(p.getT1())) {
              // it is a variable within a variable block
              String strGetChn = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_GET), p.getT3());
              str += strGetChn + "?" + v + " -> ";
            }
          }
        }
      }
    }
    return str;
  }

  /**
   * Return formatted CSP structure to update the local variables in input set
   * 
   * @param lvs - a set of local variables to be updated
   * @return a string like "-> put0?x -> put2?z"
   */
  String Fupdate_var(Set<String> lvs)
  {
    String str = "";

    for (String v : lvs) {
      if (varblock_var_.size() > 0) {
        for (int i = varblock_var_.size() - 1; i >= 0; i--) {
          for (Triple<String, Pair<String, Term>, String> p : varblock_var_.get(i)) {
            if (v.equals(p.getT1())) {
              // it is a variable within a variable block
              String strPutChn = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_PUT), p.getT3());
              str += " -> " + strPutChn + "!" + v;
            }
          }
        }
      }
    }
    return str;
  }

  /**
   * Access to local variables by prefixing getn?lv
   * Update to local variables by suffixing putn?lv
   * 
   * @param term
   * @param ts
   * @return
   */
  boolean Fvar(Term term, Set<String> ts)
  {
    // 1. determine the access to local variables or update to local variables separately
    // from term
    String opname;
    // for input variables, such as op?x
    // we will have the process "op?x -> putx!x -> SKIP" to save x in the var_x process

    return true;
  }

  /**
   * @param comm - input communication: format like c?a!b
   * @return get1?b -> c?a!b -> put0!a
   */
  String Fvar(String comm)
  {
    String str = "";

    List<String> inVars = new ArrayList<String>();
    List<String> outVars = new ArrayList<String>();

    // get the in and out variables from the schema name
    getInOutVarFromSchemaName(comm, inVars, outVars);

    String pre = Faccess_var(new HashSet<String>(outVars));

    String post = Fupdate_var(new HashSet<String>(inVars));

    comm = Faccess_stVar(comm, new HashSet<String>(outVars));

    str = pre + comm + post;
    return str;
  }

  /**
   * Return the dashed local variables and their type from input String
   * 
   * @param st
   * @param llst
   * @return
   */
  public boolean isLocDashVar(String st, List<Pair<String, Term>> llst)
  {
    boolean ret = false;
    /*
     * an expression can be split into a list of variables or expression
     * as well according to punctuation
     * ^\w - except [a-zA-Z_0-9]
     */
    llst.clear();

    String[] strs = st.split("[^\\w^" + ZChar.PRIME + "]");
    List<String> lstDashVar = new ArrayList<String>();

    for (int i = 0; i < strs.length; i++) {
      String s = strs[i].trim();
      // Remove all not dashed variables
      if (s.endsWith("" + ZChar.PRIME) && !lstDashVar.contains(s)) {
        lstDashVar.add(s);
      }
    }

    for (String ds : lstDashVar) {
      // remove the last PRIME (')
      String uds = ds.substring(0, ds.length() - 1);
      /*
       * Check from loc_var_ first
       */
      for (Pair<String, Term> ve : loc_var_) {
        if (ve.getFirst().equals(uds)) {
          ret = true;
          llst.add(new Pair<String, Term>(ds, ve.getSecond()));
        }
      }

      /*
       * Check from varblock_var_
       */
      if (varblock_var_.size() > 0) {
        for (int j = varblock_var_.size() - 1; j >= 0; j--) {
          for (Triple<String, Pair<String, Term>, String> p : varblock_var_.get(j)) {
            if (uds.equals(p.getT1())) {
              ret = true;
              llst.add(new Pair<String, Term>(ds, p.getT2().getSecond()));
            }
          }
        }
      }
    }

    return ret;
  }

  /**
   * Return the undashed local variables and their type from input String
   * 
   * @param st
   * @param llst
   * @return
   */
  public boolean isLocUndashVar(String st, List<Pair<String, Term>> llst)
  {
    boolean ret = false;
    /*
     * an expression can be split into a list of variables or expression
     * as well according to punctuation
     * ^\w - except [a-zA-Z_0-9]
     */
    llst.clear();
    String[] strs = st.split("[^\\w^" + ZChar.PRIME + "]");
    List<String> lstDashVar = new ArrayList<String>();

    for (int i = 0; i < strs.length; i++) {
      String s = strs[i].trim();
      // Remove all not dashed variables
      if (!s.endsWith("" + ZChar.PRIME) && !s.equals("") && !lstDashVar.contains(s)) {
        lstDashVar.add(s);
      }
    }

    for (String ds : lstDashVar) {
      /*
       * Check from loc_var_ first
       */
      for (Pair<String, Term> ve : loc_var_) {
        if (ve.getFirst().equals(ds)) {
          ret = true;
          llst.add(new Pair<String, Term>(ds, ve.getSecond()));
        }
      }

      /*
       * Check from varblock_var_
       */
      if (varblock_var_.size() > 0) {
        for (int j = varblock_var_.size() - 1; j >= 0; j--) {
          for (Triple<String, Pair<String, Term>, String> p : varblock_var_.get(j)) {
            if (ds.equals(p.getT1())) {
              ret = true;
              llst.add(new Pair<String, Term>(ds, p.getT2().getSecond()));
            }
          }
        }
      }
    }

    return ret;
  }

  /**
   * Return all dashed variables and their type from input String
   * 
   * @param st
   * @param llst
   * @return
   */
  public void getDashVar(String st, List<String> llst)
  {
    /*
     * an expression can be split into a list of variables or expression
     * as well according to punctuation
     * ^\w - except [a-zA-Z_0-9]
     */
    llst.clear();
    String[] strs = st.split("[^\\w^" + ZChar.PRIME + "]");

    for (int i = 0; i < strs.length; i++) {
      String s = strs[i].trim();
      // Remove all not dashed variables
      if (s.endsWith("" + ZChar.PRIME) && !llst.contains(s)) {
        llst.add(s);
      }
    }
  }

  /**
   * Return a list of variables (state and local variables) from input String
   * 
   * @param st
   * @param llst
   * @return
   */
  public void getAllVars(String st, List<String> llst)
  {
    llst.clear();

    // Local variables in scope
    List<Pair<String, Term>> lLocNameSet = new ArrayList<Pair<String, Term>>();

    isState(st, llst);

    isLocVar(st, lLocNameSet);

    for (Pair<String, Term> p : lLocNameSet) {
      llst.add(p.getFirst());
    }
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
    // safe_visit mode
//    safe_visit_.push(true);
    // save cspspec_
//    safe_visit_cspspec_.push(cspspec_);
    
    str = "" + visit(term);
    
    // restore cspspec_
//    cspspec_ = safe_visit_cspspec_.pop();
    // exit safe_visit mode
//    safe_visit_.pop();
    // restore str_
    restore_str();

    return str;
  }
  
  public Boolean AddPara(Para para) 
  {
    assert(para instanceof AxPara);
    
    /** 
     * If it is not safe visit, the para can be added
     * otherwise, nothing changed
     */
//    if (safe_visit_.size() == 0) {
      paralist_.add(para);
//    }
    return true;
  }
  
  /** FvarPre function to extract prefixing from action A
   * For example, Fvar_pre ("(get0?x -> get1?y -> (A))") => return "get0?x -> get1?y ->", and evts={"get0?x","get1?y"}
   * @param a - translated action
   * @param evts - gets event array
   * @return
   */
  public String Fvar_pre (String strA, List<String> evts)
  {
    String ret = "";
    // it may have multiple ( in the beginning, we need to remove the same number of ) from the end
    // Reluctant quantifiers (.*?) starting from empty
    Pattern pattern = Pattern.compile("^\\(*(.*?get.*?)-> *([a-fh-zA-Z\\(].*)");
    Matcher matcher = pattern.matcher(strA);
    if (matcher.find())
    {
      Debug.debug_print(matcher.group(0));
      Debug.debug_print(matcher.group(1));
      Debug.debug_print(matcher.group(2));
    }
    return ret;
  }
}

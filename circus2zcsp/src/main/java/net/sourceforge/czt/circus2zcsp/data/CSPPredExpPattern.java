package net.sourceforge.czt.circus2zcsp.data;

import java.util.HashMap;
import java.util.Map;

import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.z.util.ZChar;
import net.sourceforge.czt.z.util.ZString;

/**
 * Predicate and Expression Pattern in CSP
 * @author rye
 *
 */
public class CSPPredExpPattern
{
  private static final Map<PredExpPattern, String> pattmap_ = new HashMap<PredExpPattern, String>()
  {
    /**
     * 
     */
    private static final long serialVersionUID = 1L;

    {
      /**
       * {0} expression   => left expression;
       * {1} rel          => operator;
       * {2} expression   => right expression;
       *
       * Note: getRel implements the MemPred cases in the order they appear in Z.xsd
       */
      put(PredExpPattern.INFIX_PATTERN, "({0} {1} {2})");
      
      /**
       * {0} expression   => left expression;
       * {1} rel          => operator;
       * {2} expression   => right expression;
       *
       * Note: getRel implements the MemPred cases in the order they appear in Z.xsd
       */
      put(PredExpPattern.INFIX_PATTERN_WITH_BRACES, "'{'{0} {1} {2}'}'");
      
      /**
       * {0} rel                 => op;
       * {1} expression          => rhs;
       *
       * Note: getRel implements the MemPred cases in the order they appear in Z.xsd
       */
      put(PredExpPattern.PREFIX_PATTERN, "({0}{1})");
      
      /**
       * Prefixed operator, operator rhs without parentheses and with a blank
       * {0} rel                 => op;
       * {1} expression          => rhs;
       * such as, not a
       */
      put(PredExpPattern.PREFIX2_PATTERN, "({0} {1})");
      
      /**
       * Prefixed operator, operator rhs without parentheses and with a blank
       * {0} expression           => lhs;
       * {1} rel                  => op;
       * such as, a'
       */
      put(PredExpPattern.POSTFIX_PATTERN, "({0}{1})");
      
      /**
       * Set pattern with prefixed operator, operator(lhs, rhs)
       * 
       * {0} rel                 => operator;
       * {1} expression          => lhs;
       * {2} expression          => rhs;
       * such as, member(x, a), not member(x, a), union(a1, a2)
       */
      put(PredExpPattern.PRESET3_PATTERN, "{0}({1}, {2})");
      
      /**
       * Set pattern with prefixed operator just with rhs and lhs swapped, operator(rhs, lhs)
       * 
       * {0} rel                 => operator;
       * {1} expression          => rhs;
       * {2} expression          => lhs;
       * such as, iter(s, n)
       */
      put(PredExpPattern.PRESET3_PATTERN_RHS_LHS, "{0}({1}, {2})");
      
      /**
       * Set pattern with prefixed operator, operator(rhs)
       * 
       * {0} rel                 => operator;
       * {1} expression          => rhs;
       * such as, card(a)
       */
      put(PredExpPattern.PRESET2_PATTERN, "{0}({1})");
      
      /**
       * Set pattern with prefixed operator, operator rhs
       * 
       * {0} rel                 => operator;
       * {1} expression          => rhs;
       * such as, not p
       */
      put(PredExpPattern.PRESET2_PATTERN_1, "({0} ({1}))");
      
      /**
       * Set pattern with prefixed operator, operator(lhs)
       * 
       * {0} rel                 => operator;
       * {1} expression          => lhs;
       * relation inversion, r~
       */
      put(PredExpPattern.PRESET2_LHS_PATTERN, "({0}({1}))");
      
      /**
       * tuple, (lhs, rhs)
       * 
       * such as, (a, b), ({1,2}, {0,2})
       */
      put(PredExpPattern.TUPLE_PATTERN, "({0}, {1})");
      
      /**
       * Sequence brackets ⟨, ,⟩
       * rel - ⟨,,⟩
       * lhs - ""
       * rhs - {(1,2),(2,7),(3,10)}
       * 
       * to <2,7,10>
       */
      put(PredExpPattern.SEQ_BRACKETS_PATTERN, "<{0}>");
      
      /**
       * Var Process Name (proname + _Var_ + varname)
       *    such as Register_Var_x
       */
    //  put(PredExpPattern.VAR_PROCESS_NAME, "{0}_Var_{1}");
      
      /**
       * Var Process Name (proname + _Var_ + varname1)
       *    such as Register_Var_x1
       */
    //  put(PredExpPattern.VAR_PROCESS_NAME1, "{0}_Var_{1}1");
      
      /**
       * Var Process: channel put name
       *    such as Register_putx
       */
    //  put(PredExpPattern.VAR_PROCESS_PUT, "{0}_put{1}");
      
      /**
       * Var Process: channel get name
       *    such as Register_getx
       */
    //  put(PredExpPattern.VAR_PROCESS_GET, "{0}_get{1}");
      
      /**
       * Var Process Name (Var_ + numbering)
       *    such as Var_n
       */
      put(PredExpPattern.VAR_PROCESS_NAME, "MemCell_{0}");
      
      /**
       * Var Process Name (Var1_ + numbering)
       *    such as Var1_n
       */
      put(PredExpPattern.VAR_PROCESS_NAME1, "MCell_{0}");
      
      /**
       * Var Process: channel put (putn)
       *    such as putn
       */
      put(PredExpPattern.VAR_PROCESS_PUT, "set{0}");
      
      /**
       * Var Process: channel get (getn)
       *    such as getn
       */
      put(PredExpPattern.VAR_PROCESS_GET, "get{0}");
      
      put(PredExpPattern.VAR_PROCESS_END, "end");
      
      /**
       * The name of \exists_1 operator: Exists1
       */
      put(PredExpPattern.OP_NAME_EXISTS_1, "Exists1");
      
      /**
       * The name of \power_1 operator: \Power\1\
       */
      put(PredExpPattern.OP_NAME_POWER_1, ZString.POWER + ZString.SE + "1" + ZString.NW);
      
      /**
       * The name of \seq_1 operator: \seq\1\
       */
      put(PredExpPattern.OP_NAME_SEQ_1, "seq" + ZString.SE + "1" + ZString.NW);
      
      /**
       * The name of sequence bracket operator: \langle \listarg \rangle
       */
      put(PredExpPattern.OP_NAME_SEQ_BRACKET, ZString.LANGLE + ZString.LISTARG + ZString.RANGLE);
      
      /**
       * Distributed concatenation
       */
      put(PredExpPattern.OP_NAME_DIS_CONC, ZString.CAT + "/");
      
      /**
       * \boolean.
       */
    //  public static ZChar BOOLEAN, new ZChar(0x1D539);
      put(PredExpPattern.BOOLEAN, String.valueOf(new ZChar(0x1D539)));
      
      /**
       * The paragraph name pattern for guarded command
       * {0} - process name
       * {1} - unique number
       */
      put(PredExpPattern.GA_NAME_PATT, "{0}_GAOp{1}");
      
      /**
       * The paragraph name pattern for assignment
       * {0} - process name
       * {1} - unique number
       */
      put(PredExpPattern.ASSIGN_NAME_PATT, "{0}_AssgnOp{1}");
      
      /**
       * The paragraph name pattern for assignment
       * {0} - process name
       * {1} - unique number
       */
      put(PredExpPattern.PARA_ACTION_NAME_PATT, "{0}_ParaAction{1}");
      
      /**
       * The temporary state variable renaming pattern, used in state variable 
       * getting with var channel in CSP
       * for example, c.sv => sv?tsv__sv -> c.tsv__sv
       * {0} - original variable name
       */
      put(PredExpPattern.TEMP_VAR_RENAMING_PATT, "tsv__{0}");
      
      /**
       * The paragraph name pattern for specification
       * {0} - process name
       * {1} - unique number
       */
      put(PredExpPattern.SPEC_NAME_PATT, "{0}_SpecOp{1}");
      
      /**
       * The paragraph name pattern for assumption
       * {0} - process name
       * {1} - unique number
       */
      put(PredExpPattern.ASSUMP_NAME_PATT, "{0}_Assmp{1}");
      
      /**
       * The paragraph name pattern for coercion
       * {0} - process name
       * {1} - unique number
       */
      put(PredExpPattern.COERC_NAME_PATT, "{0}_Coer{1}");
      
      /**
       * The paragraph name pattern for alternation
       * {0} - process name
       * {1} - unique number
       */
      put(PredExpPattern.ALT_NAME_PATT, "{0}_AltOp{1}");
      
      /**
       * The datatype pattern for schema type
       * {0}_rec_field
       * {0} - schema name
       */
      put(PredExpPattern.SCHEMA_TO_DATATYPE_PATT, "{0}_rec_field");
      
      /**
       * The datatype pattern for schema type
       * {0}_rec_{1}
       * {0} - schema name
       * {1} - field name
       */
      put(PredExpPattern.SCHEMA_TO_DATATYPE_FIELD_PATT, "{0}_rec_{1}");
      
      /**
       * The select function for schema's field
       * select_field_{0}
       * {0} - schema name
       */
      put(PredExpPattern.SCHEMA_TO_DATATYPE_SELECT_FIELD_PATT, "select_field_{0}");
      
      /** temporary variable name pattern
       * {0}_var_t
       */
      put(PredExpPattern.SCHEMA_COMP_INTERMEDIATE_VAR_PATT, "{0}_var_t");
    }
  };
  
  public static String getPattern(PredExpPattern p)
  {
    String ret = pattmap_.get(p);
    return ret;    
  }
}

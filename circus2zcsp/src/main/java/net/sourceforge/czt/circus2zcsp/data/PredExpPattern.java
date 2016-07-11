package net.sourceforge.czt.circus2zcsp.data;

public enum PredExpPattern {
  /**
   * {0} expression   => left expression;
   * {1} rel          => operator;
   * {2} expression   => right expression;
   *
   * Note: getRel implements the MemPred cases in the order they appear in Z.xsd
   */
  INFIX_PATTERN,
  
  /**
   * {0} expression   => left expression;
   * {1} rel          => operator;
   * {2} expression   => right expression;
   *
   * Note: getRel implements the MemPred cases in the order they appear in Z.xsd
   */
  INFIX_PATTERN_WITH_BRACES,
  
  /**
   * {0} rel                 => op;
   * {1} expression          => rhs;
   *
   * Note: getRel implements the MemPred cases in the order they appear in Z.xsd
   */
  PREFIX_PATTERN,
  
  /**
   * Prefixed operator, operator rhs without parentheses and with a blank
   * {0} rel                 => op;
   * {1} expression          => rhs;
   * such as, not a
   */
    PREFIX2_PATTERN,
  
  /**
   * Prefixed operator, operator rhs without parentheses and with a blank
   * {0} expression           => lhs;
   * {1} rel                  => op;
   * such as, a'
   */
    POSTFIX_PATTERN,
  
  /**
   * Set pattern with prefixed operator, operator(lhs, rhs)
   * 
   * {0} rel                 => operator;
   * {1} expression          => lhs;
   * {2} expression          => rhs;
   * such as, member(x, a), not member(x, a), union(a1, a2)
   */
    PRESET3_PATTERN,
  
  /**
   * Set pattern with prefixed operator just with rhs and lhs swapped, operator(rhs, lhs)
   * 
   * {0} rel                 => operator;
   * {1} expression          => rhs;
   * {2} expression          => lhs;
   * such as, iter(s, n)
   */
    PRESET3_PATTERN_RHS_LHS,
  
  /**
   * Set pattern with prefixed operator, operator(rhs)
   * 
   * {0} rel                 => operator;
   * {1} expression          => rhs;
   * such as, card(a)
   */
    PRESET2_PATTERN ,
  
  /**
   * Set pattern with prefixed operator, operator rhs
   * 
   * {0} rel                 => operator;
   * {1} expression          => rhs;
   * such as, not p
   */
    PRESET2_PATTERN_1,
  
  /**
   * Set pattern with prefixed operator, operator(lhs)
   * 
   * {0} rel                 => operator;
   * {1} expression          => lhs;
   * relation inversion, r~
   */
    PRESET2_LHS_PATTERN,
  
  /**
   * tuple, (lhs, rhs)
   * 
   * such as, (a, b), ({1,2}, {0,2})
   */
    TUPLE_PATTERN,
  
  /**
   * Sequence brackets ⟨, ,⟩
   * rel - ⟨,,⟩
   * lhs - ""
   * rhs - {(1,2),(2,7),(3,10)}
   * 
   * to <2,7,10>
   */
    SEQ_BRACKETS_PATTERN,
  
  /**
   * Var Process Name (proname + _Var_ + varname)
   *    such as Register_Var_x
   */
//    VAR_PROCESS_NAME,
  
  /**
   * Var Process Name (proname + _Var_ + varname1)
   *    such as Register_Var_x1
   */
//    VAR_PROCESS_NAME1,
  
  /**
   * Var Process: channel put name
   *    such as Register_putx
   */
//    VAR_PROCESS_PUT,
  
  /**
   * Var Process: channel get name
   *    such as Register_getx
   */
//    VAR_PROCESS_GET,
  
  /**
   * Var Process Name (Var_ + numbering)
   *    such as Var_n
   */
    VAR_PROCESS_NAME,
  
  /**
   * Var Process Name (Var1_ + numbering)
   *    such as Var1_n
   */
    VAR_PROCESS_NAME1,
  
  /**
   * Var Process: channel put (putn)
   *    such as putn
   */
    VAR_PROCESS_PUT,
  
  /**
   * Var Process: channel get (getn)
   *    such as getn
   */
    VAR_PROCESS_GET,
  
    VAR_PROCESS_END,
  
  /**
   * The name of \exists_1 operator: Exists1
   */
    OP_NAME_EXISTS_1,
  
  /**
   * The name of \power_1 operator: \Power\1\
   */
    OP_NAME_POWER_1,
  
  /**
   * The name of \seq_1 operator: \seq\1\
   */
    OP_NAME_SEQ_1,
  
  /**
   * The name of sequence bracket operator: \langle \listarg \rangle
   */
    OP_NAME_SEQ_BRACKET,
  
  /**
   * Distributed concatenation
   */
    OP_NAME_DIS_CONC,
  
  /**
   * \boolean.
   */
//  public static ZChar BOOLEAN,
    BOOLEAN,
  
  /**
   * The paragraph name pattern for guarded command
   * {0} - process name
   * {1} - unique number
   */
    GA_NAME_PATT,
  
  /**
   * The paragraph name pattern for assignment
   * {0} - process name
   * {1} - unique number
   */
    ASSIGN_NAME_PATT,
  
  /**
   * The paragraph name pattern for assignment
   * {0} - process name
   * {1} - unique number
   */
    PARA_ACTION_NAME_PATT,
  
  /**
   * The temporary state variable renaming pattern, used in state variable 
   * getting with var channel in CSP
   * for example, c.sv => sv?tsv__sv -> c.tsv__sv
   * {0} - original variable name
   */
    TEMP_VAR_RENAMING_PATT,
  
  /**
   * The paragraph name pattern for specification
   * {0} - process name
   * {1} - unique number
   */
    SPEC_NAME_PATT,
    
  /**
   * The paragraph name pattern for specification
   * {0} - process name
   * {1} - unique number
   */
    ASSUMP_NAME_PATT,
      
  /**
   * The paragraph name pattern for specification
   * {0} - process name
   * {1} - unique number
   */
    COERC_NAME_PATT,
  
  /**
   * The paragraph name pattern for alternation
   * {0} - process name
   * {1} - unique number
   */
    ALT_NAME_PATT,

    /**
     * The datatype pattern for schema type
     * {0}_rec_field
     * {0} - schema name
     */
    SCHEMA_TO_DATATYPE_PATT,
    
    /**
     * The datatype pattern for schema type
     * {0}_rec_{1}
     * {0} - schema name
     * {1} - field name
     */
    SCHEMA_TO_DATATYPE_FIELD_PATT,

    /**
     * The select function for schema's field
     * select_field_{0}
     * {0} - schema name
     */
    SCHEMA_TO_DATATYPE_SELECT_FIELD_PATT,
    
    /** temporary variable name pattern
     * {0}_var_t
     */
    SCHEMA_COMP_INTERMEDIATE_VAR_PATT,
    
    /**
     * special unknown
     */
    UNKNOWN,
}

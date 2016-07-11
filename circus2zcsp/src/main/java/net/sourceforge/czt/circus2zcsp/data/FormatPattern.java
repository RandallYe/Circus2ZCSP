package net.sourceforge.czt.circus2zcsp.data;

/**
 * Format pattern for this project
 * 
 * @author rye
 *
 */
public class FormatPattern
{
  /**
   * schema name for negation of precondition
   *    Read => fRead
   */
  public static final String NEG_PRECONDITION_SCHEMA = "{0}_fOp";
  
  /**
   * Init schema name
   */
  public static final String INIT_SCHEMA_NAME = "Init"; 
  
  /**
   * Variable, schema and action name renaming
   *    {0} - process name
   *    {1} - schema, var or action name
   * For example,
   *    Register + Read => Register_Read
   */
  public static final String RENAMING_IN_PROC = "{0}_{1}";
  
  /**
   * Action name renaming
   *    {0} - process name
   *    {1} - action name
   * For example,
   *    Register + Run => Register_Action_Run
   */
  public static final String ACT_RENAMING_IN_PROC = "{0}_Action_{1}";
  
  /**
   * Main action name renaming
   *    {0} - process name
   * For example,
   *    Register => Register_Main
   */
  public static final String MACT_RENAMING_IN_PROC = "{0}_Main";
  
  /**
   * Temporary variable naming pattern
   *    {0} - var name
   * For example,
   *    x => x_t
   */
  public static final String TEMP_VAR_PATT = "{0}_t";
  
  /**
   * parametrised process rewritten to a set of basic process
   *    {0} - parametrised process name
   *    {1} - the element of variable v
   * For example,
   *    pp => pp_1 where 1 is the possible value of x that is the parameter
   */
  public static final String PARAM_PROCESS_RENAMING_PATT = "{0}_{1}";
  
  /**
   * the channel in an indexed process rewritten to chn_i.i
   *    {0} - channel_name
   *    {1} - the name of index
   *    {2} - the element of index
   * For example,
   *    c => c_i.1 where 1 is the possible value of index i that is the parameter
   */
  public static final String INDEXED_PROCESS_CHN_RENAMING_PATT = "{0}_{1}.{2}";
  
  /**
   * state retrieve paragraph name pattern OP\_s
   *    {1} - state variable name
   */
  public static final String STATE_RETR_PARA_NAME_PATT = "OP_{0}";
  
  /**
   * final state paragraph name
   *    
   */
  public static final String STATE_PARA_NAME_PATT = "State";
  
  /**
   * final init paragraph name
   *    
   */
  public static final String Init_PARA_NAME_PATT = "Init";
  
  /**
   * empty state paragraph name in a process
   *    
   */
  public static final String DUMMY_STATE_PARA_NAME_PATT = "DummyState";
  
  /**
   * empty state paragraph name in a process
   *    
   */
  public static final String DUMMY_STATE_COMP_PATT = "dv";
  
  /**
   * given set name
   * {0} - given set name
   * {1} - numbering from 1
   *    
   */
  public static final String GIVEN_SET_NAME_PATT = "{0}_GS_{1}";
  
  /**
   * generic channel declaration
   *    
   */
  public static final String GENERIC_CHANNEL_PATT = "{0}_gen_{1}";
  
  /**
   * generic process
   *    
   */
  public static final String GENERIC_PROCESS_PATT = "{0}_gen_{1}";
  
  /**
   * Temporary schema name for generic instantiation
   *    
   */
  public static final String TEMP_SCHEMA_NAMING_GENERIC_INST = "SchInstRef_{0}";
  
  /**
   * Temporary schema name for schema expression action
   *    
   */
  public static final String TEMP_SCHEMA_NAMING_SCHEXPR = "SchExpr_{0}";
}


package net.sourceforge.czt.circus2zcsp.ast;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import net.sourceforge.czt.circus2zcsp.Debug;
import net.sourceforge.czt.circus2zcsp.data.CSPPredExpPattern;
import net.sourceforge.czt.circus2zcsp.data.PredExpPattern;

public class CSPSpec
{
  private final List<String> header_;
  
  /**
   * Axiomatic definition
   */
  private final List<String> axiomdef_;
  
  private final List<String> datatype_;
  
  private final List<String> nametype_;

  private final List<String> channels_;
  
  private final List<String> channelsets_;

  private final List<String> processes_;
  
  private final List<String> var_processes_;
  
  private final List<String> assert_;
  
  private final List<String> functions_;
  
  /**
   * HIDE_CSPB
   */
  private final List<String> HIDE_CSPB_;

  public CSPSpec()
  {
    header_ = new ArrayList<String>();
    this.axiomdef_ = new ArrayList<String>();
    this.datatype_ = new ArrayList<String>();
    this.nametype_ = new ArrayList<String>();
    this.channels_ = new ArrayList<String>();
    this.channelsets_ = new ArrayList<String>();
    this.processes_ = new ArrayList<String>();
    this.var_processes_ = new ArrayList<String>();
    this.HIDE_CSPB_ = new ArrayList<String>();
    this.assert_ = new ArrayList<String>();
    this.functions_ = new ArrayList<String>();
  }
  
  public void addHeader(String libpath, String minInt, String maxInt, String maxIns)
  {
    if (libpath == null) {
      libpath = "";
    }
    
    if (minInt == null) {
      minInt = "0";
    }
    
    if (maxInt == null) {
      maxInt = "3";
    }

    if (maxIns == null) {
      maxIns = "3";
    }

    /*
     * Add header of CSP Program
     */
//    header_.add("-- This CSP specification is translated from a Circus program by Circus2ZCSP translator.");
//    header_.add("");
    header_.add("-- Minimum and maximum integers for model checking. Make sure they are set in advance.");
    header_.add("MININT = " + minInt);
    header_.add("MAXINT = " + maxInt);
    header_.add("");
    header_.add("-- Maximum instances generated for iseq.  Make sure it is set in advance.");
    header_.add("MAXINS = " + maxIns);
    header_.add("");
    
    header_.add("-- include a set of libraries");
    header_.add("include \"" + libpath + "lib_basic.csp\"");
    header_.add("include \"" + libpath + "lib_num.csp\"");
    header_.add("include \"" + libpath + "lib_card.csp\"");
    header_.add("include \"" + libpath + "lib_log.csp\"");
    header_.add("include \"" + libpath + "lib_set.csp\"");
    header_.add("include \"" + libpath + "lib_rel.csp\"");
    header_.add("include \"" + libpath + "lib_fun.csp\"");
    header_.add("include \"" + libpath + "lib_seq.csp\"");
    header_.add("");
    
//    /** definition of natural number in csp */
//    addNametype("nametype Nat = {0..}");
//    addProcess("-- Divergent Process \nDIV = DIV\n");
    addChannel("channel div");
    addProcess("-- Divergent Process \nDIV = div -> STOP\n");
  }

  public void addAxiomaticDef(String axdef)
  {
    axdef = typeReplacement(axdef);
    if(!axiomdef_.contains(axdef)) {
      axiomdef_.add(axdef);
    }
  }
  
  public void addDatatype(String datatype)
  {
    datatype = typeReplacement(datatype);
    if(!datatype_.contains(datatype)) {
      datatype_.add(datatype);
    }
  }
  
  public void addNametype(String nametype)
  {
    nametype = typeReplacement(nametype);
    if(!nametype_.contains(nametype)) {
      nametype_.add(nametype);
    }
  }

  /**
   * Add a channel declaration to CSP spec
   * @param channel
   */
  public void addChannel(String channel)
  {
    channel = typeReplacement(channel);
    if(!channels_.contains(channel))
    {
      channels_.add(channel);
    }
  }
  
  public void addChannelSet(String channelset)
  {
    channelset = typeReplacement(channelset);
    if(!channelsets_.contains(channelset))
    {
      channelsets_.add(channelset);
    }
  }

  public void addChannel(List<String> channels)
  {
    for (String str : channels) {
//      Debug.debug_print("Add Channel: " + str);
      addChannel(str);
    }
  }

  public void addProcess(String process)
  {
    process = typeReplacement(process);
    if(!processes_.contains(process)) {
      processes_.add(process);
    }
  }

  public void addProcess(List<String> processes)
  {
    for (String str : processes) {
      addProcess(str);
    }
  }
  
  public void addVarProcess(String process)
  {
    process = typeReplacement(process);
    if(!var_processes_.contains(process)) {
      var_processes_.add(process);
    }
  }
  
  /**
   * Add schema event to be hidden from communication
   * @param sch
   */
  public void addHideCSPB(String sch)
  {
    if(!HIDE_CSPB_.contains(sch)) {
      HIDE_CSPB_.add(sch);
    }
  }
  
  public void addAssertion(String assertion)
  {
    assertion = typeReplacement(assertion);
    if(!assert_.contains(assertion)) {
      assert_.add(assertion);
    }
  }

  public void addFunctions(String function)
  {
    function = typeReplacement(function);
    if(!functions_.contains(function)) {
      functions_.add(function);
    }
  }

  public String typeReplacement(String input)
  {
    String output;
    /** \nat */
    char cnat = new Character('\u2115');
    /** \num */
    char cnum = new Character('\u2124');
    /** \power */
    char cpower = new Character('\u2119');
    String nat = "" + cnat;
    String num = "" + cnum;
    String power = "" + cpower;
    output = input.replaceAll(nat, "Nat");
    output = output.replaceAll(num, "Int");
    return output;
 }
  
  public void updateProMainAction(String proname)
  {
    // find main action of the process
    for(String proc: processes_)
    {
      String newProc = proc;
      if(proc.indexOf(proname + "_Main = ") == 0)
      {
        // find the variable process
        for(String varProc: var_processes_)
        {
          if(varProc.startsWith(proname + "_Var_", 0) && !varProc.contains(") = "))
          {
            int idxEq = varProc.indexOf(" = ");
            String prefix = proname + "_Var_";
            String varName = varProc.substring(prefix.length(), idxEq);
            
            prefix = proname + "_Main = ";
            idxEq = prefix.length();
            
            String strProc = newProc.substring(idxEq);
            
            String strVarProc = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_NAME), proname, varName);
            String strPutChn = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_PUT), proname, varName);
            String strGetChn = MessageFormat.format(CSPPredExpPattern.getPattern(PredExpPattern.VAR_PROCESS_GET), proname, varName);
            String strChanset = "{| " + strPutChn + ", " + strGetChn + "|}";
            newProc = prefix + "((" + strProc + ")" + 
                " [|" + strChanset + "|] " + strVarProc + // parallel
                ") \\" + strChanset; // hide
            Debug.debug_print(varProc + ": " + varName + "\n");
            Debug.debug_print(newProc + "\n");
          }
        }
        processes_.remove(proc);
        processes_.add(newProc);
        return;
      }
    }
  }

  public String toString()
  {
    String ret = "";

    if(header_.isEmpty()) {
      addHeader("", null, null, null);
    }
    
    // header
    for (String nt : header_) {
      ret += nt + "\n";
    }
    
    ret += "\n";
    // axiomatic definition
    ret += "-- Axiomatic definition (Constant)\n";
    ret += "-- They should be assigned manually to meet its type and predicate restriction\n";
    ret += "-- and match the values assigned in Z as well\n";
    for (String nt : axiomdef_) {
      ret += nt + "\n";
    }
    
    ret += "\n";
    ret += "-- type\n";
    // declaration
    for (String nt : nametype_) {
      ret += nt + "\n";
    }
    ret += "\n";
    
    for (String dt : datatype_) {
      ret += dt + "\n";
    }
    ret += "\n";

    for (String dt : functions_) {
      ret += dt + "\n";
    }
    ret += "\n";
    
    ret += "-- channel declarations\n";
    for (String cl : channels_) {
      ret += cl + "\n";
    }
    ret += "\n";
    
    if(channelsets_.size() > 0)
    {
      ret += "-- channel set declarations\n";
    }
    
    for (String cl : channelsets_) {
      ret += cl + "\n";
    }
    ret += "\n";
    
    ret += "-- hidden event\n";
    String hide = "HIDE_CSPB = {|";
    for (String cl : HIDE_CSPB_) {
      if(hide.equals("HIDE_CSPB = {|"))
      {
        hide += cl;
      }
      else
      {
        hide += ", " + cl;
      }
    }
    if(!hide.equals("HIDE_CSPB = {|"))
    {
      ret += hide + "|}\n";
    }
    ret += "\n";

    ret += "-- processes for variable storing and retrieving \n";
    for (String pr : var_processes_) {
      ret += pr + "\n";
    }
    ret += "\n";
    
    ret += "-- processes \n";
    for (String pr : processes_) {
      ret += pr + "\n\n";
    }
    ret += "\n";
    
    ret += "-- assertions \n";
    for (String pr : assert_) {
      ret += pr + "\n";
    }
    ret += "\n";
    return ret;
  }
}

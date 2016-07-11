/*
 * Conversion from ISO Z to ZRM
 *      Both input and output are String type   
 */
package net.sourceforge.czt.circus2zcsp;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NegExpr;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.PreExpr;
import net.sourceforge.czt.z.ast.Qnt1Expr;
import net.sourceforge.czt.z.ast.RenameExpr;
import net.sourceforge.czt.z.ast.SchExpr2;
import net.sourceforge.czt.z.ast.ThetaExpr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZUtils;

public class ISOZ2ZRM
{
  public ISOZ2ZRM()
  {
  }
  
  public static String convert(ZSect circusSect, ZSect zs, String isoz)
  {
    String zrm;
    /**
     * before convert, we need to identify some specific constructs in ISO Z
     */
    for(Para para: circusSect.getZParaList()) {
      AxPara axpara = null;
      if(para instanceof AxPara) {
        // only treat global abbreviation specially
        if(ZUtils.isAbbreviation(para)) {
          axpara = (AxPara) para;
//          Name zn = ZUtils.getAbbreviationName(para);
//          String strAbbrName = Circus2ZCSPUtils.termToString(zn);
//          Pattern regex = Pattern.compile("}" + strAbbrName + " == ", Pattern.DOTALL | Pattern.MULTILINE);
//          Matcher matcher = regex.matcher(isoz);
//          isoz = matcher.replaceAll("}" + strAbbrName + " =Abbr= ");
        }
      }
      else if(para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          if(ZUtils.isAbbreviation(para)) {
            axpara = (AxPara) para;
          }
        }
      }
      else {
        
      }
      
      if(axpara != null) {
        ZName zn = (ZName) ZUtils.getAbbreviationName(axpara);
        Expr expr = ZUtils.getAbbreviationExpr(axpara);
        
//        if(expr instanceof SchExpr2 || 
//            expr instanceof NegExpr || 
//            expr instanceof ThetaExpr || 
//            expr instanceof RenameExpr ||
//            expr instanceof PreExpr) {
//          // If abbreviation has schema expression, just regard it as not an abbreviation
//          String strAbbrName = Circus2ZCSPUtils.termToString(zn);
//          strAbbrName = strAbbrName.replaceAll("_", "\\\\\\\\_ ");
//          Pattern regex = Pattern.compile("}" + strAbbrName + " ==", 
//              Pattern.DOTALL | Pattern.MULTILINE);
//          Matcher matcher = regex.matcher(isoz);
//          isoz = matcher.replaceAll("}" + strAbbrName + " =Sch=");          
//        }
//        else if(expr instanceof Qnt1Expr) {
        boolean isSchExpr = false;
        if(para instanceof ProcessPara) {
          isSchExpr = Circus2ZCSPUtils.isSchemaExpr(expr, circusSect, (ProcessPara)para);
        }
        else {
          isSchExpr = Circus2ZCSPUtils.isSchemaExpr(expr);
        }
        
        if(isSchExpr) {
       // If abbreviation has schema expression, just regard it as not an abbreviation
          String strAbbrName = Circus2ZCSPUtils.termToString(zn);
          strAbbrName = strAbbrName.replaceAll("_", "\\\\\\\\_ ");
          Pattern regex = Pattern.compile("}" + strAbbrName + " ==", 
              Pattern.DOTALL | Pattern.MULTILINE);
          Matcher matcher = regex.matcher(isoz);
          isoz = matcher.replaceAll("}" + strAbbrName + " =Sch=");
        }
        else {
          String strAbbrName = Circus2ZCSPUtils.termToString(zn);
          strAbbrName = strAbbrName.replaceAll("_", "\\\\\\\\_ ");
          Pattern regex = Pattern.compile("}" + strAbbrName + " == ", 
              Pattern.DOTALL | Pattern.MULTILINE);
          Matcher matcher = regex.matcher(isoz);
          isoz = matcher.replaceAll("}" + strAbbrName + " =Abbr= ");          
        }
      }
    }
    
    for(Para para: zs.getZParaList()) {
      AxPara axpara = null;
      if(para instanceof AxPara) {
        // only treat global abbreviation specially
        if(ZUtils.isAbbreviation(para)) {
          axpara = (AxPara) para;
//          Name zn = ZUtils.getAbbreviationName(para);
//          String strAbbrName = Circus2ZCSPUtils.termToString(zn);
//          Pattern regex = Pattern.compile("}" + strAbbrName + " == ", Pattern.DOTALL | Pattern.MULTILINE);
//          Matcher matcher = regex.matcher(isoz);
//          isoz = matcher.replaceAll("}" + strAbbrName + " =Abbr= ");
        }
      }
      else if(para instanceof ProcessPara) {
        if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
          if(ZUtils.isAbbreviation(para)) {
            axpara = (AxPara) para;
          }
        }
      }
      else {
        
      }
      
      if(axpara != null) {
        ZName zn = (ZName) ZUtils.getAbbreviationName(axpara);
        Expr expr = ZUtils.getAbbreviationExpr(axpara);
        
//        if(expr instanceof SchExpr2 || 
//            expr instanceof NegExpr || 
//            expr instanceof ThetaExpr || 
//            expr instanceof RenameExpr ||
//            expr instanceof PreExpr) {
//          // If abbreviation has schema expression, just regard it as not an abbreviation
//          String strAbbrName = Circus2ZCSPUtils.termToString(zn);
//          // strAbbrName has '_' for '_', but in isoz, it's "\_ ". 
//          strAbbrName = strAbbrName.replaceAll("_", "\\\\\\\\_ ");
//          Pattern regex = Pattern.compile("}" + strAbbrName + " ==", 
//              Pattern.DOTALL | Pattern.MULTILINE);
//          Matcher matcher = regex.matcher(isoz);
//          isoz = matcher.replaceAll("}" + strAbbrName + " =Sch=");
//        }
//        else if(expr instanceof Qnt1Expr) {
        boolean isSchExpr = false;
        if(para instanceof ProcessPara) {
          isSchExpr = Circus2ZCSPUtils.isSchemaExpr(expr, zs, (ProcessPara)para);
        }
        else {
          isSchExpr = Circus2ZCSPUtils.isSchemaExpr(expr, zs, null);
        }
        
        if(isSchExpr) {
       // If abbreviation has schema expression, just regard it as not an abbreviation
          String strAbbrName = Circus2ZCSPUtils.termToString(zn);
          strAbbrName = strAbbrName.replaceAll("_", "\\\\\\\\_ ");
          Pattern regex = Pattern.compile("}" + strAbbrName + " ==", 
              Pattern.DOTALL | Pattern.MULTILINE);
          Matcher matcher = regex.matcher(isoz);
          isoz = matcher.replaceAll("}" + strAbbrName + " =Sch=");
        }
        else {
          String strAbbrName = Circus2ZCSPUtils.termToString(zn);
          strAbbrName = strAbbrName.replaceAll("_", "\\\\\\\\_ ");
          Pattern regex = Pattern.compile("}" + strAbbrName + " == ", 
              Pattern.DOTALL | Pattern.MULTILINE);
          Matcher matcher = regex.matcher(isoz);
          isoz = matcher.replaceAll("}" + strAbbrName + " =Abbr= ");          
        }
      }
    }

    zrm = convert(isoz);
    return zrm;
  }
  
  public static String convert(String isoz)
  {
    String zrm;
    
    /** 
     * Rule.1 insert the followings in the beginning
     * 
     * \documentclass{article}
     * \\usepackage{fuzz}
     * 
     * \begin{document} 
     * 
     */
    String start = new String("\\documentclass{article}\n"+"\\usepackage{fuzz}\n\n"+"\\begin{document}\n\n");
    zrm = start.concat(isoz);
    
    /**
     * Rule.2 comment the following lines
     * 
     * \begin{zsection}  \SECTION register \parents~standard\_toolkit
     * \end{zsection}
     */
    
    Pattern regex = Pattern.compile("^\\\\(begin|end)\\{zsection\\}", Pattern.DOTALL | Pattern.MULTILINE);
    Matcher matcher = regex.matcher(zrm);
    zrm = matcher.replaceAll("%\\\\$1\\{zsection\\}");

    /**
     * Rule.3 add additional linefeed after \begin{zed}
     * 
     *          \begin{zed}Register_State 
     *  to
     *          \begin{zed}
     *                  Register_State
     */
    
    regex = Pattern.compile("^\\\\begin\\{zed\\}", Pattern.DOTALL | Pattern.MULTILINE);
    matcher = regex.matcher(zrm);
    zrm = matcher.replaceAll("\\\\begin\\{zed\\}\n\t");
    
    regex = Pattern.compile("^\\\\begin\\{axdef\\}", Pattern.DOTALL | Pattern.MULTILINE);
    matcher = regex.matcher(zrm);
    zrm = matcher.replaceAll("\\\\begin\\{axdef\\}\n\t");
    
    /**
     * Rule.4 
     * 
     * Schema horizontal definition "== [" is replaced by "\defs [~ ~]" 
     */
    regex = Pattern.compile("== \\[([^\n\r]*)\\]", Pattern.DOTALL | Pattern.MULTILINE);
    matcher = regex.matcher(zrm);
    zrm = matcher.replaceAll("\\\\defs \\[~ $1 ~\\]");
    
//    regex = Pattern.compile("State == (.*)", Pattern.DOTALL | Pattern.MULTILINE);
//    matcher = regex.matcher(zrm);
//    zrm = matcher.replaceAll("State \\\\defs $1");
    
    // replace other == to \defs except the (\LET x==y @ P) expression 
//    regex = Pattern.compile("([^(LET)].*) == ", Pattern.DOTALL | Pattern.MULTILINE);
    // (?!X)    X, via zero-width negative lookahead
    regex = Pattern.compile("(^\\(?!.*\\(\\\\LET\\)\\).*) == ", Pattern.DOTALL | Pattern.MULTILINE);
    matcher = regex.matcher(zrm);
    zrm = matcher.replaceAll("$1 \\\\defs ");
    
    // for abbreviations, we recover them
    regex = Pattern.compile("=Sch=", Pattern.DOTALL | Pattern.MULTILINE);
    matcher = regex.matcher(zrm);
    zrm = matcher.replaceAll("\\\\defs");
    
    // for abbreviations, we recover them
    regex = Pattern.compile("=Abbr=", Pattern.DOTALL | Pattern.MULTILINE);
    matcher = regex.matcher(zrm);
    zrm = matcher.replaceAll("==");
    
    /**
     * Rule.5 remove additional blankspace
     * 
     *  "Register\_ State" to "Register\_State"
     */
    regex = Pattern.compile("(\\w)\\\\_ (\\w)", Pattern.DOTALL | Pattern.MULTILINE);
    matcher = regex.matcher(zrm);
    zrm = matcher.replaceAll("$1\\\\_$2");
    
    /**
     * "\_ " to "\_"
     */
    regex = Pattern.compile("\\\\_ (\\w)", Pattern.DOTALL | Pattern.MULTILINE);
    matcher = regex.matcher(zrm);
    zrm = matcher.replaceAll("\\\\_$1");
    
    /**
     * Rule.6 schema decoration
     * 
     *  "( Register\_State ) '" to "Register\_State'"
     */
    regex = Pattern.compile("\\( ([^\\)]+) \\) \\'", Pattern.DOTALL | Pattern.MULTILINE);
    matcher = regex.matcher(zrm);
    zrm = matcher.replaceAll("$1\\'");
    
    // State~' to State'
    regex = Pattern.compile("\\~\\'", Pattern.DOTALL | Pattern.MULTILINE);
    matcher = regex.matcher(zrm);
    zrm = matcher.replaceAll("\\'");
    
    /**
     * Rule.7 schema init renaming
     * 
     *  "Register\_Init" to "Init"
     *  "fRegister\_Init" to "fRegister\_Init"
     */
//    regex = Pattern.compile("\t([^f]\\w*)\\\\_Init \\\\defs", Pattern.DOTALL | Pattern.MULTILINE);
//    matcher = regex.matcher(zrm);
//    zrm = matcher.replaceAll("\tInit \\\\defs");
    
    /**
     * Rule.8 ~\negate to -
     * 
     *  "~\negate" to "-"
     */
    regex = Pattern.compile("\\~\\\\negate ", Pattern.DOTALL | Pattern.MULTILINE);
    matcher = regex.matcher(zrm);
    zrm = matcher.replaceAll(" -");
    
    /**
     * Rule.1 Append in the end
     */
    zrm = zrm.concat("\\end{document}\n");
    
    
    /**
     * Rule.xxx "\\" only line should be removed 
     * 
        \begin{schema}{P\_CellWrite}
        \\
         \Delta P\_State \\
         x? : \nat 
        \where
         P\_v' = x?
        \end{schema}
     */
    regex = Pattern.compile("^\\\\\\\\$", Pattern.DOTALL | Pattern.MULTILINE);
    matcher = regex.matcher(zrm);
    zrm = matcher.replaceAll("");
    
    /**
     * Omega_2 Rule 9
     *  \infix => \inseq
     */
    regex = Pattern.compile("\\\\infix", Pattern.DOTALL | Pattern.MULTILINE);
    matcher = regex.matcher(zrm);
    zrm = matcher.replaceAll("\\\\inseq");
    
    /**
     * some special conversion and may be removed in the future
     * 1. \nat _{1} should be \nat_1
     */
    regex = Pattern.compile("\\\\nat _\\{1\\}", Pattern.DOTALL | Pattern.MULTILINE);
    matcher = regex.matcher(zrm);
    zrm = matcher.replaceAll("\\\\nat_1");

    /**
     * some special conversion and may be removed in the future
     * 2. \emptyset[T] to \emptyset
     */
    regex = Pattern.compile("\\\\emptyset \\[[\\\\a-zA-Z0-9_ ]+\\]", Pattern.DOTALL | Pattern.MULTILINE);
    matcher = regex.matcher(zrm);
    zrm = matcher.replaceAll("\\\\emptyset");
    return zrm;
  }
}

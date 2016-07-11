
package net.sourceforge.czt.circus2zcsp.visitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus.ast.CircusFactory;
import net.sourceforge.czt.circus.ast.CircusFieldList;
import net.sourceforge.czt.circus.ast.CommPattern;
import net.sourceforge.czt.circus.ast.Communication;
import net.sourceforge.czt.circus.visitor.CommunicationVisitor;
import net.sourceforge.czt.circus2zcsp.Debug;
import net.sourceforge.czt.circus2zcsp.data.VariableRenameSchema;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.OutStroke;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.StrokeList;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZStrokeList;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.ZNameVisitor;

/**
 * Rename the variable name in ZName according to different schema
 * 
 * @author rye
 */
public class VariableRenamingSchemaVisitor 
  implements    TermVisitor<Object>, 
                ZNameVisitor<Object>,
                CommunicationVisitor<Object>
{
  /**
   * a list of original names in Term to be renamed
   */
  private List<String> vlist_ = null;

  /**
   * a list of original names in Term to be renamed
   */
  private Set<Pair<ZName, ZName>> vzname_list_ = null;

  /**
   * a list of (original name, replaced name) pair
   */
  private List<Pair<String, String>> vlist2_ = null;
  
  /**
   * a set of (original name, (replaced name, its expr)) pair
   */
  private Map<String, Pair<String, Expr>> vmap3_ = null;

  /**
   * rename schema
   */
  private VariableRenameSchema vrs_;

  private ZFactory fac_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
  
  private CircusFactory cfac_ = new net.sourceforge.czt.circus.impl.CircusFactoryImpl();

  private final Stack<Term> stack_parent_ = new Stack<Term>();;

  /**
   * According to VariableRenameSchema to rename the variables which are in vlist in the term
   * @param vlist
   * @param vrs
   */
  public VariableRenamingSchemaVisitor(List<String> vlist, VariableRenameSchema vrs)
  {
    vlist_ = vlist;
    vrs_ = vrs;
  }

  /**
   * Rename the variables, which are in the first of vlist2, to the second of vlist2
   * @param vrs
   * @param vlist2
   */
  public VariableRenamingSchemaVisitor(VariableRenameSchema vrs, List<Pair<String, String>> vlist2)
  {
    vlist2_ = vlist2;
    vrs_ = vrs;
  }
  
  /**
   * Rename the variables, which are in the key of vmap3, to the first of value of vmap3 with its
   *  type in the second of pair
   * @param vrs
   * @param vmap3
   */
  public VariableRenamingSchemaVisitor(VariableRenameSchema vrs, Map<String, Pair<String, Expr>> vmap3)
  {
    vmap3_ = vmap3;
    vrs_ = vrs;
  }

  /**
   * Rename the variables, for VRS_ZNAME_RENAME
   * @param vrs - VRS_ZNAME_RENAME
   * @param vlist4
   */
  public VariableRenamingSchemaVisitor(VariableRenameSchema vrs, Set<Pair<ZName, ZName>> vlist4)
  {
    vzname_list_ = vlist4;
    vrs_ = vrs;
  }

  /**
   * Traverse the whole tree under this term
   */
  @Override
  public Object visitTerm(Term zedObject)
  {
//        System.out.println("visitTerm: " + zedObject.toString());
    Object[] args = zedObject.getChildren();
    for (int i = 0; i < args.length; i++) {
      if (args[i] instanceof Term) {
        stack_parent_.push((Term)args[i]);
        args[i] = ((Term) args[i]).accept(this);
        stack_parent_.pop();
      }
    }
    return null;
  }

  protected Object visit(Term t)
  {
    if (t != null) {
      stack_parent_.push(t);
      Object o = t.accept(this);
      stack_parent_.pop();
      return o;
    }
    return null;
  }

  /**
   * replace name in ZName according to the map in map_
   */
  @Override
  public Object visitZName(ZName term)
  {
    // Stroke is not counted in
    String oldname = term.getWord();

    if (vrs_ == VariableRenameSchema.VRS_UNKNOWN) {
      return null;
    }
    else if (vrs_ == VariableRenameSchema.VRS_APPEND_INSTROKE) {
      if (vlist_ == null || !vlist_.contains(oldname))
      {
        return null;
      }
      
      net.sourceforge.czt.z.ast.ZStrokeList slt = term.getZStrokeList();
      if (slt.isEmpty()) {
        // create InStroke ?
        List<Stroke> ls = new ArrayList<Stroke>();
        Stroke st = fac_.createInStroke();
        ls.add(st);

        net.sourceforge.czt.z.ast.StrokeList sl = fac_.createZStrokeList(ls);
        term.setStrokeList(sl);
      }
    }
    else if (vrs_ == VariableRenameSchema.VRS_APPEND_OUTSTROKE) {
      if (vlist_ == null || !vlist_.contains(oldname))
      {
        return null;
      }
      
      net.sourceforge.czt.z.ast.ZStrokeList slt = term.getZStrokeList();
      if (slt.isEmpty()) {
        // create OutStroke ?
        List<Stroke> ls = new ArrayList<Stroke>();
        Stroke st = fac_.createOutStroke();
        ls.add(st);

        net.sourceforge.czt.z.ast.StrokeList sl = fac_.createZStrokeList(ls);
        term.setStrokeList(sl);
      }
    }
    else if (vrs_ == VariableRenameSchema.VRS_APPEND_NEXTSTROKE) {
      if (vlist_ == null || !vlist_.contains(oldname))
      {
        return null;
      }
      
      net.sourceforge.czt.z.ast.ZStrokeList slt = term.getZStrokeList();
      if (slt.isEmpty()) {
        // create NextStroke ?
        List<Stroke> ls = new ArrayList<Stroke>();
        Stroke st = fac_.createNextStroke();
        ls.add(st);

        net.sourceforge.czt.z.ast.StrokeList sl = fac_.createZStrokeList(ls);
        term.setStrokeList(sl);
      }
    }
    else if (vrs_ == VariableRenameSchema.VRS_ACTION_RENAME) {
      if (vlist2_ == null) {
        return null;
      }
      for(Pair<String, String> p: vlist2_) {
        if (p.getFirst().equals(oldname)) {
          term.setWord(p.getSecond());
        }
      }
    }
    else if (vrs_ == VariableRenameSchema.VRS_NEXT_OUTSTROKE) {
      oldname = term.getWord(); //term.toString();
      if (vlist_ == null || !vlist_.contains(oldname))
      {
        return null;
      }
      
      net.sourceforge.czt.z.ast.ZStrokeList slt = term.getZStrokeList();
      // create OutStroke !
      List<Stroke> ls = new ArrayList<Stroke>();
      Stroke st = fac_.createOutStroke();
      
      if (!slt.isEmpty()) {
        for(int i = 0; i < slt.size(); i++) {
          if(slt.get(i) instanceof NextStroke) {
            ls.add(st);
          }
          else {
            ls.add(slt.get(i));
          }
        }

        net.sourceforge.czt.z.ast.StrokeList sl = fac_.createZStrokeList(ls);
        term.setStrokeList(sl);
      }
    }
    else if (vrs_ == VariableRenameSchema.VRS_NAME_REPLACE) {
      assert (vlist2_ == null || vmap3_ == null);
      
      if(ZUtils.isDelta(term)) {
        oldname = term.getWord().replace(ZString.DELTA, "");
      }
      else if(ZUtils.isXi(term)) {
        oldname = term.getWord().replace(ZString.XI, "");
      }
      
      if (vlist2_ != null) {
        for(Pair<String, String> p: vlist2_) {
          if (p.getFirst().equals(oldname)) {
            if(ZUtils.isDelta(term)) {
              term.setWord(ZString.DELTA + p.getSecond());
            }
            else if(ZUtils.isXi(term)) {
              term.setWord(ZString.XI + p.getSecond());
            }
            else {
              term.setWord(p.getSecond());
            }
          }
        }
      }
      else if(vmap3_ != null) {
        Pair<String, Expr> p = vmap3_.get(oldname);
        if(p != null) {
          if(ZUtils.isDelta(term)) {
            term.setWord(ZString.DELTA + p.getFirst());
          }
          else if(ZUtils.isXi(term)) {
            term.setWord(ZString.XI + p.getFirst());
          }
          else {
            // if its parent is RefExpr, replace it by this new expr
            if(p.getSecond() != null && stack_parent_.size() > 2 && 
                stack_parent_.get(stack_parent_.size() - 2) instanceof RefExpr) {
              
              Stack<Term> temp = new Stack<Term>();
              temp.addAll(stack_parent_);
              temp.pop();
              Circus2ZCSPUtils.updateParentRef(temp, 
                  (RefExpr)temp.get(temp.size() - 1), p.getSecond());
            }
            else {
              term.setWord(p.getFirst());
            }
          }
        }
      }
    }
    else if (vrs_ == VariableRenameSchema.VRS_RWT_RENAME) {
      if(ZUtils.isDelta(term)) {
        oldname = term.getWord().replace(ZString.DELTA, "");
      }
      else if(ZUtils.isXi(term)) {
        oldname = term.getWord().replace(ZString.XI, "");
      }
      
      // x! will not be renamed and only x will
      if (vlist2_ == null) {
        return null;
      }
      
      ZStrokeList sl = term.getZStrokeList();
      boolean b = true;
      
      if(sl.isEmpty()) {
        b = true;
      }
      else {
        for(Stroke s: sl) {
          // x! and x? would not be renamed, but x' will be renamed.
          if((s instanceof InStroke) || (s instanceof OutStroke)) {
//            b = false; // would not be renamed
            b = true; // renamed
          }
        }
      }
      
      if(b) {
        for(Pair<String, String> p: vlist2_) {
          if (p.getFirst().equals(oldname)) {
            if(ZUtils.isDelta(term)) {
              term.setWord(ZString.DELTA + p.getSecond());
            }
            else if(ZUtils.isXi(term)) {
              term.setWord(ZString.XI + p.getSecond());
            }
            else {
              term.setWord(p.getSecond());
            }
          }        
        }
      }
    }
    else if(vrs_ == VariableRenameSchema.VRS_ZNAME_RENAME) {
      ZName term2 = ZUtils.cloneTerm(term);
      
      if(ZUtils.isDelta(term)) {
        term2.setWord(term2.getWord().replace(ZString.DELTA, ""));
      }
      else if(ZUtils.isXi(term)) {
        term2.setWord(term2.getWord().replace(ZString.XI, ""));
      }
      
      // x! will not be renamed and only x will
      if (vzname_list_ == null) {
        return null;
      }

      for(Pair<ZName, ZName> p: vzname_list_) {
        if(Circus2ZCSPUtils.isEquals(term2, p.getFirst())) {
          term.setStrokeList(p.getSecond().getZStrokeList());
          term.setId(p.getSecond().getId());
          if(ZUtils.isDelta(term)) {
            term.setWord(ZString.DELTA + p.getSecond().getWord());
          }
          else if(ZUtils.isXi(term)) {
            term.setWord(ZString.XI + p.getSecond().getWord());
          }
          
        }
      }
    }

    return term;
  }

  @Override
  public Object visitCommunication(Communication term)
  {
    /**
     * for indexed process, 
     *  if its process is a basic process and after typechecking, the channel may be renamed to c\_i
     *  if its process is a reference expr to another basic process, the channel still has name c
     */
    // it may like c\_i
    String chn_name = Circus2ZCSPUtils.termToString(term.getChannelExpr().getZName());

    // extract channel name (c) only
    Pattern tptn = Pattern.compile("^(\\w+)\\\\_(\\w+)"); // extract c and i from c\_i
    Matcher tm = tptn.matcher(chn_name);
    String old_chn_name = "";
    if(tm.find()) {
      old_chn_name = tm.group(1);
    }
    
    if(old_chn_name.isEmpty()) {
      old_chn_name = chn_name;
    }
    
    if(vrs_ == VariableRenameSchema.VRS_CHN_RENAME) {
      // like c_i.1, c_i!1, c_i?1!2
      // TODO: since Expr in p is only for one expr, we only support one field in new name.
      // So c_i.1 is fine but c_i.1.2 is wrong.
      
      Pair<String, Expr> p = vmap3_.get(old_chn_name);
      if(p == null) {
        // no need to rename
        return null;
      }
      String new_name = p.getFirst();
      Pattern ptn = Pattern.compile("^(\\w+)"); // extract channel name of c_i.1
      Matcher m = ptn.matcher(new_name);
      if(m.find()) {
        String new_chn = m.group(1);
//        assert(new_chn.equals(chn_name));
        
        // replace c to c_i
        term.getChannelExpr().setName(fac_.createZName(new_chn, 
            fac_.createZStrokeList(), null));
        
        // add field
        CircusFieldList cfl = term.getCircusFieldList();
        ptn = Pattern.compile("([\\.!?])(\\w+)");
        m = ptn.matcher(new_name);
//            m = ptn.matcher("c_v.2!3?4");
        CircusFieldList new_fieldlist = cfac_.createCircusFieldList();
        boolean b_input_field = false;
        boolean b_output_field = false;
        
        while(m.find()) {
          String delimiter = m.group(1);
          String field = m.group(2);
          Debug.debug_print(delimiter + ":" + field);
          
          RefExpr re = fac_.createRefExpr(fac_.createZName(field, fac_.createZStrokeList(), null), 
              fac_.createZExprList(), false, false);
          net.sourceforge.czt.circus.ast.Field f = null;
          if (delimiter.equals(".")) {
             f = cfac_.createDotField(p.getSecond());
             b_output_field = true; // dot is treated as output
          }
          else if (delimiter.equals("!")) {
            f = cfac_.createOutputField(p.getSecond());
            b_output_field = true;
          }
          else if (delimiter.equals("?")) {
            f = cfac_.createInputField(fac_.createZName(field, fac_.createZStrokeList(), null), 
                 fac_.createFalsePred());
            b_input_field = true;
          }
          
          new_fieldlist.add(f);
        }
        new_fieldlist.addAll(cfl);
        term.setFieldList(new_fieldlist);
        
        // change of CommPattern
        switch(term.getCommPattern()) {
          case Synch:
            if(b_output_field && b_input_field) {
              term.setCommPattern(CommPattern.Mixed);
            } else if (b_output_field) {
              term.setCommPattern(CommPattern.Output);
            } else if (b_input_field) {
              term.setCommPattern(CommPattern.Input);
            }
            break;
          case Mixed: // no change
            break;
          case Input:
            if(b_output_field) {
              term.setCommPattern(CommPattern.Mixed);
            }
            break;
          case Output:
            if (b_input_field) {
              term.setCommPattern(CommPattern.Mixed);
            }
          default :
            break;
        }
      }
      else {
        throw new CztException("Invalid channel name renamed to from " + chn_name);
      }
    }
    else if (vrs_ == VariableRenameSchema.VRS_NAME_REPLACE) {
      assert (vlist2_ == null || vmap3_ == null);
      if (vlist2_ != null) {
        for(Pair<String, String> p: vlist2_) {
          if (p.getFirst().equals(chn_name)) {
            term.getChannelExpr().getZName().setWord(p.getSecond());
          }
        }
      }
      else if(vmap3_ != null) {
        Pair<String, Expr> p = vmap3_.get(chn_name);
        if(p != null) {
          term.getChannelExpr().getZName().setWord(p.getFirst());
        }
        visitTerm(term.getCircusFieldList());
      }
    }
    else if(vrs_ == VariableRenameSchema.VRS_RWT_RENAME) {
      visitTerm(term.getChannelExpr());
      visitTerm(term.getCircusFieldList());
    }
    return null;
  }

}

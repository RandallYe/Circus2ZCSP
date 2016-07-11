/*
 * Schema Expression in AxPara
 */

package net.sourceforge.czt.circus2zcsp.visitor;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.parser.util.Pair;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.NumStroke;
import net.sourceforge.czt.z.ast.OutStroke;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.MemPredVisitor;
import net.sourceforge.czt.z.visitor.SchExprVisitor;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;

public class SchemaExprInOutsVisitor 
  implements AxParaVisitor<Object>,
    SchExprVisitor<Object>
{
  /**
   * schema decoration, such as ?in!out
   */
  private String sch_decor_;
  
  private final Visitor<Object> visitor_ = this;
  
  private final String section_name_;
  
  private final SectionManager manager_;
  
  private final List<Pair<String, Term>> inout_expr_;

  public String getSchDecor()
  {
    return sch_decor_;
  }

  public SchemaExprInOutsVisitor()
  {
    sch_decor_ = new String();
    section_name_ = null;
    manager_ = null;
    inout_expr_ = new ArrayList<Pair<String, Term>>();
  }
  
  public SchemaExprInOutsVisitor(String sectionName, SectionManager manager)
  {
    sch_decor_ = new String();
    section_name_ = sectionName;
    manager_ = manager;
    inout_expr_ = new ArrayList<Pair<String, Term>>();
  }
  
  public List<Pair<String, Term>> getInOutExpr()
  {
    return inout_expr_;
  }

  @Override
  public String visitAxPara(AxPara term)
  {
    String ret = "";
    
    ZName name = null;
    Expr expr = null;
    
    switch(Circus2ZCSPUtils.getAxParaKind(term)) {
      case ABBR:
        expr = ZUtils.getAbbreviationExpr(term);
        name = (ZName) ZUtils.getAbbreviationName(term);
        break;
      case BOXED_SCHEMA:
      case HORIZON_SCHEMA:
        name = (ZName) ZUtils.getSchemaName(term);
        expr = ZUtils.getSchemaDefExpr(term);
        break;
      default:
        break;
    }
    
    if(name != null) {
      ret = Circus2ZCSPUtils.termToString(name);
      sch_decor_ += ret;
    }
    
    if(expr != null) {
      // expand the schema
      if(section_name_ != null && manager_ != null) {
        expr = Circus2ZCSPUtils.expansionSchema(expr, section_name_, manager_);
      }
      
      visit(expr);
    }
//    for (Decl decl : term.getZSchText().getZDeclList()) {
//      if (decl instanceof ConstDecl) {
//        /* get schema name */
//        ret = ((ConstDecl) decl).getZName().getWord();
//
//        InOutVisitor iov = new InOutVisitor();
//        decl.accept(iov);
//        /* append the input and output declarations */
//        ret = ret.concat(iov.toString());
//        sch_decor_ = ret;
//      }
//    }

    return sch_decor_;
  }

  @Override
  public Object visitSchExpr(SchExpr term)
  {
    for(Decl decl: term.getZSchText().getZDeclList()) {
      String ret = "";
      SchExprInOutVisitor iov = new SchExprInOutVisitor();
      decl.accept(iov);
      /* append the input and output declarations */
      ret = ret.concat(iov.toString());
      inout_expr_.addAll(iov.getInOutExpr());
      sch_decor_ += ret;
    }
    return null;
  }

  protected Object visit(Term t)
  {
    if (t != null) {
      return t.accept(visitor_);
    }
    return null;
  }

}

/**
 * Extract input and output declarations from a schema expression
 * @author rye
 */
class SchExprInOutVisitor
    implements
      TermVisitor<String>,
      VarDeclVisitor<String>
{
  /**
   * map between the name of declared variable and its expression
   * for example, o!:RES => {o!, RES}
   */
  private List<Pair<String, Term>> inout_expr_ = null;

  public SchExprInOutVisitor()
  {
    inout_expr_ = new ArrayList<Pair<String, Term>>();
  }

  public List<Pair<String, Term>> getInOutExpr() 
  {
    return inout_expr_;
  }
  
  @Override
  public String visitTerm(Term zedObject)
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
  public String visitVarDecl(VarDecl term)
  {
    for (Name zn : term.getZNameList()) {
      if (zn instanceof ZName) {
        for (net.sourceforge.czt.z.ast.Stroke sk : ((ZName) zn).getZStrokeList()) {
          // ? input or output parameters
          if ((sk instanceof InStroke) || (sk instanceof OutStroke)) {
            int index = 0;
            boolean found = false;
            for(Pair<String, Term> p: inout_expr_) {
              if(p.getFirst().equals(Circus2ZCSPUtils.termToString(zn))) {
//                inout_expr_.set(index, new Pair<String, String>(p.getFirst(), 
//                    p.getSecond() + "." + Circus2ZCSPUtils.termToString(term.getExpr())));
                inout_expr_.set(index, new Pair<String, Term>(p.getFirst(), term.getExpr()));
                found = true;
                break;
              }
              index++;
            }
            if(!found) {
              inout_expr_.add(new Pair<String, Term>(Circus2ZCSPUtils.termToString(zn), term.getExpr()));
            }
          }
          // '
          else if (sk instanceof NextStroke) {

          }
          //
          else if (sk instanceof NumStroke) {
          }
        }
      }
    }
    return null;
  }

  public String toString()
  {
    String str = "";
    for(Pair<String, Term> p: inout_expr_) {
      if (p.getFirst().endsWith("?")) {
        str += "!" + p.getFirst().replace("?", "");
      }
      else if (p.getFirst().endsWith("!")) {
        str += "?" + p.getFirst().replace("!", "");
      }
    }
    return str;
  }

}

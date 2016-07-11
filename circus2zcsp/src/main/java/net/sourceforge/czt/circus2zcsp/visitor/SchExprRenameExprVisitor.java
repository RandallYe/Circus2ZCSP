package net.sourceforge.czt.circus2zcsp.visitor;

import java.text.MessageFormat;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.visitor.BasicProcessVisitor;
import net.sourceforge.czt.circus.visitor.ProcessParaVisitor;
import net.sourceforge.czt.circus2zcsp.data.CircusSpecMap;
import net.sourceforge.czt.circus2zcsp.data.FormatPattern;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.RenameExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SchText;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.visitor.RenameExprVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;

/**
 * Rewrite SchExpr in RenameExpr by adding another schema definition and 
 * referring the new schema in current RenameExpr
 * @author rye
 *
 */
public class SchExprRenameExprVisitor
  implements RenameExprVisitor<Object>,
  ZSectVisitor<Object>,
//  AxParaVisitor<Object>,
  TermVisitor<Object>,
  ProcessParaVisitor<Object>,
  BasicProcessVisitor<Object>
{
  private ZSect zs_ = null;
  private String sectname_ = null;
  private Visitor<Object> visitor_ = this;
  private BasicProcess basic_proc_ = null;
  private CircusSpecMap map_ = null;
  private final ZFactory fac_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();
  
  /**
   * The index of the paragraph, which is in visiting, in ZSect 
   */
  private int global_index_ = 0;

  /**
   * The index of the paragraph, which is in visiting, in ZSect 
   */
  private int local_index_ = 0;

  public SchExprRenameExprVisitor(CircusSpecMap map)
  {
    map_ = map;
  }
  
  protected Object visit(Term t)
  {    
    if (t != null) {
      return t.accept(visitor_);
    }
    return null;
  }
  
  @Override
  public Object visitProcessPara(ProcessPara term)
  {
    visit(term.getCircusProcess());
    //
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

//  @Override
//  public Object visitAxPara(AxPara term)
//  {
//    return null;
//  }

  @Override
  public Object visitZSect(ZSect term)
  {
    zs_ = term;
    global_index_ = 0;
    for(Para p: term.getZParaList()) {
      if(p instanceof ProcessPara) {
        visit(p);
      }
      else if(p instanceof AxPara) {
        visit(p);
      }
      global_index_++;
    }

    zs_ = null;
    return null;
  }

  @Override
  public Object visitRenameExpr(RenameExpr term)
  {
    if(term.getExpr() instanceof SchExpr) {
      // in this case, we have to add additional schema abbr in Z and then this Schema Expression refers to it
      String strParaName = 
          MessageFormat.format(FormatPattern.TEMP_SCHEMA_NAMING_SCHEXPR, map_.getAndIncVarNum());
      ZName paraname = fac_.createZName(
          strParaName, fac_.createZStrokeList(), null);
      ConstDecl cd = fac_.createConstDecl(paraname, term.getExpr());

      ZDeclList declList0 = fac_.createZDeclList();
      declList0.add(cd);
      
      SchText schtext = fac_.createZSchText(declList0, null);

      ZNameList fp = fac_.createZNameList();
      AxPara axpara = fac_.createAxPara(fp, schtext, Box.OmitBox);
      
      if(basic_proc_ != null) {
        basic_proc_.getZParaList().add(local_index_, axpara);
      }
      else {
        zs_.getZParaList().add(global_index_, axpara);
      }
      
      term.setExpr(fac_.createRefExpr(paraname, fac_.createZExprList(), false, false));
    }
    return null;
  }

  @Override
  public Object visitBasicProcess(BasicProcess term)
  {
    local_index_ = 0;
    basic_proc_ = term;

    for(Para p: term.getZParaList()) {
      if(p instanceof AxPara) {
        visit(p);
      }
      local_index_++;
    }
    basic_proc_ = null;
    return null;
  }

}

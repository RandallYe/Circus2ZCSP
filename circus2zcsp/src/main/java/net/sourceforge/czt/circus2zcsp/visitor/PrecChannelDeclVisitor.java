/*
 * The precondition of Schema Paragraph to channel definition
 * All outputs are removed since precondition only includes state variables and inputs
 * For example,
 *      Read = [\Delta S; o!:\nat | pred]
 *    to
 *      channel Read
 * For example,
 *      Write = [\Delta S; i?:\nat; o!:\nat | pred]
 *    to
 *      channel Write:Nat
 */

package net.sourceforge.czt.circus2zcsp.visitor;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.circus2zcsp.data.FormatPattern;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.visitor.AxParaVisitor;

public class PrecChannelDeclVisitor implements AxParaVisitor<Object>
{
  private List<String> channels_;

  public List<String> getChannels()
  {
    return channels_;
  }

  public PrecChannelDeclVisitor()
  {
    channels_ = new ArrayList<String>();
  }

  @Override
  public List<String> visitAxPara(AxPara term)
  {
    String ret = "";
    String expr;

    for (Decl decl : term.getZSchText().getZDeclList()) {
      if (decl instanceof ConstDecl) {
        ret = "channel " + MessageFormat.format(FormatPattern.NEG_PRECONDITION_SCHEMA, 
            ((ConstDecl) decl).getZName().getWord());

        expr = decl.accept(new InVisitor());
        if (!expr.equals("") && expr != null) {
          ret += " : " + expr;
        }

        channels_.add(ret);
      }
    }

    return channels_;
  }
}

/*
 * Schema Paragraph to channel definition
 * For example,
 *      Read = [\Delta S; o!:\nat | pred]
 *    to
 *      channel Read:Nat
 * For example,
 *      Write = [\Delta S; i?:\nat; o!:\nat | pred]
 *    to
 *      channel Write:Nat.Nat
 */
package net.sourceforge.czt.circus2zcsp.visitor;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.visitor.AxParaVisitor;

public class ChannelDeclVisitor implements /* TermVisitor<Object>, */
//				NameVisitor<Object>,
//				ZNameVisitor<Object>,
      AxParaVisitor<Object>
{

  private List<String> channels_;

  public List<String> getChannels()
  {
    return channels_;
  }

  public ChannelDeclVisitor()
  {
    channels_ = new ArrayList<String>();
  }

//	@Override
//	public String visitZName(ZName term) {
//		Map<String, String> namemap = new HashMap<String, String>();
//		String ret = "";
//		for(net.sourceforge.czt.z.ast.Stroke sk: term.getZStrokeList())
//		{
//			// ?
//			if (sk instanceof InStroke)
//			{
//				ret = term.getWord();
//			}
//			// !
//			else if (sk instanceof OutStroke)
//			{
//				ret = term.getWord();
//			}
//			// '
//			else if (sk instanceof NextStroke)
//			{
//				
//			}
//			//
//			else if (sk instanceof NumStroke)
//			{
//				
//			}
//		}
//		return ret;
//	}
//
//	@Override
//	public String visitName(Name term) {
//		// TODO Auto-generated method stub
//		return null;
//	}

//	@Override
//	public String visitTerm(Term zedObject) {
//		Object[] args = zedObject.getChildren();
//		for (int i = 0; i < args.length; i++) {
//			if (args[i] instanceof Term) {
//				args[i] = ((Term) args[i]).accept(this);
//			} 
//		}
//		return null;
//	}

  @Override
  public List<String> visitAxPara(AxPara term)
  {
    String ret = "";
    String expr;

    for (Decl decl : term.getZSchText().getZDeclList()) {
      if (decl instanceof ConstDecl) {
        ret = "channel " + ((ConstDecl) decl).getZName().getWord();
//				channels_.add(ret);

        expr = decl.accept(new InOutVisitor());
        if (!expr.equals("") && expr != null) {
          ret += " : " + expr;
        }

        channels_.add(ret);
      }
    }

    return channels_;
  }

}

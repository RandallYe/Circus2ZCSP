package net.sourceforge.czt.circus2zcsp.visitor;

import java.util.HashSet;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus.ast.Communication;
import net.sourceforge.czt.circus.visitor.CommunicationVisitor;

/*
 * get a set of communication channels in the term
 */
public class CommsVisitor
  implements
  TermVisitor<Object>,
  CommunicationVisitor<Object>
{
  private Set<String> set_comms_ = new HashSet<String>();
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
  
  public Set<String> getCommsSet()
  {
    return set_comms_;
  }

  @Override
  public Object visitCommunication(Communication term)
  {
    set_comms_.add(term.toString());
    return null;
  }
}

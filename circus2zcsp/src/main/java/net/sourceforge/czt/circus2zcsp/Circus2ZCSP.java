/*
 * Convert Circus specification to CSP || Z
 */

package net.sourceforge.czt.circus2zcsp;

import net.sourceforge.czt.circus2zcsp.ast.CSPSpec;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.SectionInfoException;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

public class Circus2ZCSP
{
  public Circus2ZCSP(SectionManager manager, String name) throws SectionInfoException,
      CommandException
  {
    Transformer trans = new Transformer(manager, name);
    Spec spec = trans.getSpec();
    CSPSpec cspspec = trans.getCSPSpec();
    ZSect zs = trans.getZSectOfCircus();
    
    Circus2ZCSPUtils.outputZCSPSpecToFile(zs, spec, cspspec, manager);
  }
  

}

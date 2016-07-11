/*
 * Type in CSPm
 */

package net.sourceforge.czt.circus2zcsp.ast;

public abstract class Type
{
  /**
   * Required by VisitReturn
   */
  public abstract <T> T accept();
}

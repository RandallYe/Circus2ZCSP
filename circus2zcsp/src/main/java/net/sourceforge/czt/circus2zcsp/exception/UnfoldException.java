package net.sourceforge.czt.circus2zcsp.exception;

public class UnfoldException
  extends Exception
{
  /**
   * 
   */
  private static final long serialVersionUID = -1879278911820249212L;

  public UnfoldException(Throwable cause)
  {
    super("Unfolding failed", cause);
  }
}

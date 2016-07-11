package net.sourceforge.czt.circus2zcsp.data;

public class Triple<T1, T2, T3>
{
  private T1 t1_;
  private T2 t2_;
  private T3 t3_;

  public Triple(T1 t1, T2 t2, T3 t3)
  {
    // parameters can be null
//    if (t1 == null) throw new NullPointerException();
//    if (t2 == null) throw new NullPointerException();
//    if (t3 == null) throw new NullPointerException();
    t1_ = t1;
    t2_ = t2;
    t3_ = t3;
  }

  public T1 getT1()
  {
    return t1_;
  }
  
  public T1 getFirst()
  {
    return t1_;
  }
  
  public T2 getT2()
  {
    return t2_;
  }

  public T2 getSecond()
  {
    return t2_;
  }
  
  public T3 getT3()
  {
    return t3_;
  }
  
  public T3 getThird()
  {
    return t3_;
  }

  @Override
  public int hashCode()
  {
    return t1_.hashCode() + t2_.hashCode() + t3_.hashCode();
  }

  @Override
  public boolean equals(Object other)
  {
    if (other == null || ! (other instanceof Triple<?,?,?>))
      return false;
    Triple<?,?,?> triple = (Triple<?,?,?>) other;
    return t1_.equals(triple.getT1()) && 
        t2_.equals(triple.getT2()) && 
        t3_.equals(triple.getT3());
  }

  @Override
  public String toString()
  {
    return "(" + t1_ + "," + t2_ + "," + t3_ + ")";
  }
}

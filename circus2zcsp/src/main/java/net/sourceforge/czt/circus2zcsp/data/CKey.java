/*
 * A Circus key pair
 */
package net.sourceforge.czt.circus2zcsp.data;


/**
 * CKey is pair (String, CircusMapType)
 * @author randall
 *
 * @param <T>
 */
public class CKey<T1, T2>
{
  private T1 name1_;
  private T2 name2_;
  private CircusMapType type_;

  public CKey(T1 name1, T2 name2, CircusMapType type)
  {
    if (name1 == null) throw new NullPointerException();
    if (name2 == null) throw new NullPointerException();
    if (type == null) throw new NullPointerException();
    name1_ = name1;
    name2_ = name2;
    type_ = type;
  }

  public T1 getName1()
  {
    return name1_;
  }
  
  public T2 getName2()
  {
    return name2_;
  }

  public CircusMapType getType()
  {
    return type_;
  }

  @Override
  public int hashCode()
  {
    return name1_.hashCode() + name2_.hashCode() + type_.hashCode();
  }

  @Override
  public boolean equals(Object other)
  {
    if (other == null || ! (other instanceof CKey<?,?>))
      return false;
    CKey<?,?> key2 = (CKey<?,?>) other;
    return name1_.equals(key2.name1_) && name2_.equals(key2.name2_) && type_.equals(key2.type_);
  }

  @Override
  public String toString()
  {
    return "(" + name1_ + "," + name2_ + "," + type_.toString() + ")";
  }
}

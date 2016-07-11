/*
 * datatype in CSPm
 */
package net.sourceforge.czt.circus2zcsp.ast;

import java.util.List;

public class Datatype extends Type
{
  private final String name_;

  private final List<String> list_;

  public Datatype(String name, List<String> list)
  {
    name_ = name;
    list_ = list;
  }

  public List<String> getList()
  {
    return list_;
  }

  public String toString()
  {
    String ret = "datatype " + name_ + " = ";
    int size = list_.size();

    if (size > 0) {
      ret += list_.get(0);
    }

    for (int i = 1; i < size; i++) {
      ret += " | " + list_.get(i);
    }
    return ret;
  }

  @Override
  public <T> T accept()
  {
    // TODO Auto-generated method stub
    return null;
  }

}

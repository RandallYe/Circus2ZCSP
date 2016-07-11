package net.sourceforge.czt.circus2zcsp.data;

import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.z.ast.ZName;

public class Node implements Comparable<Node> {
  private ZName name_;
  private ZName process_;
  
  void create(ZName name, ZName process)
  {
    name_ = name;
    process_ = process;
    
    if(name_ != null) {
      // id is ignore for comparing
      name_.setId(null);
    }
    
    if(process_ != null) {
      process_.setId(null);
    }
  }
  
  public ZName getName() {
    return name_;
  }
  
  public ZName getProcess() {
    return process_;
  }
  
  public Node(ZName name, ZName process)
  {
    create(name, process);
  }
  
  public Node(ZName name, ProcessPara process)
  {
    ZName procName;
    if(process == null) {
      procName = null;
    }
    else 
    {
      procName = process.getZName();
    }
    
    create(name, procName);
  }
  
  /**
   * check if this node is equal to obj
   */
  @Override
  public boolean equals(Object obj) 
  {
    if (obj != null) {
      if (this.getClass().equals(obj.getClass())/* && super.equals(obj)*/) {
        if (name_ != null) {
          if (!name_.equals(((Node)obj).name_)) {
            return false;
          }
        }
        else {
          if (((Node) obj).name_ != null) {
            return false;
          }
        }
        
        if (process_ != null) {
          if (!process_.equals(((Node)obj).process_)) {
            return false;
          }
        }
        else {
          if (((Node) obj).process_ != null) {
            return false;
          }
        }
        return true;
      }
    }
    return false;
  }

  /**
   * Returns the hash code value for this Node.
   */
  @Override
  public int hashCode()
  {
//    int hashCode = super.hashCode();
    int hashCode = name_.toString().hashCode();
//    Debug.debug_print("Object: " + name_.toString() + " has Hashcode: " + hashCode);
    return hashCode;
  }
  
  /**
   * return 0 if they are equal, or > 0 if this is greater than o, or < 0 if this is less than o
   */
  @Override
  public int compareTo(Node o)
  {
    if(o == null) {
      return 1;
    }
    
    if(name_ == null) {
      if(o.getName() != null) {
        return -1;
      }
    }
    else {
      if(o.getName() == null) {
        return 1;
      }
      else {
        if(!name_.equals(o.getName())) {
          return name_.toString().compareTo(o.getName().toString());
        }
      }
    }
    
    if(process_ == null) {
      if(o.getProcess() != null) {
        return -1;
      }
    }
    else {
      if(o.getProcess() == null) {
        return 1;
      }
      else {
        if(!process_.equals(o.getProcess())) {
          return process_.toString().compareTo(o.getProcess().toString());
        }
      }
    }
    
    return 0;
  }
  
  @Override
  public String toString()
  {
    StringBuilder sb = new StringBuilder();
    
    sb.append("(");
    sb.append(Circus2ZCSPUtils.termToString(name_));
    sb.append(", ");
    sb.append((process_ == null)?"null" : Circus2ZCSPUtils.termToString(process_));
    sb.append(")");
    
    return sb.toString();
  }
}
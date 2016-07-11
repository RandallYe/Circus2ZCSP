package net.sourceforge.czt.circus2zcsp.data;

import java.util.List;

import net.sourceforge.czt.circus2zcsp.data.CircusSpecMap;
import junit.framework.TestCase;

public class CircusSpecMapTest
  extends TestCase
{

  private CircusSpecMap map_ = null;
  
  public CircusSpecMapTest()
  {
    map_ = new CircusSpecMap();
  }

  public void testProcAddGet()
  {
    map_.clear();
    
    /** add */
    map_.addProc("sectname", "procname");
    assertEquals(map_.size(), 2); // consider the default GANumber
    
    /** get */
    List<String> lstr = map_.getProcList("sectname");
    assertTrue(lstr.contains("procname"));
    
    map_.addProc("sectname", "procname2");
    assertEquals(map_.size(), 4);
    
    /** get */
    lstr = map_.getProcList("sectname");
    assertTrue(lstr.contains("procname") && lstr.contains("procname2"));
  }
}

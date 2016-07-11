package net.sourceforge.czt.circus2zcsp.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.parser.util.Pair;


public class ZStat
{
  public int nr_of_paras_;    // number of paragraphs
  public int nr_of_processes_;// number of processes
  public List<String> lst_processes_; // a list of processes name
  public String str_spec_;      // print of spec
  public Map<String, Set<String>> map_set_id_;   // map from process name to a set of its identifiers
  public Map<String, Set<String>> map_set_comms_;// map from process name to a set of communications
  public Map<String, Set<String>> map_set_schemas_;// map from process name to a set of schemas
  public Map<String, Set<String>> map_set_actions_;// map from process name to a set of action paras
  
  public ZStat()
  {
    nr_of_paras_ = 0;
    nr_of_processes_ = 0;
    lst_processes_ = new ArrayList<String>();
    str_spec_ = "";
    map_set_id_ = new HashMap<String, Set<String>>();
    map_set_comms_ = new HashMap<String, Set<String>>();
    map_set_schemas_ = new HashMap<String, Set<String>>();
    map_set_actions_ = new HashMap<String, Set<String>>();
  }
}

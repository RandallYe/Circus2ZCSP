/*
 * Contain the information of a Circus specification
 * map is a type of Hashmap(Pair<String, String, Type>, Pair<String, Term>)
 * 
 * (CKey<sectionname, procname, CMT_PROCNAME>, Pair<String, Term>(procname, null))
 * - e.g. (CKey<"Fuel_Pump", "Pump", CMT_PROCNAME>, Pair<String, Term>("Pump", null))
 * 
 * (CKey<procname, stateparaname, CMT_STATENAME>, Pair<String, Term>(stateparaname, null))
 * - e.g. (CKey<"Pump", "PState", CMT_STATENAME>, Pair<String, Term>("PState", null))
 * 
 * (CKey<procname, varname, CMT_STATEVAR>, Pair<String, Term>(varname, null))
 * - e.g. (CKey<"Pump", "fuleQ", CMT_STATEVAR>, Pair<String, Term>("fuelQ", null))
 * 
 * --------------- not used ------------------
 * (CKey<procname, "", CMT_GANUMBER>, Pair<String, Term>("num", null))
 * - e.g. (CKey<"Pump", "", CMT_GANUMBER>, Pair<String, Term>("0", null))
 * 
 * (CKey<procname, original var or schema name or action name, CMT_NAMEREP>, Pair<String, Term>(repname, term))
 * - e.g. (CKey<"Pump", "PState", CMT_NAMEREP>, Pair<String, Term>("Pump_PState", para)) - for schema, term is the schema paragraph
 * - e.g. (CKey<"Pump", "fuelQ", CMT_NAMEREP>, Pair<String, Term>("Pump_fuelQ", expr)) - for state var, term is exp/type of var
 * - e.g. (CKey<"Pump", "PumpIdle", CMT_NAMEREP>, Pair<String, Term>("Pump_PumpIdle", para)) - for action, term is the action paragraph
 * 
 * --------------- not used ------------------
 * (CKey<"", "", CMT_VARNUMBER>, "num")
 * - e.g. ("", "", CMT_VARNUMBER>, "0")
 * 
 * (CKey<"", chnname, CMT_CHNDECL>, Pair<String, Term>("expr", expr))
 * - e.g. ("", "c", CMT_CHNDECL>, Pair<String, Term>("{1,3}.{green,red}", expr))
 * 
 * (CKey<schtype_name, varname, CMT_SCHTYPE>, Pair<String, Term>("exp", exp))
 * - e.g. (CKey<"Tsch", "x", CMT_SCHTYPE>, Pair<String, Term>("{1,3}", expr))
 * - e.g. (CKey<"Tsch", "y", CMT_SCHTYPE>, Pair<String, Term>("{green}", expr))
 * 
 * (CKey<procname, nsname, CMT_NAMESET>, Pair<String, Term>("expr", expr))
 * - e.g. (CKey<"Pump", "NS1", CMT_NAMESET>, Pair<String, Term>("{x,y}", expr))
 * 
 * (CKey<"", freetype name, CMT_FREETYPE>, Pair<String, Term>("expr", expr))
 * - e.g. ("", "FT", CMT_FREETYPE>, Pair<String, Term>("a1 | a2 | a3 | d1<<T>>", expr))
 *
 * (CKey<freetype name, const name, CMT_FREETYPE_CONST>, Pair<String, Term>(const name, expr))
 * - e.g. ("FT", "a1", CMT_FREETYPE_CONST>, Pair<String, Term>("a1", RefExpr))
 *
 * (CKey<freetype name, constructor name, CMT_FREETYPE_CONSTRUCTOR>, Pair<String, Term>(constructor type string, expr))
 * - e.g. ("FT", "d1", CMT_FREETYPE_CONSTRUCTOR>, Pair<String, Term>("T", RefExpr(T)))
 */

package net.sourceforge.czt.circus2zcsp.data;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus2zcsp.Debug;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.parser.util.Pair;

public class CircusSpecMap
{

  // private Map<Pair<String, CircusMapType>, String> map_ = null;
  private Map<CKey<String, String>, Pair<String, Term>> map_ = null;
  
  /**
   * A global unique number and should not be used twice
   * It is also used to differentiate between different items
   */
  private int n_ = 0;
  
  // all channels
  private Set<String> chn_set_ = null;

  public CircusSpecMap(Map<CKey<String, String>, Pair<String, Term>> map_)
  {
    this.map_ = map_;
    chn_set_ = new HashSet<String>();
  }

  public CircusSpecMap()
  {
    this.map_ = new HashMap<CKey<String, String>, Pair<String, Term>>();
    chn_set_ = new HashSet<String>();
    addVarNum();
  }

  public Map<CKey<String, String>, Pair<String, Term>> getMap()
  {
    return map_;
  }

  public String addProc(String secName, String procName)
  {
    addGANum(procName);
    Pair<String, Term> temp = map_.put(new CKey<String, String>(secName, procName,
        CircusMapType.CMT_PROCNAME), new Pair<String, Term>(procName, null));
    return procName;
  }

  public List<String> getProcList(String secName)
  {
    List<String> lst = new ArrayList<String>();
    Iterator<Entry<CKey<String, String>, Pair<String, Term>>> it = map_.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<CKey<String, String>, Pair<String, Term>> pairs = (Map.Entry<CKey<String, String>, Pair<String, Term>>) it
          .next();
      if ((pairs.getKey().getType() == CircusMapType.CMT_PROCNAME)
          && (pairs.getKey().getName1().equals(secName))) {
        lst.add(pairs.getKey().getName2());
//        System.out.println(pairs.getKey().getName1() + ":" + pairs.getValue());
      }
//        it.remove(); // avoids a ConcurrentModificationException
    }
    return lst;
  }

  public String addStatPara(String procName, String statParaName)
  {
    Pair<String, Term> temp = map_.put(new CKey<String, String>(procName, statParaName,
        CircusMapType.CMT_STATENAME), new Pair<String, Term>(statParaName, null));
    return statParaName;
  }

  public String getStatPara(String procName)
  {
    String statPara = new String();
    Iterator<Entry<CKey<String, String>, Pair<String, Term>>> it = map_.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<CKey<String, String>, Pair<String, Term>> pairs = (Map.Entry<CKey<String, String>, Pair<String, Term>>) it
          .next();
      if ((pairs.getKey().getType() == CircusMapType.CMT_STATENAME)
          && (pairs.getKey().getName1().equals(procName))) {
        statPara = pairs.getKey().getName2();
//        System.out.println(pairs.getKey().getName1() + ":" + pairs.getValue());
        return statPara;
      }
//        it.remove(); // avoids a ConcurrentModificationException
    }
    return null;
  }

  /**
   * @param procName - process name
   * @param varName - state variable name
   * @param term - type expression
   * @return
   */
  public String addStat(String procName, String varName, Term term)
  {
    /*Pair<String, Term> temp = */map_.put(new CKey<String, String>(procName, varName,
        CircusMapType.CMT_STATEVAR), new Pair<String, Term>(varName, term));
    return varName;
  }

  /**
   * @param procName
   * @return a list of variables with original name (x)
   */
  public List<String> getStatList(String procName)
  {
    List<String> lst = new ArrayList<String>();
    Iterator<Entry<CKey<String, String>, Pair<String, Term>>> it = map_.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<CKey<String, String>, Pair<String, Term>> pairs = (Map.Entry<CKey<String, String>, Pair<String, Term>>) it
          .next();
      if ((pairs.getKey().getType() == CircusMapType.CMT_STATEVAR)
          && (pairs.getKey().getName1().equals(procName))) {
        lst.add(pairs.getKey().getName2());
//        Debug.debug_print("State Component of process [" + pairs.getKey().getName1() + "]: " + pairs.getValue().getFirst() + " [type:" 
//            + Circus2ZCSPUtils.termToString(pairs.getValue().getSecond()) + "]");
      }
//        it.remove(); // avoids a ConcurrentModificationException
    }
    return lst;
  }
  
  /**
   * @param procName
   * @return a list of variables with replaced name (PROC_x)
   */
  public List<Pair<String, Term>> getStatListWithExp(String procName)
  {
    List<Pair<String, Term>> lst = new ArrayList<Pair<String, Term>>();
    Iterator<Entry<CKey<String, String>, Pair<String, Term>>> it = map_.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<CKey<String, String>, Pair<String, Term>> pairs = (Map.Entry<CKey<String, String>, Pair<String, Term>>) it
          .next();
      if ((pairs.getKey().getType() == CircusMapType.CMT_STATEVAR)
          && (pairs.getKey().getName1().equals(procName))) {
//        lst.add(new Pair<String, Term>(
////            MessageFormat.format(FormatPattern.RENAMING_IN_PROC, procName, pairs.getValue().getFirst()),
//            pairs.getValue().getFirst(),
//            pairs.getValue().getSecond()));
        lst.add(pairs.getValue());
//        Debug.debug_print(pairs.getKey().getName1() + ":" + pairs.getValue());
      }
    }
    return lst;
  }
  
  /**
   * @param procName
   * @return a list of variables with replaced name (PROC_x, Tx)
   */
  public List<Pair<String, Term>> getStatListWithExpProName(String procName)
  {
    List<Pair<String, Term>> lst = new ArrayList<Pair<String, Term>>();
    Iterator<Entry<CKey<String, String>, Pair<String, Term>>> it = map_.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<CKey<String, String>, Pair<String, Term>> pairs = (Map.Entry<CKey<String, String>, Pair<String, Term>>) it
          .next();
      if ((pairs.getKey().getType() == CircusMapType.CMT_STATEVAR)
          && (pairs.getKey().getName1().equals(procName))) {
        lst.add(new Pair<String, Term>(
            MessageFormat.format(FormatPattern.RENAMING_IN_PROC, procName, pairs.getValue().getFirst()),
            pairs.getValue().getSecond()));
        lst.add(pairs.getValue());
//        Debug.debug_print(pairs.getKey().getName1() + ":" + pairs.getValue());
      }
    }
    return lst;
  }

  /**
   * @param procName
   * @return a list of variables with replaced name (PROC_x)
   */
  public List<String> getStatListWithProName(String procName)
  {
    List<String> lst = new ArrayList<String>();
    Iterator<Entry<CKey<String, String>, Pair<String, Term>>> it = map_.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<CKey<String, String>, Pair<String, Term>> pairs = (Map.Entry<CKey<String, String>, Pair<String, Term>>) it
          .next();
      if ((pairs.getKey().getType() == CircusMapType.CMT_STATEVAR)
          && (pairs.getKey().getName1().equals(procName))) {
        lst.add(MessageFormat.format(FormatPattern.RENAMING_IN_PROC, procName, pairs.getKey().getName2()));
//        System.out.println(pairs.getKey().getName1() + ":" + procName + "_"
//            + pairs.getKey().getName2());
      }
//        it.remove(); // avoids a ConcurrentModificationException
    }
    return lst;
  }
  
  /**
   * @param procName
   * @return a list of variables with replaced name (PROC_x)
   */
  public List<String> getStatListWithProName()
  {
    List<String> lst = new ArrayList<String>();
    Iterator<Entry<CKey<String, String>, Pair<String, Term>>> it = map_.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<CKey<String, String>, Pair<String, Term>> pairs = (Map.Entry<CKey<String, String>, Pair<String, Term>>) it
          .next();
      if (pairs.getKey().getType() == CircusMapType.CMT_STATEVAR) {
        lst.add(MessageFormat.format(FormatPattern.RENAMING_IN_PROC, pairs.getKey().getName1(), pairs.getKey().getName2()));
      }
//        it.remove(); // avoids a ConcurrentModificationException
    }
    return lst;
  }

  public String addGANum(String procName)
  {
    return "0";
  }

  public String getGANum(String procName)
  {
    return String.format("%d", getn());
  }

  public boolean incGANum(String procName)
  {
    incn();
    return true;
  }

  public String addRep(String procName, String origName, String repName, Term term)
  {
    /*Pair<String, Term> temp = */map_.put(new CKey<String, String>(procName, origName, CircusMapType.CMT_NAMEREP),
        new Pair<String, Term>(repName, term));
    return repName;
  }

  public Pair<String, Term> getRep(String procName, String origName)
  {
    Pair<String, Term> temp = map_.get(new CKey<String, String>(procName, origName, CircusMapType.CMT_NAMEREP));
    return temp;
  }
  
  public Pair<String, Term> getRepByNewName(String procName, String newName)
  {
    Iterator<Entry<CKey<String, String>, Pair<String, Term>>> it = 
        map_.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<CKey<String, String>, Pair<String, Term>> pairs = 
          (Map.Entry<CKey<String, String>, Pair<String, Term>>) it.next();
      if (pairs.getValue().getFirst().equals(newName) && pairs.getKey().getType() == CircusMapType.CMT_NAMEREP) {
        return pairs.getValue();
      }
    }

    return null;
  }

  public String addVarNum()
  {
    return "0";
  }

  /**
   * get current global number
   * @return
   *    string representation of number
   */
  public String getVarNum()
  {
    return String.format("%d", getn());
  }

  /**
   * increase the global number by one
   * @return
   *    true
   */
  public boolean incVarNum()
  {
    incn();
    return true;
  }
  
  /**
   * get current global number and also increase it by one 
   * @return
   *    string representation of number
   */
  public String getAndIncVarNum()
  {
    String ret = String.format("%d", getn());
    incn();
    return ret;
  }
  

  /**
   * @param chnname
   * @param exp
   * @param term - exp term
   * @return
   */
  public String addChnDecl(String chnname, String exp, Term term)
  {
    Pair<String, Term> temp = map_.put(new CKey<String, String>("", chnname, CircusMapType.CMT_CHNDECL), 
        new Pair<String, Term>(exp, term));
    chn_set_.add(chnname);
    return exp;
  }

  public Pair<String, Term> getChnDecl(String chnname)
  {
    Pair<String, Term> temp = map_.get(new CKey<String, String>("", chnname, CircusMapType.CMT_CHNDECL));
    return temp;// == null ? null : temp.getFirst();
  }
  
  public Set<String> getAllChannels()
  {
    return chn_set_;
  }

  /**
   * Add global schema type
   * 
   * @param chnname
   * @param exp
   * @return
   */
  public String addSchType(String schname, String varname, String exp, Term term)
  {
    Pair<String, Term> temp = map_.put(new CKey<String, String>(schname, varname, CircusMapType.CMT_SCHTYPE), 
        new Pair<String, Term>(exp, term));
    return exp;
  }

  /**
   * Return the variables and their corresponding expression for the schema name
   * 
   * @param schname
   * @return
   */
  public List<Triple<String, String, Term>> getSchType(String schname)
  {
    List<Triple<String, String, Term>> lst = new ArrayList<Triple<String, String, Term>>();
    Iterator<Entry<CKey<String, String>, Pair<String, Term>>> it = map_.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<CKey<String, String>, Pair<String, Term>> pairs = 
          (Map.Entry<CKey<String, String>, Pair<String, Term>>) it.next();
      if ((pairs.getKey().getType() == CircusMapType.CMT_SCHTYPE)
          && (pairs.getKey().getName1().equals(schname))) {
        lst.add(new Triple<String, String, Term>(pairs.getKey().getName2(), 
            pairs.getValue().getFirst(),  pairs.getValue().getSecond()));
//        Debug.debug_print(pairs.getKey().getName1() + "[" + pairs.getKey().getName2() + "] :"
//            + pairs.getValue());
      }
//      it.remove(); // avoids a ConcurrentModificationException
    }
    return lst;
  }
  
  /**
   * Add global free type
   * 
   * @param ftname - free type name
   * @param exp - the string of free type definition
   * @param term - the definition of free type
   * @return
   */
  public String addFreeType(String ftname, String exp, Term term)
  {
    Pair<String, Term> temp = map_.put(new CKey<String, String>("", ftname, CircusMapType.CMT_FREETYPE), 
        new Pair<String, Term>(exp, term));
    return exp;
  }

  /**
   * Return definition of the free type name
   * 
   * @param ftname
   * @return the definition of specified free type
   *    Triple<String, String, Term>(ftname, def, Tdef)
   */
  public List<Triple<String, String, Term>> getFreeType(String ftname)
  {
    List<Triple<String, String, Term>> lst = new ArrayList<Triple<String, String, Term>>();
    Iterator<Entry<CKey<String, String>, Pair<String, Term>>> it = map_.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<CKey<String, String>, Pair<String, Term>> pairs = (Map.Entry<CKey<String, String>, Pair<String, Term>>) it
          .next();
      if ((pairs.getKey().getType() == CircusMapType.CMT_FREETYPE)
          && (pairs.getKey().getName2().equals(ftname))) {
        lst.add(new Triple<String, String, Term>(pairs.getKey().getName2(), 
            pairs.getValue().getFirst(),  pairs.getValue().getSecond()));
//        Debug.debug_print(pairs.getKey().getName2() + " :"
//            + pairs.getValue().getFirst());
      }
//      it.remove(); // avoids a ConcurrentModificationException
    }
    return lst;
  }
  
  /**
   * Return definition of the free type name
   * 
   * @return
   *    Triple<String, String, Term>(ftname, def, Tdef)
   */
  public List<Triple<String, String, Term>> getAllFreeTypes()
  {
    List<Triple<String, String, Term>> lst = new ArrayList<Triple<String, String, Term>>();
    Iterator<Entry<CKey<String, String>, Pair<String, Term>>> it = map_.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<CKey<String, String>, Pair<String, Term>> pairs = 
          (Map.Entry<CKey<String, String>, Pair<String, Term>>) it.next();
      if ((pairs.getKey().getType() == CircusMapType.CMT_FREETYPE)) {
        lst.add(new Triple<String, String, Term>(pairs.getKey().getName2(), 
            pairs.getValue().getFirst(),  pairs.getValue().getSecond()));
//        Debug.debug_print(pairs.getKey().getName2() + " :"
//            + pairs.getValue().getFirst());
      }
//      it.remove(); // avoids a ConcurrentModificationException
    }
    return lst;
  }
  
  /**
   * Add global free type constants
   * 
   * @param ftname - free type name
   * @param constName - the string of constant name
   * @param term - expression of constant (should be ZName)
   * @return
   */
  public String addFreeTypeConst(String ftname, String constName, Term term)
  {
    Pair<String, Term> temp = map_.put(
        new CKey<String, String>(ftname, constName, CircusMapType.CMT_FREETYPE_CONST), 
        new Pair<String, Term>(constName, term));
    return constName;
  }

  /**
   * Return all constants of the freetype name
   * 
   * @param ftname - freetype name
   * @return
   *    Triple<String, String, Term>(ftname, constant, ZName(constant))
   */
  public List<Triple<String, String, Term>> getFreeTypeConsts(String ftname)
  {
    List<Triple<String, String, Term>> lst = new ArrayList<Triple<String, String, Term>>();
    Iterator<Entry<CKey<String, String>, Pair<String, Term>>> it = map_.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<CKey<String, String>, Pair<String, Term>> pairs = 
          (Map.Entry<CKey<String, String>, Pair<String, Term>>) it.next();
      if ((pairs.getKey().getType() == CircusMapType.CMT_FREETYPE_CONST)
          && (pairs.getKey().getName1().equals(ftname))) {
        lst.add(new Triple<String, String, Term>(pairs.getKey().getName1(), 
            pairs.getValue().getFirst(),  pairs.getValue().getSecond()));
//        Debug.debug_print(pairs.getKey().getName1() + "[" + pairs.getKey().getName2() + "] :"
//            + pairs.getValue().getFirst());
      }
    }
    return lst;
  }


  /**
   * Return all freetype constants
   * 
   * @param ftname
   * @return
   *    Triple<String, String, Term>(ftname, constant, ZName(constant))
   */
  public List<Triple<String, String, Term>> getAllFreeTypeConsts()
  {
    List<Triple<String, String, Term>> lst = new ArrayList<Triple<String, String, Term>>();
    Iterator<Entry<CKey<String, String>, Pair<String, Term>>> it = map_.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<CKey<String, String>, Pair<String, Term>> pairs = 
          (Map.Entry<CKey<String, String>, Pair<String, Term>>) it.next();
      if ((pairs.getKey().getType() == CircusMapType.CMT_FREETYPE_CONST)) {
        lst.add(new Triple<String, String, Term>(pairs.getKey().getName1(), 
            pairs.getValue().getFirst(),  pairs.getValue().getSecond()));
//        Debug.debug_print(pairs.getKey().getName1() + "[" + pairs.getKey().getName2() + "] :"
//            + pairs.getValue().getFirst());
      }
    }
    return lst;
  }
  
  /**
   * Add global free type constructor
   * 
   * @param ftname - free type name
   * @param constructorName - the string of constructor name
   * @param expr - the expression string of constructor
   * @param term - the term of constructor expression
   * @return
   */
  public String addFreeTypeConstructor(String ftname, String constructorName, String expr, Term term)
  {
    Pair<String, Term> temp = map_.put(
        new CKey<String, String>(ftname, constructorName, CircusMapType.CMT_FREETYPE_CONSTRUCTOR), 
        new Pair<String, Term>(expr, term));
    return expr;
  }

  /**
   * Return all constructors of the freetype name
   * 
   * @param ftname - freetype name
   * @return
   *    Triple<String, String, Term>(constructor, expr, Texpr)
   */
  public List<Triple<String, String, Term>> getFreeTypeConstructors(String ftname)
  {
    List<Triple<String, String, Term>> lst = new ArrayList<Triple<String, String, Term>>();
    Iterator<Entry<CKey<String, String>, Pair<String, Term>>> it = map_.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<CKey<String, String>, Pair<String, Term>> pairs = 
          (Map.Entry<CKey<String, String>, Pair<String, Term>>) it.next();
      if ((pairs.getKey().getType() == CircusMapType.CMT_FREETYPE_CONSTRUCTOR)
          && (pairs.getKey().getName1().equals(ftname))) {
        lst.add(new Triple<String, String, Term>(pairs.getKey().getName2(), 
            pairs.getValue().getFirst(),  pairs.getValue().getSecond()));
//        Debug.debug_print(pairs.getKey().getName1() + "[" + pairs.getKey().getName2() + "] :"
//            + pairs.getValue().getFirst());
      }
    }
    return lst;
  }


  /**
   * Return all freetype constructors
   * 
   * @param ftname
   * @return
   *    Triple<String, String, Term>(constructor, expr, Texpr)
   */
  public List<Triple<String, String, Term>> getAllFreeTypeConstructors()
  {
    List<Triple<String, String, Term>> lst = new ArrayList<Triple<String, String, Term>>();
    Iterator<Entry<CKey<String, String>, Pair<String, Term>>> it = map_.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<CKey<String, String>, Pair<String, Term>> pairs = 
          (Map.Entry<CKey<String, String>, Pair<String, Term>>) it.next();
      if ((pairs.getKey().getType() == CircusMapType.CMT_FREETYPE_CONSTRUCTOR)) {
        lst.add(new Triple<String, String, Term>(pairs.getKey().getName2(), 
            pairs.getValue().getFirst(),  pairs.getValue().getSecond()));
//        Debug.debug_print(pairs.getKey().getName1() + "[" + pairs.getKey().getName2() + "] :"
//            + pairs.getValue().getFirst());
      }
    }
    return lst;
  }
  
  /**
   * Add NameSet
   * 
   * @param chnname
   * @param exp
   * @return
   */
  public String addNameSet(String procName, String nsname, String exp, Term term)
  {
    /*Pair<String, Term> temp = */map_.put(new CKey<String, String>(procName, nsname, CircusMapType.CMT_NAMESET), 
        new Pair<String, Term>(exp, term));
    return exp;
  }
  
  public Pair<String, Term> getNameSet(String procName, String nsname)
  {
    Pair<String, Term> temp = map_.get(new CKey<String, String>(procName, nsname, CircusMapType.CMT_NAMESET));
    return temp;
  }
  
  /**
   * Add global GivenSet name
   * 
   * @param name
   * @param 
   * @return
   */
  public String addGivenSet(String name)
  {
    /*Pair<String, Term> temp = */map_.put(new CKey<String, String>("", name, CircusMapType.CMT_GIVENTYPE), 
        null);
    return null;
  }
  
  public List<String> getGivenSetName()
  {
    List<String> lst = new ArrayList<String>();
    Iterator<Entry<CKey<String, String>, Pair<String, Term>>> it = map_.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<CKey<String, String>, Pair<String, Term>> pairs = 
          (Map.Entry<CKey<String, String>, Pair<String, Term>>) it.next();
      if ((pairs.getKey().getType() == CircusMapType.CMT_GIVENTYPE)) {
        lst.add(pairs.getKey().getName2());
      }
    }
    return lst;
  }

  
  public boolean clear()
  {
    map_.clear();
    return true;
  }

  public int size()
  {
    return map_.size();
  }
  
  /**
   * get the global unique number
   * @return
   */
  public int getn()
  {
    return n_;
  }
  
  /**
   *  auto increment global unique number by one
   */
  public int incn()
  {
    return n_++;
  }
}

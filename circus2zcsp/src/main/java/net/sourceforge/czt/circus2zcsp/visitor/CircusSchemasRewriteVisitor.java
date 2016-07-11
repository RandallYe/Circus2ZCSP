package net.sourceforge.czt.circus2zcsp.visitor;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.ChannelDecl;
import net.sourceforge.czt.circus.ast.ChannelPara;
import net.sourceforge.czt.circus.ast.ChannelSetPara;
import net.sourceforge.czt.circus.ast.NameSetPara;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.visitor.BasicProcessVisitor;
import net.sourceforge.czt.circus.visitor.ChannelParaVisitor;
import net.sourceforge.czt.circus.visitor.ProcessParaVisitor;
import net.sourceforge.czt.circus2zcsp.Debug;
import net.sourceforge.czt.circus2zcsp.data.Node;
import net.sourceforge.czt.circus2zcsp.util.AxParaKind;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.circus2zcsp.util.RefExprKind;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.RefExprVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;

/**
 * Rewrite the schema definitions in an original Circus program.
 * <ul>
 * <li> re-placing </li>
 *      <ul>
 *      <li> For a global schema referred in a BasicProcess, it is duplicated in the process. (might be renamed)</li>
 *      <li> For a global schema, if it is only referred in a BasicProcess, or the global reference <br> 
 *           number is 0, then remove it.</li>
 *      </ul>
 * </ul>
 *
 * @author rye
 *
 */
public class CircusSchemasRewriteVisitor
  implements
  TermVisitor<Object>,
  ZSectVisitor<Object>,
  AxParaVisitor<Object>,
  RefExprVisitor<Object>,
  ProcessParaVisitor<Object>,
  BasicProcessVisitor<Object>,
  ChannelParaVisitor<Object>
{
  private final Visitor<Object> visitor_ = this;

  private ZSect zsect_;
  
  /**
   * Current process paragraph in processing
   */
  private ProcessPara process_para_;
  
  /**
   * Current process paragraph in processing
   */
  private BasicProcess basic_process_;
  
  /**
   * a set of schema reference name in the current schema
   */
  private final Set<Node> set_id_;
  
  /**
   * 
   */
  private ZName cur_schname_ = null;
  
  /**
   * a set of axparas that are added in BasicProcess
   */
  private final List<AxPara> lst_axpara_;
  
  /**
   * A table to maintain the reference number of a schema. Each entry is composed of four columns.
   * <ul>
   * <li> Schema Name (ZName) </li>
   * <li> A set of referred schemas (Set&lt;ZName&gt;) </li>
   * <li> Global reference number (int) </li>
   * <li> Local reference number (int) </li>
   * 
   */
  private final Map<Node, Entry<Node>> ref_map_;
  
  class Entry<T> {
    private T id_;
    private Set<T> set_id_;
    private int global_ref_num_ = 0;
    private int local_ref_num_ = 0;
    
    public Entry(T id)
    {
      id_ = id;
      set_id_ = new HashSet<T>();
    }

    public Entry(T id, Set<T> set_id)
    {
      id_ = id;
      set_id_ = set_id;
    }

    public T getId()
    {
      return id_;
    }
    
    public Set<T> getSetId()
    {
      return set_id_;
    }

    public int getGlobalRefNum()
    {
      return global_ref_num_;
    }
    
    public int getLocalRefNum()
    {
      return local_ref_num_;
    }
    
    public void addARef(T id)
    {
      set_id_.add(id);
    }
    
    public void delARef(T id)
    {
      set_id_.remove(id);
    } 
    
    public void incRef(boolean global)
    {
      if(global) {
        global_ref_num_++;
      }
      else {
        local_ref_num_++;
      }      
    }
    
    public void decRef(boolean global)
    {
      if(global) {
        if(global_ref_num_ == 0) {
          Debug.debug_print(
              Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
                  Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
                  Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
                  "The global reference of " + 
          id_.toString() + " has been zero and can not reduce");

          throw new CztException("The global reference of " + 
              id_.toString() + " has been zero and can not reduce");
        }
        else {
          global_ref_num_--;
        }
      }
      else {
        if(local_ref_num_ == 0) {
          throw new CztException("The local reference of " + 
              id_.toString() + " has been zero and can not reduce");
        }

        local_ref_num_--;
      }
    }
    
  }
  
  public CircusSchemasRewriteVisitor()
  {
    ref_map_       = new TreeMap<Node, Entry<Node>>();
    set_id_        = new HashSet<Node>();
    lst_axpara_    = new ArrayList<AxPara>();
  }
  
  
  private boolean isGlobal()
  {
    return (process_para_ == null && basic_process_ == null);
  }
  
  private void addToRefMap(Node id, Set<Node> setNode) 
  {
    Set<Node> tmpSet = new HashSet<Node>();
    tmpSet.addAll(setNode);
    addToRefMap(id, new Entry<Node>(id, tmpSet));
  }
  
  private void addToRefMap(Node id, Entry<Node> entry) 
  {
    String cmd = "";
    if(getEntryByIdFromRefMap(id) != null) {
      cmd = "Update";
    }
    else {
      cmd = "Add";
    }
    
    ref_map_.put(id, entry);
   
    Debug.debug_print(
        Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
        Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
        Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
        cmd + " [" + id.toString() + "]: " + entryToString(entry));
  }
  
  private String entryToString(Entry<Node> entry)
  {
    String ret = "";
    String strSet = "[";
    
    if(entry != null) {
      for(Node n: entry.getSetId()) {
        strSet += n.toString() + " ";
      }
    }
    else {
      strSet += "null";
    }
    strSet = strSet.trim();
    strSet += "]";
    
    ret += strSet;
    ret += "<" + entry.getGlobalRefNum() + ", " + entry.getLocalRefNum() + ">";
    
    return ret;
  }
  
  private void printRefMap(Map<Node, Entry<Node>> ref_map)
  {
    for(Map.Entry<Node, Entry<Node>> entry : ref_map.entrySet()) {
      Debug.debug_print(
          Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
              Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
              Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
              "[" + entry.getKey().toString() + "]: " + entryToString(entry.getValue()));
    }
  }
  
  private Entry<Node> getEntryByIdFromRefMap(Node id)
  {
    for(Map.Entry<Node, Entry<Node>> entry : ref_map_.entrySet()) {
      if(Circus2ZCSPUtils.isEquals(entry.getKey().getName(), id.getName())) {
        return entry.getValue();
      }
    }
    
    return null;
  }
  /**
   * 
   * @param t
   * @return
   */
  protected Object visit(Term t)
  {
    if (t != null) {
      return t.accept(visitor_);
    }
    return null;
  }
    
  @Override
  public Object visitTerm(Term zedObject)
  {
    Object[] args = zedObject.getChildren();
    for (int i = 0; i < args.length; i++) {
      if (args[i] instanceof Term) {
        args[i] = ((Term) args[i]).accept(this);
      }
    }
    return null;
  }
  
  @Override
  public Object visitZSect(ZSect term)
  {
    zsect_ = term;
    for(Para p: term.getZParaList()) {
      if(p instanceof ProcessPara) {
        visit(p);
      }
      else if(p instanceof AxPara) {
        visit(p);
      }
      else if(p instanceof ChannelPara) {
        visit(p);
      }
      else if(p instanceof ChannelSetPara) {
        visit(p);
      }
      else if(p instanceof FreePara) {
        visit(p);
      }
      else if(p instanceof GivenPara) {
        visit(p);
      }
      else if(p instanceof NameSetPara) {
        visit(p);
      }
      else {
        // skip
      }
    }

    // a set of AxPara's name to be removed since their reference is 0
    Set<ZName> axParaToRemove = new HashSet<ZName>();
    TreeMap<Node, Entry<Node>> ref_map = new TreeMap<Node, Entry<Node>>();
    
    ref_map.putAll(ref_map_);
    int size = 0;
    size = ref_map.size() + 1;
    
    while(ref_map.size() > 0 && ref_map.size() < size) {
      Debug.debug_print(
          Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
          Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
          Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
          "====> Ref Map: " + ref_map.size());
      size = ref_map.size();
      ref_map_.clear();
      ref_map_.putAll(ref_map);
      for(Map.Entry<Node, Entry<Node>> entry : ref_map_.entrySet()) {
        if(entry.getValue().getGlobalRefNum() == 0) {
          // remove it
          axParaToRemove.add(entry.getKey().getName());
          // check its references
          Entry<Node> e = getEntryByIdFromRefMap(entry.getKey());
          Debug.debug_print(
              Thread.currentThread().getStackTrace()[1].getFileName() + ":" +
              Thread.currentThread().getStackTrace()[1].getMethodName() + ":" +
              Thread.currentThread().getStackTrace()[1].getLineNumber() + "  " + 
              "Decrease reference from " + entry.getKey().toString());
          for(Node n: e.getSetId()) {
            Entry<Node> e1 = getEntryByIdFromRefMap(n);
            e1.decRef(true);
            // update the reference
            addToRefMap(n, e1);
          }
          
          ref_map.remove(entry.getKey());
        }
      }
    }
    
//    printRefMap(ref_map);
    
    List<AxPara> setAxParaToRemove = new ArrayList<AxPara>();
    
    for(Para p: term.getZParaList()) {
      if(p instanceof AxPara) {
        AxParaKind kind = Circus2ZCSPUtils.getAxParaKind((AxPara)p);
        ZName name = null;
        switch(kind) {
          case ABBR:
          case GEN_ABBR:
            name = (ZName) ZUtils.getAbbreviationName((AxPara)p);
            break;
          case AXDEF:
          case GEN_AXDEF:
            break;
          case BOXED_SCHEMA:
          case HORIZON_SCHEMA:
          case GEN_BOXED_SCHEMA:
          case GEN_HORIZON_SCHEMA:
            name = (ZName) ZUtils.getSchemaName((AxPara)p);
            break;
          default:
              break;
        }
        
        if(name != null) {
          for(ZName n: axParaToRemove) {
            if(Circus2ZCSPUtils.isEquals(name, n)) {
              setAxParaToRemove.add((AxPara) p);
            }
          }
        }
      }
    }
    
    term.getZParaList().removeAll(setAxParaToRemove);
    
    zsect_ = null;
    return null;
  }

  /**
   * Get a global AxPara by its name
   * @param apname
   * @return
   */
  private AxPara getAGlobalAxPara(ZName apname)
  {
    for(Para p: zsect_.getZParaList()) {
      if(p instanceof AxPara) {
        AxParaKind kind = Circus2ZCSPUtils.getAxParaKind((AxPara) p);
        switch(kind) {
          case ABBR:
          case GEN_ABBR:
            ZName name = (ZName) ZUtils.getAbbreviationName((AxPara) p);
            if(Circus2ZCSPUtils.isEquals(apname, name)) {
              return (AxPara)p;
            }
            break;
          case AXDEF:
          case GEN_AXDEF:
            break;
          case BOXED_SCHEMA:
          case HORIZON_SCHEMA:
          case GEN_BOXED_SCHEMA:
          case GEN_HORIZON_SCHEMA:
            name = (ZName) ZUtils.getSchemaName((AxPara) p);
            if(Circus2ZCSPUtils.isEquals(apname, name)) {
              return (AxPara)p;
            }
            break;
          default:
              break;
        }
      }
    }
    
    return null;
  }
  
  /**
   * 
   * @param e - the entry for global schema/abbr
   */
  private void addSchemasIntoLocalProcess(Entry<Node> e, List<AxPara> lstAP)
  {
    List<AxPara> lstTempAP = new ArrayList<AxPara>();
    
    AxPara ap = getAGlobalAxPara(e.getId().getName());
    if(ap != null) {
      Set<Node> setNode = e.getSetId();
      for(Node n: setNode) {
        Entry<Node> entry = getEntryByIdFromRefMap(n);
        if(entry != null) {
          addSchemasIntoLocalProcess(entry, lstTempAP);
        }
      }
      // the one to be found is in the end
      if(!lstTempAP.contains(ap) && !lstAP.contains(ap))  {
        lstTempAP.add(ap);
      }
      
      for(AxPara p: lstTempAP) {
        if(!lstAP.contains(p)) {
          lstAP.add(p);
        }
      }
    }
  }
  
  @Override
  public Object visitRefExpr(RefExpr term)
  {
    ZExprList zel = term.getZExprList();
    ZName name = ZUtils.cloneTerm(term.getZName());
    
    // for reference, just remove prefixing Delta or Xi
    if(ZUtils.isDeltaXi(name)) {
      name.setWord(name.getWord().replace(ZString.DELTA, "").replace(ZString.XI, ""));
    }
    
    Node id = new Node(name, (ZName)null);
    Entry<Node> e = getEntryByIdFromRefMap(id);
    if(e != null) {
      if(!set_id_.contains(id)) {
        // found and it is a reference to a global schema
        if(isGlobal()) {
          e.incRef(true);
        }
        else {
          e.incRef(false);
        }
        // update the reference
        addToRefMap(id, e);
        
        set_id_.add(id/*new Node(name, cur_schname_)*/);
      }
      else {
        // but if there has been a same reference in the set_id_, just ignore
        // since the same references in one schema are also taken as one reference.
      }
      
      // if local process, we copy this referred schema into this process, and also other schemas referred by this schema 
      if(!isGlobal()) {
        List<AxPara> lstAp = new ArrayList<AxPara>();
        addSchemasIntoLocalProcess(e, lstAp);
        for(AxPara p: lstAp) {
          if(!lst_axpara_.contains(p)) {
            lst_axpara_.add(p);
          }
        }
      }
    }
    
    RefExprKind kind = Circus2ZCSPUtils.getRefExprKind(term);
    switch(kind) {
      case GEN_OP_APPL:
        visit(zel);
        break;
      case OP_APPL:
        break;
      case GEN_REF:
        visit(zel);
        break;
      case REF:
        break;
      default:
        throw new CztException("Unknown RefExpr kind");
    }
    
    return null;
  }

  @Override
  public Object visitAxPara(AxPara term)
  {
    // formals are ignored since they will not include a reference to a schema
    AxParaKind kind = Circus2ZCSPUtils.getAxParaKind(term);
    switch(kind) {
      case ABBR:
      case GEN_ABBR:
        ZName name = (ZName) ZUtils.getAbbreviationName(term);

        if(isGlobal()) {
          set_id_.clear();
          cur_schname_ = name;
          visit(ZUtils.getAbbreviationExpr(term));
          
          Node id = new Node(name, (ZName)null);
          // if this Abbr doesn't refer to other global schemas, don't duplicate it within a process
          // since it might be very simple definiton like P == 0..3
          if(!set_id_.isEmpty()) {
            addToRefMap(id, set_id_);
          }
        }
        else {
          visit(ZUtils.getAbbreviationExpr(term));
        }
        break;
      case AXDEF:
      case GEN_AXDEF:
        visit(ZUtils.getAxBoxDecls(term));
        visit(ZUtils.getAxBoxPred(term));
        break;
      case BOXED_SCHEMA:
      case HORIZON_SCHEMA:
        name = (ZName) ZUtils.getSchemaName(term);

        if(isGlobal()) {
          set_id_.clear();
          cur_schname_ = name;
          visit(ZUtils.getSchemaDefExpr(term));
          
          Node id = new Node(name, (ZName)null);
          
          addToRefMap(id, set_id_);
        }
        else {
          visit(ZUtils.getSchemaDefExpr(term));
        }
        break;
      case GEN_BOXED_SCHEMA:
      case GEN_HORIZON_SCHEMA:
        name = (ZName) ZUtils.getSchemaName(term);

        if(isGlobal()) {
          set_id_.clear();
          cur_schname_ = name;
          visit(ZUtils.getSchemaDefExpr(term));
          
          Node id = new Node(name, (ZName)null);
          addToRefMap(id, set_id_);
        }
        else {
          visit(ZUtils.getSchemaDefExpr(term));
        }
        break;
      default:
          break;
    }
    return null;
  }

  @Override
  public Object visitProcessPara(ProcessPara term)
  {
    process_para_ = term;
    // 
    
    visit(term.getCircusProcess());
    //
    process_para_ = null;
    return null;
  }


  @Override
  public Object visitBasicProcess(BasicProcess term)
  {
    basic_process_ = term;
    lst_axpara_.clear();
    
    for(Para p: term.getZParaList()) {
      visit(p);
    }
    
    if(!lst_axpara_.isEmpty()) {
      List<AxPara> lstAxpara = new ArrayList<AxPara>();
      
      for(Para p: zsect_.getZParaList()) {
        if(p instanceof AxPara) {
          if(lst_axpara_.contains(p)) {
            lstAxpara.add((AxPara) ZUtils.cloneTerm(p));
          }
        }
      }
      
      // sort lst_axpara_ according to their order in ZSect
      term.getZParaList().addAll(0, lstAxpara);
    }
    
    basic_process_ = null;
    return null;
  }


  @Override
  public Object visitChannelPara(ChannelPara term)
  {
    for(Decl decl: term.getZDeclList()) {
      if(decl instanceof ChannelDecl) {
        set_id_.clear();
        visit(((ChannelDecl)decl).getExpr());
        for(Name name: ((ChannelDecl)decl).getZChannelNameList()) {
          cur_schname_ = (ZName) name;
          
          Node id = new Node((ZName) name, (ZName)null);
          if(!set_id_.isEmpty()) {
            addToRefMap(id, set_id_);
            // for channel, we add it by one automatically and so won't remove it
            Entry<Node> e = getEntryByIdFromRefMap(id);
            if(e != null) {
              e.incRef(true);
            }
          }
        }
      }
    }
    return null;
  }

}

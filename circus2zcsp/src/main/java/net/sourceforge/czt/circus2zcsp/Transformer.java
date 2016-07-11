
package net.sourceforge.czt.circus2zcsp;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import net.sourceforge.czt.circus.ast.BasicProcess;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus2zcsp.ast.CSPSpec;
import net.sourceforge.czt.circus2zcsp.data.CircusSpecMap;
import net.sourceforge.czt.circus2zcsp.data.Node;
import net.sourceforge.czt.circus2zcsp.util.Circus2ZCSPUtils;
import net.sourceforge.czt.circus2zcsp.visitor.CircusRewriteVisitor;
import net.sourceforge.czt.circus2zcsp.visitor.CircusSchemasAsPredicateVisitor;
import net.sourceforge.czt.circus2zcsp.visitor.CircusSchemasRewriteVisitor;
import net.sourceforge.czt.circus2zcsp.visitor.CircusToCSPVisitor;
import net.sourceforge.czt.circus2zcsp.visitor.DefinitionReferencesMapVisitor;
import net.sourceforge.czt.circus2zcsp.visitor.SchExprRenameExprVisitor;
import net.sourceforge.czt.circus2zcsp.visitor.ZNameSetVisitor;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionInfoException;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.NameSectTypeTriple;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Parent;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZFactory;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.Version;
import net.sourceforge.czt.z.util.ZString;

/**
 * Transform Circus specification to Z and CSP
 * 
 * @author rye
 */
public class Transformer
{
  private SectionManager manager_;

  private ZFactory fac_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();

  private ZSect circusSect_ = null;
  
  /* spec for resultant Z*/
  private Spec spec_;
  private ZParaList paraList_;
  private ZSect zsect_;
  
  /* for resultant CSP spec */
  final private CSPSpec cspspec_ = new CSPSpec();

  // a map from original variable or schema name to replaced new name
  // private Map<String, String> map_ = null;
  private CircusSpecMap map_ = new CircusSpecMap();

//  private List<String> sections_added_ = new ArrayList<String>();
  
  private Map<String, ZParaList> sections_paralist_map_ = new HashMap<String, ZParaList>();
//  private Map<String, Set<String>> sections_deps_map_ = new HashMap<String, Set<String>>();
  
  private Stack<String> sections_stack_ = new Stack<String>();
  
  final List<String> lst_standard_toolkits_ = Arrays.asList (
      "standard_toolkit", "number_toolkit", "set_toolkit",
      "relation_toolkit",  "function_toolkit",   "sequence_toolkit",  "circus_toolkit"
  );

  private void createSpec()
  {
//    orig_spec_ = fac_.createSpec();
//    orig_spec_.setVersion(Version.ZML_VERSION);
    
    spec_ = fac_.createSpec();
    spec_.setVersion(Version.ZML_VERSION);
    paraList_ = fac_.createZParaList();
  }

  public Transformer(SectionManager manager, String name)
  {
    manager_ = manager;
    if (manager_.getDialect() != Dialect.CIRCUS) {
      Debug.debug_print("This is not a CIRCUS manager");
    }

    createSpec();

    Spec spec;
    try {
      spec = manager_.get(new Key<Spec>(name, Spec.class));
    }
    catch (SectionInfoException e) {
      throw new CztException("Fail to get the spec [" + name + "]. \n\t\t" + 
          e.getMessage());
    }
    catch (CommandException e) {
      throw new CztException("Fail to get the spec [" + name + "]. \n\t\t" + 
          e.getMessage());
    }
    
    CircusRewriteVisitor crtv = new CircusRewriteVisitor(map_, manager_, cspspec_);

    int nrOfZSect = 0;
    String sectionName = "";
    for (Sect sect : spec.getSect()) {
      // If the section is a ZSection
      if (sect instanceof ZSect) {
        nrOfZSect++;
        if(nrOfZSect > 1) {
          throw new CztException(name + " has " + spec.getSect().size() + 
              " sections. We only support one now!");
        }
        
        ZSect zs = (ZSect) sect;
        circusSect_ = zs;
        sectionName = zs.getName();

        // type check it
        try {
          manager_.get(new Key<SectTypeEnvAnn>(sectionName, SectTypeEnvAnn.class));
        }
        catch (SectionInfoException e) {
          throw new CztException("Type check the section [" + sectionName + "] Error. \n\t\t" + 
              e.getMessage());
        }
        catch (CommandException e) {
          throw new CztException("Type check the section [" + sectionName + "] Error. \n\t\t" + 
              e.getMessage());
        }
        
/*        try {
          SectTypeEnvAnn ann = 
              manager_.get(new Key<SectTypeEnvAnn>(zs.getName(), SectTypeEnvAnn.class));
          for (NameSectTypeTriple p: ann.getNameSectTypeTriple()) {
            Debug.debug_print("(" + Circus2ZCSPUtils.termToString(p.getName()) + 
                ", " + (p.getSect()) + 
                ", " + Circus2ZCSPUtils.termToString(p.getType()));
          }
        }
        catch (SectionInfoException e) {
          e.printStackTrace();
        }
        catch (CommandException e) {
          e.printStackTrace();
        }
*/        
        ///////////////////////////////////////////////////////////////////////
        // Load all parent sections into this section
        ///////////////////////////////////////////////////////////////////////
        getItsParentSections(manager_, zs);
        
        // assemble new section
        assembleZSections(zs);
        ///////////////////////////////////////////////////////////////////////
        // Check Identifiers follow [a-zA-Z][a-zA-Z0-9_][’!?]
        ///////////////////////////////////////////////////////////////////////
        ZNameSetVisitor znsv = new ZNameSetVisitor();
        zs.accept(znsv);
        Set<String> setName = znsv.getStrSet();
        boolean match_all = true;
        // setName can be like "[r′, Write, ΔState, x?, out, P, Init, Temp, T, 
        // ℕ, CellWrite, X, Record, write, read, in,  _ .. _ , r, Read↗1↙, 
        // $$mainAction_L22C12, State, v, x, y, Init↘1↖, v′]"
        for(String s: setName) {
          if(s.startsWith(ZString.DELTA) || s.startsWith(ZString.XI) || 
              s.endsWith("?") || s.endsWith("!") || s.endsWith("′")) {
            continue;
          }
          else if(s.matches("^[a-zA-Z].*$")) {
            // for a name that starts with a letter, it must follow our restriction.
            Pattern regex = Pattern.compile("^[a-zA-Z][a-zA-Z0-9_]*$");
            Matcher matcher = regex.matcher(s);
            if(!matcher.matches()) {
              match_all = false;
              System.err.printf("[ERROR] Name: %s is not allowed!\n", s);
            }
          }
          else {
            // others
//            Debug.debug_format_print("Not a name: %s to be checked!", s);
          }
        }
        
        if(!match_all) {
          throw new CztException("Not all names are allowed. Please check and correct them first!");
        }
        
        // rewrite schemas that are used in CSP
        // only schema as declaration or predicate are supported in CSP now
//        CircusSchemasAsPredicateVisitor csapv = new CircusSchemasAsPredicateVisitor(manager_);
//        zs.accept(csapv);
        
        // localisation of schemas
        CircusSchemasRewriteVisitor csrv = new CircusSchemasRewriteVisitor();
        zs.accept(csrv);
        
        ///////////////////////////////////////////////////////////////////////
        // rewrite
        ///////////////////////////////////////////////////////////////////////
        // stage 1.
        zs.accept(crtv);
        
        // rewrite schemas that are used in CSP
        // schema as predicate in CSP is rewritten now
        CircusSchemasAsPredicateVisitor csapv = new CircusSchemasAsPredicateVisitor(manager_);
        zs.accept(csapv);
        
        // stage 2. 
        crtv.setRewriteStage(2);
        crtv.setSectName(sectionName);
        
        for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
          if (para instanceof ProcessPara) {
            if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
              ((ProcessPara)para).accept(crtv);
            }
          }
        }
        
        // stage 3. 
        crtv.setRewriteStage(3);
        for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
          if (para instanceof ProcessPara) {
            if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
              ((ProcessPara)para).accept(crtv);
            }
          }
        }
        
        // stage 4. 
        crtv.setRewriteStage(4);
        for (net.sourceforge.czt.z.ast.Para para : zs.getZParaList()) {
          if (para instanceof ProcessPara) {
            if(((ProcessPara)para).getCircusProcess() instanceof BasicProcess) {
              ((ProcessPara)para).accept(crtv);
              String st = Circus2ZCSPUtils.termToString(((ProcessPara)para).getCircusProcess());
            }
          }
        }
        
        zs.accept(new SchExprRenameExprVisitor(map_));
        
        ///////////////////////////////////////////////////////////////////////
        // \Omega_1
        ///////////////////////////////////////////////////////////////////////
        StateMergeOmega1 smo1 = new StateMergeOmega1(zs, crtv.getCircusSpecMap(), manager_, crtv.getInitPredSet());
        zsect_ = smo1.getZSect();
        zsect_.setName(sectionName);
        spec_.getSect().add(zsect_);
        
        // get all references in this rewritten circus program
        DefinitionReferencesMapVisitor drmv = new DefinitionReferencesMapVisitor(crtv.getCircusSpecMap(), manager_, sectionName);
        zs.accept(drmv);

        Map<Node, Set<Node>> refmap = drmv.getRefMap();
        
        ///////////////////////////////////////////////////////////////////////
        // \Phi
        ///////////////////////////////////////////////////////////////////////
        CircusToCSPVisitor ctcv = new CircusToCSPVisitor(crtv.getCircusSpecMap(), cspspec_, manager_, refmap);
        zs.accept(ctcv);
      }
    }
  }

  public Spec getSpec()
  {
    return spec_;
  }

  public CSPSpec getCSPSpec()
  {
    return cspspec_;
  }
  
  public ZSect getZSectOfCircus()
  {
    return circusSect_;
  }
  
  /**
   * 
   * @param manager
   * @param zs
   */
  public void getItsParentSections(SectionManager manager, ZSect zs) {
    
    Set<String> parentSects = new HashSet<String>();
    for(Parent p: zs.getParent()) {
      // not a standard toolkit
      if(!lst_standard_toolkits_.contains(p.getWord())) {
        parentSects.add(p.getWord());
      }
    }
    
    // only have standard toolkits
    if(parentSects.isEmpty()) {
      sections_stack_.add(0, zs.getName());
      sections_paralist_map_.put(zs.getName(), zs.getZParaList());
    }
    else if(sections_stack_.containsAll(parentSects)) {
      sections_stack_.push(zs.getName());
      sections_paralist_map_.put(zs.getName(), zs.getZParaList());
    }
    
    for(String p: parentSects) {
      if(sections_stack_.contains(p)) {
        continue;
      }
      
      String path = manager.getProperty("czt.path");
      if(path == null) {
        path = "~/tmp/";
      }
      else if(path.startsWith("file:")) {
        path = path.substring(5);
      }
      path += "/" + p;
      
      String pathExt = path + ".tex";
      
      File file = new File(pathExt);
      
      /**
       * Check if the file specified exists
       */
      if(!file.exists() || file.isDirectory()) {
        pathExt = path + ".zed";
        file = new File(pathExt);
        if(!file.exists() || file.isDirectory()) {
          System.err.printf("[ERROR] File: %s does not exist!\n", path);
          System.exit(1);
        }
      }
      
      FileSource source = new FileSource(pathExt);
      source.setMarkup(Markup.LATEX);
      source.setEncoding("Default");

      SectionManager manager1 = new SectionManager(Dialect.CIRCUS);
      manager1.setProperty("czt.path", file.getParent());
      String name = "spec";
      manager1.put(new Key<Source>(name, Source.class), source);
      
      Spec spec;
      try {
        spec = manager1.get(new Key<Spec>(name, Spec.class));
      }
      catch (SectionInfoException e) {
        throw new CztException("Fail to get the spec [" + name + "]. \n\t\t" + 
            e.getMessage());
      }
      catch (CommandException e) {
        throw new CztException("Fail to get the spec [" + name + "]. \n\t\t" + 
            e.getMessage());
      }
      
      ZSect zs1 = null;
      for(Sect s: spec.getSect()) {
        if(s instanceof ZSect) {
          zs1 = (ZSect)s;
        }
      }
      
      if(zs1 != null) {
        getItsParentSections(manager1, zs1);
      }
      
      sections_paralist_map_.put(p, zs1.getZParaList());
      // add in the beginning
//      zs.getZParaList().addAll(0, zs1.getZParaList());
//      sections_added_.add(p.getWord());
      
//      ZParaList paraList = fac_.createZParaList();
//      paraList.addAll(zs1.getZParaList());
//      
//      // remove duplicate
//      for(Para p1: zs1.getZParaList()) {
//        for(Para pp: zs.getZParaList()) {
//          if(p1.equals(pp)) {
//            paraList.remove(p1);
//          }
//        }
//      }
//      
//      zs.getZParaList().addAll(0, paraList);
    }
    
    if(!sections_stack_.contains(zs.getName())) {
      sections_stack_.push(zs.getName());
      sections_paralist_map_.put(zs.getName(), zs.getZParaList());
    }
  }
  
  private void assembleZSections(ZSect sect)
  {
    ZParaList paralist = fac_.createZParaList();
    for(String p: sections_stack_) {
      paralist.addAll(sections_paralist_map_.get(p));
    }
    
    sect.setParaList(paralist);
  }
}

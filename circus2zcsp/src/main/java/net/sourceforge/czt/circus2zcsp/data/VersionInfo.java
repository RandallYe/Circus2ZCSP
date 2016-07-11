
package net.sourceforge.czt.circus2zcsp.data;

import java.util.HashMap;
import java.util.Map;

public class VersionInfo
{
  /**
   * Strategies
   */
  final static private String VERSION_0_1 = "0.1";

  final static private String TESTVERSION_0_1_1 = "0.1_B1";
  
  final static private String VERSION_0_2 = "0.2";
  
  final static private String VERSION_0_3 = "0.3";
  
  /**
   * Current version
   */
  final static public String CUR_VERSION = VERSION_0_3;

  final static private int MAX_WIDTH = 80;

  /**
   * a map from version to its release note
   */
  private static final Map<String, String> version_ = new HashMap<String, String>()
  {
    /**
     * 
     */
    private static final long serialVersionUID = 10L;

    {
      put(VERSION_0_3, "This is the third release built on June 30th, 2016. "
          + "It is capable of translating all constructs in the reactive buffer, "
          + "the steam boiler cases, and the ESEL case.\n"
          + "-------------------------------------- New ------------------------------------\n"
          + "------------------------------------- Fixed -----------------------------------\n"
          + "------------------------------------ Changed ----------------------------------\n"
          + "1. Check if a schema that corresponding a schema expression as action shall be \n"
          + "   an operational schema. \n"
          + "----------------------------------- Limitations -------------------------------\n"
          + "1. External choice of actions are only available to \"prefixed\" actions "
          + "(such as basic actions, prefixing, guarded commands), and compound CSP actions"
          + " of these \"prefixed\" actions. \n"
          + "2. Parallel composition and interleaving for actions are not supported if "
          + "both actions share variables in scope.\n"
          + "3. Operator template is not supported.\n" //  due to lack of support of generic definition in ProB
          + "4. Reflexive-transitive closure (*) is not supported.\n"
          );
      
      put(VERSION_0_2, "This is the second release built on May 13th, 2016. "
          + "It is capable of translating all constructs in the reactive buffer, "
          + "the steam boiler cases, and the ESEL case.\n"
          + "-------------------------------------- New ------------------------------------\n"
          + "1. Add support of iterated parallel and interleaving of actions for the case if their actions have disjoint variables in scope\n"
          + "2. Add support of iterated parallel of processes\n"
          + "------------------------------------- Fixed -----------------------------------\n"
          + "1. Add parenthesis around translated freetype constructor d~1: d.1 => (d.1) in csp\n"
          + "2. The problem that freetype is not translated to CSP though this type is used in the behavioural part\n"
          + "------------------------------------ Changed ----------------------------------\n"
          + "1. The processing of u'=u (u - variables not in frame) in schema expression as action\n"
          + "    1.1 if v' is included in its declaration part, then this v is regarded in frame\n"
          + "    1.2 if v' is nto included in its declaration part (though v might be included), then this v is regarded not in frame\n"
          + "2. The logic to include parent sections\n"
          + "    2.1 use a stack to keep dependency order of all sections\n"
          + "    2.2 assemble all sections into a big section according to their dependency order\n"
          + "----------------------------------- Limitations -------------------------------\n"
          + "1. External choice of actions are only available to \"prefixed\" actions "
          + "(such as basic actions, prefixing, guarded commands), and compound CSP actions"
          + " of these \"prefixed\" actions. \n"
          + "2. Parallel composition and interleaving for actions are not supported if "
          + "both actions share variables in scope.\n"
          + "3. Operator template is not supported.\n" //  due to lack of support of generic definition in ProB
          + "4. Reflexive-transitive closure (*) is not supported.\n"
          );
      
      put(VERSION_0_1, "This is the first release built on March 15th, 2016. \n"
          + "It is capable of translating all constructs in the reactive buffer \n"
          + "and the steam boiler cases.\n"
          + "Limitations:\n"
          + "    1. External choice of actions are only available to \"prefixed\" actions "
          + "(such as basic actions, prefixing, guarded commands), and compound CSP actions"
          + " of these \"prefixed\" actions. \n"
          + "    2. Parallel composition and interleaving for actions are not supported if "
          + "both actions share variables in scope.\n"
          + "    3. Operator template is not supported.\n" //  due to lack of support of generic definition in ProB
          + "    4. Reflexive-transitive closure (*) is not supported.\n"
          ); 
      
//      put(TESTVERSION_0_1_1, "This is a test version. \nIt is capable of translating "
//          + "all constructs in the reactive buffer and the steam boiler cases.");
      
    }
  };

  static public String getCurrentRelease()
  {
    return version_.get(CUR_VERSION);
  }

  static public Map<String, String> getAllReleases()
  {
    return version_;
  }

  static public String wrap(String longInput)
  {
    String result = "";
    
    String[] splittedString = longInput.split("\n");
    
    for(String s: splittedString) {
      if(s.length() <= MAX_WIDTH) {
        result += s + "\n";
      }
      else {
        while(s.length() > MAX_WIDTH) {
          result += s.substring(0, MAX_WIDTH) + "\n";
          s = s.substring(MAX_WIDTH);
        }
        result += s + "\n";
      }
    }
    
    return result;
  }
}

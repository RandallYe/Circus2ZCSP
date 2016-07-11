package net.sourceforge.czt.circus2zcsp.conf;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

import net.sourceforge.czt.circus2zcsp.Debug;
import net.sourceforge.czt.util.CztException;

public class Config
{
  public static final String CONF_MININT = "CONF_MININT";
  
  public static final String CONF_MAXINT = "CONF_MAXINT";
  
  public static final String CONF_MAXINS = "CONF_MAXINS";
  
  public static final String CSPLIBSPATH = "CSPLIBSPATH";
  /**
   * How many instantiations when converting given set in Circus to CSP
   */
  public static final String CONF_GIVEN_SET_INST_NO = "CONF_GIVEN_SET_INST_NO";
  
  public static final String file_name_ = "config.properties";
  private final Properties prop_ = new Properties();
  
  /**
   * constructor of Config, if filename is given, then Config will load all properties from this file instead
   * of default "config.properties" in class path
   * @param filename
   */
  public Config(String filename)
  {
    InputStream in = null;
    
    try {
      // first check input filename
      if(filename != null) {
        try{
          in = new FileInputStream(filename);
        }
        catch (FileNotFoundException e) {
          Debug.debug_print("File [" + filename + "] can not be found and will use default " + file_name_ +"!" );
          in = null;
        }
      }      
      
      // if not possible, then use default file under class path 
      if(in == null) {
        in = getClass().getClassLoader().getResourceAsStream(file_name_);
        if (in == null) {
          throw new CztException("Can not find configuration file [" + file_name_ + "]!");
        }
      }
      prop_.load(in);
    } 
    catch (IOException ex) {
      throw new CztException("IOException to load configuration file:" + ex.getMessage());      
    } 
    finally {
      if (in != null) {
        try {
          in.close();
        }
        catch (IOException e) {
          e.printStackTrace();
        }
      }
    }
  }
  
  /**
   * get the configuration value by its key
   * @param key
   * @return
   *    null if not found
   */
  public String getConfig(String key) 
  {
    String str = prop_.getProperty(key.trim());
    if(str != null) {
      str = str.trim();
    }
    return str;
  }
}

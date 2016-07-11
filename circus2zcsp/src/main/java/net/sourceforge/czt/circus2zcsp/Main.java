/*
 * 
 */
package net.sourceforge.czt.circus2zcsp;

import java.io.File;
import java.io.PrintWriter;
import java.util.Map;
import java.util.logging.FileHandler;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.UnrecognizedOptionException;

import net.sourceforge.czt.circus2zcsp.data.VersionInfo;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;

/**
 * Translate a Z specification from ZML format into B format.
 * It takes a file spec.xml and produces a file spec.mch.
 */
public class Main
{
  @SuppressWarnings("unused")
  public static void main(String[] args)
  {
    Options opt = new Options();
    opt.addOption("d", "verbose", false, "run in debug mode");
    opt.addOption("v", "version", false, "show version");
    opt.addOption("V", "Versions", false, "show detailed versions information");
    CommandLineParser parser = new DefaultParser();
    
    try {
      // set up our debug log.
      Handler handler = new FileHandler("circus2zcsp.log");
      handler.setLevel(Level.ALL);
      handler.setEncoding("utf8");
      Logger.getLogger("").addHandler(handler);
      Logger circus2zcspLogger = Logger.getLogger("net.sourceforge.czt.circus2zcsp");
      circus2zcspLogger.setLevel(Level.FINEST);

      CommandLine cmd = parser.parse(opt, args);
      
      if(cmd.hasOption("v")) {
        System.out.println("Current Circus2ZCSP version: " + VersionInfo.CUR_VERSION);
        System.exit(1);
      }
      
      if(cmd.hasOption("V")) {
        System.out.println("Current Circus2ZCSP version: " + VersionInfo.CUR_VERSION);
        Map<String, String> map = VersionInfo.getAllReleases();
        
        System.out.println();
        for (Map.Entry<String, String> entry : map.entrySet()) {
            System.out.println("==> " + entry.getKey());
            System.out.println(VersionInfo.wrap(entry.getValue()));
        }
        System.exit(1);
      }
      
      if(cmd.hasOption("d")) {
      }
      else {
        Debug.turnOffDebug();
      }
      
      String files[] = cmd.getArgs();
      
      if(files.length < 1)
      {
        PrintWriter pwriter = new PrintWriter(System.err);
        String header = 
            "\n" +
            "Circus2ZCSP is a translator to link one (or more) Circus specification to " +
            "its corresponding model in Z || CSP, which is sequentially model-checked by ProB.\n" +
            "Options:";
        String footer = "For any problems, please contac <ky582@york.ac.uk> or <ye.randall@gmail.com>";
        // automatically generate the help statement
        HelpFormatter formatter = new HelpFormatter();
        formatter.printHelp(pwriter, 80, "java -jar circus2zcsp.jar spec.tex [spec1.tex [...]]", 
            header, opt, 4, 5, footer, true);
        pwriter.flush();
        System.exit(1);
      }
      
      for(String input: files) {
        Debug.debug_format_print("Reading spec: %s", input);
        
        File file = new File(input);
        
        /**
         * Check if the file specified exists
         */
        if(!file.exists() || file.isDirectory()) {
      	  System.err.printf("[ERROR] File: %s does not exist!\n", input);
            System.exit(1);
        }
        
        FileSource source = new FileSource(input);
        source.setMarkup(Markup.LATEX);
        source.setEncoding("Default");
  
        SectionManager manager = new SectionManager(Dialect.CIRCUS);
        
        String cztpath = file.getParent();

        if(file.getParent() == null) {
          cztpath = System.getProperty("user.dir");
        }

        Debug.debug_print("czt.path is set to \'" + cztpath + "\'");
        manager.setProperty("czt.path", cztpath);
        String name = "spec";
        manager.put(new Key<Source>(name, Source.class), source);
  
        Circus2ZCSP c2z = new Circus2ZCSP(manager, name);
      }
    }
    catch (UnrecognizedOptionException e) {
      System.err.println(e.getMessage());
    }
    catch (Exception e) {
      System.err.println("[ERROR] " + e);
      System.err.println("");
      if (Debug.isDebugMode()) {
        System.err.println("For debugging purposes, here is a stack trace:");
        e.printStackTrace();
      }
    }
  }
}

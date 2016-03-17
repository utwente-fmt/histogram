/* editor settings
 -*- tab-width:2 ; indent-tabs-mode:nil -*-
 */
/***********************************************************************
Copyright (c) 2011, IT University of Copenhagen and Joseph Kiniry and
Regulated Software Research Group at Dundalk Institute of Technology and
Lero and Stefan Blom.

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:

1. Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.

3. Neither the name of the copyright holders nor the names of its
   contributors may be used to endorse or promote products derived from
   this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF
THE POSSIBILITY OF SUCH DAMAGE.
************************************************************************/

package root;
/**
 * This class deals with the command line options of the histogram application.
 * It provides option parsing, pretty printing and queries.
 */
import java.io.StringWriter;
import java.io.PrintWriter;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.OptionBuilder;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.apache.commons.cli.PosixParser;

public final class CommandLineOptions {
  
  /**
   * The options for histogram.
   */
  private static final Options options;
  static {
    options = new Options();
    options.addOption("h", false, "brief help information");
    options.addOption("help", false, "extended help");
    OptionBuilder.withDescription( "write the output to the given file" );
    OptionBuilder.hasArg();
    OptionBuilder.withArgName("file.csv");
    options.addOption(OptionBuilder.create("output"));
    options.addOption("class_use", false, 
                      "count references to classes (the default is to count references to methods)");    
  }
  
  /**
   * Remember the result of parsing a command line.
   */
  private static CommandLine line = null;
  
  /**
   * Process the given command line.
   * 
   * This method attempts to parse the given command line,
   * print help messages if requested and
   * checks for the correct formatting of the command line.
   * 
   * @param args the command-line arguments.
   * @return The exit status of option processing: 0, in case of no problems;
   * 1 in case of an error that has been dealt with and
   * 2 in case of an unexpected error.
   */
  public static int processOptions(final String[] args) {
    final CommandLineParser parser = new PosixParser();
    try {
      line = parser.parse(options, args);
    } catch (ParseException pe) {
      System.err.println(pe);
      usage();
      return 2;
    }
    if (line.hasOption("help")) {
      extendedHelp();
      return 1;     
    }
    if (line.hasOption("h")) {
      help();
      return 1;     
    }
    if (line.getArgs().length==0) {
      usage();
      return 1;
    }
    return 0;
  }
  
  /**
   * Print the full set of command-line switches and their brief summaries.
   */
  public static void switches() {
    HelpFormatter fmt=new HelpFormatter();
    StringWriter sw=new StringWriter();
    PrintWriter pw=new PrintWriter(sw);
    fmt.printOptions(pw,80,options,4,8);
    TextIo.message(sw.toString());
  }
  
  /**
   * Get the command line argument remaining after options have been removed.
   * @return The non-option arguments parsed.
   */
  public static String[] getArgs(){
    return line.getArgs();
  }
  
  /**
   * Get the name of the file to which output must be sent.
   * @return A file name, or null if the output is to standard out.
   */
  public static String outputName(){
    String name=null;
    if (line.hasOption("output")) {
      name=line.getOptionValue("output");
      if (name.equals("-"))
        name=null;
    }
    return name;
  }
  
  /**
   * Check if option for class use histogram has been set.
   * @return true if class use histogram must be generated, false if method use histogram must be generated
   */
  public static boolean classUse(){
    return line.hasOption("class_use");
  }

  
  public static final String bugs_message =
    "Report bugs to <charter-tools-bugs@googlegroups.com>";
  
  /**
   * Print bug report message.
   */
  public static void bugs() {
    TextIo.message(bugs_message);
  }

  public static final String example_message =
    "Examples: histogram rt.jar";
  
  /**
   * Print example use.
   */
  public static void example() {
    TextIo.message(example_message);
  }

  /**
   * Print extended help message.
   */
  public static void extendedHelp() {
    usage();
    example();
    switches();
    input();
    bugs();
  }
  
  public static final String help_info_message =
    "Try `histogram -help' for more information.";
  
  /**
   * Print brief help information.
   */
  public static void help() {
    TextIo.message(help_info_message);
  }

  public static final String input_message =
    "With no FILE, a usage message is printed.  When FILE is -,\n" + 
    "read standard input.  If multiple FILEs given, process all FILEs.\n" +
    "Exit status is 0 if at least one FILE is successfully processed,\n" +
    "1 if no FILEs were provided, and 2 if trouble.";
  
  /**
   * Print input characterization.
   */
  public static void input() {
    TextIo.message(input_message);
  }
  
  public static final String usage_message =
    "Usage: histogram [[-help|-h] |  [-output OUTPUT_FILE] [-class_use] FILE [FILE ...]]";
  
  /**
   * Print the usage message.
   */
  public static void usage() {
    TextIo.message(usage_message);
  }

  public static final String summary_message =
    "Count the number of times each method is used in the " +
    "body of one or more classes.";
  
  /**
   * Print tool summary.
   */
  public static void summary() {
    TextIo.message(summary_message);
  }

}


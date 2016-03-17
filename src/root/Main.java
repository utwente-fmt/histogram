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

import java.io.File;
import java.io.FileOutputStream;
import java.io.PrintStream;

import util.HashMapHistogram;
import util.Histogram;

/**
 * The main class of this system.
 * @author Joe Kiniry
 * @version 25-03-2001
 */
public final class Main {
  public static boolean recursive_option;
  public static boolean method_option;
  public static boolean class_option;
  public static Histogram class_histogram[];
  public static Histogram method_histogram[];
  public static int exit_status = 0;

 
  /** This class is not meant to be instantiated. */
  private Main() {
    assert false;
    //@ assert false;
  }
  
  /**
   * Perform analysis according to the command-line arguments.
   */
  public static void perform_analysis() {
    final String[] inputs = CommandLineOptions.getArgs();
    TextIo.error("Histogram analysis"); // NOPMD
    class_histogram=new Histogram[inputs.length];
    method_histogram=new Histogram[inputs.length];
    for (int i=0; i<inputs.length;i++) {
      TextIo.error("Processing " + inputs[i]); // NOPMD
      class_histogram[i] = new HashMapHistogram();
      method_histogram[i] = new HashMapHistogram();
      FileIo.find(new File(inputs[i]), class_histogram[i], method_histogram[i]);
    }
  }
  
  /**
   * Output results of analysis.
   */
  public static void output_results() {
    final String[] inputs = CommandLineOptions.getArgs();
    PrintStream out = null;
    String name = CommandLineOptions.outputName();
    if (name != null) {
      try {
        out = new PrintStream(new FileOutputStream(name));
      } catch (java.io.FileNotFoundException fnfe) {
        System.err.printf("while trying to open %s: %s\n", name, fnfe); // NOPMD
        exit_status = 2;
        quit(true);
      }
    } else
      out = System.out;
    if (out!=null){
      if (CommandLineOptions.classUse())
        TextIo.write_csv("class",inputs,class_histogram,out);
      else
        TextIo.write_csv("method",inputs,method_histogram,out);
      out.close();
    }
  }

  /**
   * Close down the system and quit if exit_status is non-zero or if
   * definitely is true.
   * @param definitely true iff the system must quit/exit.
   */
  public static void quit(final boolean definitely) {
    if ((exit_status != 0) || definitely) {
      if (TextIo.debug_state)
        return;
      else
        System.exit(exit_status);
    }
  }
  
  /**
   * Start the system with this command-line.
   * @param the_args the command-line.
   */
  public static void main(final String[] the_args) {
    // argument processing
    exit_status=CommandLineOptions.processOptions(the_args);
    if (exit_status == 0) {
      perform_analysis();
      output_results();
    }
    if (TextIo.debug_state)
      return;
    else
      System.exit(exit_status);
  }
}


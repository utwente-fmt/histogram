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

import java.io.PrintStream;
import java.util.Set;
import java.util.TreeSet;
import util.Histogram;

/**
 * Textual input and produces output for this system.
 * @author Joe Kiniry
 * @version 25-03-2001
 */
public final class TextIo {
  /**
   * This class is never meant to be initialized.
   */
  private TextIo() {
    assert false;
  }
  
  /**
   * The debugging status for this class.
   */
  public static boolean debug_state = false;
  
  private static final StringBuffer stdout_debug_buffer = new StringBuffer();
  private static final StringBuffer stderr_debug_buffer = new StringBuffer();

  /**
   * Enable or disable debugging of text I/O.
   * @param a_status true if debugging is enabled; false otherwise.
   */
  public static void debug(final boolean a_status) {
    debug_state = a_status;
  }
  
  /**
   * Print error message to STDERR.
   * @param a_message the message to print.
   */
  public static void error(final String a_message) {
    System.err.println(a_message); // NOPMD
    if (debug_state)
      stderr_debug_buffer.append(a_message);
  }

  /**
   * Print message to STDOUT.
   * @param a_message the message to print.
   */
  public static void message(final String a_message) {
    System.out.println(a_message); // NOPMD
    if (debug_state)
      stdout_debug_buffer.append(a_message);
  }
  
  /**
   * @param some_output the expected output.
   * @return check that the output sent by the program thus far to STDERR
   * is equal to {@code some_output}.
   */
  public static boolean validate_stderr(final String some_output) {
    return some_output.equals(stderr_debug_buffer.toString());
  }

  /**
   * @param some_output the expected output.
   * @return check that the output sent by the program thus far to STDOUT
   * is equal to {@code some_output}.
   */
  public static boolean validate_stdout(final String some_output) {
    return some_output.equals(stdout_debug_buffer.toString());
  }
  
  /**
   * Print a Histogram matrix in CSV form
   */
  public static void write_csv(final String description,final String names[],final Histogram hist[], final PrintStream out){
    final Set<String> keys = new TreeSet<String>();
    out.printf("\"%s\"",description);
    for(int i=0;i<names.length;i++){
      out.printf(",\"%s\"",names[i]);
      keys.addAll(hist[i].keySet());
    }
    out.println("");
    for (String key: keys) {
      out.printf("\"%s\"",key);
      for(int i=0;i<names.length;i++){
        out.printf(",%d", hist[i].getValue(key));
      }
      out.printf("\n");
    }
  }
}


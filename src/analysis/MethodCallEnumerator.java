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

package analysis;

import java.util.Set;
import java.io.InputStream;
import util.Histogram;

import org.objectweb.asm.ClassReader;

/**
 * Performs the analysis of method call use in various artifacts.
 * @author Joe Kiniry
 * @version 25-03-2001
 */
public class MethodCallEnumerator  {
  /**
   * @return What are the methods of this class?
   * @param a_class_name the class in question.
   */
  public /*@ pure @*/ Set<String> methods(final String a_class_name) {
    assert false;
    //@ assert false;
    return null;
  }

  /**
   * Analyze this classfile and put the results into that class use histogram,
   * and that other method use histogram.
   * @param object_stream the class to analyze.
   * @param a_clh the class use histogram in which to record analysis.
   * @param a_muh the method use histogram in which to record analysis.
   */
  public static void analyzeClass(final InputStream object_stream,
                                  final Histogram a_clh,
                                  final Histogram a_muh) {
    final HistogramClassVisitor visitor = new HistogramClassVisitor(a_clh, a_muh);
    try {
      final ClassReader reader = new ClassReader(object_stream);
      reader.accept(visitor, 0);
    } catch (Exception e) {
      assert false;
    }
    assert false;
    //@ assert false;
  }

  /**
   * Analyze this method signature and put the results into that method use
   * histogram.
   * @param a_method_name the method to analyze.
   * @param a_muh the method use histogram in which to record analysis.
   */
  public void analyzeMethod(final String a_method_name,
                            final Histogram a_muh) {
    assert false;
    //@ assert false;
  }
}


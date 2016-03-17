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

import org.objectweb.asm.MethodVisitor;
import org.objectweb.asm.Type;
import org.objectweb.asm.commons.EmptyVisitor;

import util.Histogram;

/**
 * DependencyVisitor
 * 
 * @author Eugene Kuleshov
 */
public class HistogramMethodVisitor extends EmptyVisitor implements MethodVisitor
{
  /**
   * @todo Write docs.
   */
  private transient final Histogram my_class_use_histogram;

  /**
   * @todo Write docs.
   */
  private transient final Histogram my_method_use_histogram;

  /**
   * @todo Write docs.
   * @param a_class_use_histogram TBD
   * @param a_method_use_histogram TBD
   */
  public HistogramMethodVisitor(final Histogram a_class_use_histogram,
                          final Histogram a_method_use_histogram){
    my_class_use_histogram = a_class_use_histogram;
    my_method_use_histogram = a_method_use_histogram;
  }

  public void visitMethodInsn(final int opcode,
                              final String owner,
                              final String name,
                              final String desc) {
    // This is the only case where a method is called and the counts have to be increased.
    final Type owner_type=Type.getObjectType(owner);
    my_class_use_histogram.increment(owner_type.getClassName());
    my_method_use_histogram.increment(owner_type.getClassName()+"."+name+PrettyPrintSpec(desc));
  }
  
  /**
   * @todo Write docs.
   * @param spec TBD
   * @return TBD
   */
  private static String PrettyPrintSpec(final String spec) {
    final Type args[] = Type.getArgumentTypes(spec);
    final Type return_type = Type.getReturnType(spec);
    final StringBuffer result = new StringBuffer("(");
    for(int i = 0; i < args.length; i++){
      if (0 < i) result.append(',');
      result.append(args[i].getClassName());
    }
    result.append(") : ");
    result.append(return_type.getClassName());
    return result.toString();
  }

}


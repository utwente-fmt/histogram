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

package util;

import java.util.HashMap;
import java.util.Set;
import java.util.TreeSet;

/**
 * Maps string to a count.
 * @author Stefan Blom
 * @author Joe Kiniry
 * @version 08-04-2011
 * @bug JML4c cannot compile this class due to a bug in its support for
 * parameterized classes.
 */
public class HashMapHistogram
  extends HashMap<String, Counter> implements Histogram {

  /** The generated serialVersionUID. */
  private static final long serialVersionUID = -2478428912366914689L;

  /**
   * Increment the usage count for this class.
   * @param a_class_name the name of the class for which the count must be incremented.
   */
  //@ ensures getValue(a_class_name) == \old(getValue(a_class_name) + 1);
  public void increment(final String a_class_name) {
    final Counter counter = get(a_class_name);
    if (counter == null)
      put(a_class_name, new Counter(1));
    else
      counter.increment();
  }

  /**
   * @param a_class_name the name of the class in question.
   * @return the number of times the class has been counted.
   */
  public /*@ pure @*/ int getValue(final String a_class_name){
    final Counter counter = get(a_class_name);
    int result = 0;
    if (counter != null)
      result = counter.getValue();
    return result;
  }

  /**
   * {@inheritDoc}
   */
  public String toString() {
    int max = 0;
    final Set<String> keys = new TreeSet<String>(keySet());
    for (String key: keys)
      if (max < key.length())
        max = key.length();
    max++;
    final String format = "%" + max + "s %5d\n";
    final StringBuffer result = new StringBuffer();
    for (String key: keys)
      result.append(String.format(format, key, getValue(key)));
    return result.toString();
  }
}


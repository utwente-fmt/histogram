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

/**
 * A simple counter class that can be initialized to a specific value,
 * incremented, and cleared.
 * @author Owen Astrachan
 * @author Joe Kiniry
 * @version 11-4-2011
 */

public class Counter {

  /** The counter. */
  //@ private invariant 0 <= my_count;
  private transient int my_count;

  /**
   * Construct a counter whose value is zero.
   */
  //@ ensures getValue() == 0;
  public /*@ pure @*/ Counter() {
    my_count = 0;
  }

  /**
   * Construct a counter with given initial value.
   * @param the_initial_value is the initial value of the counter.
   */
  //@ ensures getValue() == the_initial_value;
  public /*@ pure @*/ Counter(final int the_initial_value) {
    my_count = the_initial_value;
  }

  /**
   * Returns the value of the counter.
   * @return the value of the counter
   */
  //@ ensures 0 <= \result;
  public /*@ pure @*/ int getValue() {
    return my_count;
  }

  /** Zeros this counter. */
  //@ ensures getValue() == 0;
  public void clear() {
    my_count = 0;
  }

  /** Increase the value of the counter by one. */
  //@ ensures getValue() == \old(getValue() + 1);
  public void increment() {
    my_count++;
  }

  /** @return a string representation of the value */
  public String toString() {
    return Integer.toString(my_count);
  }
}

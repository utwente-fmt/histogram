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
import java.io.FileInputStream;
import java.io.InputStream;
import java.util.Enumeration;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

import util.Histogram;

import analysis.MethodCallEnumerator;

/**
 * File input and output for this system.
 * @author Joe Kiniry
 * @version 25-03-2001
 */
public final class FileIo  {

  /**
   * Add the counts for one class file to the histograms.
   * @param file_name The name of the class file, whose contents must be analyzed.
   * @param class_use The class use histogram, to which the count must be added.
   * @param method_use The method use histogram, to which the count must be added.
   */
  private static void processClass(File file_name, final Histogram class_use, final Histogram method_use) {
    try {
      final InputStream object_stream=new FileInputStream(file_name);
      MethodCallEnumerator.analyzeClass(object_stream,class_use,method_use);
      object_stream.close();
    } catch (Exception e) {
      throw new IllegalStateException("while processing: " + e);
    }
  }

  /**
   * Add the counts all class files in a zip archive to the histograms.
   * @param zip_name The name of the archive, whose contents must be analyzed.
   * @param class_use The class use histogram, to which the count must be added.
   * @param method_use The method use histogram, to which the count must be added.
   */
  private static void processZip(File zip_name, final Histogram class_use, final Histogram method_use) {
    ZipFile zip_file;
    try {
      zip_file = new ZipFile(zip_name);
    } catch (Exception e) {
      throw new IllegalStateException("while reading archive '"+zip_name+"': "+e);
    }
    final Enumeration< ? extends ZipEntry> en = zip_file.entries();
    while (en.hasMoreElements()) {
      final ZipEntry e = en.nextElement();
      final String e_name = e.getName();
      if (e.isDirectory()) continue;
      if (e_name.endsWith(".class")){
        try {
          final InputStream object_stream=zip_file.getInputStream(e);
          MethodCallEnumerator.analyzeClass(object_stream,class_use,method_use);
          object_stream.close();
        } catch (Exception ex) {
          throw new IllegalStateException("while processing: "+ ex);
        }
      }           
    }
    try {
      zip_file.close();
    } catch (Exception e) {
      throw new IllegalStateException("while reading archive: " + e);
    }
  }

  /**
   * Recursively scan for class files and zip archives (including jar files) and 
   * analyze their content.
   * @param current the current item under inspection.
   * @param class_use the class use histogram, to which the count must be added.
   * @param method_use the method use histogram, to which the count must be added.
   */
  static void find(final File current,
                   final Histogram class_use,
                   final Histogram method_use) {
    if (current.isDirectory()) {
      for (File child:current.listFiles()){
        find(child, class_use, method_use);
      }
    } else if (current.isFile()) {
      String name = current.toString();
      if (  name.endsWith(".zip")
      || name.endsWith(".jar")
      || name.endsWith(".rar") // weird use of rar for zip, but ... used in case study.
      || name.endsWith(".war")
      ) {
        processZip(current, class_use, method_use);
      } else if (name.endsWith(".class")) {
        processClass(current, class_use, method_use);
      }
    } else {
      TextIo.error("While processing file `" + current + "` an error occurred.");
    }
  }
 
}


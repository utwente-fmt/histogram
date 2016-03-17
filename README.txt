Histogram is a very simple tool that compute the number of times
any class or method is used by a given body of Java byte code.

Contained in the jar archive is everything one needs to run the tool as:

java -jar histogram.jar <arguments>

Contained in the repository are:

build.xml    An ANT build file for the project.
libs         The libraries neede to buidl the tool.
license-info The licenses for the histogram tool and its libraries.
README.txt   This file.
src          The sources of the Histogram tool.

The ant build files has serveral targets:

compile      Will create the bin directory and compile all of the class files.
clean        Will remove the generated files.
jar          Will build histogram.jar.

This project uses two external libraries:
* The ASM byte code manipulation library, see http://asm.ow2.org/index.html
  Version 3.3.1 is included in the binary distribution.
* The Apache Commons CLI library, see http://commons.apache.org/cli/
  Version 1.2 is included in the binary distribution.

Joseph Kiniry
Stefan Blom


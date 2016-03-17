# histogram
Produce histograms of class and method use in JVM byte code


Contained in the jar archive is everything one needs to run the tool as:

java -jar histogram.jar <arguments>

Contained in the src archive are:

arch         The design of the tool using BON notation.
build.xml    An ANT build file for the project.
configs      Several Eclipse config files that may be used with the project.
libs         The libraries neede to buidl the tool.
license-info The licenses for the histogram tool and its libraries.
README.txt   This file.
src          The sources of the Histogram tool.

The ant build files has serveral targets:

compile      Will create the bin directory and compile all of the class files.
clean        Will remove the generated files.
docs         Will generate the javadoc documentation and the BON documentation.
             This target will not build unless the BONc tool is installed.
jar          Will build histogram.jar.
dist         Will build histogram-src.zip.
             Note that this target assume you use git for version control.

This project uses two external libraries:
* The ASM byte code manipulaiton library, see http://asm.ow2.org/index.html
  Version 3.3.1 is included in the binary distribution.
* The Apache Commons CLI library, see http://commons.apache.org/cli/
  Version 1.2 is included in the binary distribution.

Joseph Kiniry
Stefan Blom


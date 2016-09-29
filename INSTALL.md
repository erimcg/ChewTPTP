# Installation

You will need the following software packages:

* chewtptp-src-1.0.0.tar.gz (included here)
* gmp-4.2.2.tar.gz
* yices-1.0.13-i686-pc-linux-gnu.tar.gz OR yices-1.0.13-x86_64-pc-linux-gnu.tar.gz

1.  Install GMP (GNU Multiprecision Library) which is required to run Yices. To install, execute the following commands.  Look out for errors, especially when running 'make check'. The libraries are written to $INSTALL_DIR/chewtptp/gmp-4.2.2/.libs. (Note the 's' on the end of directory name '.libs')

        $ cd $INSTALL_DIR/chewtptp
        $ tar -xzvf gmp-4.2.2.tar.gz
        $ cd $INSTALL_DIR/chewtptp/gmp-4.2.2
        $ ./configure
        $ make
        $ make check    <= VERY IMPORTANT!!!

2.  Untar the appropriate version of Yices (http://yices.csl.sri.com) depending on your system architecture.

        $ cd $INSTALL_DIR/chewtptp
        $ tar -xzvf yices-1.0.13-i686-pc-linux-gnu.tar.gz
        or
        $ tar -xzvf yices-1.0.13-x86_64-pc-linux-gnu.tar.gz

3.  Add the directores $INSTALL_DIR/chewtptp/gmp-4.2.2/.libs and $INSTALL_DIR/chewtptp/yices-1.0.13/lib to your LD_LIBRARY_PATH environmental variable in your shell script file.  Don't forget to reload the shell script file to make the variable visible in you environment.
        
        E.g. add 'export LD_LIBRARY_PATH=$INSTALL_DIR/chewtptp/gmp-4.2.2/.libs:$INSTALL_DIR/chewtptp/yices-1.0.13/lib' to .bashrc.

4.  Compile the ChewTPTP theorem prover
        
        $ cd $INSTALL_DIR/chewtptp
        $ tar -xzvf chewtptp-src-1.0.0.tar.tz
        $ cd $INSTALL_DIR/chewtptp/src
        $ make

5.  Test that ChweTPTP is executable.

        $ cd $INSTALL_DIR/chewtptp/bin
        $ ./chewtptp

        If you see the message "SZS status InputError: too few arguments" 
        you have succeeded in installing our theorem prover.  
    
If you have any questions, please email me at erimcg@n0code.net.

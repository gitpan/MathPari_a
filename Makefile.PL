# $Id: Makefile.PL,v 1.1 1995/01/23 04:46:12 ilya Exp $
use ExtUtils::MakeMaker;
# See lib/ExtUtils/MakeMaker.pm for details of how to influence
# the contents of the Makefile being created.
&WriteMakefile(
	       # Below -R specifies the path to search for this file when the program will run, -L the path to search when the program is linked
	'LIBS' =>  '-R/home/ilya/pari/pari-1.39/src -L/home/ilya/pari/pari-1.39/src -lm -lpari -L/opt/SUNWspro/SC3.0/lib -lsunmath',
	'INC' => '-I/home/ilya/pari/pari-1.39/src',
	'DISTNAME' => 'Pari',
	'NAME' => 'Math::Pari',
	'VERSION' => '0.1',
	'DEFINE' => '-DLONG_IS_32BIT',
);

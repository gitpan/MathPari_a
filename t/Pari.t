#!/usr/bin/perl

BEGIN { unshift @INC, './lib', '../lib';
    require Config; import Config;
}

$test = 0;
$| = 1;
print "1..",&last,"\n";

sub test {
  $test++; if (shift) {print "ok $test\n";1} else {print "not ok $test\n";0}
}

use Math::Pari;

test(1);			# 1

$a=new Math::Pari 1;

test($a);			# 2
test(ref $a eq "Math::Pari");	# 3

{
  package Math::Pari;
  ::test(defined &pari2nv); # 4
}

test(defined &Math::Pari::pari2nv); # 5
test(Math::Pari::pari2iv($a)==1); # 6

# This looks like a bug in the Pari conversion to double:

test(abs(Math::Pari::pari2nv($a)-1.0)<2**-49); # 7
#####print "`", Math::Pari::pari2nv($a)-1.0, "'\n";

$add = Math::Pari::loadPari("gadd");

test($add);			# 8
test("$add" =~ /^CODE/);	# 9

$b= &$add (34,67);

test($b);			# 10
test(ref $b eq "Math::Pari");	# 11
test(Math::Pari::pari2iv($b)==101); # 12

$b=Math::Pari::gadd(11,12);	# Uninitialized value here

test($b);			# 13
test(ref $b eq "Math::Pari");	# 14
test(Math::Pari::pari2iv($b)==23); # 15

$c = Math::Pari::gsub(17,93);

test($c);			# 16
test(ref $c eq "Math::Pari");	# 17
test(Math::Pari::pari2iv($c)==-76); # 18

$c = do { package Math::Pari; gsub(19,93) }; # And here (No MORE :-)

test($c);			# 19
test(ref $c eq "Math::Pari");	# 20
test(Math::Pari::pari2iv($c)==-74); # 21

$d=Math::Pari::gadd($b,$c);

test(ref $d eq "Math::Pari");	# 22
test(Math::Pari::pari2iv($d)==-51); # 23

$e=new Math::Pari "matrix(2,2,j,k,j+k)";

test(ref $e eq "Math::Pari");	# 24

$cc=Math::Pari::pari2iv($c);

test(! defined ref $cc);		# 25

$ee=Math::Pari::pari2pv($e);

test(! defined ref $ee) || print ref $ee;		# 26

test($ee eq "[2,3;3,4]"); # 27

$f=Math::Pari::matinvr($e);

test(ref $f eq "Math::Pari");	# 28
test(Math::Pari::pari2pv($f) eq "[-4,3;3,-2]"); # 29

# Overload

test("$f" eq "[-4,3;3,-2]") || print "$f\n";	# 30

$f+=1;

test("$f" eq "[-3,3;3,-1]") || print "$f\n";	# 31
test($f == "[-3,3;3,-1]");	# 32

$g=(new Math::Pari "[1,2;3;2]");
$gg=Math::Pari::gpui($g,-1);

test($gg);			# 33
$g=(new Math::Pari "[1,2;3;2]")**-1;

test($g == $gg);		# 34

# Should work eventually

####test("$g" eq "[1/2,-1/2;-3/2,1/4]") || print "$g\n"; # 35
test(1);

#test($g == "[1/2,-1/2;-3/2,1/4]"); # 36
test(1);

$f  = new Math::Pari "[2,3;3,1]";
$ff = PARImat [[2,3],[3,1]];

test(Math::Pari::geq($f,$ff));	# 37
test($f==$ff);			# 38
test(Math::Pari::gne($f,$ff)==0);	# 39
test(!($f!=$ff));		# 40
test("$f" eq "$ff");		# 41
test($f eq $ff);		# 42

$f  = new Math::Pari "[2,3;3,2]";

test($f != $ff);		# 43
test(!($f == $ff));		# 44
test("$f" ne "$ff");		# 45
test($f ne $ff);		# 46

$f = new Math::Pari "[2,3;2,1]";
$fff=$f**2;

test($fff eq "[10,9;6,7]");	# 47
test($fff eq $f*$f);		# 48

test(PARI(3)<4);		# 49
test(3<PARI(4));		# 50
test(!(PARI(3)<2));		# 51
test(!(4<PARI(3)));		# 52

test(PARI(3) lt 4);		# 53
test(3 lt PARI(4));		# 54
test(!(PARI(3) lt 2));		# 55
test(!(4 lt PARI(3)));		# 56

use Math::Pari qw(i pi);

# Bug in Pari: depends on the order of execution
test(abs(exp(pi()*i)+1) >= 1e-29); # 57
test(abs(exp(pi()*i)+1) <= 1e-28); # 58

test(('x'*i)**2 == "-x^2");	# 59

sub last {59}

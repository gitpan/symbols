#!perl -W
#______________________________________________________________________
# Symbolic algebra.
# PhilipRBrenan@yahoo.com, 2004.
#______________________________________________________________________

package Math::Algebra::Symbols;
use strict;
use integer;
use Carp;
use Math::BigInt;

$symbols::VERSION = '1.00';

#______________________________________________________________________
# Overload.
# The operator representations are very convenient, but suffer from two
# major defects:
# Major Defect 1: There are not enough operators
# Major Defect 2: The priority of ^ which I use for dot is far too low.    
#______________________________________________________________________

use overload
 '+'     =>\&add3,
 '-'     =>\&negate3,
 'eq'    =>\&negate3,
 '*'     =>\&multiply3,
 '/'     =>\&divide3,
 '**'    =>\&power3,
 'sqrt'  =>\&sqrt3,
 'exp',  =>\&exp3, 
 '=='    =>\&equals3,
 '""'    =>\&print3,
 '^'     =>\&dot3,       # Beware the low priority of this operator
 '~'     =>\&conjugate,  
 'x'     =>\&cross,  
 'abs'   =>\&modulus,  
 '!'     =>\&unit,  
 fallback=>1;

#______________________________________________________________________
# Forward.
#______________________________________________________________________

sub new($);

#______________________________________________________________________
# Big integer version - slower.
#______________________________________________________________________

sub bintBigInt($) {Math::BigInt->new($_[0])}
sub bintBigOne    {Math::BigInt->bone()}
sub bintBigZero   {Math::BigInt->bzero()}

#______________________________________________________________________
# Regular size integer version - faster.
#______________________________________________________________________

sub bint($) {$_[0]}
sub bone()  {1}
sub bzero   {0}

#______________________________________________________________________
# Import - parameters from caller - set up as requested.
#______________________________________________________________________

sub import
 {my %P = (program=>@_);
  my %p; $p{lc()} = $P{$_} for(keys(%P));

#______________________________________________________________________
# Numbers
#______________________________________________________________________

  *bint  = *bintBigInt  if $p{bigint}; # Select integer type
  *bone  = *bintBigOne  if $p{bigint}; # Select integer type
  *bzero = *bintBigZero if $p{bigint}; # Select integer type

#______________________________________________________________________
# New symbolic term - export to calling package.
#______________________________________________________________________

  my $name = 'symbols';
     $name = $p{symbols} if defined($p{symbols});

  my $s = <<'END';
package XXXX;

sub NNNN
 {return SSSS::symbols(@_);
 }
END

  my ($main) = caller();
  my $pack   = ref(bless({}));

  $s=~ s/XXXX/$main/;
  $s=~ s/NNNN/$name/;
  $s=~ s/SSSS/$pack/;
  eval($s);

#______________________________________________________________________
# Check options supplied by user
#______________________________________________________________________

  delete $p{bigint};
  delete $p{symbols};
  delete $p{program};

  croak "Unknown option(s): ". join(' ', keys(%p))."\n\n". <<'END' if keys(%p);
Valid options are:
  BigInt =>0      The default - use regular perl numbers.
  BigInt =>1      Use Perl BigInt to represent numbers.  

  symbols=>'name' Create a routine with this name in the callers
                  namespace to create new symbols. The default is
                  'symbols'.
END

 }

#______________________________________________________________________
# Create a new symbol                              
#______________________________________________________________________

sub symbols
 {return new(shift()) if scalar(@_) == 1;
  my @A = ();
  push @A, new($_) for(@_);
  @A; 
 }

#______________________________________________________________________
# New symbolic term.
#______________________________________________________________________

sub new($)
 {my $s = $_[0];

#______________________________________________________________________
# From array of terms.
#______________________________________________________________________

  if (ref $s eq 'ARRAY' or ref $s eq ref bless {})
   {my @E;
    push @E, @{new($_)} for(@$s);
    return bless \@E;
   }

#______________________________________________________________________
# From a string.
#______________________________________________________________________

  if (!ref($s) or ref($s) eq 'Math::BigInt')
   {my $a = "$s";
    my @T;

    defined($a) or croak "Cannot parse undefined string"; 

    for (;$a ne '' and $a =~ /^\s*([+-])?\s*(\d+)?(?:\/(\d+))?(i)?(.*)$/;)
     {my $c  = bone(); 
         $c  = bint(-1) if $1 and $1 eq '-';
         $c *= bint($2) if defined($2);
      my $d  = bone();
         $d  = bint($3) if $3;
      my $i = 0;
         $i = 1 if $4;
      my $r = {c=>$c, d=>$d, i=>$i};

      my $b = $5;

      for (;$b =~ /^([a-zA-Z]+)(\*|\d+)?(.*)$/;)
       {my $v = $1;
        my $p = 1;
        $p = $2 if $2 and $2 ne '*';
        $b = $3;
        $r->{v}{$v}  = 0 unless $r->{v}{$v};
        $r->{v}{$v} += $p;
       }

      croak "Cannot parse: $a" if $a eq $b;
      $a = $b;

      push @T, $r;
     }

    return new(\@T); 
   }

#______________________________________________________________________
# From a single term supplied in a hash
#______________________________________________________________________

  my $t = {%$s};
  for my $e(qw(sqrt divide exp))
   {$t->{$e} = new($s->{$e}) if defined($s->{$e});
   }
  $t->{v} = {%{$s->{v}}} if defined($s->{v});
  $s = $t;

#______________________________________________________________________
# From term: Assume zero if coefficient not set.
#______________________________________________________________________

  return bless [{c=>bint(0)}] if !exists $s->{c} or $s->{c} == 0;

#______________________________________________________________________
# Reduce coefficent and divisor by common factor.
#______________________________________________________________________

  if (my $d = $s->{d})
   {if ($d != 1)
     {my $g = gcd($s->{c}, $d);
      $s->{c} /= $g;
      $s->{d} /= $g;
     }
   }

#______________________________________________________________________
# Remove divisor if possible.  
#______________________________________________________________________

  if (my $d = $s->{d})
   {if ($d < 0)
     {$s->{c} *= -1;
      $s->{d} *= -1;
     }
    delete $s->{d} if $d == 1;
   }

#______________________________________________________________________
# Remove i if possible.                       
#______________________________________________________________________

  delete $s->{i} if defined $s->{i} and $s->{i} == 0;

#______________________________________________________________________
# Remove sqrt if possible.                       
#______________________________________________________________________

  simplifySqrt($s) if defined $s->{sqrt};

#______________________________________________________________________
# Remove divide by if possible by eliminating common factors.
#______________________________________________________________________

  if (defined($s->{divide}))
   {my $d = $s->{divide};
    removeCommonCD    ($s, $d);
    removeCommonSqrt  ($s, $d);
    removeCommonFactor($s, $d);
    if (my $i = invert($d))
     {my $t = bless[$s]; 
      delete $s->{divide};     
      $s = multiply($t, $i);
      $s = $$s[0]; 
     }
   }

#______________________________________________________________________
# Remove exp if possible.
#______________________________________________________________________

  $s->{exp} = undef if defined($s->{exp}) and !nonZero($s->{exp});

#______________________________________________________________________
# Result - clean up.
#______________________________________________________________________

  delete $s->{i}    unless defined $s->{i} and $s->{i} != 0;
  delete $s->{d}    unless defined $s->{d} and $s->{d} != 1;

  for my $e(qw(sqrt divide exp))
   {delete $s->{$e} if defined $s->{$e} and scalar(@{$s->{$e}}) == 0;
    delete $s->{$e} unless defined $s->{$e};
   }

  if (defined($s->{v}))
   {for my $v(keys(%{$s->{v}}))
     {delete $s->{v}{$v} if $s->{v}{$v} == 0;
     }
    delete $s->{v}  if scalar(keys(%{$s->{v}})) == 0;
   } 

  croak "Zero divisor not allowed" if $s->{d} and $s->{d} == 0;

  bless [$s];
 }

#______________________________________________________________________
# Get component values or supply defaults if not present.
#______________________________________________________________________

sub get($)
 {my $e = $_[0];

  return ($e->{c} || bzero(),  $e->{i} || 0,  $e->{d} || bone(),
          $e->{sqrt}, $e->{divide}, $e->{exp});
 };

#______________________________________________________________________
# Variables and their associated powers.
#______________________________________________________________________

sub getVP($)
 {my $e = $_[0];
  return () unless exists $e->{v};
  my @v = (); push @v, [$_, $e->{v}{$_}] for(keys(%{$e->{v}}));
  @v;
 };

#______________________________________________________________________
# Variables and their associated powers - in sort order.
#______________________________________________________________________

sub getVPSort($)
 {my $e = $_[0];
  return () unless exists $e->{v};
  my @v = (); push @v, [$_, $e->{v}{$_}] for(sort(keys(%{$e->{v}})));
  @v;
 };

#______________________________________________________________________
# Check whether an expression is not zero.
#______________________________________________________________________

sub nonZero($)
 {my $A = $_[0];
  for my $a(@$A)
   {return 1 if defined($a->{c}) and $a->{c} != 0;
   }
  0;
 }

#______________________________________________________________________
# Check whether an expression is one.
#______________________________________________________________________

sub isOne($)
 {my $A = $_[0];
  return 0 unless scalar(@$A) == 1;

  for my $a(@$A)
   {return 0 unless defined($a->{c}) and $a->{c} == 1;
    return 0 unless scalar(keys(%$a)) == 1;
   }
  1;
 }

#______________________________________________________________________
# Factor a number.
#______________________________________________________________________

sub factorize($)
 {my @primes = qw(
  2  3   5   7   11  13  17  19  23  29  31  37  41  43  47  53  59  61
 67 71  73  79   83  89  97 101 103 107 109 113 127 131 137 139 149 151
157 163 167 173 179 181 191 193 197 199 211 223 227 229 233 239 241 251
257 263 269 271 277 281 283 293 307 311 313 317 331 337 347 349 353 359
367 373 379 383 389 397 401 409 419 421 431 433 439 443 449 457 461 463
467 479 487 491 499 503 509 521 523 541 547 557 563 569 571 577 587 593
599 601 607 613 617 619 631 641 643 647 653 659 661 673 677 683 691 701
709 719 727 733 739 743 751 757 761 769 773 787 797 809 811 821 823 827
829 839 853 857 859 863 877 881 883 887 907 911 919 929 937 941 947 953
967 971 977 983 991 997);

  my $n = bint($_[0]);
  my $f;

  for my $p(@primes)
   {for(;$n % $p == 0;)
     {$f->{$p}++;
      $n /= $p;
     }
    last unless $n > $p;
   }
  $f;
 };

#______________________________________________________________________
# Greatest Common Divisor.
#______________________________________________________________________

sub gcd($$)
 {my $x = abs($_[0]);
  my $y = abs($_[1]);

  return 1 if $x == 1 or $y == 1; 

  my ($a, $b) = ($x, $y); $a = $y, $b = $x if $y < $a;
  
  for(my $r;;)
   {$r = $b % $a;
    return $a if $r == 0;
    ($a, $b) = ($r, $a);
   }
 };

#______________________________________________________________________
# Least common multiple.  
#______________________________________________________________________

sub lcm($$)
 {my $x = abs($_[0]);
  my $y = abs($_[1]);
  return $x*$y if $x == 1 or $y == 1; 
  $x*$y / gcd($x, $y);
 };

#______________________________________________________________________
# Print.
#______________________________________________________________________

sub print($)
 {my $a = $_[0]; # Expression

#______________________________________________________________________
# Print expression
#______________________________________________________________________

  if (ref($a) eq ref bless {})
   {my @s = ();
    push @s, &print($_) for(@$a);
    my $s = join('+', @s);
    $s =~ s/\+\-/\-/g;
    $s = '0' if $s eq '';
    return $s;
   }

#______________________________________________________________________
# Print term
#______________________________________________________________________
  
  return '' unless nonZero([$a]);

# Variables

  my @v = ();
  for my $vp(getVP($a))
   {my ($v, $p) = @$vp;
    next if $p == 0;
    push @v, '*', '$'.$v;
    push @v, "**$p" if $p != 1;
   }

# Other components

  my ($c, $i, $d) = get($a);

  my @s = ();
  push @s, '+', abs($c) if     $c >= 0;
  push @s, '-', abs($c) unless $c >= 0;
  push @s, '/', $d      unless $d == 1;
  push @s, '*', '$i'    unless $i == 0;
  push @s, '*', 'sqrt', '(', &print($a->{sqrt}),   ')' if $a->{sqrt};
  push @s, '*', 'exp',  '(', &print($a->{exp}),    ')' if $a->{exp};
  push @s, '/',         '(', &print($a->{divide}), ')' if $a->{divide};
  push @s, @v;

# Clean up

  shift @s if $s[0] =~ m#[\+]#;

# Join terms up and return
     
  my $r = join('', @s);
  $r =~ s/(?<!\*\*\-)1\*//g;        # remove: 1*
  $r =~ s/\*(\$\w+)\*\*\-1/\/$1/g;  # change: *$y**-1 to /$y
  return $r;        
 }

#______________________________________________________________________
# Print operator.
#______________________________________________________________________

sub print3($$$)
 {&print($_[0]);
 }

#______________________________________________________________________
# Add a term.  Return undef if the terms are cannot be added.
#______________________________________________________________________

sub addTerm($$)
 {my ($a, $b) = @_;

# ci

  my ($ca, $ia, $da) = get($a);
  my ($cb, $ib, $db) = get($b);

  return undef unless $ia == $ib; 

# v

  my %v = ();                      
     %v = (%v, %{$a->{v}}) if $a->{v};
     %v = (%v, %{$b->{v}}) if $b->{v};

# for my $v(sort(keys(%v)))
  for my $v(keys(%v))
   {my $A = $a->{v}{$v} || 0;
    my $B = $b->{v}{$v} || 0;
    
    return undef unless $A == $B;
   }

# sqrt, divide, exp

  for my $e(qw(sqrt divide exp))
   {my ($s, $t) = ($a->{$e}, $b->{$e});
    return undef if defined($s) xor defined($t);
    return undef if defined($s) and defined($t) and !equals($s, $t);
   } 

# result: the two terms have the same variables, sqrt etc. and so can be added

  my $d = lcm($da, $db);
  my $c = $ca * ($d/$da) + $cb * ($d/$db);
  return {c=>bint(0)} unless $c != 0;

  my $g  = gcd($c, $d); $c /= $g; $d /= $g;

  my $r   = {};
  $r->{c} = $c;
  $r->{i} = $ia;
  $r->{d} = $d;
  $r->{v} = $a->{v};
  for my $e(qw(sqrt divide exp))
   {$r->{$e} = $a->{$e} if defined($a->{$e});
   }
  $r;                                            
 }

#______________________________________________________________________
# All expressions.
#______________________________________________________________________

sub getAllExpressions($)
 {my $e = [];
  for my $a(@{$_[0]})                      
   {if (ref($a) eq ref bless {})
     {push @$e, $_ for (@$a);                      
     }
    else
     {push @$e, $a;                      
     }
   }
  $e;
 }

#______________________________________________________________________
# Signature for a term - used to speed up add.
#______________________________________________________________________

sub signature($)
 {my $t = $_[0]; # Term
  return '' unless exists $t->{v};

  my $s = ''; $s .= $_.$t->{v}{$_} for (sort(keys(%{$t->{v}})));
  $s;
 }

#______________________________________________________________________
# Add.
#______________________________________________________________________

sub add(@)
 {my @S;

#______________________________________________________________________
# Partition terms by signature.
#______________________________________________________________________
    
  my %P; push @{$P{signature($_)}}, $_ for (@{getAllExpressions(\@_)});
 
#______________________________________________________________________
# Collect like terms by trying to add every possible combination within
# each partition induced by the signature.
#______________________________________________________________________
    
  my @T = ();
  for     my $p(keys(%P))
   {my @P = @{$P{$p}};
    my $n = scalar(@P)-1;
    for   my $s(0..$n)
     {next   unless defined($P[$s]);
      for my $t($s+1..$n)
       {next unless defined($P[$t]);
        if (my $r = addTerm($P[$s], $P[$t]))
         {delete $P[$t];
          $P[$s] = $r;
         }
       }
     }
    for my $p(@P)
     {push @T, $p if defined($p) and $p->{c} != 0;
     }
   }

#______________________________________________________________________
# Sort terms into degree order.
# PolynomialDivision() relies on this feature.
# Performance is acceptable as we are not in addTerm().
#______________________________________________________________________

  my @t = ();
  for my $t(@T)
   {my $k = '';
    for my $vp(getVP($t))
     {my ($v, $p) = @$vp;
      $k .= $v x (abs($p)+1);
     }
    push @t, [$t, $k];
   }

  my @s = sort {$a->[1] cmp $b->[1]} @t;
  my @r = ();
  for my $t(@s)
   {push @r, $t->[0];
   }  
  new(\@r);
 }

#______________________________________________________________________
# Add operator.
#______________________________________________________________________

sub add3($$$)
 {my ($a, $b) = @_;
  add($a, new($b));
 }

#______________________________________________________________________
# Negate.
#______________________________________________________________________

sub negate($)
 {my $a = $_[0];
  my $b = new($a);
  $_->{c} = -$_->{c} for(@$b);
  $b;
 }

#______________________________________________________________________
# Negate operator.
#______________________________________________________________________

sub negate3($$$)
 {my ($a, $b, $c) = @_;
  my $r;
  $b = new($b) if defined($b) and !ref($b);
  if (ref($b))
   {$r = add($b, negate($a)) if     $c;
    $r = add($a, negate($b)) unless $c;
   }   
  else
   {$r = negate($a);
   } 
  return $r;
 }

#______________________________________________________________________
# Multiply a term.
#______________________________________________________________________

sub multiplyTerm($$)
 {my ($a, $b) = @_;
  my ($ca, $ia, $da, $sa, $va, $ea) = get($a);
  my ($cb, $ib, $db, $sb, $vb, $eb) = get($b);

# c

  my $c = $ca * $cb;
  my $d = $da * $db;
  my $g = gcd($c, $d);
     $c /= $g; $d /= $g; 

# i

  my $i = ($ia + $ib) % 4;
  ($c *= -1, $i -= 2) if $i == 2 or $i == 3;

# v

  my %v = ();                      
     %v = (%v, %{$a->{v}}) if $a->{v};
     %v = (%v, %{$b->{v}}) if $b->{v};
  my $w;

  for my $v(sort(keys(%v)))
   {my $av = $a->{v}{$v} || 0;
    my $bv = $b->{v}{$v} || 0;
    my $n = $av + $bv;
    $w->{$v} = $n unless $n == 0;
   }

# sqrt divide exp

  my ($extra, $s, $e, $v);

# sqrt

  $s = $sa if defined($sa); 
  $s = $sb if defined($sb);
  if (defined($sa) and defined($sb))
   {if (equals($sa, $sb))
     {$extra = new($sa); # Equal square roots - move a copy out
      $s = undef;
     }
    else
     {$s = $sa * $sb;
     }
   }

# divide

  $v = $va if defined($va); 
  $v = $vb if defined($vb);
  $v = $va * $vb if defined($va) and defined($vb);

# exp

  $e = $ea if defined($ea); 
  $e = $eb if defined($eb);
  $e = $ea + $eb if defined($ea) and defined($eb);
  $e = undef if defined($e) and !nonZero($e);
  
# Result
  
  my $r        = {};
  $r->{c}      = $c;
  $r->{d}      = $d;
  $r->{i}      = $i;
  $r->{v}      = $w;
  $r->{sqrt}   = $s if defined($s);
  $r->{divide} = $v if defined($v);
  $r->{exp}    = $e if defined($e);

  return new($r)*$extra if defined($extra);
  return bless [$r];
 }

#______________________________________________________________________
# Multiply.
#______________________________________________________________________

sub multiply($$)
 {my ($A, $B) = @_;

  return $A if !nonZero($A) or isOne($B);
  return $B if !nonZero($B) or isOne($A);

  my @T = ();

  for my $a(@$A)
   {for my $b(@$B)
     {push @T, @{multiplyTerm($a, $b)};
     }
   }
  add(bless \@T);
 }

#______________________________________________________________________
# Multiply operator.
#______________________________________________________________________

sub multiply3($$$)
 {my ($a, $b) = @_;
  $b = new($b) unless ref($b);
  multiply($a, $b);
 }

#______________________________________________________________________
# Divide.
#______________________________________________________________________

sub divide($$)
 {my ($A, $B) = @_;

  my $b  = $$B[0];
  nonZero([$b]) or croak "Cannot divide by zero";

# Simple divide - single invertible term

  my $i = invert($B);
  return multiply($A, $i) if $i;

# Difficult divide

  my ($D, $R) = polynomialDivision($A, $B);

  my @E = (@$D);         # Divide result
  for my $r(@$R)         # Divide remainder 
   {my $d = $r->{divide};
    $r->{divide} = multiply($d, $B) if     $d;
    $r->{divide} = new($B)          unless $d;  
    push @E, $r;
   }
  add(bless \@E);
 }

#______________________________________________________________________
# Invert - take the reciprocal of a single term.
#______________________________________________________________________

sub invert($);
sub invert($)
 {my $A = $_[0];
  my @B = ();

  return undef unless scalar(@$A) == 1;  

  for my $a(@$A)
   {my ($c, $i, $d, $s, $v, $e) = get($a);

# i
    $c = -$c if $i;

# Sqrt

    if (defined($s))
     {my $S = invert($s);
      return undef unless $S;
      $s = $S;
     } 

# Exp

    $e = -$e if defined($e);

# Variable powers
    
    my $w; $w->{$_} = -$a->{v}{$_} for(sort(keys(%{$a->{v}})));

# Result

    my $r = new {c=>$d, d=>$c, i=>$i, sqrt=>$s, v=>$w, exp=>$e};
    return $r unless $v;
    return $r * $v;
   }
 }

#______________________________________________________________________
# Divide operator.
#______________________________________________________________________

sub divide3($$$)
 {my ($a, $b, $c) = @_;
  my $d = $b;
     $d = new($d) unless ref($d) eq ref bless {};
  my $r;
     $r = divide($d, $a) if     $c;
     $r = divide($a, $d) unless $c;
  $r;
 }

#______________________________________________________________________
# Power.
#______________________________________________________________________

sub power($$)
 {my ($e, $p) = @_;
  my $r = new($e);

  if (!ref($p))
   {my @B = ([1, $r]);
    my $b;
    for ($b = 2; $b <= $p; $b *= 2)
     {$r *= $r;
      push @B, [$b, $r];
     }
    pop @B; $b = $b/2; $p -= $b;
    for (; $p > 0 ;)
     {my ($B, $R) = @{pop @B};
      if ($B <= $p)
       {$r *= $R;
        $p -= $B;
       }
     }
   return $r;
  }   
 else   
  {my $R = $r;
   $R *= $r for(2..$p);
   return $R;
  }
 }

#______________________________________________________________________
# Power operator.
#______________________________________________________________________

sub power3($$$)
 {my ($a, $b) = @_;
  power($a, $b);
 }

#______________________________________________________________________
# Equals.
#______________________________________________________________________

sub equals($$)
 {my ($a, $b) = @_;
  !nonZero(add($a, negate($b)));
 }

#______________________________________________________________________
# Equals operator.
#______________________________________________________________________

sub equals3($$$)
 {my ($a, $b) = @_;
  !nonZero(isZero(add($a, negate($b))));
 }

#______________________________________________________________________
# Square root operator.
#______________________________________________________________________

sub sqrt3($)
 {new({c=>1, sqrt=>new($_[0])});
 }

#______________________________________________________________________
# Exponential operator.
#______________________________________________________________________

sub exp3($)
 {new({c=>1, exp=>$_[0]});
 }

#______________________________________________________________________
# Real part.
#______________________________________________________________________

sub re($)
 {my $A = $_[0];
  $A = new($A) unless ref($A);
  my @r;
  for my $a(@$A)
   {push @r, $a if !defined($a->{i}) or  $a->{i} == 0;
   }
  bless \@r;
 }

#______________________________________________________________________
# Imaginary part.
#______________________________________________________________________

sub im($)
 {my $A = $_[0];
  $A = new($A) unless ref($A);
  my @i;
  for my $a(@$A)
   {next unless defined($a->{i});
    my $b = {%$a};
    delete $b->{i};
    push @i, $b;
   }
  bless \@i;
 }

#______________________________________________________________________
# Modulus.
#______________________________________________________________________

sub modulus($)
 {my $a = $_[0];
  sqrt((re($a))**2+((im($a))**2));
 }

#______________________________________________________________________
# Conjugate.
#______________________________________________________________________

sub conjugate($)
 {my $a = $_[0];
  re($a) - im($a) * new('i');
 }

#______________________________________________________________________
# Simplify square root.
#______________________________________________________________________

sub simplifySqrt($)
 {my $t = $_[0];

# cdis

  my ($c, $i, $d, $s) = get($t);

# No simplification unless single term sqrt

  return if !defined($s) or scalar(@$s) > 1;

# Array of zero entries means the square root is zero

  if (scalar(@$s) == 0)
   {delete $t->{sqrt};
    $t->{c} = 0;
    return; 
   }

# cdis for square root

  my $r = $s->[0];
  my ($c2, $i2, $d2, $s2) = get($r);

# Remove largest square root

  my $lsr = sub ($)
   {my $n = shift();
    my ($a, $b) = (1, $n);
    my $f = factorize($n);
  
    for my $v(keys(%$f))
     {my $p = $f->{$v};
      if ($p % 2 == 0)
       {$a *= $v**($p/2);
        $b /= $v** $p;
       }
     }
    return ($a, $b);
   };

# Remove duplicate factors from square root

   my ($a, $b) = &$lsr($c2);
   $t->{c} *= $a; $r->{c} = $b;


   if ($d2 != 1)
    {my ($a, $b) = &$lsr($d2);

     $t->{d} = 1 unless $t->{d};
     $t->{d} *= $a;
     $r->{d}  = $b;
     delete $r->{d} if $b == 1; 
    }

# Remove duplicate powers from square root

  for my $vp(getVP($r))
   {my ($v, $p) = @$vp;
    my $q = $p - $p % 2;
    $r->{v}{$v} -= $q;
    $t->{v}{$v} += $q/2;
   }

# Remove zero powers from square root and container

  for my $o(($r, $t))
   {for my $vp(getVP($o))
     {my ($v, $p) = @$vp;
      delete $o->{v}{$v} if $p == 0;
     }
    delete $o->{v}  if scalar(keys(%{$o->{v}})) == 0;
   }

# Remove sign from square root

  if ($r->{c} < 0)
   {$r->{c}  = abs($r->{c});
    $t->{i} += 1;
   } 

# Remove sqrt if 1

  delete $t->{sqrt} if isOne($s);
 };

#______________________________________________________________________
# Remove common coefficients and divisor.
#______________________________________________________________________

sub removeCommonCD(@)
 {my $e = getAllExpressions(\@_);

  return unless scalar(@$e);

  my @c; my @d;                          
  for my $a(@$e)                      
   {my ($c, undef, $d) = get($a);
    push @c, $c; push @d, $d;
   }

  my $dd = $d[0]; $dd = lcm($dd, $_) for (@d);                      

  my $cc;
  for my $i(0..scalar(@c)-1)
   {$c[$i] *= $dd/ $d[$i];
    $cc = $c[$i]           unless $cc;
    $cc = gcd($cc, $c[$i]) if     $cc;
   }

  $_ /= $cc for (@c);

  for my $i(0..scalar(@c)-1)
   {$e->[$i]{c} = $c[$i];
    delete $e->[$i]{d};
   }
 }

#______________________________________________________________________
# Remove a common factor from an assorted list of expressions.
#______________________________________________________________________

sub removeCommonFactor(@)
 {my $e = getAllExpressions(\@_);

# Get all the variables across all expressions

  my $w = {};                          
  for my $a(@$e)                      
   {$w = {%$w, %{$a->{v}}} if $a->{v};
   }

# Find minimum power of each variable across all expressions

  for my $a(@$e)                      
   {my $W = {};
    for my $vp(getVP($a))
     {my ($v, $p) = @$vp;
      $W->{$v} = $w->{$v} if exists($w->{$v});
      $W->{$v} = $p       if exists($W->{$v}) and $W->{$v} > $p;
     }
    $w = {%$W};
   }

  return undef unless keys(%$w);

# Remove common factor from all expressions

  for my $a(@$e)                      
   {for my $vp(getVP($a))
     {my ($v, $p) = @$vp;
      next unless exists($w->{$v});
      $a->{v}{$v} -= $w->{$v};
      delete $a->{v}{$v} unless $a->{v}{$v}; 
     }  
    delete $a->{v} unless keys(%{$a->{v}}); 
   }
 }

#______________________________________________________________________
# Remove a common square root.
#______________________________________________________________________

sub removeCommonSqrt(@)
 {my $e = getAllExpressions(\@_);

# Check they all have square roots before going further

  my @s = ();                    
  for my $a(@$e)                      
   {return undef unless defined($a->{sqrt});
    push @s, $a->{sqrt};
   }

  return undef unless @s;

# Confirm thay all have the same root

  my $a = shift(@s);
  for my $b(@s)    
   {return undef unless equals($a, $b); 
   }

# Delete the common square root

  delete $_->{sqrt} for (@$e);    
 }

#______________________________________________________________________
# Substitute.
#______________________________________________________________________

sub sub($@)
 {my $E = new(shift());
  my @R = @_;
  my $S = $E;

# Each replacement

  for(;@R > 0;)
   {my $s =     shift @R;  # Replace this variable
    my $W = new(shift @R); # With this expression
    my @T = ();

    $s =~ /^\w+$/ or croak "Can only substitute an expression for a variable, not $s";

# Each expression

    for my $e(@$S)
     {for my $f(qw(sqrt divide exp))
       {$e->{$f} = &sub($e->{$f},  @_) if defined($e->{$f});
       }

      my $n = delete $e->{v}{$s} || 0;
      if ($n == 0)
       {push @T, $e;
       }
      else
       {push @T, @{multiply(new($e), power($W,  $n))} if $n > 0;
        push @T, @{divide  (new($e), power($W, -$n))} if $n < 0;
       }
     }
    $S = \@T;
   }

  return add(new($S));
 }

#______________________________________________________________________
# Differentiate.
#______________________________________________________________________

sub diff($$)
 {my $e = $_[0]; # Differentiate this expression 
  my $d = $_[1]; # with this variable

  my @R = ();
  for my $T(@$e)
   {if ($T->{v}{$d})
     {my $t = new([$T]);
      $t = shift(@$t);
      for my $vp(getVP($t))
       {my ($v, $p) = @$vp;
        next unless $v eq $d;
        $t->{c} *= $p;
        $t->{v}{$v}--;
       }
      push @R, $t;
     }
    elsif ($T->{sqrt})
     {my $s = new([$T->{sqrt}]);
      my $i = invert(multiply($s, new(2)));
      my $m = multiply([$T], $i);
      push @R, @$m;
     }
   }
  new(\@R);
 }

#______________________________________________________________________
# Dot - complex dot product.
#______________________________________________________________________

sub dot($$)
 {my ($a, $b) = @_;

  new(re($a) * re($b) + im($a)* im($b));
 }

#______________________________________________________________________
# Dot Product operator.
#______________________________________________________________________

sub dot3($$$)
 {my ($a, $b, $c) = @_;
  dot($a, $b);
 }

#______________________________________________________________________
# Unit: intersection with unit circle.
#______________________________________________________________________

sub unit($)
 {my $a = $_[0];
  my $l = modulus($a);
  croak "Cannot make unit out of zero" if $l == 0;
  divide($a, $l); 
 }

#______________________________________________________________________
# The area of the parallelogram formed by two complex vectors.
#______________________________________________________________________

sub cross($$)
 {my ($a, $b) = (new($_[0]), new($_[1]));

  sqrt((dot($a,$a) * dot($b,$b)) - (dot($a,$b)**2)); 
 }

#______________________________________________________________________
# Simplify an equation known to be zero by multiplying out by all
# 'divide by' and eliminiating common coefficients, divisors, sqrts.
#______________________________________________________________________

sub isZeroRemoveCD($)
 {my $r = new($_[0]); # Expression

# Each term: multiply out divides

  for my $a(@$r)
   {my $ad = $a->{divide};
    next unless defined($ad);
    my @B = ();
    for my $b(@$r)
     {my $bd = $b->{divide};
      if ($a == $b or (defined($bd) and equals($ad, $bd)))
       {delete $b->{divide};
        push @B, $b
       }
      else
       {push @B, @{new($b) * $ad};
       }
     }
    $r = add(new(\@B));
   }

# Each term: multiply out all negative powers

  my %v = ();                          
  for my $a(@$r)                      
   {for my $vp(getVP($a))
     {my ($v, $p) = @$vp;
      $v{$v} += -$p if $p < 0;
     }
   }

  for my $a(@$r)                      
   {for my $v(keys(%v))
     {$a->{v}{$v} += $v{$v};
      delete $a->{v}{$v} unless $a->{v}{$v};
     }
   }

# Result

  removeCommonCD     ($r); # Common coefficients and divisors
  removeCommonSqrt   ($r); # Common square roots
  removeCommonFactor ($r); # Common variable powers
  $r;
 }

#______________________________________________________________________
# Simplify an equation known to equal zero.
#______________________________________________________________________

sub isZero($);
sub isZero($)
 {my $E = new($_[0]);           # Expression
  return $E unless scalar(@$E); # Immediate return if empty (0) expression

#______________________________________________________________________
# Remove square roots.
#______________________________________________________________________

  for my $h(1..100)               # 100 but is unlikely to be exceeded
   {$E = isZeroRemoveCD($E);      # Remove common factors
    return $E unless scalar(@$E); # Immediate return if empty (0) expression

#______________________________________________________________________
# Partition by square roots.
#______________________________________________________________________

    my %S = ();
    for my $e(@$E)
     {my $s = $e->{sqrt};
      push @{$S{"$s"}}, $e if $s;      # Square root
      push @{$S{""}},   $e unless $s;  # Non square root
     }

#______________________________________________________________________
# Return immediately if there are no square roots.
#______________________________________________________________________

    my $ns =  scalar(keys(%S)); 
    return $E unless $ns;
    return $E if $ns == 1 and $S{''}; 

#______________________________________________________________________
# Square each partitions, as required by the formulae below.
# Convert: sqrt(a)*b + sqrt(a)*c to sqrt(a)*(b+c) and then square to 
# get:     a*(b+c)**2.
#______________________________________________________________________

    my @t;
    for my $s(keys(%S))
     {if ($s eq '')
       {my $r = add(new([$S{$s}]))**2;
        push @t, $r;
       }
      else
       {my @s = @{$S{$s}};
        my @R;  # Result of squaring this partition
        my $q;  # The sqrt, common to all terms, characterizing this partition
        for my $t(@s)
         {my $A = new($t);
          for my $a(@$A)
           {$q = delete $a->{sqrt};
           }
          push @R, $A; # Sum terms in this parition
         }
        my $s = add(new(\@R));
        my $r = add(new(\@R))**2*$q;
        push @t, $r;
       }
     }  

#______________________________________________________________________
# I can multiply out upto 4 square roots using the formulae below.     
# There is a formula for 5 sqrts, but it is big. I believe there is
# no formulae for 6 and above - rather like Galois.
# These formulae are obtained by squaring out and rearranging:
# sqrt(a)+sqrt(b)+sqrt(c)+sqrt(d) == 0 until no sqrts remain, and
# then matching terms to produce optimal execution.
#______________________________________________________________________
   
    $ns < 5 or die "There are $ns square roots present.  I can handle less than 5";

    my ($a, $b, $c, $d) = @t;

    if    ($ns == 1)
     {$E = $a;
     }
    elsif ($ns == 2)
     {$E = $a-$b;
     }
    elsif ($ns == 3)
     {$E = -$a**2+2*$a*$b-$b**2+2*$c*$a+2*$c*$b-$c**2;
     }
    elsif ($ns == 4)
     {my $a2=$a *$a;
      my $a3=$a2*$a;  
      my $a4=$a3*$a;  
      my $b2=$b *$b;
      my $b3=$b2*$b;  
      my $b4=$b3*$b;  
      my $c2=$c *$c;
      my $c3=$c2*$c;  
      my $c4=$c3*$c;  
      my $d2=$d *$d;
      my $d3=$d2*$d;  
      my $d4=$d3*$d;
      my $bpd = $b+$d;  
      my $bpc = $b+$c;  
      my $cpd = $c+$d;  
      $E =
-  ($a4 + $b4 + $c4 + $d4)
+ 4*(
   +$a3*($b+$cpd)+$b3*($a+$cpd)+$c3*($a+$bpd)+$d3*($a+$bpc)
   -$a2*($b *($cpd)+ $c*$d)   
   -$a *($b2*($cpd)+$d2*($bpc))
    )

- 6*($a2*$b2+($a2+$b2)*($c2+$d2)+$c2*$d2)

- 4*$c*($b2*$d+$b*$d2)
- 4*$c2*($a*($bpd)+$b*$d)
+40*$c*$a*$b*$d   
;   
     }
   }
 }

#______________________________________________________________________
# Solve an equation known to be equal to zero for a specified variable. 
# ($x+1)->solve(qw(x)) produces -1.  Variables whose values are known,
# and thus are in effect, known constants, should be listed after the 
# variable to be solved for.  
#______________________________________________________________________

sub solve($@)
 {my $e = shift; # Expression to solve
  my $x = shift; # Solve for this variable
  my @c = @_;    # Variables whose values are known

  my $z = isZero($e);            # Set equation to zero

# Classify variables in the expressions comprising equation

  my %v = ();
  for my $y (@{getAllExpressions($z)})
   {%v = (%v, %{$y->{v}}) if defined($y->{v});          
   }                                                                
  $_ = 0 for(values(%v)); # Set unknowns to 0 
  $v{$_} = 1 for(@c);     #   and knowns to 1 
  $v{$x} = 2;             # Solve for x            

# Consider terms which are constant with respect to x

  my @T = (); my @X = ();
  C: for my $t(@$z)
   {for my $v(keys(%{$t->{v}}))
     {next C unless $v{$v};
     }
    push @T, $t unless $t->{v}{$x};
    push @X, $t if     $t->{v}{$x};
   }
  die "Variable $x does not occur in equation to solve: $e" unless @X;
    
# Maximum power of x and gcd of power of x

   my $p = $X[0]->{v}{$x};
   for my $y(@X)
    {$p = $y->{v}{$x} if $p > $y->{v}{$x};
    }
   my $g = $p;
   for my $y(@X)
    {$g = gcd($g, $y->{v}{$x});
    }

# Proposed solution

  my $xx;

  if    ($p == 1 and $p == $g)
   {delete $_->{v}{$x} for(@X);
    $xx = divide(negate(new(bless([@T]))), new(bless([@X])));
   } 
  elsif ($p == 2 and $p == $g)
   {delete $_->{v}{$x} for(@X);
    $xx = sqrt(divide(negate(new(bless([@T]))), new(bless([@X]))));
   } 
  else
   {die "Maximum power of $x is $p/$g";
   }

# Check that it works

  my $yy = $e->sub($x=>$xx);
  $yy == 0 or die "Proposed solution \$$x=$xx does not zero equation $e";
  $xx; 
 }

#______________________________________________________________________
# Check that one term is within another, i.e. that inverting $B and   
# multiplying by $A will not produce negative powers. Although
# this technique used in conjunction with polynomial division, should
# be applicable to negative powers as well.
#______________________________________________________________________

sub within($$)
 {my ($a, $b) = @_;

  for my $vp(getVP($b))
   {my ($v, $p) = @$vp;
    return undef if     $p < 0;
    return undef unless defined($a->{v}{$v}); 
    my $P = $a->{v}{$v} - $p;
    return undef if $P < 0;
   }

  return 1;
 }

#______________________________________________________________________
# Degree of a polynomial.   
#______________________________________________________________________

sub polynomialDegree($)
 {my $A = $_[0];

  my $D = 0;
  for my $a(@$A)
   {my $d = 0;
    for my $vp(getVP($a))
     {my ($v, $p) = @$vp;
      $d += $p;
     }
    $D = $d if $d > $D; 
   }
  return $D;
 }

#______________________________________________________________________
# Polynomial division.
#______________________________________________________________________

sub polynomialDivision($$);
sub polynomialDivision($$)
 {my ($A, $B) = @_;

#______________________________________________________________________
# If the divisor is bigger than the dividend, try and remove a common
# factor from both.
#______________________________________________________________________

  if (polynomialDegree($A) < polynomialDegree($B))
   {my ($d, $r) = polynomialDivision($B, $A);
    return ($A, $B) if nonZero($r);
    return (new({c=>1, divide=>$d}), new('0'));
   }

#______________________________________________________________________
# Otherwise divide larger dividend by smaller divisor and return
# result and remainder.
#______________________________________________________________________

  my $C = new($A);
  my $D = new(0);

  for   my $bb(@$B)
   {my $b = new($bb); 
    my $i = invert($b);
    return (new('0'), $A) unless $i;
LOOP: 
    for my $aa(@$C)
     {next unless within($aa, $bb);
      my $a = new($aa);
      my $c = multiply($a, $i);
      $D += $c; 
      $C -= $c * $B;
      last unless nonZero($C);
      goto LOOP;
     }
    last unless nonZero($C);
   } 
 ($D, ($A - $D * $B));
 }

#______________________________________________________________________
#   T E S T S  tests  T E S T S  tests  T E S T S  tests  T E S T S
# The following routines test the above.  These tests are run by default
# if you execute this package as opposed to using it.
#   T E S T S  tests  T E S T S  tests  T E S T S  tests  T E S T S
#______________________________________________________________________
#______________________________________________________________________
# Ellipse: Demonstrate various invariants of the ellipse algebraically.
# The expanded expressions are quite large.  Either substitution, via
# eval(), or careful choice of expresion for the locus of ellipse can
# be used to overcome this difficulty.
#______________________________________________________________________

sub testEllipse
 {my $errors = 0;

#______________________________________________________________________
# Test conjecture.
#______________________________________________________________________

  my $test = sub($$)
   {my $z = shift();              # Expression
    my $t = shift();              # Title
    my $y = $z->isZero();         # Is result zero as desired? 

    print "z=$z\ny=$y\n";
    print "FAIL: $t"    if     $y;
    print "SUCCESS: $t" unless $y;
    print "\n\n";
    $errors++ if $y;
   };

#______________________________________________________________________
# Focus trip == 2R.
#______________________________________________________________________

   {my ($i, $r, $R, $f, $x) = symbols(qw(i r R f x));

    my $y  = sqrt($R*$R-$f*$f - $x*$x +$f*$f*$x*$x / ($R*$R));  # Ellipse: rr=RR-ff
    my $a  = $x+$i*$y - $f;            # Vector from Focus to locus
    my $b  = $x+$i*$y + $f;            # Vector from other Focus to locus

    my $z  = abs($a) + abs($b) - 2*$R; # Focus trip

    $test->($z, "Focus trip == 2R");
   }

#______________________________________________________________________
# Angle of incidence equals angle of reflection via dot product with
# normal to tangent vector.                                         
#______________________________________________________________________

   {my ($i, $r, $R, $f, $x, $y) = symbols(qw(i r R f x y));

       $r  = sqrt($R*$R - $f*$f);      # Focus
       $y  = sqrt($R*$R-$f*$f - $x*$x +$f*$f*$x*$x / ($R*$R));  # Ellipse: rr=RR-ff
  
    my $p  = $x + $i * $y;             # x,y point on locus of ellipse
    my $s  = $x*$r*$r + $i*$y*$R*$R;   # Normal to tangent at locus
  
    my $a  = $p - $f;                  # Vector from Focus to locus
    my $b  = $p + $f;                  # Vector from other Focus to locus
  
    my $c  = $a * abs($b);             # Make each focus vector the same length 
    my $d  = $b * abs($a);             #   so that dot or cross will measure angle          
  
    my $A  = $c^$s;                    # Angle of Reflection vs
    my $B  = $d^$s;                    # Angle of Incidence
  
    my $z  = $A - $B;                  # Compare angle of incidence to angle of reflection
  
#      $y  = sqrt($r*$r - $r*$r*$x*$x / ($R*$R));  # Ellipse
#      $f  = sqrt($R*$R - $r*$r);      # Focus
#      $z  = eval($z);                 # Substitute for f,y
  
    $test->($z, "Angle of incidence equals angle of reflection via dot product with normal to tangent");
   }

#______________________________________________________________________
# Angle of incidence equals angle of reflection via dot product with
# tangent vector using optimized substitutions.
# NB: A+B not A-B.                
#______________________________________________________________________

   {my ($i, $r, $R, $f, $x, $y) = symbols(qw(i r R f x y));

       $r  = sqrt($R*$R - $f*$f);      # Focus
       $y  = sqrt($R*$R-$f*$f - $x*$x +$f*$f*$x*$x / ($R*$R));  # Ellipse: rr=RR-ff
  
    my $p  = $x + $i * $y;             # x,y point on locus of ellipse
    my $s  = $i*$x*$r*$r - $y*$R*$R;   # Tangent at locus
  
    my $a  = $p - $f;                  # Vector from Focus to locus
    my $b  = $p + $f;                  # Vector from other Focus to locus
  
    my $c  = $a * abs($b);             # Make each focus vector the same length 
    my $d  = $b * abs($a);             #   so that dot or cross will measure angle          
  
    my $A  = $c ^ $s;                  # Angle of Reflection vs
    my $B  = $d ^ $s;                  # Angle of Incidence
  
    my $z  = $A + $B;                  # Compare angle of incidence to angle of reflection
                                       # NB: Need A+B here due to antisymmetry of cosine around pi/2
#      $r  = sqrt($R*$R - $f*$f);      # Focus
#      $y  = sqrt($R*$R-$f*$f - $x*$x +$f*$f*$x*$x / ($R*$R));  # Ellipse: rr=RR-ff
#      $z  = eval($z);                 # Substitute for r,y
  
    $test->($z, "Angle of incidence equals angle of reflection via dot product with tangent");
   }

#______________________________________________________________________
# Angle of incidence equals angle of reflection via cross product with
# normal to tangent vector.
#______________________________________________________________________

   {my ($i, $r, $R, $f, $x, $y) = symbols(qw(i r R f x y));

       $r  = sqrt($R*$R - $f*$f);      # Focus
       $y  = sqrt($R*$R-$f*$f - $x*$x +$f*$f*$x*$x / ($R*$R));  # Ellipse: rr=RR-ff
  
    my $p  = $x + $i * $y;             # x,y point on locus of ellipse
    my $s  = $x*$r*$r + $y*$R*$R*$i;   # Normal to tangent at locus
  
    my $a  = $p - $f;                  # Vector from Focus to locus
    my $b  = $p + $f;                  # Vector from other Focus to locus
  
    my $c  = $a * abs($b);             # Make each focus vector the same length 
    my $d  = $b * abs($a);             #   so that dot or cross will measure angle          
  
    my $A  = $c x $s;                  # Angle of Reflection vs
    my $B  = $d x $s;                  # Angle of Incidence
  
    my $z  = $A - $B;                  # Compare angle of incidence to angle of reflection
  
 #     $y  = sqrt($r*$r - $r*$r*$x*$x / ($R*$R));  # Ellipse
 #     $f  = sqrt($R*$R - $r*$r);      # Focus
 #     $z  = eval($z);                 # Substitute for f,y
  
    $test->($z, "Angle of incidence equals angle of reflection via cross product with normal to tangent");
   }

#______________________________________________________________________
# Angle of incidence equals angle of reflection via cross product with
# tangent vector.
#______________________________________________________________________

   {my ($i, $r, $R, $f, $x, $y) = symbols(qw(i r R f x y));

       $r  = sqrt($R*$R - $f*$f);      # Focus
       $y  = sqrt($R*$R-$f*$f - $x*$x +$f*$f*$x*$x / ($R*$R));  # Ellipse: rr=RR-ff
  
    my $p  = $x + $i * $y;             # x,y point on locus of ellipse
    my $s  = $i*($x*$r*$r + $y*$R*$R*$i);   # Normal to tangent at locus
  
    my $a  = $p - $f;                  # Vector from Focus to locus
    my $b  = $p + $f;                  # Vector from other Focus to locus
  
    my $c  = $a * abs($b);             # Make each focus vector the same length 
    my $d  = $b * abs($a);             #   so that dot or cross will measure angle          
  
    my $A  = $c x $s;                  # Angle of Reflection vs
    my $B  = $d x $s;                  # Angle of Incidence
  
    my $z  = $A - $B;                  # Compare angle of incidence to angle of reflection

#      $y  = sqrt($r*$r - $r*$r*$x*$x / ($R*$R));  # Ellipse
#      $f  = sqrt($R*$R - $r*$r);      # Focus
#      $z  = eval($z);                 # Substitute for f,y
  
    $test->($z, "Angle of incidence equals angle of reflection via cross product with tangent");
   }

#______________________________________________________________________
# Return number of errors.
#______________________________________________________________________

  return [$errors, 'Ellipse'];
 }

#______________________________________________________________________
# General tests.
#______________________________________________________________________

sub generalTests()
 {my $errors = 0;
 
#______________________________________________________________________
# Test each expression.
#______________________________________________________________________

  my $test = sub ($$$)
   {my ($t, $a, $b) = @_;
    my $c = $a-$b;

    if ($c == 0)
     {print "OK $t\n";
     }
    else
     {print "ERROR :$t! Following two expressions not equal!\n$a\n\n$b\n\n",
         "Difference:\n$c\n\n";
      ++$errors;
     }
   };

#______________________________________________________________________
# Test these expressions.
#______________________________________________________________________

  my ($a, $b, $x, $y, $i, $o, $c2, $c3) = symbols(qw(a b x y i 1 2 3));

#______________________________________________________________________
# Complex number basics.
#______________________________________________________________________

  $test->('aa', $i x 1,  1);
  $test->('ab', $i^1,    0);
  $test->('ac', $i^$i,   1);
  $test->('ad', !$i,     $i);
  $test->('ae', abs $i,  1);
  $test->('af', re $i,   0);
  $test->('ag', im $i,   1);
  $test->('ah', re $o,   1);
  $test->('ai', im $o,   0);
  $test->('aj', ~($a+$b) == ~ $a + ~ $b,                           1);     # Conjugation distributes over addition
  $test->('ak', ~($a*$b) == ~ $a * ~ $b,                           1);     # Conjugation distributes over times
  $test->('al', ~($a**2) == (~ $a)**2,                             1);     # Conjugation distributes over power
  $test->('am',  abs(!($x+$y*$i)),                                 1);     # Length of unit vector
  $test->('an',  abs(($a+$i*sqrt(1-$a*$a))*($b+$i*sqrt(1-$b*$b))), 1);
  $test->('ao',  abs($a+$i*$b)*abs($x+$i*$y), abs(($a+$i*$b)*($x+$i*$y))); # Length of product = product of lengths
  my $q = ($i+1) x ($i-1); # For some strange reason, does not work in parameter list
  $test->('ap', $q,  2);
  $test->('aq', (1+$i)^(-1+$i),       0);

#______________________________________________________________________
# Exp.
#______________________________________________________________________
   
  $test->('ea',  exp($x)*exp($i*$x)*exp($x)*exp(-$i*$x)-exp(2*$x), 0);
  $test->('eb', 1+$o+'1/2'*$o**2+'1/6'*$o**3+'1/24'*$o**4+'1/120'*$o**5+
               '1/720'*$o**6+'1/5040'*$o**7+'1/40320'*$o**8,
               '109601/40320'); # Approximate exp(1) 

#______________________________________________________________________
# Polynomials.
#______________________________________________________________________
   
  $test->('pa', ($x+$x*$x)*$y/($x*$y),                  1+$x);
  $test->('pb', (2*$a*$b**20) / (4*$b**19+4*$b**19),     ($a*$b)/4);
  $test->('pc', (4*$b+4*$a*$b)/(4*$b+4*$a*$b),          1/($a+1)*$a+1/($a+1));
  $test->('pd', (($x+$i*sqrt(1-$x*$x))**3 -
                ($x+$i*sqrt(1-$x*$x))**2)->im->isZero == -1-2*$x+4*$x**2, 1);            # Side of pentagon crosses -x axis in  unit circle.  
  $test->('pe', (sqrt($c2)+sqrt($c3))**4-10*(sqrt($c2)+sqrt($c3))**2,    -1);            # Polynomial with sqrt(2)+sqrt(3) as a zero
  $test->('sf', ($a**16-1)/($a**8-1),                   ($a**8+1));
  $test->('pg', ($a+1)**11 / (1+$a)**12,                1/($a+1));
  $test->('ph', ($a**2 + $b**2)/($a**2 + $b**2),        1);
  $test->('pi', ($a**2 + 2*$a*$b +$b**2) / ($a+$b),     $a+$b);

#______________________________________________________________________
# Square roots.
#______________________________________________________________________
   
  $test->('sc', sqrt($a+1) / sqrt(1+$a),                1);
  $test->('sd', 2*$b**2*sqrt($a+1) / (4*$b*sqrt(1+$a)), $b/2);
  $test->('se', 1/sqrt(1+$a),                           1/sqrt(1+$a)); 
  $test->('sf', 1/sqrt(1+$a)**3,                        1/(sqrt(1+$a)+sqrt(1+$a)*$a));
  $test->('sg', sqrt($a+1)**3 / sqrt(1+$a)**3,          1);

#______________________________________________________________________
# Improvements pending.
#______________________________________________________________________

  $test->('za',  sqrt($a+1)**2 / sqrt(1+$a), sqrt(1+$a)); # Poor representation of #1

  return [$errors, 'General Tests'];
 }

#______________________________________________________________________
# Tests collected together.
#______________________________________________________________________

sub test()
 {my @e;
# import('symbols', BigInt=>1);
  push @e, generalTests();
  push @e, testEllipse();

  my $n = 0;
  for my $e(@e)
   {my ($c, $m) = @$e;
    print "OK:   $m\n"               unless $c; 
    print "FAIL: $c errors in: $m\n" if     $c;
    $n += $c;
   }
  print STDERR "No Errors\n"         unless $n;
  print STDERR "DANGER: $n errors\n" if     $n;
  $n; 
 }

#______________________________________________________________________
# Set up install
#______________________________________________________________________

sub install()
 {my $package = 'Math::Algebra::Symbols';

  print `mkdir i` unless -e 'i';
  print `rm -vr i/*`;
  print `pod2html.bat --infile=symbols.pm --outfile=symbols.html`;

# Make file
 
   my $t = << "END";
use ExtUtils::MakeMaker;

WriteMakefile
 (NAME		=> '$package',
  VERSION	=> '$symbols::VERSION',	
  ABSTRACT=> 'Symbolic Manipulation in Perl',
  AUTHOR 	=> 'PhilipRBrenan\@yahoo.com',
 );
END

  my $o;
  open  $o, ">i/Makefile.PL";
  print $o $t;
  close $o;

# Copy and edit files

  for my $f([qw(symbols.pm Symbols.pm)], [qw(test.pl test.pl)])
   {my ($if, $of) = @$f;
    my ($i,  $o);

    open $i, "<$if";
    my @l = <$i>;
    close $i;

    for (@l)
     {s/^package symbols/package $package/;
      s/^use symbols/use $package/;
      s/^ use symbols/ use $package/;
     }
 
    open  $o, ">i/$of";
    print $o join('', @l);
    close $o;
   }

# Create archive

  print `tar -cvz -C i -f i/symbols-$symbols::VERSION.tar.gz Symbols.pm test.pl Makefile.PL`;
  `rm *.x~~ symbols.htmlpod.pl`;
  print "Package Installer created successfully\n"; 
 }

#______________________________________________________________________
# Perform tests or install if necessary
#______________________________________________________________________

unless (caller())
 {unless (scalar(@ARGV))
   {test() unless caller();
   }
  else 
   {my @p = @ARGV;
    if ($p[0] =~ /install/i)
     {&install();
     }
   }
 }

#______________________________________________________________________
# Package installed successfully.
#______________________________________________________________________

1;

#______________________________________________________________________
# User guide follows.
#______________________________________________________________________
 
__END__

=head1 NAME

Math::Algebra::Symbols - Symbolic Manipulation in Perl

=head1 SYNOPSIS

 use Math::Algebra::Symbols;

 $x = symbols(qw(x));

 $y = ($x**8 - 1) / ($x-1);

 print "y=$y\n";

 # y=1+$x+$x**2+$x**3+$x**4+$x**5+$x**6+$x**7

=head1 DESCRIPTION

This package supplies a set of functions and operators to manipulate
operator expressions algebraically. These expressions are constructed
from L</Symbols> and L</Operators> using the familiar Perl syntax.

=head2 Symbols

Symbols are created with the exported B<symbols()> constructor routine:

 use Math::Algebra::Symbols;

 my ($x, $y, $i, $o) = symbols(qw(x y i 1));

 print "$x $y $i $o\n";

 # $x $y $i 1

The B<symbols()> routine constructs references to symbolic variables and
symbolic constants from a list of names and integer constants.

The special symbol B<i> is recognized as the square root of -1.

In the example above, two symbolic variables: B<$x>, B<$y> are created and
two symbolic constants: B<$i> with value square root of -1 and B<$o>
with value 1.

If you wish to use a different name for the constructor routine, say
B<S>:

 use Math::Algebra::Symbols symbols=>'S';

 my ($x, $y, $i, $o) = S(qw(x y i 1));

 print "$x $y $i $o\n";

 # $x $y $i 1

If you wish to use big integers from L<Math::BigInt>:

 use Math::Algebra::Symbols BigInt=>1;

 my $z = symbols('1234567890987654321/1234567890987654321');

 print "$z\n";

 # 1

=head2 Operators

L</Symbols> can be combined with L</Operators> to create symbolic expressions:

=head3 Arithmetic operators

=over                                    

=item Arithmetic Operators: B<+> B<-> B<*> B</> B<**> 

 use Math::Algebra::Symbols;

 ($x, $y) = symbols(qw(x y));

 $z = ($x**2-$y**2)/($x-$y);

 print "$z\n";

 # $x+$y

The power operator B<**> expects an integer constant on its right hand side.

The auto assign versions of these operators: B<+=> B<-=> B<*=> B</=> all
work courtesy of Perl Auto-Magical Operator Generation.

=item Square root Operator: B<sqrt>       

 use Math::Algebra::Symbols;

 $x = symbols(qw(x));

 $z = sqrt(-$x**2);

 print "$z\n";

 # $i*$x

=back

=head3 Relational operators

=over                                    

=item Relational operator: B<==> 

 use Math::Algebra::Symbols;

 ($x, $y) = symbols(qw(x y));

 $z = ($x**2-$y**2)/($x+$y) == $x - $y;

 print "$z\n";

 # 1

The relational equality operator B<==> compares two symbolic expressions
and returns TRUE(1) or FALSE(0) accordingly.

=item Relational operator: B<eq> 

 use Math::Algebra::Symbols;

 ($x, $v, $t) = symbols(qw(x v t));

 $z = ($x / $t eq $v)->solve(qw(x in terms of v t));

 print "x=$z\n";

 # x=$v*$t

The relational operator B<eq> is in fact a synonym for the minus B<->
operator, with the expectation that later on the L<solve()|/Solving equations>
function will be used to simplify and rearrange the equation.

=back

=head3 Complex operators

=over

=item Complex operators: the B<dot> operator: B<^>       

 use Math::Algebra::Symbols;

 ($a, $b, $i) = symbols(qw(a b i));

 $z = ($a+$i*$b)^($a-$i*$b);

 print "$z\n";

 # $a**2-$b**2

Note the use of brackets.  The B<^> operator has low priority.

The B<^> operator treats its left hand and right hand arguments as
complex numbers, which in turn are regarded as two dimensional vectors
to which the vector dot product is applied.

=item Complex operators: the B<cross> operator: B<x>       

 use Math::Algebra::Symbols;

 ($x, $i) = symbols(qw(x i));

 $z = $i*$x x $x;

 print "$z\n";

 # $x**2

The B<x> operator treats its left hand and right hand arguments as
complex numbers, which in turn are regarded as two dimensional vectors
defining the sides of a parallelogram. The B<x> operator returns the
area of this parallelogram.

Note the space before the B<x>, otherwise Perl is unable to disambiguate
the expression correctly.

=item Complex operators: the B<conjugate> operator: B<~>       

 use Math::Algebra::Symbols;

 ($x, $y, $i) = symbols(qw(x y i));

 $z = $x+$i*$y;

 print ~$z, "\n";

 # $x-$i*$y

The B<~> operator returns the complex conjugate of its right hand side.

=item Complex operators: the B<modulus> operator: B<abs>       

 use Math::Algebra::Symbols;

 ($x, $i) = symbols(qw(x i));

 $z = abs($x+$i*$x);

 print "$z\n";

 # sqrt(2)*$x

The B<abs> operator returns the modulus (length) of its right hand side.

=item Complex operators: the B<unit> operator: B<!>       

 use Math::Algebra::Symbols;

 $i = symbols(qw(i));

 print !$i, "\n";

 # $i

The B<!> operator returns a complex number of unit length pointing in
the same direction as its right hand side.

=back

=head2 Functions

=head3 Complex functions

=over

=item Complex functions: B<re> and B<im>       

 use Math::Algebra::Symbols;

 ($x, $i) = symbols(qw(x i));

 $R = re $i*$x;
 $I = im $i*$x;

 print "$R $I\n";

 # 0 $x

The B<re> and B<im> functions return an expression which represents the
real and iumaginary parts of the expression, assuming that symbolic
variables represent real numbers.

=back

=head3 Functions for simplifying and solving equations

=over

=item Simplifying equations: B<sub()>

 use Math::Algebra::Symbols;
 
 ($x, $y) = symbols(qw(x y));
 
 $e = 1+$x+'1/2'*$x**2+'1/6'*$x**3+'1/24'*$x**4+'1/120'*$x**5; #1

 $e2 = $e->sub(x=>$y**2, z=>2);   #2
 $e3 = $e->sub(x=>1);             #3

 print "$e2\n\n$e3\n\n";

 # 1+$y**2+1/2*$y**4+1/6*$y**6+1/24*$y**8+1/120*$y**10

 # 163/60

The quotes in line B<#1> are used to stop Perl evaluating the constant
fractions as decimals, they are instead handed directly to the L</Symbols>
constructor for interpretation as symbolic fractions.

The B<sub()> function example on line B<#2> demonstrates replacing
variables with expressions. The replacement specified for B<z> has no
effect as B<z> is not present in this equation.

Line B<#3> demonstrates the resulting rational fraction that arises when
all the variables have been replaced by constants. This package does not
convert fractions to decimal expressions in case there is a loss of
acuracy, however:

 $e3 =~ /^(\d+)\/(\d+)$/;
 $result = $1/$2;

or similar will produce approximate results.

=item Solving equations: B<solve()>

 use Math::Algebra::Symbols;

 ($x, $v, $t) = symbols(qw(x v t));

 $z = ($v eq $x / $t)->solve(qw(x in terms of v t)); #1

 print "x=$z\n";

 # x=$v*$t

B<solve()> assumes that the equation on the left hand side is equal to
zero, applies various simplifications, then attempts to rearrange the
equation to obtain an equation for the first variable in the parameter
list assuming that the other terms mentioned in the parameter list are
known constants. There may of course be other unknown free variables in
the equation to be solved: the proposed solution is automatically tested
against the original equation to check that the proposed solution
removes these variables, an error is reported if it does not.

=back

=head2 Example Expressions:

 use Math::Algebra::Symbols;

 ($a, $b, $x, $y, $i) = symbols(qw(a b x y i));

   print $i x 1, "\n";              # Cross product
 # 1

   print $i^1,   "\n";              # Dot product - different vectors
 # 0

   print $i^$i,  "\n";              # Dot product - same vector
 # 1

   print abs $i, "\n";              # Length of unit vector
 # 1

   print ~($a+$b) == ~$a+~$b, "\n"; # Conjugation is distributive
 # 1                                  over addition

   print ~($a*$b) == ~$a*~$b, "\n"; # Conjugation is distributive
 # 1                                  over multiplication

   print ~($a**2) == (~$a)**2,"\n"; # Conjugation is distributive
 # 1                                  over power

   print  abs(!($x+$y*$i))==1,"\n"; # Length of unit vector
 # 1

   print                            # Length of product = product of lengths
         abs($a+$i*$b)*abs($x+$i*$y) ==
        abs(($a+$i*$b)*   ($x+$i*$y)), "\n";
 # 1  


=head2 Example of Equation Solving: the focii of a hyperbola:

 use Math::Algebra::Symbols;
 ($a, $b, $x, $y, $i, $o) = symbols(qw(a b x y i 1));

 print
 "Hyperbola: Constant difference between distances from focii to locus of y=1/x",
 "\n  Assume by symmetry the focii are on ",
 "\n    the line y=x:                     ",  $f1 = $x + $i * $x,
 "\n  and equidistant from the origin:    ",  $f2 = -$f1,
 "\n  Choose a convenient point on y=1/x: ",  $a = $o+$i,
 "\n        and a general point on y=1/x: ",  $b = $y+$i/$y,
 "\n  Difference in distances from focii",
 "\n    From convenient point:            ",  $A = abs($a - $f2) - abs($a - $f1),  
 "\n    From general point:               ",  $B = abs($b - $f2) + abs($b - $f1),
 "\n\n  Solving for x we get:            x=", ($A eq $B)->solve(qw(x)),
 "\n                         (should be: sqrt(2))",                        
 "\n  Which is indeed constant, as was to be demonstrated\n";

This example demonstrates the power of symbolic processing by finding the
focii of the curve B<y=1/x>, and incidentally, demonstrating that this curve
is a hyperbola.

=head1 EXPORT

The package exports the constructor, which by default is called

L</Symbols>()

However, this can be overriden on the use statement:

 use Math::Algebra::Symbols symbols=>S

which would instead request that the constructor routine
should be called B<S()> instead.

=head1 AUTHOR

Philip R Brenan at B<philiprbrenan@yahoo.com>

=cut


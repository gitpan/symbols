#!perl -W
#______________________________________________________________________
# Symbolic algebra.
# PhilipRBrenan@yahoo.com, 2004.
#______________________________________________________________________

use Math::Algebra::Symbols;
$errors = 0;

sub init
 {($a, $b, $x, $y, $R, $f, $i, $o) = symbols(qw(a b x y R f i 1))
 }

#______________________________________________________________________
# Symbolic algebra.
#______________________________________________________________________

init();
&test(1,  [ #----------------------------------------------------------

"Algebraic operations:\n\n", 
  $x**8 - 1,                         # Symbolic multiplication
 ($x**8 - 1) /  ($x**4+1),           # Polynomial division
 ($x**8 - 1) /  ($x-1),                 
 ($x**2 - 1) / (($x-1) * ($x+1)),                        
 ($x + $i)**8,                       # i = sqrt(-1)
  abs(!($x+$y*$i)*!($a+$b*$i)) == 1, # Length of product of units 

], << 'END' #----------------------------------------------------------

Algebraic operations:
  -1+$x**8
  -1+$x**4
  1+$x+$x**2+$x**3+$x**4+$x**5+$x**6+$x**7
  1
  1-8*$i*$x-28*$x**2+56*$i*$x**3+70*$x**4-56*$i*$x**5-28*$x**6+8*$i*$x**7+$x**8
  1

END
);          #----------------------------------------------------------

#______________________________________________________________________
# Ellipse: Focus Trip: Distance from focus to locus to other focus
#______________________________________________________________________

print "\nConic invariants:\n";

init();
&test(2,  [ #----------------------------------------------------------

"Ellipse:\n",
"  Locus:          y=",
      $y = sqrt($R*$R-$f*$f - $x*$x+$f*$f*$x*$x / ($R*$R)),

"  At x=0:         y=",     $y->sub(x=>0),
"  At x=1 f=1 R=2: y=",     $y->sub(x=>1, f=>1, R=>2),
"  at x=R:         y=",     $y->sub(x=>$R), 

"\nFocus trip: distance from focus to locus to other focus =\n",

  $z =  abs($x+$i*$y - $f) + abs($x+$i*$y + $f),
 ($z == 2*$R ? "  Equals" : "  DOES NOT EQUAL"). " 2R\n",

], << 'END' #----------------------------------------------------------

Ellipse:
  Locus:          y=sqrt($R**2+$R**-2*$x**2*$f**2-$f**2-$x**2)
  At x=0:         y=sqrt($R**2-$f**2)
  At x=1 f=1 R=2: y=3/2
  at x=R:         y=0

Focus trip: distance from focus to locus to other focus =
  sqrt($R**2+$R**-2*$x**2*$f**2-2*$x*$f)+sqrt($R**2+$R**-2*$x**2*$f**2+2*$x*$f)
  Equals 2R
END
);          #----------------------------------------------------------

#______________________________________________________________________
# Parabola:  Focusing to infinity
#______________________________________________________________________

init();
&test(3,  [ #----------------------------------------------------------

"Parabola: Focussing to infinity\n",
"  From focus to locus:    ",        $a = $x + $i * $x**2 - $i/4,
"  Vertical of same length:",        $b = $i * abs($a),
"  Tangent vector to locus:",        $d =  1 + 2*$x*$i,
"  Compare angles via dot: ",        $z = ($a ^ $d) - ($b ^ $d),
($z == 0 ? "  Focusses to infinity\n"
         : "  DOES NOT FOCUS TO INFINITY\n"),

], << 'END' #----------------------------------------------------------

Parabola: Focussing to infinity
  From focus to locus:      -1/4*$i+$x+$i*$x**2
  Vertical of same length:  $i*sqrt(1/16+1/2*$x**2+$x**4)
  Tangent vector to locus:  1+2*$i*$x
  Compare angles via dot:   1/2*$x-2*sqrt(1/16+1/2*$x**2+$x**4)*$x+2*$x**3
  Focusses to infinity

END
);          #----------------------------------------------------------

#______________________________________________________________________
# Parabola: Distance from focus to locus to directrix
#______________________________________________________________________

init();
&test(4,  [ #----------------------------------------------------------

"Parabola:  Distance from focus to locus to directrix\n",
"  From focus to locus:            ",      $a = $x + $i * $x**2 - $i/4,
"  From focus to locus squared:    ",      $A = $a^$a,
"  From locus to directrix squared:",      $B = ($x**2+'1/4')**2, 

($A == $B ? "  Equal lengths\n" : "  UNEQUAL LENGTHS\n"),

], << 'END' #----------------------------------------------------------

Parabola:  Distance from focus to locus to directrix
  From focus to locus:              -1/4*$i+$x+$i*$x**2
  From focus to locus squared:      1/16+1/2*$x**2+$x**4
  From locus to directrix squared:  1/16+1/2*$x**2+$x**4
  Equal lengths

END
);          #----------------------------------------------------------

#______________________________________________________________________
# Hyperbola: Constant difference between distances from focii to locus.
#______________________________________________________________________

init();
&test(5,  [ #----------------------------------------------------------

"Hyperbola:  Constant difference between distances from focii to locus of y=1/x\n",
"  Assume by symmetry the focii are on\n",
"    the line y=x:                    ",   $f1 = $x + $i * $x,
"    and equidistant from the origin: ",   $f2 = -$f1,
"\n  Choose a convenient point on y=1/x:", $a = $o+$i,
"    and another point:               ",   $b = $y+$i/$y,
"\n  Difference in distances from focii\n",
"    From first point:                ",   $A = abs($a - $f2) - abs($a - $f1),  
"    From second point:               ",   $B = abs($b - $f2) + abs($b - $f1),
"\n  Assuming the difference is constant,\n",
"    and solving for x, we get:       x=", ($A eq $B)->solve(qw(x)),                        
"\n  Which is indeed constant, as was to be demonstrated\n",                                                

], << 'END' #----------------------------------------------------------

Hyperbola:  Constant difference between distances from focii to locus of y=1/x
  Assume by symmetry the focii are on
    the line y=x:                      $x+$i*$x
    and equidistant from the origin:   -$x-$i*$x

  Choose a convenient point on y=1/x:  1+$i
    and another point:                 $y+$i/$y

  Difference in distances from focii
    From first point:       sqrt(2+4*$x+2*$x**2)
                           -sqrt(2-4*$x+2*$x**2)

    From second point:      sqrt(2*$x**2+2/$y*$x+2*$y*$x+$y**-2+$y**2)
                           +sqrt(2*$x**2-2/$y*$x-2*$y*$x+$y**-2+$y**2)

  Assuming the difference is constant,
    and solving for x, we get:       x=sqrt(2)

  Which is indeed constant, as was to be demonstrated
END
);          #----------------------------------------------------------

#______________________________________________________________________
# Execute test and check results
#______________________________________________________________________

sub test($$$)
 {my $t = shift;       # Test number
  my @a = @{shift()};  # Tests
  my $b = shift();     # Expected results
  my $l = '';

  for my $e(@a)
   {$l .= "  $e\n", next if ref($e) or $e =~ /^\d+$/;
    $l .= $e;
   }
  $l =~ s/\=\ \ /\=/g;

  print "\nTest $t\n$l\nTest ";

  my $c = $b;
     $c =~ s/\s+//sg;
     $l =~ s/\s+//sg;

  print("$t: Fail:\n\n$b\n"), ++$errors unless $l eq $c;
  print "$t: OK\n"                      if     $l eq $c;
 }

#______________________________________________________________________
# Check errors over all
#______________________________________________________________________

print "$errors errors\n" if     $errors;
print "No errors\n"      unless $errors;

return $errors if caller();

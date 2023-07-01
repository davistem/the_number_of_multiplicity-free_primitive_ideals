#########################################
## SETUP
#########################################

TYPE := "E8";

type := [TYPE[1]];
rk := EvalString([TYPE[2]]); #the rank of g
g_rat := SimpleLieAlgebra(type,rk,Rationals); #rational version for root calcs
R := PolynomialRing(Rationals,2*Dimension(g_rat));
g := SimpleLieAlgebra(type,rk,R); #Simply connected simple Lie algebra over R=[x_1,...,x_(2.dim g)]
x := IndeterminatesOfPolynomialRing(R);
t := x[Dimension(g_rat)+1];
B := Basis(g); # Chevalley basis of g
B_rat := Basis(g_rat);

zero := 0 * x[1];
roots := RootSystem(g_rat);
posroots := PositiveRoots(roots);
nrpos := Length(posroots);
negroots := NegativeRoots(roots);
S := SimpleSystem(roots);

# rootcoeffs[i] is a vector giving the coefficients of the ith root in terms of simple roots in Bourbaki=GAP ordering
rootcoeffs := []; 
for i in [1..nrpos] do
  rootcoeffs[i] := SolutionMat(S,posroots[i]);
  rootcoeffs[i + Length(posroots)] := SolutionMat(S,negroots[i]);
od;

#########################################
## Custom stuff for calculating g_e(r) etc
#########################################

# produce generic element of g for prescribed root vectors; u
generic_element_by_roots := function(list)
local a,i;
a := 0 * B[1];
for i in list do
  a := a + x[i]*B[i];
od;
return a;
end;;

# produce completely generic element in g 
generic_element := function()
local f;
f := generic_element_by_roots([1..Dimension(g)]);
return f;
end;;

  
# degree of a polynomial
degree := function(f)
local deg,leadmon,i;
if (f=0*x[1]) then return -infinity; fi;
leadmon:=LeadingMonomial(f);
deg:=0;
for i in [1..Length(leadmon)/2] do
  deg:=deg+leadmon[2*i];
od;
return deg;
end;;

# Replace all B-coefficients y[i] of elt in g by substituting out the first non-constant term in both f and y[i] from y[i]; e.g.
#  gap> elt:=Sum(List([1..3],i->x[i]^2*B[i]));
#   (x_1^2)*v.1+(x_2^2)*v.2+(x_3^2)*v.3
# gap> linear_substitute(elt,x[1]-x[2]-2);
#   (x_2^2+4*x_2+4)*v.1+(x_2^2)*v.2+(x_3^2)*v.3

linear_substitute := function(elt,f)
local coef,coeffs,g,i,index,result;
index := 1;
coef := PolynomialCoefficientsOfPolynomial(f,index);
while (Length(coef)<>2 or not(degree(coef[2])=0) ) do
  index := index + 1;
  if index = Length(x)+1 then
    return elt;
  fi;
  coef := PolynomialCoefficientsOfPolynomial(f,index);
od;
g := -(f-coef[2]*x[index])/coef[2];   
result := 0 * B[1];
coeffs := Coefficients(B,elt);
for i in [1..Length(B)] do
  result := result + Value(coeffs[i],[index],[g])*B[i];
od;
return result;
end;;


# Fix e and y; perform a linear substitution on y so that e*f =[e,f]= y. 
tweak := function(e,f,y)
local test,i,j,coeffs,testcoeffs;
test := (e*f) - y; 
coeffs := Coefficients(B,0*B[1]);
testcoeffs := Coefficients(B,test);
# goal: make test = 0 
i := checkzeros(coeffs,testcoeffs);
while (i>0) do
  f := linear_substitute(f,testcoeffs[i]);
  test := (e*f) - y; 
  testcoeffs := Coefficients(B,test);
  i := checkzeros(coeffs,testcoeffs);
od;
return f;
end;;

# Fix h; perform an ls on f to make [h,f] = 3*f. 
tweak3 := function(h,f)
local test,i,j,coeffs,testcoeffs;
test := (h*f) - 3*f; 
coeffs := Coefficients(B,0*B[1]);
testcoeffs := Coefficients(B,test);
# goal: make test = 0 
i := checkzeros(coeffs,testcoeffs);
while (i>0) do
  f := linear_substitute(f,testcoeffs[i]);
  test := (h*f) - 3*f; 
  testcoeffs := Coefficients(B,test);
  i := checkzeros(coeffs,testcoeffs);
od;
return f;
end;;

#########################################
## Actual calcs
#########################################

#########################################
#CASE 1
#########################################

#From 3.1, e is given, with f forming a standard sl2

e:=B[1]+B[2]+B[4]+B[5]+B[6]+B[7];
f:=B[121]+5*B[122]+8*B[124]+9*B[125]+8*B[126]+5*B[127];
h:=e*f;

#Check an sl2:

f*e*e+2*e=0*B[1];

#Setup highest root sl2, which commutes with <e,f>

ea0:=B[120]; fa0:=B[240]; ha0:=ea0*fa0;

#And other commuting sl2 in ge0.

gen:=generic_element();

ce:=tweak(e,gen,0*B[1]); #make generic elt commute with e; this is now a generic element of the centraliser g_e
ce0:=tweak(h,ce,0*B[1]); #make generic elt commute with h; this is now a generic element of g_e(0)

#From ce one can read off the sl_2 e',f',h':

edash:=-B[69]+B[70]-B[71];
fdash:=-B[189]+B[190]-B[191];
hdash:=edash*fdash;

fdash*edash*edash+2*edash=0*B[1];

#we also need the long root sl_2:

e1:=B[1];
f1:=B[121];
h1:=e1*f1;

#... and moreover u, v, u', v' which are in g_e(3)

ce3:=tweak3(h,ce);

# from which one reads off:

u:=B[94]-B[95]+B[96];
udash:=B[45]-2*B[46]+B[48]-B[49]; # NB, the Gilkey-Seitz structure constants as used by Lawther-Testerman are not the same as those used in GAP.

# we check u and udash are correct since they have correct weights for hdash and ha0
hdash*udash=udash;
ha0*udash=0*B[1];

ha0*u=u;
hdash*u=0*B[1];

# and then the images under fa0 and fdash
v:=u*fa0;
vdash:=udash*fdash;

# with this *** particular choice ***  of the basis for the two commuting sl2s we get
u*v+udash*vdash=0*B[1];

# now we want uminus, vminus. From u*f*f*f, and from u*f*f*f*e*e*e [etc] we guess
uminus:=u*f*f*f*(-One(R)/36);
vminus:=v*f*f*f*(-One(R)/36);
udminus:=udash*f*f*f*(-One(R)/36);
vdminus:=vdash*f*f*f*(-One(R)/36);

# Calculating A
A1:=(e*(e*(uminus*(f-f1)))-3*(e*uminus)*(h-h1))
*
(e*(e*(vminus*(f-f1)))-3*(e*vminus)*(h-h1));

A:=CoefficientsOfUnivariatePolynomial(
TraceMat(
AdjointMatrix(B,e)*AdjointMatrix(B,A1)
)/60)[1];

# Calculating B

B1:= 8*(udash*e1)*f1-3*(h-h1)*((h-h1)*udash - 2*udash);

BB:=CoefficientsOfUnivariatePolynomial(
TraceMat(
AdjointMatrix(B,vdminus)*AdjointMatrix(B,B1)
)/60)[1];

#

Print("Case 1: 36*(A+B) = ",36*(A+BB),", with prime divisors ", PrimePowersInt(36*(A+BB)),"\n");


#########################################
#CASE 2
#########################################

e:=B[1]+B[2]+B[3]+B[5]+B[7]+B[8]+B[10]+B[12];
	f:=[6,1,10,1,2,2,6,6]*B{[121,122,123,125,127,128,130,132]};
h:=e*f;

#check
h*e=2*e;
h*f=-2*f;

### get g_e(0)

gen:=generic_element();

ce:=tweak(e,gen,0*B[1]); #make generic elt commute with e
ce0:=tweak(h,ce,0*B[1]); #make generic elt commute with h

### from this get

edash:=2*B[85]-B[86]-B[87]+B[88];
fdash:=B[205]-B[206]-B[207]+2*B[208];
hdash:=edash*fdash;

#check

hdash*edash=2*edash;
hdash*fdash=-2*fdash;


#u and v from ge_3

ce3:=tweak3(h,ce);

u:=3*B[54]-B[57]-B[58]-2*B[59]-B[60]-B[63];
v:=fdash*u;

uminus:=-u*f*f*f*(One(R)/36);
vminus:=-v*f*f*f*(One(R)/36);

#e0andh0

e0:=B[2]+B[5]+B[7]+B[8];
h0:=e0*f;
f0:=(1/2*One(R))*e0*f*f;


# CALC OF INNER PRODUCT

AA:=(e*(e*(uminus*(f+f0)))-3*(e*uminus)*(h-h0))
*
(e*(e*(vminus*(f+f0)))-3*(e*vminus)*(h-h0));

A:=CoefficientsOfUnivariatePolynomial(
TraceMat(
AdjointMatrix(B,e)*AdjointMatrix(B,AA)
)/60)[1];

Print("Case 2 first line: A = ",A,", with prime divisors ", PrimePowersInt(A),"\n");

# SECOND LINE

AA2:=(e*(e*(e*uminus)))*(f+f0);
BB2:=e*(e*(vminus*(f+f0))) - 3*(e*vminus)*(h-h0);

A2:=CoefficientsOfUnivariatePolynomial(
TraceMat(
AdjointMatrix(B,AA2)*AdjointMatrix(B,BB2)
)/60)[1];

Print("Case 2 second line: A = ",A2,", with prime divisors ", PrimePowersInt(A2),"\n");

# LAST LINE
#
AA3 := -3 * (
(e0*f) * ((e0*f) * u) - 4*(e0*f)*u + 3*u 
)
-8 *
(f0 * (e0* u) )
;

A3:=CoefficientsOfUnivariatePolynomial(
TraceMat(
AdjointMatrix(B,AA3)*AdjointMatrix(B,vminus)
)/60)[1];

Print("Case 2 last line: A = ",A3,", with prime divisors ", PrimePowersInt(A3),"\n");


# THRID TO LAST LINE
#
AA4 := -2 * (
u*e0*f0)
-3*(
(h-e0*f)*((h-e0*f)*u)
)
-6*(f0*(u*e0))
+6*(h-e0*f)*u
;

AA4:=CoefficientsOfUnivariatePolynomial(
TraceMat(
AdjointMatrix(B,AA4)*AdjointMatrix(B,vminus)
)/60)[1];

# MIDDLELINE
#
TraceMat(AdjointMatrix(B,2*u*e0)*AdjointMatrix(B,vminus*f0))
-3*TraceMat(AdjointMatrix(B,u)*AdjointMatrix(B,(h+e*f0)*((h+e*f0)*vminus)))
+3*TraceMat(AdjointMatrix(B,u*(e*f0))*AdjointMatrix(B,e*(f0*(vminus))))
-3*TraceMat(AdjointMatrix(B,u)*AdjointMatrix(B,(e*vminus)*(2*f+2*f0+2*f0-2*f0)));

AA4:=CoefficientsOfUnivariatePolynomial(
TraceMat(
AdjointMatrix(B,AA4)*AdjointMatrix(B,vminus)
)/60)[1];

TraceMat(AdjointMatrix(B,2*u*e0)*AdjointMatrix(B,vminus*f0))
-3*TraceMat(AdjointMatrix(B,u*(f+f0))*AdjointMatrix(B,(h+e*f0)*((h+e*f0)*vminus)))
+3*TraceMat(AdjointMatrix(B,u*(e*f0))*AdjointMatrix(B,e*(f0*(vminus))))
-3*TraceMat(AdjointMatrix(B,u)*AdjointMatrix(B,(e*vminus)*(2*f+2*f0+2*f0-2*f0)));


TraceMat(AdjointMatrix(B,u*(f+f0))*AdjointMatrix(B,e*(e*(vminus*(f+f0)))))
- 3* TraceMat(AdjointMatrix(B,u*(f+f0))*AdjointMatrix(B,(e*vminus)*(h-h0)));

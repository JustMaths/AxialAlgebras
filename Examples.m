/*

Some examples of use of the partial axial algebras code

*/
AttachSpec("ParAxlAlg.spec");

// You can set the verbose setting to 1, 2, 3, or 4.
// 4 gives lots of verbose and timing for individual parts
SetVerbose("ParAxlAlg", 2);

// We begin by getting some possible shapes for a group
G := Sym(4);
shapes := Shapes(G);
assert #shapes eq 12;
// There are 12 different shapes for Sym(4)

shapes[1];

// So the first shape has 6 axes and has shape 3A 2A
// We build an axial algebra

A:=PartialAxialAlgebra(shapes[1]);

// We can either run an automated routine to construct the axial algebra

// A := AxialReduce(A);

// Or we can run each bit individually:
// We begin by expanding the partial algebra

A := ExpandSpace(A);

// This has also finds relations coming from the odd part.

// Next we can try to expand the even part:

A := ExpandEven(A);

// If neither of these produce any further reduction, then we need to expand our algebra again

// There are also handy functions for seeing where we have got to with our reduction:

Dimension(A);

// The print for a partial algebra contains its dimension and the dimension of the space where the multiplication is known
A;

// This function lists the dimensions of all the eigenspaces for the axes.  The order is:
// 1, 0, 1/4, {1, 0}, {1, 1/4}, {0, 1/4}, {1, 0, 1/4}, 1/32
CheckEigenspaceDimensions(A);

// Given a partial axial algebra we can take elements of it and use normal operations

x := A.1 + A.4;
y := 5*A.2;

// Sometimes the multiplication will be defined and sometimes not.
x*y;

// This checks to see whether the multiplication is known or not and if so returns the answer

IsTimesable(x, y);

// The group connected to the algebra is known and can act on the elements

G := Group(A);
g := G!(1,2);
x*g;

// Equality and membership is implemented for elements and subspaces

x eq y;
A eq A;

x in A;
U := A`V;  // a vector subspace
x in U;

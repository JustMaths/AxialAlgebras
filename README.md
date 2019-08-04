# AxialAlgebras

This is a magma package for constructing axial algebra with a given Miyamoto group.  It implements the algorithm described in the paper "An expansion algorithm for constructing axial algebras" (https://arxiv.org/abs/1804.00587) by J. McInroy and S. Shpectorov.

## Getting started

Begin by cloning the repository by running

    git clone https://github.com/JustMaths/AxialAlgebras
    
or

    git clone git@github.com:JustMaths/AxialAlgebras.git
    
Now, when you are in the AxialAlgebras directory start magma and attach the spec file

    AttachSpec("ParAxlAlg.spec");
    
NB some of the commands will use python 2.7.

## Find some shapes

We want to build an axial algebra with a given Miyamoto group `G`.  Our algorithm works using a general action of a permutation group `G` on a set of axes.  We do not assume that this action is the action of `G` on some subset of its involutions.  That is, we do not assume a bijection between axes and involutions.  If you do just want this case

    shapes := Shapes(G);

will give you all shapes which correspond to actions of `G` on some subset of involutions (up to isomorphism).

For the general case, we begin with the action of a permutation group `G` on some putative axes.

    Ax := GSet(G);

Now, we want to find what addmissible tau maps there are

    taus := AdmissibleTauMaps(Ax);

This produces a sequence of tuples `<tau, stab>` where tau is a tau map and stab is its stabiliser in the normaliser of the action.  Let's pick the first one and find some shapes:

    tau, stab := Explode(taus[1]);
    shapes := Shapes(Ax, tau, stab);
    
`shapes` is now a sequence of all the possible shapes for the action `Ax` and tau map `tau` up to the action of `stab`.  A shape is a triple `<Ax, tau, sh>` where `sh` is a sequence describing the configuration of the 2-generated subalgebras.

## Building an axial algebra

Given a shape `shape := <Ax, tau, sh>` we can construct a partial axial algebra by using

    A := PartialAxialAlgebra(shape);

or

    A := PartialAxialAlgebra(Ax, tau, sh);

We can now try to complete it into a full axial algebra.

    A := AxialReduce(A);

There are a number of verbose settings, between 1 and 4, with 4 giving timing information for all the operations.

    SetVerbose("ParAxlAlg", 2);

## Properties

We have several functions to get information about our algebra `A`.  Firstly,

    A;

will print some information about the algebra.  For example:

    A complete axial algebra for the group S4, 3+6 axes, of shape 4A3A2B and dimension 25.

We can also get other information using the following commands:

    Group(A);
    MiyamotoGroup(A);
    Dimension(A);
    BaseField(A);
    BaseRing(A);
    Basis(A);

Note that `Group(A)` may be larger than the Miaymoto group.  We also have normal algebra functions for `A` and an action of the group:

    a := 5*A.1 + 6/7*A.2;
    b := 3*A.4;
    a + b;
    a*b;
    g := Random(Group(A));
    a*g;

We can get some other properties of `A`:

    mClosed(A);
    so, F := HasFrobeniusForm(A);
    Properties(A);

The last command will output a sequence of various properties including: primitivity, existence of Frobenius form, whether it is positive definite or positive semi-definite, m-closed value and wether the algebra satisfies the various 2A, 3A, 4A, 5A conditions sometimes assumed in Majorana algebras.

We can change the base ring/field of the algebra to the integers, a polynomial ring in one variable, finite fields, or function fileds in any number of variables.

    A := ChangeRing(A, R);
    A := ChangeField(A, F);

if it doesn't know how to coerce into the new field you must also supply a map `f`:

    A := ChangeField(A, F, f);

## Saving and loading

We can save and load our algebras.  These are stored in a library database and can be used to glue (automatically) into other larger algebras to help computation.

    SavePartialAxialAlgebra(A);
    A := LoadPartialAxialAlgbera(filename);

We can also load all algebras for a given group:

    algs := LoadAllGroup(G);

## Additional functions

The `AxialReduce` function runs two other functions repeatedly until either we have completed the algebra, or the `dimension_limit` is reached.  These are:

    Anew, phi := ExpandSpace(A);

This expands `A` to a larger partial axial algebra `Anew` by adding all the unknown products between elements of `A`.  It also returns a map `phi` from `A` to `Anew`.  The second function is:

    Anew, phi := ExpandSpace(A);

This runs a series of functions which intersect and sum subspaces, impose that they are (sums of) eigenspaces, impose the fusion rules.

Instead of expanding by all unknown multiplications, we may partially expand by just some of them.  Given a subspace U, we expand by the unknown products between `U` and `U + V` where `V` is the subspace of known multiplication.

    Anew, phi := PartialExpandSpace(A, U);

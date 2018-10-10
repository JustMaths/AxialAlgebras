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

This produces a sequence of tuples `<tau, stab>` where tau is a tau map and stab is its stabiliser in the normaliser of the action.  Let's pick one and find some shapes:

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

This runs two commands over and 

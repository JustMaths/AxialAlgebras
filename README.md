# AxialAlgebras

This is a magma package for constructing axial algebra with a given Miyamoto group.  It implements the algorithm described in the paper "An expansion algorithm for constructing axial algebras" (https://arxiv.org/abs/1804.00587) by J. McInroy and S. Shpectorov.

## Getting started

Begin by cloning the repository by running

    git clone https://github.com/JustMaths/AxialAlgebras
    
or

    git clone git@github.com:JustMaths/AxialAlgebras.git
    
Now, when you are in the AxialAlgebras directory start magma and attach the spec file

    AttachSpec("ParAxlAlg.spec")
    
NB some of the commands will use python 2.7.

## Find some shapes

To construct an axial algebra with a given Miyamoto group `G`, we need to begin with an action of a permutation group `G` on some putative axes.

    Ax := GSet(G);

Now, we want to find what addmissible tau maps there are

    taus := AdmissibleTauMaps(Ax);

This produces a sequence of tuples `<tau, stab>` where tau is a tau map and stab is its stabiliser in the normaliser of the action.  Let's pick one and find some shapes:

    tau, stab := Explode(taus[1]);
    shapes := Shapes(Ax, tau, stab);

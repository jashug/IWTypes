# IWTypes
A Coq development of the theory of Indexed W types with function extensionality.

## Setting
We define Indexed W types as a generalization of W types, where we define an inductive family of types.
They are very similar to dependent W types and indexed containers.
The type former is `IW A B I C D : I -> Type`, with `A I : Type`, `B : A -> Type`, `C : A -> I`, and `D : forall x : A, B x -> I`.
The interpretation is the same as `W A B`, but with `I` being the index type, and the constructor taking the form
`sup : forall x : A, (forall c : B x, IW (D x c)) -> IW (C x)`.
They then satisfy a dependent induction principle, which computes as expected.

Here, we examine the behaviour of these types, characterize their equality,
and find sufficient conditions for them to be n-types or have decidable equality.
We also present a reduction to non-indexed W types.

Apart from the reduction to W types, I am not aware of these results being published anywhere in the literature.

## Module index
Indexed W types are defined in `IWType.v`. We also show that IW types are unique up to equivalence.

`CharacterizeIWEquality.v` contains a proof that for `a b : IW A B I C D i` (abbreviated `IW i`),
`a = b` is equivalent to
```
IW
{x : A & (forall c : B x, IW (D x c) * (forall c : B x, IW (D x c))}
(fun (x, _, _) => B x)
{i : I & IW i * IW i}
(fun (x, children1, children2) => (C x, sup x children1, sup x children2))
(fun (x, children1, children2) (c : B x) => (D x c, children1 c, children2 c))
(i, a, b)
```

In `FiberEquiv.v`, we show that for a b : IW i,
`{(x, children1, children2) & (C x, sup x children1, sup x children2) = (i, a, b)}` is equivalent to
`data_part a = data_part b :> {x & C x = i}`,
that is, the fibers of C for equality as above are equivalent to equality in a fiber of `C`.

In `FiberProperties.v`, we show that if the fibers of `C` are mere propositions, then `IW A B I C D i` is a mere proposition for all `i`,
and that if the fibers of `C` have decidable equality, then `IW A B I C D i` has decidable equality for all i.

Combined with the results in `CharacterizeIWEquality.v` and `FiberEquiv.v`,
this implies that all positive h-levels are inherited from the fibers of C by induction.
If you represent usual W types by setting `I=1`, then this matches the result by Danielsson:
https://homotopytypetheory.org/2012/09/21/positive-h-levels-are-closed-under-w/

Finally, in a different vein, we show that IW types can be reduced to W types by typechecking `W A B` in `ReductIWtoW.v`.
This is a known result, which I found in
Indexed Containers by Thorsten Altenkirch and Peter Morris
http://www.cs.nott.ac.uk/~psztxa/publ/ICont.pdf

Modules `Adjointification.v`, `FunctionExtensionality.v`, `SigmaEta.v`, `Eqdep_dec.v` contain nothing new.
They contain standard lemmas used in the main proofs.

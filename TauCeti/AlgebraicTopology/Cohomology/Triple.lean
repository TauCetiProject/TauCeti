/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Singular.Triple

/-!
# The relative singular cochain sequence of a triple

For a triple `B ⊆ A ⊆ X` of topological spaces, the relative singular chain sequence
`0 ⟶ C(A, B) ⟶ C(X, B) ⟶ C(X, A) ⟶ 0` of `TauCeti.AlgebraicTopology.Singular.Triple` is split
in each degree: a section of the quotient map from the chains of `X` onto those of `(X, A)`,
followed by the quotient map onto the chains of `(X, B)`, is a section of `C(X, B) ⟶ C(X, A)`
(`TauCeti.TopTriple.isSplitEpi_singularChainComplexMap_totalToOuter_f`). Applying `Hom(-, M)`
therefore gives a short exact sequence of relative singular cochain complexes

`0 ⟶ C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B) ⟶ 0`

(`TauCeti.TopTriple.shortExact_singularCochainComplexShortComplex`), which generalizes the cochain
sequence of the pair `(X, A)` (`TauCeti.TopPair.shortExact_singularCochainComplexShortComplex`).
A filtration of a space by subspaces gives a decreasing filtration of its singular cochains by
relative cochains, and this sequence identifies the quotients of that filtration with relative
cochains.

## Main declarations

* `TauCeti.TopTriple.singularCochainComplexShortComplex`: the cochain sequence
  `C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B)` of a triple `(X, A, B)`.
* `TauCeti.TopTriple.shortExact_singularCochainComplexShortComplex`: it is short exact.

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace TauCeti

namespace TopTriple

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  (T : TopTriple.{w}) (R : C)

variable (k : Type*) [Ring k] [Linear k C] (M : C)

/-- The relative singular cochain sequence `C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B)` of a triple
`(X, A, B)`: the image under `Hom(-, M)` of its relative singular chain sequence. The first map is
induced by the map of pairs `(X, B) ⟶ (X, A)`, the second by `(A, B) ⟶ (X, B)`. -/
abbrev singularCochainComplexShortComplex : ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  (T.singularChainComplexShortComplex R).op.map (TauCeti.ChainComplex.linearYonedaFunctor k M)

/-- The first map of the cochain sequence of a triple `(X, A, B)` is the relative cochain map of
the map of pairs `(X, B) ⟶ (X, A)`. -/
lemma singularCochainComplexShortComplex_f :
    (T.singularCochainComplexShortComplex R k M).f =
      TopPair.singularCochainComplexMap (totalToOuter.app T) := (rfl)

/-- The second map of the cochain sequence of a triple `(X, A, B)` is the relative cochain map of
the map of pairs `(A, B) ⟶ (X, B)`. -/
lemma singularCochainComplexShortComplex_g :
    (T.singularCochainComplexShortComplex R k M).g =
      TopPair.singularCochainComplexMap (innerToTotal.app T) := (rfl)

/-- The relative singular cochain sequence `0 ⟶ C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B) ⟶ 0` of a triple
`(X, A, B)` is short exact. -/
lemma shortExact_singularCochainComplexShortComplex :
    (T.singularCochainComplexShortComplex R k M).ShortExact :=
  TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor k M
    (T.shortExact_singularChainComplexShortComplex R)

end TopTriple

end TauCeti

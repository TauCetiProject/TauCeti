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

For a triple `B ⊆ A ⊆ X` of topological spaces the relative singular chain complexes of its three
pairs form the short exact sequence `0 ⟶ C(A, B) ⟶ C(X, B) ⟶ C(X, A) ⟶ 0`
(`TauCeti.TopTriple.shortExact_singularChainComplexShortComplex`). It is split in each degree: a
section of the quotient map `Cₙ(X) ⟶ Cₙ(X, A)` of the pair `(X, A)`, followed by the quotient map
`Cₙ(X) ⟶ Cₙ(X, B)`, is a section of `Cₙ(X, B) ⟶ Cₙ(X, A)`
(`TauCeti.TopTriple.singularChainComplexXSplitting`). Applying `Hom(-, M)` therefore gives a short
exact sequence of relative singular cochain complexes

`0 ⟶ C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B) ⟶ 0`

(`TauCeti.TopTriple.shortExact_singularCochainComplexShortComplex`), whose long exact cohomology
sequence is the long exact sequence of the triple in singular cohomology. For `B` empty it is the
cochain sequence of the pair `(X, A)`.

This sequence identifies the graded pieces of the filtration of the singular cochains of a space by
the cochains vanishing on the members of an increasing family of subspaces, which is how the
cohomological spectral sequence of a filtered space is computed.

## Main declarations

* `TauCeti.TopTriple.singularChainComplexXSplitting`: the degreewise splitting of the relative
  singular chain sequence of a triple.
* `TauCeti.TopTriple.singularCochainComplexShortComplex`: the relative singular cochain sequence
  `C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B)` of a triple.
* `TauCeti.TopTriple.shortExact_singularCochainComplexShortComplex`: it is short exact.

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Sections 2.1 and 3.1.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace TauCeti

namespace TopTriple

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  (T : TopTriple.{w}) (R : C)

/-- The degree-`n` part `0 ⟶ Cₙ(A, B) ⟶ Cₙ(X, B) ⟶ Cₙ(X, A) ⟶ 0` of the relative singular chain
sequence of a triple `(X, A, B)` is split: a section of the quotient map `Cₙ(X) ⟶ Cₙ(X, A)`,
followed by the quotient map `Cₙ(X) ⟶ Cₙ(X, B)`, is a section of its last map. -/
def singularChainComplexXSplitting (n : ℕ) :
    ((T.singularChainComplexShortComplex R).map (HomologicalComplex.eval C _ n)).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _
    ((T.shortExact_singularChainComplexShortComplex R).map_of_exact
      (HomologicalComplex.eval C _ n)).exact
    ((SSetPair.chainComplexXSplitting R (TopPair.toSSetPair.obj (outerPair.obj T)) n).s ≫
      ((totalPair.obj T).singularChainComplexπ R).f n)
    -- On the chains of `X` the composite of the two quotient maps is the quotient map of the pair
    -- `(X, A)`, which the section splits.
    ((Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) <|
      (HomologicalComplex.comp_f _ _ n).symm.trans <|
        congrArg (fun f ↦ f.f n) (T.singularChainComplexπ_comp_totalToOuter R)).trans
      (SSetPair.chainComplexXSplitting R (TopPair.toSSetPair.obj (outerPair.obj T)) n).s_g)
    ((T.shortExact_singularChainComplexShortComplex R).map_of_exact
      (HomologicalComplex.eval C _ n)).mono_f

instance (n : ℕ) : IsSplitMono ((T.singularChainComplexShortComplex R).f.f n) :=
  IsSplitMono.mk' ⟨(T.singularChainComplexXSplitting R n).r,
    (T.singularChainComplexXSplitting R n).f_r⟩

variable (k : Type*) [Ring k] [Linear k C] (M : C)

/-- The relative singular cochain sequence `C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B)` of a triple
`(X, A, B)`: the image under `Hom(-, M)` of its relative singular chain sequence. Its maps are
induced by the maps of pairs `(X, B) ⟶ (X, A)` and `(A, B) ⟶ (X, B)`. -/
abbrev singularCochainComplexShortComplex : ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  (T.singularChainComplexShortComplex R).op.map (TauCeti.ChainComplex.linearYonedaFunctor k M)

/-- The first map of the cochain sequence of a triple is induced by the map of pairs
`(X, B) ⟶ (X, A)`. -/
lemma singularCochainComplexShortComplex_f :
    (T.singularCochainComplexShortComplex R k M).f =
      TopPair.singularCochainComplexMap (totalToOuter.app T) := (rfl)

/-- The second map of the cochain sequence of a triple is induced by the map of pairs
`(A, B) ⟶ (X, B)`. -/
lemma singularCochainComplexShortComplex_g :
    (T.singularCochainComplexShortComplex R k M).g =
      TopPair.singularCochainComplexMap (innerToTotal.app T) := (rfl)

/-- **The cochain sequence of a triple is short exact**: for a triple `(X, A, B)`, the sequence
`0 ⟶ C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B) ⟶ 0` of relative singular cochain complexes is short exact. -/
theorem shortExact_singularCochainComplexShortComplex :
    (T.singularCochainComplexShortComplex R k M).ShortExact :=
  TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor k M
    (T.shortExact_singularChainComplexShortComplex R)

end TopTriple

end TauCeti

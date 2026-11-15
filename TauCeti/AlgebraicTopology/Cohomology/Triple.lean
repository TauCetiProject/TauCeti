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
* `TauCeti.TopTriple.singularCohomologyδ`: the connecting map `Hⁿ(A, B) ⟶ Hⁿ⁺¹(X, A)` of the
  associated long exact sequence, with the three exactness statements
  `TauCeti.TopTriple.singularCohomology_exact_outer`,
  `TauCeti.TopTriple.singularCohomology_exact_total` and
  `TauCeti.TopTriple.singularCohomology_exact_inner`, and its naturality
  `TauCeti.TopTriple.singularCohomologyδ_naturality`.

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

/-- The connecting morphism `Hⁿ(A, B) ⟶ Hᵐ(X, A)` of the long exact cohomology sequence of a
triple `(X, A, B)`, where `n + 1 = m`. -/
abbrev singularCohomologyδ (n m : ℕ) (h : n + 1 = m := by lia) :
    (innerPair.obj T).singularCohomology R k M n ⟶
      (outerPair.obj T).singularCohomology R k M m :=
  (T.shortExact_singularCochainComplexShortComplex R k M).δ n m (by simpa)

/-- The connecting morphism of a triple is the connecting morphism of the short exact sequence of
relative singular cochain complexes of the triple. -/
lemma singularCohomologyδ_def (n m : ℕ) (h : n + 1 = m := by lia) :
    T.singularCohomologyδ R k M n m h =
      (T.shortExact_singularCochainComplexShortComplex R k M).δ n m (by simpa) :=
  (rfl)

/-- The maps `Hⁿ(X, A) ⟶ Hⁿ(X, B) ⟶ Hⁿ(A, B)` of a triple compose to zero. -/
@[reassoc (attr := simp)]
lemma singularCohomologyMap_totalToOuter_comp_innerToTotal (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (totalToOuter.app T) n ≫
      TopPair.singularCohomologyMap (innerToTotal.app T) n = 0 :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
    (congrArg (HomologicalComplex.homologyMap · n)
      (T.singularCochainComplexShortComplex R k M).zero).trans
        (HomologicalComplex.homologyMap_zero _ _ n)

/-- The map `Hⁿ(X, B) ⟶ Hⁿ(A, B)` of a triple followed by the connecting map
`Hⁿ(A, B) ⟶ Hᵐ(X, A)` is zero. -/
@[reassoc (attr := simp)]
lemma comp_singularCohomologyδ (n m : ℕ) (h : n + 1 = m := by lia) :
    TopPair.singularCohomologyMap (innerToTotal.app T) n ≫ T.singularCohomologyδ R k M n m h = 0 :=
  (T.shortExact_singularCochainComplexShortComplex R k M).comp_δ n m (by simpa)

/-- The connecting map `Hⁿ(A, B) ⟶ Hᵐ(X, A)` of a triple followed by the map
`Hᵐ(X, A) ⟶ Hᵐ(X, B)` is zero. -/
@[reassoc (attr := simp)]
lemma singularCohomologyδ_comp (n m : ℕ) (h : n + 1 = m := by lia) :
    T.singularCohomologyδ R k M n m h ≫ TopPair.singularCohomologyMap (totalToOuter.app T) m = 0 :=
  (T.shortExact_singularCochainComplexShortComplex R k M).δ_comp n m (by simpa)

/-- Exactness at `Hᵐ(X, A)` in the long exact cohomology sequence of a triple. -/
lemma singularCohomology_exact_outer (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (T.singularCohomologyδ_comp R k M n m h)).Exact :=
  (T.shortExact_singularCochainComplexShortComplex R k M).homology_exact₁ n m (by simpa)

/-- Exactness at `Hⁿ(X, B)` in the long exact cohomology sequence of a triple. -/
lemma singularCohomology_exact_total (n : ℕ) :
    (ShortComplex.mk _ _ (T.singularCohomologyMap_totalToOuter_comp_innerToTotal R k M n)).Exact :=
  (T.shortExact_singularCochainComplexShortComplex R k M).homology_exact₂ n

/-- Exactness at `Hⁿ(A, B)` in the long exact cohomology sequence of a triple. -/
lemma singularCohomology_exact_inner (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (T.comp_singularCohomologyδ R k M n m h)).Exact :=
  (T.shortExact_singularCochainComplexShortComplex R k M).homology_exact₃ n m (by simpa)

variable {R k M} in
/-- The morphism of relative singular cochain sequences induced by a morphism of triples, used to
prove the naturality of the connecting morphism. -/
private def singularCochainComplexShortComplexMap {T T' : TopTriple.{w}} (φ : T ⟶ T') :
    T'.singularCochainComplexShortComplex R k M ⟶ T.singularCochainComplexShortComplex R k M where
  τ₁ := TopPair.singularCochainComplexMap (outerPair.map φ)
  τ₂ := TopPair.singularCochainComplexMap (totalPair.map φ)
  τ₃ := TopPair.singularCochainComplexMap (innerPair.map φ)
  comm₁₂ := (TopPair.singularCochainComplexMap_comp _ _).symm.trans <|
    (congrArg TopPair.singularCochainComplexMap (totalToOuter.naturality φ)).symm.trans
      (TopPair.singularCochainComplexMap_comp _ _)
  comm₂₃ := (TopPair.singularCochainComplexMap_comp _ _).symm.trans <|
    (congrArg TopPair.singularCochainComplexMap (innerToTotal.naturality φ)).symm.trans
      (TopPair.singularCochainComplexMap_comp _ _)

variable {R k M} in
/-- The connecting morphism of the long exact cohomology sequence of a triple is natural: for a
morphism of triples `φ : (X, A, B) ⟶ (X', A', B')`, following `Hⁿ(A', B') ⟶ Hᵐ(X', A')` by the map
induced by `φ` on `Hᵐ(X', A')` agrees with following the map induced by `φ` on `Hⁿ(A', B')` by
`Hⁿ(A, B) ⟶ Hᵐ(X, A)`. -/
@[reassoc]
lemma singularCohomologyδ_naturality {T T' : TopTriple.{w}} (φ : T ⟶ T') (n m : ℕ)
    (h : n + 1 = m := by lia) :
    T'.singularCohomologyδ R k M n m h ≫ TopPair.singularCohomologyMap (outerPair.map φ) m =
      TopPair.singularCohomologyMap (innerPair.map φ) n ≫ T.singularCohomologyδ R k M n m h :=
  HomologicalComplex.HomologySequence.δ_naturality (singularCochainComplexShortComplexMap φ)
    (T'.shortExact_singularCochainComplexShortComplex R k M)
    (T.shortExact_singularCochainComplexShortComplex R k M) n m (by simpa)

end TopTriple

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.Singular.Triple

/-!
# The long exact sequence of a triple in relative singular cohomology

For a triple `B ⊆ A ⊆ X` of topological spaces, the relative singular chain sequence
`0 ⟶ C(A, B) ⟶ C(X, B) ⟶ C(X, A) ⟶ 0` is short exact and split in each degree
(`TauCeti.TopTriple.isSplitMono_singularChainComplexMap_innerToTotal_f`). Applying `Hom(-, M)`
therefore gives a short exact sequence of relative singular cochain complexes

`0 ⟶ C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B) ⟶ 0`

(`TauCeti.TopTriple.shortExact_singularCochainComplexShortComplex`), whose long exact cohomology
sequence is the long exact sequence of the triple

`⋯ ⟶ Hⁿ(X, A) ⟶ Hⁿ(X, B) ⟶ Hⁿ(A, B) ⟶ Hⁿ⁺¹(X, A) ⟶ ⋯`.

It is the cohomological counterpart of the long exact sequence of a triple in relative singular
homology (`TauCeti.TopTriple.singularHomologyδ`). The short exactness identifies the graded pieces
of the filtration of singular cochains by relative cochains, which underlies the cohomology spectral
sequence of a filtered space.

## Main declarations

* `TauCeti.TopTriple.singularCochainComplexShortComplex`: the cochain sequence of a triple.
* `TauCeti.TopTriple.shortExact_singularCochainComplexShortComplex`: it is short exact.
* `TauCeti.TopTriple.singularCohomologyδ`: the connecting morphism `Hⁿ(A, B) ⟶ Hⁿ⁺¹(X, A)`, with
  the zero composites `TauCeti.TopTriple.singularCohomologyδ_comp` and
  `TauCeti.TopTriple.comp_singularCohomologyδ`, and the exactness statements
  `TauCeti.TopTriple.singularCohomology_exact_outer`,
  `TauCeti.TopTriple.singularCohomology_exact_total` and
  `TauCeti.TopTriple.singularCohomology_exact_inner`.

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TauCeti

namespace TopTriple

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  (T : TopTriple.{w}) (R : C) (k : Type*) [Ring k] [Linear k C] (M : C)

/-- The cochain sequence `C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B)` of a triple `(X, A, B)`: the image under
`Hom(-, M)` of its relative singular chain sequence. -/
abbrev singularCochainComplexShortComplex : ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  (T.singularChainComplexShortComplex R).op.map (TauCeti.ChainComplex.linearYonedaFunctor k M)

/-- The cochain sequence `0 ⟶ C*(X, A) ⟶ C*(X, B) ⟶ C*(A, B) ⟶ 0` of a triple is short exact. -/
lemma shortExact_singularCochainComplexShortComplex :
    (T.singularCochainComplexShortComplex R k M).ShortExact :=
  TauCeti.ChainComplex.shortExact_map_linearYonedaFunctor k M
    (T.shortExact_singularChainComplexShortComplex R)

/-- The connecting morphism `Hⁿ(A, B) ⟶ Hᵐ(X, A)` in the long exact sequence of a triple
`(X, A, B)`, where `n + 1 = m`. -/
abbrev singularCohomologyδ (n m : ℕ) (h : n + 1 = m := by lia) :
    (innerPair.obj T).singularCohomology R k M n ⟶ (outerPair.obj T).singularCohomology R k M m :=
  (T.shortExact_singularCochainComplexShortComplex R k M).δ n m (by simpa)

/-- The connecting morphism `Hⁿ(A, B) ⟶ Hᵐ(X, A)` followed by `Hᵐ(X, A) ⟶ Hᵐ(X, B)` is zero. -/
@[reassoc (attr := simp)]
lemma singularCohomologyδ_comp (n m : ℕ) (h : n + 1 = m := by lia) :
    T.singularCohomologyδ R k M n m h ≫ TopPair.singularCohomologyMap (totalToOuter.app T) m = 0 :=
  (T.shortExact_singularCochainComplexShortComplex R k M).δ_comp n m (by simpa)

/-- The map `Hⁿ(X, B) ⟶ Hⁿ(A, B)` followed by the connecting morphism `Hⁿ(A, B) ⟶ Hᵐ(X, A)` is
zero. -/
@[reassoc (attr := simp)]
lemma comp_singularCohomologyδ (n m : ℕ) (h : n + 1 = m := by lia) :
    TopPair.singularCohomologyMap (innerToTotal.app T) n ≫ T.singularCohomologyδ R k M n m h = 0 :=
  (T.shortExact_singularCochainComplexShortComplex R k M).comp_δ n m (by simpa)

/-- Exactness of `Hⁿ(A, B) ⟶ Hᵐ(X, A) ⟶ Hᵐ(X, B)` in the long exact sequence of a triple, for
`n + 1 = m`. -/
lemma singularCohomology_exact_outer (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (T.singularCohomologyδ_comp R k M n m h)).Exact :=
  (T.shortExact_singularCochainComplexShortComplex R k M).homology_exact₁ n m (by simpa)

/-- Exactness of `Hⁿ(X, A) ⟶ Hⁿ(X, B) ⟶ Hⁿ(A, B)` in the long exact sequence of a triple. -/
lemma singularCohomology_exact_total (n : ℕ) :
    ((T.singularCochainComplexShortComplex R k M).map
      (HomologicalComplex.homologyFunctor _ _ n)).Exact :=
  (T.shortExact_singularCochainComplexShortComplex R k M).homology_exact₂ n

/-- Exactness of `Hⁿ(X, B) ⟶ Hⁿ(A, B) ⟶ Hᵐ(X, A)` in the long exact sequence of a triple, for
`n + 1 = m`. -/
lemma singularCohomology_exact_inner (n m : ℕ) (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _ (T.comp_singularCohomologyδ R k M n m h)).Exact :=
  (T.shortExact_singularCochainComplexShortComplex R k M).homology_exact₃ n m (by simpa)

end TopTriple

end TauCeti

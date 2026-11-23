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
  the zero composites `TauCeti.TopTriple.singularCohomologyMap_totalToOuter_comp_innerToTotal`,
  `TauCeti.TopTriple.singularCohomologyδ_comp` and `TauCeti.TopTriple.comp_singularCohomologyδ`,
  the exactness statements `TauCeti.TopTriple.singularCohomology_exact_outer`,
  `TauCeti.TopTriple.singularCohomology_exact_total` and
  `TauCeti.TopTriple.singularCohomology_exact_inner`, and its naturality
  `TauCeti.TopTriple.singularCohomologyδ_naturality`.
* `TauCeti.TopTriple.isIso_biprod_lift_singularCohomology`: when retractions out of `Hⁿ(X, B)` and
  `Hⁿ⁺¹(X, B)` split the outer maps `H*(X, A) ⟶ H*(X, B)` up to isomorphism, the connecting
  morphism vanishes and `Hⁿ(X, B)` splits as a binary biproduct.
* `TauCeti.TopTriple.isIso_singularCohomologyMap_totalToOuter_of_isZero`: if `Hⁿ(A, B)` vanishes,
  and so does `Hⁿ⁻¹(A, B)` when `n > 0`, restriction `Hⁿ(X, A) ⟶ Hⁿ(X, B)` is an isomorphism.
* `TauCeti.TopTriple.isIso_singularCohomologyMap_innerToTotal_of_isZero`: if `Hⁿ(X, A)` and
  `Hⁿ⁺¹(X, A)` vanish, restriction `Hⁿ(X, B) ⟶ Hⁿ(A, B)` is an isomorphism.

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

/-- The maps `Hⁿ(X, A) ⟶ Hⁿ(X, B) ⟶ Hⁿ(A, B)` of a triple compose to zero. -/
@[reassoc (attr := simp)]
lemma singularCohomologyMap_totalToOuter_comp_innerToTotal (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (totalToOuter.app T) n ≫
      TopPair.singularCohomologyMap (innerToTotal.app T) n = 0 :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
    (congrArg (HomologicalComplex.homologyMap · n)
      (T.singularCochainComplexShortComplex R k M).zero).trans
        (HomologicalComplex.homologyMap_zero _ _ n)

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

/-- **Splitting the cohomology sequence of a triple.** In a triple `T = (X, A, B)`, if morphisms
out of `Hⁿ(X, B)` and `Hⁿ⁺¹(X, B)` compose with `H*(X, A) ⟶ H*(X, B)` to isomorphisms, then
`Hⁿ(X, B) ⟶ B₀ ⊞ Hⁿ(A, B)` is an isomorphism. -/
theorem isIso_biprod_lift_singularCohomology (n : ℕ) {B₀ B₁ : ModuleCat.{v} k}
    (p₀ : (totalPair.obj T).singularCohomology R k M n ⟶ B₀)
    (p₁ : (totalPair.obj T).singularCohomology R k M (n + 1) ⟶ B₁)
    (hp₀ : IsIso (TopPair.singularCohomologyMap (totalToOuter.app T) n ≫ p₀))
    (hp₁ : IsIso (TopPair.singularCohomologyMap (totalToOuter.app T) (n + 1) ≫ p₁)) :
    IsIso (biprod.lift p₀ (TopPair.singularCohomologyMap (innerToTotal.app T) n)) := by
  let q₀ := TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (totalToOuter.app T) n
  let q₁ := TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (totalToOuter.app T) (n + 1)
  let i₀ := TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (innerToTotal.app T) n
  have hδ : T.singularCohomologyδ R k M n (n + 1) rfl = 0 := by
    rw [← Category.comp_id (T.singularCohomologyδ R k M n (n + 1) rfl),
      ← IsIso.hom_inv_id (q₁ ≫ p₁), ← Category.assoc, ← Category.assoc,
      T.singularCohomologyδ_comp R k M n (n + 1) rfl, zero_comp, zero_comp]
  have hepi : Epi i₀ := (T.singularCohomology_exact_inner R k M n (n + 1) rfl).epi_f hδ
  let r' : (totalPair.obj T).singularCohomology R k M n ⟶
      (outerPair.obj T).singularCohomology R k M n := p₀ ≫ inv (q₀ ≫ p₀)
  have hr' : q₀ ≫ r' = 𝟙 _ := by
    dsimp only [r']
    rw [← Category.assoc]
    exact IsIso.hom_inv_id _
  let spl := ShortComplex.Splitting.ofExactOfRetraction _
    (T.singularCohomology_exact_total R k M n) r' hr' hepi
  have hspl : IsIso (biprod.lift r' i₀) := spl.isoBinaryBiproduct.isIso_hom
  have hfac : biprod.lift r' i₀ ≫ (biprod.mapIso (asIso (q₀ ≫ p₀)) (Iso.refl _)).hom =
      biprod.lift p₀ i₀ :=
    biprod.hom_ext _ _ (by simp [r', biprod.lift_fst_assoc]) (by simp)
  rw [← hfac]
  infer_instance

/-- **Removing an acyclic inner pair**: if `Hⁿ(A, B)` vanishes, and so does `Hᵐ(A, B)` for
`m + 1 = n`, then restriction `Hⁿ(X, A) ⟶ Hⁿ(X, B)` is an isomorphism. -/
theorem isIso_singularCohomologyMap_totalToOuter_of_isZero (n : ℕ)
    (hn : IsZero ((innerPair.obj T).singularCohomology R k M n))
    (hm : ∀ m, m + 1 = n → IsZero ((innerPair.obj T).singularCohomology R k M m)) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (totalToOuter.app T) n) := by
  have : Epi (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (totalToOuter.app T) n) :=
    (T.singularCohomology_exact_total R k M n).epi_f (hn.eq_of_tgt _ _)
  have :
      Mono (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (totalToOuter.app T) n) := by
    cases n with
    | zero =>
      -- In degree `0` there is no earlier term: the cochain map is injective in degree `0`.
      have := (T.shortExact_singularCochainComplexShortComplex R k M).mono_f
      have : Mono ((T.singularCochainComplexShortComplex R k M).f.f 0) := inferInstance
      exact HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
        (T.singularCochainComplexShortComplex R k M).f 0 (by simp)
    | succ m =>
      exact (T.singularCohomology_exact_outer R k M m (m + 1)).mono_g ((hm m rfl).eq_of_src _ _)
  exact isIso_of_mono_of_epi _

/-- **Removing an acyclic outer pair**: if `Hⁿ(X, A)` and `Hⁿ⁺¹(X, A)` vanish, then restriction
`Hⁿ(X, B) ⟶ Hⁿ(A, B)` is an isomorphism. This is the cohomology form of
`TauCeti.TopTriple.isIso_singularHomologyMap_innerToTotal_of_isZero`. -/
theorem isIso_singularCohomologyMap_innerToTotal_of_isZero (n : ℕ)
    (hn : IsZero ((outerPair.obj T).singularCohomology R k M n))
    (hn' : IsZero ((outerPair.obj T).singularCohomology R k M (n + 1))) :
    IsIso (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (innerToTotal.app T) n) := by
  have : Mono (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (innerToTotal.app T) n) :=
    (T.singularCohomology_exact_total R k M n).mono_g (hn.eq_of_src _ _)
  have : Epi (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (innerToTotal.app T) n) :=
    (T.singularCohomology_exact_inner R k M n (n + 1)).epi_f (hn'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end TopTriple

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Limit
public import TauCeti.RingTheory.AdicRing.CompletedTensorProduct.Restricted
public import TauCeti.RingTheory.Huber.Restricted.Comparison
public import TauCeti.RingTheory.Huber.Restricted.Reduction

import TauCeti.RingTheory.AdicCompletion.Topology

/-!
# Inverse-limit description and compatibilities of adic restricted power series

For a commutative topological ring `A` whose topology is `I`-adic for a finitely generated
ideal `I`, the quotients `(A ⧸ I ^ (m + 1))[X₁, …, Xₖ]` form an inverse system in
`CommRingCat` (`Ideal.mvPolynomialQuotientPowSuccDiagram`). When `A` is complete and Hausdorff,
the polynomial reductions of the completed restricted power-series algebra
`TauCeti.Huber.restrictedMvPowerSeriesCompletion k A` and of the coefficient-subring carrier
`TauCeti.Huber.weightedRestrictedSubring` form limit cones over this system, identifying both
carriers with the inverse limit of `(A ⧸ I ^ (m + 1))[X₁, …, Xₖ]`.

This module also establishes reduction compatibility for coefficient maps
(`Ideal.restrictedReduction_weightedMap`,
`TauCeti.Huber.restrictedReduction_weightedMapCompletion`), for continuous evaluation into linearly
topologised rings (`Ideal.quotientMk_weightedEvalHom`,
`TauCeti.Huber.quotientMk_weightedEvalHomCompletion`), and for base change along completed tensor
products, as well as the compatibility of these reductions, inverse limits, and continuous maps
with the unit-radius Gauss-normed carrier `MvPowerSeries.IsRestricted.subring` whenever `A` is an
`I`-adic ultrametric Banach ring.

## Main definitions

* `Ideal.mvPolynomialQuotientPowSuccDiagram`: the inverse system
  `m ↦ (A ⧸ I ^ (m + 1))[X₁, …, Xₖ]` in `CommRingCat`.
* `TauCeti.Huber.quotientPowRestrictedCompletionEquivMvPolynomialQuotient`: the `A`-algebra
  isomorphism `A⟨X₁, …, Xₖ⟩ ⧸ I ^ (m + 1) · A⟨X₁, …, Xₖ⟩ ≃ₐ[A] (A ⧸ I ^ (m + 1))[X₁, …, Xₖ]`.
* `TauCeti.Huber.restrictedMvPowerSeriesCompletionQuotientPowSuccCone` and
  `TauCeti.Huber.weightedRestrictedQuotientPowSuccCone`: the cones of compatible polynomial
  reductions out of the completed and coefficient-subring carriers.
* `TauCeti.Huber.liftOfReductions`: the unique ring homomorphism into `A⟨X₁, …, Xₖ⟩` induced by
  a compatible family of ring homomorphisms into `(A ⧸ I ^ (m + 1))[X₁, …, Xₖ]`.
* `TauCeti.Huber.quotientIsRestrictedSubringEquivMvPolynomialQuotient`: the polynomial reduction
  isomorphism for the Gauss-normed unit-radius carrier `MvPowerSeries.IsRestricted.subring`.

## Main results

* `TauCeti.Huber.isLimitRestrictedMvPowerSeriesCompletionQuotientPowSuccCone` and
  `TauCeti.Huber.isLimitWeightedRestrictedQuotientPowSuccCone`: the inverse-limit descriptions
  of `A⟨X₁, …, Xₖ⟩` and the coefficient-subring carrier.
* `Ideal.restrictedReduction_weightedMap` and `Ideal.quotientMk_weightedEvalHom`: reduction
  compatibility of coefficient maps and continuous evaluation on restricted series, with their
  completed counterparts `TauCeti.Huber.restrictedReduction_weightedMapCompletion` and
  `TauCeti.Huber.quotientMk_weightedEvalHomCompletion`.
* `TauCeti.Huber.isAdic_map_algebraMap_isRestricted_subring`,
  `TauCeti.Huber.isLimitIsRestrictedSubringQuotientPowSuccCone`, and
  `TauCeti.Huber.eq_restrictedEval₂OfBound_of_existsUnique_isLinearTopology`: compatibility of
  adic reductions, inverse limits, and continuous universal-property maps with the Gauss-normed
  carrier.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.5.1–7.5.3.
* T. Wedhorn, *Adic Spaces*, §5.6.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

open CategoryTheory Limits Opposite Filter Topology UniformSpace

section PolynomialReductionCompatibility

namespace Ideal

variable {k : ℕ}

section Diagram

universe u

variable {A : Type u} [CommRing A]

/-- The inverse system `(A ⧸ I)[X] ← (A ⧸ I ^ 2)[X] ← (A ⧸ I ^ 3)[X] ← ⋯` of polynomial rings
in `k` variables over the quotients `A ⧸ I ^ (m + 1)`. -/
@[expose, simps]
noncomputable def mvPolynomialQuotientPowSuccDiagram (I : Ideal A) (k : ℕ) :
    ℕᵒᵖ ⥤ CommRingCat.{u} where
  obj m := CommRingCat.of (MvPolynomial (Fin k) (A ⧸ I ^ (m.unop + 1)))
  map f := CommRingCat.ofHom
    (MvPolynomial.map (Ideal.Quotient.factorPow I (Nat.succ_le_succ (leOfHom f.unop))))
  map_id _ := by
    apply CommRingCat.hom_ext
    exact MvPolynomial.ringHom_ext (fun _ ↦ by simp) (fun _ ↦ by simp)
  map_comp _ _ := by
    apply CommRingCat.hom_ext
    exact MvPolynomial.ringHom_ext (fun _ ↦ by simp) (fun _ ↦ by simp)

end Diagram

section Maps

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]

/-- Coefficient maps of restricted series commute with polynomial reduction modulo open ideals. -/
theorem restrictedReduction_weightedMap (J : Ideal B) (hJ : IsOpen (J : Set B))
    {I : Ideal A} (hI : IsOpen (I : Set A)) {φ : A →+* B} (hφ : Continuous φ)
    (hIJ : I ≤ J.comap φ)
    (f : TauCeti.Huber.weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      TauCeti.Huber.isWeightFamily_one_weight) :
    restrictedReduction J hJ
        (TauCeti.Huber.weightedMap hφ TauCeti.Huber.isWeightFamily_one_weight
          TauCeti.Huber.isWeightFamily_one_weight (fun _ ↦ by simp) f) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ) (restrictedReduction I hI f) := by
  ext ν
  simp [MvPolynomial.coeff_map]

end Maps

section Eval

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [CompleteSpace B] [T3Space B]

/-- Continuous evaluation out of `A⟨X₁, …, Xₖ⟩` into a complete Hausdorff nonarchimedean ring `B`
reduces modulo an open ideal `J` of `B` to polynomial evaluation of the polynomial reduction
modulo any open ideal `I` of `A` mapping into `J`. -/
theorem quotientMk_weightedEvalHom (J : Ideal B) (hJ : IsOpen (J : Set B))
    {I : Ideal A} (hI : IsOpen (I : Set A)) {φ : A →+* B} (hφ : ContinuousAt φ 0)
    (hIJ : I ≤ J.comap φ) {b : Fin k → B}
    (hb : TauCeti.Huber.IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b)
    (f : TauCeti.Huber.weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      TauCeti.Huber.isWeightFamily_one_weight) :
    Ideal.Quotient.mk J
        (TauCeti.Huber.weightedEvalHom TauCeti.Huber.isWeightFamily_one_weight hφ hb f) =
      MvPolynomial.eval₂ (Ideal.quotientMap J φ hIJ) (fun i ↦ Ideal.Quotient.mk J (b i))
        (restrictedReduction I hI f) := by
  have : DiscreteTopology (B ⧸ J) := QuotientAddGroup.discreteTopology_iff.mpr hJ
  let lhs : TauCeti.Huber.weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      TauCeti.Huber.isWeightFamily_one_weight →+* B ⧸ J :=
    (Ideal.Quotient.mk J).comp
      (TauCeti.Huber.weightedEvalHom TauCeti.Huber.isWeightFamily_one_weight hφ hb)
  let evalRed : MvPolynomial (Fin k) (A ⧸ I) →+* B ⧸ J :=
    MvPolynomial.eval₂Hom (Ideal.quotientMap J φ hIJ) (fun i ↦ Ideal.Quotient.mk J (b i))
  let rhs : TauCeti.Huber.weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      TauCeti.Huber.isWeightFamily_one_weight →+* B ⧸ J :=
    evalRed.comp (restrictedReduction I hI)
  have hlhs : Continuous lhs :=
    continuous_quot_mk.comp (TauCeti.Huber.continuous_weightedEvalHom _ hφ hb)
  have hrhs : Continuous rhs := by
    refine continuous_of_continuousAt_zero rhs ?_
    rw [ContinuousAt, map_zero, nhds_discrete (α := B ⧸ J), Filter.tendsto_pure]
    filter_upwards [(TauCeti.Huber.hasBasis_nhds_zero_weightedTopology
      TauCeti.Huber.isWeightFamily_one_weight).mem_of_mem
      (i := ⟨I.toAddSubgroup, hI⟩) trivial] with g hg
    have hred : restrictedReduction I hI g = 0 := by
      ext ν
      simpa [Ideal.Quotient.eq_zero_iff_mem] using TauCeti.Huber.mem_weightedNhd.mp hg ν
    simp [rhs, hred]
  refine RingHom.congr_fun
    (TauCeti.Huber.weightedRestrictedSubring_ringHom_ext_of_continuous
      TauCeti.Huber.isWeightFamily_one_weight hlhs hrhs (fun a ↦ ?_) (fun i ↦ ?_)) f
  · simp [lhs, rhs, evalRed]
  · simp [lhs, rhs, evalRed]

end Eval

end Ideal

end PolynomialReductionCompatibility

namespace TauCeti.Huber

section InverseLimit

universe u

variable {k : ℕ} {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A] [T2Space A] [CompleteSpace A] {I : Ideal A}

/-- For every `m : ℕ`, the completed restricted-series algebra modulo `(I · A⟨X⟩) ^ (m + 1)` is
`A`-algebra isomorphic to `(A ⧸ I ^ (m + 1))[X₁, …, Xₖ]`. -/
noncomputable def quotientPowRestrictedCompletionEquivMvPolynomialQuotient
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) :
    (restrictedMvPowerSeriesCompletion k A ⧸
      (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))) ^ (m + 1)) ≃ₐ[A]
      MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)) :=
  (Ideal.quotientEquivAlgOfEq A
    (Ideal.map_pow (algebraMap A (restrictedMvPowerSeriesCompletion k A)) I (m + 1)).symm).trans
    (quotientRestrictedCompletionEquivMvPolynomialQuotient
      (is_ideal_adic_pow hI (Nat.succ_pos m)) (Ideal.FG.pow (n := m + 1) hfg))

/-- On an arbitrary element of `A⟨X₁, …, Xₖ⟩`, the modulo-`I ^ (m + 1)` quotient equivalence
computes its polynomial reduction. -/
@[simp]
theorem quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk
    (hI : IsAdic I) (hfg : I.FG) (m : ℕ) (x : restrictedMvPowerSeriesCompletion k A) :
    quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI hfg m (Ideal.Quotient.mk _ x) =
      Ideal.restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1))
        (restrictedMvPowerSeriesCompletionEquiv k A x) := by
  simp [quotientPowRestrictedCompletionEquivMvPolynomialQuotient]

/-- The diagram of quotients `A⟨X⟩ ⧸ (I · A⟨X⟩) ^ (m + 1)` is naturally isomorphic in `CommRingCat`
to the inverse system `(A ⧸ I ^ (m + 1))[X₁, …, Xₖ]`. -/
noncomputable def quotientPowSuccDiagramIsoMvPolynomial
    (k : ℕ) (hI : IsAdic I) (hfg : I.FG) :
    Ideal.quotientPowSuccDiagram
        (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))) ≅
      Ideal.mvPolynomialQuotientPowSuccDiagram I k :=
  NatIso.ofComponents
    (fun m ↦ (quotientPowRestrictedCompletionEquivMvPolynomialQuotient
      (k := k) hI hfg m.unop).toRingEquiv.toCommRingCatIso)
    (fun {m n} f ↦ by
      ext y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      simp only [Ideal.quotientPowSuccDiagram_map, RingEquiv.toCommRingCatIso_hom,
        Ideal.mvPolynomialQuotientPowSuccDiagram_map]
      change (quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI hfg n.unop)
          (Ideal.Quotient.mk _ x) =
        MvPolynomial.map (Ideal.Quotient.factorPow I (Nat.succ_le_succ (leOfHom f.unop)))
          ((quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI hfg m.unop)
            (Ideal.Quotient.mk _ x))
      rw [quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk,
        quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk]
      exact (map_restrictedReduction (hI.isOpen_pow (m.unop + 1)) (hI.isOpen_pow (n.unop + 1))
        (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop)))
        (restrictedMvPowerSeriesCompletionEquiv k A x)).symm)

variable (k) in
/-- The cone of polynomial reductions out of `restrictedMvPowerSeriesCompletion k A` over the
inverse system `(A ⧸ I ^ (m + 1))[X₁, …, Xₖ]`. -/
@[expose, simps]
noncomputable def restrictedMvPowerSeriesCompletionQuotientPowSuccCone (hI : IsAdic I) :
    Cone (Ideal.mvPolynomialQuotientPowSuccDiagram I k) where
  pt := CommRingCat.of (restrictedMvPowerSeriesCompletion k A)
  π.app m := CommRingCat.ofHom
    ((Ideal.restrictedReduction (I ^ (m.unop + 1)) (hI.isOpen_pow (m.unop + 1))).comp
      (restrictedMvPowerSeriesCompletionEquiv k A).toRingHom)
  π.naturality m n f := by
    ext x
    simp only [Ideal.mvPolynomialQuotientPowSuccDiagram_map]
    exact (map_restrictedReduction (hI.isOpen_pow (m.unop + 1)) (hI.isOpen_pow (n.unop + 1))
      (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop)))
      (restrictedMvPowerSeriesCompletionEquiv k A x)).symm

variable (k) in
/-- The cone of polynomial reductions out of the coefficient-subring carrier
`weightedRestrictedSubring` over `(A ⧸ I ^ (m + 1))[X₁, …, Xₖ]`. -/
@[expose, simps]
noncomputable def weightedRestrictedQuotientPowSuccCone (hI : IsAdic I) :
    Cone (Ideal.mvPolynomialQuotientPowSuccDiagram I k) where
  pt := CommRingCat.of
    (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)
  π.app m := CommRingCat.ofHom
    (Ideal.restrictedReduction (I ^ (m.unop + 1)) (hI.isOpen_pow (m.unop + 1)))
  π.naturality m n f := by
    ext x
    simp only [Ideal.mvPolynomialQuotientPowSuccDiagram_map]
    exact (map_restrictedReduction (hI.isOpen_pow (m.unop + 1)) (hI.isOpen_pow (n.unop + 1))
      (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop))) x).symm

variable (k) in
/-- **Inverse-limit description of `A⟨X₁, …, Xₖ⟩`.** Over a complete Hausdorff `I`-adic ring `A`
with `I` finitely generated, `A⟨X₁, …, Xₖ⟩` is the limit in `CommRingCat` of the polynomial
reductions `(A ⧸ I ^ (m + 1))[X₁, …, Xₖ]`. -/
noncomputable def isLimitRestrictedMvPowerSeriesCompletionQuotientPowSuccCone
    (hI : IsAdic I) (hfg : I.FG) :
    IsLimit (restrictedMvPowerSeriesCompletionQuotientPowSuccCone k hI) := by
  let J := I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))
  have hJ : IsAdic J := isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg
  have : IsAdicComplete J (restrictedMvPowerSeriesCompletion k A) :=
    hJ.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩
  have hlim : IsLimit ((Cone.postcompose (quotientPowSuccDiagramIsoMvPolynomial k hI hfg).hom).obj
      (Ideal.quotientPowSuccCone J)) :=
    (IsLimit.postcomposeHomEquiv (quotientPowSuccDiagramIsoMvPolynomial k hI hfg)
      (Ideal.quotientPowSuccCone J)).symm (IsAdicComplete.isLimitQuotientPowSuccCone J)
  refine IsLimit.ofIsoLimit hlim (Cone.ext (Iso.refl _) fun m ↦ ?_)
  ext x
  exact quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk hI hfg m.unop x

variable (k) in
/-- **Inverse-limit description of the coefficient-subring carrier.** Over a complete Hausdorff
`I`-adic ring `A` with `I` finitely generated, `weightedRestrictedSubring` is the limit in
`CommRingCat` of the polynomial reductions `(A ⧸ I ^ (m + 1))[X₁, …, Xₖ]`. -/
noncomputable def isLimitWeightedRestrictedQuotientPowSuccCone
    (hI : IsAdic I) (hfg : I.FG) :
    IsLimit (weightedRestrictedQuotientPowSuccCone k hI) := by
  refine IsLimit.ofIsoLimit (isLimitRestrictedMvPowerSeriesCompletionQuotientPowSuccCone k hI hfg)
    (Cone.ext (restrictedMvPowerSeriesCompletionEquiv k A).toCommRingCatIso fun m ↦ ?_)
  rfl

end InverseLimit

section UniversalLift

variable {k : ℕ} {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A] [T2Space A] [CompleteSpace A] {I : Ideal A}

private theorem strictMono_succ : StrictMono (fun m : ℕ ↦ m + 1) :=
  fun _ _ h ↦ Nat.add_lt_add_right h 1

private theorem liftOfReductions_compat (hI : IsAdic I) (hfg : I.FG)
    {B : Type*} [CommRing B]
    (f : (m : ℕ) → B →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (MvPolynomial.map (Ideal.Quotient.factorPow I (Nat.succ_le_succ hle))).comp (f n) = f m)
    {m : ℕ} :
    (Ideal.Quotient.factorPow
        (I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A)))
        (Nat.succ_le_succ (Nat.le_succ m))).comp
        ((quotientPowRestrictedCompletionEquivMvPolynomialQuotient
          hI hfg (m + 1)).symm.toRingHom.comp (f (m + 1))) =
      (quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI hfg m).symm.toRingHom.comp
        (f m) := by
  ext b
  let J := I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))
  let em := quotientPowRestrictedCompletionEquivMvPolynomialQuotient (k := k) hI hfg m
  apply em.injective
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
    ((quotientPowRestrictedCompletionEquivMvPolynomialQuotient (k := k) hI hfg (m + 1)).symm
      (f (m + 1) b))
  have hy' : f (m + 1) b =
      Ideal.restrictedReduction (I ^ (m + 2)) (hI.isOpen_pow (m + 2))
        (restrictedMvPowerSeriesCompletionEquiv k A y) := by
    rw [← quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk hI hfg (m + 1) y, hy,
      AlgEquiv.apply_symm_apply]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv]
  have hrhs : em ((quotientPowRestrictedCompletionEquivMvPolynomialQuotient hI hfg
      m).symm (f m b)) = f m b :=
    em.apply_symm_apply (f m b)
  rw [hrhs]
  have hfac : Ideal.Quotient.factorPow J (Nat.succ_le_succ (Nat.le_succ m))
      ((quotientPowRestrictedCompletionEquivMvPolynomialQuotient (k := k) hI hfg
        (m + 1)).symm (f (m + 1) b)) =
      Ideal.Quotient.factorPow J (Nat.succ_le_succ (Nat.le_succ m))
        (Ideal.Quotient.mk (J ^ (m + 2)) y) :=
    congrArg _ hy.symm
  rw [hfac, Ideal.Quotient.factor_mk]
  dsimp only [em]
  rw [quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk]
  have hcompat := RingHom.congr_fun (hf (Nat.le_succ m)) b
  rw [RingHom.comp_apply, hy'] at hcompat
  rw [← hcompat]
  exact (map_restrictedReduction (hI.isOpen_pow (m + 2)) (hI.isOpen_pow (m + 1))
    (Ideal.pow_le_pow_right (Nat.succ_le_succ (Nat.le_succ m))) _).symm

/-- Lift a compatible family of ring homomorphisms `B →+* (A ⧸ I ^ (m + 1))[X₁, …, Xₖ]` to a
ring homomorphism `B →+* A⟨X₁, …, Xₖ⟩`. This universe-polymorphic counterpart to the
`CommRingCat` limit avoids locking the source `B` and coefficient ring `A` into the same
universe. -/
noncomputable def liftOfReductions (hI : IsAdic I) (hfg : I.FG)
    {B : Type*} [CommRing B]
    (f : (m : ℕ) → B →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (MvPolynomial.map (Ideal.Quotient.factorPow I (Nat.succ_le_succ hle))).comp (f n) = f m) :
    B →+* restrictedMvPowerSeriesCompletion k A :=
  let J := I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))
  have hJ : IsAdic J := isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg
  have : IsAdicComplete J (restrictedMvPowerSeriesCompletion k A) :=
    hJ.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩
  IsAdicComplete.StrictMono.liftRingHom J strictMono_succ
    (fun m ↦ (quotientPowRestrictedCompletionEquivMvPolynomialQuotient
      hI hfg m).symm.toRingHom.comp (f m))
    (liftOfReductions_compat hI hfg f hf)

/-- The lift of a compatible family of reductions recovers each reduction modulo `I ^ (m + 1)`. -/
@[simp]
theorem restrictedReduction_liftOfReductions (hI : IsAdic I) (hfg : I.FG)
    {B : Type*} [CommRing B]
    (f : (m : ℕ) → B →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (MvPolynomial.map (Ideal.Quotient.factorPow I (Nat.succ_le_succ hle))).comp (f n) = f m)
    (m : ℕ) (b : B) :
    Ideal.restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1))
        (restrictedMvPowerSeriesCompletionEquiv k A (liftOfReductions hI hfg f hf b)) =
      f m b := by
  let J := I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))
  have hJ : IsAdic J := isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg
  have : IsAdicComplete J (restrictedMvPowerSeriesCompletion k A) :=
    hJ.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩
  rw [← quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk hI hfg m]
  dsimp only [liftOfReductions]
  rw [IsAdicComplete.StrictMono.mk_liftRingHom (n := m) J strictMono_succ _
    (liftOfReductions_compat hI hfg f hf)]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv]
  exact (quotientPowRestrictedCompletionEquivMvPolynomialQuotient (k := k) hI
    hfg m).apply_symm_apply (f m b)

/-- A ring homomorphism into `A⟨X₁, …, Xₖ⟩` is uniquely determined by its reductions modulo
`I ^ (m + 1)` for all `m : ℕ`. -/
theorem eq_liftOfReductions (hI : IsAdic I) (hfg : I.FG)
    {B : Type*} [CommRing B]
    (f : (m : ℕ) → B →+* MvPolynomial (Fin k) (A ⧸ I ^ (m + 1)))
    (hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (MvPolynomial.map (Ideal.Quotient.factorPow I (Nat.succ_le_succ hle))).comp (f n) = f m)
    (F : B →+* restrictedMvPowerSeriesCompletion k A)
    (hF : ∀ m b, Ideal.restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1))
      (restrictedMvPowerSeriesCompletionEquiv k A (F b)) = f m b) :
    F = liftOfReductions hI hfg f hf := by
  let J := I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))
  have hJ : IsAdic J := isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg
  have : IsAdicComplete J (restrictedMvPowerSeriesCompletion k A) :=
    hJ.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩
  refine IsAdicComplete.StrictMono.eq_liftRingHom J strictMono_succ _
    (liftOfReductions_compat hI hfg f hf) fun m ↦ ?_
  ext b
  apply (quotientPowRestrictedCompletionEquivMvPolynomialQuotient (k := k) hI hfg m).injective
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv]
  rw [quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk, AlgEquiv.apply_symm_apply]
  exact hF m b

/-- Two elements of `A⟨X₁, …, Xₖ⟩` with the same polynomial reductions modulo `I ^ (m + 1)` for
all `m` are equal. -/
theorem restrictedMvPowerSeriesCompletion_eq_of_forall_restrictedReduction
    (hI : IsAdic I) (hfg : I.FG) {x y : restrictedMvPowerSeriesCompletion k A}
    (h : ∀ m : ℕ, Ideal.restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1))
        (restrictedMvPowerSeriesCompletionEquiv k A x) =
      Ideal.restrictedReduction (I ^ (m + 1)) (hI.isOpen_pow (m + 1))
        (restrictedMvPowerSeriesCompletionEquiv k A y)) :
    x = y := by
  let J := I.map (algebraMap A (restrictedMvPowerSeriesCompletion k A))
  have hJ : IsAdic J := isAdic_map_algebraMap_restrictedMvPowerSeriesCompletion k hI hfg
  have : IsAdicComplete J (restrictedMvPowerSeriesCompletion k A) :=
    hJ.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩
  have hfn := IsHausdorff.StrictMono.funext' J strictMono_succ
    (f := fun _ : Unit ↦ x) (g := fun _ : Unit ↦ y) fun m _ ↦ by
      apply (quotientPowRestrictedCompletionEquivMvPolynomialQuotient (k := k) hI hfg m).injective
      rw [quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk,
        quotientPowRestrictedCompletionEquivMvPolynomialQuotient_mk]
      exact h m
  exact congrFun hfn ()

end UniversalLift

section CompletedMaps

variable {k : ℕ} {A B : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A] [T2Space A] [CompleteSpace A]
  [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B]
  [T2Space B] [CompleteSpace B]

/-- Continuous coefficient maps on completed restricted power series commute with polynomial
reduction modulo open ideals. -/
theorem restrictedReduction_weightedMapCompletion (J : Ideal B) (hJ : IsOpen (J : Set B))
    {I : Ideal A} (hI : IsOpen (I : Set A)) {φ : A →+* B} (hφ : Continuous φ)
    (hIJ : I ≤ J.comap φ) (f : restrictedMvPowerSeriesCompletion k A) :
    Ideal.restrictedReduction J hJ (restrictedMvPowerSeriesCompletionEquiv k B
        (weightedMapCompletion hφ isWeightFamily_one_weight isWeightFamily_one_weight
          (fun _ ↦ by simp) f)) =
      MvPolynomial.map (Ideal.quotientMap J φ hIJ)
        (Ideal.restrictedReduction I hI (restrictedMvPowerSeriesCompletionEquiv k A f)) := by
  obtain ⟨g, rfl⟩ := (restrictedMvPowerSeriesCompletionEquiv k A).symm.surjective f
  simp only [restrictedMvPowerSeriesCompletionEquiv_symm_apply, weightedMapCompletion_coe,
    restrictedMvPowerSeriesCompletionEquiv_coe]
  exact Ideal.restrictedReduction_weightedMap J hJ hI hφ hIJ g

omit [T2Space B] in
/-- Evaluation out of `A⟨X₁, …, Xₖ⟩` into a complete Hausdorff nonarchimedean ring `B`
commutes with polynomial reduction modulo open ideals. -/
theorem quotientMk_weightedEvalHomCompletion [T3Space B]
    (J : Ideal B) (hJ : IsOpen (J : Set B)) {I : Ideal A} (hI : IsOpen (I : Set A))
    {φ : A →+* B} (hφ : ContinuousAt φ 0) (hIJ : I ≤ J.comap φ) {b : Fin k → B}
    (hb : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set A)) b)
    (f : restrictedMvPowerSeriesCompletion k A) :
    Ideal.Quotient.mk J (weightedEvalHomCompletion isWeightFamily_one_weight hφ hb f) =
      MvPolynomial.eval₂ (Ideal.quotientMap J φ hIJ) (fun i ↦ Ideal.Quotient.mk J (b i))
        (Ideal.restrictedReduction I hI (restrictedMvPowerSeriesCompletionEquiv k A f)) := by
  obtain ⟨g, rfl⟩ := (restrictedMvPowerSeriesCompletionEquiv k A).symm.surjective f
  simp only [restrictedMvPowerSeriesCompletionEquiv_symm_apply, weightedEvalHomCompletion_coe,
    restrictedMvPowerSeriesCompletionEquiv_coe]
  exact Ideal.quotientMk_weightedEvalHom J hJ hI hφ hIJ hb g

/-- Reduction compatibility for the universal property of `A⟨X₁, …, Xₖ⟩` into a complete
Hausdorff linearly topologised ring `B`, where arbitrary choices of the variables are
automatically power-bounded. -/
theorem quotientMk_of_existsUnique_isLinearTopology [IsLinearTopology B B]
    (J : Ideal B) (hJ : IsOpen (J : Set B)) {I : Ideal A} (hI : IsOpen (I : Set A))
    {φ : A →+* B} (hφ : Continuous φ) (hIJ : I ≤ J.comap φ) (b : Fin k → B)
    {ψ : restrictedMvPowerSeriesCompletion k A →+* B} (hψc : Continuous ψ)
    (hψC : ∀ a, ψ (algebraMap A (restrictedMvPowerSeriesCompletion k A) a) = φ a)
    (hψX : ∀ i, ψ ((weightedX _ isWeightFamily_one_weight i :
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
        restrictedMvPowerSeriesCompletion k A) = b i)
    (f : restrictedMvPowerSeriesCompletion k A) :
    Ideal.Quotient.mk J (ψ f) =
      MvPolynomial.eval₂ (Ideal.quotientMap J φ hIJ) (fun i ↦ Ideal.Quotient.mk J (b i))
        (Ideal.restrictedReduction I hI (restrictedMvPowerSeriesCompletionEquiv k A f)) := by
  obtain ⟨χ, -, hχu⟩ :=
    existsUnique_continuous_ringHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology hφ b
  have hψw : ψ = weightedEvalHomCompletion isWeightFamily_one_weight hφ.continuousAt
      (isWeightBounded_of_isLinearTopology φ _ b) := by
    refine (hχu ψ ⟨hψc, hψC, hψX⟩).trans (hχu _ ⟨continuous_weightedEvalHomCompletion ..,
      fun a ↦ ?_, fun i ↦ ?_⟩).symm
    · rw [algebraMap_completion_weightedRestrictedSubring_apply, weightedEvalHomCompletion_coe,
        weightedEvalHom_weightedC]
    · rw [weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]
  rw [hψw]
  exact quotientMk_weightedEvalHomCompletion J hJ hI hφ.continuousAt hIJ _ f

end CompletedMaps

section CompletedTensorBaseChange

variable {m : ℕ} {A C : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsAdicRing A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C]
  [Algebra A C] [ContinuousSMul A C]

/-- Base change of adic restricted power series via the completed tensor product
`A⟨X₁, …, Xₘ⟩ ⊗̂_A C ≃+* C⟨X₁, …, Xₘ⟩` commutes on `A⟨X₁, …, Xₘ⟩` with polynomial reduction
modulo open ideals. -/
theorem restrictedReduction_restrictedEquiv_inl (J : Ideal C) (hJ : IsOpen (J : Set C))
    {I : Ideal A} (hI : IsOpen (I : Set A)) (hIJ : I ≤ J.comap (algebraMap A C))
    (x : restrictedMvPowerSeriesCompletion m A) :
    let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    have _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
    let _ : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
    have _ : IsUniformAddGroup C := isUniformAddGroup_of_addCommGroup
    Ideal.restrictedReduction J hJ (restrictedMvPowerSeriesCompletionEquiv m C
        (AdicRing.CompletedTensorProduct.restrictedEquiv m A C
          (AdicRing.CompletedTensorProduct.inl A
            (restrictedMvPowerSeriesCompletion m A) C x))) =
      MvPolynomial.map (Ideal.quotientMap J (algebraMap A C) hIJ)
        (Ideal.restrictedReduction I hI (restrictedMvPowerSeriesCompletionEquiv m A x)) := by
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  let _ : UniformSpace C := IsTopologicalAddGroup.rightUniformSpace C
  have _ : IsUniformAddGroup C := isUniformAddGroup_of_addCommGroup
  rw [AdicRing.CompletedTensorProduct.restrictedEquiv_inl]
  exact restrictedReduction_weightedMapCompletion J hJ hI (continuous_algebraMap A C) hIJ x

end CompletedTensorBaseChange

section GaussNormCompatibility

universe u

variable {k : ℕ} {R : Type u} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

omit [CompleteSpace R] in
/-- When an ultrametric Banach ring `R` carries the `I`-adic topology for a finitely generated
ideal `I`, the extended ideal `I · R⟨X₁, …, Xₖ⟩` defines the Gauss-norm topology on the
unit-radius restricted-series algebra `MvPowerSeries.IsRestricted.subring`. -/
theorem isAdic_map_algebraMap_isRestricted_subring {I : Ideal R} (hI : IsAdic I) (hfg : I.FG) :
    IsAdic (I.map (algebraMap R
      (_root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)))) := by
  let e : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight ≃+*
      _root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) :=
    restrictedMvPowerSeriesGaussEquiv
  let heHomeo : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R))
        isWeightFamily_one_weight ≃ₜ
      _root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) :=
    { toEquiv := e.toEquiv
      continuous_toFun := continuous_restrictedMvPowerSeriesGaussEquiv
      continuous_invFun := continuous_restrictedMvPowerSeriesGaussEquiv_symm }
  have he : IsOpenQuotientMap e.toRingHom := heHomeo.isOpenQuotientMap
  have hadic : IsAdic (I.map (algebraMap R (weightedRestrictedSubring
      (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight))) :=
    isAdic_map_algebraMap_weightedRestrictedSubring_one_weight k hI hfg
  have hmap : (I.map (algebraMap R (weightedRestrictedSubring
      (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight))).map e.toRingHom =
      I.map (algebraMap R (_root_.MvPowerSeries.IsRestricted.subring (R := R)
        (fun _ : Fin k ↦ 1))) := by
    rw [Ideal.map_map]
    congr 1
    ext r
    simp [e]
  rw [← hmap]
  exact hadic.map_of_isOpenQuotientMap e.toRingHom he

/-- Over a complete `I`-adic ultrametric normed ring `R` with `I` finitely generated, the
Gauss-normed unit-radius algebra `MvPowerSeries.IsRestricted.subring` is `I · R⟨X⟩`-adically
separated and complete. -/
theorem isAdicComplete_map_algebraMap_isRestricted_subring {I : Ideal R}
    (hI : IsAdic I) (hfg : I.FG) :
    IsAdicComplete
      (I.map (algebraMap R (_root_.MvPowerSeries.IsRestricted.subring (R := R)
        (fun _ : Fin k ↦ 1))))
      (_root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
  (isAdic_map_algebraMap_isRestricted_subring hI hfg).isAdicComplete_iff.mpr
    ⟨inferInstance, inferInstance⟩

/-- Over a complete `I`-adic ultrametric normed ring `R` with `I` finitely generated, the
Gauss-normed unit-radius restricted-series algebra is an adic ring of finite ideal type. -/
theorem isAdicRing_isRestricted_subring {I : Ideal R} (hI : IsAdic I) (hfg : I.FG) :
    IsAdicRing (_root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :=
  ⟨I.map (algebraMap R _), hfg.map _,
    isAdic_map_algebraMap_isRestricted_subring hI hfg,
    isAdicComplete_map_algebraMap_isRestricted_subring hI hfg⟩

/-- Over a complete `I`-adic ultrametric normed ring `R` with `I` finitely generated, the
quotient of the Gauss-normed unit-radius algebra by `I · R⟨X₁, …, Xₖ⟩` is isomorphic to the
polynomial algebra `(R ⧸ I)[X₁, …, Xₖ]`. -/
noncomputable def quotientIsRestrictedSubringEquivMvPolynomialQuotient
    {I : Ideal R} (hI : IsAdic I) (hfg : I.FG) :
    (_root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ⧸
      I.map (algebraMap R (_root_.MvPowerSeries.IsRestricted.subring (R := R)
        (fun _ : Fin k ↦ 1)))) ≃ₐ[R]
      MvPolynomial (Fin k) (R ⧸ I) := by
  let e : _root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) ≃+*
      restrictedMvPowerSeriesCompletion k R :=
    restrictedMvPowerSeriesCompletionGaussEquiv.symm
  have hcomp : e.toRingHom.comp (algebraMap R _) =
      algebraMap R (restrictedMvPowerSeriesCompletion k R) := by
    ext r
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
      ← coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv_symm, AlgEquiv.commutes]
  have hmap : I.map (algebraMap R (restrictedMvPowerSeriesCompletion k R)) =
      Ideal.map (↑e : _root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1) →+*
        restrictedMvPowerSeriesCompletion k R) (I.map (algebraMap R _)) := by
    rw [← RingEquiv.toRingHom_eq_coe, Ideal.map_map, hcomp]
  let f := (Ideal.quotientEquiv _ _ e hmap).trans
    (quotientRestrictedCompletionEquivMvPolynomialQuotient hI hfg).toRingEquiv
  refine AlgEquiv.ofRingEquiv (f := f) fun r ↦ ?_
  have hr : (Ideal.quotientEquiv _ _ e hmap) (algebraMap R _ r) = algebraMap R _ r := by
    rw [← Ideal.Quotient.mk_algebraMap]
    change (Ideal.quotientEquiv _ _ e hmap) (Ideal.Quotient.mk _ (algebraMap R _ r)) = _
    rw [Ideal.quotientEquiv_mk]
    have hcr : e (algebraMap R _ r) =
        algebraMap R (restrictedMvPowerSeriesCompletion k R) r :=
      RingHom.congr_fun hcomp r
    rw [hcr, Ideal.Quotient.mk_algebraMap]
  simp only [f, RingEquiv.trans_apply, hr, AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes]

/-- On a represented series, `quotientIsRestrictedSubringEquivMvPolynomialQuotient` computes the
polynomial reduction of its underlying series. -/
@[simp]
theorem quotientIsRestrictedSubringEquivMvPolynomialQuotient_mk
    {I : Ideal R} (hI : IsAdic I) (hfg : I.FG)
    (f : _root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1)) :
    quotientIsRestrictedSubringEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ f) =
      Ideal.restrictedReduction I (by simpa only [pow_one] using hI.isOpen_pow 1)
        (restrictedMvPowerSeriesGaussEquiv.symm f) := by
  dsimp only [quotientIsRestrictedSubringEquivMvPolynomialQuotient]
  rw [AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, Ideal.quotientEquiv_mk]
  dsimp only [RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv]
  rw [quotientRestrictedCompletionEquivMvPolynomialQuotient_mk]
  congr 1
  rw [coe_restrictedMvPowerSeriesCompletionAlgEquiv,
    restrictedMvPowerSeriesCompletionGaussEquiv_symm_apply,
    restrictedMvPowerSeriesCompletionEquiv_coe]

/-- The Gauss-norm comparison intertwines the polynomial reduction equivalences on the completed
Huber carrier and on the Gauss-normed unit-radius carrier. -/
theorem quotientIsRestrictedSubringEquivMvPolynomialQuotient_comp_gaussAlgEquiv
    {I : Ideal R} (hI : IsAdic I) (hfg : I.FG) (x : restrictedMvPowerSeriesCompletion k R) :
    quotientIsRestrictedSubringEquivMvPolynomialQuotient hI hfg
        (Ideal.Quotient.mk _ (restrictedMvPowerSeriesCompletionGaussAlgEquiv x)) =
      quotientRestrictedCompletionEquivMvPolynomialQuotient hI hfg (Ideal.Quotient.mk _ x) := by
  rw [quotientIsRestrictedSubringEquivMvPolynomialQuotient_mk,
    quotientRestrictedCompletionEquivMvPolynomialQuotient_mk]
  congr 1
  rw [coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv,
    coe_restrictedMvPowerSeriesCompletionAlgEquiv]
  conv_rhs =>
    rw [← RingEquiv.symm_apply_apply restrictedMvPowerSeriesCompletionGaussEquiv x,
      restrictedMvPowerSeriesCompletionGaussEquiv_symm_apply,
      restrictedMvPowerSeriesCompletionEquiv_coe]

variable (k) in
/-- The cone of polynomial reductions out of the Gauss-normed unit-radius algebra over
`(R ⧸ I ^ (m + 1))[X₁, …, Xₖ]`. -/
@[expose, simps]
noncomputable def isRestrictedSubringQuotientPowSuccCone {I : Ideal R} (hI : IsAdic I) :
    Cone (Ideal.mvPolynomialQuotientPowSuccDiagram I k) where
  pt := CommRingCat.of (_root_.MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin k ↦ 1))
  π.app m := CommRingCat.ofHom
    ((Ideal.restrictedReduction (I ^ (m.unop + 1)) (hI.isOpen_pow (m.unop + 1))).comp
      restrictedMvPowerSeriesGaussEquiv.symm.toRingHom)
  π.naturality m n f := by
    ext x
    simp only [Ideal.mvPolynomialQuotientPowSuccDiagram_map]
    exact (map_restrictedReduction (hI.isOpen_pow (m.unop + 1)) (hI.isOpen_pow (n.unop + 1))
      (Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop)))
      (restrictedMvPowerSeriesGaussEquiv.symm x)).symm

variable (k) in
/-- **Inverse-limit compatibility with the Gauss-normed carrier.** Over a complete `I`-adic
ultrametric normed ring `R` with `I` finitely generated, the unit-radius Gauss-normed algebra
`MvPowerSeries.IsRestricted.subring` is the limit in `CommRingCat` of the polynomial reductions
`(R ⧸ I ^ (m + 1))[X₁, …, Xₖ]`. -/
noncomputable def isLimitIsRestrictedSubringQuotientPowSuccCone {I : Ideal R}
    (hI : IsAdic I) (hfg : I.FG) :
    IsLimit (isRestrictedSubringQuotientPowSuccCone k hI) :=
  IsLimit.ofIsoLimit (isLimitWeightedRestrictedQuotientPowSuccCone k hI hfg)
    (Cone.ext restrictedMvPowerSeriesGaussEquiv.toCommRingCatIso fun m ↦
      CommRingCat.hom_ext <| RingHom.ext fun x ↦
        (congrArg (Ideal.restrictedReduction (I ^ (m.unop + 1)) (hI.isOpen_pow (m.unop + 1)))
          (restrictedMvPowerSeriesGaussEquiv.symm_apply_apply x)).symm)

section UniversalProperty

variable {S : Type*} [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]
  {φ : R →+* S} {C : ℝ}

/-- **Compatibility of the adic universal property with normed evaluation.** When `S` is a
complete ultrametric normed ring whose topology is linearly topologised, the unique continuous map
`ψ : R⟨X₁, …, Xₖ⟩ →+* S` extending a continuous bounded `φ : R →+* S` with `ψ(Xᵢ) = bᵢ`
(for `‖bᵢ‖ ≤ 1`) agrees with normed evaluation `φ.restrictedEval₂OfBound` through the Gauss
comparison. -/
theorem eq_restrictedEval₂OfBound_of_existsUnique_isLinearTopology [IsLinearTopology S S]
    (hφc : Continuous φ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    {b : Fin k → S} (hb : ∀ i, ‖b i‖ ≤ 1)
    {ψ : restrictedMvPowerSeriesCompletion k R →+* S} (hψc : Continuous ψ)
    (hψC : ∀ a, ψ (algebraMap R (restrictedMvPowerSeriesCompletion k R) a) = φ a)
    (hψX : ∀ i, ψ ((weightedX _ isWeightFamily_one_weight i :
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
        restrictedMvPowerSeriesCompletion k R) = b i)
    (f : restrictedMvPowerSeriesCompletion k R) :
    ψ f = φ.restrictedEval₂OfBound b hφ hb (restrictedMvPowerSeriesCompletionGaussEquiv f) := by
  obtain ⟨χ, -, hχu⟩ :=
    existsUnique_continuous_ringHom_restrictedMvPowerSeriesCompletion_of_isLinearTopology hφc b
  have hbw : IsWeightBounded φ (fun _ : Fin k ↦ ({1} : Set R)) b :=
    isWeightBounded_of_isLinearTopology φ _ b
  have hψw : ψ = weightedEvalHomCompletion isWeightFamily_one_weight hφc.continuousAt hbw := by
    refine (hχu ψ ⟨hψc, hψC, hψX⟩).trans (hχu _ ⟨continuous_weightedEvalHomCompletion ..,
      fun a ↦ ?_, fun i ↦ ?_⟩).symm
    · rw [algebraMap_completion_weightedRestrictedSubring_apply, weightedEvalHomCompletion_coe,
        weightedEvalHom_weightedC]
    · rw [weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]
  rw [hψw]
  exact weightedEvalHomCompletion_eq_restrictedEval₂OfBound hφc.continuousAt hφ hb hbw f

/-- When `S` is a complete ultrametric normed ring whose topology is linearly topologised, the
unique continuous map `ψ : R⟨X₁, …, Xₖ⟩ →+* S` extending a continuous bounded `φ : R →+* S`
obeys the Gauss-norm bound `‖ψ f‖ ≤ C ‖f‖`. -/
theorem norm_le_of_existsUnique_isLinearTopology [IsLinearTopology S S]
    (hφc : Continuous φ) (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖)
    {b : Fin k → S} (hb : ∀ i, ‖b i‖ ≤ 1)
    {ψ : restrictedMvPowerSeriesCompletion k R →+* S} (hψc : Continuous ψ)
    (hψC : ∀ a, ψ (algebraMap R (restrictedMvPowerSeriesCompletion k R) a) = φ a)
    (hψX : ∀ i, ψ ((weightedX _ isWeightFamily_one_weight i :
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set R)) isWeightFamily_one_weight) :
        restrictedMvPowerSeriesCompletion k R) = b i)
    (f : restrictedMvPowerSeriesCompletion k R) :
    ‖ψ f‖ ≤ C * ‖restrictedMvPowerSeriesCompletionGaussEquiv f‖ := by
  rw [eq_restrictedEval₂OfBound_of_existsUnique_isLinearTopology hφc hφ hb hψc hψC hψX f]
  exact φ.norm_restrictedEval₂OfBound_le b hφ hb _

end UniversalProperty

end GaussNormCompatibility

end TauCeti.Huber

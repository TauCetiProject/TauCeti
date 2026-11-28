/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.TateSeries.Eval
public import TauCeti.RingTheory.Huber.WeightedEval.Newton
import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
import TauCeti.RingTheory.Subsemiring.SpanSingleton

/-!
# Multivariable Newton–Hensel lifting for `tateSeries`

Let `C` be a complete Hausdorff nonarchimedean ring with a pair of definition `P` whose ring of
definition `C₀` contains a pseudouniformiser `ϖ` of `C`. Given `F : Fin N → tateSeries N C` with
`F i ∈ tateSeriesPlus N C C₀`, a point `t : Fin N → C₀` with scaled Jacobian inverse
`M * J(t) = ϖ ^ k • 1`, and a residual bound `Fᵢ(t) ∈ ϖ ^ e • C₀` (`2 * k + 1 ≤ e`), this file
specialises `TauCeti.Huber.existsUnique_weightedEval_eq_zero`,
`TauCeti.Huber.pow_dvd_sub_of_weightedEval_eq_zero`, and `TauCeti.Huber.eq_of_weightedEval_eq_zero`
to `tateSeries N C`, provides an adjugate constructor for scaled Jacobian inverses, treats
coefficientwise `ϖ ^ e`-perturbations of the defining system, and establishes functoriality of
Newton roots under continuous ring homomorphisms:

1. **Adjugate scaled inverse** (`tateSeries.adjugateJacobianMatrixInv`,
   `tateSeries.adjugateJacobianMatrixInv_mul`): given a subring `R ≤ C` containing the evaluated
   Jacobian entries and a scaled scalar inverse `s` of `weightedEval φ x (tateSeries.jacobian F)`,
   constructs an `R`-valued matrix `M` with `M * J(x) = (s * weightedEval φ x (jacobian F)) • 1`.
2. **Existence, uniqueness, and error bound** (`existsUnique_weightedEval_tateSeries_eq_zero` and
   `existsUnique_weightedEval_tateSeries_eq_zero_of_coeff_sub`): `F` (or any coefficientwise
   `ϖ ^ e`-perturbation `G`) has a unique zero `u ∈ C₀^N` with `u ≡ t mod ϖ ^ (k + 1)`, and
   `u ≡ t mod ϖ ^ (e - k)`.
3. **Functoriality** (`map_weightedEval_tateSeries_eq_zero`): continuous ring homomorphisms
   preserve Newton roots.

## Main definitions

* `TauCeti.Huber.tateSeries.adjugateJacobianMatrixInv`: integral `s`-scaled inverse of the
  evaluated Jacobian matrix via the adjugate.

## Main results

* `TauCeti.Huber.tateSeries.adjugateJacobianMatrixInv_mul`: left inverse identity for
  `tateSeries.adjugateJacobianMatrixInv`.
* `TauCeti.Huber.existsUnique_weightedEval_tateSeries_eq_zero`: multivariable Newton–Hensel lifting
  and quantitative error bound `u ≡ t mod ϖ ^ (e - k)` on `tateSeries N C`.
* `TauCeti.Huber.existsUnique_weightedEval_tateSeries_eq_zero_of_coeff_sub`: Newton–Hensel lifting
  after a coefficientwise `ϖ ^ e`-perturbation of the defining series.
* `TauCeti.Huber.map_weightedEval_tateSeries_eq_zero`: compatibility of Newton roots with
  continuous ring homomorphisms.

## References

* R. Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*, Vieweg (1996),
  Proposition 1.7.1.
* O. Gabber and L. Ramero, *Almost Ring Theory*, Lecture Notes in Math. **1800**, Springer (2003),
  Lemma 5.4.8.
-/

public section

open Matrix Pointwise

namespace TauCeti.Huber

section Adjugate

/-- **Adjugate construction of an integral scaled Jacobian inverse:** given a subring `R` of `C`
containing every evaluated partial derivative `weightedEval φ x (∂ⱼFᵢ)` and a scalar `s ∈ R`,
this defines the `R`-valued matrix `s • adjugate J(x)`. -/
noncomputable def tateSeries.adjugateJacobianMatrixInv
    {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
    {C : Type*} [CommRing C] [TopologicalSpace C] (R : Subring C)
    (φ : A →+* C) {N : ℕ} (x : Fin N → C) (F : Fin N → tateSeries N A)
    (hJ : ∀ i j, weightedEval φ x
      (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) A)) ∈ R)
    {s : C} (hs : s ∈ R) : Matrix (Fin N) (Fin N) R :=
  (⟨s, hs⟩ : R) • (Matrix.of fun i j ↦ ⟨weightedEval φ x
    (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) A)), hJ i j⟩).adjugate

/-- **Scaled inverse identity for `tateSeries.adjugateJacobianMatrixInv`:** over `C`,
`(tateSeries.adjugateJacobianMatrixInv R φ x F hJ hs) * J(x)` equals
`(s * weightedEval φ x (tateSeries.jacobian F)) • 1`. -/
theorem tateSeries.adjugateJacobianMatrixInv_mul
    {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
    {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
    [NonarchimedeanRing C] [CompleteSpace C] [T3Space C]
    {R : Subring C} {φ : A →+* C} (hφ : ContinuousAt φ 0)
    {N : ℕ} {x : Fin N → C} (hx : ∀ i, IsPowerBounded (x i))
    (F : Fin N → tateSeries N A)
    (hJ : ∀ i j, weightedEval φ x
      (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) A)) ∈ R)
    {s : C} (hs : s ∈ R) :
    (tateSeries.adjugateJacobianMatrixInv R φ x F hJ hs).map Subtype.val *
        Matrix.of (fun i j ↦ weightedEval φ x
          (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) A))) =
      (s * weightedEval φ x (tateSeries.jacobian F : MvPowerSeries (Fin N) A)) •
        (1 : Matrix (Fin N) (Fin N) C) := by
  let J : Matrix (Fin N) (Fin N) C :=
    Matrix.of fun i j ↦ weightedEval φ x
      (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) A))
  have hJR_map : (Matrix.of fun i j ↦ (⟨weightedEval φ x
      (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) A)), hJ i j⟩ : R)).map R.subtype =
      J := by
    ext i j
    simp [J]
  have hadj : (tateSeries.adjugateJacobianMatrixInv R φ x F hJ hs).map Subtype.val =
      s • J.adjugate := by
    rw [tateSeries.adjugateJacobianMatrixInv, ← Subring.coe_subtype (s := R),
      Matrix.map_smul' _ _ _ (map_mul R.subtype), ← RingHom.mapMatrix_apply,
      RingHom.map_adjugate, RingHom.mapMatrix_apply, hJR_map]
    simp
  rw [hadj, Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, weightedEval_tateSeries_jacobian hφ hx]

end Adjugate

section Newton

variable {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
  [NonarchimedeanRing C] [CompleteSpace C] [T0Space C]

/-- **Multivariable Newton–Hensel lifting for `tateSeries`:** if `F : Fin N → tateSeries N C` has
coefficients in `P.ringOfDefinition`, its Jacobian at `t` has an integral `ϖ ^ k`-scaled left
inverse `M`, and `F(t) ≡ 0 mod ϖ ^ e` with `2 * k + 1 ≤ e`, then `F` has a unique zero `u` in
`P.ringOfDefinition^N` congruent to `t` modulo `ϖ ^ (k + 1)`, and `u` satisfies
`u ≡ t mod ϖ ^ (e - k)`. -/
theorem existsUnique_weightedEval_tateSeries_eq_zero
    (P : PairOfDefinition C) (ϖ : P.ringOfDefinition) (hϖ : IsPseudoUniformizer (ϖ : C))
    (N : ℕ) (F : Fin N → tateSeries N C)
    (hF : ∀ i, F i ∈ tateSeriesPlus N C P.ringOfDefinition)
    (t : Fin N → P.ringOfDefinition) (k e : ℕ) (he : 2 * k + 1 ≤ e)
    (M : Matrix (Fin N) (Fin N) P.ringOfDefinition)
    (hJ : M.map Subtype.val *
        Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (t l : C))
          (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) C))) =
      (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C))
    (hFt : ∀ i, ∃ r : P.ringOfDefinition,
      weightedEval (RingHom.id C) (fun l ↦ (t l : C)) (F i : MvPowerSeries (Fin N) C) =
        (ϖ : C) ^ e * (r : C)) :
    ∃ u : Fin N → P.ringOfDefinition,
      ((∀ i, ϖ ^ (k + 1) ∣ u i - t i) ∧
      (∀ i, weightedEval (RingHom.id C) (fun l ↦ (u l : C))
        (F i : MvPowerSeries (Fin N) C) = 0) ∧
      (∀ i, ϖ ^ (e - k) ∣ u i - t i)) ∧
      ∀ v : Fin N → P.ringOfDefinition,
        (∀ i, ϖ ^ (k + 1) ∣ v i - t i) →
        (∀ i, weightedEval (RingHom.id C) (fun l ↦ (v l : C))
          (F i : MvPowerSeries (Fin N) C) = 0) →
        v = u := by
  have hFres (i) := mem_weightedRestrictedSubring.mp (F i).property
  have hF₀ (i) := mem_tateSeriesPlus_iff.mp (hF i)
  have hFt_smul (i) : weightedEval (RingHom.id C) (fun l ↦ (t l : C))
      (F i : MvPowerSeries (Fin N) C) ∈ (ϖ : C) ^ e • (P.ringOfDefinition : Set C) := by
    obtain ⟨r, hr⟩ := hFt i; exact ⟨r, r.property, hr.symm⟩
  have hFt_base (i) : weightedEval (RingHom.id C) (fun l ↦ (t l : C))
      (F i : MvPowerSeries (Fin N) C) ∈
        (ϖ : C) ^ (2 * k + 1) • (P.ringOfDefinition : Set C) := by
    rw [← SubsemiringClass.image_coe_span_singleton_pow P.ringOfDefinition ϖ.property]
    exact Set.image_mono (Ideal.pow_le_pow_right he)
      ((SubsemiringClass.image_coe_span_singleton_pow P.ringOfDefinition ϖ.property e).symm ▸
        hFt_smul i)
  obtain ⟨u, ⟨hu_mod, hu_zero⟩, hu_uniq⟩ :=
    existsUnique_weightedEval_eq_zero P hϖ hFres hF₀ t hJ hFt_base
  exact ⟨u, ⟨hu_mod, hu_zero,
    pow_dvd_sub_of_weightedEval_eq_zero P hϖ.isUnit hFres hF₀ hJ hFt_smul hu_mod hu_zero⟩,
    fun v hv_mod hv_zero ↦ hu_uniq v ⟨hv_mod, hv_zero⟩⟩

/-- **Newton–Hensel lifting for a coefficientwise `ϖ ^ e`-perturbed `tateSeries` system:**
if `F : Fin N → tateSeries N C` has coefficients in `P.ringOfDefinition`, `M * J_F(t) = ϖ ^ k • 1`,
`F(t) ≡ 0 mod ϖ ^ e` with `2 * k + 1 ≤ e`, and `G : Fin N → tateSeries N C` satisfies
`Gᵢ - Fᵢ ≡ 0 mod ϖ ^ e` coefficientwise in `P.ringOfDefinition`, then `G` has a unique zero `u` in
`P.ringOfDefinition^N` congruent to `t` modulo `ϖ ^ (k + 1)`, and `u` satisfies
`u ≡ t mod ϖ ^ (e - k)`. -/
theorem existsUnique_weightedEval_tateSeries_eq_zero_of_coeff_sub
    (P : PairOfDefinition C) (ϖ : P.ringOfDefinition) (hϖ : IsPseudoUniformizer (ϖ : C))
    (N : ℕ) (F G : Fin N → tateSeries N C)
    (hF : ∀ i, F i ∈ tateSeriesPlus N C P.ringOfDefinition)
    (t : Fin N → P.ringOfDefinition) (k e : ℕ) (he : 2 * k + 1 ≤ e)
    (M : Matrix (Fin N) (Fin N) P.ringOfDefinition)
    (hJ : M.map Subtype.val *
        Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (t l : C))
          (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) C))) =
      (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C))
    (hFt : ∀ i, ∃ r : P.ringOfDefinition,
      weightedEval (RingHom.id C) (fun l ↦ (t l : C)) (F i : MvPowerSeries (Fin N) C) =
        (ϖ : C) ^ e * (r : C))
    (hFG : ∀ i ν, ∃ r : P.ringOfDefinition,
      MvPowerSeries.coeff ν ((G i - F i : tateSeries N C) : MvPowerSeries (Fin N) C) =
        (ϖ : C) ^ e * (r : C)) :
    ∃ u : Fin N → P.ringOfDefinition,
      ((∀ i, ϖ ^ (k + 1) ∣ u i - t i) ∧
      (∀ i, weightedEval (RingHom.id C) (fun l ↦ (u l : C))
        (G i : MvPowerSeries (Fin N) C) = 0) ∧
      (∀ i, ϖ ^ (e - k) ∣ u i - t i)) ∧
      ∀ v : Fin N → P.ringOfDefinition,
        (∀ i, ϖ ^ (k + 1) ∣ v i - t i) →
        (∀ i, weightedEval (RingHom.id C) (fun l ↦ (v l : C))
          (G i : MvPowerSeries (Fin N) C) = 0) →
        v = u := by
  have hke : k + 1 ≤ e := by omega
  have hG : ∀ i, G i ∈ tateSeriesPlus N C P.ringOfDefinition := by
    intro i
    rw [mem_tateSeriesPlus_iff]
    intro ν
    obtain ⟨r, hr⟩ := hFG i ν
    have hsub : MvPowerSeries.coeff ν
        ((G i : MvPowerSeries (Fin N) C) - (F i : MvPowerSeries (Fin N) C)) ∈
        P.ringOfDefinition := by
      rw [← AddSubgroupClass.coe_sub (G i) (F i), hr]
      exact mul_mem (pow_mem ϖ.property e) r.property
    rw [map_sub] at hsub
    simpa only [sub_add_cancel] using add_mem hsub (mem_tateSeriesPlus_iff.mp (hF i) ν)
  have hFG_mem : ∀ i ν, MvPowerSeries.coeff ν
      ((G i : MvPowerSeries (Fin N) C) - (F i : MvPowerSeries (Fin N) C)) ∈
      (ϖ : C) ^ (k + 1) • (P.ringOfDefinition : Set C) := by
    intro i ν
    obtain ⟨r, hr⟩ := hFG i ν
    rw [← AddSubgroupClass.coe_sub (G i) (F i),
      ← SubsemiringClass.image_coe_span_singleton_pow P.ringOfDefinition ϖ.property]
    exact Set.image_mono (Ideal.pow_le_pow_right hke)
      ((SubsemiringClass.image_coe_span_singleton_pow P.ringOfDefinition ϖ.property e).symm ▸
        ⟨r, r.property, hr.symm⟩)
  obtain ⟨M', -, hJM', -⟩ := exists_mul_jacobianMatrix_eq_pow_smul_one_of_coeff_mem P hϖ
    (fun i ↦ mem_weightedRestrictedSubring.mp (F i).property)
    (fun i ↦ mem_tateSeriesPlus_iff.mp (hF i))
    (fun i ↦ mem_weightedRestrictedSubring.mp (G i).property)
    (fun i ↦ mem_tateSeriesPlus_iff.mp (hG i))
    hFG_mem hJ
  have hGt : ∀ i, ∃ r : P.ringOfDefinition,
      weightedEval (RingHom.id C) (fun l ↦ (t l : C)) (G i : MvPowerSeries (Fin N) C) =
        (ϖ : C) ^ e * (r : C) := by
    intro i
    have hid : ContinuousAt (RingHom.id C) 0 := continuous_id.continuousAt
    have ht_bd := (isWeightBounded_one_weight_iff_forall_isPowerBounded (RingHom.id C)
      (fun l ↦ (t l : C))).mpr fun l ↦
        P.isBounded_ringOfDefinition.isPowerBounded_of_mem (t l).property
    have hdiff_eval : weightedEval (RingHom.id C) (fun l ↦ (t l : C))
        ((G i - F i : tateSeries N C) : MvPowerSeries (Fin N) C) ∈
        (ϖ : C) ^ e • (P.ringOfDefinition : Set C) := by
      refine weightedEval_mem_pow_smul_of_coeff P hϖ.isUnit
        (mem_weightedRestrictedSubring.mp (G i - F i).property) (fun ν ↦ ?_) t
      obtain ⟨r, hr⟩ := hFG i ν
      exact ⟨r, r.property, hr.symm⟩
    obtain ⟨r₁, hr₁, hdiff_eq⟩ := Set.mem_smul_set.mp hdiff_eval
    obtain ⟨r₂, hFt_eq⟩ := hFt i
    have hadd := weightedEval_add hid ht_bd
      (mem_weightedRestrictedSubring.mp (G i - F i).property)
      (mem_weightedRestrictedSubring.mp (F i).property)
    rw [← AddMemClass.coe_add, sub_add_cancel] at hadd
    refine ⟨⟨r₁, hr₁⟩ + r₂, ?_⟩
    rw [hadd, ← hdiff_eq, hFt_eq, smul_eq_mul, AddMemClass.coe_add, mul_add]
  exact existsUnique_weightedEval_tateSeries_eq_zero P ϖ hϖ N G hG t k e he M' hJM' hGt

end Newton

section Functoriality

/-- **Functoriality of Newton roots along a continuous ring homomorphism:** if `u ∈ C₀^N` is a
zero of `F` congruent to `t` modulo `ϖ ^ (k + 1)` under the Newton hypotheses over `(C, P, ϖ)`,
and `φ : C →+* C'` is continuous with `φ(C₀) ⊆ C'₀`, then `φ ∘ u` is the unique zero of the mapped
system `tateSeries.mapRingHom hφ ∘ F` congruent to `φ ∘ t` modulo `(φ ϖ) ^ (k + 1)`. -/
theorem map_weightedEval_tateSeries_eq_zero
    {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
    [NonarchimedeanRing C] [CompleteSpace C]
    (P : PairOfDefinition C) (ϖ : P.ringOfDefinition) (hϖ : IsPseudoUniformizer (ϖ : C))
    {C' : Type*} [CommRing C'] [UniformSpace C'] [IsUniformAddGroup C']
    [NonarchimedeanRing C'] [CompleteSpace C'] [T0Space C'] (P' : PairOfDefinition C')
    {φ : C →+* C'} (hφ : Continuous φ)
    (hPφ : ∀ a ∈ P.ringOfDefinition, φ a ∈ P'.ringOfDefinition)
    {N : ℕ} (F : Fin N → tateSeries N C)
    (hF : ∀ i, F i ∈ tateSeriesPlus N C P.ringOfDefinition)
    (t : Fin N → P.ringOfDefinition) {k : ℕ}
    (M : Matrix (Fin N) (Fin N) P.ringOfDefinition)
    (hJ : M.map Subtype.val *
        Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (t l : C))
          (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) C))) =
      (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C))
    {u : Fin N → P.ringOfDefinition}
    (hu_mod : ∀ i, ϖ ^ (k + 1) ∣ u i - t i)
    (hu_zero : ∀ i, weightedEval (RingHom.id C) (fun l ↦ (u l : C))
      (F i : MvPowerSeries (Fin N) C) = 0) :
    let ϖ' : P'.ringOfDefinition := ⟨φ ϖ, hPφ _ ϖ.property⟩
    let t' : Fin N → P'.ringOfDefinition := fun l ↦ ⟨φ (t l), hPφ _ (t l).property⟩
    let u' : Fin N → P'.ringOfDefinition := fun l ↦ ⟨φ (u l), hPφ _ (u l).property⟩
    (∀ i, ϖ' ^ (k + 1) ∣ u' i - t' i) ∧
    (∀ i, weightedEval (RingHom.id C') (fun l ↦ (u' l : C'))
      (tateSeries.mapRingHom hφ (F i) : MvPowerSeries (Fin N) C') = 0) ∧
    ∀ v' : Fin N → P'.ringOfDefinition,
      (∀ i, ϖ' ^ (k + 1) ∣ v' i - t' i) →
      (∀ i, weightedEval (RingHom.id C') (fun l ↦ (v' l : C'))
        (tateSeries.mapRingHom hφ (F i) : MvPowerSeries (Fin N) C') = 0) →
      v' = u' := by
  intro ϖ' t' u'
  let φ₀ : P.ringOfDefinition →+* P'.ringOfDefinition :=
    φ.restrict P.ringOfDefinition P'.ringOfDefinition hPφ
  have hu'_mod (i) : ϖ' ^ (k + 1) ∣ u' i - t' i := by
    have h := map_dvd φ₀ (hu_mod i)
    rwa [map_pow, map_sub] at h
  have hu'_zero (i) : weightedEval (RingHom.id C') (fun l ↦ (u' l : C'))
      (tateSeries.mapRingHom hφ (F i) : MvPowerSeries (Fin N) C') = 0 := by
    dsimp only [u']
    rw [← map_weightedEval_tateSeries hφ
      (fun l ↦ P.isBounded_ringOfDefinition.isPowerBounded_of_mem (u l).property) (F i),
      hu_zero i, map_zero]
  refine ⟨hu'_mod, hu'_zero, fun v' hv'_mod hv'_zero ↦ ?_⟩
  let M' : Matrix (Fin N) (Fin N) P'.ringOfDefinition := M.map φ₀
  have hF' (i) := tateSeries.mapRingHom_mem_tateSeriesPlus hφ hPφ (hF i)
  have hJ' : M'.map Subtype.val *
      Matrix.of (fun i j ↦ weightedEval (RingHom.id C') (fun l ↦ (t' l : C'))
        (MvPowerSeries.pderiv j (tateSeries.mapRingHom hφ (F i) : MvPowerSeries (Fin N) C'))) =
      (ϖ' : C') ^ k • (1 : Matrix (Fin N) (Fin N) C') := by
    have hJφ : (Matrix.of fun i j ↦ weightedEval (RingHom.id C') (fun l ↦ (t' l : C'))
          (MvPowerSeries.pderiv j (tateSeries.mapRingHom hφ (F i) : MvPowerSeries (Fin N) C'))) =
        (Matrix.of fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (t l : C))
          (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) C))).map φ := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply, ← tateSeries.coe_pderiv,
        tateSeries.pderiv_mapRingHom]
      exact (map_weightedEval_tateSeries hφ
        (fun m ↦ P.isBounded_ringOfDefinition.isPowerBounded_of_mem (t m).property)
        (tateSeries.pderiv j (F i))).symm
    have hM' : M'.map Subtype.val = (M.map Subtype.val).map φ := rfl
    rw [hM', hJφ]
    simpa only [map_pow] using Matrix.map_mul_eq_smul_one φ hJ
  exact eq_of_weightedEval_eq_zero P' (hϖ.map hφ)
    (fun i ↦ mem_weightedRestrictedSubring.mp (tateSeries.mapRingHom hφ (F i)).property)
    (fun i ↦ mem_tateSeriesPlus_iff.mp (hF' i))
    hJ' hv'_mod hv'_zero hu'_mod hu'_zero

end Functoriality

end TauCeti.Huber

end

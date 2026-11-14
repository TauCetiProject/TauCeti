/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.StandardEtale.TateSeries
public import TauCeti.RingTheory.Huber.WeightedEval.Newton
import Mathlib.RingTheory.Jacobson.Ideal
import TauCeti.RingTheory.Huber.Padic.Field
import TauCeti.RingTheory.Huber.WeightedEval.Continuous
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PairOfDefinition
import TauCeti.RingTheory.Subsemiring.SpanSingleton

/-!
# Multivariable Newton–Hensel lifting for `tateSeries`

Let `C` be a complete Hausdorff nonarchimedean ring with a pair of definition `P` whose ring of
definition `C₀` contains a pseudouniformiser `ϖ` of `C`. Given a square system
`F : Fin N → tateSeries N C` with integral coefficients `F i ∈ tateSeriesPlus N C C₀`, an initial
point `t : Fin N → C₀` whose Jacobian matrix `J(t) = (∂ⱼFᵢ(t))` admits an integral scaled inverse
`M * J(t) = ϖ ^ k • 1`, and an initial residual bound `Fᵢ(t) ∈ ϖ ^ e • C₀` with `2 * k + 1 ≤ e`,
this file packages `TauCeti.Huber.existsUnique_weightedEval_eq_zero` and
`TauCeti.Huber.pow_dvd_sub_of_weightedEval_eq_zero` on `tateSeries N C` together with three
companions needed for lifting standard étale algebras:

1. **Existence, uniqueness, and quantitative error bound**
   (`TauCeti.Huber.exists_unique_zero_restrictedPowerSeries`): there is a unique zero `u ∈ C₀^N` of
   `F` congruent to `t` modulo `ϖ ^ (k + 1)`, and it satisfies `u ≡ t mod ϖ ^ (e - k)`.
2. **Stability of the scaled Jacobian inverse**
   (`TauCeti.Huber.exists_mul_jacobian_eq_pow_smul_of_dvd`): for *any* `u ∈ C₀^N` with
   `u ≡ t mod ϖ ^ (k + 1)`, Taylor's estimate gives `J(u) ≡ J(t) mod ϖ ^ (k + 1)`, so
   `M * J(u) = ϖ ^ k • U` for a matrix `U ≡ 1 mod ϖ` over the `ϖ`-adically complete ring `C₀`;
   inverting `U` produces an integral matrix `M' ≡ M mod ϖ` satisfying both
   `M' * J(u) = ϖ ^ k • 1` and `J(u) * M' = ϖ ^ k • 1`.
3. **Functoriality and restricted-series parameters**
   (`TauCeti.Huber.map_weightedEval_tateSeries`, `TauCeti.Huber.map_zero_restrictedPowerSeries`,
   `TauCeti.Huber.exists_unique_zero_tateSeries_parameters`): continuous ring homomorphisms
   compatible with rings of definition preserve evaluations and hence send the lifted zero of `F`
   to the unique lifted zero of the mapped system; applying the theorem to the complete Tate ring
   `tateSeries M C` lifts approximate zeros with restricted-series parameters in `C₀⟨S₁, …, S_M⟩`.

## Main results

* `TauCeti.Huber.exists_unique_zero_restrictedPowerSeries`: multivariable Newton–Hensel lifting and
  quantitative error bound `u ≡ t mod ϖ ^ (e - k)` on `tateSeries N C`.
* `TauCeti.Huber.exists_mul_jacobian_eq_pow_smul_of_dvd`: two-sided `ϖ ^ k`-scaled Jacobian inverse
  `M' ≡ M mod ϖ` at any perturbed point `u ≡ t mod ϖ ^ (k + 1)`.
* `TauCeti.Huber.map_weightedEval_tateSeries` and `TauCeti.Huber.map_zero_restrictedPowerSeries`:
  compatibility of evaluation and Newton roots with continuous ring homomorphisms.
* `TauCeti.Huber.exists_unique_zero_tateSeries_parameters`: Newton–Hensel lifting over the
  parameter ring `tateSeries M C` with integral ring of definition `tateSeriesPlus M C C₀`.

## References

* R. Huber, *Étale Cohomology of Rigid Analytic Varieties and Adic Spaces*, Vieweg (1996),
  Proposition 1.7.1.
* O. Gabber and L. Ramero, *Almost Ring Theory*, Lecture Notes in Math. **1800**, Springer (2003),
  Lemma 5.4.8.
-/

public section

open Matrix Pointwise

namespace TauCeti.Huber

section Newton

variable {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
  [NonarchimedeanRing C] [CompleteSpace C]

/-- **Multivariable Newton–Hensel lifting for `tateSeries`:** if `F : Fin N → tateSeries N C` has
coefficients in `P.ringOfDefinition`, its Jacobian at `t` has an integral `ϖ ^ k`-scaled left
inverse `M`, and `F(t) ≡ 0 mod ϖ ^ e` with `2 * k + 1 ≤ e`, then `F` has a unique zero `u` in
`P.ringOfDefinition^N` congruent to `t` modulo `ϖ ^ (k + 1)`, and `u` satisfies
`u ≡ t mod ϖ ^ (e - k)`. -/
theorem exists_unique_zero_restrictedPowerSeries [T0Space C]
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
    ∃! u : Fin N → P.ringOfDefinition,
      (∀ i, ϖ ^ (k + 1) ∣ u i - t i) ∧
      (∀ i, weightedEval (RingHom.id C) (fun l ↦ (u l : C))
        (F i : MvPowerSeries (Fin N) C) = 0) ∧
      (∀ i, ϖ ^ (e - k) ∣ u i - t i) := by
  have hFres : ∀ i, IsWeightedRestricted (fun _ : Fin N ↦ ({1} : Set C))
      (F i : MvPowerSeries (Fin N) C) :=
    fun i ↦ mem_weightedRestrictedSubring.mp (F i).2
  have hF₀ : ∀ i ν, MvPowerSeries.coeff ν (F i : MvPowerSeries (Fin N) C) ∈
      P.ringOfDefinition :=
    fun i ↦ mem_tateSeriesPlus_iff.mp (hF i)
  have hFt_smul : ∀ i, weightedEval (RingHom.id C) (fun l ↦ (t l : C))
      (F i : MvPowerSeries (Fin N) C) ∈ (ϖ : C) ^ e • (P.ringOfDefinition : Set C) := by
    intro i
    obtain ⟨r, hr⟩ := hFt i
    exact ⟨r, r.2, hr.symm⟩
  have hFt_base : ∀ i, weightedEval (RingHom.id C) (fun l ↦ (t l : C))
      (F i : MvPowerSeries (Fin N) C) ∈
        (ϖ : C) ^ (2 * k + 1) • (P.ringOfDefinition : Set C) := by
    intro i
    obtain ⟨r, hr⟩ := hFt i
    refine ⟨(ϖ ^ (e - (2 * k + 1)) * r : P.ringOfDefinition),
      (ϖ ^ (e - (2 * k + 1)) * r : P.ringOfDefinition).2, ?_⟩
    push_cast
    rw [hr, smul_eq_mul, ← mul_assoc, ← pow_add, Nat.add_sub_of_le he]
  obtain ⟨u, ⟨hu_mod, hu_zero⟩, hu_uniq⟩ :=
    existsUnique_weightedEval_eq_zero P hϖ hFres hF₀ t hJ hFt_base
  have hu_err : ∀ i, ϖ ^ (e - k) ∣ u i - t i :=
    pow_dvd_sub_of_weightedEval_eq_zero P hϖ.isUnit hFres hF₀ hJ hFt_smul hu_mod hu_zero
  exact ⟨u, ⟨hu_mod, hu_zero, hu_err⟩, fun u' ⟨hu'_mod, hu'_zero, _⟩ ↦
    hu_uniq u' ⟨hu'_mod, hu'_zero⟩⟩

/-- **Uniqueness of the Newton root in `t + ϖ ^ (k + 1) C₀^N`**, without needing the refined error
bound `u' ≡ t mod ϖ ^ (e - k)` as an input. -/
theorem eq_of_zero_restrictedPowerSeries [T0Space C]
    (P : PairOfDefinition C) (ϖ : P.ringOfDefinition) (hϖ : IsPseudoUniformizer (ϖ : C))
    {N : ℕ} {F : Fin N → tateSeries N C}
    (hF : ∀ i, F i ∈ tateSeriesPlus N C P.ringOfDefinition)
    {t : Fin N → P.ringOfDefinition} {k : ℕ}
    {M : Matrix (Fin N) (Fin N) P.ringOfDefinition}
    (hJ : M.map Subtype.val *
        Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (t l : C))
          (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) C))) =
      (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C))
    (hFt : ∀ i, weightedEval (RingHom.id C) (fun l ↦ (t l : C))
      (F i : MvPowerSeries (Fin N) C) ∈
        (ϖ : C) ^ (2 * k + 1) • (P.ringOfDefinition : Set C))
    {u u' : Fin N → P.ringOfDefinition}
    (hu : ∀ i, ϖ ^ (k + 1) ∣ u i - t i)
    (hFu : ∀ i, weightedEval (RingHom.id C) (fun l ↦ (u l : C))
      (F i : MvPowerSeries (Fin N) C) = 0)
    (hu' : ∀ i, ϖ ^ (k + 1) ∣ u' i - t i)
    (hFu' : ∀ i, weightedEval (RingHom.id C) (fun l ↦ (u' l : C))
      (F i : MvPowerSeries (Fin N) C) = 0) :
    u = u' :=
  (existsUnique_weightedEval_eq_zero P hϖ
    (fun i ↦ mem_weightedRestrictedSubring.mp (F i).2)
    (fun i ↦ mem_tateSeriesPlus_iff.mp (hF i))
    t hJ hFt).unique ⟨hu, hFu⟩ ⟨hu', hFu'⟩

/-- **First-order congruence for integral restricted power series:** if
`g ∈ tateSeriesPlus N C P.ringOfDefinition` and `u ≡ t mod ϖ ^ m` coordinatewise in
`P.ringOfDefinition`, then `g(u) - g(t) ∈ ϖ ^ m • P.ringOfDefinition`. -/
theorem weightedEval_sub_mem_pow_smul
    (P : PairOfDefinition C) (ϖ : P.ringOfDefinition) (hϖ : IsUnit (ϖ : C))
    {N : ℕ} {g : tateSeries N C} (hg : g ∈ tateSeriesPlus N C P.ringOfDefinition)
    {t u : Fin N → P.ringOfDefinition} {m : ℕ} (hu : ∀ l, ϖ ^ m ∣ u l - t l) :
    weightedEval (RingHom.id C) (fun l ↦ (u l : C)) (g : MvPowerSeries (Fin N) C) -
      weightedEval (RingHom.id C) (fun l ↦ (t l : C)) (g : MvPowerSeries (Fin N) C) ∈
        (ϖ : C) ^ m • (P.ringOfDefinition : Set C) := by
  have hg_res := mem_weightedRestrictedSubring.mp g.2
  have hg₀ := mem_tateSeriesPlus_iff.mp hg
  have htaylor := weightedEval_sub_weightedEval_sub_sum_mem_pow_smul P hϖ hg_res hg₀
    (t := t) (x := t) (x' := u) (a := 0) (b := m) (Nat.zero_le _)
    (fun _ ↦ by rw [sub_self]; exact dvd_zero _) hu
  rw [zero_add] at htaylor
  let gu : P.ringOfDefinition :=
    ⟨_, weightedEval_mem_ringOfDefinition P hg_res hg₀ u⟩
  let gt : P.ringOfDefinition :=
    ⟨_, weightedEval_mem_ringOfDefinition P hg_res hg₀ t⟩
  let lin : P.ringOfDefinition := ∑ l,
    ⟨weightedEval (RingHom.id C) (fun r ↦ (t r : C))
        (MvPowerSeries.pderiv l (g : MvPowerSeries (Fin N) C)),
      weightedEval_mem_ringOfDefinition P (hg_res.pderiv_one_weight l)
        (MvPowerSeries.coeff_pderiv_mem hg₀ l) t⟩ * (u l - t l)
  have hrem : ϖ ^ m ∣ (gu - gt) - lin := by
    refine (SubsemiringClass.coe_mem_smul_iff_dvd P.ringOfDefinition).mp ?_
    convert htaylor using 1
    simp only [gu, gt, lin]
    push_cast
    rfl
  have hlin : ϖ ^ m ∣ lin :=
    Finset.dvd_sum fun l _ ↦ dvd_mul_of_dvd_right (hu l) _
  have hdvd : ϖ ^ m ∣ gu - gt := by
    simpa only [sub_add_cancel] using dvd_add hrem hlin
  exact (SubsemiringClass.coe_mem_smul_iff_dvd P.ringOfDefinition).mpr hdvd

private theorem isUnit_det_one_add_smul_of_isAdicComplete
    {R : Type*} [CommRing R] (ϖ : R) [IsAdicComplete (Ideal.span ({ϖ} : Set R)) R]
    {N : ℕ} (B : Matrix (Fin N) (Fin N) R) :
    IsUnit (1 + ϖ • B).det := by
  refine Ideal.isUnit_of_sub_one_mem_jacobson (1 + ϖ • B).det
    (IsAdicComplete.le_jacobson (Ideal.span ({ϖ} : Set R)) ?_)
  let q := Ideal.Quotient.mk (Ideal.span ({ϖ} : Set R))
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det,
    RingHom.mapMatrix_apply]
  have hBq : (1 + ϖ • B).map q = 1 := by
    ext i j
    have hqϖ : q ϖ = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ)
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, map_add, map_mul, hqϖ, zero_mul, add_zero]
    split_ifs <;> simp
  rw [hBq, det_one, sub_self]

private theorem matrix_mul_comm_of_mul_eq_smul_one
    {R : Type*} [CommRing R] {c : R} (hc : IsUnit c) {N : ℕ}
    {A B : Matrix (Fin N) (Fin N) R}
    (hAB : A * B = c • (1 : Matrix (Fin N) (Fin N) R)) :
    B * A = c • (1 : Matrix (Fin N) (Fin N) R) := by
  let u : Rˣ := hc.unit
  have hu : (u : R) = c := IsUnit.unit_spec hc
  have h1 : ((↑u⁻¹ : R) • A) * B = 1 := by
    rw [Matrix.smul_mul, hAB, ← hu, smul_smul, Units.inv_mul, one_smul]
  have h2 : B * ((↑u⁻¹ : R) • A) = 1 := mul_eq_one_comm.mp h1
  calc
    B * A = (u : R) • (B * ((↑u⁻¹ : R) • A)) := by
      rw [Matrix.mul_smul, smul_smul, Units.mul_inv, one_smul]
    _ = c • 1 := by rw [h2, hu]

/-- **Stability of the `ϖ ^ k`-scaled Jacobian inverse under `ϖ ^ (k + 1)`-perturbations:** if
`M * J(t) = ϖ ^ k • 1` and `u ≡ t mod ϖ ^ (k + 1)` in `P.ringOfDefinition^N` (for instance when `u`
is the Newton root of `F`), then there is an integral matrix `M' ≡ M mod ϖ` satisfying both
`M' * J(u) = ϖ ^ k • 1` and `J(u) * M' = ϖ ^ k • 1`. -/
theorem exists_mul_jacobian_eq_pow_smul_of_dvd [T0Space C]
    (P : PairOfDefinition C) (ϖ : P.ringOfDefinition) (hϖ : IsPseudoUniformizer (ϖ : C))
    {N : ℕ} {F : Fin N → tateSeries N C}
    (hF : ∀ i, F i ∈ tateSeriesPlus N C P.ringOfDefinition)
    {t u : Fin N → P.ringOfDefinition} {k : ℕ}
    {M : Matrix (Fin N) (Fin N) P.ringOfDefinition}
    (hJ : M.map Subtype.val *
        Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (t l : C))
          (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) C))) =
      (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C))
    (hu : ∀ l, ϖ ^ (k + 1) ∣ u l - t l) :
    ∃ M' : Matrix (Fin N) (Fin N) P.ringOfDefinition,
      (∀ i j, ϖ ∣ M' i j - M i j) ∧
      M'.map Subtype.val *
        Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (u l : C))
          (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) C))) =
        (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C) ∧
      Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (u l : C))
          (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) C))) *
        M'.map Subtype.val =
        (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C) := by
  have := P.isAdicComplete_span_singleton ϖ hϖ
  let J₀ (x : Fin N → P.ringOfDefinition) : Matrix (Fin N) (Fin N) P.ringOfDefinition :=
    Matrix.of fun i j ↦
      ⟨weightedEval (RingHom.id C) (fun l ↦ (x l : C))
          (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) C)),
        weightedEval_mem_ringOfDefinition P
          ((mem_weightedRestrictedSubring.mp (F i).2).pderiv_one_weight j)
          (MvPowerSeries.coeff_pderiv_mem (mem_tateSeriesPlus_iff.mp (hF i)) j) x⟩
  have hJdiff : ∀ i j, ϖ ^ (k + 1) ∣ J₀ u i j - J₀ t i j := fun i j ↦ by
    refine (SubsemiringClass.coe_mem_smul_iff_dvd P.ringOfDefinition).mp ?_
    simpa only [J₀, Matrix.of_apply, AddSubgroupClass.coe_sub, Subring.coe_pow,
      ← tateSeries.coe_pderiv] using
      weightedEval_sub_mem_pow_smul P ϖ hϖ.isUnit
        (tateSeries.pderiv_mem_tateSeriesPlus (hF i) j) hu
  choose Δ hΔ using hJdiff
  have hJu_eq : J₀ u = J₀ t + ϖ ^ (k + 1) • Matrix.of Δ := by
    refine Matrix.ext fun i j ↦ ?_
    have hij := hΔ i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    linear_combination hij
  have hMJt : M * J₀ t = ϖ ^ k • (1 : Matrix (Fin N) (Fin N) P.ringOfDefinition) := by
    ext i j
    have hij := congrFun (congrFun hJ i) j
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul] at hij ⊢
    push_cast
    convert hij using 2
    · simp [J₀]
    · split_ifs <;> simp
  let U : Matrix (Fin N) (Fin N) P.ringOfDefinition := 1 + ϖ • (M * Matrix.of Δ)
  have hMJu : M * J₀ u = ϖ ^ k • U := by
    rw [hJu_eq, Matrix.mul_add, hMJt, Matrix.mul_smul, pow_succ, mul_comm (ϖ ^ k) ϖ,
      ← smul_smul, smul_add]
    simp [smul_smul, mul_comm]
  have hUdet : IsUnit U.det := isUnit_det_one_add_smul_of_isAdicComplete ϖ (M * Matrix.of Δ)
  let M' : Matrix (Fin N) (Fin N) P.ringOfDefinition := U⁻¹ * M
  have hUM' : U * M' = M := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hUdet, Matrix.one_mul]
  have hM'mod : ∀ i j, ϖ ∣ M' i j - M i j := fun i j ↦ ⟨-((M * Matrix.of Δ * M') i j), by
    have hij := congrFun (congrFun hUM' i) j
    have hUExpand : U * M' = M' + ϖ • (M * Matrix.of Δ * M') := by
      simp [U, Matrix.add_mul, Matrix.mul_assoc]
    rw [hUExpand] at hij
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hij
    linear_combination hij⟩
  have hM'Ju₀ : M' * J₀ u = ϖ ^ k • (1 : Matrix (Fin N) (Fin N) P.ringOfDefinition) := by
    rw [Matrix.mul_assoc, hMJu, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hUdet]
  have hleft : M'.map Subtype.val *
      Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun l ↦ (u l : C))
        (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) C))) =
      (ϖ : C) ^ k • (1 : Matrix (Fin N) (Fin N) C) := by
    ext i j
    have hij := congrArg Subtype.val (congrFun (congrFun hM'Ju₀ i) j)
    simp only [J₀, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul] at hij ⊢
    push_cast at hij
    convert hij using 1
    split_ifs <;> simp
  exact ⟨M', hM'mod, hleft, matrix_mul_comm_of_mul_eq_smul_one (hϖ.isUnit.pow k) hleft⟩

end Newton

section Functoriality

/-- **Compatibility of `weightedEval` on `tateSeries` with continuous ring homomorphisms:** if
`φ : C →+* C'` is continuous between complete Hausdorff nonarchimedean rings with pairs of
definition `P` and `P'` such that `φ(C₀) ⊆ C'₀`, then evaluating `g : tateSeries N C` at
`x ∈ C₀^N` and applying `φ` agrees with evaluating `tateSeries.mapRingHom hφ g` at `φ ∘ x`. -/
theorem map_weightedEval_tateSeries
    {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
    [NonarchimedeanRing C] [CompleteSpace C] [T0Space C] (P : PairOfDefinition C)
    {C' : Type*} [CommRing C'] [UniformSpace C'] [IsUniformAddGroup C']
    [NonarchimedeanRing C'] [CompleteSpace C'] [T0Space C'] (P' : PairOfDefinition C')
    {φ : C →+* C'} (hφ : Continuous φ)
    (hPφ : ∀ a ∈ P.ringOfDefinition, φ a ∈ P'.ringOfDefinition)
    {N : ℕ} (x : Fin N → P.ringOfDefinition) (g : tateSeries N C) :
    φ (weightedEval (RingHom.id C) (fun l ↦ (x l : C)) (g : MvPowerSeries (Fin N) C)) =
      weightedEval (RingHom.id C') (fun l ↦ φ (x l))
        (tateSeries.mapRingHom hφ g : MvPowerSeries (Fin N) C') := by
  have hx : IsWeightBounded (RingHom.id C) (fun _ : Fin N ↦ ({1} : Set C))
      (fun l ↦ (x l : C)) :=
    (isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun l ↦
      P.isBounded_ringOfDefinition.isPowerBounded_of_mem (x l).2
  have hx' : IsWeightBounded (RingHom.id C') (fun _ : Fin N ↦ ({1} : Set C'))
      (fun l ↦ φ (x l)) :=
    (isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun l ↦
      P'.isBounded_ringOfDefinition.isPowerBounded_of_mem (hPφ _ (x l).2)
  let evC := weightedEvalHom isWeightFamily_one_weight continuous_id.continuousAt hx
  let evC' := weightedEvalHom isWeightFamily_one_weight continuous_id.continuousAt hx'
  have heq : φ.comp evC = evC'.comp (tateSeries.mapRingHom hφ) :=
    weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
      (hφ.comp (continuous_weightedEvalHom isWeightFamily_one_weight
        continuous_id.continuousAt hx))
      ((continuous_weightedEvalHom isWeightFamily_one_weight continuous_id.continuousAt hx').comp
        (tateSeries.continuous_mapRingHom hφ))
      (fun a ↦ by
        dsimp only [evC, evC']
        rw [RingHom.comp_apply, RingHom.comp_apply, weightedEvalHom_weightedC, RingHom.id_apply,
          ← algebraMap_weightedRestrictedSubring, tateSeries.mapRingHom_algebraMap,
          algebraMap_weightedRestrictedSubring, weightedEvalHom_weightedC, RingHom.id_apply])
      (fun i ↦ by
        dsimp only [evC, evC']
        rw [RingHom.comp_apply, RingHom.comp_apply, weightedEvalHom_weightedX,
          ← tateSeries.X_eq_weightedX, tateSeries.mapRingHom_X, tateSeries.X_eq_weightedX,
          weightedEvalHom_weightedX])
  simpa only [RingHom.comp_apply, evC, evC', coe_weightedEvalHom] using RingHom.congr_fun heq g

/-- **Functoriality of Newton roots along a continuous ring homomorphism:** if `u ∈ C₀^N` is a
zero of `F` congruent to `t` modulo `ϖ ^ (k + 1)` under the Newton hypotheses over `(C, P, ϖ)`,
and `φ : C →+* C'` is continuous with `φ(C₀) ⊆ C'₀`, then `φ ∘ u` is the unique zero of the mapped
system `tateSeries.mapRingHom hφ ∘ F` congruent to `φ ∘ t` modulo `(φ ϖ) ^ (k + 1)`. -/
theorem map_zero_restrictedPowerSeries
    {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
    [NonarchimedeanRing C] [CompleteSpace C] [T0Space C]
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
    let ϖ' : P'.ringOfDefinition := ⟨φ ϖ, hPφ _ ϖ.2⟩
    let t' : Fin N → P'.ringOfDefinition := fun l ↦ ⟨φ (t l), hPφ _ (t l).2⟩
    let u' : Fin N → P'.ringOfDefinition := fun l ↦ ⟨φ (u l), hPφ _ (u l).2⟩
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
  have hϖ' : IsPseudoUniformizer (ϖ' : C') := hϖ.map hφ
  have hu'_mod : ∀ i, ϖ' ^ (k + 1) ∣ u' i - t' i := by
    intro i
    obtain ⟨q, hq⟩ := hu_mod i
    exact ⟨⟨φ q, hPφ _ q.2⟩, Subtype.ext <| by
      simpa only [u', t', ϖ', AddSubgroupClass.coe_sub, Subring.coe_mul, Subring.coe_pow,
        map_sub, map_mul, map_pow] using congrArg (fun z : P.ringOfDefinition ↦ φ (z : C)) hq⟩
  have hu'_zero : ∀ i, weightedEval (RingHom.id C') (fun l ↦ (u' l : C'))
      (tateSeries.mapRingHom hφ (F i) : MvPowerSeries (Fin N) C') = 0 := by
    intro i
    dsimp only [u']
    rw [← map_weightedEval_tateSeries P P' hφ hPφ u (F i), hu_zero i, map_zero]
  refine ⟨hu'_mod, hu'_zero, fun v' hv'_mod hv'_zero ↦ ?_⟩
  let M' : Matrix (Fin N) (Fin N) P'.ringOfDefinition := M.map φ₀
  have hF' : ∀ i, tateSeries.mapRingHom hφ (F i) ∈ tateSeriesPlus N C' P'.ringOfDefinition :=
    fun i ↦ tateSeries.mapRingHom_mem_tateSeriesPlus hφ hPφ (hF i)
  have hJ' : M'.map Subtype.val *
      Matrix.of (fun i j ↦ weightedEval (RingHom.id C') (fun l ↦ (t' l : C'))
        (MvPowerSeries.pderiv j (tateSeries.mapRingHom hφ (F i) : MvPowerSeries (Fin N) C'))) =
      (ϖ' : C') ^ k • (1 : Matrix (Fin N) (Fin N) C') := by
    ext i j
    have hij := congrArg φ (congrFun (congrFun hJ i) j)
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, map_sum, map_mul, map_pow] at hij ⊢
    convert hij using 1
    · refine Finset.sum_congr rfl fun l _ ↦ congrArg (φ (M i l : C) * ·) ?_
      have hpderiv : MvPowerSeries.pderiv j
          (tateSeries.mapRingHom hφ (F l) : MvPowerSeries (Fin N) C') =
          (tateSeries.mapRingHom hφ (tateSeries.pderiv j (F l)) : MvPowerSeries (Fin N) C') := by
        rw [← tateSeries.coe_pderiv, tateSeries.pderiv_mapRingHom]
      rw [hpderiv, ← map_weightedEval_tateSeries P P' hφ hPφ t (tateSeries.pderiv j (F l)),
        tateSeries.coe_pderiv]
    · split_ifs <;> simp [ϖ']
  obtain ⟨Mu', -, hMu', -⟩ :=
    exists_mul_jacobian_eq_pow_smul_of_dvd P' ϖ' hϖ' hF' hJ' hu'_mod
  have hv'_u' : ∀ i, ϖ' ^ (k + 1) ∣ v' i - u' i := fun i ↦ by
    have hdvd := dvd_sub (hv'_mod i) (hu'_mod i)
    rwa [sub_sub_sub_cancel_right] at hdvd
  exact eq_of_zero_restrictedPowerSeries P' ϖ' hϖ' hF' hMu'
    (fun i ↦ by rw [hu'_zero i]; exact ⟨0, P'.ringOfDefinition.zero_mem, by simp⟩)
    hv'_u' hv'_zero (fun _ ↦ by rw [sub_self]; exact dvd_zero _) hu'_zero

/-- **Newton–Hensel lifting with restricted-series parameters:** applying
`exists_unique_zero_restrictedPowerSeries` to the complete Hausdorff ring `tateSeries M C` with
pair of definition `P.weighted isWeightFamily_one_weight` (whose ring of definition is
`tateSeriesPlus M C P.ringOfDefinition`) lifts approximate roots with `M` restricted-series
parameters. -/
theorem exists_unique_zero_tateSeries_parameters
    {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
    [NonarchimedeanRing C] [CompleteSpace C] [T0Space C]
    (P : PairOfDefinition C) (ϖ : P.ringOfDefinition) (hϖ : IsPseudoUniformizer (ϖ : C))
    (M N : ℕ) :
    let PM : PairOfDefinition (tateSeries M C) :=
      P.weighted (T := fun _ : Fin M ↦ ({1} : Set C)) isWeightFamily_one_weight
    let ϖM : PM.ringOfDefinition :=
      ⟨algebraMap C (tateSeries M C) (ϖ : C), by
        rw [PairOfDefinition.weighted_ringOfDefinition,
          PairOfDefinition.weightedRingOfDefinition_def, ← tateSeriesPlus_eq_weightedSubring,
          algebraMap_mem_tateSeriesPlus_iff]
        exact ϖ.2⟩
    ∀ (F : Fin N → tateSeries N (tateSeries M C))
      (_ : ∀ i, F i ∈ tateSeriesPlus N (tateSeries M C) PM.ringOfDefinition)
      (t : Fin N → PM.ringOfDefinition) (k e : ℕ) (_ : 2 * k + 1 ≤ e)
      (Mat : Matrix (Fin N) (Fin N) PM.ringOfDefinition)
      (_ : Mat.map Subtype.val *
          Matrix.of (fun i j ↦ weightedEval (RingHom.id (tateSeries M C))
            (fun l ↦ (t l : tateSeries M C))
            (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin N) (tateSeries M C)))) =
        (ϖM : tateSeries M C) ^ k • (1 : Matrix (Fin N) (Fin N) (tateSeries M C)))
      (_ : ∀ i, ∃ r : PM.ringOfDefinition,
        weightedEval (RingHom.id (tateSeries M C)) (fun l ↦ (t l : tateSeries M C))
          (F i : MvPowerSeries (Fin N) (tateSeries M C)) =
          (ϖM : tateSeries M C) ^ e * (r : tateSeries M C)),
      ∃! u : Fin N → PM.ringOfDefinition,
        (∀ i, ϖM ^ (k + 1) ∣ u i - t i) ∧
        (∀ i, weightedEval (RingHom.id (tateSeries M C)) (fun l ↦ (u l : tateSeries M C))
          (F i : MvPowerSeries (Fin N) (tateSeries M C)) = 0) ∧
        (∀ i, ϖM ^ (e - k) ∣ u i - t i) := by
  intro PM ϖM F hF t k e he Mat hJ hFt
  have hϖM : IsPseudoUniformizer (ϖM : tateSeries M C) := by
    dsimp only [ϖM]
    rw [algebraMap_weightedRestrictedSubring]
    exact hϖ.map (continuous_weightedC isWeightFamily_one_weight)
  exact exists_unique_zero_restrictedPowerSeries PM ϖM hϖM N F hF t k e he Mat hJ hFt

end Functoriality

section Checks

/-- Linear sanity check: `F(T) = T - (t₀ + ϖ · r)` with `k = 0`, `e = 1` has a unique lifted zero
`u₀` congruent to `t₀` modulo `ϖ`. -/
example {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C]
    [NonarchimedeanRing C] [CompleteSpace C] [T0Space C]
    (P : PairOfDefinition C) (ϖ : P.ringOfDefinition) (hϖ : IsPseudoUniformizer (ϖ : C))
    (t₀ r : P.ringOfDefinition) :
    let F : Fin 1 → tateSeries 1 C := fun _ ↦
      tateSeries.X 1 C 0 - algebraMap C (tateSeries 1 C) ((t₀ : C) + (ϖ : C) * (r : C))
    ∃! u : Fin 1 → P.ringOfDefinition,
      (∀ i, ϖ ^ 1 ∣ u i - (fun _ ↦ t₀) i) ∧
      (∀ i, weightedEval (RingHom.id C) (fun l ↦ (u l : C))
        (F i : MvPowerSeries (Fin 1) C) = 0) ∧
      (∀ i, ϖ ^ 1 ∣ u i - (fun _ ↦ t₀) i) := by
  intro F
  have hF : ∀ i, F i ∈ tateSeriesPlus 1 C P.ringOfDefinition := fun _ ↦
    sub_mem (tateSeries.X_mem_tateSeriesPlus P.ringOfDefinition 0)
      (algebraMap_mem_tateSeriesPlus_iff.mpr (add_mem t₀.2 (mul_mem ϖ.2 r.2)))
  have hb : IsWeightBounded (RingHom.id C) (fun _ : Fin 1 ↦ ({1} : Set C))
      (fun _ : Fin 1 ↦ (t₀ : C)) :=
    (isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun _ ↦
      P.isBounded_ringOfDefinition.isPowerBounded_of_mem t₀.2
  have hJ : (1 : Matrix (Fin 1) (Fin 1) P.ringOfDefinition).map Subtype.val *
      Matrix.of (fun i j ↦ weightedEval (RingHom.id C) (fun _ : Fin 1 ↦ (t₀ : C))
        (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin 1) C))) =
      (ϖ : C) ^ 0 • (1 : Matrix (Fin 1) (Fin 1) C) := by
    ext i j
    fin_cases i
    fin_cases j
    have hpderiv : tateSeries.pderiv 0 (F 0) = 1 := by
      dsimp only [F]
      rw [map_sub, tateSeries.pderiv_X_self, tateSeries.pderiv_algebraMap, sub_zero]
    have hev : weightedEval (RingHom.id C) (fun _ : Fin 1 ↦ (t₀ : C))
        (MvPowerSeries.pderiv 0 (F 0 : MvPowerSeries (Fin 1) C)) = 1 := by
      rw [← tateSeries.coe_pderiv, hpderiv, ← coe_weightedEvalHom isWeightFamily_one_weight
        continuous_id.continuousAt hb, map_one]
    simp [Matrix.mul_apply, hev]
  have hFt : ∀ i : Fin 1, ∃ q : P.ringOfDefinition,
      weightedEval (RingHom.id C) (fun _ : Fin 1 ↦ (t₀ : C)) (F i : MvPowerSeries (Fin 1) C) =
        (ϖ : C) ^ 1 * (q : C) := by
    intro i
    fin_cases i
    refine ⟨-r, ?_⟩
    have hev : weightedEvalHom isWeightFamily_one_weight continuous_id.continuousAt hb (F 0) =
        (t₀ : C) - ((t₀ : C) + (ϖ : C) * (r : C)) := by
      dsimp only [F]
      rw [map_sub, tateSeries.X_eq_weightedX, algebraMap_weightedRestrictedSubring,
        weightedEvalHom_weightedX, weightedEvalHom_weightedC, RingHom.id_apply]
    dsimp only
    rw [← coe_weightedEvalHom isWeightFamily_one_weight continuous_id.continuousAt hb, hev]
    push_cast
    ring
  simpa using exists_unique_zero_restrictedPowerSeries P ϖ hϖ 1 F hF (fun _ ↦ t₀) 0 1
    (by omega) 1 hJ hFt

/-- Genuine `k = 1` scaled-Jacobian check over `ℚ_[2]`: `F(T) = T^2 - 17` at `t₀ = 1` has
`F'(1) = 2 = 2 ^ 1` (not a `2`-adic unit!) and `F(1) = -16 = 2 ^ 4 · (-1)` (`e = 4 ≥ 2·1 + 1`),
yielding a unique square root `u ∈ ℤ_[2]` of `17` with `u ≡ 1 mod 4` and refined bound
`u ≡ 1 mod 8` (`2 ^ (4 - 1) = 8`). -/
example :
    let P := Padic.pairOfDefinition (p := 2)
    let ϖ : P.ringOfDefinition := ⟨(2 : ℚ_[2]), by
      rw [Padic.pairOfDefinition_ringOfDefinition]
      exact (2 : ℤ_[2]).2⟩
    let F : Fin 1 → tateSeries 1 ℚ_[2] := fun _ ↦
      tateSeries.X 1 ℚ_[2] 0 ^ 2 - algebraMap ℚ_[2] (tateSeries 1 ℚ_[2]) 17
    ∃! u : Fin 1 → P.ringOfDefinition,
      (∀ i, ϖ ^ 2 ∣ u i - (fun _ ↦ (1 : P.ringOfDefinition)) i) ∧
      (∀ i, weightedEval (RingHom.id ℚ_[2]) (fun l ↦ (u l : ℚ_[2]))
        (F i : MvPowerSeries (Fin 1) ℚ_[2]) = 0) ∧
      (∀ i, ϖ ^ 3 ∣ u i - (fun _ ↦ (1 : P.ringOfDefinition)) i) := by
  intro P ϖ F
  have hϖ : IsPseudoUniformizer (ϖ : ℚ_[2]) := by
    simpa [ϖ] using Padic.isPseudoUniformizer_p (p := 2)
  have hF : ∀ i, F i ∈ tateSeriesPlus 1 ℚ_[2] P.ringOfDefinition := fun _ ↦
    sub_mem (pow_mem (tateSeries.X_mem_tateSeriesPlus P.ringOfDefinition 0) 2)
      (algebraMap_mem_tateSeriesPlus_iff.mpr (by
        rw [Padic.pairOfDefinition_ringOfDefinition]
        exact (17 : ℤ_[2]).2))
  have hb : IsWeightBounded (RingHom.id ℚ_[2]) (fun _ : Fin 1 ↦ ({1} : Set ℚ_[2]))
      (fun _ : Fin 1 ↦ (1 : ℚ_[2])) :=
    (isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr fun _ ↦
      P.isBounded_ringOfDefinition.isPowerBounded_of_mem P.ringOfDefinition.one_mem
  have hJ : (1 : Matrix (Fin 1) (Fin 1) P.ringOfDefinition).map Subtype.val *
      Matrix.of (fun i j ↦ weightedEval (RingHom.id ℚ_[2]) (fun _ : Fin 1 ↦ (1 : ℚ_[2]))
        (MvPowerSeries.pderiv j (F i : MvPowerSeries (Fin 1) ℚ_[2]))) =
      (ϖ : ℚ_[2]) ^ 1 • (1 : Matrix (Fin 1) (Fin 1) ℚ_[2]) := by
    ext i j
    fin_cases i
    fin_cases j
    have hpderiv : tateSeries.pderiv 0 (F 0) = 2 • tateSeries.X 1 ℚ_[2] 0 := by
      dsimp only [F]
      rw [map_sub, tateSeries.pderiv_pow, tateSeries.pderiv_X_self, tateSeries.pderiv_algebraMap,
        sub_zero, pow_one, mul_one]
    have hev : weightedEval (RingHom.id ℚ_[2]) (fun _ : Fin 1 ↦ (1 : ℚ_[2]))
        (MvPowerSeries.pderiv 0 (F 0 : MvPowerSeries (Fin 1) ℚ_[2])) = 2 := by
      rw [← tateSeries.coe_pderiv, hpderiv,
        ← coe_weightedEvalHom isWeightFamily_one_weight continuous_id.continuousAt hb,
        two_smul, map_add, tateSeries.X_eq_weightedX, weightedEvalHom_weightedX]
      norm_num
    simp [Matrix.mul_apply, hev, ϖ]
  have hFt : ∀ i : Fin 1, ∃ r : P.ringOfDefinition,
      weightedEval (RingHom.id ℚ_[2]) (fun _ : Fin 1 ↦ (1 : ℚ_[2]))
        (F i : MvPowerSeries (Fin 1) ℚ_[2]) = (ϖ : ℚ_[2]) ^ 4 * (r : ℚ_[2]) := by
    intro i
    fin_cases i
    refine ⟨-1, ?_⟩
    have hev : weightedEvalHom isWeightFamily_one_weight continuous_id.continuousAt hb (F 0) =
        (1 : ℚ_[2]) ^ 2 - 17 := by
      dsimp only [F]
      rw [map_sub, map_pow, tateSeries.X_eq_weightedX, algebraMap_weightedRestrictedSubring,
        weightedEvalHom_weightedX, weightedEvalHom_weightedC, RingHom.id_apply]
    dsimp only
    rw [← coe_weightedEvalHom isWeightFamily_one_weight continuous_id.continuousAt hb, hev]
    push_cast
    norm_num [ϖ]
  simpa using exists_unique_zero_restrictedPowerSeries P ϖ hϖ 1 F hF (fun _ ↦ 1) 1 4
    (by omega) 1 hJ hFt

end Checks

end TauCeti.Huber

end

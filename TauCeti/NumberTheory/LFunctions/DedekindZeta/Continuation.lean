/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Continued.Basic
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Card
import TauCeti.NumberTheory.NumberField.Discriminant.Basic
import TauCeti.NumberTheory.NumberField.Units.Dirichlet

/-!
# Meromorphic continuation and analytic properties of the Dedekind zeta function

Identifying the continued function `(TauCeti.LFunctions.dedekindZetaData K).continuedL` of the
Dedekind zeta card with `TauCeti.LFunctions.dedekindZetaC K` yields the global meromorphic
properties of `dedekindZetaC K` from `TauCeti.LFunctions.completedDedekindZeta K` and the generic
card-continuation API.

Because the reciprocal archimedean factor `|d_K|^(-s/2) Γ_ℝ(s)⁻¹^r₁ Γ_ℂ(s)⁻¹^r₂` is entire and
vanishes at `s = 0` to order `r₁ + r₂ ≥ 1` while `completedDedekindZeta K` is analytic off `{0, 1}`
with simple poles at `0` and `1`, the reciprocal archimedean vanishing cancels the simple pole of
`Λ_K` at `0` in the meromorphic product. Consequently, `dedekindZetaC K` is analytic away from
`s = 1`, has a simple pole at `s = 1` with residue `NumberField.dedekindZeta_residue K` in the
full punctured complex neighborhood `𝓝[≠] 1` (taking the canonical normal-form value `0` at `1`),
and has analytic order `r₁ + r₂ - 1 = NumberField.Units.rank K` at `s = 0` with leading
coefficient `-h R / w`. In particular, `s = 0` is a zero of `dedekindZetaC K` exactly when the unit
rank is positive, whereas in unit rank `0` (`ℚ` and imaginary quadratic fields)
`dedekindZetaC K 0 = -h R / w`.

## Main results

* `TauCeti.LFunctions.dedekindZetaData_continuedL`:
  `(dedekindZetaData K).continuedL = dedekindZetaC K`.
* `TauCeti.LFunctions.dedekindZetaC_eventuallyEq_mul_completedDedekindZeta`,
  `TauCeti.LFunctions.dedekindZetaC_eq_mul_completedDedekindZeta`,
  `TauCeti.LFunctions.completedDedekindZeta_eventuallyEq_mul_dedekindZetaC`: relation between
  `dedekindZetaC K` and `completedDedekindZeta K`.
* `TauCeti.LFunctions.dedekindZetaC_eq`: agreement with `NumberField.dedekindZeta K` on
  `Re s > 1`.
* `TauCeti.LFunctions.analyticAt_dedekindZetaC`,
  `TauCeti.LFunctions.analyticAt_dedekindZetaC_iff`: analyticity away from `s = 1`.
* `TauCeti.LFunctions.tendsto_sub_one_mul_dedekindZetaC`,
  `TauCeti.LFunctions.meromorphicOrderAt_dedekindZetaC_one`,
  `TauCeti.LFunctions.dedekindZetaC_one`: simple pole, canonical value `0`, and analytic class
  number formula at `s = 1` in `𝓝[≠] 1`.
* `TauCeti.LFunctions.meromorphicOrderAt_dedekindZetaC_zero`,
  `TauCeti.LFunctions.analyticOrderAt_dedekindZetaC_zero`,
  `TauCeti.LFunctions.tendsto_dedekindZetaC_div_pow_rank_zero`,
  `TauCeti.LFunctions.dedekindZetaC_zero_of_rank_eq_zero`,
  `TauCeti.LFunctions.dedekindZetaC_zero_of_rank_pos`: vanishing order `r₁ + r₂ - 1`, leading
  coefficient `-h R / w`, and value at `s = 0`.
* `TauCeti.LFunctions.dedekindZetaC_conj`: reflection symmetry
  `dedekindZetaC K (conj s) = conj (dedekindZetaC K s)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5, Corollary 5.10 and Corollary 5.11.
-/

public section

noncomputable section

open Complex ComplexConjugate Filter NumberField NumberField.InfinitePlace NumberField.Units Set
open scoped Topology

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K]

/-! ### Identification with `(dedekindZetaData K).continuedL` -/

variable (K) in
private theorem meromorphic_dedekindZetaData_completed :
    Meromorphic (dedekindZetaData K).completed := by
  rw [dedekindZetaData_completed]
  exact meromorphic_completedDedekindZeta K

variable (K) in
/-- Identifying the continued uncompleted function of `dedekindZetaData K` with
`dedekindZetaC K`. -/
@[simp]
theorem dedekindZetaData_continuedL : (dedekindZetaData K).continuedL = dedekindZetaC K := by
  have hnf : MeromorphicNFOn (dedekindZetaData K).completed univ := by
    rw [dedekindZetaData_completed]
    exact meromorphicNFOn_completedDedekindZeta K
  rw [(dedekindZetaData_hasDirichletAgreement K).continuedL_eq_meromorphicContinuation hnf,
    dedekindZetaC_def]
  congr 1
  funext s
  rw [funext (dedekindZetaData_coeff K), ← dedekindZeta_eq_LSeries_normCoeff_one K s]

private theorem uncompletedProduct_dedekindZetaData (s : ℂ) :
    (dedekindZetaData K).uncompletedProduct s =
      ((|discr K| : ℤ) : ℂ) ^ (-s / 2) *
        (Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K *
        completedDedekindZeta K s := by
  rw [AnalyticLFunctionData.uncompletedProduct_def, dedekindZetaData_conductor, PNat.mk_coe,
    ← Int.cast_natCast (R := ℂ), Int.natCast_natAbs, dedekindZetaData_completed,
    AnalyticLFunctionData.invGammaFactor_def, dedekindZetaData_gammaFactor, mul_inv, inv_pow,
    inv_pow]
  ring

variable (K) in
/-- At every `s : ℂ`, `dedekindZetaC K` has the same punctured germ as
`|d_K|^(-z/2) Γ_ℝ(z)⁻¹^r₁ Γ_ℂ(z)⁻¹^r₂ Λ_K(z)`. -/
theorem dedekindZetaC_eventuallyEq_mul_completedDedekindZeta (s : ℂ) :
    dedekindZetaC K =ᶠ[𝓝[≠] s] fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-z / 2) *
        (Gammaℝ z)⁻¹ ^ nrRealPlaces K * (Gammaℂ z)⁻¹ ^ nrComplexPlaces K *
        completedDedekindZeta K z := by
  rw [← dedekindZetaData_continuedL K]
  exact (AnalyticLFunctionData.continuedL_eventuallyEq
    (meromorphic_dedekindZetaData_completed K) s).trans
    (Eventually.of_forall uncompletedProduct_dedekindZetaData)

/-- Away from `0` (including at `s = 1`, where both sides take the canonical normal-form value
`0`), `dedekindZetaC K s` equals `|d_K|^(-s/2) Γ_ℝ(s)⁻¹^r₁ Γ_ℂ(s)⁻¹^r₂ Λ_K(s)`. -/
theorem dedekindZetaC_eq_mul_completedDedekindZeta {s : ℂ} (h0 : s ≠ 0) :
    dedekindZetaC K s =
      ((|discr K| : ℤ) : ℂ) ^ (-s / 2) *
        (Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K *
        completedDedekindZeta K s := by
  rw [← dedekindZetaData_continuedL K, ← uncompletedProduct_dedekindZetaData]
  by_cases h1 : s = 1
  · subst h1
    refine (dedekindZetaData_hasMeromorphicContinuation K).continuedL_eq_of_gammaFactor_ne_zero ?_
    simp [Gammaℝ_one, Gammaℂ_one, Real.pi_ne_zero]
  · refine AnalyticLFunctionData.continuedL_eq_uncompletedProduct_of_analyticAt
      (meromorphic_dedekindZetaData_completed K)
      (AnalyticLFunctionData.analyticAt_uncompletedProduct ?_)
    rw [dedekindZetaData_completed]
    exact analyticAt_completedDedekindZeta h0 h1

/-- On `Re s > 1`, the continued Dedekind zeta function agrees with Mathlib's Dirichlet series
`NumberField.dedekindZeta K`. -/
theorem dedekindZetaC_eq {s : ℂ} (hs : 1 < s.re) :
    dedekindZetaC K s = NumberField.dedekindZeta K s := by
  rw [← dedekindZetaData_continuedL K,
    (dedekindZetaData_hasDirichletAgreement K).continuedL_eq_LSeries
      (meromorphic_dedekindZetaData_completed K) hs,
    funext (dedekindZetaData_coeff K), ← dedekindZeta_eq_LSeries_normCoeff_one K s]

variable (K) in
/-- At every `s : ℂ`, `completedDedekindZeta K` has the same punctured germ as
`(|d_K|^(z/2) Γ_ℝ(z)^r₁ Γ_ℂ(z)^r₂) * dedekindZetaC K z`. -/
theorem completedDedekindZeta_eventuallyEq_mul_dedekindZetaC (s : ℂ) :
    completedDedekindZeta K =ᶠ[𝓝[≠] s] fun z : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (z / 2) *
        Gammaℝ z ^ nrRealPlaces K * Gammaℂ z ^ nrComplexPlaces K *
        dedekindZetaC K z := by
  simpa only [dedekindZetaData_completed, dedekindZetaData_conductor, PNat.mk_coe,
    ← Int.cast_natCast (R := ℂ), Int.natCast_natAbs, dedekindZetaData_gammaFactor,
    dedekindZetaData_continuedL, mul_assoc] using
    AnalyticLFunctionData.completed_eventuallyEq_mul_continuedL
      (meromorphic_dedekindZetaData_completed K) s

/-! ### Vanishing order and leading coefficient at `s = 0` -/

variable (K) in
/-- **Vanishing order of the Dedekind zeta function at `s = 0`**: `dedekindZetaC K` has meromorphic
order `r₁ + r₂ - 1 = NumberField.Units.rank K` at `s = 0`. -/
@[simp]
theorem meromorphicOrderAt_dedekindZetaC_zero :
    meromorphicOrderAt (dedekindZetaC K) 0 = (NumberField.Units.rank K : ℤ) := by
  classical
  rw [← dedekindZetaData_continuedL K,
    AnalyticLFunctionData.meromorphicOrderAt_continuedL
      (meromorphic_dedekindZetaData_completed K) 0,
    dedekindZetaData_completed, meromorphicOrderAt_completedDedekindZeta_zero,
    AnalyticLFunctionData.meromorphicOrderAt_gammaFactor_eq_neg_count]
  have hr : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    rw [← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  have hR : ((dedekindZetaData K).gammaR.countP fun μ ↦ ∃ n : ℕ, 0 + μ = -(2 * (n : ℂ))) =
      nrRealPlaces K := by
    rw [dedekindZetaData_gammaR, Multiset.countP_eq_card_filter, Multiset.filter_eq_self.mpr ?_,
      Multiset.card_replicate]
    intro μ hμ
    rw [Multiset.eq_of_mem_replicate hμ]
    exact ⟨0, by norm_num⟩
  have hC : ((dedekindZetaData K).gammaC.countP fun ν ↦ ∃ n : ℕ, 0 + ν = -(n : ℂ)) =
      nrComplexPlaces K := by
    rw [dedekindZetaData_gammaC, Multiset.countP_eq_card_filter, Multiset.filter_eq_self.mpr ?_,
      Multiset.card_replicate]
    intro ν hν
    rw [Multiset.eq_of_mem_replicate hν]
    exact ⟨0, by norm_num⟩
  rw [hR, hC, NumberField.Units.rank_eq_nrRealPlaces_add_nrComplexPlaces_sub_one]
  norm_cast
  omega

/-- **Holomorphy of the Dedekind zeta function away from `s = 1`**: `dedekindZetaC K` is analytic
at every `s ≠ 1`, including `s = 0` where the reciprocal archimedean factor
`|d_K|^(-s/2) Γ_ℝ(s)⁻¹^r₁ Γ_ℂ(s)⁻¹^r₂` vanishes to order `r₁ + r₂ ≥ 1`, cancelling the simple pole
of `Λ_K` in the meromorphic product. -/
@[fun_prop]
theorem analyticAt_dedekindZetaC {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ (dedekindZetaC K) s := by
  rw [← dedekindZetaData_continuedL K]
  rcases eq_or_ne s 0 with rfl | h0
  · rw [AnalyticLFunctionData.analyticAt_continuedL_iff, dedekindZetaData_continuedL,
      meromorphicOrderAt_dedekindZetaC_zero]
    exact WithTop.coe_nonneg.mpr (Int.natCast_nonneg _)
  · refine AnalyticLFunctionData.analyticAt_continuedL_of_analyticAt ?_
    rw [dedekindZetaData_completed]
    exact analyticAt_completedDedekindZeta h0 hs

variable (K) in
/-- At `s = 0`, `dedekindZetaC K` has analytic vanishing order equal to the Dirichlet unit rank
`NumberField.Units.rank K = r₁ + r₂ - 1`. -/
@[simp]
theorem analyticOrderAt_dedekindZetaC_zero :
    analyticOrderAt (dedekindZetaC K) 0 = NumberField.Units.rank K := by
  have h := (analyticAt_dedekindZetaC (K := K) zero_ne_one).meromorphicOrderAt_eq
  rw [meromorphicOrderAt_dedekindZetaC_zero K] at h
  cases hord : analyticOrderAt (dedekindZetaC K) 0 with
  | top =>
    rw [hord] at h
    simp at h
  | coe n =>
    rw [hord] at h
    exact_mod_cast (WithTop.coe_inj.mp h).symm

private theorem inv_two_pow_mul_completedDedekindZeta_residue
    (K : Type*) [Field K] [NumberField K] :
    (1 : ℂ) * (2 : ℂ)⁻¹ ^ nrRealPlaces K * (2 : ℂ)⁻¹ ^ nrComplexPlaces K *
        (-((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
          torsionOrder K : ℝ) : ℂ)) =
      -(((classNumber K : ℝ) * regulator K / torsionOrder K : ℝ) : ℂ) := by
  have h2 : (2 : ℂ)⁻¹ ^ nrRealPlaces K * (2 : ℂ)⁻¹ ^ nrComplexPlaces K *
      (2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K) = 1 := by
    rw [← pow_add, ← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  push_cast
  calc
    1 * (2 : ℂ)⁻¹ ^ nrRealPlaces K * (2 : ℂ)⁻¹ ^ nrComplexPlaces K *
        -(2 ^ (nrRealPlaces K + nrComplexPlaces K) * (regulator K : ℂ) * (classNumber K : ℂ) /
          (torsionOrder K : ℂ))
      = -(((2 : ℂ)⁻¹ ^ nrRealPlaces K * (2 : ℂ)⁻¹ ^ nrComplexPlaces K *
          (2 : ℂ) ^ (nrRealPlaces K + nrComplexPlaces K)) *
          ((classNumber K : ℂ) * (regulator K : ℂ) / (torsionOrder K : ℂ))) := by ring
    _ = -((classNumber K : ℂ) * (regulator K : ℂ) / (torsionOrder K : ℂ)) := by
      rw [h2, one_mul]

private theorem uncompletedProduct_div_pow_rank_eq (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : s ≠ 0) :
    ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * (s * Gammaℝ s)⁻¹ ^ nrRealPlaces K *
        (s * Gammaℂ s)⁻¹ ^ nrComplexPlaces K * (s * completedDedekindZeta K s) =
      (dedekindZetaData K).uncompletedProduct s / s ^ NumberField.Units.rank K := by
  have hr : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    rw [← InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    exact Fintype.card_pos
  have hspow : s ^ NumberField.Units.rank K * s = s ^ (nrRealPlaces K + nrComplexPlaces K) := by
    rw [NumberField.Units.rank_eq_nrRealPlaces_add_nrComplexPlaces_sub_one, ← pow_succ,
      Nat.sub_add_cancel hr]
  rw [uncompletedProduct_dedekindZetaData, div_eq_mul_inv]
  simp only [mul_inv, mul_pow]
  calc
    ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * (s⁻¹ ^ nrRealPlaces K * (Gammaℝ s)⁻¹ ^ nrRealPlaces K) *
        (s⁻¹ ^ nrComplexPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K) *
        (s * completedDedekindZeta K s)
      = ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * (Gammaℝ s)⁻¹ ^ nrRealPlaces K *
          (Gammaℂ s)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K s *
          ((s ^ (nrRealPlaces K + nrComplexPlaces K))⁻¹ * s) := by
            rw [pow_add, mul_inv, inv_pow, inv_pow]
            ring
    _ = ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * (Gammaℝ s)⁻¹ ^ nrRealPlaces K *
          (Gammaℂ s)⁻¹ ^ nrComplexPlaces K * completedDedekindZeta K s *
          (s ^ NumberField.Units.rank K)⁻¹ := by
            rw [← hspow, mul_inv]
            congr 1
            rw [mul_assoc, inv_mul_cancel₀ hs, mul_one]

variable (K) in
/-- **Leading coefficient of the Dedekind zeta function at `s = 0`**, Neukirch VII Corollary 5.11:
`dedekindZetaC K s / s ^ rank K → -h R / w` as `s → 0`. -/
theorem tendsto_dedekindZetaC_div_pow_rank_zero :
    Tendsto (fun s : ℂ ↦ dedekindZetaC K s / s ^ NumberField.Units.rank K) (𝓝[≠] 0)
      (𝓝 (-(((classNumber K : ℝ) * regulator K / torsionOrder K : ℝ) : ℂ))) := by
  have hdiscr : Tendsto (fun s : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-s / 2)) (𝓝[≠] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun s : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-s / 2)) 0 :=
      (((differentiable_neg.div_const (2 : ℂ)).const_cpow
        (Or.inl (NumberField.cast_abs_discr_ne_zero K))).continuous).continuousAt
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hΓℝ : Tendsto (fun s : ℂ ↦ (s * Gammaℝ s)⁻¹ ^ nrRealPlaces K) (𝓝[≠] 0)
      (𝓝 ((2 : ℂ)⁻¹ ^ nrRealPlaces K)) :=
    (Gammaℝ_residue_zero.inv₀ two_ne_zero).pow _
  have hΓℂ : Tendsto (fun s : ℂ ↦ (s * Gammaℂ s)⁻¹ ^ nrComplexPlaces K) (𝓝[≠] 0)
      (𝓝 ((2 : ℂ)⁻¹ ^ nrComplexPlaces K)) :=
    (Gammaℂ_residue_zero.inv₀ two_ne_zero).pow _
  have hprod := ((hdiscr.mul hΓℝ).mul hΓℂ).mul (tendsto_mul_completedDedekindZeta_zero K)
  rw [inv_two_pow_mul_completedDedekindZeta_residue] at hprod
  refine hprod.congr' ?_
  have hev : dedekindZetaC K =ᶠ[𝓝[≠] 0] (dedekindZetaData K).uncompletedProduct := by
    rw [← dedekindZetaData_continuedL K]
    exact AnalyticLFunctionData.continuedL_eventuallyEq (meromorphic_dedekindZetaData_completed K) 0
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hne
  rw [hs, uncompletedProduct_div_pow_rank_eq K hne]

/-- When `K` has unit rank `0` (`ℚ` or an imaginary quadratic field),
`dedekindZetaC K 0 = -h R / w`. -/
theorem dedekindZetaC_zero_of_rank_eq_zero (hr : NumberField.Units.rank K = 0) :
    dedekindZetaC K 0 = -(((classNumber K : ℝ) * regulator K / torsionOrder K : ℝ) : ℂ) := by
  have hcont : Tendsto (dedekindZetaC K) (𝓝[≠] 0) (𝓝 (dedekindZetaC K 0)) :=
    (analyticAt_dedekindZetaC (K := K) zero_ne_one).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hlim := tendsto_dedekindZetaC_div_pow_rank_zero K
  simp only [hr, pow_zero, div_one] at hlim
  exact tendsto_nhds_unique hcont hlim

/-- When `K` has positive unit rank, `dedekindZetaC K 0 = 0`. -/
theorem dedekindZetaC_zero_of_rank_pos (hr : 0 < NumberField.Units.rank K) :
    dedekindZetaC K 0 = 0 := by
  by_contra hne
  have hord := (analyticAt_dedekindZetaC (K := K) zero_ne_one).analyticOrderAt_eq_zero.mpr hne
  rw [analyticOrderAt_dedekindZetaC_zero K] at hord
  exact hr.ne' (by exact_mod_cast hord)

/-! ### Simple pole and complex class number formula at `s = 1` -/

private theorem archInvFactor_mul_archFactor (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 0 < s.re) :
    (((|discr K| : ℤ) : ℂ) ^ (-s / 2) *
        (Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K) *
      (((|discr K| : ℤ) : ℂ) ^ (s / 2) *
        Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K) = 1 := by
  have hd : ((|discr K| : ℤ) : ℂ) ^ (-s / 2) * ((|discr K| : ℤ) : ℂ) ^ (s / 2) = 1 := by
    rw [neg_div, Complex.cpow_neg, inv_mul_cancel₀
      (cpow_ne_zero_iff.mpr (Or.inl (NumberField.cast_abs_discr_ne_zero K)))]
  have hΓℝ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hΓℂ : Gammaℂ s ≠ 0 := Gammaℂ_ne_zero_of_re_pos hs
  calc
    (((|discr K| : ℤ) : ℂ) ^ (-s / 2) * (Gammaℝ s)⁻¹ ^ nrRealPlaces K *
        (Gammaℂ s)⁻¹ ^ nrComplexPlaces K) *
        (((|discr K| : ℤ) : ℂ) ^ (s / 2) * Gammaℝ s ^ nrRealPlaces K *
          Gammaℂ s ^ nrComplexPlaces K)
      = (((|discr K| : ℤ) : ℂ) ^ (-s / 2) * ((|discr K| : ℤ) : ℂ) ^ (s / 2)) *
          ((Gammaℝ s)⁻¹ * Gammaℝ s) ^ nrRealPlaces K *
          ((Gammaℂ s)⁻¹ * Gammaℂ s) ^ nrComplexPlaces K := by
            simp only [mul_pow]
            ring
    _ = 1 := by
      rw [hd, inv_mul_cancel₀ hΓℝ, inv_mul_cancel₀ hΓℂ, one_pow, one_pow, one_mul, one_mul]

variable (K) in
/-- **Analytic class number formula in the complex plane**:
`(s - 1) * dedekindZetaC K s → NumberField.dedekindZeta_residue K` as `s → 1` in `𝓝[≠] 1`. -/
theorem tendsto_sub_one_mul_dedekindZetaC :
    Tendsto (fun s : ℂ ↦ (s - 1) * dedekindZetaC K s) (𝓝[≠] 1)
      (𝓝 (NumberField.dedekindZeta_residue K : ℂ)) := by
  have hdiscr : ContinuousAt (fun s : ℂ ↦ ((|discr K| : ℤ) : ℂ) ^ (-s / 2)) 1 :=
    (((differentiable_neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (NumberField.cast_abs_discr_ne_zero K))).continuous).continuousAt
  have harch : Tendsto (fun s : ℂ ↦
      ((|discr K| : ℤ) : ℂ) ^ (-s / 2) *
        (Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K) (𝓝[≠] 1)
      (𝓝 (((|discr K| : ℤ) : ℂ) ^ (-(1 : ℂ) / 2) *
        (Gammaℝ 1)⁻¹ ^ nrRealPlaces K * (Gammaℂ 1)⁻¹ ^ nrComplexPlaces K)) :=
    ((hdiscr.mul (differentiable_Gammaℝ_inv.continuous.continuousAt.pow _)).mul
      (differentiable_Gammaℂ_inv.continuous.continuousAt.pow _)).tendsto.mono_left
      nhdsWithin_le_nhds
  have hprod := harch.mul (tendsto_sub_one_mul_completedDedekindZeta K)
  have hlim :
      (((|discr K| : ℤ) : ℂ) ^ (-(1 : ℂ) / 2) *
          (Gammaℝ 1)⁻¹ ^ nrRealPlaces K * (Gammaℂ 1)⁻¹ ^ nrComplexPlaces K) *
          ((2 ^ (nrRealPlaces K + nrComplexPlaces K) * regulator K * classNumber K /
            torsionOrder K : ℝ) : ℂ) =
        (NumberField.dedekindZeta_residue K : ℂ) := by
    rw [two_pow_mul_regulator_mul_classNumber_div_torsionOrder_eq K]
    calc
      (((|discr K| : ℤ) : ℂ) ^ (-(1 : ℂ) / 2) *
          (Gammaℝ 1)⁻¹ ^ nrRealPlaces K * (Gammaℂ 1)⁻¹ ^ nrComplexPlaces K) *
          (((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) *
            Gammaℝ 1 ^ nrRealPlaces K * Gammaℂ 1 ^ nrComplexPlaces K *
            (NumberField.dedekindZeta_residue K : ℂ))
        = ((((|discr K| : ℤ) : ℂ) ^ (-(1 : ℂ) / 2) *
            (Gammaℝ 1)⁻¹ ^ nrRealPlaces K * (Gammaℂ 1)⁻¹ ^ nrComplexPlaces K) *
            (((|discr K| : ℤ) : ℂ) ^ ((1 : ℂ) / 2) *
              Gammaℝ 1 ^ nrRealPlaces K * Gammaℂ 1 ^ nrComplexPlaces K)) *
            (NumberField.dedekindZeta_residue K : ℂ) := by ring
      _ = (NumberField.dedekindZeta_residue K : ℂ) := by
        rw [archInvFactor_mul_archFactor K (by norm_num : (0 : ℝ) < (1 : ℂ).re), one_mul]
  rw [hlim] at hprod
  refine hprod.congr' ?_
  filter_upwards [dedekindZetaC_eventuallyEq_mul_completedDedekindZeta K 1] with s hs
  rw [hs]
  ring

variable (K) in
/-- The continued Dedekind zeta function has a simple pole at `s = 1`. -/
@[simp]
theorem meromorphicOrderAt_dedekindZetaC_one :
    meromorphicOrderAt (dedekindZetaC K) 1 = (-1 : ℤ) := by
  have hne : (NumberField.dedekindZeta_residue K : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (NumberField.dedekindZeta_residue_pos K).ne'
  refine (meromorphic_dedekindZetaC K 1).meromorphicOrderAt_eq_neg_one_of_tendsto_sub_smul hne ?_
  simpa only [smul_eq_mul] using tendsto_sub_one_mul_dedekindZetaC K

/-- `dedekindZetaC K` is analytic at `s` if and only if `s ≠ 1`. -/
@[simp]
theorem analyticAt_dedekindZetaC_iff {s : ℂ} :
    AnalyticAt ℂ (dedekindZetaC K) s ↔ s ≠ 1 := by
  refine ⟨fun han ↦ ?_, analyticAt_dedekindZetaC⟩
  rintro rfl
  have hnonneg := han.meromorphicOrderAt_nonneg
  simp only [meromorphicOrderAt_dedekindZetaC_one, WithTop.coe_nonneg] at hnonneg
  omega

variable (K) in
/-- As a meromorphic normal form, `dedekindZetaC K` takes the canonical value `0` at its pole
`s = 1`. -/
@[simp]
theorem dedekindZetaC_one : dedekindZetaC K 1 = 0 :=
  not_not.mp <| (meromorphicNFOn_dedekindZetaC K (mem_univ 1))
    |>.meromorphicOrderAt_eq_zero_iff.not.mp (by simp)

/-! ### Reflection symmetry -/

variable (K) in
/-- **Reflection symmetry of the continued Dedekind zeta function**:
`dedekindZetaC K (conj s) = conj (dedekindZetaC K s)` for every `s : ℂ`. -/
theorem dedekindZetaC_conj (s : ℂ) :
    dedekindZetaC K (conj s) = conj (dedekindZetaC K s) := by
  have h := (dedekindZetaData K).continuedL_dual_apply (conj s)
  rw [dedekindZetaData_dual, dedekindZetaData_continuedL, Complex.conj_conj] at h
  exact h

end TauCeti.LFunctions

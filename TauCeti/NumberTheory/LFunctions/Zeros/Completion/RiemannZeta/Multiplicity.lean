/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.CriticalLine

import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Growth
import TauCeti.NumberTheory.LFunctions.Zeros.Divisor

/-!
# The zero multiset of the completed Riemann zeta function

`TauCeti.LFunctions.zetaZeroMult ρ` is the multiplicity of `ρ` as a zero of Mathlib's completed
Riemann zeta function `Λ(s) = π^(-s/2) Γ(s/2) ζ(s)`: the positive part of the divisor of `Λ` on
`ℂ`. It is the weight with which a nontrivial zero of `ζ` enters a sum over the zeros.

Taking the positive part discards the two poles of `Λ` at `0` and `1`, where the divisor is `-1`.
At the trivial zeros `-2(n + 1)` of `riemannZeta` the function `Λ` is regular and nonzero, so
they carry multiplicity `0` as well. Thus `zetaZeroMult ρ ≠ 0` exactly at the zeros of `ζ` that
`RiemannHypothesis` constrains, and every such `ρ` lies in the open critical strip.

The multiplicity is also the order of vanishing of the entire function `zetaEntireCompletion`
(twice Riemann's ξ-function), which is how its symmetries and the summability of the zeros are
read off: the zero multiset is invariant under `ρ ↦ 1 - ρ` (the functional equation) and under
`ρ ↦ conj ρ` (`Λ` is real on the real axis), hence under the reflection `ρ ↦ 1 - conj ρ` in the
critical line; it is finite on bounded sets; and since `zetaEntireCompletion` has order at most
`1`, the families `zetaZeroMult ρ / (1 + ‖ρ‖)²` and `zetaZeroMult ρ (1 + |Re ρ|) / (1 + ‖ρ‖)²`
are summable over `ℂ`.

## Main definitions

* `TauCeti.LFunctions.zetaZeroMult`: the zero multiplicity of `completedRiemannZeta`.

## Main results

* `TauCeti.LFunctions.zetaZeroMult_eq_analyticOrderNatAt`: it is the order of vanishing of
  `zetaEntireCompletion`.
* `TauCeti.LFunctions.zetaZeroMult_ne_zero_iff_riemannZeta_eq_zero`: the points of positive
  multiplicity are the zeros of `riemannZeta` other than the trivial zeros and the pole `1`.
* `TauCeti.LFunctions.zetaZeroMult_one_sub`, `TauCeti.LFunctions.zetaZeroMult_conj`,
  `TauCeti.LFunctions.zetaZeroMult_one_sub_conj`: the symmetries of the zero multiset.
* `TauCeti.LFunctions.re_mem_Ioo_of_zetaZeroMult_ne_zero`: the zeros lie in `0 < Re ρ < 1`.
* `Bornology.IsBounded.finite_inter_support_zetaZeroMult`: finitely many zeros in a bounded set.
* `TauCeti.LFunctions.summable_zetaZeroMult_div_one_add_norm_sq`,
  `TauCeti.LFunctions.summable_zetaZeroMult_mul_one_add_abs_re_div_one_add_norm_sq`: summability
  of the zeros.
* `TauCeti.LFunctions.riemannHypothesis_iff_forall_re_eq_of_zetaZeroMult_ne_zero`: the Riemann
  hypothesis in terms of the zero multiset.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §11 and §12.
* E. Bombieri and J. C. Lagarias, *Complements to Li's criterion for the Riemann hypothesis*,
  J. Number Theory 77 (1999), for sums over the zeros weighted by these multiplicities.
-/

public section

open Complex ComplexConjugate Set

namespace TauCeti.LFunctions

/-- The multiplicity of `ρ` as a zero of the completed Riemann zeta function: the positive part of
the divisor of `completedRiemannZeta` on `ℂ`. It vanishes at the poles `0` and `1` and at the
trivial zeros of `riemannZeta`. -/
noncomputable def zetaZeroMult (ρ : ℂ) : ℕ :=
  (MeromorphicOn.divisor completedRiemannZeta univ ρ).toNat

theorem zetaZeroMult_def (ρ : ℂ) :
    zetaZeroMult ρ = (MeromorphicOn.divisor completedRiemannZeta univ ρ).toNat := (rfl)

/-- Clearing the poles of `completedRiemannZeta` does not change any zero multiplicity: the zero
multiplicity is read equally from the divisor of `zetaEntireCompletion`. -/
theorem zetaZeroMult_eq_toNat_divisor_zetaEntireCompletion (ρ : ℂ) :
    zetaZeroMult ρ = (MeromorphicOn.divisor zetaEntireCompletion univ ρ).toNat := by
  rw [zetaZeroMult_def]
  simpa only [riemannZetaData_entireCompletion, riemannZetaData_completed] using
    (riemannZetaData_hasMeromorphicContinuation.toNat_divisor_entireCompletion ρ).symm

/-- The zero multiplicity is the order of vanishing of the entire function
`zetaEntireCompletion`. -/
theorem zetaZeroMult_eq_analyticOrderNatAt (ρ : ℂ) :
    zetaZeroMult ρ = analyticOrderNatAt zetaEntireCompletion ρ := by
  rw [zetaZeroMult_def]
  simpa only [riemannZetaData_entireCompletion, riemannZetaData_completed] using
    (riemannZetaData_hasMeromorphicContinuation
      |>.analyticOrderNatAt_entireCompletion_eq_toNat_divisor_completed ρ).symm

/-- A point has positive zero multiplicity exactly where the divisor of `completedRiemannZeta` is
positive. -/
theorem zetaZeroMult_ne_zero_iff {ρ : ℂ} :
    zetaZeroMult ρ ≠ 0 ↔ 0 < MeromorphicOn.divisor completedRiemannZeta univ ρ := by
  rw [zetaZeroMult_def, ne_eq, Int.toNat_eq_zero, not_le]

/-- A point has positive zero multiplicity exactly where `zetaEntireCompletion` vanishes. -/
theorem zetaZeroMult_ne_zero_iff_zetaEntireCompletion_eq_zero {ρ : ℂ} :
    zetaZeroMult ρ ≠ 0 ↔ zetaEntireCompletion ρ = 0 := by
  have hf : AnalyticOnNhd ℂ zetaEntireCompletion univ :=
    fun z _ ↦ differentiable_zetaEntireCompletion.analyticAt z
  have hnn : 0 ≤ MeromorphicOn.divisor zetaEntireCompletion univ ρ :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf ρ
  have h0 := hf.divisor_apply_eq_zero_iff isPreconnected_univ (mem_univ 0) (by simp) (mem_univ ρ)
  rw [zetaZeroMult_eq_toNat_divisor_zetaEntireCompletion, ne_eq, Int.toNat_eq_zero, not_le]
  refine ⟨fun hpos ↦ ?_, fun hz ↦ ?_⟩
  · by_contra hne
    have := h0.2 hne
    omega
  · by_contra hle
    exact h0.1 (by omega) hz

/-- A point has positive zero multiplicity exactly at the zeros of `riemannZeta` that are neither
trivial zeros `-2(n + 1)` nor the pole `1`, the zeros constrained by `RiemannHypothesis`. -/
theorem zetaZeroMult_ne_zero_iff_riemannZeta_eq_zero {ρ : ℂ} :
    zetaZeroMult ρ ≠ 0 ↔ riemannZeta ρ = 0 ∧ (¬∃ n : ℕ, ρ = -2 * (n + 1)) ∧ ρ ≠ 1 := by
  rw [zetaZeroMult_ne_zero_iff, zero_lt_divisor_completedRiemannZeta_iff]

/-- The pole of `completedRiemannZeta` at `0` carries zero multiplicity `0`. -/
@[simp]
theorem zetaZeroMult_zero : zetaZeroMult 0 = 0 := by
  simp [zetaZeroMult_def, divisor_completedRiemannZeta_zero]

/-- The pole of `completedRiemannZeta` at `1` carries zero multiplicity `0`, although the divisor
there is `-1`. -/
@[simp]
theorem zetaZeroMult_one : zetaZeroMult 1 = 0 := by
  simp [zetaZeroMult_def, divisor_completedRiemannZeta_one]

/-- The trivial zeros `-2(n + 1)` of `riemannZeta` carry zero multiplicity `0`. -/
theorem zetaZeroMult_neg_two_mul_nat_add_one (n : ℕ) : zetaZeroMult (-2 * (n + 1)) = 0 := by
  by_contra h
  exact (zetaZeroMult_ne_zero_iff_riemannZeta_eq_zero.1 h).2.1 ⟨n, rfl⟩

/-- Every point of positive zero multiplicity lies in the open critical strip `0 < Re ρ < 1`. -/
theorem re_mem_Ioo_of_zetaZeroMult_ne_zero {ρ : ℂ} (hρ : zetaZeroMult ρ ≠ 0) :
    ρ.re ∈ Ioo 0 1 :=
  re_mem_Ioo_of_zetaEntireCompletion_eq_zero
    (zetaZeroMult_ne_zero_iff_zetaEntireCompletion_eq_zero.1 hρ)

/-- **The Riemann hypothesis** says exactly that every point of positive zero multiplicity of the
completed Riemann zeta function lies on the critical line. -/
theorem riemannHypothesis_iff_forall_re_eq_of_zetaZeroMult_ne_zero :
    RiemannHypothesis ↔ ∀ ρ, zetaZeroMult ρ ≠ 0 → ρ.re = 1 / 2 := by
  simp only [← allOnCriticalLine_completedRiemannZeta_iff, allOnCriticalLine_iff, mem_univ,
    true_imp_iff, zetaZeroMult_ne_zero_iff]

/-! ### Symmetries -/

/-- The functional equation `Λ(1 - s) = Λ(s)` makes the zero multiset invariant under
`ρ ↦ 1 - ρ`. -/
theorem zetaZeroMult_one_sub (ρ : ℂ) : zetaZeroMult (1 - ρ) = zetaZeroMult ρ := by
  have h := riemannZetaData_hasFunctionalEquation.divisor_entireCompletion_one_sub
    riemannZetaData_hasMeromorphicContinuation ρ
  simp only [riemannZetaData_dual, riemannZetaData_entireCompletion] at h
  rw [zetaZeroMult_eq_toNat_divisor_zetaEntireCompletion,
    zetaZeroMult_eq_toNat_divisor_zetaEntireCompletion, h]

/-- The conjugation symmetry `Λ(conj s) = conj Λ(s)` makes the zero multiset invariant under
`ρ ↦ conj ρ`. -/
theorem zetaZeroMult_conj (ρ : ℂ) : zetaZeroMult (conj ρ) = zetaZeroMult ρ := by
  have h := riemannZetaData_hasMeromorphicContinuation.divisor_dual_entireCompletion_conj ρ
  simp only [riemannZetaData_dual, riemannZetaData_entireCompletion] at h
  rw [zetaZeroMult_eq_toNat_divisor_zetaEntireCompletion,
    zetaZeroMult_eq_toNat_divisor_zetaEntireCompletion, h]

/-- The zero multiset is invariant under the reflection `ρ ↦ 1 - conj ρ` in the critical line. -/
theorem zetaZeroMult_one_sub_conj (ρ : ℂ) : zetaZeroMult (1 - conj ρ) = zetaZeroMult ρ := by
  rw [zetaZeroMult_one_sub, zetaZeroMult_conj]

/-! ### Summability -/

/-- The zeros of the completed Riemann zeta function, counted with multiplicity, satisfy
`∑ zetaZeroMult ρ / (1 + ‖ρ‖)² < ∞`. -/
theorem summable_zetaZeroMult_div_one_add_norm_sq :
    Summable fun ρ : ℂ ↦ (zetaZeroMult ρ : ℝ) / (1 + ‖ρ‖) ^ 2 := by
  -- The order-one bound gives `∑ m_ρ ‖ρ⁻¹‖² < ∞` over the divisor support of the entire
  -- completion; extend it by zero to `ℂ` and compare termwise.
  have hsub := orderLE_zetaEntireCompletion.summable_divisor_toNat_mul_norm_inv_sq
    differentiable_zetaEntireCompletion one_lt_two
  have hall : Summable fun ρ : ℂ ↦ (zetaZeroMult ρ : ℝ) * ‖ρ⁻¹‖ ^ 2 := by
    refine (Function.Injective.summable_iff
      (g := fun ρ : (MeromorphicOn.divisor zetaEntireCompletion univ).support ↦ (ρ : ℂ))
      Subtype.val_injective fun ρ hρ ↦ ?_).1 ?_
    · have : MeromorphicOn.divisor zetaEntireCompletion univ ρ = 0 := by
        simpa using fun h ↦ hρ ⟨⟨ρ, h⟩, rfl⟩
      simp [zetaZeroMult_eq_toNat_divisor_zetaEntireCompletion, this]
    · simpa only [Function.comp_def, zetaZeroMult_eq_toNat_divisor_zetaEntireCompletion] using hsub
  refine hall.of_nonneg_of_le (fun ρ ↦ by positivity) fun ρ ↦ ?_
  rcases eq_or_ne ρ 0 with rfl | hρ
  · simp
  rw [norm_inv, inv_pow, ← div_eq_mul_inv]
  have : 0 < ‖ρ‖ := norm_pos_iff.2 hρ
  gcongr
  linarith

/-- The zeros of the completed Riemann zeta function, counted with multiplicity, satisfy
`∑ zetaZeroMult ρ (1 + |Re ρ|) / (1 + ‖ρ‖)² < ∞`. -/
theorem summable_zetaZeroMult_mul_one_add_abs_re_div_one_add_norm_sq :
    Summable fun ρ : ℂ ↦ (zetaZeroMult ρ : ℝ) * (1 + |ρ.re|) / (1 + ‖ρ‖) ^ 2 := by
  -- On the support `|Re ρ| < 1`, so each term is at most twice the term of
  -- `summable_zetaZeroMult_div_one_add_norm_sq`.
  refine (summable_zetaZeroMult_div_one_add_norm_sq.mul_left 2).of_nonneg_of_le
    (fun ρ ↦ by positivity) fun ρ ↦ ?_
  rcases eq_or_ne (zetaZeroMult ρ) 0 with h | h
  · simp [h]
  obtain ⟨h0, h1⟩ := re_mem_Ioo_of_zetaZeroMult_ne_zero h
  rw [mul_div_assoc', mul_comm (2 : ℝ)]
  gcongr
  rw [abs_of_pos h0]
  linarith

end TauCeti.LFunctions

open TauCeti.LFunctions in
/-- A bounded set contains only finitely many points of positive zero multiplicity. -/
theorem Bornology.IsBounded.finite_inter_support_zetaZeroMult {S : Set ℂ}
    (hS : Bornology.IsBounded S) : (S ∩ Function.support zetaZeroMult).Finite := by
  refine (MeromorphicOn.divisor_finite_inter_support (f := completedRiemannZeta) hS
    (subset_univ _)).subset ?_
  rintro ρ ⟨hρS, hρ⟩
  exact ⟨hρS, (zetaZeroMult_ne_zero_iff.1 hρ).ne'⟩


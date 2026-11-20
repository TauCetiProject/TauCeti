/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.OrderOne
public import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv.Bound
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic

import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Growth
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.LogDeriv
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Hadamard
public import TauCeti.Analysis.Complex.Hadamard.RealPart
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Growth
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.LogDeriv
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros

/-!
# Hadamard factorization and retained-zero inequalities for Dirichlet L-functions

Let `χ` be a primitive Dirichlet character modulo `N`, and write
`Λ₀ = (dirichletData χ hχ).entireCompletion`. For `χ ≠ 1`, `Λ₀` has no poles to clear, while at
conductor `N = 1` it recovers `zetaEntireCompletion`. In all cases `Λ₀` satisfies `Λ₀ 0 ≠ 0`, has
growth order at most `1`, has all its zeros inside the open critical strip `0 < Re ρ < 1`, and
obeys the combined functional and conjugation identity `Λ₀ (1 - z) = ε(χ) * conj (Λ₀ (conj z))`.
Specializing `TauCeti.hadamard_of_orderLE_one` and the record-level real-part cancellation theorems
of `TauCeti.NumberTheory.LFunctions.Zeros.Completion.Hadamard` gives:

* **Hadamard factorization** (`dirichletData_entireCompletion_hadamard`): for every primitive `χ`,
  `Λ₀` factors globally as `exp (a + b * s)` times the multipliable genus-one canonical product over
  its zeros.
* **Real-part cancellation** (`re_logDeriv_dirichletData_entireCompletion_zero` and
  `re_logDeriv_dirichletData_entireCompletion_eq_tsum`): for every primitive `χ` (real or complex),
  `(logDeriv Λ₀ 0).re = -∑' ρ, m_ρ * (1 / ρ).re`, so off the zeros one has
  `(logDeriv Λ₀ s).re = ∑' ρ, m_ρ * (1 / (s - ρ)).re` with no additive constant.
* **Retained-zero inequalities** (in `namespace DirichletCharacter`,
  `sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_re_logDeriv_LFunction_add` and
  `one_div_sub_le_re_logDeriv_LFunction_add`): for nonprincipal primitive `χ ≠ 1` and `σ ∈ [1, 2]`,
  every zero summand `m_ρ * Re (1 / (σ - ρ))` is nonnegative and the archimedean logarithmic
  derivative is bounded in norm by `TauCeti.gammaLogDerivBound` (`C_Γ`), so discarding all zeros
  outside a chosen finite set `S` (or keeping a single real zero `0 < β`) yields
  `∑ ρ ∈ S, analyticOrderNatAt χ.LFunction ρ * Re (1 / (σ - ρ)) ≤ Re (L'/L)(σ, χ) + ½ log N + C_Γ`
  and `1 / (σ - β) ≤ Re (L'/L)(σ, χ) + ½ log N + C_Γ`.

Dropping outside nonnegative zero terms on `σ ∈ [1, 2]` turns lower bounds on `-Re (L'/L)(σ, χ)`
(equivalently upper bounds on `Re (L'/L)(σ, χ)`) into quantitative bounds on zeros near `Re s = 1`
(for zero-free regions and real-zero exclusion), and conversely yields upper bounds on
`-Re (L'/L)(σ, χ)` from retained zeros.
In `sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_re_logDeriv_LFunction_add`, the
hypothesis `0 < ρ.re` on `S` restricts to the right half-plane where `Λ₀` and `χ.LFunction` share
the same zero multiplicities, excluding the trivial Gamma-cancelled zero `L(0, χ) = 0` of even
characters while allowing non-zeros in `S` since they contribute
`analyticOrderNatAt χ.LFunction ρ = 0`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §§10.2 and
  11.1–11.2, Theorem 10.16 and Corollary 10.18.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
-/

public section

open Complex
open scoped BigOperators

namespace TauCeti.LFunctions

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

/-! ### Hadamard factorization and real-part cancellation -/

/-- **Hadamard product for primitive Dirichlet completions.** For every primitive Dirichlet
character `χ`, `(dirichletData χ hχ).entireCompletion` factors globally as `exp (a + b * s)` times
the multipliable genus-one canonical product over its zeros, with
`exp a = (dirichletData χ hχ).entireCompletion 0` and
`b = logDeriv (dirichletData χ hχ).entireCompletion 0`. -/
theorem dirichletData_entireCompletion_hadamard :
    ∃ a b : ℂ, exp a = (dirichletData χ hχ).entireCompletion 0 ∧
      b = logDeriv (dirichletData χ hχ).entireCompletion 0 ∧ ∀ s : ℂ,
      Multipliable (fun ρ : ℂ ↦
        weierstrassFactor 1 (ρ⁻¹ * s) ^
          (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat) ∧
      (dirichletData χ hχ).entireCompletion s = exp (a + b * s) * ∏' ρ : ℂ,
        weierstrassFactor 1 (ρ⁻¹ * s) ^
          (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat :=
  hadamard_of_orderLE_one
    (dirichletData_entireCompletion_orderLE_one χ hχ)
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ)

/-- **Real-part formula for the Hadamard linear constant.** For every primitive Dirichlet character
`χ` (real or complex), the real part of `logDeriv (dirichletData χ hχ).entireCompletion 0` equals
`-∑' ρ, m_ρ * Re (1 / ρ)`. -/
theorem re_logDeriv_dirichletData_entireCompletion_zero :
    (logDeriv (dirichletData χ hχ).entireCompletion 0).re =
      -∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (ρ : ℂ)).re :=
  (dirichletData_hasFunctionalEquation χ hχ).re_logDeriv_entireCompletion_zero
    (dirichletData_hasMeromorphicContinuation χ hχ)
    (dirichletData_entireCompletion_orderLE_one χ hχ)
    (fun _ ↦ dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ)

/-- **Cancelled real-part partial-fraction expansion.** Off the zeros of
`(dirichletData χ hχ).entireCompletion`, its logarithmic derivative has real part
`∑' ρ, m_ρ * Re (1 / (s - ρ))`, with no additive constant. -/
theorem re_logDeriv_dirichletData_entireCompletion_eq_tsum {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    (logDeriv (dirichletData χ hχ).entireCompletion s).re =
      ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (s - ρ)).re :=
  (dirichletData_hasFunctionalEquation χ hχ).re_logDeriv_entireCompletion_eq_tsum
    (dirichletData_hasMeromorphicContinuation χ hχ)
    (dirichletData_entireCompletion_orderLE_one χ hχ)
    (fun _ ↦ dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ) hs

/-! ### Partial fractions and positivity -/

/-- **Partial fractions.** Off its zeros, the logarithmic derivative of a primitive
Dirichlet entire completion is `B(χ) + ∑_ρ m_ρ (1 / (s - ρ) + 1 / ρ)` with `B(χ) = Λ₀'/Λ₀ (0)`. -/
theorem logDeriv_dirichletData_entireCompletion_eq_add_tsum {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    logDeriv (dirichletData χ hχ).entireCompletion s =
      logDeriv (dirichletData χ hχ).entireCompletion 0 +
        ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
          ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℂ) *
            (1 / (s - ρ) + 1 / ρ) :=
  (dirichletData_entireCompletion_orderLE_one χ hχ).logDeriv_eq_add_tsum
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ) hs

/-- The partial-fraction series of a primitive Dirichlet entire completion converges
absolutely. -/
theorem summable_norm_divisor_dirichletData_entireCompletion_mul_one_div_sub_add_one_div
    (s : ℂ) :
    Summable (fun ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion
        Set.univ).support ↦
      ‖((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℂ) *
        (1 / (s - ρ) + 1 / ρ)‖) :=
  OrderLE.summable_norm_divisor_mul_one_div_sub_add_one_div
    (dirichletData_entireCompletion_orderLE_one χ hχ)
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion (by norm_num) s

/-- The partial-fraction series of a primitive Dirichlet entire completion converges
locally uniformly off its zeros to `Λ₀'/Λ₀ - B(χ)`. -/
theorem hasSumLocallyUniformlyOn_logDeriv_dirichletData_entireCompletion_sub :
    HasSumLocallyUniformlyOn
      (fun (ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support)
          s ↦
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℂ) *
          (1 / (s - ρ) + 1 / ρ))
      (fun s ↦ logDeriv (dirichletData χ hχ).entireCompletion s -
        logDeriv (dirichletData χ hχ).entireCompletion 0)
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support)ᶜ :=
  (dirichletData_entireCompletion_orderLE_one χ hχ).hasSumLocallyUniformlyOn_logDeriv_sub
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ)

/-! ### Real parts of the sum over zeros -/

/-- Every zero of `Λ₀` has `0 ≤ Re ρ`, the zero-location hypothesis of the general real-part
lemmas. -/
private theorem re_nonneg_of_divisor_dirichletData_entireCompletion_pos (ρ : ℂ)
    (hρ : 0 < MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ) :
    0 ≤ ρ.re :=
  (re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hρ).1.le

/-- Every zero of `Λ₀` has `|Re ρ| ≤ 1`. -/
private theorem abs_re_le_one_of_divisor_dirichletData_entireCompletion_pos (ρ : ℂ)
    (hρ : 0 < MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ) :
    |ρ.re| ≤ 1 :=
  have h := re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hρ
  abs_le.mpr ⟨by linarith [h.1], h.2.le⟩

/-- The real parts `m_ρ Re (1 / ρ)` over the zeros form a summable family. -/
theorem summable_divisor_dirichletData_entireCompletion_mul_re_one_div :
    Summable (fun ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion
        Set.univ).support ↦
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / (ρ : ℂ)).re) :=
  (dirichletData_entireCompletion_orderLE_one χ hχ).summable_divisor_mul_re_one_div
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (by norm_num) (abs_re_le_one_of_divisor_dirichletData_entireCompletion_pos χ hχ)

/-- The real parts `m_ρ Re (1 / (s - ρ))` form a summable family. The complex terms
`m_ρ / (s - ρ)` are not absolutely summable. -/
theorem summable_divisor_dirichletData_entireCompletion_mul_re_one_div_sub (s : ℂ) :
    Summable (fun ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion
        Set.univ).support ↦
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / (s - ρ)).re) :=
  (dirichletData_entireCompletion_orderLE_one χ hχ).summable_divisor_mul_re_one_div_sub
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion (by norm_num)
    (abs_re_le_one_of_divisor_dirichletData_entireCompletion_pos χ hχ) s

/-- For `1 ≤ Re s`, each weighted summand `m_ρ Re (1 / (s - ρ))` is nonnegative. -/
theorem divisor_dirichletData_entireCompletion_mul_re_one_div_sub_nonneg {s : ℂ}
    (hs : 1 ≤ s.re) (ρ : ℂ) :
    0 ≤ ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
      (1 / (s - ρ)).re :=
  divisor_mul_re_one_div_sub_nonneg fun hρ ↦
    (re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hρ).2.le.trans hs

/-- For `1 ≤ Re s`, the weighted summand `m_ρ Re (1 / (s - ρ))` at a zero `ρ` is positive, since
`Re ρ < 1 ≤ Re s`. -/
theorem divisor_dirichletData_entireCompletion_mul_re_one_div_sub_pos {s ρ : ℂ}
    (hs : 1 ≤ s.re)
    (hρ : 0 < MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ) :
    0 < ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
      (1 / (s - ρ)).re :=
  divisor_mul_re_one_div_sub_pos hρ
    ((re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hρ).2.trans_le hs)

/-- **Positivity of the sum over zeros.** For `1 ≤ Re s`, `0 ≤ ∑_ρ m_ρ Re (1 / (s - ρ))`, an
absolutely convergent sum of nonnegative terms. -/
theorem tsum_divisor_dirichletData_entireCompletion_mul_re_one_div_sub_nonneg
    {s : ℂ} (hs : 1 ≤ s.re) :
    0 ≤ ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / (s - ρ)).re :=
  tsum_nonneg fun ρ ↦
    divisor_dirichletData_entireCompletion_mul_re_one_div_sub_nonneg χ hχ hs ρ

/-- For `1 ≤ Re s`, the real part of `Λ₀'/Λ₀ (s)` is nonnegative. -/
theorem re_logDeriv_dirichletData_entireCompletion_nonneg {s : ℂ}
    (hs : 1 ≤ s.re) : 0 ≤ (logDeriv (dirichletData χ hχ).entireCompletion s).re := by
  rw [re_logDeriv_dirichletData_entireCompletion_eq_tsum χ hχ
    (dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hs)]
  exact tsum_divisor_dirichletData_entireCompletion_mul_re_one_div_sub_nonneg χ hχ hs

end TauCeti.LFunctions

/-! ### Retained-zero inequalities -/

namespace DirichletCharacter

open TauCeti.LFunctions

/-- **Finite retained-zero inequality.** For any primitive nonprincipal Dirichlet character `χ` of
conductor `N` (real or complex), any finite set `S ⊆ {ρ : ℂ | 0 < ρ.re}`, and any `σ ∈ [1, 2]`,
the multiplicity-weighted sum over `S` satisfies
`∑ ρ ∈ S, analyticOrderNatAt χ.LFunction ρ * Re (1 / (σ - ρ)) ≤`
`Re (L'/L)(σ, χ) + ½ log N + TauCeti.gammaLogDerivBound`. -/
theorem sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_re_logDeriv_LFunction_add
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, 0 < ρ.re) {σ : ℝ} (hσ : σ ∈ Set.Icc 1 2) :
    ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re ≤
      (logDeriv χ.LFunction σ).re + Real.log N / 2 + TauCeti.gammaLogDerivBound := by
  have hσ1 : 1 ≤ (σ : ℂ).re := by simpa using hσ.1
  have hσ0 : 0 < (σ : ℂ).re := zero_lt_one.trans_le hσ1
  have hLσ : χ.LFunction σ ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (.inl hne) hσ1
  have hfin :=
    (dirichletData_hasFunctionalEquation χ hχ
      ).sum_divisor_entireCompletion_toNat_mul_re_one_div_sub_le_re_logDeriv
      (dirichletData_hasMeromorphicContinuation χ hχ)
      (dirichletData_entireCompletion_orderLE_one χ hχ)
      (fun _ ↦ dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ) hσ1 S
  have hsum_eq : ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re =
      ∑ ρ ∈ S, ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat :
        ℝ) * (1 / ((σ : ℂ) - ρ)).re := by
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    rw [toNat_divisor_dirichletData_entireCompletion_eq_analyticOrderNatAt χ hχ hne (hS ρ hρ)]
  have hdecomp : (logDeriv (dirichletData χ hχ).entireCompletion σ).re =
      Real.log N / 2 + (logDeriv χ.gammaFactor σ).re + (logDeriv χ.LFunction σ).re := by
    rw [logDeriv_dirichletData_entireCompletion χ hχ hne hσ0 hLσ, add_re, add_re,
      div_ofNat_re, ofReal_re]
  have hgamma : (logDeriv χ.gammaFactor σ).re ≤ TauCeti.gammaLogDerivBound :=
    (le_abs_self _).trans ((abs_re_le_norm _).trans (χ.norm_logDeriv_gammaFactor_ofReal_le hσ))
  linarith

/-- **One-zero inequality.** For any primitive nonprincipal Dirichlet character `χ` of conductor
`N` (real or complex), any real zero `0 < β` of `L(·, χ)`, and any `σ ∈ [1, 2]`,
`1 / (σ - β) ≤ Re (L'/L)(σ, χ) + ½ log N + TauCeti.gammaLogDerivBound`. -/
theorem one_div_sub_le_re_logDeriv_LFunction_add {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {β σ : ℝ} (hβ : 0 < β) (hzero : χ.LFunction β = 0)
    (hσ : σ ∈ Set.Icc 1 2) :
    1 / (σ - β) ≤ (logDeriv χ.LFunction σ).re + Real.log N / 2 + TauCeti.gammaLogDerivBound := by
  have hβre : 0 < ((β : ℂ)).re := by simpa using hβ
  have hΛβ : (dirichletData χ hχ).entireCompletion β = 0 :=
    (dirichletData_entireCompletion_eq_zero_iff χ hχ hne hβre).mpr hzero
  have hβ1 : β < 1 := by
    simpa using (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hΛβ).2
  have hσβ : 0 < σ - β := by linarith [hσ.1]
  have hm_pos : 1 ≤ analyticOrderNatAt χ.LFunction β := by
    have haL := (DirichletCharacter.differentiable_LFunction hne).analyticAt (β : ℂ)
    have hne_top : analyticOrderAt χ.LFunction β ≠ ⊤ := by
      rw [← analyticOrderAt_dirichletData_entireCompletion_eq_LFunction χ hχ hne hβre]
      exact analyticOrderAt_dirichletData_entireCompletion_ne_top χ hχ β
    rw [Nat.one_le_iff_ne_zero, ← Nat.cast_ne_zero (R := ℕ∞),
      Nat.cast_analyticOrderNatAt hne_top]
    exact haL.analyticOrderAt_ne_zero.mpr hzero
  have hre_sub : (1 / ((σ : ℂ) - (β : ℂ))).re = 1 / (σ - β) := by
    rw [← ofReal_sub, ← ofReal_one, ← ofReal_div, ofReal_re]
  have hsingle :=
    χ.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_re_logDeriv_LFunction_add hχ hne
      {(β : ℂ)} (fun ρ hρ ↦ by rw [Finset.mem_singleton.mp hρ]; exact hβre) hσ
  rw [Finset.sum_singleton, hre_sub] at hsingle
  have hmult : 1 * (1 / (σ - β)) ≤
      (analyticOrderNatAt χ.LFunction β : ℝ) * (1 / (σ - β)) := by
    refine mul_le_mul_of_nonneg_right ?_ (div_nonneg zero_le_one hσβ.le)
    exact_mod_cast hm_pos
  linarith

/-! ### Example -/

/-- Specializing `sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_re_logDeriv_LFunction_add`
to the empty set at `σ = 2` shows that for every primitive nonprincipal Dirichlet character `χ`
modulo `N`, `0 ≤ Re (L'/L)(2, χ) + ½ log N + TauCeti.gammaLogDerivBound`. -/
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    0 ≤ (logDeriv χ.LFunction 2).re + Real.log N / 2 + TauCeti.gammaLogDerivBound := by
  have h := χ.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_re_logDeriv_LFunction_add hχ
    hne ∅ (by simp) (σ := 2) ⟨by norm_num, le_rfl⟩
  simpa using h

end DirichletCharacter

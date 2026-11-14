/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.Hadamard
public import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv.Bound
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic

import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Growth
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.LogDeriv
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros

/-!
# Hadamard factorization and retained-zero inequalities for Dirichlet L-functions

Let `χ` be a primitive nonprincipal Dirichlet character modulo `N`, and write
`Λ₀ = (dirichletData χ hχ).entireCompletion`. Combining `OrderLE Λ₀ 1`, `Λ₀ 0 ≠ 0`, confinement of
all zeros of `Λ₀` to `0 < Re ρ < 1`, and the combined functional and conjugation identity
`Λ₀ (1 - z) = ε(χ) * conj (Λ₀ (conj z))` with `TauCeti.OrderLE.re_logDeriv_zero_eq_neg_tsum` gives:

* **Hadamard factorization** (`dirichletData_entireCompletion_hadamard`): `Λ₀` factors globally as
  `exp (a + b * s)` times the multipliable genus-one canonical product over its zeros.
* **Real-part cancellation** (`re_logDeriv_dirichletData_entireCompletion_zero` and
  `re_logDeriv_dirichletData_entireCompletion_eq_tsum`): for every primitive `χ ≠ 1` (real or
  complex), `(logDeriv Λ₀ 0).re = -∑' ρ, m_ρ * (1 / ρ).re`, so off the zeros one has
  `(logDeriv Λ₀ s).re = ∑' ρ, m_ρ * (1 / (s - ρ)).re` with no constant term.
* **Retained-zero inequalities** (`finite_zero_sum_le_logDeriv` and `one_zero_le_logDeriv`): for
  `σ ∈ [1, 2]`, every zero summand is nonnegative and the archimedean logarithmic derivative is
  bounded in norm by `TauCeti.gammaLogDerivBound`, so any finite subset `S` in `0 < Re ρ` satisfies
  `∑ ρ ∈ S, analyticOrderNatAt χ.LFunction ρ * Re (1 / (σ - ρ)) ≤ Re (L'/L)(σ, χ) + ½ log N + C_Γ`,
  and any real zero `0 < β` of `L(·, χ)` satisfies
  `1 / (σ - β) ≤ Re (L'/L)(σ, χ) + ½ log N + C_Γ`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §§10.2 and
  11.1–11.2, Theorem 10.16 and Corollary 10.18.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
-/

public section

open Complex ComplexConjugate
open scoped BigOperators

namespace TauCeti.LFunctions

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

/-- **Order at most one.** The entire completion of a primitive nonprincipal Dirichlet record has
growth order at most `1`. -/
theorem dirichletData_entireCompletion_orderLE_one (hne : χ ≠ 1) :
    OrderLE (dirichletData χ hχ).entireCompletion 1 := by
  rw [dirichletData_entireCompletion_of_ne_one χ hχ hne]
  exact dirichletData_completed_orderLE_one χ hχ hne

private theorem re_mem_Icc_of_dirichletData_entireCompletion_eq_zero (hne : χ ≠ 1) (ρ : ℂ)
    (hρ : (dirichletData χ hχ).entireCompletion ρ = 0) : ρ.re ∈ Set.Icc 0 1 :=
  Set.Ioo_subset_Icc_self (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hne hρ)

private theorem dirichletData_entireCompletion_one_sub_eq_rootNumber_mul_conj_conj (hne : χ ≠ 1)
    (z : ℂ) :
    (dirichletData χ hχ).entireCompletion (1 - z) =
      χ.rootNumber * conj ((dirichletData χ hχ).entireCompletion (conj z)) := by
  rw [dirichletData_entireCompletion_one_sub χ hχ hne,
    dirichletData_entireCompletion_inv_conj χ hχ hne]

/-! ### Hadamard factorization and partial-fraction expansion -/

/-- Explicit Hadamard factorization of a primitive nonprincipal Dirichlet entire completion in
terms of `TauCeti.divisorProductOne`. -/
theorem dirichletData_entireCompletion_eq_mul_cexp_logDeriv_mul_divisorProductOne (hne : χ ≠ 1)
    (s : ℂ) :
    (dirichletData χ hχ).entireCompletion s =
      (dirichletData χ hχ).entireCompletion 0 *
        exp (logDeriv (dirichletData χ hχ).entireCompletion 0 * s) *
        divisorProductOne (dirichletData χ hχ).entireCompletion s :=
  (dirichletData_entireCompletion_orderLE_one χ hχ hne).eq_mul_cexp_logDeriv_mul_divisorProductOne
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne) s

/-- **Hadamard product for primitive Dirichlet completions.** For a primitive nonprincipal
character `χ`, `(dirichletData χ hχ).entireCompletion` factors globally as `exp (a + b * s)` times
the multipliable genus-one canonical product over its zeros. -/
theorem dirichletData_entireCompletion_hadamard (hne : χ ≠ 1) :
    ∃ a b : ℂ, ∀ s : ℂ,
      Multipliable (fun ρ : ℂ ↦
        weierstrassFactorOne (s / ρ) ^
          (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat) ∧
      (dirichletData χ hχ).entireCompletion s = exp (a + b * s) * ∏' ρ : ℂ,
        weierstrassFactorOne (s / ρ) ^
          (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat :=
  hadamard_of_orderLE_one
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_orderLE_one χ hχ hne)
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne)

/-- Paired partial-fraction expansion of the logarithmic derivative of a primitive nonprincipal
Dirichlet entire completion off its zeros. -/
theorem logDeriv_dirichletData_entireCompletion_eq_add_tsum (hne : χ ≠ 1) {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    logDeriv (dirichletData χ hχ).entireCompletion s =
      logDeriv (dirichletData χ hχ).entireCompletion 0 +
        ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
          ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℂ) *
            (1 / (s - ρ) + 1 / ρ) :=
  (dirichletData_entireCompletion_orderLE_one χ hχ hne).logDeriv_eq_add_tsum
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne) hs

/-- **Real-part formula for `B(χ)`.** For every primitive nonprincipal Dirichlet character `χ`
(real or complex), the real part of `logDeriv (dirichletData χ hχ).entireCompletion 0` equals
`-∑' ρ, m_ρ * Re (1 / ρ)`. -/
theorem re_logDeriv_dirichletData_entireCompletion_zero (hne : χ ≠ 1) :
    (logDeriv (dirichletData χ hχ).entireCompletion 0).re =
      -∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (ρ : ℂ)).re :=
  (dirichletData_entireCompletion_orderLE_one χ hχ hne).re_logDeriv_zero_eq_neg_tsum
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne)
    (re_mem_Icc_of_dirichletData_entireCompletion_eq_zero χ hχ hne)
    (dirichletData_entireCompletion_one_sub_eq_rootNumber_mul_conj_conj χ hχ hne)

/-- **Cancelled real-part partial-fraction expansion.** Off the zeros of
`(dirichletData χ hχ).entireCompletion`, its logarithmic derivative has real part
`∑' ρ, m_ρ * Re (1 / (s - ρ))`, with no additive constant. -/
theorem re_logDeriv_dirichletData_entireCompletion_eq_tsum (hne : χ ≠ 1) {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    (logDeriv (dirichletData χ hχ).entireCompletion s).re =
      ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (s - ρ)).re :=
  (dirichletData_entireCompletion_orderLE_one χ hχ hne).re_logDeriv_eq_tsum
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne)
    (re_mem_Icc_of_dirichletData_entireCompletion_eq_zero χ hχ hne)
    (dirichletData_entireCompletion_one_sub_eq_rootNumber_mul_conj_conj χ hχ hne) hs

/-- On `1 ≤ Re s`, the real part of the logarithmic derivative of a primitive nonprincipal
Dirichlet entire completion is nonnegative. -/
theorem re_logDeriv_dirichletData_entireCompletion_nonneg (hne : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    0 ≤ (logDeriv (dirichletData χ hχ).entireCompletion s).re := by
  rw [re_logDeriv_dirichletData_entireCompletion_eq_tsum χ hχ hne
    (dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hne hs)]
  exact OrderLE.tsum_divisor_toNat_mul_re_one_div_sub_nonneg
    (re_mem_Icc_of_dirichletData_entireCompletion_eq_zero χ hχ hne)
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion hs

/-! ### Retained-zero inequalities -/

/-- On the positive half-plane, the natural divisor multiplicity of the entire completion equals
the analytic vanishing order `analyticOrderNatAt χ.LFunction s`. -/
theorem toNat_divisor_dirichletData_entireCompletion_eq_analyticOrderNatAt (hne : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ s).toNat =
      analyticOrderNatAt χ.LFunction s := by
  have hm := dirichletData_hasMeromorphicContinuation χ hχ
  rw [MeromorphicOn.divisor_eq_analyticOrderNatAt hm.meromorphicOn_entireCompletion
    (hm.analyticAt_entireCompletion s) (Set.mem_univ s), Int.toNat_natCast,
    analyticOrderNatAt, analyticOrderNatAt,
    analyticOrderAt_dirichletData_entireCompletion_eq_LFunction χ hχ hne hs]

include hχ in
/-- **Finite retained-zero inequality.** For any primitive nonprincipal Dirichlet character `χ` of
conductor `N` (real or complex), any finite set `S ⊆ {ρ : ℂ | 0 < ρ.re}`, and any `σ ∈ [1, 2]`,
the multiplicity-weighted sum over `S` satisfies
`∑ ρ ∈ S, analyticOrderNatAt χ.LFunction ρ * Re (1 / (σ - ρ)) ≤ Re (L'/L)(σ, χ) + ½ log N + C_Γ`. -/
theorem finite_zero_sum_le_logDeriv (hne : χ ≠ 1) (S : Finset ℂ) (hS : ∀ ρ ∈ S, 0 < ρ.re)
    {σ : ℝ} (hσ : σ ∈ Set.Icc 1 2) :
    ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re ≤
      (logDeriv χ.LFunction σ).re + Real.log N / 2 + gammaLogDerivBound := by
  let Λ₀ := (dirichletData χ hχ).entireCompletion
  let d := MeromorphicOn.divisor Λ₀ Set.univ
  have hσ1 : 1 ≤ (σ : ℂ).re := by simpa using hσ.1
  have hσ0 : 0 < (σ : ℂ).re := lt_of_lt_of_le zero_lt_one hσ1
  have hΛσ : Λ₀ σ ≠ 0 := dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hne hσ1
  have hLσ : χ.LFunction σ ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (.inl hne) hσ1
  -- Extend the nonnegatively-termed zero series from `d.support` to all of `ℂ`.
  let F : ℂ → ℝ := fun ρ ↦ ((d ρ).toNat : ℝ) * (1 / ((σ : ℂ) - ρ)).re
  have hF_supp : Function.support F ⊆ d.support := fun ρ hρ ↦
    Function.mem_support.mpr fun h0 ↦ hρ (by simp [F, h0])
  have hsub_sum : HasSum (F ∘ (↑) : d.support → ℝ) (logDeriv Λ₀ σ).re := by
    rw [re_logDeriv_dirichletData_entireCompletion_eq_tsum χ hχ hne hΛσ]
    have hord := dirichletData_entireCompletion_orderLE_one χ hχ hne
    exact (hord.summable_divisor_toNat_mul_re_one_div_sub
      (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
      (dirichletData_entireCompletion_zero_ne_zero χ hχ hne)
      (re_mem_Icc_of_dirichletData_entireCompletion_eq_zero χ hχ hne) hΛσ).hasSum
  have hF_sum : HasSum F (logDeriv Λ₀ σ).re :=
    (hasSum_subtype_iff_of_support_subset hF_supp).mp hsub_sum
  have hF_nonneg (ρ : ℂ) : 0 ≤ F ρ := by
    rcases le_or_gt (d ρ) 0 with hd0 | hdpos
    · simp [F, Int.toNat_of_nonpos hd0]
    · have hΛρ := ((dirichletData_hasMeromorphicContinuation χ hχ
          ).analyticAt_entireCompletion ρ).apply_eq_zero_of_divisor_ne_zero hdpos.ne'
      exact mul_nonneg (Nat.cast_nonneg _)
        (re_one_div_sub_pos_of_dirichletData_entireCompletion_eq_zero χ hχ hne hΛρ hσ1).le
  have hfin_le : ∑ ρ ∈ S, F ρ ≤ (logDeriv Λ₀ σ).re := by
    rw [← hF_sum.tsum_eq]
    exact hF_sum.summable.sum_le_tsum S fun ρ _ ↦ hF_nonneg ρ
  have hsum_eq : ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re =
      ∑ ρ ∈ S, F ρ := by
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    dsimp only [F, d, Λ₀]
    rw [toNat_divisor_dirichletData_entireCompletion_eq_analyticOrderNatAt χ hχ hne (hS ρ hρ)]
  -- Decompose `(logDeriv Λ₀ σ).re` and bound the archimedean term by `gammaLogDerivBound`.
  have hdecomp : (logDeriv Λ₀ σ).re =
      Real.log N / 2 + (logDeriv χ.gammaFactor σ).re + (logDeriv χ.LFunction σ).re := by
    dsimp only [Λ₀]
    rw [logDeriv_dirichletData_entireCompletion χ hχ hne hσ0 hLσ, add_re, add_re,
      div_ofNat_re, ofReal_re]
  have hgamma : (logDeriv χ.gammaFactor σ).re ≤ gammaLogDerivBound :=
    (le_abs_self _).trans ((abs_re_le_norm _).trans (χ.norm_logDeriv_gammaFactor_ofReal_le hσ))
  linarith

include hχ in
/-- **One-zero inequality.** For any primitive nonprincipal Dirichlet character `χ` of conductor
`N` (real or complex), any real zero `0 < β` of `L(·, χ)`, and any `σ ∈ [1, 2]`,
`1 / (σ - β) ≤ Re (L'/L)(σ, χ) + ½ log N + C_Γ`. -/
theorem one_zero_le_logDeriv (hne : χ ≠ 1) {β σ : ℝ} (hβ : 0 < β)
    (hzero : χ.LFunction β = 0) (hσ : σ ∈ Set.Icc 1 2) :
    1 / (σ - β) ≤ (logDeriv χ.LFunction σ).re + Real.log N / 2 + gammaLogDerivBound := by
  have hβre : 0 < ((β : ℂ)).re := by simpa using hβ
  have hΛβ : (dirichletData χ hχ).entireCompletion β = 0 :=
    (dirichletData_entireCompletion_eq_zero_iff χ hχ hne hβre).mpr hzero
  have hβ1 : β < 1 := by
    simpa using (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hne hΛβ).2
  have hσβ : 0 < σ - β := by linarith [hσ.1]
  have hm_pos : 1 ≤ analyticOrderNatAt χ.LFunction β := by
    have haL := (DirichletCharacter.differentiable_LFunction hne).analyticAt (β : ℂ)
    have hne_top : analyticOrderAt χ.LFunction β ≠ ⊤ := by
      rw [← analyticOrderAt_dirichletData_entireCompletion_eq_LFunction χ hχ hne hβre]
      exact analyticOrderAt_dirichletData_entireCompletion_ne_top χ hχ hne β
    rw [Nat.one_le_iff_ne_zero, ← Nat.cast_ne_zero (R := ℕ∞),
      Nat.cast_analyticOrderNatAt hne_top]
    exact haL.analyticOrderAt_ne_zero.mpr hzero
  have hre_sub : (1 / ((σ : ℂ) - (β : ℂ))).re = 1 / (σ - β) := by
    rw [← ofReal_sub, ← ofReal_one, ← ofReal_div, ofReal_re]
  have hsingle := finite_zero_sum_le_logDeriv χ hχ hne {(β : ℂ)}
    (fun ρ hρ ↦ by rw [Finset.mem_singleton.mp hρ]; exact hβre) hσ
  rw [Finset.sum_singleton, hre_sub] at hsingle
  have hmult : 1 * (1 / (σ - β)) ≤
      (analyticOrderNatAt χ.LFunction β : ℝ) * (1 / (σ - β)) := by
    refine mul_le_mul_of_nonneg_right ?_ (div_nonneg zero_le_one hσβ.le)
    exact_mod_cast hm_pos
  linarith

/-! ### Example -/

include hχ in
/-- Specializing `finite_zero_sum_le_logDeriv` to the empty set at `σ = 2` shows that for every
primitive nonprincipal Dirichlet character `χ` modulo `N`,
`0 ≤ Re (L'/L)(2, χ) + ½ log N + C_Γ`. -/
example (hne : χ ≠ 1) :
    0 ≤ (logDeriv χ.LFunction 2).re + Real.log N / 2 + gammaLogDerivBound := by
  have h := finite_zero_sum_le_logDeriv χ hχ hne ∅ (by simp) (σ := 2) ⟨by norm_num, le_rfl⟩
  simpa using h

end TauCeti.LFunctions

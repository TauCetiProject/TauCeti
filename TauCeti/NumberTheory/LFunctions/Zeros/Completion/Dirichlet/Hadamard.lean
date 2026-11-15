/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.LogDeriv
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Hadamard
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Growth
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros

/-!
# Hadamard partial-fraction identities and retained-zero bounds for Dirichlet L-functions

Let `χ` be a nonprincipal primitive Dirichlet character of conductor `N`, and write
`Λ₀(s, χ) = (dirichletData χ hχ).entireCompletion s = N ^ (s / 2) Λ(s, χ)`. Combining order at
most one (`dirichletData_completed_orderLE_one`), nonvanishing at `0`
(`dirichletData_entireCompletion_zero_ne_zero`), location of all zeros in the open critical strip
`0 < Re ρ < 1` (`re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero`), and the general
functional-equation cancellation of `TauCeti.NumberTheory.LFunctions.Zeros.Completion.Hadamard`
gives:

* the Hadamard constant formula `(logDeriv Λ₀ 0).re = -∑' ρ, m_ρ Re (1 / ρ)`, or equivalently
  `Re (Λ'/Λ(0, χ)) + ½ log N = -∑' ρ, m_ρ Re (1 / ρ)`;
* the unpaired real-part partial-fraction expansion
  `(logDeriv Λ₀ s).re = ∑' ρ, m_ρ Re (1 / (s - ρ))` off the zeros of `Λ₀`, and hence on `0 < Re s`
  off the zeros of `L(s, χ)`
  `Re (L'/L(s, χ)) + ½ log N + Re (γ'/γ(s, χ)) = ∑' ρ, m_ρ Re (1 / (s - ρ))`, where the sum runs
  over the nontrivial zeros (`analyticOrderNatAt χ.completedLFunction ρ`) rather than the trivial
  zeros of `L(s, χ)` at nonpositive integers;
* positivity `(logDeriv Λ₀ s).re ≥ 0` and finite-subset retention on `1 ≤ Re s`: on any finite set
  `S` contained in `0 < Re ρ`, the multiplicities of `Λ₀` and `L(·, χ)` coincide, so
  `∑ ρ ∈ S, m_ρ Re (1 / (s - ρ)) ≤ Re (L'/L(s, χ)) + ½ log N + Re (γ'/γ(s, χ))` for `1 ≤ Re s`,
  and for real `σ ∈ [1, 2]` the explicit bound `TauCeti.gammaLogDerivBound` controls the gamma term
  uniformly in `N`, `χ`, and `σ`.

## Main results

* `TauCeti.LFunctions.re_logDeriv_dirichletData_entireCompletion_zero` and
  `DirichletCharacter.re_logDeriv_completedLFunction_zero`: the real part of the Hadamard constant
  equals `-∑' ρ, m_ρ Re (1 / ρ)`.
* `TauCeti.LFunctions.re_logDeriv_dirichletData_entireCompletion` and
  `DirichletCharacter.re_logDeriv_LFunction_add_eq_tsum`: unpaired real-part partial-fraction
  identities for `Λ₀(s, χ)` and `L(s, χ)`.
* `DirichletCharacter.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_add_gammaFactor` and
  `DirichletCharacter.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le`: retained finite-sum
  lower bounds on `1 ≤ Re s` and on `σ ∈ [1, 2]`.
* `DirichletCharacter.re_one_div_sub_le_re_logDeriv_LFunction_add` and
  `DirichletCharacter.one_div_sub_le_re_logDeriv_LFunction_add`: single-zero specializations for
  complex and real zeros.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), Theorem 10.16 and
  Corollary 10.18, pp. 351–353, and §11.1.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
-/

public section

open Complex ComplexConjugate Filter Topology Bornology
open scoped BigOperators

namespace TauCeti.LFunctions

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

/-- The entire completion of a nonprincipal primitive Dirichlet record has order at most one. -/
theorem dirichletData_entireCompletion_orderLE_one (hne : χ ≠ 1) :
    OrderLE (dirichletData χ hχ).entireCompletion 1 := by
  rw [dirichletData_entireCompletion_of_ne_one χ hχ hne]
  exact dirichletData_completed_orderLE_one χ hχ hne

/-- The zeros of a nonprincipal primitive Dirichlet entire completion have bounded real parts. -/
theorem isBounded_re_divisor_support_dirichletData_entireCompletion (hne : χ ≠ 1) :
    IsBounded (Complex.re ''
      (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support) :=
  (dirichletData_hasFunctionalEquation χ hχ).isBounded_re_divisor_support_entireCompletion
    (dirichletData_hasMeromorphicContinuation χ hχ)
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne) (B := 1) fun _ hρ ↦
      (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hne hρ).2.le

/-- **Paired complex partial fractions for a primitive Dirichlet completion.** Off the zeros of
`Λ₀(s, χ)`, its logarithmic derivative expands as `Λ₀'/Λ₀(0, χ) + ∑' ρ, m_ρ (1 / (s - ρ) + 1 / ρ)`.
-/
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

/-- Absolute summability of `(analyticOrderNatAt Λ₀ ρ) * Re (1 / (s - ρ))` over `ℂ` for a
nonprincipal primitive Dirichlet entire completion. -/
theorem summable_norm_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div_sub
    (hne : χ ≠ 1) (s : ℂ) :
    Summable (fun ρ : ℂ ↦
      ‖(analyticOrderNatAt (dirichletData χ hχ).entireCompletion ρ : ℝ) * (1 / (s - ρ)).re‖) :=
  OrderLE.summable_norm_analyticOrderNatAt_mul_re_one_div_sub
    (dirichletData_entireCompletion_orderLE_one χ hχ hne)
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion (by norm_num)
    (isBounded_re_divisor_support_dirichletData_entireCompletion χ hχ hne) s

/-- Absolute summability of `(analyticOrderNatAt Λ₀ ρ) * Re (1 / ρ)` over `ℂ` for a nonprincipal
primitive Dirichlet entire completion. -/
theorem summable_norm_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div
    (hne : χ ≠ 1) :
    Summable (fun ρ : ℂ ↦
      ‖(analyticOrderNatAt (dirichletData χ hχ).entireCompletion ρ : ℝ) * (1 / ρ).re‖) :=
  OrderLE.summable_norm_analyticOrderNatAt_mul_re_one_div
    (dirichletData_entireCompletion_orderLE_one χ hχ hne)
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion (by norm_num)
    (isBounded_re_divisor_support_dirichletData_entireCompletion χ hχ hne)

/-- **Real part of the Hadamard constant for a primitive Dirichlet completion.** For a nonprincipal
primitive character `χ`, `(logDeriv Λ₀ 0).re = -∑' ρ, m_ρ Re (1 / ρ)`. -/
theorem re_logDeriv_dirichletData_entireCompletion_zero (hne : χ ≠ 1) :
    (logDeriv (dirichletData χ hχ).entireCompletion 0).re =
      -∑' ρ : ℂ,
        (analyticOrderNatAt (dirichletData χ hχ).entireCompletion ρ : ℝ) * (1 / ρ).re :=
  (dirichletData_hasFunctionalEquation χ hχ).re_logDeriv_entireCompletion_zero
    (dirichletData_hasMeromorphicContinuation χ hχ)
    (dirichletData_entireCompletion_orderLE_one χ hχ hne)
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne)
    (isBounded_re_divisor_support_dirichletData_entireCompletion χ hχ hne)

/-- **Unpaired real-part partial fractions for a primitive Dirichlet completion.** Off the zeros of
`Λ₀(s, χ)`, `(logDeriv Λ₀ s).re = ∑' ρ, m_ρ Re (1 / (s - ρ))`. -/
theorem re_logDeriv_dirichletData_entireCompletion (hne : χ ≠ 1) {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    (logDeriv (dirichletData χ hχ).entireCompletion s).re =
      ∑' ρ : ℂ,
        (analyticOrderNatAt (dirichletData χ hχ).entireCompletion ρ : ℝ) * (1 / (s - ρ)).re :=
  (dirichletData_hasFunctionalEquation χ hχ).re_logDeriv_entireCompletion
    (dirichletData_hasMeromorphicContinuation χ hχ)
    (dirichletData_entireCompletion_orderLE_one χ hχ hne)
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne)
    (isBounded_re_divisor_support_dirichletData_entireCompletion χ hχ hne) hs

/-- On `1 ≤ Re s`, the real part of the logarithmic derivative of a nonprincipal primitive
Dirichlet entire completion is nonnegative. -/
theorem re_logDeriv_dirichletData_entireCompletion_nonneg (hne : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    0 ≤ (logDeriv (dirichletData χ hχ).entireCompletion s).re :=
  (dirichletData_hasFunctionalEquation χ hχ).re_logDeriv_entireCompletion_nonneg
    (dirichletData_hasMeromorphicContinuation χ hχ)
    (dirichletData_entireCompletion_orderLE_one χ hχ hne)
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne)
    (dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hne hs) fun _ hρ ↦
      (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hne hρ).2.le.trans hs

/-- On `1 ≤ Re s`, any finite sum of zero terms of a nonprincipal primitive Dirichlet entire
completion is bounded by `(logDeriv Λ₀ s).re`. -/
theorem sum_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div_sub_le (hne : χ ≠ 1)
    {s : ℂ} (hs : 1 ≤ s.re) (S : Finset ℂ) :
    (∑ ρ ∈ S,
        (analyticOrderNatAt (dirichletData χ hχ).entireCompletion ρ : ℝ) * (1 / (s - ρ)).re) ≤
      (logDeriv (dirichletData χ hχ).entireCompletion s).re := by
  have hfe := dirichletData_hasFunctionalEquation χ hχ
  exact hfe.sum_analyticOrderNatAt_entireCompletion_mul_re_one_div_sub_le
    (dirichletData_hasMeromorphicContinuation χ hχ)
    (dirichletData_entireCompletion_orderLE_one χ hχ hne)
    (dirichletData_entireCompletion_zero_ne_zero χ hχ hne)
    (dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hne hs)
    (fun _ hρ ↦ (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hne hρ).2.le.trans hs) S

end TauCeti.LFunctions

/-! ### Formulas and retained-zero bounds in terms of `DirichletCharacter.LFunction` -/

namespace DirichletCharacter

open TauCeti.LFunctions

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- Absolute summability of `(analyticOrderNatAt χ.completedLFunction ρ) * Re (1 / (s - ρ))` over
`ℂ` for a nonprincipal primitive character `χ`. -/
theorem summable_norm_analyticOrderNatAt_completedLFunction_mul_re_one_div_sub
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ) :
    Summable (fun ρ : ℂ ↦
      ‖(analyticOrderNatAt χ.completedLFunction ρ : ℝ) * (1 / (s - ρ)).re‖) := by
  simpa only [analyticOrderNatAt_dirichletData_entireCompletion χ hχ hne] using
    summable_norm_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div_sub χ hχ hne s

/-- Absolute summability of `(analyticOrderNatAt χ.completedLFunction ρ) * Re (1 / ρ)` over `ℂ` for
a nonprincipal primitive character `χ`. -/
theorem summable_norm_analyticOrderNatAt_completedLFunction_mul_re_one_div
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    Summable (fun ρ : ℂ ↦ ‖(analyticOrderNatAt χ.completedLFunction ρ : ℝ) * (1 / ρ).re‖) := by
  simpa only [analyticOrderNatAt_dirichletData_entireCompletion χ hχ hne] using
    summable_norm_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div χ hχ hne

/-- **Real part of the Hadamard constant for Mathlib's completed Dirichlet L-function.** For a
nonprincipal primitive character `χ` modulo `N`,
`Re (logDeriv χ.completedLFunction 0) + ½ log N = -∑' ρ, m_ρ Re (1 / ρ)`. -/
theorem re_logDeriv_completedLFunction_zero (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    (logDeriv χ.completedLFunction 0).re + Real.log N / 2 =
      -∑' ρ : ℂ, (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * (1 / ρ).re := by
  have h0 : χ.completedLFunction 0 ≠ 0 := by
    have hΛ := dirichletData_entireCompletion_zero_ne_zero χ hχ hne
    rw [dirichletData_entireCompletion_eq χ hχ hne] at hΛ
    exact right_ne_zero_of_mul hΛ
  have hlog := congrArg Complex.re
    (logDeriv_dirichletData_entireCompletion_eq_completed χ hχ hne h0)
  rw [add_re, div_ofNat_re, ofReal_re,
    re_logDeriv_dirichletData_entireCompletion_zero χ hχ hne] at hlog
  simp_rw [← analyticOrderNatAt_dirichletData_entireCompletion χ hχ hne]
  linarith

/-- **Unpaired real-part partial fractions for `DirichletCharacter.LFunction`.** On `0 < Re s` away
from the zeros of `L(s, χ)`,
`Re (L'/L(s, χ)) + ½ log N + Re (γ'/γ(s, χ)) = ∑' ρ, m_ρ Re (1 / (s - ρ))`, where `m_ρ` is the
multiplicity of `ρ` as a nontrivial zero (`analyticOrderNatAt χ.completedLFunction ρ`). -/
theorem re_logDeriv_LFunction_add_eq_tsum (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) (hL : χ.LFunction s ≠ 0) :
    (logDeriv χ.LFunction s).re + Real.log N / 2 + (logDeriv χ.gammaFactor s).re =
      ∑' ρ : ℂ, (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * (1 / (s - ρ)).re := by
  have hΛ : (dirichletData χ hχ).entireCompletion s ≠ 0 :=
    (dirichletData_entireCompletion_eq_zero_iff χ hχ hne hs).not.mpr hL
  have hlog := congrArg Complex.re (logDeriv_dirichletData_entireCompletion χ hχ hne hs hL)
  rw [add_re, add_re, div_ofNat_re, ofReal_re,
    re_logDeriv_dirichletData_entireCompletion χ hχ hne hΛ] at hlog
  simp_rw [← analyticOrderNatAt_dirichletData_entireCompletion χ hχ hne]
  linarith

/-- **Retained finite zero sum on `1 ≤ Re s`.** For any finite set `S` in the open right half-plane
`0 < Re ρ` and any `s` with `1 ≤ Re s`, the finite sum of `m_ρ Re (1 / (s - ρ))` weighted by the
analytic multiplicities of `χ.LFunction` is bounded by
`Re (L'/L(s, χ)) + ½ log N + Re (γ'/γ(s, χ))`. -/
theorem sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_add_gammaFactor
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {S : Finset ℂ} (hS : ∀ ρ ∈ S, 0 < ρ.re)
    {s : ℂ} (hs : 1 ≤ s.re) :
    (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / (s - ρ)).re) ≤
      (logDeriv χ.LFunction s).re + Real.log N / 2 + (logDeriv χ.gammaFactor s).re := by
  have hspos : 0 < s.re := by linarith
  have hL : χ.LFunction s ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (.inl hne) hs
  have hsum : (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / (s - ρ)).re) =
      ∑ ρ ∈ S,
        (analyticOrderNatAt (dirichletData χ hχ).entireCompletion ρ : ℝ) * (1 / (s - ρ)).re := by
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    rw [analyticOrderNatAt_dirichletData_entireCompletion_eq_LFunction χ hχ hne (hS ρ hρ)]
  have hlog := congrArg Complex.re (logDeriv_dirichletData_entireCompletion χ hχ hne hspos hL)
  rw [add_re, add_re, div_ofNat_re, ofReal_re] at hlog
  have hle := sum_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div_sub_le χ hχ hne
    hs S
  linarith

/-- **Retained finite zero sum on `[1, 2]`.** For a nonprincipal primitive character `χ` modulo
`N`, any finite set `S` in `0 < Re ρ`, and any real `σ ∈ [1, 2]`,
`∑ ρ ∈ S, m_ρ Re (1 / (σ - ρ)) ≤ Re (L'/L(σ, χ)) + ½ log N + TauCeti.gammaLogDerivBound`. -/
theorem sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {S : Finset ℂ} (hS : ∀ ρ ∈ S, 0 < ρ.re) {σ : ℝ} (hσ₁ : 1 ≤ σ) (hσ₂ : σ ≤ 2) :
    (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re) ≤
      (logDeriv χ.LFunction σ).re + Real.log N / 2 + TauCeti.gammaLogDerivBound := by
  have hle := χ.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_add_gammaFactor hχ hne hS
    (s := (σ : ℂ)) (by simpa using hσ₁)
  have hγ : (logDeriv χ.gammaFactor (σ : ℂ)).re ≤ TauCeti.gammaLogDerivBound :=
    (re_le_norm _).trans (χ.norm_logDeriv_gammaFactor_ofReal_le ⟨hσ₁, hσ₂⟩)
  linarith

/-- **Single-zero lower bound on `1 ≤ Re s`.** If `ρ` is a zero of `χ.LFunction` with `0 < Re ρ`
and `1 ≤ Re s`, then `Re (1 / (s - ρ)) ≤ Re (L'/L(s, χ)) + ½ log N + Re (γ'/γ(s, χ))`. -/
theorem re_one_div_sub_le_re_logDeriv_LFunction_add_gammaFactor (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hz : χ.LFunction ρ = 0) {s : ℂ} (hs : 1 ≤ s.re) :
    (1 / (s - ρ)).re ≤
      (logDeriv χ.LFunction s).re + Real.log N / 2 + (logDeriv χ.gammaFactor s).re := by
  have hsum := χ.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_add_gammaFactor hχ hne
    (S := {ρ}) (by simpa using hρ) hs
  rw [Finset.sum_singleton] at hsum
  have hΛ0 : (dirichletData χ hχ).entireCompletion ρ = 0 :=
    (dirichletData_entireCompletion_eq_zero_iff χ hχ hne hρ).mpr hz
  have hpos : 0 ≤ (1 / (s - ρ)).re :=
    (re_one_div_sub_pos_of_dirichletData_entireCompletion_eq_zero χ hχ hne hΛ0 hs).le
  have hm : (1 : ℝ) ≤ (analyticOrderNatAt χ.LFunction ρ : ℝ) := by
    rw [← analyticOrderNatAt_dirichletData_entireCompletion_eq_LFunction χ hχ hne hρ]
    have ha := (dirichletData_hasMeromorphicContinuation χ hχ).analyticAt_entireCompletion ρ
    have hne0 : analyticOrderNatAt (dirichletData χ hχ).entireCompletion ρ ≠ 0 := by
      rw [← Nat.cast_ne_zero (R := ℕ∞), Nat.cast_analyticOrderNatAt
        (analyticOrderAt_dirichletData_entireCompletion_ne_top χ hχ hne ρ)]
      exact ha.analyticOrderAt_ne_zero.mpr hΛ0
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne0
  calc (1 / (s - ρ)).re = 1 * (1 / (s - ρ)).re := (one_mul _).symm
    _ ≤ (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / (s - ρ)).re :=
        mul_le_mul_of_nonneg_right hm hpos
    _ ≤ (logDeriv χ.LFunction s).re + Real.log N / 2 + (logDeriv χ.gammaFactor s).re := hsum

/-- **Single complex zero lower bound on `[1, 2]`.** If `ρ` is a zero of `χ.LFunction` with
`0 < Re ρ` and `σ ∈ [1, 2]`, then
`Re (1 / (σ - ρ)) ≤ Re (L'/L(σ, χ)) + ½ log N + TauCeti.gammaLogDerivBound`. -/
theorem re_one_div_sub_le_re_logDeriv_LFunction_add (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hz : χ.LFunction ρ = 0) {σ : ℝ} (hσ₁ : 1 ≤ σ) (hσ₂ : σ ≤ 2) :
    (1 / ((σ : ℂ) - ρ)).re ≤
      (logDeriv χ.LFunction σ).re + Real.log N / 2 + TauCeti.gammaLogDerivBound := by
  have hle := χ.re_one_div_sub_le_re_logDeriv_LFunction_add_gammaFactor hχ hne hρ hz
    (s := (σ : ℂ)) (by simpa using hσ₁)
  have hγ : (logDeriv χ.gammaFactor (σ : ℂ)).re ≤ TauCeti.gammaLogDerivBound :=
    (re_le_norm _).trans (χ.norm_logDeriv_gammaFactor_ofReal_le ⟨hσ₁, hσ₂⟩)
  linarith

/-- **Single real zero lower bound on `[1, 2]`.** If `β > 0` is a real zero of `χ.LFunction` for a
nonprincipal primitive character `χ` modulo `N`, then for every `σ ∈ [1, 2]`,
`1 / (σ - β) ≤ Re (L'/L(σ, χ)) + ½ log N + TauCeti.gammaLogDerivBound`. -/
theorem one_div_sub_le_re_logDeriv_LFunction_add (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {β : ℝ} (hβ : 0 < β) (hz : χ.LFunction (β : ℂ) = 0) {σ : ℝ} (hσ₁ : 1 ≤ σ) (hσ₂ : σ ≤ 2) :
    1 / (σ - β) ≤
      (logDeriv χ.LFunction σ).re + Real.log N / 2 + TauCeti.gammaLogDerivBound := by
  have hle := χ.re_one_div_sub_le_re_logDeriv_LFunction_add hχ hne
    (ρ := (β : ℂ)) (by simpa using hβ) hz hσ₁ hσ₂
  have hre : (1 / ((σ : ℂ) - (β : ℂ))).re = 1 / (σ - β) := by
    rw [← ofReal_sub, ← ofReal_one, ← ofReal_div, ofReal_re]
  rwa [hre] at hle

/-! ### Examples -/

/-- The retained zero-sum bound specializes directly when `S` consists of nontrivial zeros in the
open critical strip and `1 < σ ≤ 2`. -/
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, (0 < ρ.re ∧ ρ.re < 1) ∧ χ.LFunction ρ = 0)
    {σ : ℝ} (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re ≤
      (logDeriv χ.LFunction σ).re + Real.log N / 2 + TauCeti.gammaLogDerivBound :=
  χ.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le hχ hne (fun ρ hρ ↦ (hS ρ hρ).1.1)
    hσ₁.le hσ₂

/-- Every nonprincipal Dirichlet character has modulus `N ≥ 3`, so `Real.log N / 2 > 0` in the
retained-zero inequalities (moduli `1` and `2` admit only the principal character). -/
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hne : χ ≠ 1) :
    3 ≤ N ∧ 0 < Real.log N / 2 := by
  have hN3 : 3 ≤ N := by
    by_contra hlt
    have hpos : 0 < N := NeZero.pos N
    interval_cases N
    · exact hne <| MulChar.ext fun u ↦ by
        rw [(by decide : ∀ u : (ZMod 1)ˣ, (u : ZMod 1) = 1) u]
        simp
    · exact hne <| MulChar.ext fun u ↦ by
        rw [(by decide : ∀ u : (ZMod 2)ˣ, (u : ZMod 2) = 1) u]
        simp
  refine ⟨hN3, div_pos (Real.log_pos ?_) two_pos⟩
  exact_mod_cast (by omega : 1 < N)

/-- Sign check on a complex critical-strip summand: at `s = 2` and `ρ = 1/2 + 14i`, the retained
partial-fraction term `(1 / (2 - ρ)).re` is strictly positive. -/
example : 0 < (1 / ((2 : ℂ) - (1 / 2 + 14 * I))).re := by
  rw [one_div, Complex.inv_re_pos]
  simp
  norm_num

end DirichletCharacter

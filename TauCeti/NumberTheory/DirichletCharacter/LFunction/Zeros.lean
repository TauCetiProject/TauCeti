/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.LogDeriv
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Hadamard

/-!
# Partial-fraction expansion and retained-zero inequalities for Dirichlet L-functions

Let `χ` be a nonprincipal primitive Dirichlet character of conductor `q` (real or complex). On the
open right half-plane `0 < Re s` away from the zeros of `L(χ, ·)`, combining the logarithmic
derivative of the completed L-function with the Hadamard real-part cancellation
`Re B(χ) = -∑_ρ m_ρ Re (1 / ρ)` expresses `(logDeriv χ.LFunction s).re` in terms of the nontrivial
zeros `{z : ℂ | 0 < z.re}` of `L(χ, ·)`, weighted by their analytic multiplicities
`analyticOrderNatAt χ.LFunction ρ`:
`(logDeriv χ.LFunction s).re + ½ log q + (logDeriv χ.gammaFactor s).re = ∑_ρ m_ρ Re (1 / (s - ρ))`.

Every zero of `L(χ, ·)` has `Re ρ < 1` and finite positive multiplicity. On `1 ≤ Re s`, all terms
`m_ρ Re (1 / (s - ρ))` in `{0 < Re ρ}` are nonnegative, while the hypothesis `0 < Re ρ` excludes
the trivial zeros of `L(χ, ·)` on `Re ρ ≤ 0` that the archimedean factor cancels in the completed
function. Discarding zeros outside any finite subset `S ⊆ {0 < Re ρ}` and bounding the archimedean
term on the real interval `[1, 2]` by `TauCeti.gammaLogDerivBound` yields the retained-zero
inequalities `DirichletCharacter.finite_zero_sum_le_logDeriv` and
`DirichletCharacter.one_zero_le_logDeriv`, with `TauCeti.gammaLogDerivBound` chosen before `q`,
`χ`, `S`, `β` and `σ`.

## Main results

* `DirichletCharacter.re_lt_one_of_LFunction_eq_zero` and
  `DirichletCharacter.analyticOrderNatAt_LFunction_pos`: every zero of a nonprincipal Dirichlet
  L-function lies in `Re ρ < 1` and has finite positive analytic multiplicity.
* `DirichletCharacter.re_logDeriv_LFunction_add_eq_tsum`: exact real-part partial-fraction
  identity over `{z : ℂ | 0 < z.re}` on `0 < Re s` away from zeros.
* `DirichletCharacter.sum_analyticOrderNatAt_mul_re_one_div_sub_le_re_logDeriv_add`: finite-sum
  retained-zero inequality at arbitrary complex height in `1 ≤ Re s`.
* `DirichletCharacter.tsum_analyticOrderNatAt_mul_re_one_div_sub_le_logDeriv`,
  `DirichletCharacter.finite_zero_sum_le_logDeriv` and
  `DirichletCharacter.sum_re_one_div_sub_le_logDeriv`: infinite, multiplicity-weighted finite, and
  unweighted finite retained-zero inequalities on `σ ∈ [1, 2]` with explicit constant
  `TauCeti.gammaLogDerivBound`.
* `DirichletCharacter.mul_one_div_sub_le_logDeriv`, `DirichletCharacter.one_zero_le_logDeriv` and
  `DirichletCharacter.one_zero_le_logDeriv_one`: single real-zero inequalities on `[1, 2]` and at
  `σ = 1`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), Theorem 10.16 and
  Corollary 10.18, pp. 351–353.
-/

public section

open Complex
open scoped BigOperators

namespace DirichletCharacter

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-! ### Zero location and finiteness of multiplicities for nonprincipal characters -/

/-- Every zero of a nonprincipal Dirichlet L-function has real part strictly less than `1`. -/
theorem re_lt_one_of_LFunction_eq_zero (hne : χ ≠ 1) {ρ : ℂ} (hzero : χ.LFunction ρ = 0) :
    ρ.re < 1 := by
  by_contra h
  exact χ.LFunction_ne_zero_of_one_le_re (.inl hne) (not_lt.mp h) hzero

/-- A nonprincipal Dirichlet L-function has finite analytic order at every complex point. -/
theorem analyticOrderAt_LFunction_ne_top (hne : χ ≠ 1) (s : ℂ) :
    analyticOrderAt χ.LFunction s ≠ ⊤ := by
  have ha : AnalyticOnNhd ℂ χ.LFunction Set.univ :=
    fun z _ ↦ (differentiable_LFunction hne).analyticAt z
  refine ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := 1) (Set.mem_univ 1) (Set.mem_univ s) ?_
  rw [(ha 1 (Set.mem_univ 1)).analyticOrderAt_eq_zero.mpr (LFunction_apply_one_ne_zero hne)]
  simp

/-- At any zero of a nonprincipal Dirichlet L-function, the natural analytic multiplicity
`analyticOrderNatAt χ.LFunction ρ` is positive. -/
theorem analyticOrderNatAt_LFunction_pos (hne : χ ≠ 1) {ρ : ℂ} (hzero : χ.LFunction ρ = 0) :
    0 < analyticOrderNatAt χ.LFunction ρ := by
  have ha := (differentiable_LFunction hne).analyticAt ρ
  have h0 : analyticOrderAt χ.LFunction ρ ≠ 0 := ha.analyticOrderAt_ne_zero.mpr hzero
  have htop := χ.analyticOrderAt_LFunction_ne_top hne ρ
  rw [Nat.pos_iff_ne_zero]
  intro hnat
  apply h0
  rw [← Nat.cast_analyticOrderNatAt htop, hnat, Nat.cast_zero]

/-- Away from the zeros of a nonprincipal Dirichlet L-function, `analyticOrderNatAt` vanishes. -/
theorem analyticOrderNatAt_LFunction_eq_zero_of_ne_zero (hne : χ ≠ 1) {s : ℂ}
    (hs : χ.LFunction s ≠ 0) : analyticOrderNatAt χ.LFunction s = 0 := by
  rw [analyticOrderNatAt,
    ((differentiable_LFunction hne).analyticAt s).analyticOrderAt_eq_zero.mpr hs,
    ENat.toNat_zero]

/-! ### Unpaired real-part partial fractions over nontrivial zeros -/

/-- For a nonprincipal primitive character, `∑ m_ρ Re (1 / ρ)` over `{z : ℂ | 0 < z.re}` is
summable. -/
theorem summable_analyticOrderNatAt_LFunction_mul_re_one_div (hprim : χ.IsPrimitive)
    (hne : χ ≠ 1) :
    Summable (fun ρ : {z : ℂ | 0 < z.re} ↦
      (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / (ρ : ℂ)).re) := by
  refine ((TauCeti.LFunctions.summable_divisor_dirichletData_entireCompletion_mul_re_one_div
    χ hprim hne).comp_injective Subtype.val_injective).congr fun ρ ↦ ?_
  dsimp only [Function.comp_apply]
  rw [TauCeti.LFunctions.divisor_toNat_dirichletData_entireCompletion_eq χ hprim hne ρ,
    ite_eq_left ρ.property.out]

/-- For a nonprincipal primitive character, `∑ m_ρ Re (1 / (s - ρ))` over `{z : ℂ | 0 < z.re}` is
summable at every `s : ℂ`. -/
theorem summable_analyticOrderNatAt_LFunction_mul_re_one_div_sub (hprim : χ.IsPrimitive)
    (hne : χ ≠ 1) (s : ℂ) :
    Summable (fun ρ : {z : ℂ | 0 < z.re} ↦
      (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / (s - ρ)).re) := by
  refine ((TauCeti.LFunctions.summable_divisor_dirichletData_entireCompletion_mul_re_one_div_sub
    χ hprim hne s).comp_injective Subtype.val_injective).congr fun ρ ↦ ?_
  dsimp only [Function.comp_apply]
  rw [TauCeti.LFunctions.divisor_toNat_dirichletData_entireCompletion_eq χ hprim hne ρ,
    ite_eq_left ρ.property.out]

/-- **Real-part partial-fraction expansion of `L'/L(s, χ)`.** On `0 < Re s` away from the zeros of
`L(χ, ·)`, for any nonprincipal primitive character `χ` (real or complex),
`Re (L'/L)(s, χ) + ½ log q + Re (Γ_χ'/Γ_χ)(s) = ∑_{0 < Re ρ} m_ρ Re (1 / (s - ρ))`. -/
theorem re_logDeriv_LFunction_add_eq_tsum (hprim : χ.IsPrimitive) (hne : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) (hL : χ.LFunction s ≠ 0) :
    (logDeriv χ.LFunction s).re + Real.log q / 2 + (logDeriv χ.gammaFactor s).re =
      ∑' ρ : {z : ℂ | 0 < z.re},
        (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / (s - ρ)).re := by
  have hΛs : (TauCeti.LFunctions.dirichletData χ hprim).entireCompletion s ≠ 0 :=
    (TauCeti.LFunctions.dirichletData_entireCompletion_eq_zero_iff χ hprim hne hs).not.mpr hL
  have hlog := congrArg re
    (TauCeti.LFunctions.logDeriv_dirichletData_entireCompletion χ hprim hne hs hL)
  simp only [add_re, div_ofNat_re, ofReal_re] at hlog
  have htsum := TauCeti.LFunctions.re_logDeriv_dirichletData_entireCompletion χ hprim hne hΛs
  let g : ℂ → ℝ := fun ρ ↦
    ((MeromorphicOn.divisor (TauCeti.LFunctions.dirichletData χ hprim).entireCompletion
      Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re
  have hsupp : Function.support g ⊆ {z : ℂ | 0 < z.re} := by
    intro ρ hρ
    rw [Set.mem_ofPred_eq]
    by_contra hle
    exact hρ (by
      simp [g, TauCeti.LFunctions.divisor_toNat_dirichletData_entireCompletion_eq χ hprim hne ρ,
        hle])
  rw [← tsum_subtype_eq_of_support_subset hsupp] at htsum
  have hcongr : (∑' ρ : {z : ℂ | 0 < z.re}, g ρ) =
      ∑' ρ : {z : ℂ | 0 < z.re}, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / (s - ρ)).re := by
    refine tsum_congr fun ρ ↦ ?_
    simp only [g,
      TauCeti.LFunctions.divisor_toNat_dirichletData_entireCompletion_eq χ hprim hne ρ,
      ite_eq_left ρ.property.out]
  linarith

/-- On `1 ≤ Re s`, for any finite set `S` in the open right half-plane `{0 < Re ρ}`, the
multiplicity-weighted zero sum is bounded by
`Re (L'/L)(s, χ) + ½ log q + Re (Γ_χ'/Γ_χ)(s)`. -/
theorem sum_analyticOrderNatAt_mul_re_one_div_sub_le_re_logDeriv_add (hprim : χ.IsPrimitive)
    (hne : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) {S : Finset ℂ} (hS : ∀ ρ ∈ S, 0 < ρ.re) :
    (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / (s - ρ)).re) ≤
      (logDeriv χ.LFunction s).re + Real.log q / 2 + (logDeriv χ.gammaFactor s).re := by
  have hs0 : 0 < s.re := zero_lt_one.trans_le hs
  have hL : χ.LFunction s ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (.inl hne) hs
  have hlog := congrArg re
    (TauCeti.LFunctions.logDeriv_dirichletData_entireCompletion χ hprim hne hs0 hL)
  simp only [add_re, div_ofNat_re, ofReal_re] at hlog
  have hsum :=
    TauCeti.LFunctions.sum_divisor_mul_re_one_div_sub_le_re_logDeriv_dirichletData_entireCompletion
      χ hprim hne hs S
  have heq : (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / (s - ρ)).re) =
      ∑ ρ ∈ S,
        ((MeromorphicOn.divisor (TauCeti.LFunctions.dirichletData χ hprim).entireCompletion
          Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re := by
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    rw [TauCeti.LFunctions.divisor_toNat_dirichletData_entireCompletion_eq χ hprim hne ρ,
      ite_eq_left (hS ρ hρ)]
  linarith

/-! ### Explicit retained-zero inequalities on `[1, 2]` -/

/-- **Infinite retained-zero inequality on `[1, 2]`.** For any nonprincipal primitive character `χ`
of conductor `q` (real or complex) and `σ ∈ [1, 2]`, the full multiplicity-weighted series over
`{0 < Re ρ}` is bounded by `Re (L'/L)(σ, χ) + ½ log q + C_Γ`. -/
theorem tsum_analyticOrderNatAt_mul_re_one_div_sub_le_logDeriv (hprim : χ.IsPrimitive)
    (hne : χ ≠ 1) {σ : ℝ} (hσ : σ ∈ Set.Icc 1 2) :
    (∑' ρ : {z : ℂ | 0 < z.re},
      (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re) ≤
      (logDeriv χ.LFunction (σ : ℂ)).re + Real.log q / 2 + TauCeti.gammaLogDerivBound := by
  have hs0 : 0 < (σ : ℂ).re := by simp only [ofReal_re]; linarith [hσ.1]
  have hL : χ.LFunction (σ : ℂ) ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (.inl hne) (by simpa using hσ.1)
  rw [← χ.re_logDeriv_LFunction_add_eq_tsum hprim hne hs0 hL]
  linarith [(le_abs_self (logDeriv χ.gammaFactor (σ : ℂ)).re).trans
    (χ.abs_re_logDeriv_gammaFactor_ofReal_le hσ)]

/-- **Finite-sum retained-zero inequality.** For any nonprincipal primitive Dirichlet character `χ`
of conductor `q` (real or complex), any finite subset `S` of the open right half-plane `0 < Re ρ`,
and any `σ ∈ [1, 2]`,
`∑_{ρ ∈ S} m_ρ Re (1 / (σ - ρ)) ≤ Re (L'/L)(σ, χ) + ½ log q + C_Γ`, where
`m_ρ = analyticOrderNatAt χ.LFunction ρ` and `C_Γ = TauCeti.gammaLogDerivBound` is fixed before
`q`, `χ`, `S`, and `σ`. Non-zeros in `S` contribute `0`, while `0 < Re ρ` excludes trivial zeros on
`Re ρ ≤ 0`. -/
theorem finite_zero_sum_le_logDeriv (hprim : χ.IsPrimitive) (hne : χ ≠ 1) {S : Finset ℂ}
    (hS : ∀ ρ ∈ S, 0 < ρ.re) {σ : ℝ} (hσ : σ ∈ Set.Icc 1 2) :
    (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re) ≤
      (logDeriv χ.LFunction (σ : ℂ)).re + Real.log q / 2 + TauCeti.gammaLogDerivBound := by
  have hsum := χ.sum_analyticOrderNatAt_mul_re_one_div_sub_le_re_logDeriv_add hprim hne
    (s := (σ : ℂ)) (by simpa using hσ.1) hS
  linarith [(le_abs_self (logDeriv χ.gammaFactor (σ : ℂ)).re).trans
    (χ.abs_re_logDeriv_gammaFactor_ofReal_le hσ)]

/-- For any finite set `S` of zeros of `L(·, χ)` in `0 < Re ρ` and any `σ ∈ [1, 2]`, keeping one
copy of each zero gives `∑_{ρ ∈ S} Re (1 / (σ - ρ)) ≤ Re (L'/L)(σ, χ) + ½ log q + C_Γ`. -/
theorem sum_re_one_div_sub_le_logDeriv (hprim : χ.IsPrimitive) (hne : χ ≠ 1) {S : Finset ℂ}
    (hS : ∀ ρ ∈ S, 0 < ρ.re ∧ χ.LFunction ρ = 0) {σ : ℝ} (hσ : σ ∈ Set.Icc 1 2) :
    (∑ ρ ∈ S, (1 / ((σ : ℂ) - ρ)).re) ≤
      (logDeriv χ.LFunction (σ : ℂ)).re + Real.log q / 2 + TauCeti.gammaLogDerivBound := by
  refine (Finset.sum_le_sum fun ρ hρ ↦ ?_).trans
    (χ.finite_zero_sum_le_logDeriv hprim hne (fun ρ hρ ↦ (hS ρ hρ).1) hσ)
  have hm : (1 : ℝ) ≤ analyticOrderNatAt χ.LFunction ρ := by
    exact_mod_cast χ.analyticOrderNatAt_LFunction_pos hne (hS ρ hρ).2
  have hre : 0 ≤ (1 / ((σ : ℂ) - ρ)).re := by
    have hlt := χ.re_lt_one_of_LFunction_eq_zero hne (hS ρ hρ).2
    rw [one_div, inv_re]
    exact div_nonneg (by rw [sub_re, ofReal_re]; linarith [hσ.1]) (normSq_nonneg _)
  simpa using mul_le_mul_of_nonneg_right hm hre

/-- For a real point `0 < β` and `σ ∈ [1, 2]`, keeping only `{β}` in
`finite_zero_sum_le_logDeriv` bounds `(analyticOrderNatAt χ.LFunction β) / (σ - β)` by
`Re (L'/L)(σ, χ) + ½ log q + C_Γ`. -/
theorem mul_one_div_sub_le_logDeriv (hprim : χ.IsPrimitive) (hne : χ ≠ 1) {β σ : ℝ}
    (hβ0 : 0 < β) (hσ : σ ∈ Set.Icc 1 2) :
    (analyticOrderNatAt χ.LFunction (β : ℂ) : ℝ) / (σ - β) ≤
      (logDeriv χ.LFunction (σ : ℂ)).re + Real.log q / 2 + TauCeti.gammaLogDerivBound := by
  have h := χ.finite_zero_sum_le_logDeriv hprim hne (S := {(β : ℂ)})
    (fun ρ hρ ↦ by simpa [Finset.mem_singleton.mp hρ] using hβ0) hσ
  have hre : (1 / ((σ : ℂ) - (β : ℂ))).re = 1 / (σ - β) := by
    rw [← ofReal_sub, ← ofReal_one, ← ofReal_div, ofReal_re]
  rw [Finset.sum_singleton, hre, mul_one_div] at h
  exact h

/-- **Single real-zero inequality.** For any nonprincipal primitive Dirichlet character `χ` of
conductor `q` (real or complex), a real zero `0 < β` of `L(·, χ)` (necessarily `β < 1`, of any
positive multiplicity), and `σ ∈ [1, 2]`,
`1 / (σ - β) ≤ Re (L'/L)(σ, χ) + ½ log q + C_Γ`. -/
theorem one_zero_le_logDeriv (hprim : χ.IsPrimitive) (hne : χ ≠ 1) {β σ : ℝ}
    (hβ0 : 0 < β) (hzero : χ.LFunction β = 0) (hσ : σ ∈ Set.Icc 1 2) :
    1 / (σ - β) ≤
      (logDeriv χ.LFunction (σ : ℂ)).re + Real.log q / 2 + TauCeti.gammaLogDerivBound := by
  have h := χ.sum_re_one_div_sub_le_logDeriv hprim hne (S := {(β : ℂ)})
    (fun ρ hρ ↦ by simpa [Finset.mem_singleton.mp hρ] using ⟨hβ0, hzero⟩) hσ
  rwa [Finset.sum_singleton, ← ofReal_sub, ← ofReal_one, ← ofReal_div, ofReal_re] at h

/-- Specialization of `one_zero_le_logDeriv` to the edge `σ = 1`:
`1 / (1 - β) ≤ Re (L'/L)(1, χ) + ½ log q + C_Γ`. -/
theorem one_zero_le_logDeriv_one (hprim : χ.IsPrimitive) (hne : χ ≠ 1) {β : ℝ}
    (hβ0 : 0 < β) (hzero : χ.LFunction β = 0) :
    1 / (1 - β) ≤
      (logDeriv χ.LFunction 1).re + Real.log q / 2 + TauCeti.gammaLogDerivBound := by
  simpa using χ.one_zero_le_logDeriv hprim hne hβ0 hzero ⟨le_rfl, by norm_num⟩

/-! ### Examples and checks -/

/-- With `S = ∅`, `finite_zero_sum_le_logDeriv` applies to every nonprincipal primitive character
(including complex characters) and yields `0 ≤ Re (L'/L)(σ, χ) + ½ log q + C_Γ` on `[1, 2]`. -/
example (hprim : χ.IsPrimitive) (hne : χ ≠ 1) {σ : ℝ} (hσ : σ ∈ Set.Icc 1 2) :
    0 ≤ (logDeriv χ.LFunction (σ : ℂ)).re + Real.log q / 2 + TauCeti.gammaLogDerivBound := by
  simpa using χ.finite_zero_sum_le_logDeriv hprim hne (S := ∅) (by simp) hσ

/-- Sign check for a complex critical-strip point `ρ = 1/2 + 14i` at `σ = 2`:
`Re (1 / (2 - ρ)) = 6 / 793 > 0`, whereas reversing the difference to `ρ - 2` flips the sign. -/
example :
    (1 / ((2 : ℂ) - (1 / 2 + 14 * I))).re = 6 / 793 ∧
      (1 / ((1 / 2 + 14 * I) - 2)).re = -(6 / 793) := by
  have hsub : (2 : ℂ) - (1 / 2 + 14 * I) = (3 / 2 : ℝ) + (-14 : ℝ) * I := by push_cast; ring
  have hrev : (1 / 2 + 14 * I : ℂ) - 2 = -((2 : ℂ) - (1 / 2 + 14 * I)) := by ring
  refine ⟨?_, ?_⟩
  · rw [hsub, one_div, inv_re, normSq_apply]
    norm_num
  · rw [hrev, one_div, inv_neg, neg_re, ← one_div, hsub, one_div, inv_re, normSq_apply]
    norm_num

/-- Multiplicity check: a real zero `0 < β` of multiplicity at least `2` contributes at least
`2 / (σ - β)`, twice the single-zero bound `1 / (σ - β)`. -/
example (hprim : χ.IsPrimitive) (hne : χ ≠ 1) {β σ : ℝ} (hβ0 : 0 < β)
    (hzero : χ.LFunction β = 0) (hmult : 2 ≤ analyticOrderNatAt χ.LFunction (β : ℂ))
    (hσ : σ ∈ Set.Icc 1 2) :
    2 / (σ - β) ≤
      (logDeriv χ.LFunction (σ : ℂ)).re + Real.log q / 2 + TauCeti.gammaLogDerivBound := by
  have hβ1 : β < 1 := by simpa using χ.re_lt_one_of_LFunction_eq_zero hne hzero
  have hm : (2 : ℝ) ≤ analyticOrderNatAt χ.LFunction (β : ℂ) := by exact_mod_cast hmult
  have hpos : 0 < σ - β := by linarith [hσ.1]
  calc 2 / (σ - β) ≤ (analyticOrderNatAt χ.LFunction (β : ℂ) : ℝ) / (σ - β) := by gcongr
    _ ≤ _ := χ.mul_one_div_sub_le_logDeriv hprim hne hβ0 hσ

end DirichletCharacter

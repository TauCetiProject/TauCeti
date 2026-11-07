/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Logarithmic derivatives of the archimedean gamma factors

Deligne's factors have logarithmic derivatives
`Γℝ'/Γℝ(s) = ψ(s/2)/2 - log(π)/2` and
`Γℂ'/Γℂ(s) = ψ(s) - log(2π)`, where `ψ = Complex.digamma`.
The identities hold away from the corresponding poles. The factor two in Mathlib's
complex-place normalization contributes no logarithmic derivative.

The logarithmic derivatives are analytic wherever the factors are nonzero. On every
compact subset of the positive half-plane they have a uniform norm bound. Taking the
complex image of `[1,3]` for the real-place factor controls both Dirichlet parity shifts
at real arguments in `[1,2]`, as needed in real-zero estimates for Dirichlet L-functions.

## References

* NIST Digital Library of Mathematical Functions, §§5.2 and 5.5.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 12.
-/

public section

namespace Complex

/-- The logarithmic derivative of the real-place gamma factor, away from its poles. -/
theorem logDeriv_Gammaℝ {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(2 * n)) :
    logDeriv Gammaℝ s = digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2 := by
  have hh : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n hn
    apply hs n
    linear_combination 2 * hn
  have hp := ((hasDerivAt_id' s).neg.div_const 2).const_cpow
    (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  simp only [Pi.neg_apply] at hp
  have hne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by simp [Real.pi_ne_zero]
  have hlog : logDeriv (fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2)) s =
      -(Real.log Real.pi : ℂ) / 2 := by
    have hg := (hasDerivAt_id' s).neg.div_const 2
    simp only [Pi.neg_apply] at hg
    rw [logDeriv_fun_comp (f := fun w : ℂ ↦ (Real.pi : ℂ) ^ w)
      (g := fun z : ℂ ↦ -z / 2)
      (by fun_prop (disch := exact Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)))
      (by fun_prop), logDeriv_const_cpow (ofReal_ne_zero.mpr Real.pi_ne_zero),
      hg.deriv, ← ofReal_log Real.pi_pos.le]
    ring
  rw [show Gammaℝ = fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2) from
    funext Gammaℝ_def]
  rw [logDeriv_fun_mul (f := fun z : ℂ ↦ (Real.pi : ℂ) ^ (-z / 2))
    (g := fun z ↦ Gamma (z / 2)) s hne (Gamma_ne_zero hh) hp.differentiableAt
    ((differentiableAt_Gamma _ hh).comp s (by fun_prop)), hlog,
    ((hasDerivAt_id' s).div_const 2).logDeriv_Gamma hh]
  ring

/-- The logarithmic derivative of the complex-place gamma factor, away from its poles. -/
theorem logDeriv_Gammaℂ {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) :
    logDeriv Gammaℂ s = digamma s - (Real.log (2 * Real.pi) : ℂ) := by
  have hb : (2 : ℂ) * Real.pi ≠ 0 := by simp [Real.pi_ne_zero]
  have hp := (hasDerivAt_id' s).neg.const_cpow (Or.inl hb)
  simp only [Pi.neg_apply] at hp
  have hne : ((2 : ℂ) * Real.pi) ^ (-s) ≠ 0 := by simp [hb]
  have hlog : logDeriv (fun z : ℂ ↦ ((2 : ℂ) * Real.pi) ^ (-z)) s =
      -(Real.log (2 * Real.pi) : ℂ) := by
    rw [logDeriv_const_cpow_neg hb]
    have hreal : Complex.log ((2 : ℂ) * Real.pi) = (Real.log (2 * Real.pi) : ℂ) := by
      rw [← ofReal_ofNat, ← ofReal_mul, ← ofReal_log (by positivity)]
    exact congrArg Neg.neg hreal
  have heq : Gammaℂ = fun z : ℂ ↦ 2 * (((2 : ℂ) * Real.pi) ^ (-z) * Gamma z) := by
    ext z
    rw [Gammaℂ_def]
    ring
  rw [heq, logDeriv_const_mul s 2 (by norm_num),
    logDeriv_fun_mul (f := fun z : ℂ ↦ ((2 : ℂ) * Real.pi) ^ (-z))
      (g := Gamma) s hne (Gamma_ne_zero hs) hp.differentiableAt
      (differentiableAt_Gamma _ hs), hlog, ← digamma_def]
  ring

/-- The logarithmic derivative is analytic off the poles of the real-place gamma factor. -/
theorem analyticAt_logDeriv_Gammaℝ {s : ℂ} (hs : Gammaℝ s ≠ 0) :
    AnalyticAt ℂ (logDeriv Gammaℝ) s := by
  have ha : AnalyticAt ℂ Gammaℝ s := by
    have h := (differentiable_Gammaℝ_inv.analyticAt s).inv (inv_ne_zero hs)
    rw [show (fun z ↦ (Gammaℝ z)⁻¹)⁻¹ = Gammaℝ from funext (fun z ↦ inv_inv _)] at h
    exact h
  exact ha.deriv.div ha hs

/-- The logarithmic derivative is analytic off the poles of the complex-place gamma factor. -/
theorem analyticAt_logDeriv_Gammaℂ {s : ℂ} (hs : Gammaℂ s ≠ 0) :
    AnalyticAt ℂ (logDeriv Gammaℂ) s := by
  have ha : AnalyticAt ℂ Gammaℂ s := by
    have h := (differentiable_Gammaℂ_inv.analyticAt s).inv (inv_ne_zero hs)
    rw [show (fun z ↦ (Gammaℂ z)⁻¹)⁻¹ = Gammaℂ from funext (fun z ↦ inv_inv _)] at h
    exact h
  exact ha.deriv.div ha hs

/-- The complex-place gamma factor is nonzero on the positive half-plane. -/
theorem Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (by simp [Real.pi_ne_zero]))
    (Gamma_ne_zero_of_re_pos hs)

/-- The real-place logarithmic derivative is continuous on the positive half-plane. -/
theorem continuousOn_logDeriv_Gammaℝ :
    ContinuousOn (logDeriv Gammaℝ) {s : ℂ | 0 < s.re} := by
  intro s hs
  exact (analyticAt_logDeriv_Gammaℝ (Gammaℝ_ne_zero_of_re_pos hs)).continuousAt.continuousWithinAt

/-- The complex-place logarithmic derivative is continuous on the positive half-plane. -/
theorem continuousOn_logDeriv_Gammaℂ :
    ContinuousOn (logDeriv Gammaℂ) {s : ℂ | 0 < s.re} := by
  intro s hs
  exact (analyticAt_logDeriv_Gammaℂ (Gammaℂ_ne_zero_of_re_pos hs)).continuousAt.continuousWithinAt

/-- The real-place logarithmic derivative is bounded on compact subsets of the
positive half-plane. -/
theorem exists_norm_logDeriv_Gammaℝ_le (K : Set ℂ) (hK : IsCompact K)
    (hKre : K ⊆ {s : ℂ | 0 < s.re}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ‖logDeriv Gammaℝ s‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuousOn_logDeriv_Gammaℝ.mono hKre)
  exact ⟨max C 0, le_max_right _ _, fun s hs ↦ (hC s hs).trans (le_max_left _ _)⟩

/-- The complex-place logarithmic derivative is bounded on compact subsets of the
positive half-plane. -/
theorem exists_norm_logDeriv_Gammaℂ_le (K : Set ℂ) (hK : IsCompact K)
    (hKre : K ⊆ {s : ℂ | 0 < s.re}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ‖logDeriv Gammaℂ s‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuousOn_logDeriv_Gammaℂ.mono hKre)
  exact ⟨max C 0, le_max_right _ _, fun s hs ↦ (hC s hs).trans (le_max_left _ _)⟩

end Complex

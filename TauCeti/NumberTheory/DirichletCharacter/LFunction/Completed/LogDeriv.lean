/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.Basic

/-!
# Logarithmic derivatives of completed Dirichlet L-functions

The archimedean factor of a Dirichlet character `χ` has the logarithmic derivative of `Γℝ` at
`s + a`, where `a` is `0` for even and `1` for odd characters; off its poles this is
`ψ((s + a)/2)/2 − ½ log π`. On each compact subset of the positive half-plane these logarithmic
derivatives are bounded by one constant for all characters of all moduli.

On the positive half-plane, away from the zeros of `L(χ, ·)`, the logarithmic derivative of
Mathlib's completed function `Λ(χ, s)` is the sum of those of the archimedean factor and of
`L(χ, s)`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §10.2.
-/

public section

open Complex Filter Topology

namespace DirichletCharacter

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

/-- The archimedean factor of an even character has the real-place logarithmic derivative. -/
theorem Even.logDeriv_gammaFactor {χ : DirichletCharacter ℂ N} (he : χ.Even) (s : ℂ) :
    logDeriv χ.gammaFactor s = logDeriv Gammaℝ s := by
  rw [show χ.gammaFactor = Gammaℝ from funext he.gammaFactor_def]

/-- The archimedean factor of an odd character has the shifted real-place logarithmic
derivative. -/
theorem Odd.logDeriv_gammaFactor {χ : DirichletCharacter ℂ N} (ho : χ.Odd) (s : ℂ) :
    logDeriv χ.gammaFactor s = logDeriv Gammaℝ (s + 1) := by
  rw [show χ.gammaFactor = fun z ↦ Gammaℝ (z + 1) from funext ho.gammaFactor_def,
    logDeriv_apply, logDeriv_apply, deriv_comp_add_const]

open scoped Classical in
/-- The logarithmic derivative of the archimedean factor is that of `Γℝ` at the parity shift. -/
theorem logDeriv_gammaFactor (s : ℂ) :
    logDeriv χ.gammaFactor s = logDeriv Gammaℝ (s + if χ.Even then 0 else 1) := by
  rcases χ.even_or_odd with he | ho
  · rw [he.logDeriv_gammaFactor, ite_eq_left he, add_zero]
  · rw [ho.logDeriv_gammaFactor, ite_eq_right ho.not_even]

open scoped Classical in
/-- Off its poles, the logarithmic derivative of the archimedean factor is a digamma value. -/
theorem logDeriv_gammaFactor_eq_digamma {s : ℂ} (hs : χ.gammaFactor s ≠ 0) :
    logDeriv χ.gammaFactor s =
      digamma ((s + if χ.Even then 0 else 1) / 2) / 2 - (Real.log Real.pi : ℂ) / 2 := by
  rw [χ.logDeriv_gammaFactor]
  refine logDeriv_Gammaℝ fun n hn ↦ hs ?_
  rcases χ.even_or_odd with he | ho
  · rw [ite_eq_left he, add_zero] at hn
    exact (gammaFactor_eq_zero_iff_of_even he).mpr ⟨n, hn⟩
  · rw [ite_eq_right ho.not_even] at hn
    exact (gammaFactor_eq_zero_iff_of_odd ho).mpr ⟨n, hn⟩

/-- On every compact subset of the positive half-plane, the logarithmic derivatives of the
archimedean factors of all Dirichlet characters are bounded by one constant. -/
theorem exists_norm_logDeriv_gammaFactor_le (K : Set ℂ) (hK : IsCompact K)
    (hKre : K ⊆ {s : ℂ | 0 < s.re}) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ} (χ : DirichletCharacter ℂ N), ∀ s ∈ K,
      ‖logDeriv χ.gammaFactor s‖ ≤ C := by
  have hK' : IsCompact (K ∪ (· + 1) '' K) := hK.union (hK.image (by fun_prop))
  obtain ⟨C, hC0, hC⟩ := exists_norm_logDeriv_Gammaℝ_le _ hK' <| by
    rintro z (hz | ⟨w, hw, rfl⟩)
    · exact hKre hz
    · have := (hKre hw).out
      simp only [Set.mem_ofPred_eq, add_re, one_re]
      linarith
  refine ⟨C, hC0, fun χ s hs ↦ ?_⟩
  rcases χ.even_or_odd with he | ho
  · rw [he.logDeriv_gammaFactor]
    exact hC s (.inl hs)
  · rw [ho.logDeriv_gammaFactor]
    exact hC (s + 1) (.inr ⟨s, hs, rfl⟩)

variable [NeZero N]

/-- On the positive half-plane, away from the zeros of `L(χ, ·)`, the logarithmic derivative of
the completed function splits into its archimedean and Dirichlet-series parts. -/
theorem logDeriv_completedLFunction {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1 ∨ χ ≠ 1)
    (hL : χ.LFunction s ≠ 0) :
    logDeriv χ.completedLFunction s = logDeriv χ.gammaFactor s + logDeriv χ.LFunction s := by
  have he : χ.completedLFunction =ᶠ[𝓝 s] χ.gammaFactor * χ.LFunction := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    rw [Pi.mul_apply, χ.LFunction_eq_completed_div_gammaFactor z
      (.inl fun h ↦ by simp [h] at hz), mul_div_cancel₀ _ (χ.gammaFactor_ne_zero_of_re_pos hz)]
  rw [(logDeriv_congr_nhds he).eq_of_nhds]
  exact logDeriv_mul s (χ.gammaFactor_ne_zero_of_re_pos hs) hL
    (χ.analyticAt_gammaFactor_of_re_pos hs).differentiableAt
    (χ.differentiableAt_LFunction s hs₁)

end DirichletCharacter

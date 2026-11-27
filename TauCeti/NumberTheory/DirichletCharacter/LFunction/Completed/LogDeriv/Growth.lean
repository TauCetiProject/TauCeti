/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.LogDeriv
import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv.VerticalStrip

/-!
# Growth of Dirichlet gamma logarithmic derivatives

The logarithmic derivative of the gamma factor in a completed Dirichlet L-function has
logarithmic growth on the strip used for horizontal contours, uniformly in the parity.
-/

public section

open Complex

namespace DirichletCharacter

/-- On `-1 ≤ Re s ≤ 2` at heights of absolute value at least `1/2`, the logarithmic derivative
of the parity-dependent gamma factor is bounded by an absolute constant times
`log (|Im s| + 2)`. -/
theorem exists_norm_logDeriv_gammaFactor_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) (s : ℂ),
      s.re ∈ Set.Icc (-1) 2 → 1 / 2 ≤ |s.im| →
      ‖logDeriv χ.gammaFactor s‖ ≤ C * Real.log (|s.im| + 2) := by
  obtain ⟨C, hC, hΓ⟩ := exists_norm_logDeriv_Gammaℝ_le_log
  refine ⟨C, hC, fun {_} χ s hs him ↦ ?_⟩
  rcases χ.even_or_odd with he | ho
  · rw [he.logDeriv_gammaFactor]
    exact hΓ s ⟨hs.1, hs.2.trans (by norm_num)⟩ him
  · rw [ho.logDeriv_gammaFactor]
    have hs' : (s + 1).re ∈ Set.Icc (-1) 3 := by
      simp only [Set.mem_Icc, add_re, one_re]
      constructor <;> linarith [hs.1, hs.2]
    simpa using hΓ (s + 1) hs' (by simpa using him)

end DirichletCharacter

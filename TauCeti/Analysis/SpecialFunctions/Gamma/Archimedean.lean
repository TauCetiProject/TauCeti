/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Zero values of the complex archimedean gamma factor

Mathlib uses total division for the gamma function, so the archimedean factor `Gammaℂ`
has value zero at the nonpositive integers. These are poles of its meromorphic germ.
This characterization complements `Complex.Gammaℝ_eq_zero_iff` for the real factor and
identifies the exceptional values in finite products of shifted gamma factors.
-/

public section

namespace Complex

/-- The total zero values of the complex archimedean factor occur at the nonpositive integers. -/
theorem Gammaℂ_eq_zero_iff (z : ℂ) : Gammaℂ z = 0 ↔ ∃ n : ℕ, z = -(n : ℂ) := by
  simp [Gammaℂ_def, Real.pi_ne_zero, Gamma_eq_zero_iff]

end Complex

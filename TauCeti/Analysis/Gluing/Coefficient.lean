/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# The glued coefficient

Gluing the positive end of a coefficient `A₁ : ℝ → X` to the negative end of `A₂ : ℝ → X` along a
neck of length `2 R` gives the coefficient `TauCeti.gluedCoeff A₁ A₂ R`, equal to `A₁ (s + R)` for
`s < 0` and to `A₂ (s - R)` for `s ≥ 0`. With translation by `a` meaning `f ↦ f (· + a)`, it is
`A₁` translated by `R` on `(-∞, 0)` and `A₂` translated by `-R` on `[0, ∞)`. It is the coefficient
of the glued operators in `TauCeti.Analysis.ODE.TrajectoryOperator.Gluing` and
`TauCeti.Analysis.Sobolev.Cylinder.Glued.Basic`, whose right inverses are spliced with the neck
cutoffs `TauCeti.neckCutoff`.

## Main declarations

* `TauCeti.gluedCoeff`: the coefficient of two operators glued along a neck of length `2 R`.
* `TauCeti.gluedCoeff_of_neg` and `TauCeti.gluedCoeff_of_nonneg`: its values on the two
  half-lines.
-/

public section

noncomputable section

namespace TauCeti

/-- **The glued coefficient.** The coefficient obtained by gluing the positive end of `A₁` to the
negative end of `A₂` along a neck of length `2 R`: it is `A₁` translated by `R`, that is
`A₁ (· + R)`, on `(-∞, 0)` and `A₂` translated by `-R`, that is `A₂ (· - R)`, on `[0, ∞)`. -/
def gluedCoeff {X : Type*} (A₁ A₂ : ℝ → X) (R s : ℝ) : X :=
  if s < 0 then A₁ (s + R) else A₂ (s - R)

/-- The glued coefficient is `A₁` translated by `R` on `(-∞, 0)`. -/
theorem gluedCoeff_of_neg {X : Type*} (A₁ A₂ : ℝ → X) (R : ℝ) {s : ℝ} (hs : s < 0) :
    gluedCoeff A₁ A₂ R s = A₁ (s + R) := by
  simp [gluedCoeff, hs]

/-- The glued coefficient is `A₂` translated by `-R` on `[0, ∞)`. -/
theorem gluedCoeff_of_nonneg {X : Type*} (A₁ A₂ : ℝ → X) (R : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    gluedCoeff A₁ A₂ R s = A₂ (s - R) := by
  simp [gluedCoeff, not_lt.2 hs]

end TauCeti

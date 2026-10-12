/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Exponential bounds on the upper half-plane

An exponential growth bound with real rate `k` at `i∞` remains valid after increasing `k`. This
monotonicity feeds the independence of a cusp Laurent expansion from the chosen growth bound.

-/

public section

open UpperHalfPlane

namespace TauCeti.UpperHalfPlane

/-- An exponential growth bound at `i∞` remains valid after increasing its real rate. -/
theorem isBigO_exp_of_le {E : Type*} [NormedAddCommGroup E]
    (w : ℝ) (hw : 0 < w) {k k' : ℝ} (hkk' : k ≤ k') {f : ℍ → E}
    (hf : f =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * k * z.im / w)) :
    f =O[atImInfty] fun z ↦ Real.exp (2 * Real.pi * k' * z.im / w) := by
  refine hf.trans (Asymptotics.isBigO_of_le _ fun z ↦ ?_)
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  gcongr

end TauCeti.UpperHalfPlane

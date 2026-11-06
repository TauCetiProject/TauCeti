/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smoothness of the complex phase

Away from the origin the norm of a complex number is a real-smooth function, so the phase
`w / ‖w‖` and its powers `(w / ‖w‖) ^ m` are real-smooth there
(`Complex.contDiffAt_div_norm_pow`). The powers are the winding phases of degree `m`, which have
unit modulus and are homogeneous of degree `0`.
-/

public section

namespace Complex

/-- The winding phase `(w / ‖w‖) ^ m` is real-smooth away from the origin. -/
theorem contDiffAt_div_norm_pow {n : WithTop ℕ∞} (m : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ n (fun w : ℂ ↦ (w / (‖w‖ : ℂ)) ^ m) z := by
  have hn : ContDiffAt ℝ n (fun w : ℂ ↦ (‖w‖ : ℂ)) z :=
    ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_norm ℂ hz)
  have hp : ContDiffAt ℝ n (fun w : ℂ ↦ w / (‖w‖ : ℂ)) z := by
    simpa only [div_eq_mul_inv, Pi.inv_apply, id_eq] using
      contDiffAt_id.mul (hn.inv (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)))
  exact hp.pow m

end Complex

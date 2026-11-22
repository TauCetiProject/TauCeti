/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Norm inequalities for Birkhoff averages

Elementary pointwise norm bounds for the Birkhoff averages `birkhoffAverage ℝ T f n` of an
observable `f : Ω → E` taking values in a real seminormed space, requiring no measure theory.

## Main results

* `TauCeti.norm_birkhoffAverage_le_birkhoffAverage_norm` — triangle inequality for Birkhoff
  averages: `‖birkhoffAverage ℝ T f n x‖ ≤ birkhoffAverage ℝ T (‖f ·‖) n x`.
-/

public section

namespace TauCeti

/-- The norm of a Birkhoff average is bounded by the Birkhoff average of the norms. -/
theorem norm_birkhoffAverage_le_birkhoffAverage_norm {Ω E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (T : Ω → Ω) (f : Ω → E) (n : ℕ) (x : Ω) :
    ‖birkhoffAverage ℝ T f n x‖ ≤ birkhoffAverage ℝ T (fun y ↦ ‖f y‖) n x := by
  simp only [birkhoffAverage, birkhoffSum, norm_smul, Real.norm_eq_abs, abs_inv,
    Nat.abs_cast, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

end TauCeti

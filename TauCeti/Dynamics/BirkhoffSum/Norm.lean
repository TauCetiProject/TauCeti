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
* `TauCeti.norm_birkhoffAverage_le_of_forall_norm_le` — a uniform pointwise norm bound
  `∀ x, ‖f x‖ ≤ C` transfers to every Birkhoff average `birkhoffAverage ℝ T f n x`.
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

/-- If an observable is pointwise bounded in norm by `C`, then so are all its Birkhoff averages. -/
theorem norm_birkhoffAverage_le_of_forall_norm_le {Ω E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {T : Ω → Ω} {f : Ω → E} {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C)
    (n : ℕ) (x : Ω) :
    ‖birkhoffAverage ℝ T f n x‖ ≤ C := by
  calc
    ‖birkhoffAverage ℝ T f n x‖ ≤ birkhoffAverage ℝ T (fun y ↦ ‖f y‖) n x :=
      norm_birkhoffAverage_le_birkhoffAverage_norm T f n x
    _ ≤ C := by
      rcases eq_or_ne n 0 with rfl | hn
      · simpa using (norm_nonneg (f x)).trans (hC x)
      · have hconst : birkhoffAverage ℝ T (fun _ ↦ C) n x = C :=
          congrFun (birkhoffAverage_const ℝ T C (Nat.cast_ne_zero.mpr hn)) x
        rw [← hconst]
        simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ hC (T^[k] x)) (by positivity)

end TauCeti

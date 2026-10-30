/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Int

/-!
# The sup norm of an integer vector

The norm on `ℤ` is the restriction of the norm on `ℝ` (`Int.norm_cast_real`). Coordinatewise, the
sup norm of an integer vector `z : ι → ℤ` is the sup norm of the real vector with the same
coordinates (`TauCeti.pi_norm_intCast_real`).
-/

public section

namespace TauCeti

/-- The sup norm of an integer vector is the sup norm of its cast to a real vector. -/
theorem pi_norm_intCast_real {ι : Type*} [Fintype ι] (z : ι → ℤ) :
    ‖fun i ↦ (z i : ℝ)‖ = ‖z‖ :=
  le_antisymm
    ((pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun i ↦
      (Int.norm_cast_real (z i)).trans_le (norm_le_pi_norm z i))
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i ↦
      (Int.norm_cast_real (z i)).symm.trans_le (norm_le_pi_norm (fun i ↦ (z i : ℝ)) i))

end TauCeti

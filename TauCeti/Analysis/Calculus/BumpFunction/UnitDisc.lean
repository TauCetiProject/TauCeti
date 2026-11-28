/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Complex.Basic

/-!
# A smooth cutoff of the unit disc in `ℂ`

The smooth bump function `TauCeti.unitDiscCutoff` on `ℂ`, centred at `0`, is equal to `1` on the
closed unit disc and to `0` outside the open disc of radius `2`
(`TauCeti.unitDiscCutoff_of_norm_le_one`, `TauCeti.unitDiscCutoff_of_two_le_norm`); its
topological support is the closed disc of radius `2` (`ContDiffBump.tsupport_eq` together with
`TauCeti.unitDiscCutoff_rOut`).
-/

public noncomputable section

namespace TauCeti

/-- A smooth cutoff on `ℂ`, equal to `1` on the closed unit disc and to `0` outside the open
disc of radius `2`. -/
def unitDiscCutoff : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cutoff `TauCeti.unitDiscCutoff` equals `1` on the closed disc of radius `1`. -/
@[simp]
theorem unitDiscCutoff_rIn : unitDiscCutoff.rIn = 1 := (rfl)

/-- The cutoff `TauCeti.unitDiscCutoff` is supported in the closed disc of radius `2`. -/
@[simp]
theorem unitDiscCutoff_rOut : unitDiscCutoff.rOut = 2 := (rfl)

/-- The cutoff `TauCeti.unitDiscCutoff` equals `1` on the closed unit disc. -/
@[simp]
theorem unitDiscCutoff_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) : unitDiscCutoff z = 1 :=
  unitDiscCutoff.one_of_mem_closedBall (by simpa using hz)

/-- The cutoff `TauCeti.unitDiscCutoff` vanishes outside the open disc of radius `2`. -/
@[simp]
theorem unitDiscCutoff_of_two_le_norm {z : ℂ} (hz : 2 ≤ ‖z‖) : unitDiscCutoff z = 0 :=
  unitDiscCutoff.zero_of_le_dist (by simpa using hz)

end TauCeti

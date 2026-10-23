/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Basic.Real.Basic
import TauCeti.Combinatorics.Network.Coefficients

/-!
# Examples of bounded assignments

Take two vertices `false` and `true`, with one arrow for each ordered pair, including the two
loops, lower bound `-2` and upper bound `1` on every arrow. The integral assignment with value
`-1` on the arrow from `false` to `true` and zero elsewhere is a bounded `false`–`true` assignment
of negative value `-1`; conservation is vacuous because both vertices are terminals. Casting its
coefficients from `ℤ` to `ℝ` gives a real bounded assignment for the cast bounds, of value `-1`.
-/

namespace TauCeti

-- An integral bounded assignment with negative bounds and negative value, carried to `ℝ`.
example :
    let lo : Assignment (fun _ _ : Bool ↦ Unit) ℤ := fun _ _ _ ↦ -2
    let hi : Assignment (fun _ _ : Bool ↦ Unit) ℤ := fun _ _ _ ↦ 1
    let φ : ℤ →+o ℝ :=
      { toFun := Int.cast
        map_zero' := Int.cast_zero
        map_add' := Int.cast_add
        monotone' := Int.cast_mono }
    ∃ f : BoundedFlow lo hi false true, f.val = -1 ∧ (f.map φ).val = -1 ∧
      (f.map φ).toFun (x := false) (y := true) () = -1 := by
  intro lo hi φ
  refine ⟨⟨fun a b _ ↦ if a = false ∧ b = true then -1 else 0, ⟨?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · intro a b _
    simp only [lo]
    split_ifs <;> norm_num
  · intro a b _
    simp only [hi]
    split_ifs <;> norm_num
  · intro v hvs hvt
    cases v <;> simp_all
  · simp [BoundedFlow.val_def, excessAt_def]
  · simp [BoundedFlow.val_def, excessAt_def, φ]
  · simp [φ]

end TauCeti

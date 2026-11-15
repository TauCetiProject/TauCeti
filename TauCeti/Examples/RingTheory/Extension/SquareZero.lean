/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import TauCeti.RingTheory.Extension.SquareZero.Basic

/-!
# A nonsplit square-zero extension

The extension `ℤ/4 → ℤ/2` of `ℤ/2` by `ℤ/2` over `ℤ`, with kernel `2ℤ/4ℤ`, does not split, since
there is no ring map `ℤ/2 → ℤ/4`. Its class in `Exal_ℤ(ℤ/2, ℤ/2)` is therefore nonzero.

## Main results

* `TauCeti.SquareZeroExtension.zmodFour_extensionClass_ne_zero`: the extension `ℤ/4 → ℤ/2` has
  a nonzero class.
-/

public section

namespace TauCeti

namespace SquareZeroExtension

/-- The square-zero extension `ℤ/4 → ℤ/2` of `ℤ/2` by `ℤ/2` over `ℤ`, whose kernel `2ℤ/4ℤ` is
identified with `ℤ/2` by `m ↦ 2m`. -/
@[expose] def zmodFour : SquareZeroExtension.{0} ℤ (ZMod 2) (ZMod 2) where
  Ring := ZMod 4
  π := (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)).toIntAlgHom
  π_surjective := by decide
  ι := AddMonoidHom.mk' (fun m ↦ 2 * (m.val : ZMod 4)) (by decide)
  ι_injective := by decide
  exact y := by
    rw [Set.mem_range]
    revert y
    decide
  mul_ι := by decide

/-- The extension `ℤ/4 → ℤ/2` does not split: there is no ring map `ℤ/2 → ℤ/4`. -/
theorem isEmpty_splitting_zmodFour : IsEmpty zmodFour.Splitting := by
  refine ⟨fun s ↦ ?_⟩
  have h := map_add s.toAlgHom 1 1
  rw [(by decide : (1 + 1 : ZMod 2) = 0), map_zero, map_one] at h
  exact absurd h (by decide : (0 : ZMod 4) ≠ 1 + 1)

/-- The extension `ℤ/4 → ℤ/2` has a nonzero class in `Exal_ℤ(ℤ/2, ℤ/2)`. -/
theorem zmodFour_extensionClass_ne_zero : zmodFour.extensionClass ≠ 0 := by
  rw [Ne, extensionClass_eq_zero_iff, not_nonempty_iff]
  exact isEmpty_splitting_zmodFour

end SquareZeroExtension

end TauCeti

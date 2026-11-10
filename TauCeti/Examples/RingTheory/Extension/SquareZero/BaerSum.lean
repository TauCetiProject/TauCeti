/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RingTheory.Extension.SquareZero
public import TauCeti.RingTheory.Extension.SquareZero.BaerSum

/-!
# The Baer sum of two copies of `ℤ/4 → ℤ/2`

The extension `ℤ/4 → ℤ/2` of `ℤ/2` by `ℤ/2` over `ℤ` has a nonzero class in `Exal_ℤ(ℤ/2, ℤ/2)`,
but the Baer sum of two copies of it splits. Indeed its kernel inclusion `m ↦ 2m` agrees with its
negative in `ℤ/4`, so the extension is isomorphic to its negative and its class has order two.
Without the quotient by the antidiagonal, the fibre product `ℤ/4 ×_{ℤ/2} ℤ/4` alone would still
contain `(1, 1)` of additive order four.

## Main results

* `TauCeti.SquareZeroExtension.zmodFour_extensionClass_add_self`: twice the class of `ℤ/4 → ℤ/2`
  is zero.
* `TauCeti.SquareZeroExtension.nonempty_splitting_baerSum_zmodFour`: the Baer sum of two copies of
  `ℤ/4 → ℤ/2` splits.
-/

public section

namespace TauCeti

namespace SquareZeroExtension

/-- The extension `ℤ/4 → ℤ/2` is isomorphic to its negative, since `-2m = 2m` in `ℤ/4`. -/
def zmodFourToNeg : zmodFour ⟶ neg zmodFour where
  toAlgHom := AlgHom.id ℤ (ZMod 4)
  π_toAlgHom _ := rfl
  -- Both sides unfold to the values `2m` and `-2m` in `ℤ/4` of the kernel inclusion of
  -- `zmodFour`, which agree for each of the two elements `m` of `ℤ/2`.
  toAlgHom_ι := (by decide : ∀ m : ZMod 2, 2 * (m.val : ZMod 4) = -(2 * (m.val : ZMod 4)))

/-- Twice the class of `ℤ/4 → ℤ/2` in `Exal_ℤ(ℤ/2, ℤ/2)` is zero, although the class itself is
nonzero (`TauCeti.SquareZeroExtension.zmodFour_extensionClass_ne_zero`). -/
theorem zmodFour_extensionClass_add_self :
    zmodFour.extensionClass + zmodFour.extensionClass = 0 := by
  nth_rw 1 [extensionClass_eq_extensionClass_iff.2 ⟨zmodFourToNeg⟩]
  rw [extensionClass_neg, neg_add_cancel]

/-- The Baer sum of two copies of `ℤ/4 → ℤ/2` splits. -/
theorem nonempty_splitting_baerSum_zmodFour : Nonempty (baerSum zmodFour zmodFour).Splitting := by
  rw [← extensionClass_eq_zero_iff, extensionClass_baerSum, zmodFour_extensionClass_add_self]

end SquareZeroExtension

end TauCeti

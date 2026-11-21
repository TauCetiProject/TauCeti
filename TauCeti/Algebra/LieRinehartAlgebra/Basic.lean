/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.LieRinehartAlgebra.Defs

/-!
# Basic properties of Lie–Rinehart rings

Basic identities for `LieRinehartRing` complementing `Mathlib.Algebra.LieRinehartAlgebra.Defs`.

## References

* G. S. Rinehart, *Differential forms on general commutative algebras*, Trans. Amer. Math. Soc.
  108 (1963), 195–222, §2.
-/

public section

namespace LieRinehartRing

/-- The Leibniz rule in the first slot of the Lie bracket of a Lie–Rinehart ring:
`⁅a • x, y⁆ = a • ⁅x, y⁆ - ⁅y, a⁆ • x`. -/
theorem leibniz_smul_left {A L : Type*} [CommRing A] [LieRing L] [Module A L]
    [LieRingModule L A] [LieRinehartRing A L] (a : A) (x y : L) :
    ⁅a • x, y⁆ = a • ⁅x, y⁆ - ⁅y, a⁆ • x := by
  rw [← lie_skew (a • x) y, LieRinehartRing.leibniz_smul_right, neg_add, ← smul_neg,
    lie_skew x y, sub_eq_add_neg]

end LieRinehartRing

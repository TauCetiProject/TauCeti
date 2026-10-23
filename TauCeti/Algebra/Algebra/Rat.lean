/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat

/-!
# Rational algebras from ring homomorphisms

The image of a ring homomorphism `ℚ →+* B` is central, because every rational number is a
quotient of integers and integer casts commute with everything. Hence such a homomorphism
makes `B` a `ℚ`-algebra, even when `B` is not commutative. This is used, for instance, to view
the target of a ring homomorphism out of a `ℚ`-algebra as a `ℚ`-algebra.

## Main declarations

* `RingHom.commute_apply_rat`: the image of a rational number commutes with every element.
* `RingHom.toRatAlgebra`: the `ℚ`-algebra structure induced by a ring homomorphism `ℚ →+* B`.
* `RingHom.algebraMap_toRatAlgebra`: its algebra map is the given homomorphism.
-/

public section

namespace RingHom

variable {B : Type*} [Ring B]

/-- The image of a rational number under a ring homomorphism is central. -/
theorem commute_apply_rat (g : ℚ →+* B) (q : ℚ) (y : B) : Commute (g q) y := by
  let u : ℚˣ := Units.mk0 (q.den : ℚ) (Nat.cast_ne_zero.mpr q.den_nz)
  have hu : Commute (↑(Units.map (g : ℚ →* B) u)⁻¹ : B) y :=
    Commute.units_inv_left (by simpa [u] using Nat.cast_commute q.den y)
  rw [← Rat.num_div_den q, div_eq_mul_inv, map_mul, map_intCast]
  exact (Int.cast_commute q.num y).mul_left (by simpa [u] using hu)

/-- A ring homomorphism `ℚ →+* B` makes `B` a `ℚ`-algebra, since its image is central.
See note [reducible non-instances]. -/
abbrev toRatAlgebra (g : ℚ →+* B) : Algebra ℚ B :=
  g.toAlgebra' fun q y ↦ (g.commute_apply_rat q y).eq

/-- The algebra map of `RingHom.toRatAlgebra g` is `g`. -/
theorem algebraMap_toRatAlgebra (g : ℚ →+* B) :
    @algebraMap ℚ B _ _ g.toRatAlgebra = g :=
  rfl

end RingHom

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ComplexShapeSigns

/-!
# Computations for additive total-complex shapes

The total-complex shape induced by tensor signs adds the two input indices.
This characteristic equation is independent of the category or bifunctor
used to form a total complex.

The instance `HomologicalComplex₂.totalComplexShapeSymmetryDownNat` identifies the total
complexes of a first-quadrant bicomplex and of its flip by the Koszul sign `(-1)^(p*q)` in
bidegree `(p, q)`. It is the natural-number analogue of Mathlib's `TotalComplexShapeSymmetry`
instance for cochain complexes indexed by `ℤ`, and adapts its sign calculation.
-/

public section

namespace ComplexShape

/-- The additive total-complex shape sends a pair of indices to their sum. -/
@[simp]
theorem π_eq_add {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns]
    (p q : I) : π c c c (p, q) = p + q := by
  -- This is the index component of the additive total-complex-shape instance.
  rfl

end ComplexShape

namespace HomologicalComplex₂

/-- The total complexes of a first-quadrant bicomplex and its flip are identified by the Koszul
sign `(-1)^(p*q)` on the term in bidegree `(p, q)`. -/
instance totalComplexShapeSymmetryDownNat :
    TotalComplexShapeSymmetry (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) where
  symm p q := Nat.add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    rintro p _ rfl q
    dsimp
    rw [mul_one, Nat.add_mul, one_mul, pow_add]
    ac_rfl
  σ_ε₂ := by
    rintro p q _ rfl
    dsimp
    rw [one_mul, Nat.mul_add, Nat.mul_one, pow_add, mul_assoc, Int.units_mul_self, mul_one]

end HomologicalComplex₂

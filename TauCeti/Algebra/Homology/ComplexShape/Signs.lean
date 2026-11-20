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

Tensor signs on a complex shape `c` are also tensor signs on the opposite shape `c.symm`, with the
same signs, and a `TotalComplexShapeSymmetry c c c` gives one for `c.symm` with the same signs
`σ`. Bicomplexes with values in an opposite category have the opposite shapes, so these instances
equip them with total complexes and their symmetries.
-/

public section

namespace ComplexShape

/-- The additive total-complex shape sends a pair of indices to their sum. -/
@[simp]
theorem π_eq_add {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns]
    (p q : I) : π c c c (p, q) = p + q := by
  -- This is the index component of the additive total-complex-shape instance.
  rfl

section Symm

variable {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns]

/-- The tensor signs of a complex shape are tensor signs for the opposite shape. -/
instance tensorSignsSymm : c.symm.TensorSigns where
  ε' := TensorSigns.ε' c
  rel_add _ _ r hpq := c.rel_add hpq r
  add_rel _ _ r hpq := c.add_rel r hpq
  ε'_succ _ _ hpq := (neg_eq_iff_eq_neg.mpr (c.ε_succ hpq)).symm

@[simp]
lemma ε_symm (p : I) : c.symm.ε p = c.ε p := rfl

/-- A symmetry of the total complex shape `c, c, c` is also one of `c.symm, c.symm, c.symm`,
with the same signs. -/
instance totalComplexShapeSymmetrySymm [TotalComplexShapeSymmetry c c c] :
    TotalComplexShapeSymmetry c.symm c.symm c.symm where
  symm p q := π_symm c c c p q
  σ := σ c c c
  -- A relation `c.symm.Rel p p'` is by definition the relation `c.Rel p' p`.
  σ_ε₁ {p p'} h q := by
    have := σ_ε₁ c c (c₁ := c) (show c.Rel p' p from h) q
    simp only [ε₁_def, mul_one, ε₂_def, ε_symm] at this ⊢
    rw [this, ← mul_assoc, Int.units_mul_self, one_mul]
  σ_ε₂ p {q q'} h := by
    have := σ_ε₂ c c p (show c.Rel q' q from h)
    simp only [ε₂_def, ε₁_def, one_mul, ε_symm] at this ⊢
    rw [← this, mul_assoc, Int.units_mul_self, mul_one]

@[simp]
lemma σ_symm_symm_symm [TotalComplexShapeSymmetry c c c] (p q : I) :
    σ c.symm c.symm c.symm p q = σ c c c p q := rfl

end Symm

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

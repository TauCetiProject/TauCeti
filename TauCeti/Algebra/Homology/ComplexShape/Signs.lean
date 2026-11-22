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

Mathlib supplies tensor signs for `ComplexShape.down ℕ` and `ComplexShape.up ℤ`; the instance
`ComplexShape.instTensorSignsDownInt` supplies the sign `ε p = (-1)^p` on `ComplexShape.down ℤ`, so
that chain complexes indexed by `ℤ`, such as Floer complexes graded by an index, have tensor
products with the Koszul differential `d (x ⊗ y) = d x ⊗ y + (-1)^p x ⊗ d y`.

The instance `HomologicalComplex₂.totalComplexShapeSymmetryDownNat` identifies the total
complexes of a first-quadrant bicomplex and of its flip by the Koszul sign `(-1)^(p*q)` in
bidegree `(p, q)`. It is the natural-number analogue of Mathlib's `TotalComplexShapeSymmetry`
instance for cochain complexes indexed by `ℤ`, and adapts its sign calculation. The instances
`HomologicalComplex₂.totalComplexShapeSymmetrySymmetryDownNat` and
`HomologicalComplex₂.totalComplexShapeSymmetrySymmetryUpInt` record that both signs are symmetric
in the two factors (`TotalComplexShapeSymmetrySymmetry`), as the Koszul braiding of
`TauCeti/Algebra/Homology/Monoidal/Braiding.lean` needs for its inverse and symmetry laws.
-/

public section

namespace ComplexShape

/-- The additive total-complex shape sends a pair of indices to their sum. -/
@[simp]
theorem π_eq_add {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns]
    (p q : I) : π c c c (p, q) = p + q := by
  -- This is the index component of the additive total-complex-shape instance.
  rfl

/-- Chain complexes indexed by `ℤ` carry the tensor signs `ε p = (-1)^p`, as cochain complexes
indexed by `ℤ` do in Mathlib. -/
instance instTensorSignsDownInt : TensorSigns (ComplexShape.down ℤ) where
  ε' :=
    { toFun n := n.toAdd.negOnePow
      map_one' := by simp
      map_mul' a b := by simp [Int.negOnePow_add] }
  rel_add p q r hpq := by simp only [down_Rel] at hpq ⊢; omega
  add_rel p q r hpq := by simp only [down_Rel] at hpq ⊢; omega
  ε'_succ := by
    rintro _ q rfl
    -- Unfold `Multiplicative.toAdd` from the `toFun` of `ε'` so that `Int.negOnePow_succ` can
    -- rewrite the goal.
    change q.negOnePow = -(q + 1).negOnePow
    rw [Int.negOnePow_succ, neg_neg]

@[simp]
theorem ε_down_ℤ (n : ℤ) : (ComplexShape.down ℤ).ε n = n.negOnePow := rfl

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

/-- The Koszul sign `(-1)^(p*q)` of `HomologicalComplex₂.totalComplexShapeSymmetryDownNat` is
symmetric in the two factors. -/
instance totalComplexShapeSymmetrySymmetryDownNat :
    TotalComplexShapeSymmetrySymmetry (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) where
  σ_symm p q := by
    change (-1 : ℤˣ) ^ (q * p) = (-1 : ℤˣ) ^ (p * q)
    rw [Nat.mul_comm]

/-- The Koszul sign `(p * q).negOnePow` of Mathlib's `TotalComplexShapeSymmetry` instance for
cochain complexes indexed by `ℤ` is symmetric in the two factors. -/
instance totalComplexShapeSymmetrySymmetryUpInt :
    TotalComplexShapeSymmetrySymmetry (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) where
  σ_symm p q := by
    change (q * p).negOnePow = (p * q).negOnePow
    rw [mul_comm]

end HomologicalComplex₂

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Algebra.Homology.HasNoLoop

/-!
# Computations for additive total-complex shapes

The total-complex shape induced by tensor signs adds the two input indices.
This characteristic equation is independent of the category or bifunctor
used to form a total complex. Tensor signs change sign along every relation, so a complex shape
with tensor signs has no loops.

Mathlib supplies tensor signs for `ComplexShape.down ℕ` and `ComplexShape.up ℤ`; the instance
`ComplexShape.instTensorSignsDownInt` supplies the sign `ε p = (-1)^p` on `ComplexShape.down ℤ`, so
that chain complexes indexed by `ℤ`, such as Floer complexes graded by an index, have tensor
products with the Koszul differential `d (x ⊗ y) = d x ⊗ y + (-1)^p x ⊗ d y`. The instance
`ComplexShape.instTotalComplexShapeSymmetryDownInt` adds the Koszul sign `(-1)^(p q)` relating the
total complexes of a bicomplex indexed by `ℤ` and of its flip (`ComplexShape.σ_down_ℤ`), the
chain-complex counterpart of Mathlib's instance for `ComplexShape.up ℤ`, whose sign is
`ComplexShape.σ_up_ℤ`; it gives the signed interchange of the factors of tensor products of such
chain complexes. The signs on
`ComplexShape.down ℤ` and on `ComplexShape.up ℤ` are symmetric in the two factors
(`TotalComplexShapeSymmetrySymmetry`).

The instance `HomologicalComplex₂.totalComplexShapeSymmetryDownNat` identifies the total
complexes of a first-quadrant bicomplex and of its flip by the Koszul sign `(-1)^(p*q)` in
bidegree `(p, q)`. It is the natural-number analogue of Mathlib's `TotalComplexShapeSymmetry`
instance for cochain complexes indexed by `ℤ`, and adapts its sign calculation
(`ComplexShape.σ_down_ℕ`). These signs are also symmetric in the two factors.

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

/-- The total complexes of a bicomplex of chain complexes indexed by `ℤ` and of its flip are
identified by the Koszul sign `(-1)^(p q)` in bidegree `(p, q)` (`ComplexShape.σ_down_ℤ`), as for
cochain complexes indexed by `ℤ` in Mathlib. -/
instance instTotalComplexShapeSymmetryDownInt :
    TotalComplexShapeSymmetry (down ℤ) (down ℤ) (down ℤ) where
  symm p q := add_comm q p
  σ p q := (p * q).negOnePow
  σ_ε₁ := by
    rintro _ p rfl q
    simp only [ε₁_def, ε₂_def, ε_down_ℤ, mul_one, add_mul, one_mul, add_comm (p * q) q,
      Int.negOnePow_add]
  σ_ε₂ := by
    rintro p _ q rfl
    simp only [ε₁_def, ε₂_def, ε_down_ℤ, one_mul, mul_add, mul_one, Int.negOnePow_add, mul_assoc,
      Int.units_mul_self]

/-- The Koszul symmetry sign on `ComplexShape.down ℤ` in bidegree `(p, q)` is `(-1)^(p q)`. -/
@[simp]
theorem σ_down_ℤ (p q : ℤ) : σ (down ℤ) (down ℤ) (down ℤ) p q = (p * q).negOnePow := rfl

/-- The Koszul symmetry signs on `ComplexShape.down ℤ` are symmetric in the two factors. -/
instance : TotalComplexShapeSymmetrySymmetry (down ℤ) (down ℤ) (down ℤ) where
  σ_symm p q := by rw [σ_down_ℤ, σ_down_ℤ, mul_comm]

/-- The Koszul symmetry sign of Mathlib's instance on `ComplexShape.up ℤ` in bidegree `(p, q)` is
`(-1)^(p q)`. -/
@[simp]
theorem σ_up_ℤ (p q : ℤ) : σ (up ℤ) (up ℤ) (up ℤ) p q = (p * q).negOnePow := rfl

/-- The Koszul symmetry signs on `ComplexShape.up ℤ` are symmetric in the two factors. -/
instance : TotalComplexShapeSymmetrySymmetry (up ℤ) (up ℤ) (up ℤ) where
  σ_symm p q := by rw [σ_up_ℤ, σ_up_ℤ, mul_comm]

/-- A complex shape with tensor signs has no relation from an index to itself, since the sign
changes along every relation. -/
instance hasNoLoop_of_tensorSigns {I : Type*} [AddMonoid I] (c : ComplexShape I)
    [c.TensorSigns] : c.HasNoLoop where
  not_rel_self p h := units_ne_neg_self (c.ε p) (c.ε_succ h)

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

/-- The Koszul symmetry sign on `ComplexShape.down ℕ` in bidegree `(p, q)` is `(-1)^(p q)`. -/
@[simp]
theorem _root_.ComplexShape.σ_down_ℕ (p q : ℕ) :
    ComplexShape.σ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) p q =
      (-1 : ℤˣ) ^ (p * q) :=
  rfl

/-- As an integer, the Koszul symmetry sign on `ComplexShape.down ℕ` in bidegree `(p, q)` is
`(-1)^(p * q)`. -/
theorem _root_.ComplexShape.val_σ_down_ℕ (p q : ℕ) :
    (ComplexShape.σ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) p q : ℤ) =
      (-1 : ℤ) ^ (p * q) := by
  simp

/-- The Koszul symmetry signs on `ComplexShape.down ℕ` are symmetric in the two factors. -/
instance : TotalComplexShapeSymmetrySymmetry (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ) where
  σ_symm p q := by rw [ComplexShape.σ_down_ℕ, ComplexShape.σ_down_ℕ, Nat.mul_comm]

end HomologicalComplex₂

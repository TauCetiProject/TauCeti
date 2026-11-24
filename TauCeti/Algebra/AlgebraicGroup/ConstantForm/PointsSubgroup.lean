/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The matrix group preserving a constant form

For a commutative semiring `A` and a square matrix `C` over `A`, this file defines the subgroup

```text
{g ∈ GL_ι(A) : g C gᵀ = C}
```

of the invertible matrices preserving `C` in the row convention of `TauCeti.ConstantForm`, and
shows that entrywise mapping along a ring homomorphism `f` sends it into the subgroup for
`C.map f`. Nothing is assumed of `C`. These are the matrix point groups that the constant-form
group schemes specialize, for instance `TauCeti.AntidiagonalSpecialOrthogonal.pointsSubgroup`.

## Main declarations

* `TauCeti.ConstantForm.pointsSubgroup`: the subgroup of `GL_ι(A)` preserving `C`.
* `TauCeti.ConstantForm.map_mem_pointsSubgroup`: entrywise mapping along a ring homomorphism
  preserves membership, with `C` replaced by `C.map f`.

## References

* J. S. Milne, *Algebraic Groups* (2017), 2.10, the group `{A ∈ GLₙ(R) | AᵗCA = C}` (in the
  column convention).
-/

public section

open Matrix

namespace TauCeti.ConstantForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section CommSemiring

variable {A : Type*} [CommSemiring A]

/-- **The matrices preserving a constant form**: the invertible matrices `g` with `g C gᵀ = C`,
in the row convention of `TauCeti.ConstantForm`. -/
def pointsSubgroup (C : Matrix ι ι A) : Subgroup (GL ι A) where
  carrier := {g | (g : Matrix ι ι A) * C * (g : Matrix ι ι A)ᵀ = C}
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_ofPred_eq, Units.val_mul, transpose_mul] at hg hh ⊢
    calc _ = (g : Matrix ι ι A) * ((h : Matrix ι ι A) * C * (h : Matrix ι ι A)ᵀ) *
            (g : Matrix ι ι A)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = C := by rw [hh, hg]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Units.val_one, transpose_one, Matrix.one_mul, Matrix.mul_one]
  inv_mem' {g} hg := by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have hinv : ((g⁻¹ : GL ι A) : Matrix ι ι A) * (g : Matrix ι ι A) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    conv_lhs => rw [← hg]
    calc _ = (((g⁻¹ : GL ι A) : Matrix ι ι A) * (g : Matrix ι ι A)) * C *
            (((g⁻¹ : GL ι A) : Matrix ι ι A) * (g : Matrix ι ι A))ᵀ := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = C := by rw [hinv, transpose_one, Matrix.one_mul, Matrix.mul_one]

/-- Membership in the matrix group preserving `C`: `g C gᵀ = C`. -/
@[simp]
theorem mem_pointsSubgroup_iff {C : Matrix ι ι A} (g : GL ι A) :
    g ∈ pointsSubgroup C ↔ (g : Matrix ι ι A) * C * (g : Matrix ι ι A)ᵀ = C :=
  Iff.rfl

end CommSemiring

/-- Entrywise mapping along a ring homomorphism `f` sends a matrix preserving `C` to a matrix
preserving `C.map f`. -/
theorem map_mem_pointsSubgroup {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    {C : Matrix ι ι A} {g : GL ι A} (hg : g ∈ pointsSubgroup C) :
    Matrix.GeneralLinearGroup.map f g ∈ pointsSubgroup (C.map f) := by
  have hcoe : (Matrix.GeneralLinearGroup.map f g : Matrix ι ι B) = (g : Matrix ι ι A).map f := by
    ext i j
    exact Matrix.GeneralLinearGroup.map_apply f i j g
  rw [mem_pointsSubgroup_iff, hcoe, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
    (mem_pointsSubgroup_iff g).mp hg]

end TauCeti.ConstantForm

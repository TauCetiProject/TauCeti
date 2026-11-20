/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# The bilinear form of a basis

A basis `b` of a module `M` over a commutative semiring defines the bilinear form `b.toDual`, in
which the basis vectors are orthonormal. This file records that this form is symmetric and
nondegenerate, and that for a finite basis it is the dot product of coordinates.

## Main results

* `Module.Basis.toDual_comm`: `b.toDual x y = b.toDual y x`.
* `Module.Basis.isSymm_toDual`, `Module.Basis.nondegenerate_toDual`: the form `b.toDual` is
  symmetric and nondegenerate.
* `Module.Basis.toDual_apply_eq_sum`: for a finite basis, `b.toDual x y` is the dot product of the
  coordinates of `x` and `y`.
-/

public section

namespace Module.Basis

variable {R M ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [DecidableEq ι]
  (b : Basis ι R M)

/-- **The bilinear form of a basis is symmetric.** -/
theorem toDual_comm (x y : M) : b.toDual x y = b.toDual y x := by
  have : b.toDual.flip = b.toDual :=
    LinearMap.BilinForm.ext_basis b fun i j => by simp [toDual_apply, eq_comm]
  exact LinearMap.congr_fun₂ this y x

/-- **The bilinear form of a basis is a symmetric bilinear form.** -/
theorem isSymm_toDual : LinearMap.BilinForm.IsSymm b.toDual :=
  LinearMap.BilinForm.isSymm_def.mpr b.toDual_comm

/-- **The bilinear form of a basis is nondegenerate.** -/
theorem nondegenerate_toDual : LinearMap.BilinForm.Nondegenerate b.toDual :=
  ⟨fun x hx => b.toDual_inj x (LinearMap.ext hx),
    fun y hy => b.toDual_inj y (LinearMap.ext fun x => by rw [toDual_comm]; exact hy x)⟩

/-- **The bilinear form of a finite basis is the dot product of coordinates.** -/
theorem toDual_apply_eq_sum [Fintype ι] (x y : M) :
    b.toDual x y = ∑ i, b.repr x i * b.repr y i := by
  conv_lhs => rw [← b.sum_repr y]
  simp only [map_sum, map_smul, toDual_apply_left, smul_eq_mul, mul_comm]

end Module.Basis

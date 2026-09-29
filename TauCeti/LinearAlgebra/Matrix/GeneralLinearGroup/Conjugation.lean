/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `GL`, its coercion to matrices, the scalar embedding, and the determinant occur in the
-- statements below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- Non-public: `Matrix.GeneralLinearGroup.center_eq_range_scalar`, that the centre of `GL n R`
-- is the scalars, is used only in a proof.
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Conjugation invariants in the general linear group

This file records elementary invariants of conjugation in a general linear group that are useful
across the concrete subgroup and conjugacy-class computations, and the fact that conjugation by an
element of `GL n R` determines that element up to a unit scalar. The latter is what makes the
conjugators of a family of inner automorphisms of `Mₙ(R)` multiply up to scalars, as in the
construction of the Galois `2`-cocycle of a split central simple algebra.

## Main results

* `Matrix.GeneralLinearGroup.det_sub_algebraMap_conj`: shifting a matrix by a scalar and taking its
  determinant is invariant under conjugation.
* `Matrix.GeneralLinearGroup.exists_scalar_mul_eq_of_forall_conj_eq`: two elements of `GL n R`
  inducing the same conjugation of `Matrix n n R` differ by a unit scalar.
* `Matrix.GeneralLinearGroup.scalar_injective`: for nonempty `n`, the scalar embedding
  `Rˣ → GL n R` is injective.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n]

/-- For nonempty `n`, the scalar embedding `Rˣ → GL n R` is injective. -/
theorem scalar_injective [Semiring R] [Nonempty n] :
    Function.Injective (scalar n : Rˣ →* GL n R) :=
  fun u v h ↦
    Units.ext (Matrix.scalar_inj.mp (by simpa only [coe_scalar] using congrArg Units.val h))

variable [CommRing R]

/-- Shifting a matrix by a scalar and taking its determinant is invariant under conjugation in
the general linear group. -/
theorem det_sub_algebraMap_conj (g x : GL n R) (a : R) :
    (((x⁻¹ * g * x : GL n R) : Matrix n n R) - algebraMap R (Matrix n n R) a).det =
      ((g : Matrix n n R) - algebraMap R (Matrix n n R) a).det := by
  have hxx : ((x⁻¹ : GL n R) : Matrix n n R) * (x : Matrix n n R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcancel : ((x⁻¹ : GL n R) : Matrix n n R) *
      algebraMap R (Matrix n n R) a * (x : Matrix n n R) =
      algebraMap R (Matrix n n R) a := by
    rw [mul_assoc, Algebra.commutes a (x : Matrix n n R), ← mul_assoc, hxx, one_mul]
  have hsplit : ((x⁻¹ * g * x : GL n R) : Matrix n n R) -
      algebraMap R (Matrix n n R) a =
      ((x⁻¹ : GL n R) : Matrix n n R) *
        ((g : Matrix n n R) - algebraMap R (Matrix n n R) a) * (x : Matrix n n R) := by
    rw [mul_sub, sub_mul, hcancel, Units.val_mul, Units.val_mul]
  rw [hsplit, Matrix.coe_units_inv, Matrix.det_conj' x.isUnit]

/-- **An inner automorphism determines its conjugator up to a scalar.** If `g` and `h` in
`GL n R` conjugate every matrix in the same way, then `g` is `h` multiplied by the scalar matrix
of a unit `u`. -/
theorem exists_scalar_mul_eq_of_forall_conj_eq {g h : GL n R}
    (H : ∀ m : Matrix n n R, (g : Matrix n n R) * m * ((g⁻¹ : GL n R) : Matrix n n R) =
      h * m * ((h⁻¹ : GL n R) : Matrix n n R)) :
    ∃ u : Rˣ, scalar n u * h = g := by
  -- `h⁻¹ * g` commutes with every unit, so it is a scalar
  have hz : h⁻¹ * g ∈ Subgroup.center (GL n R) := Subgroup.mem_center_iff.mpr fun x ↦ by
    have e : g * x * g⁻¹ = h * x * h⁻¹ := Units.ext (by simpa only [Units.val_mul] using H x)
    calc x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by group
      _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [e]
      _ = h⁻¹ * g * x := by group
  rw [center_eq_range_scalar] at hz
  obtain ⟨u, hu⟩ := hz
  exact ⟨u, by rw [scalar_commute, hu, mul_inv_cancel_left]⟩

end Matrix.GeneralLinearGroup

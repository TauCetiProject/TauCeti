/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Instances.Matrix

/-!
# `U(n) = Circle · SU(n)`

The determinant of a complex unitary matrix has modulus one, and every point of the circle has a
`card n`-th root there, so a unitary matrix can be rescaled by a scalar of modulus one until its
determinant is one: the unitary group is the product of the scalars of modulus one with the special
unitary group. Rescaling by a scalar of modulus one keeps a matrix unitary, so nothing is lost.

## Main results

* `Circle.coe_mem_unitary`: a point of the circle is a unitary complex number.
* `Matrix.diagonal_mem_unitaryGroup_iff`: a diagonal matrix is unitary exactly when its diagonal
  entries are.
* `Matrix.diagonal_update_one_mem_unitaryGroup`: a diagonal matrix with one unitary diagonal entry
  and all other entries `1` is unitary.
* `Matrix.exists_circle_smul_mem_specialUnitaryGroup`: every complex unitary matrix becomes
  special unitary after multiplication by a suitable scalar of modulus one.
* `Matrix.mem_unitaryGroup_of_star_mul_self_eq_scalar`: over `ℝ` or `ℂ`, a matrix `A` for which
  `Aᴴ A` is a scalar matrix and `‖det A‖ = 1` is unitary. This turns conditions that determine a
  matrix only up to a scalar factor, such as those coming from its action on a projective space,
  into unitarity.


## Main definitions

* `Matrix.UnitaryGroup.detCircle`: the determinant of a complex unitary matrix, as a continuous
  group morphism `U(n) →* Circle`.
-/

public section

namespace Matrix

variable {n α : Type*} [Fintype n] [DecidableEq n] [CommRing α] [StarRing α]

/-- A diagonal matrix is unitary exactly when each of its diagonal entries is unitary. -/
theorem diagonal_mem_unitaryGroup_iff {d : n → α} :
    diagonal d ∈ unitaryGroup n α ↔ ∀ i, d i ∈ unitary α := by
  simp only [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal, ← diagonal_one, diagonal_eq_diagonal_iff, Pi.star_apply,
    Unitary.mem_iff_self_mul_star]

/-- A diagonal matrix with one diagonal entry a unitary scalar and the others `1` is unitary. -/
theorem diagonal_update_one_mem_unitaryGroup {a : α} (ha : a ∈ unitary α) (i : n) :
    diagonal (Function.update (1 : n → α) i a) ∈ unitaryGroup n α :=
  diagonal_mem_unitaryGroup_iff.mpr fun j ↦ by
    rcases eq_or_ne j i with rfl | h
    · simpa using ha
    · simp [Function.update_of_ne h]

/-- **Recognizing unitary matrices.** If `Aᴴ A` is a scalar matrix and the determinant of `A` has
norm one, then `A` is unitary: the scalar is the squared norm of a column of `A`, a nonnegative
real number whose `card n`-th power is `‖det A‖ ^ 2 = 1`. -/
theorem mem_unitaryGroup_of_star_mul_self_eq_scalar {𝕜 : Type*} [RCLike 𝕜] {A : Matrix n n 𝕜}
    {u : 𝕜} (hdet : ‖A.det‖ = 1) (h : star A * A = scalar n u) :
    A ∈ unitaryGroup n 𝕜 := by
  rw [mem_unitaryGroup_iff', h]
  rcases isEmpty_or_nonempty n with hn | hn
  · exact Subsingleton.elim _ _
  obtain ⟨i⟩ := id hn
  -- The scalar is the squared norm of the `i`-th column of `A`.
  have hu : u = ((∑ k, ‖A k i‖ ^ 2 : ℝ) : 𝕜) := by
    have hii := congrFun (congrFun h i) i
    rw [Matrix.mul_apply, scalar_apply, diagonal_apply_eq] at hii
    simp only [star_apply] at hii
    rw [← hii]
    push_cast
    exact Finset.sum_congr rfl fun k _ => RCLike.conj_mul (A k i)
  -- Its `card n`-th power is `‖det A‖ ^ 2 = 1`.
  have hpow : (∑ k, ‖A k i‖ ^ 2) ^ Fintype.card n = 1 := by
    have hd := congrArg det h
    simp only [det_mul, star_eq_conjTranspose, det_conjTranspose, RCLike.star_def,
      RCLike.conj_mul, hdet, RCLike.ofReal_one, one_pow, scalar_apply, det_diagonal,
      Finset.prod_const, Finset.card_univ, hu] at hd
    exact_mod_cast hd.symm
  rw [hu, (pow_eq_one_iff_of_nonneg (a := ∑ k, ‖A k i‖ ^ 2)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    Fintype.card_ne_zero).mp hpow]
  simp

end Matrix

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A point of the circle is a unitary complex number. -/
theorem _root_.Circle.coe_mem_unitary (z : Circle) : (z : ℂ) ∈ unitary ℂ :=
  Unitary.mem_iff_star_mul_self.mpr <| by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Circle.normSq_coe, Complex.ofReal_one]

/-- `U(n) = Circle · SU(n)`: every complex unitary matrix becomes special unitary after
multiplication by a suitable scalar of modulus one. The scalar is a `card n`-th root of the inverse
of the determinant, which has modulus one; the root is taken through `Circle.exp`. -/
theorem _root_.Matrix.exists_circle_smul_mem_specialUnitaryGroup (U : Matrix.unitaryGroup n ℂ) :
    ∃ c : Circle, ((c : ℂ) • (U : Matrix n n ℂ)) ∈ Matrix.specialUnitaryGroup n ℂ := by
  -- Rescaling by a scalar of modulus one keeps the matrix unitary, whatever the scalar.
  have hunit : ∀ c : Circle, ((c : ℂ) • (U : Matrix n n ℂ)) ∈ Matrix.unitaryGroup n ℂ := fun c =>
    Unitary.smul_mem_of_mem c.coe_mem_unitary U.2
  rcases isEmpty_or_nonempty n with hn | hn
  · -- With no indices at all every determinant is one and there is nothing to rescale.
    exact ⟨1, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨hunit 1, Matrix.det_isEmpty⟩⟩
  · have hcard : (Fintype.card n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hnorm : ‖(U : Matrix n n ℂ).det‖ = 1 :=
      CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary U.2)
    obtain ⟨θ, hθ⟩ := Circle.exp_surjective
      (⟨(U : Matrix n n ℂ).det, mem_sphere_zero_iff_norm.mpr hnorm⟩ : Circle)
    have hdetU : (U : Matrix n n ℂ).det = Complex.exp ((θ : ℂ) * Complex.I) := by
      have := congrArg (fun z : Circle => (z : ℂ)) hθ
      rw [Circle.coe_exp] at this
      exact this.symm
    refine ⟨Circle.exp (-(θ / Fintype.card n)), Matrix.mem_specialUnitaryGroup_iff.mpr
      ⟨hunit _, ?_⟩⟩
    rw [Matrix.det_smul, Circle.coe_exp, hdetU, ← Complex.exp_nat_mul, ← Complex.exp_add,
      ← Complex.exp_zero]
    congr 1
    push_cast
    field_simp
    ring

end TauCeti

namespace Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant of a complex unitary matrix, as a point of the unit circle. -/
noncomputable def detCircle : unitaryGroup n ℂ →* Circle where
  toFun U := ⟨(U : Matrix n n ℂ).det,
    mem_sphere_zero_iff_norm.2 (CStarRing.norm_of_mem_unitary (det_of_mem_unitary U.2))⟩
  map_one' := Circle.ext det_one
  map_mul' U V := Circle.ext (det_mul (U : Matrix n n ℂ) V)

/-- The point of the circle given by a unitary matrix is its determinant. -/
@[simp]
theorem coe_detCircle (U : unitaryGroup n ℂ) : (detCircle U : ℂ) = (U : Matrix n n ℂ).det :=
  (rfl)

/-- The determinant of a unitary matrix depends continuously on the matrix. -/
theorem continuous_detCircle : Continuous (detCircle : unitaryGroup n ℂ → Circle) :=
  Continuous.subtype_mk (continuous_subtype_val.matrix_det) _

end Matrix.UnitaryGroup

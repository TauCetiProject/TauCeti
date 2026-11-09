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
* `Matrix.exists_circle_smul_mem_specialUnitaryGroup`: every complex unitary matrix becomes
  special unitary after multiplication by a suitable scalar of modulus one.
* `Matrix.mem_unitaryGroup_of_star_mul_self_eq_scalar`: over `ℝ` or `ℂ`, a matrix `A` for which
  `Aᴴ A` is a scalar matrix and `‖det A‖ = 1` is unitary. This turns conditions that determine a
  matrix only up to a scalar factor, such as those coming from its action on a projective space,
  into unitarity.
* `Matrix.forall_sq_norm_add_sq_norm_eq_iff_mem_unitaryGroup`: a complex `2 × 2` matrix is
  unitary exactly when it preserves the Hermitian norm of every vector `(z, 1)`.


## Main definitions

* `Matrix.UnitaryGroup.detCircle`: the determinant of a complex unitary matrix, as a continuous
  group morphism `U(n) →* Circle`.
-/

public section

/-- A point of the circle is a unitary complex number. -/
theorem Circle.coe_mem_unitary (z : Circle) : (z : ℂ) ∈ unitary ℂ :=
  Unitary.mem_iff_star_mul_self.mpr <| by simp [← Complex.normSq_eq_conj_mul_self]

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

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

open ComplexConjugate in
/-- **Recognizing `2 × 2` unitary matrices.** A complex matrix `!![a, b; c, d]` is unitary exactly
when `|a z + b|² + |c z + d|² = |z|² + 1` for every `z`, that is, when it preserves the Hermitian
norm of every vector `(z, 1)`. -/
theorem forall_sq_norm_add_sq_norm_eq_iff_mem_unitaryGroup (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (∀ z : ℂ, ‖A 0 0 * z + A 0 1‖ ^ 2 + ‖A 1 0 * z + A 1 1‖ ^ 2 = ‖z‖ ^ 2 + 1) ↔
      A ∈ unitaryGroup (Fin 2) ℂ := by
  -- Unitarity says that the columns `(a, c)` and `(b, d)` are orthonormal.
  rw [mem_unitaryGroup_iff', ← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Complex.star_def, Matrix.one_apply_eq, ne_eq, zero_ne_one, not_false_eq_true,
    Matrix.one_apply_ne, one_ne_zero]
  -- In complex form the identity reads `(conj a conj z + conj b) (a z + b) + ⋯ = conj z z + 1`.
  have key (z : ℂ) : ‖A 0 0 * z + A 0 1‖ ^ 2 + ‖A 1 0 * z + A 1 1‖ ^ 2 = ‖z‖ ^ 2 + 1 ↔
      (conj (A 0 0) * conj z + conj (A 0 1)) * (A 0 0 * z + A 0 1) +
        (conj (A 1 0) * conj z + conj (A 1 1)) * (A 1 0 * z + A 1 1) = conj z * z + 1 := by
    rw [← Complex.ofReal_inj]
    push_cast
    simp only [← Complex.conj_mul', map_add, map_mul]
  simp only [key]
  generalize A 0 0 = a
  generalize A 0 1 = b
  generalize A 1 0 = c
  generalize A 1 1 = d
  constructor
  · -- Evaluate at `z = 0, 1, -1, i` and compare.
    intro h
    have h0 := h 0
    have h1 := h 1
    have hm1 := h (-1)
    have hI := h Complex.I
    simp only [map_zero, map_one, map_neg, Complex.conj_I, mul_zero, zero_add, mul_one,
      mul_neg] at h0 h1 hm1 hI
    have h01 : conj a * b + conj c * d = 0 := by
      linear_combination (h1 - hm1) / 4 + Complex.I / 2 * hI - Complex.I / 4 * (h1 + hm1) +
        ((conj a * b + conj c * d - conj b * a - conj d * c) / 2 +
          Complex.I / 2 * (conj a * a + conj c * c - 1)) * Complex.I_sq
    refine ⟨⟨by linear_combination (h1 + hm1) / 2 - h0, h01⟩, ?_, h0⟩
    simpa [mul_comm] using congrArg conj h01
  · rintro ⟨⟨h00, h01⟩, h10, h11⟩ z
    linear_combination (conj z * z) * h00 + conj z * h01 + z * h10 + h11

/-- `U(n) = Circle · SU(n)`: every complex unitary matrix becomes special unitary after
multiplication by a suitable scalar of modulus one. The scalar is a `card n`-th root of the inverse
of the determinant, which has modulus one; the root is taken through `Circle.exp`. -/
theorem exists_circle_smul_mem_specialUnitaryGroup (U : unitaryGroup n ℂ) :
    ∃ c : Circle, (c : ℂ) • (U : Matrix n n ℂ) ∈ specialUnitaryGroup n ℂ := by
  -- Rescaling by a scalar of modulus one keeps the matrix unitary, whatever the scalar.
  have hunit (c : Circle) : (c : ℂ) • (U : Matrix n n ℂ) ∈ unitaryGroup n ℂ :=
    Unitary.smul_mem_of_mem c.coe_mem_unitary U.2
  rcases isEmpty_or_nonempty n with hn | hn
  · -- With no indices at all every determinant is one and there is nothing to rescale.
    exact ⟨1, mem_specialUnitaryGroup_iff.mpr ⟨hunit 1, det_isEmpty⟩⟩
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective (⟨(U : Matrix n n ℂ).det,
    mem_sphere_zero_iff_norm.mpr (CStarRing.norm_of_mem_unitary (det_of_mem_unitary U.2))⟩ :
      Circle)
  refine ⟨Circle.exp (-(θ / Fintype.card n)), mem_specialUnitaryGroup_iff.mpr ⟨hunit _, ?_⟩⟩
  -- `c ^ card n` is the inverse of the determinant, viewed as a point of the circle.
  rw [det_smul, ← Circle.coe_pow, ← Circle.exp_natCast_mul, mul_neg,
    mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), Circle.exp_neg,
    Circle.coe_inv, hθ]
  exact inv_mul_cancel₀ (Circle.coe_ne_zero _)

end Matrix

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

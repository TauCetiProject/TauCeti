/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Quaternion
public import TauCeti.Algebra.CayleyDickson.Quaternion
public import TauCeti.Analysis.CayleyDickson.Basic

/-!
# The Euclidean structure of the real octonions

The real octonions `TauCeti.DivisionOctonionReal` are the Cayley–Dickson double of the real
quaternions `ℍ`, normed as the `L²` product of their two quaternion coordinates
(`TauCeti.Analysis.CayleyDickson.Basic`). This file identifies that norm with the octonion norm
`N ⟨a, b⟩ = N a + N b` of `TauCeti.Algebra.CayleyDickson.Quaternion`, `‖x‖ ^ 2 = N x`, and the inner
product with its polarization, the trace pairing `⟪x, y⟫ = Re (x * star y) = T (x * star y) / 2`.
Since `N` is multiplicative, so is the norm, `‖x * y‖ = ‖x‖ * ‖y‖`, and left and right
multiplication by `x` scale the inner product by `‖x‖ ^ 2`: the real octonions form a normed
composition algebra.

The real octonions are an eight-dimensional real inner product space, and their multiplication is
a continuous real-bilinear map, `TauCeti.CayleyDickson.mulL`. Hence multiplication, conjugation, and
inversion away from `0` are smooth. The coordinates `re, i, j, k` of the two quaternion components,
in this order, identify the real octonions isometrically with `EuclideanSpace ℝ (Fin 8)`
(`TauCeti.DivisionOctonionReal.linearIsometryEquivTuple`).

No associative normed-ring structure is asserted: the octonions are not associative.

## Main definitions

* `TauCeti.CayleyDickson.mulL`: the multiplication of the real octonions, as a continuous bilinear
  map.
* `TauCeti.DivisionOctonionReal.linearIsometryEquivTuple`: the eight real coordinates, as a linear
  isometry equivalence with `EuclideanSpace ℝ (Fin 8)`.

## Main results

* `TauCeti.CayleyDickson.norm_sq_eq_normSq`: the square of the norm is the octonion norm.
* `TauCeti.CayleyDickson.real_inner_eq_re_mul_star` and
  `TauCeti.CayleyDickson.real_inner_eq_trace_mul_star`: the inner product is the trace pairing.
* The instance `NormMulClass DivisionOctonionReal`: the norm is multiplicative.
* `TauCeti.CayleyDickson.inner_mul_mul_left` and `TauCeti.CayleyDickson.inner_mul_mul_right`:
  multiplication by `x` scales the inner product by `‖x‖ ^ 2`.
* `TauCeti.CayleyDickson.norm_inv`: the norm of an inverse is the inverse of the norm.
* `TauCeti.CayleyDickson.contDiff_mul`, `TauCeti.CayleyDickson.contDiff_star` and
  `TauCeti.CayleyDickson.contDiffAt_inv`: multiplication, conjugation, and inversion at a nonzero
  point are smooth.

## References

* J. C. Baez, *The octonions*, Bull. Amer. Math. Soc. **39** (2002), 145–205, §2.2 and §3.1.
* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*,
  Springer (2000), §1.2 and §1.5.
-/

public section

open scoped Quaternion InnerProductSpace ContDiff

namespace TauCeti

namespace CayleyDickson

variable (x y z : DivisionOctonionReal)

/-! ### The norm and the inner product -/

/-- **The square of the norm of a real octonion is its octonion norm**,
`‖⟨a, b⟩‖ ^ 2 = N a + N b`. -/
theorem norm_sq_eq_normSq : ‖x‖ ^ 2 = normSq x := by
  rw [norm_sq_eq, normSq_def, Quaternion.normSq_eq_norm_mul_self,
    Quaternion.normSq_eq_norm_mul_self, sq, sq]

/-- The octonion norm is the product of the norm with itself. -/
theorem normSq_eq_norm_mul_self : normSq x = ‖x‖ * ‖x‖ := by
  rw [← sq, norm_sq_eq_normSq]

/-- The norm of a real octonion is the square root of its octonion norm. -/
theorem norm_eq_sqrt_normSq : ‖x‖ = √(normSq x) := by
  rw [← norm_sq_eq_normSq, Real.sqrt_sq (norm_nonneg x)]

/-- **The inner product of the real octonions is the real part of `x * star y`.** -/
theorem real_inner_eq_re_mul_star : ⟪x, y⟫_ℝ = (x * star y).fst.re := by
  rw [inner_def, Quaternion.inner_def, Quaternion.inner_def]
  simp only [mul_fst, star_fst, star_snd, star_neg, neg_mul, sub_neg_eq_add,
    QuaternionAlgebra.re_add, Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star]
  ring

/-- **The inner product of the real octonions is half the trace pairing**,
`⟪x, y⟫ = T (x * star y) / 2`: it is the polar form of the octonion norm. -/
theorem real_inner_eq_trace_mul_star : ⟪x, y⟫_ℝ = trace (x * star y) / 2 := by
  rw [real_inner_eq_re_mul_star, trace_apply, mul_div_cancel_left₀ _ two_ne_zero]

/-- The inner product of a real octonion with itself is its octonion norm. -/
theorem real_inner_self_eq_normSq : ⟪x, x⟫_ℝ = normSq x := by
  rw [real_inner_self_eq_norm_sq, norm_sq_eq_normSq]

/-- **The norm of the real octonions is multiplicative**: they are a normed composition algebra. -/
instance : NormMulClass DivisionOctonionReal where
  norm_mul x y := by
    rw [norm_eq_sqrt_normSq, norm_eq_sqrt_normSq, norm_eq_sqrt_normSq, normSq_mul,
      Real.sqrt_mul normSq_nonneg]

/-- **Left multiplication scales the inner product by the square of the norm**,
`⟪x * y, x * z⟫ = ‖x‖ ^ 2 * ⟪y, z⟫`, the polarization of `‖x * y‖ = ‖x‖ * ‖y‖`. -/
theorem inner_mul_mul_left : ⟪x * y, x * z⟫_ℝ = ‖x‖ ^ 2 * ⟪y, z⟫_ℝ := by
  have h := norm_add_sq_real (x * y) (x * z)
  rw [← mul_add, norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow,
    norm_add_sq_real y z] at h
  linarith

/-- **Right multiplication scales the inner product by the square of the norm**,
`⟪y * x, z * x⟫ = ‖x‖ ^ 2 * ⟪y, z⟫`. -/
theorem inner_mul_mul_right : ⟪y * x, z * x⟫_ℝ = ‖x‖ ^ 2 * ⟪y, z⟫_ℝ := by
  have h := norm_add_sq_real (y * x) (z * x)
  rw [← add_mul, norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow,
    norm_add_sq_real y z] at h
  linarith

/-- The norm of the inverse of a real octonion is the inverse of its norm. -/
@[simp]
theorem norm_inv : ‖x⁻¹‖ = ‖x‖⁻¹ := by
  rw [inv_def, norm_smul, norm_star, Real.norm_eq_abs, abs_inv, abs_of_nonneg normSq_nonneg,
    normSq_eq_norm_mul_self]
  rcases eq_or_ne ‖x‖ 0 with hx | hx
  · simp [hx]
  · field_simp

/-! ### Smoothness of the algebra operations -/

/-- The multiplication of the real octonions, as a continuous real-bilinear map. Its operator norm
is at most `1`, by `‖x * y‖ = ‖x‖ * ‖y‖`. -/
noncomputable def mulL :
    DivisionOctonionReal →L[ℝ] DivisionOctonionReal →L[ℝ] DivisionOctonionReal :=
  (LinearMap.mul ℝ DivisionOctonionReal).mkContinuous₂ 1 fun x y => by simp

@[simp]
theorem mulL_apply : mulL x y = x * y :=
  (rfl)

/-- **The multiplication of the real octonions is smooth.** -/
theorem contDiff_mul {n : WithTop ℕ∞} :
    ContDiff ℝ n fun p : DivisionOctonionReal × DivisionOctonionReal => p.1 * p.2 :=
  mulL.isBoundedBilinearMap.contDiff

instance : ContinuousMul DivisionOctonionReal :=
  ⟨contDiff_mul.continuous (n := 0)⟩

/-- **The conjugation of the real octonions is smooth**: it is the real-linear map
`x ↦ T x • 1 - x`. -/
theorem contDiff_star {n : WithTop ℕ∞} : ContDiff ℝ n (star : DivisionOctonionReal → _) := by
  have h : (star : DivisionOctonionReal → _) = fun x => trace x • (1 : DivisionOctonionReal) - x :=
    funext star_eq_trace_smul_one_sub
  rw [h]
  exact (LinearMap.toContinuousLinearMap (trace : DivisionOctonionReal →ₗ[ℝ] ℝ)).contDiff.smul
    contDiff_const |>.sub contDiff_id

/-- **Inversion of the real octonions is smooth at every nonzero point**:
`x⁻¹ = (‖x‖ ^ 2)⁻¹ • star x`. -/
theorem contDiffAt_inv {n : WithTop ℕ∞} {x : DivisionOctonionReal} (hx : x ≠ 0) :
    ContDiffAt ℝ n (·⁻¹) x := by
  have h : (·⁻¹ : DivisionOctonionReal → _) = fun y => (‖y‖ ^ 2)⁻¹ • star y := by
    funext y
    rw [inv_def, norm_sq_eq_normSq]
  rw [h]
  exact ((contDiff_norm_sq ℝ).contDiffAt.inv (by positivity)).smul contDiff_star.contDiffAt

/-- Inversion of the real octonions is smooth on the nonzero octonions. -/
theorem contDiffOn_inv {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (·⁻¹ : DivisionOctonionReal → _) {x | x ≠ 0} :=
  fun _ hx => (contDiffAt_inv hx).contDiffWithinAt

end CayleyDickson

/-! ### The eight-coordinate Euclidean model -/

namespace DivisionOctonionReal

open CayleyDickson

/-- The square of the norm of a real octonion is the sum of the squares of its eight real
coordinates. -/
theorem norm_sq_eq_sum (x : DivisionOctonionReal) :
    ‖x‖ ^ 2 = x.fst.re ^ 2 + x.fst.imI ^ 2 + x.fst.imJ ^ 2 + x.fst.imK ^ 2 +
      (x.snd.re ^ 2 + x.snd.imI ^ 2 + x.snd.imJ ^ 2 + x.snd.imK ^ 2) := by
  rw [norm_sq_eq_normSq, normSq_def, Quaternion.normSq_def', Quaternion.normSq_def']

/-- The eight real coordinates of a real octonion have the same Euclidean norm as the octonion. -/
theorem norm_toLp_tuple (x : DivisionOctonionReal) :
    ‖(!₂[x.fst.re, x.fst.imI, x.fst.imJ, x.fst.imK, x.snd.re, x.snd.imI, x.snd.imJ, x.snd.imK] :
      EuclideanSpace ℝ (Fin 8))‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_sum]
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, Fin.sum_univ_eight, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- **The eight-coordinate Euclidean model of the real octonions**: the coordinates
`re, i, j, k` of the first quaternion component followed by those of the second, as a linear
isometry equivalence with `EuclideanSpace ℝ (Fin 8)`. -/
noncomputable def linearIsometryEquivTuple : DivisionOctonionReal ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 8)
    where
  toFun x := !₂[x.fst.re, x.fst.imI, x.fst.imJ, x.fst.imK,
    x.snd.re, x.snd.imI, x.snd.imJ, x.snd.imK]
  invFun v := ⟨⟨v 0, v 1, v 2, v 3⟩, ⟨v 4, v 5, v 6, v 7⟩⟩
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' r x := by
    ext i
    fin_cases i <;> simp
  left_inv x := rfl
  right_inv v := by
    ext i
    fin_cases i <;> rfl
  norm_map' := norm_toLp_tuple

@[simp]
theorem linearIsometryEquivTuple_apply (x : DivisionOctonionReal) :
    linearIsometryEquivTuple x = !₂[x.fst.re, x.fst.imI, x.fst.imJ, x.fst.imK,
      x.snd.re, x.snd.imI, x.snd.imJ, x.snd.imK] :=
  (rfl)

@[simp]
theorem linearIsometryEquivTuple_symm_apply (v : EuclideanSpace ℝ (Fin 8)) :
    linearIsometryEquivTuple.symm v = ⟨⟨v 0, v 1, v 2, v 3⟩, ⟨v 4, v 5, v 6, v 7⟩⟩ :=
  (rfl)

end DivisionOctonionReal

end TauCeti

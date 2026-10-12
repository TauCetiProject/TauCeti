/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Mathlib.Algebra.Quaternion` is imported publicly for `QuaternionAlgebra`, the `ℍ[·,·,·]`
-- notation, quaternion conjugation `star`, and the coordinate linear maps `QuaternionAlgebra.reₗ`
-- and `QuaternionAlgebra.linearEquivTuple`, all of which occur in the statements below.
public import Mathlib.Algebra.Quaternion
public import Mathlib.Algebra.Star.Unitary
-- `Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv` is imported publicly for
-- `QuadraticMap.IsometryEquiv` and `QuadraticMap.Equivalent`. It re-exports
-- `Mathlib.LinearAlgebra.QuadraticForm.Basic`, hence `QuadraticForm`, `QuadraticMap.ofPolar`,
-- `QuadraticMap.comp` and `QuadraticMap.weightedSumSquares`, which is why that file is not
-- imported again here.
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# The norm form of a quaternion algebra

The product `x * star x` of a quaternion with its conjugate is a scalar
(`QuaternionAlgebra.mul_star_eq_coe`). Its real part is the reduced norm, and this file packages it
as a quadratic form `QuaternionAlgebra.normForm` on `ℍ[R,c₁,c₂,c₃]` over a commutative ring, with
its coordinate expression and its multiplicativity.

In the classical presentation `ℍ[R,a,b] = ℍ[R,a,0,b]`, where `i² = a`, `j² = b` and `k = i * j`,
the basis `1, i, j, k` is orthogonal for the norm form, which is therefore the diagonal form
`⟨1, -a, -b, ab⟩`; this is the two-fold Pfister form `⟨⟨a,b⟩⟩`. The pure quaternions -- those with
vanishing real part, which by `QuaternionAlgebra.self_add_star_eq_zero_iff` are exactly those of
vanishing reduced trace once `2` is regular -- carry the restricted form `⟨-a, -b, ab⟩`.

The reduced norm is what ties a quaternion algebra to quadratic-form theory. Over a field of
characteristic other than two, with nonzero parameters `a` and `b`, whether `ℍ[K,a,b]` is split or
a division algebra is determined by its norm form; the diagonalizations above turn this into a
question about `⟨1, -a, -b, ab⟩`.

## Main definitions

* `QuaternionAlgebra.normForm`: the norm form `x ↦ (x * star x).re` of `ℍ[R,c₁,c₂,c₃]`.
* `QuaternionAlgebra.pureNormForm`: its restriction to the pure quaternions of `ℍ[R,a,b]`.

## Main results

* `QuaternionAlgebra.normForm_mul`: the norm form is multiplicative.
* `QuaternionAlgebra.mem_unitary_iff_normForm_eq_one`: a quaternion is unitary exactly when its
  norm form is one.
* `QuaternionAlgebra.isUnit_iff_normForm_isUnit`: a quaternion is invertible exactly when its norm
  is, and `QuaternionAlgebra.anisotropic_normForm_iff`: over a field, a quaternion algebra is a
  division algebra exactly when its norm form is anisotropic.
* `QuaternionAlgebra.equivalent_normForm_weightedSumSquares`: the norm form of `ℍ[R,a,b]` is the
  diagonal form `⟨1, -a, -b, ab⟩`, with the explicit isometry
  `QuaternionAlgebra.normFormIsometryEquivWeightedSumSquares`.
* `QuaternionAlgebra.equivalent_pureNormForm_weightedSumSquares`: the pure norm form of `ℍ[R,a,b]`
  is the diagonal form `⟨-a, -b, ab⟩`, with the explicit isometry
  `QuaternionAlgebra.pureNormFormIsometryEquivWeightedSumSquares`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter III, §2.
* P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §1.1.
-/

public section

open QuadraticMap

open scoped Quaternion

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R] (c₁ c₂ c₃ : R)

/-- The **norm form** of a quaternion algebra: the reduced norm `x ↦ (x * star x).re`, which is a
quadratic form because `x * star x` is the scalar `x.re² + c₂ x.re x.imI - c₁ x.imI² - c₃ x.imJ² -
c₂ c₃ x.imJ x.imK + c₁ c₃ x.imK²`. -/
def normForm : QuadraticForm R ℍ[R,c₁,c₂,c₃] :=
  ofPolar (fun x => (x * star x).re)
    (fun _ _ => by simp [re_mul]; ring)
    (fun _ _ _ => by simp [polar, re_mul]; ring)
    (fun _ _ _ => by simp [polar, re_mul]; ring)

theorem normForm_apply (x : ℍ[R,c₁,c₂,c₃]) : normForm c₁ c₂ c₃ x = (x * star x).re := (rfl)

/-- The norm form in coordinates: the basis `1, i, j, k` is orthogonal for it as soon as
`c₂ = 0`. -/
theorem normForm_apply_coordinates (x : ℍ[R,c₁,c₂,c₃]) :
    normForm c₁ c₂ c₃ x = x.re ^ 2 + c₂ * x.re * x.imI - c₁ * x.imI ^ 2 - c₃ * x.imJ ^ 2
      - c₂ * c₃ * x.imJ * x.imK + c₁ * c₃ * x.imK ^ 2 := by
  simp [normForm_apply, re_mul]; ring

/-- The companion bilinear form of the norm form is the reduced trace of `x * star y`. -/
theorem polar_normForm (x y : ℍ[R,c₁,c₂,c₃]) :
    polar (normForm c₁ c₂ c₃) x y = (x * star y + y * star x).re := by
  simp [polar, normForm_apply, re_mul]; ring

/-- A quaternion times its conjugate is the scalar given by its norm form. -/
theorem self_mul_star (x : ℍ[R,c₁,c₂,c₃]) :
    x * star x = (normForm c₁ c₂ c₃ x : ℍ[R,c₁,c₂,c₃]) := by
  rw [normForm_apply]; exact mul_star_eq_coe x

/-- The conjugate of a quaternion times the quaternion is the scalar given by its norm form. -/
theorem star_mul_self (x : ℍ[R,c₁,c₂,c₃]) :
    star x * x = (normForm c₁ c₂ c₃ x : ℍ[R,c₁,c₂,c₃]) := by
  rw [star_comm_self', self_mul_star]

/-- A quaternion is unitary exactly when its norm form is one. -/
@[simp]
theorem mem_unitary_iff_normForm_eq_one (x : ℍ[R,c₁,c₂,c₃]) :
    x ∈ unitary ℍ[R,c₁,c₂,c₃] ↔ normForm c₁ c₂ c₃ x = 1 := by
  rw [Unitary.mem_iff, star_mul_self, self_mul_star, and_self]
  constructor
  · intro h
    simpa using congrArg (fun y : ℍ[R,c₁,c₂,c₃] => y.re) h
  · intro h
    simp [h]

@[simp]
theorem normForm_coe (r : R) : normForm c₁ c₂ c₃ (r : ℍ[R,c₁,c₂,c₃]) = r ^ 2 := by
  simp [normForm_apply, _root_.sq]

@[simp]
theorem normForm_star (x : ℍ[R,c₁,c₂,c₃]) :
    normForm c₁ c₂ c₃ (star x) = normForm c₁ c₂ c₃ x := by
  rw [normForm_apply, normForm_apply, star_star, star_comm_self']

/-- **The norm form is multiplicative.** -/
@[simp]
theorem normForm_mul (x y : ℍ[R,c₁,c₂,c₃]) :
    normForm c₁ c₂ c₃ (x * y) = normForm c₁ c₂ c₃ x * normForm c₁ c₂ c₃ y := by
  -- This is Mathlib's multiplicativity argument for `Quaternion.normSq`, run for a general
  -- `ℍ[R,c₁,c₂,c₃]`: the scalar `y * star y` commutes past `star x`.
  have h : x * y * star (x * y) =
      ((normForm c₁ c₂ c₃ x * normForm c₁ c₂ c₃ y : R) : ℍ[R,c₁,c₂,c₃]) :=
    calc x * y * star (x * y)
        _ = x * (y * star y) * star x := by rw [star_mul]; simp only [mul_assoc]
        _ = x * star x * (normForm c₁ c₂ c₃ y : ℍ[R,c₁,c₂,c₃]) := by
          rw [self_mul_star, mul_assoc, coe_commutes, mul_assoc]
        _ = ((normForm c₁ c₂ c₃ x * normForm c₁ c₂ c₃ y : R) : ℍ[R,c₁,c₂,c₃]) := by
          rw [self_mul_star, coe_mul]
  rw [normForm_apply, h, re_coe]

/-- **A quaternion is invertible exactly when its norm is.** The inverse of `x` is
`N(x)⁻¹ star x`, and conversely the norm form is multiplicative. -/
theorem isUnit_iff_normForm_isUnit (x : ℍ[R,c₁,c₂,c₃]) :
    IsUnit x ↔ IsUnit (normForm c₁ c₂ c₃ x) := by
  refine ⟨fun ⟨u, hu⟩ => ?_, fun ⟨n, hn⟩ => ?_⟩
  · refine IsUnit.of_mul_eq_one (normForm c₁ c₂ c₃ ↑u⁻¹) ?_
    rw [← hu, ← normForm_mul, Units.mul_inv, ← coe_one, normForm_coe, one_pow]
  · refine ⟨⟨x, star x * ((n⁻¹ : Rˣ) : R), ?_, ?_⟩, rfl⟩
    · rw [← mul_assoc, self_mul_star, ← hn, ← coe_mul, Units.mul_inv, coe_one]
    · rw [mul_assoc, coe_commutes, ← mul_assoc, star_mul_self, ← hn, ← coe_mul, Units.mul_inv,
        coe_one]

/-- **Division or not, by the norm form.** A quaternion algebra over a field is a division algebra,
in the sense that every nonzero element is invertible, exactly when its norm form is anisotropic. -/
theorem anisotropic_normForm_iff {K : Type*} [Field K] (c₁ c₂ c₃ : K) :
    (normForm c₁ c₂ c₃).Anisotropic ↔ ∀ x : ℍ[K,c₁,c₂,c₃], x ≠ 0 → IsUnit x := by
  simp only [Anisotropic, isUnit_iff_normForm_isUnit, isUnit_iff_ne_zero, ne_eq, not_imp_not]

section Diagonal

variable (a b : R)

/-- The pure quaternions of `ℍ[R,a,b]`, the kernel of the real part, are exactly the quaternions
of vanishing reduced trace `x + star x`. -/
theorem self_add_star_eq_zero_iff (h2 : IsRegular (2 : R)) (x : ℍ[R,a,b]) :
    x + star x = 0 ↔ x ∈ LinearMap.ker (reₗ a (0 : R) b) := by
  rw [self_add_star]
  simp [QuaternionAlgebra.ext_iff, h2.left.mul_left_eq_zero_iff]

/-- The **pure norm form** of `ℍ[R,a,b]`: the norm form restricted to the pure quaternions, those
with vanishing real part. -/
def pureNormForm : QuadraticForm R (LinearMap.ker (reₗ a (0 : R) b)) :=
  (normForm a 0 b).comp (LinearMap.ker (reₗ a (0 : R) b)).subtype

@[simp]
theorem pureNormForm_apply (x : LinearMap.ker (reₗ a (0 : R) b)) :
    pureNormForm a b x = normForm a 0 b x := (rfl)

/-- The pure norm form in coordinates: the basis `i, j, k` is orthogonal for it. -/
theorem pureNormForm_apply_coordinates (x : LinearMap.ker (reₗ a (0 : R) b)) :
    pureNormForm a b x = -(a * (x : ℍ[R,a,b]).imI ^ 2) - b * (x : ℍ[R,a,b]).imJ ^ 2
      + a * b * (x : ℍ[R,a,b]).imK ^ 2 := by
  have hx : (x : ℍ[R,a,b]).re = 0 := x.2
  rw [pureNormForm_apply, normForm_apply_coordinates]
  simp [hx]

/-- The coordinates `1, i, j, k` are an isometry from the norm form of `ℍ[R,a,b]` to the diagonal
form `⟨1, -a, -b, ab⟩`, the two-fold Pfister form `⟨⟨a,b⟩⟩`. -/
def normFormIsometryEquivWeightedSumSquares :
    (normForm a 0 b).IsometryEquiv (weightedSumSquares R ![1, -a, -b, a * b]) where
  __ := linearEquivTuple a 0 b
  map_app' x := by simp [normForm_apply_coordinates, Fin.sum_univ_four]; ring

@[simp]
theorem normFormIsometryEquivWeightedSumSquares_apply (x : ℍ[R,a,b]) :
    normFormIsometryEquivWeightedSumSquares a b x = ![x.re, x.imI, x.imJ, x.imK] := (rfl)

@[simp]
theorem normFormIsometryEquivWeightedSumSquares_symm_apply (v : Fin 4 → R) :
    (normFormIsometryEquivWeightedSumSquares a b).symm v = ⟨v 0, v 1, v 2, v 3⟩ := (rfl)

/-- **The norm form of `ℍ[R,a,b]` is `⟨1, -a, -b, ab⟩`.** -/
theorem equivalent_normForm_weightedSumSquares :
    (normForm a 0 b).Equivalent (weightedSumSquares R ![(1 : R), -a, -b, a * b]) :=
  ⟨normFormIsometryEquivWeightedSumSquares a b⟩

/-- The coordinates `i, j, k` are an isometry from the pure norm form of `ℍ[R,a,b]` to the
diagonal form `⟨-a, -b, ab⟩`. -/
def pureNormFormIsometryEquivWeightedSumSquares :
    (pureNormForm a b).IsometryEquiv (weightedSumSquares R ![-a, -b, a * b]) where
  toFun x := ![(x : ℍ[R,a,b]).imI, (x : ℍ[R,a,b]).imJ, (x : ℍ[R,a,b]).imK]
  map_add' _ _ := by ext i; fin_cases i <;> simp
  map_smul' _ _ := by ext i; fin_cases i <;> simp
  invFun v := ⟨⟨0, v 0, v 1, v 2⟩, by simp⟩
  left_inv x := by
    have hx : (x : ℍ[R,a,b]).re = 0 := x.2
    ext <;> simp [hx]
  right_inv _ := by ext i; fin_cases i <;> simp
  map_app' x := by
    have hx : (x : ℍ[R,a,b]).re = 0 := x.2
    simp [normForm_apply_coordinates, hx, Fin.sum_univ_three]
    ring

@[simp]
theorem pureNormFormIsometryEquivWeightedSumSquares_apply
    (x : LinearMap.ker (reₗ a (0 : R) b)) :
    pureNormFormIsometryEquivWeightedSumSquares a b x =
      ![(x : ℍ[R,a,b]).imI, (x : ℍ[R,a,b]).imJ, (x : ℍ[R,a,b]).imK] := (rfl)

@[simp]
theorem pureNormFormIsometryEquivWeightedSumSquares_symm_apply (v : Fin 3 → R) :
    (pureNormFormIsometryEquivWeightedSumSquares a b).symm v =
      ⟨⟨0, v 0, v 1, v 2⟩, by simp⟩ := (rfl)

/-- **The pure norm form of `ℍ[R,a,b]` is `⟨-a, -b, ab⟩`.** -/
theorem equivalent_pureNormForm_weightedSumSquares :
    (pureNormForm a b).Equivalent (weightedSumSquares R ![-a, -b, a * b]) :=
  ⟨pureNormFormIsometryEquivWeightedSumSquares a b⟩

end Diagonal

end QuaternionAlgebra

namespace Quaternion

variable {R : Type*} [CommRing R]

/-- Mathlib's `Quaternion.normSq` is the norm form of `ℍ[R] = ℍ[R,-1,0,-1]`. -/
theorem normSq_eq_normForm (x : ℍ[R]) :
    normSq x = QuaternionAlgebra.normForm (-1) 0 (-1) x := by
  rw [QuaternionAlgebra.normForm_apply, normSq_def]

/-- A Hamilton quaternion is unitary exactly when its norm-square is one. -/
theorem mem_unitary_iff_normSq_eq_one (x : ℍ[R]) :
    x ∈ unitary ℍ[R] ↔ normSq x = 1 := by
  rw [normSq_eq_normForm, QuaternionAlgebra.mem_unitary_iff_normForm_eq_one]

/-- The quaternion underlying a unitary Hamilton quaternion has norm-square one. -/
@[simp]
theorem normSq_coe_unitary_eq_one (x : unitary ℍ[R]) : normSq (x : ℍ[R]) = 1 :=
  (mem_unitary_iff_normSq_eq_one _).mp x.2

end Quaternion

end

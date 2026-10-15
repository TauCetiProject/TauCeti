/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module
public import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Splitting quadratic algebras

A quadratic algebra whose defining polynomial has roots `r` and `s` with unit difference
is isomorphic to `R × R`. The two coordinates evaluate its generator at those roots.
The construction reuses Mathlib's change of generator and the elementary splitting of
`QuadraticAlgebra R 0 1`, whose generator is idempotent.

When `2` is invertible and `a` is the square of a unit `u`, the roots of
`QuadraticAlgebra R a 0` are `u` and `-u`. Its inverse splitting uses the half-sum and
rescaled half-difference. None of these maps requires a field hypothesis on `R`.
-/

public section

open QuadraticAlgebra

namespace TauCeti.QuadraticAlgebra

/-- The quadratic algebra with an idempotent generator is the product algebra. -/
def algEquivProdOfIdempotent {R : Type*} [CommRing R] :
    QuadraticAlgebra R 0 1 ≃ₐ[R] R × R where
  toFun z := (z.re + z.im, z.re)
  invFun z := ⟨z.2, z.1 - z.2⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' z w := by
    ext <;> simp
    ring
  map_add' z w := by
    ext <;> simp
    ring
  commutes' r := by ext <;> simp

/-- Evaluation of the idempotent-generator algebra at the roots `1` and `0`. -/
@[simp]
theorem _root_.QuadraticAlgebra.algEquivProdOfIdempotent_apply {R : Type*} [CommRing R]
    (z : QuadraticAlgebra R 0 1) :
    algEquivProdOfIdempotent z = (z.re + z.im, z.re) := by
  simp [algEquivProdOfIdempotent]

/-- The inverse idempotent splitting recovers the constant and generator coefficients. -/
@[simp]
theorem algEquivProdOfIdempotent_symm_apply {R : Type*} [CommRing R] (z : R × R) :
    (algEquivProdOfIdempotent (R := R)).symm z = ⟨z.2, z.1 - z.2⟩ := by
  simp [algEquivProdOfIdempotent]

/-- A quadratic algebra splits by evaluation at two roots whose difference is a unit. -/
noncomputable def algEquivProdOfRoots {R : Type*} [CommRing R] {a b : R} (r s : R)
    (h : IsUnit (r - s)) (ha : a = -(r * s)) (hb : b = r + s) :
    QuadraticAlgebra R a b ≃ₐ[R] R × R :=
  (changeGeneratorEquiv 0 1 h.unit s
    (by rw [h.unit_spec, ha]; ring) (by rw [h.unit_spec, hb]; ring)).trans
    algEquivProdOfIdempotent

private theorem algEquivProdOfRoots_omega {R : Type*} [CommRing R] {a b : R} (r s : R)
    (h : IsUnit (r - s)) (ha : a = -(r * s)) (hb : b = r + s) :
    algEquivProdOfRoots r s h ha hb ω = (r, s) := by
  ext <;> simp [algEquivProdOfRoots, Algebra.smul_def]

/-- Splitting evaluates each element at the two roots. -/
@[simp]
theorem _root_.QuadraticAlgebra.algEquivProdOfRoots_apply
    {R : Type*} [CommRing R] {a b : R} (r s : R)
    (h : IsUnit (r - s)) (ha : a = -(r * s)) (hb : b = r + s)
    (z : QuadraticAlgebra R a b) :
    algEquivProdOfRoots r s h ha hb z = (z.re + r * z.im, z.re + s * z.im) := by
  conv_lhs => rw [← re_smul_add_im_smul z]
  ext <;> simp [algEquivProdOfRoots_omega, Algebra.smul_def, mul_comm]

/-- The inverse splitting divides the coordinate difference and interpolation numerator by
the unit root difference. -/
@[simp]
theorem algEquivProdOfRoots_symm_apply {R : Type*} [CommRing R] {a b : R} (r s : R)
    (h : IsUnit (r - s)) (ha : a = -(r * s)) (hb : b = r + s) (z : R × R) :
    (algEquivProdOfRoots r s h ha hb).symm z =
      ⟨(r * z.2 - s * z.1) * (h.unit⁻¹ : Rˣ), (z.1 - z.2) * (h.unit⁻¹ : Rˣ)⟩ := by
  apply (algEquivProdOfRoots r s h ha hb).injective
  rw [AlgEquiv.apply_symm_apply, algEquivProdOfRoots_apply]
  ext <;> dsimp
  · linear_combination -z.1 * h.mul_val_inv
  · linear_combination -z.2 * h.mul_val_inv

/-- With `2` invertible, `QuadraticAlgebra R a 0` with `a = u²` for a unit `u` splits by
sending its square-root generator to `(u, -u)`. -/
noncomputable def algEquivProdOfSq {R : Type*} [CommRing R] [Invertible (2 : R)] {a : R}
    (u : Rˣ) (ha : a = (u : R) ^ 2) : QuadraticAlgebra R a 0 ≃ₐ[R] R × R :=
  algEquivProdOfRoots (u : R) (-(u : R))
    (by convert (isUnit_of_invertible (2 : R)).mul u.isUnit using 1; ring)
    (by rw [ha]; ring) (by simp)

/-- The unit-square specialization evaluates at the two opposite square roots. -/
@[simp]
theorem _root_.QuadraticAlgebra.algEquivProdOfSq_apply
    {R : Type*} [CommRing R] [Invertible (2 : R)] {a : R}
    (u : Rˣ) (ha : a = (u : R) ^ 2) (z : QuadraticAlgebra R a 0) :
    algEquivProdOfSq u ha z = (z.re + (u : R) * z.im, z.re - (u : R) * z.im) := by
  simp [algEquivProdOfSq, sub_eq_add_neg]

/-- The inverse splitting map recovers the half-sum and rescaled half-difference. -/
@[simp]
theorem algEquivProdOfSq_symm_apply {R : Type*} [CommRing R] [Invertible (2 : R)]
    {a : R} (u : Rˣ) (ha : a = (u : R) ^ 2) (z : R × R) :
    (algEquivProdOfSq u ha).symm z =
      ⟨⅟(2 : R) * (z.1 + z.2), (u⁻¹ : Rˣ) * ⅟(2 : R) * (z.1 - z.2)⟩ := by
  apply (algEquivProdOfSq u ha).injective
  rw [AlgEquiv.apply_symm_apply, algEquivProdOfSq_apply]
  ext <;> dsimp
  · simp only [mul_assoc, Units.mul_inv_cancel_left]
    linear_combination -z.1 * (invOf_mul_self (2 : R))
  · simp only [mul_assoc, Units.mul_inv_cancel_left]
    linear_combination -z.2 * (invOf_mul_self (2 : R))

end TauCeti.QuadraticAlgebra

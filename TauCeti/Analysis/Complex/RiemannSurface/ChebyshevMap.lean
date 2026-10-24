/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Polynomial

/-!
# The map `z ↦ 4z(1 - z)` of the Riemann sphere

The polynomial `4X(1 - X)` has degree `2`, so its extension to the Riemann sphere `OnePoint ℂ`,
sending `∞` to `∞`, is a holomorphic map of degree `2`. Its only finite critical point is `1/2`,
with critical value `1`, so its branch values are `1` and `∞`. Its fibre over `0` is the two points
`0` and `1`, where it is unramified; its fibres over `1` and `∞` are the single points `1/2` and
`∞`, where it is ramified of index `2`. So its ramification partitions over `0`, `1` and `∞` are
`[1, 1]`, `[2]` and `[2]`. All of this is read off from the general facts about polynomial maps of
the sphere in `TauCeti.Analysis.Complex.RiemannSurface.Polynomial`.

This is the map `z ↦ (1 - T₂(1 - 2z)) / 2` for the Chebyshev polynomial `T₂ = 2x² - 1`, one of the
basic examples of a Belyi map.

## Main declarations

* `TauCeti.RiemannSurface.degree_onePointMap_four_mul_mul_one_sub`: the map has degree `2`.
* `TauCeti.RiemannSurface.preimage_onePointMap_four_mul_mul_one_sub_zero` and
  `TauCeti.RiemannSurface.preimage_onePointMap_four_mul_mul_one_sub_one`: its fibres are `{0, 1}`
  over `0` and `{1/2}` over `1`.
* `TauCeti.RiemannSurface.localMultiplicity_onePointMap_four_mul_mul_one_sub_coe_of_ne`,
  `TauCeti.RiemannSurface.localMultiplicity_onePointMap_four_mul_mul_one_sub_half` and
  `TauCeti.RiemannSurface.localMultiplicity_onePointMap_four_mul_mul_one_sub_infty`: its local
  multiplicity is `1` away from `1/2` and `∞`, and `2` at those two points.
* `TauCeti.RiemannSurface.branchValues_spherePolynomial_four_mul_X_mul_one_sub_X`: its branch
  values are `1` and `∞`.
-/

public noncomputable section

open OnePoint Polynomial Set

namespace TauCeti.RiemannSurface

/-- The polynomial `4X(1 - X)` has degree `2`. -/
theorem natDegree_four_mul_X_mul_one_sub_X : (C 4 * X * (1 - X) : ℂ[X]).natDegree = 2 := by
  compute_degree!

/-- The polynomial `4X(1 - X)` is nonconstant. -/
theorem natDegree_four_mul_X_mul_one_sub_X_pos : 0 < (C 4 * X * (1 - X) : ℂ[X]).natDegree := by
  rw [natDegree_four_mul_X_mul_one_sub_X]
  exact two_pos

/-- The extension of `4X(1 - X)` to the Riemann sphere is the extension of `z ↦ 4z(1 - z)`. -/
theorem onePointMap_eval_four_mul_X_mul_one_sub_X :
    (OnePoint.map fun z : ℂ ↦ (C 4 * X * (1 - X) : ℂ[X]).eval z) =
      OnePoint.map fun z : ℂ ↦ 4 * z * (1 - z) := by
  simp

/-- The derivative `4 - 8z` of `4z(1 - z)` vanishes only at `1/2`. -/
theorem isRoot_derivative_four_mul_X_mul_one_sub_X_iff {z : ℂ} :
    (derivative (C 4 * X * (1 - X) : ℂ[X])).IsRoot z ↔ z = 2⁻¹ := by
  have hd : (derivative (C 4 * X * (1 - X) : ℂ[X])).eval z = 4 - 8 * z := by
    simp
    ring
  rw [IsRoot.def, hd]
  constructor <;> intro h
  · linear_combination (-1 / 8 : ℂ) * h
  · linear_combination (-8 : ℂ) * h

/-- The map `z ↦ 4z(1 - z)` of the Riemann sphere has degree `2`. -/
@[simp]
theorem degree_onePointMap_four_mul_mul_one_sub :
    degree (OnePoint.map fun z : ℂ ↦ 4 * z * (1 - z)) = 2 := by
  rw [← onePointMap_eval_four_mul_X_mul_one_sub_X,
    degree_onePointMap_eval natDegree_four_mul_X_mul_one_sub_X_pos,
    natDegree_four_mul_X_mul_one_sub_X]

/-- The fibre of `z ↦ 4z(1 - z)` over `0` consists of the two points `0` and `1`. -/
theorem preimage_onePointMap_four_mul_mul_one_sub_zero :
    (OnePoint.map fun z : ℂ ↦ 4 * z * (1 - z)) ⁻¹' {((0 : ℂ) : OnePoint ℂ)} =
      {((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ)} := by
  ext x
  induction x using OnePoint.rec with
  | infty => simp
  | coe z => simp [sub_eq_zero, eq_comm (a := (1 : ℂ))]

/-- The fibre of `z ↦ 4z(1 - z)` over `1` is the single point `1/2`. -/
theorem preimage_onePointMap_four_mul_mul_one_sub_one :
    (OnePoint.map fun z : ℂ ↦ 4 * z * (1 - z)) ⁻¹' {((1 : ℂ) : OnePoint ℂ)} =
      {((2⁻¹ : ℂ) : OnePoint ℂ)} := by
  ext x
  induction x using OnePoint.rec with
  | infty => simp
  | coe z =>
    simp only [mem_preimage, map_some, mem_singleton_iff, coe_eq_coe]
    constructor
    · intro h
      have h' : (2 * z - 1) ^ 2 = 0 := by linear_combination -h
      linear_combination (1 / 2 : ℂ) * (pow_eq_zero_iff two_ne_zero).1 h'
    · rintro rfl
      norm_num

/-- The map `z ↦ 4z(1 - z)` is unramified away from `1/2` and `∞`, in particular at the two points
`0` and `1` over `0`. -/
theorem localMultiplicity_onePointMap_four_mul_mul_one_sub_coe_of_ne {z : ℂ} (hz : z ≠ 2⁻¹) :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ 4 * z * (1 - z)) (z : OnePoint ℂ) = 1 := by
  rw [← onePointMap_eval_four_mul_X_mul_one_sub_X]
  exact localMultiplicity_onePointMap_eval_coe_of_not_isRoot
    natDegree_four_mul_X_mul_one_sub_X_pos (isRoot_derivative_four_mul_X_mul_one_sub_X_iff.not.2 hz)

/-- The map `z ↦ 4z(1 - z)` is ramified of index `2` at `1/2`, the only point over `1`. -/
@[simp]
theorem localMultiplicity_onePointMap_four_mul_mul_one_sub_half :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ 4 * z * (1 - z)) ((2⁻¹ : ℂ) : OnePoint ℂ) = 2 := by
  have h : (C 4 * X * (1 - X) : ℂ[X]) - C ((C 4 * X * (1 - X) : ℂ[X]).eval 2⁻¹) =
      C (-4) * (X - C 2⁻¹) ^ 2 :=
    Polynomial.funext fun z ↦ by
      simp only [eval_sub, eval_mul, eval_C, eval_X, eval_one, eval_pow]
      ring
  rw [← onePointMap_eval_four_mul_X_mul_one_sub_X,
    localMultiplicity_onePointMap_eval_coe natDegree_four_mul_X_mul_one_sub_X_pos, h,
    rootMultiplicity_mul_X_sub_C_pow (by simp), rootMultiplicity_C, zero_add]

/-- The map `z ↦ 4z(1 - z)` is ramified of index `2` at `∞`, the only point over `∞`. -/
@[simp]
theorem localMultiplicity_onePointMap_four_mul_mul_one_sub_infty :
    localMultiplicity (OnePoint.map fun z : ℂ ↦ 4 * z * (1 - z)) (∞ : OnePoint ℂ) = 2 := by
  rw [← onePointMap_eval_four_mul_X_mul_one_sub_X,
    localMultiplicity_onePointMap_eval_infty natDegree_four_mul_X_mul_one_sub_X_pos,
    natDegree_four_mul_X_mul_one_sub_X]

/-- The branch values of `z ↦ 4z(1 - z)` are exactly `1` and `∞`: its only finite critical point
is `1/2`, with critical value `1`. -/
theorem branchValues_spherePolynomial_four_mul_X_mul_one_sub_X :
    (FiniteHolomorphicMap.spherePolynomial natDegree_four_mul_X_mul_one_sub_X_pos).branchValues =
      {((1 : ℂ) : OnePoint ℂ), ∞} := by
  have hd : derivative (C 4 * X * (1 - X) : ℂ[X]) ≠ 0 :=
    derivative_ne_zero.mpr natDegree_four_mul_X_mul_one_sub_X_pos.ne'
  have h : (derivative (C 4 * X * (1 - X) : ℂ[X])).rootSet ℂ = {2⁻¹} :=
    Set.ext fun _ ↦ (mem_rootSet_of_ne hd).trans (by
      rw [coe_aeval_eq_eval]; exact isRoot_derivative_four_mul_X_mul_one_sub_X_iff)
  rw [FiniteHolomorphicMap.branchValues_spherePolynomial
      (by rw [natDegree_four_mul_X_mul_one_sub_X]; exact one_lt_two), criticalValues_def, h,
    image_singleton, image_singleton, pair_comm]
  norm_num

end TauCeti.RiemannSurface

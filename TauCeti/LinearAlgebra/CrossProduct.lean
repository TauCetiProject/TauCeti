/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination

/-!
# Complements on the cross product

Complements to `Mathlib.LinearAlgebra.CrossProduct`. Over a field, two nonzero vectors of `K³`
have vanishing cross product exactly when they are proportional
(`Projectivization.mk_eq_mk_iff_crossProduct_eq_zero`). Over a commutative ring `R`, the
coordinates of `v ⨯₃ w` are the `2 × 2` minors of the matrix with rows `v` and `w`, and when they
vanish and both vectors have a unit coordinate, `v` is a unit multiple of `w`.

Two vectors `u ⨯₃ w` and `v ⨯₃ w` are both orthogonal to `w`, so their cross product is a
multiple of `w`; the coefficient is the triple product of `u`, `v` and `w`. Over a field, the
triple product `x ⬝ᵥ u ⨯₃ v` is the determinant of the matrix with rows `x`, `u` and `v`, so for
linearly independent `u` and `v` it vanishes exactly when `x` lies in the plane they span.

Over a linearly ordered commutative ring, Lagrange's identity
`(u ⨯₃ w) ⬝ᵥ (u ⨯₃ w) = (u ⬝ᵥ u) (w ⬝ᵥ w) - (u ⬝ᵥ w) ^ 2` shows that two vectors of equal squared
length whose cross product has zero square are equal or opposite.

## Main results

* `TauCeti.exists_eq_units_smul_of_crossProduct_eq_zero`: if `v ⨯₃ w = 0` and `v` and `w` each
  have a unit coordinate, then `v = u • w` for a unit `u`.
* `TauCeti.cross_cross_cross_eq_smul`: `(u ⨯₃ w) ⨯₃ (v ⨯₃ w) = (u ⬝ᵥ v ⨯₃ w) • w`.
* `TauCeti.triple_product_eq_zero_iff_mem_span_pair`: for linearly independent `u` and `v`,
  `x ⬝ᵥ u ⨯₃ v = 0` exactly when `x` lies in the span of `u` and `v`.
* `TauCeti.cross_dotProduct_cross_self`: the cross product of two orthonormal vectors is a unit
  vector.
* `TauCeti.eq_or_eq_neg_of_cross_dotProduct_eq_zero`: over a linearly ordered commutative ring, two
  vectors of equal squared length whose cross product has zero square are equal or opposite.

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/AdditionChartGlue.lean`: `ratio_eq_of_minor`
and `isUnit_of_minor`, combined as `exists_eq_units_smul_of_crossProduct_eq_zero`. Here the
vanishing of the `2 × 2` minors is stated as the vanishing of the cross product.
-/

public section

open Matrix

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- Let `v` and `w` be vectors of `R³`, over a commutative ring `R`, each with a unit coordinate.
If `v ⨯₃ w = 0`, then `v` is a unit multiple of `w`. -/
theorem exists_eq_units_smul_of_crossProduct_eq_zero {v w : Fin 3 → R} (h : v ⨯₃ w = 0)
    {k l : Fin 3} (hv : IsUnit (v k)) (hw : IsUnit (w l)) : ∃ u : Rˣ, v = u • w := by
  -- the coordinates of `v ⨯₃ w` are the `2 × 2` minors of the matrix with rows `v` and `w`
  have hvw (a : Fin 3) : v a * w l = v l * w a := by
    simp only [cross_apply, cons_eq_zero_iff] at h
    fin_cases a <;> fin_cases l <;> grind
  -- hence `v = (v l / w l) • w`
  have hu : v = (v l * ↑hw.unit⁻¹) • w := funext fun a ↦ by
    rw [Pi.smul_apply, smul_eq_mul, mul_right_comm, ← hvw a, mul_assoc, hw.mul_val_inv, mul_one]
  -- and `v l / w l` is a unit since `v k = (v l / w l) * w k` is
  exact ⟨(isUnit_of_mul_isUnit_left (congrFun hu k ▸ hv)).unit, hu⟩

/-- The cross product of `u ⨯₃ w` and `v ⨯₃ w` is the multiple of `w` by the triple product of
`u`, `v` and `w`. -/
theorem cross_cross_cross_eq_smul (u v w : Fin 3 → R) :
    (u ⨯₃ w) ⨯₃ (v ⨯₃ w) = (u ⬝ᵥ v ⨯₃ w) • w := by
  ext i
  fin_cases i <;> simp [cross_apply, vecHead, vecTail] <;> ring

/-- For linearly independent vectors `u` and `v` of `K³`, the triple product `x ⬝ᵥ u ⨯₃ v`
vanishes exactly when `x` lies in the plane spanned by `u` and `v`. -/
theorem triple_product_eq_zero_iff_mem_span_pair {K : Type*} [Field K] {u v x : Fin 3 → K}
    (huv : LinearIndependent K ![u, v]) :
    x ⬝ᵥ u ⨯₃ v = 0 ↔ x ∈ Submodule.span K {u, v} := by
  refine ⟨fun h ↦ ?_, fun hx ↦ ?_⟩
  · rw [← range_cons_cons_empty u v ![]]
    by_contra hx
    have hdet := (isUnit_iff_isUnit_det _).1
      ((linearIndependent_row_iff_isUnit (A := of ![x, u, v])).1
        (linearIndependent_finCons.2 ⟨huv, hx⟩))
    have h0 : (of ![x, u, v]).det = 0 := (triple_product_eq_det x u v).symm.trans h
    rw [h0] at hdet
    exact not_isUnit_zero hdet
  · obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
    simp [add_dotProduct, dot_self_cross, dot_cross_self]

/-- The cross product of two orthonormal vectors `u` and `v` of `R³`, over a commutative ring `R`,
satisfies `(u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) = 1`. -/
theorem cross_dotProduct_cross_self {u v : Fin 3 → R} (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (huv : u ⬝ᵥ v = 0) : (u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) = 1 := by
  rw [cross_dot_cross, hu, hv, dotProduct_comm v u, huv]
  ring

/-- Two vectors of `R³` of equal squared length, over a linearly ordered commutative ring `R`
such as `ℝ`, whose cross product has zero square are equal or opposite. -/
theorem eq_or_eq_neg_of_cross_dotProduct_eq_zero [LinearOrder R] [IsStrictOrderedRing R]
    {u w : Fin 3 → R} (h : u ⬝ᵥ u = w ⬝ᵥ w) (huw : (u ⨯₃ w) ⬝ᵥ (u ⨯₃ w) = 0) :
    w = u ∨ w = -u := by
  rw [cross_dot_cross, dotProduct_comm w u] at huw
  -- By Lagrange's identity, the product of the squares of `w - u` and `w + u` is
  -- `4 ((u ⬝ᵥ u) (w ⬝ᵥ w) - (u ⬝ᵥ w) ^ 2) + (u ⬝ᵥ u - w ⬝ᵥ w) ^ 2 = 0`.
  have hprod : ((w - u) ⬝ᵥ (w - u)) * ((w + u) ⬝ᵥ (w + u)) = 0 := by
    simp only [sub_dotProduct, dotProduct_sub, add_dotProduct, dotProduct_add, dotProduct_comm w u]
    linear_combination 4 * huw + (u ⬝ᵥ u - w ⬝ᵥ w) * h
  rcases mul_eq_zero.mp hprod with h | h
  · exact .inl (sub_eq_zero.mp (dotProduct_self_eq_zero.mp h))
  · exact .inr (eq_neg_of_add_eq_zero_left (dotProduct_self_eq_zero.mp h))

end TauCeti

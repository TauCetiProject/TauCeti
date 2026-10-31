/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Antiunitary quaternionic structures

A quaternionic structure on an inner product space `E` is a conjugate-linear isometry
`j : E →ₗᵢ⋆[𝕜] E` with `j (j x) = -x`. On the positive half-spinors `ℂ² = ℍ` of a four-manifold
it is multiplication by the quaternion `j`, and it implements charge conjugation of the
Seiberg–Witten equations.

A conjugate-linear isometry conjugates inner products, so a quaternionic structure moves every
vector to an orthogonal vector of the same length. In dimension two `x` and `j x` therefore span
the space when `x ≠ 0`, and the rank-one operators `x x*` and `(j x)(j x)*` sum to `‖x‖² Id`
(equivalently, for `x ≠ 0` the orthogonal projections onto `x` and `j x` sum to the identity).

The standard quaternionic structure of `ℂ²` is
`TauCeti.Analysis.InnerProductSpace.QuaternionicStructure.Standard`.

## Main results

* `LinearIsometry.inner_map_map_eq_conj`: a conjugate-linear isometry conjugates the inner
  product.
* `LinearIsometry.inner_map_self_eq_zero`: a quaternionic structure moves every vector to an
  orthogonal vector.
* `LinearIsometry.rankOne_self_add_rankOne_map_self`: in dimension two,
  `x x* + (j x)(j x)* = ‖x‖² Id`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
-/

public section

noncomputable section

open InnerProductSpace
open scoped ComplexConjugate InnerProductSpace

namespace LinearIsometry

section Seminormed

variable {𝕜 E E' : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [SeminormedAddCommGroup E'] [InnerProductSpace 𝕜 E']

/-- A conjugate-linear isometry conjugates the inner product: `⟪f x, f y⟫ = conj ⟪x, y⟫`. -/
@[simp]
theorem inner_map_map_eq_conj (f : E →ₗᵢ⋆[𝕜] E') (x y : E) :
    ⟪f x, f y⟫_𝕜 = conj ⟪x, y⟫_𝕜 := by
  -- Polarize: `f` turns `x ∓ I • y` into `f x ± I • f y`, which swaps the imaginary terms.
  have h₁ : f x - (RCLike.I : 𝕜) • f y = f (x + (RCLike.I : 𝕜) • y) := by
    simp [map_add, map_smulₛₗ, sub_eq_add_neg]
  have h₂ : f x + (RCLike.I : 𝕜) • f y = f (x - (RCLike.I : 𝕜) • y) := by
    simp [map_sub, map_smulₛₗ]
  rw [inner_eq_sum_norm_sq_div_four (f x), inner_eq_sum_norm_sq_div_four x, h₁, h₂, ← map_add,
    ← map_sub, norm_map, norm_map, norm_map, norm_map]
  simp only [map_div₀, map_add, map_sub, map_mul, map_pow, RCLike.conj_ofReal, RCLike.conj_I,
    map_ofNat]
  ring

/-- A quaternionic structure `j` moves every vector to an orthogonal vector: `⟪j x, x⟫ = 0`. -/
theorem inner_map_self_eq_zero (j : E →ₗᵢ⋆[𝕜] E) (hj : ∀ x, j (j x) = -x) (x : E) :
    ⟪j x, x⟫_𝕜 = 0 := by
  have h := j.inner_map_map_eq_conj x (j x)
  rw [hj, inner_neg_right, inner_conj_symm] at h
  exact CharZero.neg_eq_self_iff.mp h

/-- A quaternionic structure `j` moves every vector to an orthogonal vector: `⟪x, j x⟫ = 0`. -/
theorem inner_self_map_eq_zero (j : E →ₗᵢ⋆[𝕜] E) (hj : ∀ x, j (j x) = -x) (x : E) :
    ⟪x, j x⟫_𝕜 = 0 :=
  inner_eq_zero_symm.mp (j.inner_map_self_eq_zero hj x)

end Seminormed

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- In dimension two, the rank-one operators of a vector `x` and of its image under a quaternionic
structure `j` sum to `‖x‖² Id`: `x x* + (j x)(j x)* = ‖x‖² Id`. For unit `x` these are the
orthogonal projections onto `x` and `j x`, which then add up to the identity. -/
theorem rankOne_self_add_rankOne_map_self (j : E →ₗᵢ⋆[𝕜] E) (hj : ∀ x, j (j x) = -x)
    (h₂ : Module.finrank 𝕜 E = 2) (x : E) :
    rankOne 𝕜 x x + rankOne 𝕜 (j x) (j x) = (‖x‖ : 𝕜) ^ 2 • ContinuousLinearMap.id 𝕜 E := by
  rcases eq_or_ne x 0 with rfl | hx
  · ext; simp
  -- `x` and `j x` are orthogonal and nonzero, hence a basis; compare both sides on it.
  have hjx : j x ≠ 0 := by rwa [← norm_ne_zero_iff, j.norm_map, norm_ne_zero_iff]
  have hli : LinearIndependent 𝕜 ![x, j x] := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun i ↦ ?_) fun i k hik ↦ ?_
    · fin_cases i <;> simpa
    · fin_cases i <;> fin_cases k <;>
        simp_all [j.inner_map_self_eq_zero hj, j.inner_self_map_eq_zero hj]
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h₂])
  refine ContinuousLinearMap.coe_injective (b.ext fun i ↦ ?_)
  fin_cases i <;>
    simp [b, j.inner_map_self_eq_zero hj, j.inner_self_map_eq_zero hj, inner_self_eq_norm_sq_to_K]

end LinearIsometry

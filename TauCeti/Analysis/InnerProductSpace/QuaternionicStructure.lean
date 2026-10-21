/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Algebra.Quaternion.ComplexMatrix
public import TauCeti.LinearAlgebra.UnitaryGroup

/-!
# Antiunitary quaternionic structures

A quaternionic structure on an inner product space `E` is a conjugate-linear isometry
`j : E →ₗᵢ⋆[𝕜] E` with `j (j x) = -x`. On the positive half-spinors `ℂ² = ℍ` of a four-manifold
it is multiplication by the quaternion `j`, and it implements charge conjugation of the
Seiberg–Witten equations.

A conjugate-linear isometry conjugates inner products, so a quaternionic structure moves every
vector to an orthogonal vector of the same length. In dimension two `x` and `j x` therefore span
the space when `x ≠ 0`, and the two orthogonal projections onto them add up to the identity:
`x x* + (j x)(j x)* = ‖x‖² Id`.

On `ℂ²` the standard quaternionic structure is `j (z₀, z₁) = (-conj z₁, conj z₀)`. It carries a
complex matrix `A` to the conjugate transpose of the adjugate of `A`, which for a unitary matrix
`U` is `conj (det U) • U`. So `j` commutes with `SU(2)` and twists `U(2)` by the inverse
determinant. The matrices commuting with `j` are exactly the real quaternions, embedded by
`Quaternion.toComplexMatrix`.

## Main definitions

* `TauCeti.stdQuaternionicStructure`: the quaternionic structure `(z₀, z₁) ↦ (-conj z₁, conj z₀)`
  of `ℂ²`.

## Main results

* `LinearIsometry.inner_map_map_eq_conj`: a conjugate-linear isometry conjugates the inner
  product.
* `LinearIsometry.inner_map_self_eq_zero`: a quaternionic structure moves every vector to an
  orthogonal vector.
* `LinearIsometry.rankOne_self_add_rankOne_map_self`: in dimension two,
  `x x* + (j x)(j x)* = ‖x‖² Id`.
* `TauCeti.stdQuaternionicStructure_stdQuaternionicStructure`: the standard structure squares
  to `-1`.
* `TauCeti.stdQuaternionicStructure_toEuclideanLin`: `j ∘ A = (star (adjugate A)) ∘ j`.
* `TauCeti.stdQuaternionicStructure_toEuclideanLin_of_mem_unitaryGroup`: for unitary `U`,
  `j ∘ U = conj (det U) • U ∘ j`.
* `TauCeti.stdQuaternionicStructure_toEuclideanLin_of_mem_specialUnitaryGroup`: `j` commutes with
  `SU(2)`.
* `TauCeti.stdQuaternionicStructure_comm_iff_mem_range`: a complex `2 × 2` matrix commutes with
  `j` exactly when it is the matrix of a real quaternion.

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

/-- In dimension two, the orthogonal projections onto a vector and its image under a quaternionic
structure add up to the identity: `x x* + (j x)(j x)* = ‖x‖² Id`. -/
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

namespace TauCeti

open Matrix

/-- The standard quaternionic structure `j (z₀, z₁) = (-conj z₁, conj z₀)` of `ℂ²`. Identifying
`ℂ²` with the quaternions by `(z₀, z₁) ↦ z₀ + z₁ j`, it is left multiplication by `j`. It is a
conjugate-linear isometry squaring to `-1`
(`TauCeti.stdQuaternionicStructure_stdQuaternionicStructure`). -/
def stdQuaternionicStructure : EuclideanSpace ℂ (Fin 2) →ₗᵢ⋆[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun z := !₂[-conj (z 1), conj (z 0)]
  map_add' z w := by
    ext i
    fin_cases i <;> simp [add_comm]
  map_smul' c z := by
    ext i
    fin_cases i <;> simp
  norm_map' z := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, add_comm]

/-- The standard quaternionic structure in coordinates. -/
theorem stdQuaternionicStructure_apply (z : EuclideanSpace ℂ (Fin 2)) :
    stdQuaternionicStructure z = !₂[-conj (z 1), conj (z 0)] :=
  (rfl)

/-- The first coordinate of `j z` is `-conj z₁`. -/
@[simp]
theorem stdQuaternionicStructure_apply_zero (z : EuclideanSpace ℂ (Fin 2)) :
    stdQuaternionicStructure z 0 = -conj (z 1) :=
  (rfl)

/-- The second coordinate of `j z` is `conj z₀`. -/
@[simp]
theorem stdQuaternionicStructure_apply_one (z : EuclideanSpace ℂ (Fin 2)) :
    stdQuaternionicStructure z 1 = conj (z 0) :=
  (rfl)

/-- The standard quaternionic structure squares to `-1`. -/
@[simp]
theorem stdQuaternionicStructure_stdQuaternionicStructure (z : EuclideanSpace ℂ (Fin 2)) :
    stdQuaternionicStructure (stdQuaternionicStructure z) = -z := by
  ext i
  fin_cases i <;> simp

/-- The standard quaternionic structure carries a complex matrix `A` to the conjugate transpose
of its adjugate: `j (A z) = (star (adjugate A)) (j z)`. -/
theorem stdQuaternionicStructure_toEuclideanLin (A : Matrix (Fin 2) (Fin 2) ℂ)
    (z : EuclideanSpace ℂ (Fin 2)) :
    stdQuaternionicStructure (A.toEuclideanLin z) =
      (star A.adjugate).toEuclideanLin (stdQuaternionicStructure z) := by
  ext i
  fin_cases i <;> simp [adjugate_fin_two, mulVec, dotProduct, Fin.sum_univ_two, add_comm]

/-- For a unitary matrix `U`, `j (U z) = conj (det U) • U (j z)`: charge conjugation twists the
standard representation of `U(2)` by the inverse determinant. -/
theorem stdQuaternionicStructure_toEuclideanLin_of_mem_unitaryGroup {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ unitaryGroup (Fin 2) ℂ) (z : EuclideanSpace ℂ (Fin 2)) :
    stdQuaternionicStructure (U.toEuclideanLin z) =
      conj U.det • U.toEuclideanLin (stdQuaternionicStructure z) := by
  rw [stdQuaternionicStructure_toEuclideanLin, adjugate_eq_det_smul_star_of_mem_unitaryGroup hU,
    star_smul, star_star, map_smul, LinearMap.smul_apply, Complex.star_def]

/-- The standard quaternionic structure commutes with `SU(2)`. -/
theorem stdQuaternionicStructure_toEuclideanLin_of_mem_specialUnitaryGroup
    {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ specialUnitaryGroup (Fin 2) ℂ)
    (z : EuclideanSpace ℂ (Fin 2)) :
    stdQuaternionicStructure (U.toEuclideanLin z) =
      U.toEuclideanLin (stdQuaternionicStructure z) := by
  rw [mem_specialUnitaryGroup_iff] at hU
  rw [stdQuaternionicStructure_toEuclideanLin_of_mem_unitaryGroup hU.1, hU.2, map_one, one_smul]

/-- A complex `2 × 2` matrix commutes with the standard quaternionic structure exactly when it is
the matrix of a real quaternion: the complex-linear endomorphisms of `ℂ²` commuting with `j` are
the quaternions. -/
theorem stdQuaternionicStructure_comm_iff_mem_range (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (∀ z, stdQuaternionicStructure (M.toEuclideanLin z) =
      M.toEuclideanLin (stdQuaternionicStructure z)) ↔
      M ∈ Set.range Quaternion.toComplexMatrix := by
  simp_rw [stdQuaternionicStructure_toEuclideanLin]
  rw [Quaternion.mem_range_toComplexMatrix_iff]
  constructor
  · -- Test the commutation against the images of the two basis vectors under `j`.
    intro h
    have h₀ : conj (M 1 1) = M 0 0 := by
      simpa [adjugate_fin_two, mulVec, dotProduct, Fin.sum_univ_two] using congr($(h !₂[0, -1]) 0)
    have h₁ : -conj (M 1 0) = M 0 1 := by
      simpa [adjugate_fin_two, mulVec, dotProduct, Fin.sum_univ_two] using congr($(h !₂[1, 0]) 0)
    exact ⟨by simp [← h₀], by simp [← h₁]⟩
  · rintro ⟨h₁, h₂⟩ z
    ext i
    fin_cases i <;> simp [adjugate_fin_two, mulVec, dotProduct, Fin.sum_univ_two, h₁, h₂]

end TauCeti

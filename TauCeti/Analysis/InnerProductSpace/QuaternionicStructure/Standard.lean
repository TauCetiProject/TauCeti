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
# The standard quaternionic structure of `ℂ²`

On `ℂ²` the standard quaternionic structure is `j (z₀, z₁) = (-conj z₁, conj z₀)`: a
conjugate-linear isometry squaring to `-1`, which is left multiplication by `j` under
`ℂ² = ℍ`. It carries a complex matrix `A` to the conjugate transpose of the adjugate of `A`, which
for a unitary matrix `U` is `conj (det U) • U`. So `j` commutes with `SU(2)` and twists `U(2)` by
the inverse determinant. The matrices commuting with `j` are exactly the real quaternions,
embedded by `Quaternion.toComplexMatrix`.

## Main definitions

* `TauCeti.stdQuaternionicStructure`: the quaternionic structure `(z₀, z₁) ↦ (-conj z₁, conj z₀)`
  of `ℂ²`.

## Main results

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
-/

public section

noncomputable section

open scoped ComplexConjugate

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

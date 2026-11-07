/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Lifting special-linear matrices

A special-linear matrix lifts along a surjective ring homomorphism that reflects units, such as
the quotient map by a nilpotent ideal or by an ideal contained in the Jacobson radical. Lift its
entries arbitrarily; its determinant is then a unit because it maps to one. Scaling one row by
the inverse determinant corrects the lift without changing its image.

Since the correction only rescales one row, it keeps every entry that vanishes in the original
lift; in particular, upper-triangular determinant-one matrices lift to upper-triangular ones.

## Main declarations

* `Matrix.SpecialLinearGroup.exists_map_eq_of_map_eq`: a lift of a determinant-one matrix
  corrects to a determinant-one lift with at least the same vanishing entries.
* `Matrix.SpecialLinearGroup.map_surjective`: a surjective ring homomorphism that reflects units
  is surjective on special-linear groups.
* `Matrix.SpecialLinearGroup.exists_isUpperTriangular_map_eq`: the same holds for
  upper-triangular determinant-one matrices.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 2.
-/

public section

namespace Matrix.SpecialLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {R S : Type*} [CommRing R] [CommRing S]

/-- Along a ring homomorphism that reflects units, a matrix lifting a determinant-one matrix can
be corrected to a determinant-one lift that vanishes wherever the original lift does: its
determinant is a unit, and scaling one row by the inverse determinant changes neither its image
nor its zero entries.

The statement includes the empty index type, where both special-linear groups are trivial. -/
theorem exists_map_eq_of_map_eq (φ : R →+* S) [IsLocalHom φ] (A : SpecialLinearGroup n S)
    (M : Matrix n n R) (hM : M.map φ = A) :
    ∃ N : SpecialLinearGroup n R, map φ N = A ∧
      ∀ i j, M i j = 0 → (N : Matrix n n R) i j = 0 := by
  cases isEmpty_or_nonempty n with
  | inl _ => exact ⟨1, Subsingleton.elim _ _, fun i ↦ isEmptyElim i⟩
  | inr h =>
    obtain ⟨i₀⟩ := h
    have hdet : φ M.det = 1 := by rw [RingHom.map_det, RingHom.mapMatrix_apply, hM, A.prop]
    obtain ⟨u, hu⟩ := (isUnit_map_iff φ M.det).mp (hdet ▸ isUnit_one)
    have hu_inv : φ ↑u⁻¹ = 1 := by simpa [hu, hdet] using congrArg φ u.inv_mul
    let N : Matrix n n R := M.updateRow i₀ ((↑u⁻¹ : R) • M i₀)
    have hNdet : N.det = 1 := by rw [det_updateRow_smul, updateRow_eq_self, ← hu, Units.inv_mul]
    refine ⟨⟨N, hNdet⟩, Subtype.ext <| (map_apply_coe φ ⟨N, hNdet⟩).trans ?_,
      fun i j hij ↦ ?_⟩
    · rw [RingHom.mapMatrix_apply, coe_mk, ← hM]
      ext i j
      rcases eq_or_ne i i₀ with rfl | hi
      · simp [N, hu_inv]
      · simp [N, hi]
    · rcases eq_or_ne i i₀ with rfl | hi
      · simp [N, hij]
      · simp [N, hi, hij]

/-- A surjective ring homomorphism that reflects units induces a surjection on special-linear
groups.

The statement includes the empty index type, where both special-linear groups are trivial. -/
theorem map_surjective (φ : R →+* S) [IsLocalHom φ] (hφ : Function.Surjective φ) :
    Function.Surjective (map (n := n) φ) := fun A ↦ by
  choose m hm using fun i j ↦ hφ (A i j)
  obtain ⟨N, hN, -⟩ := exists_map_eq_of_map_eq φ A (of m) (Matrix.ext hm)
  exact ⟨N, hN⟩

/-- Along a surjective ring homomorphism that reflects units, every upper-triangular
determinant-one matrix lifts to an upper-triangular determinant-one matrix. -/
theorem exists_isUpperTriangular_map_eq [LT n] (φ : R →+* S) [IsLocalHom φ]
    (hφ : Function.Surjective φ) (A : SpecialLinearGroup n S)
    (hA : (A : Matrix n n S).IsUpperTriangular) :
    ∃ N : SpecialLinearGroup n R, (N : Matrix n n R).IsUpperTriangular ∧ map φ N = A := by
  classical
  choose m hm using fun i j ↦ hφ (A i j)
  let M : Matrix n n R := of fun i j ↦ if j < i then 0 else m i j
  have hM : M.map φ = A := by
    ext i j
    by_cases hji : j < i
    · simp [M, hji, hA hji]
    · simp [M, hji, hm]
  obtain ⟨N, hN, hzero⟩ := exists_map_eq_of_map_eq φ A M hM
  -- `IsUpperTriangular` supplies `hji : id j < id i`, which is `j < i` by definition.
  exact ⟨N, fun i j hji ↦ hzero i j (ite_eq_left hji), hN⟩

end Matrix.SpecialLinearGroup

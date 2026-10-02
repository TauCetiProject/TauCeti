/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Lifting special-linear matrices

A special-linear matrix lifts across a quotient by a nilpotent ideal. Lift its entries
arbitrarily; its determinant is then a unit because it is one modulo the ideal. Scaling one row
by the inverse determinant corrects the lift without changing its image.

Since the correction only rescales one row, it keeps every entry that vanishes in the original
lift; in particular, upper-triangular determinant-one matrices lift to upper-triangular ones.

## Main declarations

* `Matrix.SpecialLinearGroup.exists_map_eq_of_map_eq_of_isNilpotent`: a lift of a determinant-one
  matrix corrects to a determinant-one lift with at least the same vanishing entries.
* `Matrix.SpecialLinearGroup.map_quotient_mk_surjective_of_isNilpotent`: entrywise reduction
  modulo a nilpotent ideal is surjective on special-linear groups.
* `Matrix.SpecialLinearGroup.exists_isUpperTriangular_map_eq_of_isNilpotent`: the same holds for
  upper-triangular determinant-one matrices.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 2.
-/

public section

namespace Matrix.SpecialLinearGroup

universe u

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type u} [CommRing R]

/-- A matrix lifting a determinant-one matrix modulo a nilpotent ideal can be corrected to a
determinant-one lift that vanishes wherever the original lift does: its determinant is a unit, and
scaling one row by the inverse determinant changes neither its image nor its zero entries.

The statement includes the empty index type, where both special-linear groups are trivial. -/
theorem exists_map_eq_of_map_eq_of_isNilpotent (I : Ideal R) (hI : IsNilpotent I)
    (A : SpecialLinearGroup n (R ⧸ I)) (M : Matrix n n R)
    (hM : M.map (Ideal.Quotient.mk I) = A) :
    ∃ N : SpecialLinearGroup n R, map (Ideal.Quotient.mk I) N = A ∧
      ∀ i j, M i j = 0 → (N : Matrix n n R) i j = 0 := by
  cases isEmpty_or_nonempty n with
  | inl _ =>
      exact ⟨1, Subsingleton.elim _ _, fun i ↦ isEmptyElim i⟩
  | inr _ =>
      have hdet_map : Ideal.Quotient.mk I M.det = 1 := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply, hM, A.prop]
      have hdet_unit : IsUnit M.det := (IsNilpotent.isUnit_quotient_mk_iff hI).mp (by
        rw [hdet_map]
        exact isUnit_one)
      let u : Rˣ := hdet_unit.unit
      have hu : (u : R) = M.det := hdet_unit.unit_spec
      have hu_inv_map : Ideal.Quotient.mk I (↑(u⁻¹) : R) = 1 := by
        have h := congrArg (Ideal.Quotient.mk I) u.inv_mul
        rw [map_mul, hu, hdet_map, mul_one, map_one] at h
        exact h
      let i₀ : n := Classical.choice inferInstance
      let N : Matrix n n R := M.updateRow i₀ ((↑(u⁻¹) : R) • M i₀)
      have hNdet : N.det = 1 := by
        dsimp only [N]
        rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
        simpa only [hu] using Units.inv_mul u
      have hN_map : N.map (Ideal.Quotient.mk I) = A.1 := by
        ext i j
        rw [← hM]
        simp only [Matrix.map_apply]
        dsimp only [N]
        by_cases hi : i = i₀
        · subst i
          rw [Matrix.updateRow_self, Pi.smul_apply, smul_eq_mul, map_mul, hu_inv_map, one_mul]
        · rw [Matrix.updateRow_apply, ite_eq_right hi]
      refine ⟨⟨N, hNdet⟩, ?_, fun i j hij ↦ ?_⟩
      · apply Subtype.ext
        exact (Matrix.SpecialLinearGroup.map_apply_coe (Ideal.Quotient.mk I) ⟨N, hNdet⟩).trans
          (by simpa only [RingHom.mapMatrix_apply] using hN_map)
      · change N i j = 0
        dsimp only [N]
        by_cases hi : i = i₀
        · subst i
          rw [Matrix.updateRow_self, Pi.smul_apply, hij, smul_zero]
        · rw [Matrix.updateRow_apply, ite_eq_right hi, hij]

/-- Every determinant-one matrix modulo a nilpotent ideal lifts to a determinant-one matrix.

The statement includes the empty index type, where both special-linear groups are trivial. -/
theorem map_quotient_mk_surjective_of_isNilpotent (I : Ideal R) (hI : IsNilpotent I) :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := n) (Ideal.Quotient.mk I)) := by
  intro A
  choose m hm using fun i j ↦ Ideal.Quotient.mk_surjective (A.1 i j)
  obtain ⟨N, hN, -⟩ := exists_map_eq_of_map_eq_of_isNilpotent I hI A (Matrix.of m) (by
    ext i j
    exact hm i j)
  exact ⟨N, hN⟩

/-- Every upper-triangular determinant-one matrix modulo a nilpotent ideal lifts to an
upper-triangular determinant-one matrix. -/
theorem exists_isUpperTriangular_map_eq_of_isNilpotent [LinearOrder n] (I : Ideal R)
    (hI : IsNilpotent I) (A : SpecialLinearGroup n (R ⧸ I))
    (hA : Matrix.IsUpperTriangular (A : Matrix n n (R ⧸ I))) :
    ∃ N : SpecialLinearGroup n R, Matrix.IsUpperTriangular (N : Matrix n n R) ∧
      map (Ideal.Quotient.mk I) N = A := by
  choose m hm using fun i j ↦ Ideal.Quotient.mk_surjective (A.1 i j)
  let M : Matrix n n R := Matrix.of fun i j ↦ if j < i then 0 else m i j
  have hM : M.map (Ideal.Quotient.mk I) = A := by
    ext i j
    by_cases hji : j < i
    · simp only [M, Matrix.map_apply, Matrix.of_apply, ite_eq_left hji, map_zero]
      exact (hA hji).symm
    · simp only [M, Matrix.map_apply, Matrix.of_apply, ite_eq_right hji]
      exact hm i j
  obtain ⟨N, hN, hzero⟩ := exists_map_eq_of_map_eq_of_isNilpotent I hI A M hM
  exact ⟨N, fun i j hji ↦ hzero i j (by simp [M, show j < i from hji]), hN⟩

end Matrix.SpecialLinearGroup

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Lifting upper-triangular invertible matrices

Upper-triangular invertible matrices lift modulo nilpotent ideals. This is the diagonal-block
lifting step for flag stabilizers: lift only the entries on and above the diagonal, then use
nilpotent invariance of invertibility of the determinant.

The entrywise construction follows
`Matrix.SpecialLinearGroup.exists_isUpperTriangular_map_eq_of_isNilpotent` in
`TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Lift`.
-/

public section

namespace TauCeti.UpperTriangularGroup

open Matrix

variable {n : Type*} [Fintype n] [LinearOrder n] {R : Type*} [CommRing R]

/-- Reduction modulo a nilpotent ideal is surjective on the upper-triangular general linear
subgroup, including for an empty index type. -/
theorem map_quotient_mk_surjective_of_isNilpotent (I : Ideal R) (hI : IsNilpotent I) :
    Function.Surjective (map (m := n) (Ideal.Quotient.mk I)) := by
  classical
  intro g
  choose a ha using fun i j ↦ Ideal.Quotient.mk_surjective ((g.val : Matrix n n (R ⧸ I)) i j)
  let M : Matrix n n R := Matrix.of fun i j ↦ if j < i then 0 else a i j
  have hM : M.map (Ideal.Quotient.mk I) = g.val := by
    ext i j
    by_cases hji : j < i
    · simpa only [M, Matrix.map_apply, Matrix.of_apply, ite_eq_left hji, map_zero] using
        ((mem_iff.mp g.2) hji).symm
    · simp only [M, Matrix.map_apply, Matrix.of_apply, ite_eq_right hji, ha]
  have hunit : IsUnit M.det := (IsNilpotent.isUnit_quotient_mk_iff hI).mp (by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
    exact (Matrix.isUnit_iff_isUnit_det _).mp g.val.isUnit)
  let t : GL n R := Matrix.GeneralLinearGroup.mk'' M hunit
  have ht : (t : Matrix n n R) = M := by simp [t]
  refine ⟨⟨t, ?_⟩, ?_⟩
  · rw [mem_iff, ht]
    intro i j hji
    exact ite_eq_left hji
  · apply Subtype.ext
    apply Units.ext
    ext i j
    rw [map_apply, ht]
    exact congrFun (congrFun hM i) j

end TauCeti.UpperTriangularGroup

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Reflection
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Module reflections

This file computes the determinant of Mathlib's `Module.reflection` on a finite free module, and
records that a reflection negates the linear form defining it. Consequently a finite free module
of positive rank has a linear automorphism of determinant `-1`.
-/

public section

universe u v

namespace Module

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {x : M} {f : Module.Dual R M} (h : f x = 2)

/-- The determinant of a module reflection is `-1` on a finite free module. -/
@[simp]
theorem det_reflection [Module.Free R M] [Module.Finite R M] :
    LinearEquiv.det (reflection h) = (-1 : Rˣ) := by
  apply Units.ext
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix (Module.Free.chooseBasis R M)]
  let b := Module.Free.chooseBasis R M
  rw [reflection]
  -- Unfold the reflection into its rank-one perturbation before applying the determinant lemma.
  change Matrix.det (LinearMap.toMatrix b b (LinearMap.id - f.smulRight x)) = -1
  rw [map_sub, LinearMap.toMatrix_id, LinearMap.toMatrix_smulRight]
  -- The rank-one determinant lemma is stated for a column matrix times a row matrix.
  rw [show Matrix.vecMulVec (b.repr x) (f ∘ b) =
      Matrix.replicateCol Unit (b.repr x) * Matrix.replicateRow Unit (f ∘ b) by
      ext i j
      simp [Matrix.mul_apply, Matrix.vecMulVec_apply]]
  rw [sub_eq_add_neg, ← Matrix.neg_mul]
  -- Put the matrix in the exact Schur-complement rank-one form.
  change Matrix.det
    (1 + Matrix.replicateCol Unit (-b.repr x) * Matrix.replicateRow Unit (f ∘ b)) = -1
  rw [Matrix.det_one_add_replicateCol_mul_replicateRow]
  -- The remaining scalar is `1 - f x = -1`.
  change 1 + ∑ i, f (b i) * -(b.repr x i) = -1
  simp_rw [mul_neg, mul_comm (f (b _))]
  rw [Finset.sum_neg_distrib]
  have hsum : ∑ i, b.repr x i * f (b i) = f x := by
    calc
      _ = ∑ i, f ((b.repr x i) • b i) := by
        simp only [map_smul, smul_eq_mul]
      _ = f (∑ i, (b.repr x i) • b i) := by rw [map_sum]
      _ = f x := congrArg f (b.sum_repr x)
  rw [hsum, h]
  ring

include h in
/-- The reflection `Module.preReflection x f` negates the linear form `f` defining it. -/
@[simp]
theorem apply_preReflection (y : M) : f (preReflection x f y) = -f y := by
  rw [preReflection_apply, map_sub, map_smul, smul_eq_mul, h]
  ring

/-- A finite free module of positive rank has a linear automorphism of determinant `-1`, namely
a reflection in a basis vector. -/
theorem exists_det_eq_neg_one [Module.Free R M] [Module.Finite R M] [StrongRankCondition R]
    (hM : 0 < finrank R M) : ∃ g : M ≃ₗ[R] M, LinearEquiv.det g = -1 := by
  let b := Module.finBasis R M
  let i : Fin (finrank R M) := ⟨0, hM⟩
  have hf : (2 • b.coord i) (b i) = 2 := by simp
  exact ⟨reflection hf, det_reflection hf⟩

end Module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Order.Star.Real
import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Nuclear.Maximizers

/-!
# Examples of nuclear-norm trace maximizers

The positive diagonal map with entries `3` and `4` has identity polar factor and maximum `7`.
The row `(1, 0)` has a unique maximizer, while the square matrix with just a `2` in its upper
right entry has multiple maximizers. The latter two examples distinguish full row rank
from rank deficiency on both sides.
-/

open LinearMap Matrix
open scoped InnerProductSpace

namespace TauCeti.UnitarilyInvariantSeminorm

/-- The polar factor of `diag(3, 4)` is the identity, and the maximum value is `7`. -/
example :
    let A := (diagonal ![(3 : ℝ), 4]).toEuclideanLin
    A.polarFactor = LinearMap.id ∧
      nuclear ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) A = 7 := by
  let M := diagonal ![(3 : ℝ), 4]
  let A := M.toEuclideanLin
  have hpos : A.IsPositive := Matrix.isPositive_toEuclideanLin_iff.mpr
    (Matrix.PosSemidef.diagonal fun i ↦ by fin_cases i <;> norm_num)
  have habs : A.operatorAbs = A :=
    (hpos.eq_operatorAbs (by rw [hpos.isSymmetric.adjoint_eq])).symm
  have hker : A.ker = ⊥ := by
    by_contra h
    have hd := LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h
    dsimp only [A, M] at hd
    rw [LinearMap.det_toLpLin, Matrix.det_diagonal, Fin.prod_univ_two] at hd
    norm_num at hd
  have hU : A.polarFactor = LinearMap.id :=
    (A.eq_polarFactor (by simp [habs]) (by simp [hker])).symm
  refine ⟨hU, ?_⟩
  rw [← A.re_trace_operatorAbs, habs, RCLike.re_to_real]
  dsimp only [A, M]
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq, Matrix.trace_diagonal,
    Fin.sum_univ_two]
  norm_num

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The surjective row `(1, 0)` has exactly one maximizing contraction. -/
example (b : OrthonormalBasis (Fin 2) ℝ E) :
    let A := (innerSL ℝ (b 0)).toLinearMap
    ∃! D : E →ₗ[ℝ] ℝ, opNorm ℝ E ℝ D ≤ 1 ∧
      RCLike.re (LinearMap.trace ℝ E (LinearMap.adjoint D ∘ₗ A)) = nuclear ℝ E ℝ A := by
  apply (existsUnique_opNorm_le_one_re_trace_adjoint_comp_eq_nuclear_iff _).mpr
  refine Or.inr fun t ↦ ⟨t • b 0, ?_⟩
  simp [b.norm_eq_one]

/-- The matrix `[[0, 2], [0, 0]]` has multiple maximizing contractions. -/
example (b : OrthonormalBasis (Fin 2) ℝ E) :
    let A := (2 : ℝ) • (InnerProductSpace.rankOne ℝ (b 0) (b 1)).toLinearMap
    ¬ ∃! D : E →ₗ[ℝ] E, opNorm ℝ E E D ≤ 1 ∧
      RCLike.re (LinearMap.trace ℝ E (LinearMap.adjoint D ∘ₗ A)) = nuclear ℝ E E A := by
  let A := (2 : ℝ) • (InnerProductSpace.rankOne ℝ (b 0) (b 1)).toLinearMap
  have hb (i j : Fin 2) : ⟪b i, b j⟫_ℝ = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal i j
  dsimp only
  rw [A.existsUnique_opNorm_le_one_re_trace_adjoint_comp_eq_nuclear_iff, not_or]
  constructor
  · intro hinj
    have h0 : A (b 0) = A 0 := by simp [A, hb]
    have hz := hinj h0
    have hnorm := b.norm_eq_one 0
    simp [hz] at hnorm
  · intro hsurj
    obtain ⟨x, hx⟩ := hsurj (b 1)
    have h := congrArg (inner ℝ (b 1)) hx
    simp [A, real_inner_smul_right, hb] at h

end TauCeti.UnitarilyInvariantSeminorm

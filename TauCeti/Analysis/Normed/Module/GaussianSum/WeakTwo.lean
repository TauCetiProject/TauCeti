/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Analysis.InnerProductSpace.Gram.Factor

/-!
# Factoring finite families under weak quadratic domination

If every continuous linear functional has smaller squared coefficient sum on `x` than on `y`,
the coefficient map for `x` factors through that for `y` by a Euclidean contraction. Taking
the adjoint gives the corresponding identity between vector-valued finite sums. This is the
finite-dimensional factorization used in Gaussian comparison.

The argument follows G. Pisier, *Factorization of Linear Operators and Geometry of Banach
Spaces*, §3, Lemma 3.5, using `ContinuousLinearMap.factorThru` for the contraction.
-/

public section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace TauCeti

variable {ι κ Y : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Weak quadratic domination of finite families gives a Euclidean contraction whose adjoint
transports the synthesis map for `y` to the synthesis map for `x`. No completeness assumption
on the ambient normed space is needed. -/
theorem exists_contraction_of_weakTwo_le (x : ι → Y) (y : κ → Y)
    (h : ∀ f : StrongDual ℝ Y, ∑ i, |f (x i)| ^ 2 ≤ ∑ j, |f (y j)| ^ 2) :
    ∃ D : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι, ‖D‖ ≤ 1 ∧
      ∀ a : EuclideanSpace ℝ ι, (∑ i, a i • x i) = ∑ j, (D.adjoint a) j • y j := by
  let T : StrongDual ℝ Y →L[ℝ] EuclideanSpace ℝ ι :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.apply ℝ ℝ (x i))
  let A : StrongDual ℝ Y →L[ℝ] EuclideanSpace ℝ κ :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ ↦ ℝ)).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.pi (fun j ↦ ContinuousLinearMap.apply ℝ ℝ (y j))
  have hbound (f : StrongDual ℝ Y) : ‖T f‖ ≤ 1 * ‖A f‖ := by
    rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
      EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simpa [T, A, Real.norm_eq_abs] using h f
  refine ⟨T.factorThru A, ContinuousLinearMap.norm_factorThru_le zero_le_one hbound, ?_⟩
  intro a
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2
  intro f
  have hf := ContinuousLinearMap.factorThru_apply_apply ⟨1, hbound⟩ f
  have hadj := (T.factorThru A).adjoint_inner_left (A f) a
  rw [hf] at hadj
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, T, A, map_sum,
    mul_comm] using hadj.symm

end TauCeti

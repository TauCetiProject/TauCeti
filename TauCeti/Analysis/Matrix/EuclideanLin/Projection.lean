/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Lp.Matrix

/-!
# The orthogonal projector onto the column space of a matrix

For a rectangular matrix `B` over `ℝ` or `ℂ` (any `RCLike` field), the orthogonal projector onto
the span of the columns of `B` in Euclidean space is a star projection `P` (self-adjoint and
idempotent) with `P * B = B`, and it factors through `B` as `P = B * M`.

## Main results

* `Matrix.exists_isStarProjection_mul_eq_self_and_eq_mul`: the column-space projector of `B`, a
  star projection `P` with `P * B = B` and `P = B * M` for some `M`.
-/

public section

namespace Matrix

variable {𝕜 n m : Type*} [RCLike 𝕜] [Fintype n] [Fintype m]

/-- **The orthogonal projector onto the column space of `B`**: a star projection `P` with
`P * B = B` and `P = B * M` for some `M`. It is the matrix of the orthogonal projection of
Euclidean space onto the range `K` of `B`, and `M` is the matrix of a linear section of `B` over
`K` composed with the orthogonal projection onto `K`. -/
theorem exists_isStarProjection_mul_eq_self_and_eq_mul (B : Matrix n m 𝕜) :
    ∃ P : Matrix n n 𝕜, ∃ M : Matrix m n 𝕜, IsStarProjection P ∧ P * B = B ∧ P = B * M := by
  classical
  set f := toEuclideanLin B
  set K : Submodule 𝕜 (EuclideanSpace 𝕜 n) := LinearMap.range f
  set P : Matrix n n 𝕜 := (toEuclideanCLM (n := n) (𝕜 := 𝕜)).symm K.starProjection
  have hP : toEuclideanLin P = K.starProjection := by
    rw [← coe_toEuclideanCLM_eq_toEuclideanLin, StarAlgEquiv.apply_symm_apply]
  -- A linear section `s` of `f` over its range `K`.
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  refine ⟨P, toEuclideanLin.symm (s ∘ₗ K.orthogonalProjectionOnto.toLinearMap),
    isStarProjection_starProjection.map toEuclideanCLM.symm, toEuclideanLin.injective ?_,
    toEuclideanLin.injective ?_⟩
  · refine LinearMap.ext fun v => ?_
    rw [toLpLin_mul_same, hP, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      Submodule.starProjection_eq_self_iff.2 (LinearMap.mem_range_self f v)]
  · refine LinearMap.ext fun v => ?_
    have h := congrArg Subtype.val (LinearMap.congr_fun hs (K.orthogonalProjectionOnto v))
    rw [toLpLin_mul_same, hP, LinearEquiv.apply_symm_apply]
    simpa using h.symm

end Matrix

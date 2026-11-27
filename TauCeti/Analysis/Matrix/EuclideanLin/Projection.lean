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

open WithLp

namespace Matrix

variable {𝕜 n m : Type*} [RCLike 𝕜] [Fintype n] [Fintype m]

/-- **The orthogonal projector onto the column space of `B`**: a star projection `P` with
`P * B = B` and `P = B * M` for some `M`. It is the matrix of the orthogonal projection of
Euclidean space onto the range of `B`. -/
theorem exists_isStarProjection_mul_eq_self_and_eq_mul (B : Matrix n m 𝕜) :
    ∃ P : Matrix n n 𝕜, ∃ M : Matrix m n 𝕜, IsStarProjection P ∧ P * B = B ∧ P = B * M := by
  classical
  set K : Submodule 𝕜 (EuclideanSpace 𝕜 n) := LinearMap.range (toEuclideanLin B)
  set P : Matrix n n 𝕜 := (toEuclideanCLM (n := n) (𝕜 := 𝕜)).symm K.starProjection
  have hP : ∀ x : n → 𝕜, P *ᵥ x = ofLp (K.starProjection (toLp 2 x)) := fun x => by
    simpa [P] using (ofLp_toEuclideanCLM P (toLp 2 x)).symm
  have hBK : ∀ v : m → 𝕜, toLp 2 (B *ᵥ v) ∈ K := fun v =>
    ⟨toLp 2 v, by rw [toLpLin_apply, ofLp_toLp]⟩
  have hM : ∀ i, ∃ a : m → 𝕜, B *ᵥ a = P *ᵥ Pi.single i 1 := fun i => by
    obtain ⟨a, ha⟩ := K.starProjection_apply_mem (toLp 2 (Pi.single i 1))
    exact ⟨ofLp a, by rw [hP, ← ha, toLpLin_apply, ofLp_toLp]⟩
  choose a ha using hM
  refine ⟨P, of fun j i => a i j, isStarProjection_starProjection.map toEuclideanCLM.symm,
    ext_iff_mulVec.2 fun v => ?_, ext_of_mulVec_single fun i => ?_⟩
  · rw [← mulVec_mulVec, hP, Submodule.starProjection_eq_self_iff.2 (hBK v), ofLp_toLp]
  · rw [← mulVec_mulVec, ← ha i]
    congr 1
    ext j
    simp

end Matrix

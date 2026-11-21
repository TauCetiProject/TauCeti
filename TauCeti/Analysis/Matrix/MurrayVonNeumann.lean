/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.LinearAlgebra.Matrix.MurrayVonNeumann
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# Murray–von Neumann equivalence of matrix projections over `ℝ` and `ℂ`

Over `𝕜 = ℝ` or `ℂ`, two matrix projections, possibly of different sizes, are Murray–von Neumann
equivalent exactly when they have the same rank (`Matrix.isMurrayVonNeumannEquivalent_iff_rank_eq`).
A projection `p` of rank `r` is the orthogonal projection onto its range, so the columns of an
orthonormal basis of that range form a rectangular matrix `W` with `Wᴴ W = 1_r` and `W Wᴴ = p`
(`IsStarProjection.isMurrayVonNeumannEquivalent_one`). The rank is therefore a complete invariant
of matrix projections over `ℂ` up to equivalence, which is the computation behind
`K₀(Mₙ(ℂ)) = ℤ`.

Over a general star ring equivalent projections still have equal rank
(`Matrix.IsMurrayVonNeumannEquivalent.rank_eq`); the converse uses orthonormal bases.

## References

* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Cambridge University Press (2000), Chapters 2 and 3 (`K₀` of `Mₙ(ℂ)`).
-/

public section

open TauCeti

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]

/-- A matrix projection of rank `r` over `ℝ` or `ℂ` is Murray–von Neumann equivalent to the
identity matrix of size `r`. -/
theorem _root_.IsStarProjection.isMurrayVonNeumannEquivalent_one {p : Matrix m m 𝕜}
    (hp : IsStarProjection p) {r : ℕ} (hr : p.rank = r) :
    IsMurrayVonNeumannEquivalent p (1 : Matrix (Fin r) (Fin r) 𝕜) := by
  classical
  -- `p` acts on Euclidean space as the orthogonal projection onto its range `U`
  set P := toEuclideanCLM (n := m) (𝕜 := 𝕜) p
  obtain ⟨_, hP⟩ :=
    isStarProjection_iff_eq_starProjection_range.mp (hp.map (toEuclideanCLM (n := m) (𝕜 := 𝕜)))
  set U := P.range
  have hU : Module.finrank 𝕜 U = r := by
    rw [← hr, rank_eq_finrank_range_toEuclideanLin, ← coe_toEuclideanCLM_eq_toEuclideanLin]
  -- the columns of `W` form an orthonormal basis of `U`
  let b : OrthonormalBasis (Fin r) 𝕜 U := (stdOrthonormalBasis 𝕜 U).reindex (finCongr hU)
  let W : Matrix m (Fin r) 𝕜 := of fun a k => (b k : EuclideanSpace 𝕜 m) a
  refine ⟨hp, .one _, Wᴴ, ?_, ?_⟩
  · rw [conjTranspose_conjTranspose]
    have hsum : W * Wᴴ = ∑ k, vecMulVec (b k : EuclideanSpace 𝕜 m)
        (star (b k : EuclideanSpace 𝕜 m)) := by
      ext a c
      simp [W, Matrix.mul_apply, vecMulVec_apply, Matrix.sum_apply]
    rw [hsum]
    simp_rw [← InnerProductSpace.symm_toEuclideanLin_rankOne]
    rw [← map_sum, LinearEquiv.symm_apply_eq, ← coe_toEuclideanCLM_eq_toEuclideanLin, hP,
      b.starProjection_eq_sum_rankOne, ContinuousLinearMap.toLinearMap_sum]
  · rw [conjTranspose_conjTranspose]
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply, ← orthonormal_iff_ite.mp b.orthonormal k l,
      Submodule.coe_inner, PiLp.inner_apply]
    simp [W, mul_comm]

/-- Over `ℝ` or `ℂ`, matrix projections of any sizes are Murray–von Neumann equivalent exactly
when they have the same rank. -/
theorem isMurrayVonNeumannEquivalent_iff_rank_eq {p : Matrix m m 𝕜} {q : Matrix n n 𝕜}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsMurrayVonNeumannEquivalent p q ↔ p.rank = q.rank :=
  ⟨IsMurrayVonNeumannEquivalent.rank_eq, fun h =>
    (hp.isMurrayVonNeumannEquivalent_one h).trans (hq.isMurrayVonNeumannEquivalent_one rfl).symm⟩

end Matrix

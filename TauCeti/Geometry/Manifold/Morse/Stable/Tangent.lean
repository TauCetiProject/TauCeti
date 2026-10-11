/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Embedding

/-!
# The stable and unstable manifolds and their tangent spaces

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, `X` a
pseudo-gradient field adapted to `f`, and `x` a critical point of index `k`. The stable manifold
`W^s(x)` is the image of a smooth embedding `ι : L → M` of a real vector space `L` of dimension
`n - k`, sending `0` to `x`, and the unstable manifold `W^u(x)` is the image of a smooth embedding
of a real vector space of dimension `k`.

Read in the preferred chart at `x`, the Hessian of `f` at `x` is a nondegenerate quadratic form `Q`
on `T_x M`. It is positive definite on the tangent space `dι₀(L)` of `W^s(x)` at `x`, and negative
definite on the tangent space of `W^u(x)`. These are the stable and unstable subspaces of the
Hessian, in the form that needs no metric: subspaces of the maximal dimensions `n - k` and `k` on
which the Hessian is definite.

The embedding of `W^s(x)` is the parametrization of
`TauCeti.IsAdaptedPseudoGradient.exists_stableParam`, built from a Morse chart `φ`. The derivative
of `φ` at `x` sends `dι₀ u` back to `u`, a vector of the stable subspace of the chart, and in the
preferred chart `Q v` is the diagonal form `Σᵢ wᵢ cᵢ(dφ v)²` in the coordinates `cᵢ` of the chart
(`TauCeti.MorseChart.hessianQuadraticForm_extChartAt`), which is positive on the nonzero vectors
of the stable subspace. The unstable side follows from the stable side for `-X`, adapted to `-f`.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.exists_isSmoothEmbedding_stableSet`: `W^s(x)` is a smoothly
  embedded vector space of dimension `n - k`, on whose tangent space at `x` the Hessian is positive
  definite.
* `TauCeti.IsAdaptedPseudoGradient.exists_isSmoothEmbedding_unstableSet`: `W^u(x)` is a smoothly
  embedded vector space of dimension `k`, on whose tangent space at `x` the Hessian is negative
  definite.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Section 2.1.
-/

public section

open Manifold Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)
include hX

/-- **The stable manifold is a smoothly embedded vector space, with positive definite Hessian on
its tangent space.** For a critical point `x` of index `k`, the stable manifold `W^s(x)` of the flow
of an adapted pseudo-gradient is the image of a smooth embedding `ι : L → M` of a real vector space
`L` of dimension `n - k`, sending `0` to `x`. The Hessian of `f` at `x`, read in the preferred
chart, is positive on every nonzero vector of the tangent space `dι₀(L)` of `W^s(x)` at `x`. -/
theorem exists_isSmoothEmbedding_stableSet (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
    ∃ L : Submodule ℝ E,
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f x = Module.finrank ℝ E ∧
      ∃ ι : L → M, IsSmoothEmbedding 𝓘(ℝ, L) 𝓘(ℝ, E) ∞ ι ∧
        range ι = hX.flow.stableSet x ∧ ι 0 = x ∧
        ∀ u : L, u ≠ 0 → 0 < hessianQuadraticForm (f ∘ (extChartAt 𝓘(ℝ, E) x).symm)
          (extChartAt 𝓘(ℝ, E) x x) (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E) ι 0 u) := by
  obtain ⟨φ, δ, hemb, hrange, h0, hd⟩ := hX.exists_stableParam hf hx
  refine ⟨φ.stableSubspace, φ.finrank_stableSubspace_add_manifoldMorseIndex, _, hemb, hrange,
    h0, fun u hu ↦ ?_⟩
  have hQ := φ.hessianQuadraticForm_extChartAt
    (mfderiv 𝓘(ℝ, φ.stableSubspace) 𝓘(ℝ, E) (hX.stableParam φ δ) 0 u)
  rw [hd] at hQ
  exact (φ.sum_weight_mul_coord_sq_pos u.2 (by simpa using hu)).trans_eq hQ.symm

/-- **The unstable manifold is a smoothly embedded vector space, with negative definite Hessian on
its tangent space.** For a critical point `x` of index `k` of a Morse function, the unstable
manifold `W^u(x)` of the flow of an adapted pseudo-gradient is the image of a smooth embedding
`ι : L → M` of a real vector space `L` of dimension `k`, sending `0` to `x`. The Hessian of `f` at
`x`, read in the preferred chart, is negative on every nonzero vector of the tangent space `dι₀(L)`
of `W^u(x)` at `x`. -/
theorem exists_isSmoothEmbedding_unstableSet (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
    ∃ L : Submodule ℝ E, Module.finrank ℝ L = manifoldMorseIndex 𝓘(ℝ, E) f x ∧
      ∃ ι : L → M, IsSmoothEmbedding 𝓘(ℝ, L) 𝓘(ℝ, E) ∞ ι ∧
        range ι = hX.flow.unstableSet x ∧ ι 0 = x ∧
        ∀ u : L, u ≠ 0 → hessianQuadraticForm (f ∘ (extChartAt 𝓘(ℝ, E) x).symm)
          (extChartAt 𝓘(ℝ, E) x x) (mfderiv 𝓘(ℝ, L) 𝓘(ℝ, E) ι 0 u) < 0 := by
  -- The unstable manifold of `X` is the stable manifold of `-X`, adapted to `-f`.
  obtain ⟨L, hL, ι, hemb, hrange, h0, hpos⟩ :=
    (hX.neg hf).exists_isSmoothEmbedding_stableSet
      (hf.neg.contMDiff.mdifferentiable (by simp)) (mfderiv_neg_eq_zero_iff.2 hx)
  have hidx := (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hx
    ).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  rw [hX.unstableSet_eq_stableSet_neg hf]
  refine ⟨L, by omega, ι, hemb, hrange, h0, fun u hu ↦ ?_⟩
  have h := hpos u hu
  rw [Pi.neg_comp, hessianQuadraticForm_neg] at h
  exact neg_pos.1 h

end IsAdaptedPseudoGradient

end TauCeti

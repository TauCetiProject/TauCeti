/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Embedding
public import TauCeti.Geometry.Manifold.Instances.OpenBall

/-!
# Stable and unstable manifolds are embedded open discs

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, `X` a
pseudo-gradient field adapted to `f`, and `x` a critical point of index `k`. The unstable manifold
`W^u(x)` is the image of a smooth embedding of the open unit disc of `ℝᵏ`, sending the centre to
`x`, and the stable manifold `W^s(x)` is the image of a smooth embedding of the open unit disc of
`ℝⁿ⁻ᵏ`. In particular, each is diffeomorphic to an open disc.

This follows from their parametrization by vector spaces of dimensions `k` and `n - k`
(`TauCeti.IsAdaptedPseudoGradient.exists_isSmoothEmbedding_unstableSet` and its stable version),
since the open unit disc of `ℝᵐ` is diffeomorphic to `ℝᵐ` (`TauCeti.unitBallDiffeomorph`).

## Main results

* `TauCeti.IsAdaptedPseudoGradient.exists_isSmoothEmbedding_unitBall_stableSet`: `W^s(x)` is an
  embedded open disc of dimension `n - k`.
* `TauCeti.IsAdaptedPseudoGradient.exists_isSmoothEmbedding_unitBall_unstableSet`: `W^u(x)` is an
  embedded open disc of dimension `k`.

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

/-- **The stable manifold is an embedded open disc.** For a critical point `x` of index `k` on a
manifold of dimension `n`, the stable manifold `W^s(x)` of the flow of an adapted pseudo-gradient is
the image of a smooth embedding of the open unit disc of `ℝⁿ⁻ᵏ`, sending the centre to `x`. -/
theorem exists_isSmoothEmbedding_unitBall_stableSet (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
    ∃ ι : unitBallOpens
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ E - manifoldMorseIndex 𝓘(ℝ, E) f x))) → M,
      IsSmoothEmbedding
        𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E - manifoldMorseIndex 𝓘(ℝ, E) f x)))
        𝓘(ℝ, E) ∞ ι ∧
      range ι = hX.flow.stableSet x ∧ ι ⟨0, zero_mem_unitBallOpens _⟩ = x := by
  obtain ⟨L, hL, ι, hι, hrange, hι0⟩ := hX.exists_isSmoothEmbedding_stableSet hf hx
  obtain ⟨ι', hι', hrange', hι'0⟩ := exists_isSmoothEmbedding_unitBall (Nat.eq_sub_of_add_eq hL) hι
  exact ⟨ι', hι', hrange'.trans hrange, hι'0.trans hι0⟩

/-- **The unstable manifold is an embedded open disc.** For a critical point `x` of index `k` of a
Morse function, the unstable manifold `W^u(x)` of the flow of an adapted pseudo-gradient is the
image of a smooth embedding of the open unit disc of `ℝᵏ`, sending the centre to `x`. -/
theorem exists_isSmoothEmbedding_unitBall_unstableSet (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) :
    ∃ ι : unitBallOpens (EuclideanSpace ℝ (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x))) → M,
      IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
        𝓘(ℝ, E) ∞ ι ∧
      range ι = hX.flow.unstableSet x ∧ ι ⟨0, zero_mem_unitBallOpens _⟩ = x := by
  obtain ⟨L, hL, ι, hι, hrange, hι0⟩ := hX.exists_isSmoothEmbedding_unstableSet hf hx
  obtain ⟨ι', hι', hrange', hι'0⟩ := exists_isSmoothEmbedding_unitBall hL hι
  exact ⟨ι', hι', hrange'.trans hrange, hι'0.trans hι0⟩

end IsAdaptedPseudoGradient

end TauCeti

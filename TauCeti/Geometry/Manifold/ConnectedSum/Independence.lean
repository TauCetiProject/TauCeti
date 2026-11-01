/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Congr
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Orientation
import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph

/-!
# The connected sum does not depend on its balls

The connected sum `TauCeti.ConnectedSum e₁ e₂` of two smooth manifolds `M` and `N` modelled on a
finite-dimensional real inner product space `E` is built from two coordinate balls
`e₁ : E → M` and `e₂ : E → N`. This file shows that, for connected summands, its diffeomorphism
type depends on the balls only through their orientations at the centres: if `e₁` and `e₁'`
preserve the same orientations of `E` and `M` at `0`, and `e₂` and `e₂'` preserve the same
orientations of `E` and `N` at `0`, then the connected sum along `e₁` and `e₂` is diffeomorphic
to the connected sum along `e₁'` and `e₂'`
(`TauCeti.ConnectedSum.nonempty_diffeomorph_of_isOrientationPreservingAt`). The centres of the
balls are arbitrary.

By the ambient disc theorem on a connected oriented manifold
(`TauCeti.SmoothEmbedding.exists_diffeotopy_eqOn_of_isOrientationPreservingAt`, in the form
`TauCeti.SmoothEmbedding.exists_diffeomorph_comp_eventuallyEq`), `e₁'` is `e₁` followed by a
diffeomorphism of `M` near `0`, and likewise for `e₂'` and `e₂`. A connected sum depends on its
balls only through their germs at the centres, up to diffeomorphisms of the summands
(`TauCeti.ConnectedSum.nonempty_diffeomorph_of_eventuallyEq`).

For the oriented connected sum one ball preserves and the other reverses the orientations, that
is, `e₂` preserves the orientation of `E` and the opposite of the orientation of `N`; this is the
case of the theorem with the opposite orientation on `N`.

## Main results

* `TauCeti.ConnectedSum.nonempty_diffeomorph_of_isOrientationPreservingAt`: connected sums of
  connected manifolds along balls with the same orientation behaviour at their centres are
  diffeomorphic.

## References

* A. Kosinski, *Differential Manifolds*, Academic Press (1993), Chapter VI, Section 1.
* R. Palais, *Extending diffeomorphisms*, Proc. Amer. Math. Soc. 11 (1960), 274–277.
* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, §6, Theorem 6.6.
-/

public section

noncomputable section

open Set Filter Topology Metric
open scoped Manifold ContDiff

namespace TauCeti.ConnectedSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [SigmaCompactSpace M] [PreconnectedSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {N : Type*} [TopologicalSpace N] [T2Space N] [SigmaCompactSpace N] [PreconnectedSpace N]
  [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
  {ι : Type*} [Fintype ι]

/-- **The connected sum does not depend on its balls.** Let `M` and `N` be connected, Hausdorff,
σ-compact smooth manifolds without boundary modelled on a finite-dimensional real inner product
space `E`, with orientations `oM` and `oN`. Let `e₁, e₁' : E → M` be coordinate balls which
preserve the orientations `o₁` of `E` and `oM` at `0`, and `e₂, e₂' : E → N` coordinate balls which
preserve the orientations `o₂` of `E` and `oN` at `0`, all of them open embeddings and smooth local
diffeomorphisms. Then the connected sum along `e₁` and `e₂` is diffeomorphic to the connected sum
along `e₁'` and `e₂'`. -/
theorem nonempty_diffeomorph_of_isOrientationPreservingAt {e₁ e₁' : E → M} {e₂ e₂' : E → N}
    (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂) (h₁' : IsOpenEmbedding e₁')
    (h₂' : IsOpenEmbedding e₂') (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₁)
    (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₂)
    (d₁' : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₁')
    (d₂' : IsLocalDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e₂')
    (o₁ o₂ : Manifold.Orientation 𝓘(ℝ, E) E ι) (oM : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (oN : Manifold.Orientation 𝓘(ℝ, E) N ι) (hf₁ : o₁.IsOrientationPreservingAt oM e₁ 0)
    (hf₁' : o₁.IsOrientationPreservingAt oM e₁' 0) (hf₂ : o₂.IsOrientationPreservingAt oN e₂ 0)
    (hf₂' : o₂.IsOrientationPreservingAt oN e₂' 0) :
    letI := chartedSpace (H := E) h₁ h₂
    letI := chartedSpace (H := E) h₁' h₂'
    Nonempty (ConnectedSum e₁ e₂ ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ ConnectedSum e₁' e₂') := by
  -- The balls as bundled smooth embeddings agree near `0` after diffeomorphisms of the summands.
  obtain ⟨φ, hφ⟩ := SmoothEmbedding.exists_diffeomorph_comp_eventuallyEq
    (SmoothEmbedding.id.compLocalDiffeomorph e₁ d₁ h₁.isEmbedding)
    (SmoothEmbedding.id.compLocalDiffeomorph e₁' d₁' h₁'.isEmbedding) o₁ oM (by simpa using hf₁)
    (by simpa using hf₁')
  obtain ⟨ψ, hψ⟩ := SmoothEmbedding.exists_diffeomorph_comp_eventuallyEq
    (SmoothEmbedding.id.compLocalDiffeomorph e₂ d₂ h₂.isEmbedding)
    (SmoothEmbedding.id.compLocalDiffeomorph e₂' d₂' h₂'.isEmbedding) o₂ oN (by simpa using hf₂)
    (by simpa using hf₂')
  exact nonempty_diffeomorph_of_eventuallyEq φ ψ (by simpa using hφ) (by simpa using hψ)
    h₁ h₂ h₁' h₂' d₁ d₂ d₁' d₂'

end TauCeti.ConnectedSum

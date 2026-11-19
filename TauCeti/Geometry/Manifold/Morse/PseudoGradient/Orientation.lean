/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Flow
public import TauCeti.Geometry.Manifold.Orientation.Family

/-!
# The flow of an adapted pseudo-gradient preserves orientations

Let `X` be a pseudo-gradient adapted to a Morse function on a compact boundaryless manifold `M`.
Its flow is a smooth family of diffeomorphisms of `M` indexed by the connected space `ℝ`, whose
time-`0` map is the identity. So every time-`t` map preserves every orientation of `M`, at every
point (`TauCeti.IsAdaptedPseudoGradient.isOrientationPreservingAt_flow`).
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

/-- **The flow of an adapted pseudo-gradient preserves every orientation** of `M`, at every time
and every point. -/
theorem isOrientationPreservingAt_flow (hX : IsAdaptedPseudoGradient f X) {ι : Type*}
    [Fintype ι] (o : Manifold.Orientation 𝓘(ℝ, E) M ι) (t : ℝ) (y : M) :
    o.IsOrientationPreservingAt o (hX.flow t) y := by
  -- Every time-`s` map is a diffeomorphism, so the flow is a smooth family with invertible slice
  -- derivatives, and its time-`0` slice is the identity.
  have h := Manifold.Orientation.isOrientationPreservingAt_family_iff o o
    (hX.contMDiff_flow_uncurry.of_le (by simp)) y
    (fun s ↦ by
      have hs : (fun z ↦ hX.flow s z) = hX.flowDiffeomorph s :=
        funext fun z ↦ (hX.flowDiffeomorph_apply s z).symm
      exact hs ▸ (hX.flowDiffeomorph s).isInvertible_mfderiv (x := y) (by simp)) t 0
  simp only [Flow.map_zero] at h
  exact h.2 (Manifold.Orientation.isOrientationPreservingAt_id o y)

end IsAdaptedPseudoGradient

end TauCeti

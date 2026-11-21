/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Diffeomorph
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Local.Basic
import TauCeti.Geometry.Manifold.Flow.Diffeomorph

/-!
# Pseudo-gradient flows under diffeomorphisms

Let `σ : M → M'` be a diffeomorphism between compact boundaryless manifolds, and `X`, `X'`
pseudo-gradients adapted to functions `f` on `M` and `f'` on `M'` which `σ` intertwines:
`dσ (X y) = X' (σ y)`. The image under `σ` of an orbit of `X` is an integral curve of `X'`, so `σ`
conjugates the flows, `Φ'_t ∘ σ = σ ∘ Φ_t`, and carries the stable and unstable manifolds of `X`
to those of `X'`. In the pullback of a Morse chart along `σ`, the linear flow is that of the chart.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.flow_apply_diffeomorph`: the diffeomorphism conjugates the
  flows.
* `TauCeti.IsAdaptedPseudoGradient.preimage_unstableSet_diffeomorph`,
  `TauCeti.IsAdaptedPseudoGradient.preimage_stableSet_diffeomorph`: it carries unstable and stable
  manifolds to those of `X'`.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E M']
  {f : M → ℝ} {f' : M' → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {X' : (x : M') → TangentSpace 𝓘(ℝ, E) x} {σ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M'}
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E) ∞ M']

/-- The linear flow of the pullback is the linear flow of `φ`. -/
@[simp]
theorem MorseChart.pullback_linearFlow (hf : f' ∘ σ = f) {x : M} (φ : MorseChart E f' (σ x)) :
    (φ.pullback hf).linearFlow = φ.linearFlow := by
  ext t z i
  simp

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M] [CompactSpace M'] [T2Space M']
  (hX : IsAdaptedPseudoGradient f X) (hX' : IsAdaptedPseudoGradient f' X')
  (hσX : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ y (X y) = X' (σ y))

include hσX

/-- **A diffeomorphism intertwining two pseudo-gradients conjugates their flows**:
`Φ'_t (σ y) = σ (Φ_t y)`. This is `Diffeomorph.apply_flowOf` for the global flows. -/
theorem flow_apply_diffeomorph (t : ℝ) (y : M) : hX'.flow t (σ y) = σ (hX.flow t y) := by
  rw [hX.flow_apply, hX'.flow_apply, ← flowOf_apply, ← flowOf_apply]
  exact (σ.apply_flowOf (by simp) (hX'.contMDiff.of_le (by simp)) hσX t y).symm

/-- **`σ` carries unstable manifolds to unstable manifolds**: `W^u(p) = σ⁻¹ (W'^u(σ p))`. -/
theorem preimage_unstableSet_diffeomorph (p : M) :
    σ ⁻¹' hX'.flow.unstableSet (σ p) = hX.flow.unstableSet p := by
  ext y
  exact σ.toHomeomorph.isInducing.map_mem_unstableSet_iff fun t z ↦
    (flow_apply_diffeomorph hX hX' hσX t z).symm

/-- **`σ` carries stable manifolds to stable manifolds**: `W^s(q) = σ⁻¹ (W'^s(σ q))`. -/
theorem preimage_stableSet_diffeomorph (q : M) :
    σ ⁻¹' hX'.flow.stableSet (σ q) = hX.flow.stableSet q := by
  ext y
  exact σ.toHomeomorph.isInducing.map_mem_stableSet_iff fun t z ↦
    (flow_apply_diffeomorph hX hX' hσX t z).symm

end IsAdaptedPseudoGradient

end TauCeti

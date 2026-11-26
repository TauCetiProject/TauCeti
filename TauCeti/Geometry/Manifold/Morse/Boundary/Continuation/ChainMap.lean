/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.BrokenPair
public import TauCeti.Geometry.Manifold.Morse.Boundary.Pair.ChainMap

/-!
# The mod-two continuation map is a chain map

Let `V` be a smooth continuation field on `M × ℝ` at rate `C > 0` from a Morse–Smale
pseudo-gradient `X₀` adapted to a Morse function `f₀` to a Morse–Smale pseudo-gradient `X₁`
adapted to a Morse function `f₁`, on a compact boundaryless manifold `M`, and suppose that the
continuation is transverse (`TauCeti.IsTransverseContinuation`). This file proves that the mod-two
continuation map `Φ = TauCeti.morseContinuationMap f₀ hf₁ V` commutes with the Morse boundaries,
`∂₁ ∘ Φ = Φ ∘ ∂₀`
(`TauCeti.IsTransverseContinuation.morseBoundary_comp_morseContinuationMap`), so that it is the
continuation morphism `TauCeti.morseContinuationHom` of mod-two Morse chain complexes and induces a
map on mod-two Morse homology.

The proof puts together two results. For all sufficiently negative `a` and sufficiently positive
`b`, with `Ψ` the transition diffeomorphism of the slab from `a` to `b`
(`TauCeti.continuationTransition`):

* the pair `(X₀, Ψ^* X₁)` is a Morse–Smale pair
  (`TauCeti.isTransverseContinuation_iff_eventually_isMorseSmalePair`), and `Φ` commutes with the
  Morse boundaries exactly when the configurations of that pair broken at the source and at the
  target are evenly many in total between any two critical points
  (`TauCeti.IsTransverseContinuation.eventually_morseBoundary_comp_morseContinuationMap_eq_iff`);
* for any Morse–Smale pair of Morse–Smale pseudo-gradients adapted to Morse functions, these broken
  configurations are the ends of the compactified one-dimensional intersections of unstable and
  stable manifolds, hence evenly many (in the namespace
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmalePair`,
  `even_ncard_morseSourceBrokenPairSet_add_ncard_morseTargetBrokenPairSet`).

The pullback `Ψ^* X₁` is a Morse–Smale pseudo-gradient adapted to the Morse function `f₁ ∘ Ψ`,
whose critical points are the images under `Ψ⁻¹` of those of `f₁`
(`TauCeti.criticalPointsEquivOfComp`), so the second result applies at `Ψ⁻¹ r` for every critical
point `r` of `f₁`. Through the chain-map criterion of
`TauCeti.IsTransverseContinuation.morseBoundary_comp_morseContinuationMap_eq_iff`, the broken
continuation trajectories themselves come in pairs (the last theorem of this file, in the namespace
`TauCeti.IsTransverseContinuation`).

## Main results

In the namespace `TauCeti.IsTransverseContinuation`:

* `morseBoundary_comp_morseContinuationMap`: the mod-two continuation map of a transverse
  continuation commutes with the Morse boundaries.
* `even_ncard_morseSourceBrokenContinuationSet_add_ncard_morseTargetBrokenContinuationSet`: between
  any two critical points, the continuation trajectories broken at the source and at the target are
  evenly many in total.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1 (the continuation map is a chain map, by counting the
  ends of the one-dimensional moduli spaces of continuation trajectories).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open Filter
open scoped ContDiff Manifold

namespace TauCeti

namespace IsTransverseContinuation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {C : ℝ}
  {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}
  {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  (hT : IsTransverseContinuation C V hX₀ hX₁) (hV : IsContinuationField X₀ X₁ C V) (hC : 0 < C)
  (hVs : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent ∞
    fun z ↦ (⟨z, V z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))
  (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
  (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
include hT hV hC hVs h₀ h₁ hf₀ hf₁

/-- **The mod-two continuation map is a chain map.** For a transverse smooth continuation field at
rate `C > 0` between Morse–Smale pseudo-gradients adapted to Morse functions on a compact
boundaryless manifold, the mod-two continuation map commutes with the Morse boundaries:
`∂₁ ∘ Φ = Φ ∘ ∂₀`. So `TauCeti.morseContinuationHom` applies to it, and it induces a map on mod-two
Morse homology. -/
theorem morseBoundary_comp_morseContinuationMap :
    h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ V =
      morseContinuationMap f₀ hf₁ V ∘ₗ h₀.morseBoundary hf₀ := by
  obtain ⟨a, ha⟩ := (((isTransverseContinuation_iff_eventually_isMorseSmalePair hVs).1 hT).and
    (hT.eventually_morseBoundary_comp_morseContinuationMap_eq_iff hV hC hVs h₀ h₁ hf₀ hf₁)).exists
  obtain ⟨b, hΨ, hiff⟩ := (ha.1.and ha.2).exists
  set Ψ := continuationTransition C hVs a b
  refine hiff.2 fun p r ↦ ?_
  -- The pulled-back pseudo-gradient is Morse–Smale and adapted to the Morse function `f₁ ∘ Ψ`,
  -- whose critical points are the preimages of those of `f₁`.
  have h₁' := h₁.pullback (hX := hX₁.mpullback Ψ) (Ψ.mfderiv_apply_mpullback (by simp) X₁)
  simpa only [coe_criticalPointsEquivOfComp_symm_apply] using
    hΨ.even_ncard_morseSourceBrokenPairSet_add_ncard_morseTargetBrokenPairSet h₀ h₁' hf₀
      (hf₁.comp_isLocalDiffeomorph Ψ.isLocalDiffeomorph) p ((criticalPointsEquivOfComp rfl).symm r)

/-- **Broken continuation trajectories come in pairs.** For a transverse smooth continuation field
at rate `C > 0` between Morse–Smale pseudo-gradients adapted to Morse functions on a compact
boundaryless manifold, between any critical point `p` of `f₀` and any critical point `r` of `f₁`,
the continuation trajectories broken at the source and at the target are evenly many in total. -/
theorem even_ncard_morseSourceBrokenContinuationSet_add_ncard_morseTargetBrokenContinuationSet
    (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₁) :
    Even ((morseSourceBrokenContinuationSet f₁ V hX₀ p r).ncard +
      (morseTargetBrokenContinuationSet f₀ V hX₁ p r).ncard) :=
  (hT.morseBoundary_comp_morseContinuationMap_eq_iff hV hC hVs h₀ h₁ hf₀ hf₁).1
    (hT.morseBoundary_comp_morseContinuationMap hV hC hVs h₀ h₁ hf₀ hf₁) p r

end IsTransverseContinuation

end TauCeti

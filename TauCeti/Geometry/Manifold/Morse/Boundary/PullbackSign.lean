/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Diffeomorph
public import TauCeti.Geometry.Manifold.Morse.Boundary.FundamentalChain
import TauCeti.LinearAlgebra.Orientation.Basic

/-!
# Signs of orientation data pulled back along a diffeomorphism

Let `σ : M → M'` be a diffeomorphism between compact boundaryless manifolds, `f` and `f'` Morse
functions with `f' ∘ σ = f`, and `X`, `X'` pseudo-gradients adapted to `f` and `f'` which `σ`
intertwines. Orientation data `𝔬'` for `(f', X')` pull back to orientation data for `(f, X)`
(`TauCeti.MorseOrientation.pullback`). This file compares the signs of the integral Morse complex
for the two:

* the augmentation signs agree (`TauCeti.MorseOrientation.augmentationSign_pullback`), so the
  bijection of critical points induced by `σ` intertwines the augmentations
  (`TauCeti.MorseOrientation.signedMorseAugmentation_comp_domLCongr`);
* the fundamental signs agree when `σ` preserves the orientations of the manifolds
  (`TauCeti.IsAdaptedPseudoGradient.fundamentalSign_pullback`): the derivative of `σ` carries the
  unstable frames of the pullback to those of `X'`.

## Main results

* `TauCeti.MorseOrientation.augmentationSign_pullback`: augmentation signs pull back.
* `TauCeti.MorseOrientation.signedMorseAugmentation_comp_domLCongr`: the augmentations are natural
  under diffeomorphisms.
* `TauCeti.IsAdaptedPseudoGradient.fundamentalSign_pullback`: fundamental signs pull back along
  orientation-preserving diffeomorphisms.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations of the descending manifolds).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients).
-/

public section

open Module

open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(ℝ, E) ∞ M']
  [CompactSpace M'] [T2Space M']
  {f : M → ℝ} {f' : M' → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {X' : (x : M') → TangentSpace 𝓘(ℝ, E) x} {σ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M'}
  (hf : f' ∘ σ = f) (hσX : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ y (X y) = X' (σ y))
  (𝔬' : MorseOrientation f' X')

omit [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M] [CompactSpace M'] [T2Space M'] in
/-- **Augmentation signs pull back.** The augmentation sign of the orientation data pulled back
along `σ` at a critical point `p` is the augmentation sign of `𝔬'` at `σ p`. -/
@[simp]
theorem MorseOrientation.augmentationSign_pullback (p : criticalPoints 𝓘(ℝ, E) f) :
    (𝔬'.pullback hf hσX).augmentationSign p =
      𝔬'.augmentationSign (criticalPointsEquivOfComp hf p) := by
  have hind : manifoldMorseIndex 𝓘(ℝ, E) f p =
      manifoldMorseIndex 𝓘(ℝ, E) f' (criticalPointsEquivOfComp hf p) :=
    (𝔬'.chart (criticalPointsEquivOfComp hf p)).manifoldMorseIndex_eq_of_comp hf
  by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 0
  · rw [augmentationSign_of_morseIndex_eq_zero _ hp,
      augmentationSign_of_morseIndex_eq_zero _ (hind ▸ hp), pullback_orientation]
    -- Bases of the zero space indexed by an empty type agree.
    rw [show Module.finBasisOfFinrankEq ℝ _
        ((𝔬'.pullback hf hσX).chart p).finrank_negativeWeight_fun =
        (Module.finBasisOfFinrankEq ℝ _
          (𝔬'.chart (criticalPointsEquivOfComp hf p)).finrank_negativeWeight_fun).reindex
          (finCongr hind.symm) from
        Module.Basis.eq_of_apply_eq fun i ↦ absurd i.isLt (by omega)]
    exact congrArg _ (Orientation.signBasis_reindex _ _ _)
  · rw [augmentationSign_of_morseIndex_ne_zero _ hp,
      augmentationSign_of_morseIndex_ne_zero _ (hind ▸ hp)]

omit [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M] [CompactSpace M'] [T2Space M'] in
/-- **The augmentations are natural**: the bijection between the critical points of `f` and of
`f'` induced by `σ` intertwines the augmentation of the pulled-back orientation data with that of
`𝔬'`, over every ring of coefficients. -/
theorem MorseOrientation.signedMorseAugmentation_comp_domLCongr (R : Type*) [Ring R] :
    𝔬'.signedMorseAugmentation R ∘ₗ
        (Finsupp.domLCongr (criticalPointsEquivOfComp hf)).toLinearMap =
      (𝔬'.pullback hf hσX).signedMorseAugmentation R :=
  Finsupp.lhom_ext fun p a ↦ by
    simp [MorseOrientation.augmentationSign_pullback]

variable {hX : IsAdaptedPseudoGradient f X} {hX' : IsAdaptedPseudoGradient f' X'}

/-- **Fundamental signs pull back along orientation-preserving diffeomorphisms.** If `σ` carries the
orientation `oM` of `M` to the orientation `oM'` of `M'` at a critical point `p` of `f`, the
fundamental sign of the orientation data pulled back along `σ` at `p`, for `oM`, is the fundamental
sign of `𝔬'` at `σ p`, for `oM'`: the derivative of `σ` at `p` carries the unstable frame of the
pullback at `p` to the unstable frame of `X'` at `σ p`. -/
theorem IsAdaptedPseudoGradient.fundamentalSign_pullback (hf' : IsMorse 𝓘(ℝ, E) f')
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E)))
    (oM' : Manifold.Orientation 𝓘(ℝ, E) M' (Fin (finrank ℝ E))) {p : criticalPoints 𝓘(ℝ, E) f}
    (hσ : oM.IsOrientationPreservingAt oM' σ p) :
    hX.fundamentalSign (𝔬'.pullback hf hσX) oM p =
      hX'.fundamentalSign 𝔬' oM' (criticalPointsEquivOfComp hf p) := by
  classical
  set p' := criticalPointsEquivOfComp hf p
  have hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f' p' :=
    (𝔬'.chart p').manifoldMorseIndex_eq_of_comp hf
  by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E
  · have hp' : manifoldMorseIndex 𝓘(ℝ, E) f' p' = finrank ℝ E := hind ▸ hp
    rw [fundamentalSign_of_morseIndex_eq hp, fundamentalSign_of_morseIndex_eq hp']
    refine if_congr ?_ rfl rfl
    obtain ⟨e, he, hmap⟩ := (Manifold.Orientation.isOrientationPreservingAt_iff oM oM' σ p).1 hσ
    rw [← (Orientation.map _ e.toLinearEquiv).injective.eq_iff, hmap, unstableOrientation_def,
      unstableOrientation_def, ← Orientation.map_trans, MorseOrientation.pullback_orientation]
    -- The coordinates of negative weight of the pulled-back chart are those of the chart of `𝔬'`
    -- only up to unfolding `MorseChart.pullback_weight`, so the two rewrites below match up to
    -- definitional equality.
    erw [Orientation.reindex_finCongr_reindex_finCongr]
    -- The derivative of `σ` carries the unstable frame of the pullback to that of `X'`.
    have hF : (LinearEquiv.ofBijective
        (hX.unstableFrame ((𝔬'.pullback hf hσX).chart p) p).toLinearMap
        (bijective_unstableFrame_self (hX := hX) (𝔬'.pullback hf hσX) hp)).trans e.toLinearEquiv =
        LinearEquiv.ofBijective (hX'.unstableFrame (𝔬'.chart p') p').toLinearMap
          (bijective_unstableFrame_self (hX := hX') 𝔬' hp') := by
      refine LinearEquiv.ext fun c ↦ ?_
      rw [LinearEquiv.trans_apply, ContinuousLinearEquiv.coe_toLinearEquiv,
        ← ContinuousLinearEquiv.coe_coe, he]
      exact mfderiv_unstableFrame_pullback hf hX hX' hσX (𝔬'.coord_mfderiv_chart p') hf'
        (hX.mem_unstableSet_inter_stableSet_self
          (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property)).1 c
    erw [hF]
    rfl
  · have hp' : manifoldMorseIndex 𝓘(ℝ, E) f' p' ≠ finrank ℝ E := hind ▸ hp
    rw [fundamentalSign_of_morseIndex_ne hp, fundamentalSign_of_morseIndex_ne hp']

end TauCeti

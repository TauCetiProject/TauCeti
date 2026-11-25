/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Transverse
public import TauCeti.Geometry.Manifold.Morse.Boundary.Diffeomorph
public import TauCeti.Geometry.Manifold.Morse.Boundary.Pair.Commutation

/-!
# Broken continuation trajectories are broken configurations of a transported pair

Let `V` be a smooth continuation field on `M × ℝ` from a pseudo-gradient `X₀` adapted to `f₀` to
a pseudo-gradient `X₁` adapted to `f₁`, at rate `C > 0` (`TauCeti.IsContinuationField`), on a
compact boundaryless manifold `M`. The mod-two continuation map commutes with the Morse boundaries
exactly when, between any two critical points `p` of `f₀` and `r` of `f₁`, the continuation
trajectories broken at the source (`TauCeti.morseSourceBrokenContinuationSet`: a trajectory of
`X₀` from `p` to `p'` followed by a continuation trajectory from `p'` to `r`) and those broken at
the target (`TauCeti.morseTargetBrokenContinuationSet`: a continuation trajectory from `p` to `q'`
followed by a trajectory of `X₁` from `q'` to `r`) are evenly many in total
(`TauCeti.IsTransverseContinuation.morseBoundary_comp_morseContinuationMap_eq_iff`).

For a very negative time `a` and a very positive time `b`, with `Φ` the transition diffeomorphism
of the slab from `a` to `b` (`TauCeti.continuationTransition`) and `Ψ` the one from the middle
level to `a`, the continuation trajectories from `p` to `q` are recorded by the points of
`W^u_{X₀}(p) ∩ W^s_{Φ^* X₁}(Φ⁻¹ q)`
(`TauCeti.IsContinuationField.eventually_morseContinuationSlice_eq_preimage_mpullback`). This file
carries the same identification over to the broken trajectories, which become the broken
configurations of the pair `(X₀, Φ^* X₁)` between `p` and `Φ⁻¹ r`
(`TauCeti.IsAdaptedPseudoGradient.morseSourceBrokenPairSet`,
`TauCeti.IsAdaptedPseudoGradient.morseTargetBrokenPairSet`):

* at the source, `(p', z, y) ↦ (p', z, Ψ y)` identifies the continuation trajectories broken at
  `p'` with the configurations of the pair broken at `p'`
  (`TauCeti.IsContinuationField.eventually_morseSourceBrokenContinuationSet_eq_preimage`);
* at the target, `(q', y, z) ↦ (Φ⁻¹ q', Ψ y, Φ⁻¹ z)` identifies the continuation trajectories
  broken at `q'` with the configurations of the pair broken at the critical point `Φ⁻¹ q'` of
  `f₁ ∘ Φ`: `Φ` carries the trajectories of `Φ^* X₁` to those of `X₁`
  (`TauCeti.IsContinuationField.eventually_morseTargetBrokenContinuationSet_eq_preimage`).

The Morse indices of `f₁ ∘ Φ` at `Φ⁻¹ q'` and of `f₁` at `q'` agree, so the index conditions match
as well. Hence the broken continuation trajectories and the broken configurations of the pair are
equally many
(`TauCeti.IsContinuationField.eventually_ncard_morseSourceBrokenContinuationSet_eq`,
`TauCeti.IsContinuationField.eventually_ncard_morseTargetBrokenContinuationSet_eq`), and for a
transverse continuation, where `(X₀, Φ^* X₁)` is a Morse–Smale pair
(`TauCeti.isTransverseContinuation_iff_eventually_isMorseSmalePair`), the mod-two continuation map
is a chain map exactly when the broken configurations of that Morse–Smale pair between any two
critical points are evenly many in total
(`TauCeti.IsTransverseContinuation.eventually_morseBoundary_comp_morseContinuationMap_eq_iff`).
That parity is the count of the ends of the compactified one-dimensional intersections
`W^u_{X₀}(p) ∩ W^s_{Φ^* X₁}(Φ⁻¹ r)`, a statement about a single Morse–Smale pair.

## Main results

In the namespace `TauCeti.IsContinuationField`:

* `eventually_morseSourceBrokenContinuationSet_eq_preimage`,
  `eventually_morseTargetBrokenContinuationSet_eq_preimage`: the broken continuation trajectories
  are the preimages of the broken configurations of the transported pair.
* `eventually_ncard_morseSourceBrokenContinuationSet_eq`,
  `eventually_ncard_morseTargetBrokenContinuationSet_eq`: they are equally many.

In the namespace `TauCeti.IsTransverseContinuation`:

* `eventually_morseBoundary_comp_morseContinuationMap_eq_iff`: the chain-map criterion for a
  transverse continuation, in terms of the broken configurations of the transported pair.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1 (the continuation map is a chain map, by counting the
  ends of the one-dimensional moduli spaces of continuation trajectories).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open Filter Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {C : ℝ}
  {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}

namespace IsContinuationField

variable (hVs : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent ∞
    fun z ↦ (⟨z, V z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))
  (hV : IsContinuationField X₀ X₁ C V) (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
  (hX₁ : IsAdaptedPseudoGradient f₁ X₁) (hC : 0 < C) (hf₁ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 f₁)
include hV hX₀ hX₁ hC hVs hf₁

/-! ### Broken trajectories as preimages -/

/-- **Continuation trajectories broken at the source are broken configurations of the
transported pair.** Let `V` be a smooth continuation field from `X₀` to `X₁` at rate `C > 0`, and
`σ` the time at which the base trajectory crosses the middle level `t = 1 / 2`. For all
sufficiently negative `a` and sufficiently positive `b`, with `Φ` the transition diffeomorphism
from `a` to `b` and `Ψ` the one from `σ` to `a`, a triple `(p', z, y)` is a continuation trajectory
from `p` to a critical point `r` of `f₁` broken at the source exactly when `(p', z, Ψ y)` is a
configuration of the pair `(X₀, Φ^* X₁)` from `p` to `Φ⁻¹ r` broken at the source. -/
theorem eventually_morseSourceBrokenContinuationSet_eq_preimage {σ : ℝ}
    (hσ : intervalBaseOrbit C σ = 1 / 2) :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop, ∀ (p : M) (r : criticalPoints 𝓘(ℝ, E) f₁),
      morseSourceBrokenContinuationSet f₁ V hX₀ p r =
        Prod.map id (Prod.map id (continuationTransition C hVs σ a)) ⁻¹'
          hX₀.morseSourceBrokenPairSet (hX₁.mpullback (continuationTransition C hVs a b)) p
            ((continuationTransition C hVs a b).symm r) := by
  filter_upwards [hV.eventually_morseContinuationSlice_eq_preimage_mpullback hVs hX₀ hX₁ hC hσ]
    with a ha
  filter_upwards [ha] with b hb p r
  set Φ := continuationTransition C hVs a b
  ext x
  simp only [mem_morseSourceBrokenContinuationSet, mem_preimage, Prod.map_fst, Prod.map_snd,
    id_eq, IsAdaptedPseudoGradient.mem_morseSourceBrokenPairSet, hb,
    manifoldMorseIndex_symm_apply_eq_of_comp (σ := Φ) rfl (hf₁ _) r.property]

/-- **Continuation trajectories broken at the target are broken configurations of the
transported pair.** Let `V` be a smooth continuation field from `X₀` to `X₁` at rate `C > 0`, and
`σ` the time at which the base trajectory crosses the middle level `t = 1 / 2`. For all
sufficiently negative `a` and sufficiently positive `b`, with `Φ` the transition diffeomorphism
from `a` to `b` and `Ψ` the one from `σ` to `a`, a triple `(q', y, z)` is a continuation trajectory
from `p` to a critical point `r` of `f₁` broken at the target exactly when `(Φ⁻¹ q', Ψ y, Φ⁻¹ z)`
is a configuration of the pair `(X₀, Φ^* X₁)` from `p` to `Φ⁻¹ r` broken at the target, at the
critical point `Φ⁻¹ q'` of `f₁ ∘ Φ`. -/
theorem eventually_morseTargetBrokenContinuationSet_eq_preimage {σ : ℝ}
    (hσ : intervalBaseOrbit C σ = 1 / 2) :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop, ∀ (p : M) (r : criticalPoints 𝓘(ℝ, E) f₁),
      morseTargetBrokenContinuationSet f₀ V hX₁ p r =
        Prod.map (criticalPointsEquivOfComp (rfl : f₁ ∘ continuationTransition C hVs a b =
            f₁ ∘ continuationTransition C hVs a b)).symm
          (Prod.map (continuationTransition C hVs σ a) (continuationTransition C hVs a b).symm) ⁻¹'
          hX₀.morseTargetBrokenPairSet (hX₁.mpullback (continuationTransition C hVs a b)) p
            ((continuationTransition C hVs a b).symm r) := by
  filter_upwards [hV.eventually_morseContinuationSlice_eq_preimage_mpullback hVs hX₀ hX₁ hC hσ]
    with a ha
  filter_upwards [ha] with b hb p r
  set Φ := continuationTransition C hVs a b
  -- The diffeomorphism `Φ` carries the trajectories of `Φ^* X₁` to those of `X₁`.
  have hslice (q : M) : Φ.symm ⁻¹' (hX₁.mpullback Φ).morseTrajectorySlice (Φ.symm q) (Φ.symm r) =
      hX₁.morseTrajectorySlice q r := by
    rw [← IsAdaptedPseudoGradient.preimage_morseTrajectorySlice_diffeomorph rfl
      (hX₁.mpullback Φ) hX₁ (Φ.mfderiv_apply_mpullback (by simp) X₁), Φ.apply_symm_apply,
      Φ.apply_symm_apply]
    ext z
    simp
  ext x
  simp only [mem_morseTargetBrokenContinuationSet, mem_preimage, Prod.map_fst, Prod.map_snd,
    IsAdaptedPseudoGradient.mem_morseTargetBrokenPairSet, hb,
    coe_criticalPointsEquivOfComp_symm_apply, ← hslice x.1,
    manifoldMorseIndex_symm_apply_eq_of_comp (σ := Φ) rfl (hf₁ _) r.property,
    manifoldMorseIndex_symm_apply_eq_of_comp (σ := Φ) rfl (hf₁ _) x.1.property]

/-! ### Counting broken trajectories -/

/-- **As many continuation trajectories broken at the source as broken configurations of the
transported pair.** For a smooth continuation field from `X₀` to `X₁` at rate `C > 0`, all
sufficiently negative `a` and sufficiently positive `b`, with `Φ` the transition diffeomorphism
from `a` to `b`, the continuation trajectories from `p` to a critical point `r` of `f₁` broken at
the source are as many as the configurations of the pair `(X₀, Φ^* X₁)` from `p` to `Φ⁻¹ r` broken
at the source. -/
theorem eventually_ncard_morseSourceBrokenContinuationSet_eq :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop, ∀ (p : M) (r : criticalPoints 𝓘(ℝ, E) f₁),
      (morseSourceBrokenContinuationSet f₁ V hX₀ p r).ncard =
        (hX₀.morseSourceBrokenPairSet (hX₁.mpullback (continuationTransition C hVs a b)) p
          ((continuationTransition C hVs a b).symm r)).ncard := by
  obtain ⟨σ, hσ⟩ := exists_intervalBaseOrbit_eq hC.ne' (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  filter_upwards [hV.eventually_morseSourceBrokenContinuationSet_eq_preimage hVs hX₀ hX₁ hC hf₁ hσ]
    with a ha
  filter_upwards [ha] with b hb p r
  set Ψ := continuationTransition C hVs σ a
  have hbij : Function.Bijective
      (Prod.map (id : criticalPoints 𝓘(ℝ, E) f₀ → _) (Prod.map (id : M → M) Ψ)) :=
    Function.bijective_id.prodMap (Function.bijective_id.prodMap Ψ.toEquiv.bijective)
  rw [hb p r]
  exact ncard_preimage_of_injective_subset_range hbij.1 (by simp [hbij.2.range_eq])

/-- **As many continuation trajectories broken at the target as broken configurations of the
transported pair.** For a smooth continuation field from `X₀` to `X₁` at rate `C > 0`, all
sufficiently negative `a` and sufficiently positive `b`, with `Φ` the transition diffeomorphism
from `a` to `b`, the continuation trajectories from `p` to a critical point `r` of `f₁` broken at
the target are as many as the configurations of the pair `(X₀, Φ^* X₁)` from `p` to `Φ⁻¹ r` broken
at the target. -/
theorem eventually_ncard_morseTargetBrokenContinuationSet_eq :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop, ∀ (p : M) (r : criticalPoints 𝓘(ℝ, E) f₁),
      (morseTargetBrokenContinuationSet f₀ V hX₁ p r).ncard =
        (hX₀.morseTargetBrokenPairSet (hX₁.mpullback (continuationTransition C hVs a b)) p
          ((continuationTransition C hVs a b).symm r)).ncard := by
  obtain ⟨σ, hσ⟩ := exists_intervalBaseOrbit_eq hC.ne' (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  filter_upwards [hV.eventually_morseTargetBrokenContinuationSet_eq_preimage hVs hX₀ hX₁ hC hf₁ hσ]
    with a ha
  filter_upwards [ha] with b hb p r
  set Φ := continuationTransition C hVs a b
  set Ψ := continuationTransition C hVs σ a
  have hbij : Function.Bijective (Prod.map (criticalPointsEquivOfComp (rfl : f₁ ∘ Φ = f₁ ∘ Φ)).symm
      (Prod.map Ψ Φ.symm)) :=
    (Equiv.bijective _).prodMap (Ψ.toEquiv.bijective.prodMap Φ.symm.toEquiv.bijective)
  rw [hb p r]
  exact ncard_preimage_of_injective_subset_range hbij.1 (by simp [hbij.2.range_eq])

end IsContinuationField

/-! ### The chain-map criterion -/

namespace IsTransverseContinuation

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  (hT : IsTransverseContinuation C V hX₀ hX₁) (hV : IsContinuationField X₀ X₁ C V) (hC : 0 < C)
  (hVs : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent ∞
    fun z ↦ (⟨z, V z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))
include hT hV hC hVs

/-- **The chain-map criterion for a transverse continuation, through the transported pair.** For a
transverse smooth continuation field at rate `C > 0` between Morse–Smale pseudo-gradients adapted
to Morse functions, and for all sufficiently negative `a` and sufficiently positive `b`, with `Φ`
the transition diffeomorphism from `a` to `b`, the mod-two continuation map commutes with the
Morse boundaries exactly when, between any critical point `p` of `f₀` and any critical point `r`
of `f₁`, the configurations of the pair `(X₀, Φ^* X₁)` from `p` to `Φ⁻¹ r` broken at the source and
at the target are evenly many in total. For all such `a` and `b` the pair `(X₀, Φ^* X₁)` is itself
Morse–Smale (`TauCeti.isTransverseContinuation_iff_eventually_isMorseSmalePair`), so this reduces
the chain-map property to a parity statement about Morse–Smale pairs. -/
theorem eventually_morseBoundary_comp_morseContinuationMap_eq_iff (h₀ : hX₀.IsMorseSmale)
    (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁) :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop,
      (h₁.morseBoundary hf₁ ∘ₗ morseContinuationMap f₀ hf₁ V =
          morseContinuationMap f₀ hf₁ V ∘ₗ h₀.morseBoundary hf₀ ↔
        ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₁),
          Even ((hX₀.morseSourceBrokenPairSet (hX₁.mpullback (continuationTransition C hVs a b))
              p ((continuationTransition C hVs a b).symm r)).ncard +
            (hX₀.morseTargetBrokenPairSet (hX₁.mpullback (continuationTransition C hVs a b))
              p ((continuationTransition C hVs a b).symm r)).ncard)) := by
  have hf₁' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 f₁ := hf₁.contMDiff.of_le (by simp)
  filter_upwards [hV.eventually_ncard_morseSourceBrokenContinuationSet_eq hVs hX₀ hX₁ hC hf₁',
    hV.eventually_ncard_morseTargetBrokenContinuationSet_eq hVs hX₀ hX₁ hC hf₁'] with a ha₁ ha₂
  filter_upwards [ha₁, ha₂] with b hb₁ hb₂
  rw [hT.morseBoundary_comp_morseContinuationMap_eq_iff hV hC hVs h₀ h₁ hf₀ hf₁]
  simp only [hb₁, hb₂]

end IsTransverseContinuation

end TauCeti

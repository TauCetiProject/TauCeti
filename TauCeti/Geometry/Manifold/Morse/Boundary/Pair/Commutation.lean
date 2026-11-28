/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Pair.Sign
import TauCeti.Data.Set.Card

/-!
# The signed pair map commutes with the integral Morse boundaries when broken configurations cancel

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M`, with Morse–Smale
pseudo-gradients `X₀` and `X₁` adapted to them, such that the pair `(X₀, X₁)` is Morse–Smale
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmalePair`), and choose orientations
`𝔬₀ : TauCeti.MorseOrientation f₀ X₀` and `𝔬₁ : TauCeti.MorseOrientation f₁ X₁` of the unstable
manifolds. The signed pair map `Φ = TauCeti.IsAdaptedPseudoGradient.signedPairMap` counts the
points of the rigid intersections `W^u_{X₀}(p) ∩ W^s_{X₁}(q)` with signs; for the pair transported
by the transition diffeomorphism of a transverse continuation, these intersections are the
continuation trajectories
(`TauCeti.IsContinuationField.eventually_morseContinuationSlice_eq_preimage_mpullback`).
For `Φ` to induce a map on integral Morse homology it must commute with the integral Morse
boundaries `∂₀` and `∂₁` (`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary`). This file proves
the algebraic half of that statement.

For a critical point `p` of `f₀` and a critical point `r` of `f₁` with `ind p = ind r + 1`, the
one-dimensional intersection `W^u_{X₀}(p) ∩ W^s_{X₁}(r)` breaks in two ways
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmalePair.closure_unstableSet_inter_stableSet_subset`):

* at the source (`TauCeti.IsAdaptedPseudoGradient.morseSourceBrokenPairSet`): a trajectory of `X₀`
  from `p` to a critical point `a` of `f₀` of index `ind r`, recorded by its point `z` on the middle
  level, followed by a point `y` of `W^u_{X₀}(a) ∩ W^s_{X₁}(r)`;
* at the target (`TauCeti.IsAdaptedPseudoGradient.morseTargetBrokenPairSet`): a point `y` of
  `W^u_{X₀}(p) ∩ W^s_{X₁}(b)` for a critical point `b` of `f₁` of index `ind p`, followed by a
  trajectory of `X₁` from `b` to `r`, recorded by its point `z` on the middle level.

The **sign** of such a broken configuration
(`TauCeti.IsAdaptedPseudoGradient.sourceBrokenPairSign`,
`TauCeti.IsAdaptedPseudoGradient.targetBrokenPairSign`) is the product of the sign
`TauCeti.IsAdaptedPseudoGradient.trajectorySign` of its trajectory and the sign
`TauCeti.IsAdaptedPseudoGradient.pairSign` of its intersection point. For the map with coefficients
in any ring `R`, the `r`-coefficient of `Φ (∂₀ p)` is the sum of the signs of the configurations
broken at the source
(`IsMorseSmalePair.signedPairMap_signedMorseBoundary_single_apply`), and that of `∂₁ (Φ p)` is
the sum of the signs of the configurations broken at the target
(`IsMorseSmalePair.signedMorseBoundary_signedPairMap_single_apply`). So `Φ` commutes with the
boundaries exactly when, between any two critical points, the two signed counts agree in `R`
(`IsMorseSmalePair.signedMorseBoundary_comp_signedPairMap_eq_iff`); the agreement of the integer
counts gives a chain map over every ring at once. The geometric half, that the broken
configurations are the ends of the compactified one-dimensional intersections and that the
orientations of these arcs make the two signed counts agree, is not proved here.

The sign of a broken configuration does not depend on the orientation chosen at its intermediate
critical point: reversing orientations changes it only through its two ends
(`TauCeti.IsAdaptedPseudoGradient.sourceBrokenPairSign_reverse`,
`TauCeti.IsAdaptedPseudoGradient.targetBrokenPairSign_reverse`). Every broken configuration has sign
`±1`, so modulo two the signed counts are the numbers of broken configurations
(`IsMorseSmalePair.intCast_finsum_mem_sourceBrokenPairSign`,
`IsMorseSmalePair.intCast_finsum_mem_targetBrokenPairSign`).

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseSourceBrokenPairSet`, `morseTargetBrokenPairSet`: the configurations broken at the source
  and at the target.
* `sourceBrokenPairSign`, `targetBrokenPairSign`: their signs.
* `sourceBrokenPairSign_reverse`, `targetBrokenPairSign_reverse`: the change of the signs under
  reversal of orientations.
* `IsMorseSmalePair.signedPairMap_signedMorseBoundary_single_apply`,
  `IsMorseSmalePair.signedMorseBoundary_signedPairMap_single_apply`: the coefficients of `Φ ∘ ∂₀`
  and `∂₁ ∘ Φ` are the signed counts of the broken configurations.
* `IsMorseSmalePair.signedMorseBoundary_comp_signedPairMap_eq_iff`: `∂₁ ∘ Φ = Φ ∘ ∂₀` exactly when
  these signed counts agree.
* `IsMorseSmalePair.intCast_finsum_mem_sourceBrokenPairSign`,
  `IsMorseSmalePair.intCast_finsum_mem_targetBrokenPairSign`: modulo two, the signed counts are
  the numbers of broken configurations.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1 (the continuation map over `ℤ` is a chain map, by counting
  the ends of the one-dimensional moduli spaces of continuation trajectories with signs).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

/-! ### Broken configurations -/

section BrokenSets

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)

/-- The configurations from `p` to `r` broken at the source: triples `(a, z, y)` of a critical
point `a` of `f₀` whose Morse index lies one below that of `p` and equals that of `r`, a point `z`
on the middle-level slice of the trajectories of `X₀` from `p` to `a`, and a point `y` of
`W^u_{X₀}(a) ∩ W^s_{X₁}(r)`. -/
def morseSourceBrokenPairSet (p r : M) : Set (criticalPoints 𝓘(ℝ, E) f₀ × M × M) :=
  {x | manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ r ∧
    x.2.1 ∈ hX₀.morseTrajectorySlice p x.1 ∧
    x.2.2 ∈ hX₀.flow.unstableSet x.1 ∩ hX₁.flow.stableSet r}

/-- Membership in the set of configurations broken at the source. -/
@[simp]
theorem mem_morseSourceBrokenPairSet {p r : M} {x : criticalPoints 𝓘(ℝ, E) f₀ × M × M} :
    x ∈ hX₀.morseSourceBrokenPairSet hX₁ p r ↔
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ r ∧
          x.2.1 ∈ hX₀.morseTrajectorySlice p x.1 ∧
            x.2.2 ∈ hX₀.flow.unstableSet x.1 ∩ hX₁.flow.stableSet r :=
  Iff.rfl

/-- The configurations from `p` to `r` broken at the target: triples `(b, y, z)` of a critical
point `b` of `f₁` whose Morse index equals that of `p` and lies one above that of `r`, a point `y`
of `W^u_{X₀}(p) ∩ W^s_{X₁}(b)`, and a point `z` on the middle-level slice of the trajectories of
`X₁` from `b` to `r`. -/
def morseTargetBrokenPairSet (p r : M) : Set (criticalPoints 𝓘(ℝ, E) f₁ × M × M) :=
  {x | manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1 ∧
    x.2.1 ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet x.1 ∧
    x.2.2 ∈ hX₁.morseTrajectorySlice x.1 r}

/-- Membership in the set of configurations broken at the target. -/
@[simp]
theorem mem_morseTargetBrokenPairSet {p r : M} {x : criticalPoints 𝓘(ℝ, E) f₁ × M × M} :
    x ∈ hX₀.morseTargetBrokenPairSet hX₁ p r ↔
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1 ∧
          x.2.1 ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet x.1 ∧
            x.2.2 ∈ hX₁.morseTrajectorySlice x.1 r :=
  Iff.rfl

end BrokenSets

/-! ### Signs of broken configurations -/

section Signs

variable (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)
  (𝔬₀ : MorseOrientation f₀ X₀) (𝔬₁ : MorseOrientation f₁ X₁)

/-- The **sign of a configuration broken at the source** `x = (a, z, y)` from `p` to `r`, for the
orientations `𝔬₀` and `𝔬₁`: the product of the sign of the trajectory of `X₀` from `p` to `a`
through `z` and the sign of the point `y` of `W^u_{X₀}(a) ∩ W^s_{X₁}(r)`, when `ind p = ind a + 1`
and `ind a = ind r`, and `0` otherwise. -/
noncomputable def sourceBrokenPairSign (p : criticalPoints 𝓘(ℝ, E) f₀)
    (r : criticalPoints 𝓘(ℝ, E) f₁) (x : criticalPoints 𝓘(ℝ, E) f₀ × M × M) : ℤ :=
  if h : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ r then
    hX₀.trajectorySign (𝔬₀.chart p) (𝔬₀.chart x.1) (𝔬₀.orientation p) (𝔬₀.orientation x.1) h.1
        x.2.1 *
      hX₀.pairSign hX₁ (𝔬₀.chart x.1) (𝔬₁.chart r) (𝔬₀.orientation x.1) (𝔬₁.orientation r) h.2
        x.2.2
  else 0

/-- The **sign of a configuration broken at the target** `x = (b, y, z)` from `p` to `r`, for the
orientations `𝔬₀` and `𝔬₁`: the product of the sign of the point `y` of
`W^u_{X₀}(p) ∩ W^s_{X₁}(b)` and the sign of the trajectory of `X₁` from `b` to `r` through `z`,
when `ind p = ind b` and `ind b = ind r + 1`, and `0` otherwise. -/
noncomputable def targetBrokenPairSign (p : criticalPoints 𝓘(ℝ, E) f₀)
    (r : criticalPoints 𝓘(ℝ, E) f₁) (x : criticalPoints 𝓘(ℝ, E) f₁ × M × M) : ℤ :=
  if h : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1 then
    hX₀.pairSign hX₁ (𝔬₀.chart p) (𝔬₁.chart x.1) (𝔬₀.orientation p) (𝔬₁.orientation x.1) h.1
        x.2.1 *
      hX₁.trajectorySign (𝔬₁.chart x.1) (𝔬₁.chart r) (𝔬₁.orientation x.1) (𝔬₁.orientation r) h.2
        x.2.2
  else 0

variable {hX₀ hX₁ 𝔬₀ 𝔬₁} {p : criticalPoints 𝓘(ℝ, E) f₀} {r : criticalPoints 𝓘(ℝ, E) f₁}

/-- When the indices are those of a configuration broken at the source, its sign is the product of
the signs of its trajectory and of its intersection point. -/
theorem sourceBrokenPairSign_of_morseIndex_eq {x : criticalPoints 𝓘(ℝ, E) f₀ × M × M}
    (hpa : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1)
    (har : manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ r) :
    hX₀.sourceBrokenPairSign hX₁ 𝔬₀ 𝔬₁ p r x =
      hX₀.trajectorySign (𝔬₀.chart p) (𝔬₀.chart x.1) (𝔬₀.orientation p) (𝔬₀.orientation x.1)
          hpa x.2.1 *
        hX₀.pairSign hX₁ (𝔬₀.chart x.1) (𝔬₁.chart r) (𝔬₀.orientation x.1) (𝔬₁.orientation r)
          har x.2.2 :=
  dite_eq_left ⟨hpa, har⟩

/-- The sign of a configuration broken at the source vanishes unless the indices are those of such
a configuration. -/
@[simp]
theorem sourceBrokenPairSign_of_not_morseIndex_eq {x : criticalPoints 𝓘(ℝ, E) f₀ × M × M}
    (h : ¬(manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ r)) :
    hX₀.sourceBrokenPairSign hX₁ 𝔬₀ 𝔬₁ p r x = 0 :=
  dite_eq_right h

/-- When the indices are those of a configuration broken at the target, its sign is the product of
the signs of its intersection point and of its trajectory. -/
theorem targetBrokenPairSign_of_morseIndex_eq {x : criticalPoints 𝓘(ℝ, E) f₁ × M × M}
    (hpb : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1)
    (hbr : manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1) :
    hX₀.targetBrokenPairSign hX₁ 𝔬₀ 𝔬₁ p r x =
      hX₀.pairSign hX₁ (𝔬₀.chart p) (𝔬₁.chart x.1) (𝔬₀.orientation p) (𝔬₁.orientation x.1) hpb
          x.2.1 *
        hX₁.trajectorySign (𝔬₁.chart x.1) (𝔬₁.chart r) (𝔬₁.orientation x.1) (𝔬₁.orientation r)
          hbr x.2.2 :=
  dite_eq_left ⟨hpb, hbr⟩

/-- The sign of a configuration broken at the target vanishes unless the indices are those of such
a configuration. -/
@[simp]
theorem targetBrokenPairSign_of_not_morseIndex_eq {x : criticalPoints 𝓘(ℝ, E) f₁ × M × M}
    (h : ¬(manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1)) :
    hX₀.targetBrokenPairSign hX₁ 𝔬₀ 𝔬₁ p r x = 0 :=
  dite_eq_right h

/-- **Reversing orientations changes the signs of the configurations broken at the source at their
ends only.** Reversing the orientations of `𝔬₀` at the critical points of `S₀` and those of `𝔬₁`
at the critical points of `S₁` multiplies the sign of a configuration broken at the source from
`p` to `r` by `-1` for `p ∈ S₀` and by `-1` for `r ∈ S₁`; the reversal at the intermediate
critical point reverses both factors and cancels. -/
theorem sourceBrokenPairSign_reverse (S₀ : Set (criticalPoints 𝓘(ℝ, E) f₀))
    [DecidablePred (· ∈ S₀)] (S₁ : Set (criticalPoints 𝓘(ℝ, E) f₁)) [DecidablePred (· ∈ S₁)]
    (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₁)
    (x : criticalPoints 𝓘(ℝ, E) f₀ × M × M) :
    hX₀.sourceBrokenPairSign hX₁ (𝔬₀.reverse S₀) (𝔬₁.reverse S₁) p r x =
      (if p ∈ S₀ then -1 else 1) * (if r ∈ S₁ then -1 else 1) *
        hX₀.sourceBrokenPairSign hX₁ 𝔬₀ 𝔬₁ p r x := by
  by_cases h : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f₀ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ r
  · rw [sourceBrokenPairSign_of_morseIndex_eq h.1 h.2,
      sourceBrokenPairSign_of_morseIndex_eq h.1 h.2, MorseOrientation.reverse_orientation,
      MorseOrientation.reverse_orientation, MorseOrientation.reverse_orientation]
    by_cases hp : p ∈ S₀ <;> by_cases ha : x.1 ∈ S₀ <;> by_cases hr : r ∈ S₁ <;>
      simp [hp, ha, hr, MorseOrientation.reverse_chart]
  · simp [sourceBrokenPairSign_of_not_morseIndex_eq h]

/-- **Reversing orientations changes the signs of the configurations broken at the target at their
ends only.** Reversing the orientations of `𝔬₀` at the critical points of `S₀` and those of `𝔬₁`
at the critical points of `S₁` multiplies the sign of a configuration broken at the target from
`p` to `r` by `-1` for `p ∈ S₀` and by `-1` for `r ∈ S₁`; the reversal at the intermediate
critical point reverses both factors and cancels. -/
theorem targetBrokenPairSign_reverse (S₀ : Set (criticalPoints 𝓘(ℝ, E) f₀))
    [DecidablePred (· ∈ S₀)] (S₁ : Set (criticalPoints 𝓘(ℝ, E) f₁)) [DecidablePred (· ∈ S₁)]
    (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₁)
    (x : criticalPoints 𝓘(ℝ, E) f₁ × M × M) :
    hX₀.targetBrokenPairSign hX₁ (𝔬₀.reverse S₀) (𝔬₁.reverse S₁) p r x =
      (if p ∈ S₀ then -1 else 1) * (if r ∈ S₁ then -1 else 1) *
        hX₀.targetBrokenPairSign hX₁ 𝔬₀ 𝔬₁ p r x := by
  by_cases h : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f₁ x.1 = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1
  · rw [targetBrokenPairSign_of_morseIndex_eq h.1 h.2,
      targetBrokenPairSign_of_morseIndex_eq h.1 h.2, MorseOrientation.reverse_orientation,
      MorseOrientation.reverse_orientation, MorseOrientation.reverse_orientation]
    by_cases hp : p ∈ S₀ <;> by_cases hb : x.1 ∈ S₁ <;> by_cases hr : r ∈ S₁ <;>
      simp [hp, hb, hr, MorseOrientation.reverse_chart]
  · simp [targetBrokenPairSign_of_not_morseIndex_eq h]

end Signs

/-! ### Counting broken configurations with signs -/

namespace IsMorseSmalePair

variable {hX₀ : IsAdaptedPseudoGradient f₀ X₀} {hX₁ : IsAdaptedPseudoGradient f₁ X₁}
  {𝔬₀ : MorseOrientation f₀ X₀} {𝔬₁ : MorseOrientation f₁ X₁}
  (h : IsMorseSmalePair hX₀ hX₁) (h₀ : hX₀.IsMorseSmale) (h₁ : hX₁.IsMorseSmale)
  (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
  {p : criticalPoints 𝓘(ℝ, E) f₀} {r : criticalPoints 𝓘(ℝ, E) f₁}

include h h₀ h₁ hf₀ hf₁

/-- **Finitely many configurations broken at the source.** -/
theorem finite_morseSourceBrokenPairSet (p r : M) :
    (hX₀.morseSourceBrokenPairSet hX₁ p r).Finite := by
  have := hf₀.finite_criticalPoints.to_subtype
  exact finite_setOf_and_and_mem_and_mem (ι := criticalPoints 𝓘(ℝ, E) f₀)
    (A := (hX₀.morseTrajectorySlice p ·))
    (B := (hX₀.flow.unstableSet · ∩ hX₁.flow.stableSet r))
    (fun _ ↦ h₀.finite_morseTrajectorySlice hf₀)
    fun _ hind ↦ h.finite_unstableSet_inter_stableSet h₀ h₁ hf₀ hf₁ (le_of_eq hind)

/-- **Finitely many configurations broken at the target.** -/
theorem finite_morseTargetBrokenPairSet (p r : M) :
    (hX₀.morseTargetBrokenPairSet hX₁ p r).Finite := by
  have := hf₁.finite_criticalPoints.to_subtype
  exact finite_setOf_and_and_mem_and_mem (ι := criticalPoints 𝓘(ℝ, E) f₁)
    (A := (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet ·))
    (B := (hX₁.morseTrajectorySlice · r))
    (fun _ hind ↦ h.finite_unstableSet_inter_stableSet h₀ h₁ hf₀ hf₁ (le_of_eq hind))
    fun _ ↦ h₁.finite_morseTrajectorySlice hf₁

omit h₁ hf₁ in
/-- **Every configuration broken at the source has sign `±1`.** -/
theorem sourceBrokenPairSign_eq_one_or_eq_neg_one {x : criticalPoints 𝓘(ℝ, E) f₀ × M × M}
    (hx : x ∈ hX₀.morseSourceBrokenPairSet hX₁ p r) :
    hX₀.sourceBrokenPairSign hX₁ 𝔬₀ 𝔬₁ p r x = 1 ∨
      hX₀.sourceBrokenPairSign hX₁ 𝔬₀ 𝔬₁ p r x = -1 := by
  obtain ⟨hpa, har, hz, hy⟩ := hx
  rw [mem_morseTrajectorySlice] at hz
  rw [sourceBrokenPairSign_of_morseIndex_eq hpa har]
  rcases trajectorySign_eq_one_or_eq_neg_one (𝔬₀.coord_mfderiv_chart p)
      (𝔬₀.coord_mfderiv_chart x.1) h₀ hf₀ (op := 𝔬₀.orientation p) (oq := 𝔬₀.orientation x.1)
      (hpq := hpa) ⟨hz.1, hz.2.1⟩ with h₁ | h₁ <;>
    rcases pairSign_eq_one_or_eq_neg_one (𝔬₀.coord_mfderiv_chart x.1)
      (𝔬₁.coord_mfderiv_chart r) h hf₀ (op := 𝔬₀.orientation x.1) (oq := 𝔬₁.orientation r)
      (hpq := har) hy with h₂ | h₂ <;>
    simp [h₁, h₂]

omit h₀ in
/-- **Every configuration broken at the target has sign `±1`.** -/
theorem targetBrokenPairSign_eq_one_or_eq_neg_one {x : criticalPoints 𝓘(ℝ, E) f₁ × M × M}
    (hx : x ∈ hX₀.morseTargetBrokenPairSet hX₁ p r) :
    hX₀.targetBrokenPairSign hX₁ 𝔬₀ 𝔬₁ p r x = 1 ∨
      hX₀.targetBrokenPairSign hX₁ 𝔬₀ 𝔬₁ p r x = -1 := by
  obtain ⟨hpb, hbr, hy, hz⟩ := hx
  rw [mem_morseTrajectorySlice] at hz
  rw [targetBrokenPairSign_of_morseIndex_eq hpb hbr]
  rcases pairSign_eq_one_or_eq_neg_one (𝔬₀.coord_mfderiv_chart p)
      (𝔬₁.coord_mfderiv_chart x.1) h hf₀ (op := 𝔬₀.orientation p) (oq := 𝔬₁.orientation x.1)
      (hpq := hpb) hy with h₂ | h₂ <;>
    rcases trajectorySign_eq_one_or_eq_neg_one (𝔬₁.coord_mfderiv_chart x.1)
      (𝔬₁.coord_mfderiv_chart r) h₁ hf₁ (op := 𝔬₁.orientation x.1) (oq := 𝔬₁.orientation r)
      (hpq := hbr) ⟨hz.1, hz.2.1⟩ with h₃ | h₃ <;>
    simp [h₂, h₃]

/-- **`Φ ∘ ∂₀` counts configurations broken at the source with signs.** For the maps with
coefficients in a ring `R`, the `r`-coefficient of the signed pair map applied to the Morse boundary
of a critical point `p` of `f₀` is the sum of the signs of the configurations from `p` to `r` broken
at the source. -/
theorem signedPairMap_signedMorseBoundary_single_apply {R : Type*} [Ring R]
    (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₁) :
    hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ R (hX₀.signedMorseBoundary 𝔬₀ hf₀ R (Finsupp.single p 1)) r =
      ((∑ᶠ x ∈ hX₀.morseSourceBrokenPairSet hX₁ p r,
        hX₀.sourceBrokenPairSign hX₁ 𝔬₀ 𝔬₁ p r x : ℤ) : R) := by
  have := hf₀.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₀)
  rw [signedPairMap_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _]
  simp_rw [signedMorseBoundary_single_apply, one_mul, ← Int.cast_mul, ← Int.cast_sum]
  congr 1
  -- Sort the broken configurations by their intermediate critical point `a`: the sign splits as
  -- the sign of the trajectory from `p` to `a` times the sign of the point of the intersection.
  rw [← finsum_mem_setOf_and_and_mem_and_mem
    (P := fun a : criticalPoints 𝓘(ℝ, E) f₀ ↦
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ a + 1)
    (Q := fun a ↦ manifoldMorseIndex 𝓘(ℝ, E) f₀ a = manifoldMorseIndex 𝓘(ℝ, E) f₁ r)
    (A := (hX₀.morseTrajectorySlice p ·)) (B := (hX₀.flow.unstableSet · ∩ hX₁.flow.stableSet r))
    (g := fun a z ↦ if hpa : _ then hX₀.trajectorySign (𝔬₀.chart p) (𝔬₀.chart a)
      (𝔬₀.orientation p) (𝔬₀.orientation a) hpa z else 0)
    (k := fun a y ↦ if har : _ then hX₀.pairSign hX₁ (𝔬₀.chart a) (𝔬₁.chart r)
      (𝔬₀.orientation a) (𝔬₁.orientation r) har y else 0)
    (fun _ ↦ h₀.finite_morseTrajectorySlice hf₀)
    (fun _ hind ↦ h.finite_unstableSet_inter_stableSet h₀ h₁ hf₀ hf₁ hind.le)
    (fun a hpa ↦ ?_) (fun _ ↦ signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one)
    (fun a har ↦ ?_) (fun _ ↦ signedPairCoeff_eq_zero_of_morseIndex_ne)]
  · exact finsum_mem_congr rfl fun x hx ↦ by
      rw [sourceBrokenPairSign_of_morseIndex_eq hx.1 hx.2.1, dite_eq_left hx.1, dite_eq_left hx.2.1]
  · exact signedMorseBoundaryCoeff_eq_finsum_mem hpa
  · rw [signedPairCoeff_of_morseIndex_eq har, signedPairCount_def]
    exact finsum_mem_congr rfl fun _ _ ↦ by rw [dite_eq_left har]

/-- **`∂₁ ∘ Φ` counts configurations broken at the target with signs.** For the maps with
coefficients in a ring `R`, the `r`-coefficient of the Morse boundary of the signed pair map applied
to a critical point `p` of `f₀` is the sum of the signs of the configurations from `p` to `r`
broken at the target. -/
theorem signedMorseBoundary_signedPairMap_single_apply {R : Type*} [Ring R]
    (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₁) :
    hX₁.signedMorseBoundary 𝔬₁ hf₁ R (hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ R (Finsupp.single p 1)) r =
      ((∑ᶠ x ∈ hX₀.morseTargetBrokenPairSet hX₁ p r,
        hX₀.targetBrokenPairSign hX₁ 𝔬₀ 𝔬₁ p r x : ℤ) : R) := by
  have := hf₁.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f₁)
  rw [signedMorseBoundary_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _]
  simp_rw [signedPairMap_single_apply, one_mul, ← Int.cast_mul, ← Int.cast_sum]
  congr 1
  -- Sort the broken configurations by their intermediate critical point `b`: the sign splits as
  -- the sign of the point of the intersection times the sign of the trajectory from `b` to `r`.
  rw [← finsum_mem_setOf_and_and_mem_and_mem
    (P := fun b : criticalPoints 𝓘(ℝ, E) f₁ ↦
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ b)
    (Q := fun b ↦ manifoldMorseIndex 𝓘(ℝ, E) f₁ b = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1)
    (A := (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet ·)) (B := (hX₁.morseTrajectorySlice · r))
    (g := fun b y ↦ if hpb : _ then hX₀.pairSign hX₁ (𝔬₀.chart p) (𝔬₁.chart b)
      (𝔬₀.orientation p) (𝔬₁.orientation b) hpb y else 0)
    (k := fun b z ↦ if hbr : _ then hX₁.trajectorySign (𝔬₁.chart b) (𝔬₁.chart r)
      (𝔬₁.orientation b) (𝔬₁.orientation r) hbr z else 0)
    (fun _ hind ↦ h.finite_unstableSet_inter_stableSet h₀ h₁ hf₀ hf₁ hind.le)
    (fun _ ↦ h₁.finite_morseTrajectorySlice hf₁)
    (fun b hpb ↦ ?_) (fun _ ↦ signedPairCoeff_eq_zero_of_morseIndex_ne)
    (fun b hbr ↦ ?_) (fun _ ↦ signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one)]
  · exact finsum_mem_congr rfl fun x hx ↦ by
      rw [targetBrokenPairSign_of_morseIndex_eq hx.1 hx.2.1, dite_eq_left hx.1,
        dite_eq_left hx.2.1]
  · rw [signedPairCoeff_of_morseIndex_eq hpb, signedPairCount_def]
    exact finsum_mem_congr rfl fun _ _ ↦ by rw [dite_eq_left hpb]
  · exact signedMorseBoundaryCoeff_eq_finsum_mem hbr

/-- **The signed pair map is a chain map exactly when broken configurations cancel.** The signed
pair map with coefficients in a ring `R` commutes with the Morse boundaries, `∂₁ ∘ Φ = Φ ∘ ∂₀`,
exactly when, between any critical point `p` of `f₀` and any critical point `r` of `f₁`, the signs
of the configurations broken at the source and of those broken at the target have the same sum in
`R`. In particular, if these integer sums agree, then the signed pair map is a chain map over every
ring. -/
theorem signedMorseBoundary_comp_signedPairMap_eq_iff {R : Type*} [Ring R] :
    hX₁.signedMorseBoundary 𝔬₁ hf₁ R ∘ₗ hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ R =
        hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ R ∘ₗ hX₀.signedMorseBoundary 𝔬₀ hf₀ R ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₁),
        ((∑ᶠ x ∈ hX₀.morseTargetBrokenPairSet hX₁ p r,
          hX₀.targetBrokenPairSign hX₁ 𝔬₀ 𝔬₁ p r x : ℤ) : R) =
          ((∑ᶠ x ∈ hX₀.morseSourceBrokenPairSet hX₁ p r,
            hX₀.sourceBrokenPairSign hX₁ 𝔬₀ 𝔬₁ p r x : ℤ) : R) := by
  simp_rw [← h.signedMorseBoundary_signedPairMap_single_apply h₀ h₁ hf₀ hf₁,
    ← h.signedPairMap_signedMorseBoundary_single_apply h₀ h₁ hf₀ hf₁]
  constructor
  · intro h0 p r
    exact DFunLike.congr_fun (LinearMap.congr_fun h0 (Finsupp.single p 1)) r
  · intro h0
    refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun r ↦ ?_
    -- Both maps send `a • p` to `a` times their value at `p`.
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← Finsupp.smul_single_one, map_smul,
      map_smul, map_smul, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, h0]

/-- **The signed count of the configurations broken at the source reduces to their number modulo
two.** -/
theorem intCast_finsum_mem_sourceBrokenPairSign (p : criticalPoints 𝓘(ℝ, E) f₀)
    (r : criticalPoints 𝓘(ℝ, E) f₁) :
    ((∑ᶠ x ∈ hX₀.morseSourceBrokenPairSet hX₁ p r,
      hX₀.sourceBrokenPairSign hX₁ 𝔬₀ 𝔬₁ p r x : ℤ) : ZMod 2) =
        ((hX₀.morseSourceBrokenPairSet hX₁ p r).ncard : ZMod 2) :=
  intCast_finsum_mem_eq_ncard_of_eq_one_or_eq_neg_one
    (h.finite_morseSourceBrokenPairSet h₀ h₁ hf₀ hf₁ p r) fun _ hx ↦
      h.sourceBrokenPairSign_eq_one_or_eq_neg_one h₀ hf₀ hx

/-- **The signed count of the configurations broken at the target reduces to their number modulo
two.** -/
theorem intCast_finsum_mem_targetBrokenPairSign (p : criticalPoints 𝓘(ℝ, E) f₀)
    (r : criticalPoints 𝓘(ℝ, E) f₁) :
    ((∑ᶠ x ∈ hX₀.morseTargetBrokenPairSet hX₁ p r,
      hX₀.targetBrokenPairSign hX₁ 𝔬₀ 𝔬₁ p r x : ℤ) : ZMod 2) =
        ((hX₀.morseTargetBrokenPairSet hX₁ p r).ncard : ZMod 2) :=
  intCast_finsum_mem_eq_ncard_of_eq_one_or_eq_neg_one
    (h.finite_morseTargetBrokenPairSet h₀ h₁ hf₀ hf₁ p r) fun _ hx ↦
      h.targetBrokenPairSign_eq_one_or_eq_neg_one h₁ hf₀ hf₁ hx

end IsMorseSmalePair

end IsAdaptedPseudoGradient

end TauCeti

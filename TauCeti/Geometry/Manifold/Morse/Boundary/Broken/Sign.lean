/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Integral
public import TauCeti.Geometry.Manifold.Morse.Boundary.Square
import TauCeti.Data.Set.Card

/-!
# The square of the integral Morse boundary counts broken trajectories with signs

Let `f` be a Morse function on a compact boundaryless manifold, `X` a Morse–Smale pseudo-gradient
adapted to `f`, and `𝔬 : TauCeti.MorseOrientation f X` a choice of orientations of the unstable
manifolds. For critical points `p` and `r` whose Morse indices differ by two, a broken trajectory
from `p` to `r` is recorded, as in `TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySet`, by
a triple `(q, z₁, z₂)` of an intermediate critical point `q` and points `z₁`, `z₂` on the
middle-level slices of trajectories from `p` to `q` and from `q` to `r`. Its **sign**
(`TauCeti.IsAdaptedPseudoGradient.brokenTrajectorySign`) is the product of the signs
`TauCeti.IsAdaptedPseudoGradient.trajectorySign` of its two components.

The `r`-coefficient of `∂ (∂ p)` for the Morse boundary with coefficients in any ring `R` is the
sum of the signs of the broken trajectories from `p` to `r`
(`IsMorseSmale.signedMorseBoundary_signedMorseBoundary_single_apply`). Consequently `∂ ∘ ∂ = 0`
holds exactly when, between any two critical points, these signed counts vanish in `R`
(`IsMorseSmale.signedMorseBoundary_comp_signedMorseBoundary_eq_zero_iff`); in particular the
vanishing of the integer signed counts gives `∂ ∘ ∂ = 0` over every ring at once. This is the
algebraic half of `∂² = 0` over `ℤ`. The geometric half is that the broken trajectories are the
ends of the compact one-dimensional space of index-two trajectories, and that the two ends of each
of its arcs carry opposite signs; the pairing of the ends is the content of
`TauCeti.Geometry.Manifold.Morse.Boundary.Differential`, which proves the mod-two statement.

The sign of a broken trajectory does not depend on the orientation chosen at the intermediate
critical point: reversing the orientations on a set `S` multiplies it by `-1` once for each of its
ends `p` and `r` lying in `S` (`TauCeti.IsAdaptedPseudoGradient.brokenTrajectorySign_reverse`).
Every broken trajectory has sign `±1`
(`IsMorseSmale.brokenTrajectorySign_eq_one_or_eq_neg_one`), so modulo two the signed count is
the number of broken trajectories (`IsMorseSmale.intCast_finsum_mem_brokenTrajectorySign`), whose
parity is the mod-two coefficient of `∂ (∂ p)` of
`TauCeti.Geometry.Manifold.Morse.Boundary.Square`.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `brokenTrajectorySign`: the sign of a broken index-two trajectory.
* `brokenTrajectorySign_reverse`: its change under reversal of orientations.
* `IsMorseSmale.brokenTrajectorySign_eq_one_or_eq_neg_one`: every broken trajectory has sign
  `±1`.
* `IsMorseSmale.signedMorseBoundary_signedMorseBoundary_single_apply`: the coefficients of
  `∂ (∂ p)` are the signed counts of broken trajectories.
* `IsMorseSmale.signedMorseBoundary_comp_signedMorseBoundary_eq_zero_iff`: `∂ ∘ ∂ = 0` exactly
  when these signed counts vanish.
* `IsMorseSmale.intCast_finsum_mem_brokenTrajectorySign`: modulo two, the signed count is the
  number of broken trajectories.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (the proof of `∂² = 0` over `ℤ` writes the coefficient of
  `r` in `∂ (∂ p)` as a signed count of broken trajectories).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X) (𝔬 : MorseOrientation f X)

/-- The **sign of a broken index-two trajectory** `x = (q, z₁, z₂)` from `p` to `r`, for the
orientations `𝔬`: the product of the sign of the trajectory from `p` to `q` through `z₁` and the
sign of the trajectory from `q` to `r` through `z₂`, when `ind p = ind q + 1` and
`ind q = ind r + 1`, and `0` otherwise. -/
noncomputable def brokenTrajectorySign (p r : criticalPoints 𝓘(ℝ, E) f)
    (x : criticalPoints 𝓘(ℝ, E) f × M × M) : ℤ :=
  if h : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x.1 + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x.1 = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 then
    hX.trajectorySign (𝔬.chart p) (𝔬.chart x.1) (𝔬.orientation p) (𝔬.orientation x.1) h.1 x.2.1 *
      hX.trajectorySign (𝔬.chart x.1) (𝔬.chart r) (𝔬.orientation x.1) (𝔬.orientation r) h.2
        x.2.2
  else 0

variable {hX 𝔬}

/-- When the indices drop by one at each step, the sign of a broken trajectory is the product of
the signs of its two components. -/
theorem brokenTrajectorySign_of_morseIndex_eq_add_one {p r : criticalPoints 𝓘(ℝ, E) f}
    {x : criticalPoints 𝓘(ℝ, E) f × M × M}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x.1 + 1)
    (hqr : manifoldMorseIndex 𝓘(ℝ, E) f x.1 = manifoldMorseIndex 𝓘(ℝ, E) f r + 1) :
    hX.brokenTrajectorySign 𝔬 p r x =
      hX.trajectorySign (𝔬.chart p) (𝔬.chart x.1) (𝔬.orientation p) (𝔬.orientation x.1) hpq
          x.2.1 *
        hX.trajectorySign (𝔬.chart x.1) (𝔬.chart r) (𝔬.orientation x.1) (𝔬.orientation r) hqr
          x.2.2 :=
  dite_eq_left ⟨hpq, hqr⟩

/-- The sign vanishes unless the indices drop by one at each step. -/
@[simp]
theorem brokenTrajectorySign_of_not_morseIndex_eq_add_one {p r : criticalPoints 𝓘(ℝ, E) f}
    {x : criticalPoints 𝓘(ℝ, E) f × M × M}
    (h : ¬(manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x.1 + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x.1 = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)) :
    hX.brokenTrajectorySign 𝔬 p r x = 0 :=
  dite_eq_right h

/-- **Reversing orientations changes the signs of the broken trajectories at their ends only.**
Reversing the orientations at the critical points of `S` multiplies the sign of a broken
trajectory from `p` to `r` by `-1` for each of `p` and `r` that lies in `S`; the reversal at the
intermediate critical point reverses both components and cancels. -/
theorem brokenTrajectorySign_reverse (S : Set (criticalPoints 𝓘(ℝ, E) f))
    [DecidablePred (· ∈ S)] (p r : criticalPoints 𝓘(ℝ, E) f)
    (x : criticalPoints 𝓘(ℝ, E) f × M × M) :
    hX.brokenTrajectorySign (𝔬.reverse S) p r x =
      (if p ∈ S then -1 else 1) * (if r ∈ S then -1 else 1) *
        hX.brokenTrajectorySign 𝔬 p r x := by
  by_cases h : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x.1 + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x.1 = manifoldMorseIndex 𝓘(ℝ, E) f r + 1
  · rw [brokenTrajectorySign_of_morseIndex_eq_add_one h.1 h.2,
      brokenTrajectorySign_of_morseIndex_eq_add_one h.1 h.2,
      MorseOrientation.reverse_orientation, MorseOrientation.reverse_orientation,
      MorseOrientation.reverse_orientation]
    by_cases hp : p ∈ S <;> by_cases hq : x.1 ∈ S <;> by_cases hr : r ∈ S <;>
      simp [hp, hq, hr, MorseOrientation.reverse_chart]
  · simp [brokenTrajectorySign_of_not_morseIndex_eq_add_one h]

namespace IsMorseSmale

variable (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

include h hf in
/-- **Every broken trajectory has sign `±1`.** Under the Morse–Smale condition, both components of
a broken index-two trajectory have sign `±1`. -/
theorem brokenTrajectorySign_eq_one_or_eq_neg_one {p r : criticalPoints 𝓘(ℝ, E) f}
    {x : criticalPoints 𝓘(ℝ, E) f × M × M} (hx : x ∈ hX.morseBrokenTrajectorySet p r) :
    hX.brokenTrajectorySign 𝔬 p r x = 1 ∨ hX.brokenTrajectorySign 𝔬 p r x = -1 := by
  obtain ⟨hpq, hqr, hz₁, hz₂⟩ := hX.mem_morseBrokenTrajectorySet.1 hx
  rw [mem_morseTrajectorySlice] at hz₁ hz₂
  rw [brokenTrajectorySign_of_morseIndex_eq_add_one hpq hqr]
  rcases trajectorySign_eq_one_or_eq_neg_one (𝔬.coord_mfderiv_chart p)
      (𝔬.coord_mfderiv_chart x.1) h hf (op := 𝔬.orientation p) (oq := 𝔬.orientation x.1)
      (hpq := hpq) ⟨hz₁.1, hz₁.2.1⟩ with h₁ | h₁ <;>
    rcases trajectorySign_eq_one_or_eq_neg_one (𝔬.coord_mfderiv_chart x.1)
      (𝔬.coord_mfderiv_chart r) h hf (op := 𝔬.orientation x.1) (oq := 𝔬.orientation r)
      (hpq := hqr) ⟨hz₂.1, hz₂.2.1⟩ with h₂ | h₂ <;>
    simp [h₁, h₂]

include h in
/-- **`∂ ∘ ∂` counts broken trajectories with signs.** For the Morse boundary with coefficients in
a ring `R`, the `r`-coefficient of the boundary of the boundary of a critical point `p` is the sum
of the signs of the broken index-two trajectories from `p` to `r`. -/
theorem signedMorseBoundary_signedMorseBoundary_single_apply {R : Type*} [Ring R]
    (p r : criticalPoints 𝓘(ℝ, E) f) :
    hX.signedMorseBoundary 𝔬 hf R (hX.signedMorseBoundary 𝔬 hf R (Finsupp.single p 1)) r =
      ((∑ᶠ x ∈ hX.morseBrokenTrajectorySet p r, hX.brokenTrajectorySign 𝔬 p r x : ℤ) : R) := by
  have := hf.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
  rw [signedMorseBoundary_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _]
  simp_rw [signedMorseBoundary_single_apply, one_mul, ← Int.cast_mul, ← Int.cast_sum]
  congr 1
  -- Sort the broken trajectories by their intermediate critical point `q`: the sign splits as the
  -- product of the signs of the trajectories from `p` to `q` and from `q` to `r`.
  rw [← finsum_mem_setOf_and_and_mem_and_mem
    (P := fun q : criticalPoints 𝓘(ℝ, E) f ↦
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (Q := fun q ↦ manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (A := (hX.morseTrajectorySlice p ·)) (B := (hX.morseTrajectorySlice · r))
    (g := fun q z ↦ if hpq : _ then hX.trajectorySign (𝔬.chart p) (𝔬.chart q)
      (𝔬.orientation p) (𝔬.orientation q) hpq z else 0)
    (k := fun q z ↦ if hqr : _ then hX.trajectorySign (𝔬.chart q) (𝔬.chart r)
      (𝔬.orientation q) (𝔬.orientation r) hqr z else 0)
    (fun _ ↦ h.finite_morseTrajectorySlice hf) (fun _ ↦ h.finite_morseTrajectorySlice hf)
    (fun q hpq ↦ ?_) (fun _ ↦ signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one)
    (fun q hqr ↦ ?_) (fun _ ↦ signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one)]
  · refine finsum_mem_congr (Set.ext fun _ ↦ hX.mem_morseBrokenTrajectorySet.symm) fun x hx ↦ ?_
    obtain ⟨hpq, hqr, -⟩ := hX.mem_morseBrokenTrajectorySet.1 hx
    rw [brokenTrajectorySign_of_morseIndex_eq_add_one hpq hqr, dite_eq_left hpq, dite_eq_left hqr]
  · rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq, signedTrajectoryCount_def]
    exact finsum_mem_congr rfl fun _ _ ↦ by rw [dite_eq_left hpq]
  · rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hqr, signedTrajectoryCount_def]
    exact finsum_mem_congr rfl fun _ _ ↦ by rw [dite_eq_left hqr]

include h in
/-- **`∂² = 0` reduces to signed counts of broken trajectories.** The Morse boundary with
coefficients in a ring `R` squares to zero exactly when, between any two critical points, the
signs of the broken index-two trajectories sum to zero in `R`. In particular, if these integer
sums vanish, then the boundary squares to zero over every ring. -/
theorem signedMorseBoundary_comp_signedMorseBoundary_eq_zero_iff {R : Type*} [Ring R] :
    hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0 ↔
      ∀ p r : criticalPoints 𝓘(ℝ, E) f,
        ((∑ᶠ x ∈ hX.morseBrokenTrajectorySet p r, hX.brokenTrajectorySign 𝔬 p r x : ℤ) : R) =
          0 := by
  simp_rw [← h.signedMorseBoundary_signedMorseBoundary_single_apply hf]
  constructor
  · intro h0 p r
    simpa using DFunLike.congr_fun (LinearMap.congr_fun h0 (Finsupp.single p 1)) r
  · intro h0
    refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun r ↦ ?_
    -- The boundary of `a • p` is `a` times the boundary of `p`.
    rw [LinearMap.comp_apply, ← Finsupp.smul_single_one, map_smul, map_smul]
    simp [h0]

include h hf in
/-- **The signed count of broken trajectories reduces to their number modulo two.** -/
theorem intCast_finsum_mem_brokenTrajectorySign (p r : criticalPoints 𝓘(ℝ, E) f) :
    ((∑ᶠ x ∈ hX.morseBrokenTrajectorySet p r, hX.brokenTrajectorySign 𝔬 p r x : ℤ) : ZMod 2) =
      ((hX.morseBrokenTrajectorySet p r).ncard : ZMod 2) := by
  rw [← h.signedMorseBoundary_signedMorseBoundary_single_apply hf,
    h.signedMorseBoundary_eq_morseBoundary, h.morseBoundary_morseBoundary_single_apply]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti

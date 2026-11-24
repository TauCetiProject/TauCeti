/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.FundamentalChain
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedAugmentation

/-!
# The integral Morse boundary at a unique maximum and a unique minimum

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, `X` a
Morse–Smale pseudo-gradient adapted to `f`, and `𝔬 : TauCeti.MorseOrientation f X` a choice of
orientations of the unstable manifolds. This file is the integral counterpart of
`TauCeti.Geometry.Manifold.Morse.Boundary.UniqueExtremum`, which treats the mod-two boundary. The
declarations below are in the namespace `TauCeti.IsAdaptedPseudoGradient`.

* **A unique maximum on an oriented manifold is an integral cycle.** If `M` is orientable and `f`
  has a single critical point `p` of index `n`, then every coefficient of the integral Morse
  boundary of `p` vanishes
  (`IsMorseSmale.signedMorseBoundaryCoeff_eq_zero_of_unique_index_finrank`). For an orientation
  of `M`, the fundamental chain of the integral Morse complex is a cycle
  (`IsMorseSmale.signedMorseBoundary_signedMorseFundamentalChain`),
  and here it is `±p`. Geometrically, the two trajectories into a critical point of index `n - 1`
  both come from `p`, and the orientation of `M` makes them cancel.
* **A unique minimum is never reached**: the dual statement, that the integral Morse boundary of a
  critical point of index `1` vanishes when `f` has a single critical point of index `0`, needs no
  orientation of `M`
  (`IsMorseSmale.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero`).

The orientability hypothesis cannot be dropped from the first statement. On the real projective
plane, the moment function has a single maximum, a single saddle and a single minimum, and the two
trajectories from the maximum to the saddle carry the same sign, so that the integral boundary of
the maximum is twice the saddle, up to sign, while its mod-two boundary vanishes.

On a surface every coefficient of the Morse boundary joins a critical point of index `2` to one of
index `1`, or a critical point of index `1` to one of index `0`. So the integral Morse boundary of a
Morse–Smale pair on a compact orientable surface vanishes as soon as `f` has at most one critical
point of index `2` and at most one of index `0`
(`IsMorseSmale.signedMorseBoundary_eq_zero_of_finrank_eq_two`),
with coefficients in any ring and whatever the orientations `𝔬`. The standard Morse function on the
torus is such a function (`IsMorseSmale.signedMorseBoundary_sphereHeight_comp_fst_add_comp_snd`):
its integral Morse complex is free on one generator in degrees `0` and `2` and two in degree `1`,
with zero differential, and its homology is the integral homology `ℤ, ℤ², ℤ` of the torus.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `signedMorseBoundaryCoeff_eq_zero_of_unique_index_finrank`: on an orientable manifold, every
  coefficient of the integral boundary of the only critical point of index `n` vanishes.
* `signedMorseBoundary_single_eq_zero_of_unique_index_finrank`: on an orientable manifold, the
  only critical point of index `n` is an integral cycle, with coefficients in any ring.
* `signedMorseBoundary_eq_zero_of_finrank_eq_two`: on a compact orientable surface, the integral
  Morse boundary vanishes when `f` has at most one critical point of index `2` and at most one of
  index `0`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations, and the integral Morse complex of the
  torus).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex, and its computation for the torus and the real projective plane).
-/

public section

open Set Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient.IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
  (𝔬 : MorseOrientation f X)
include h hf

/-- **At a unique maximum of an oriented manifold, the integral boundary vanishes.** Under the
Morse–Smale condition, if `M` is orientable and `p` is the only critical point of index
`n = dim M`, then every coefficient of the integral Morse boundary of `p` vanishes, whatever the
orientations of the unstable manifolds. -/
theorem signedMorseBoundaryCoeff_eq_zero_of_unique_index_finrank [Orientable 𝓘(ℝ, E) M]
    {p : criticalPoints 𝓘(ℝ, E) f} (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 →
      manifoldMorseIndex 𝓘(ℝ, E) f y = finrank ℝ E → y = p)
    (q : criticalPoints 𝓘(ℝ, E) f) : hX.signedMorseBoundaryCoeff 𝔬 p q = 0 := by
  obtain ⟨oM⟩ := Orientable.nonempty_orientation (I := 𝓘(ℝ, E)) (M := M)
  -- In the cycle relation of the fundamental chain, only the term of `p` survives.
  have hsum := h.finsum_fundamentalSign_mul_signedMorseBoundaryCoeff hf 𝔬 (oM := oM) q
  rw [finsum_eq_single _ p fun p' hp' ↦ ?_] at hsum
  · rcases fundamentalSign_eq_one_or_eq_neg_one (hX := hX) (𝔬 := 𝔬) (oM := oM) hp with
      h1 | h1 <;> simpa [h1] using hsum
  · refine mul_eq_zero_of_left (fundamentalSign_of_morseIndex_ne fun hp'n ↦ hp' ?_) _
    exact Subtype.ext (huniq p' (mem_criticalPoints_iff_mfderiv_eq_zero.1 p'.property) hp'n)

/-- **On an oriented manifold, a unique maximum is an integral cycle.** Under the Morse–Smale
condition, if `M` is orientable and `f` has at most one critical point of index `n = dim M`, then
the integral Morse boundary of that critical point vanishes, with coefficients in any ring and
whatever the orientations of the unstable manifolds. -/
theorem signedMorseBoundary_single_eq_zero_of_unique_index_finrank [Orientable 𝓘(ℝ, E) M]
    {R : Type*} [Ring R] {p : criticalPoints 𝓘(ℝ, E) f}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E)
    (hmax : {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x = finrank ℝ E}.Subsingleton)
    (a : R) : hX.signedMorseBoundary 𝔬 hf R (Finsupp.single p a) = 0 := by
  ext q
  rw [signedMorseBoundary_single_apply, Finsupp.coe_zero, Pi.zero_apply,
    h.signedMorseBoundaryCoeff_eq_zero_of_unique_index_finrank hf 𝔬 hp
      (fun y hy hyn ↦ hmax ⟨hy, hyn⟩ ⟨mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property, hp⟩),
    Int.cast_zero, mul_zero]

/-- **On an orientable surface with one maximum and one minimum, the integral Morse boundary
vanishes.** Under the Morse–Smale condition, on a compact orientable surface, if `f` has at most
one critical point of index `2` and at most one of index `0`, then the integral Morse boundary is
zero, with coefficients in any ring and whatever the orientations of the unstable manifolds. -/
theorem signedMorseBoundary_eq_zero_of_finrank_eq_two [Orientable 𝓘(ℝ, E) M]
    (hE : finrank ℝ E = 2)
    (hmax : {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x = 2}.Subsingleton)
    (hmin : {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f x = 0}.Subsingleton)
    (R : Type*) [Ring R] : hX.signedMorseBoundary 𝔬 hf R = 0 := by
  have hcoeff (p q : criticalPoints 𝓘(ℝ, E) f) : hX.signedMorseBoundaryCoeff 𝔬 p q = 0 := by
    by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
    · have hle : manifoldMorseIndex 𝓘(ℝ, E) f p ≤ finrank ℝ E :=
        manifoldMorseIndex_le_finrank
      have hp := mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property
      have hq := mem_criticalPoints_iff_mfderiv_eq_zero.1 q.property
      -- On a surface, the indices of `p` and `q` are `2` and `1`, or `1` and `0`.
      rcases (by omega : manifoldMorseIndex 𝓘(ℝ, E) f p = 2 ∨
          manifoldMorseIndex 𝓘(ℝ, E) f q = 0) with hp2 | hq0
      · exact h.signedMorseBoundaryCoeff_eq_zero_of_unique_index_finrank hf 𝔬 (hE ▸ hp2)
          (fun y hy hy2 ↦ hmax ⟨hy, hE ▸ hy2⟩ ⟨hp, hp2⟩) q
      · exact h.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero hf 𝔬
          (fun y hy hy0 ↦ hmin ⟨hy, hy0⟩ ⟨hq, hq0⟩) p
    · exact signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hind
  ext p q
  simp [hcoeff]

end IsAdaptedPseudoGradient.IsMorseSmale

end TauCeti

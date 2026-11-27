/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedAugmentation
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedChainComplex
public import TauCeti.Geometry.Manifold.Morse.Sphere.PseudoGradient

/-!
# The Morse complexes of the height function on the sphere

Let `v` be a unit vector in an `(n + 1)`-dimensional real inner product space and `X` any
pseudo-gradient adapted to the height function `sphereHeight v` on the unit sphere `Sⁿ`. The
critical points of the height function are the north pole `v`, of index `n`, and the south pole
`-v`, of index `0`. This file computes the mod-two and the integral Morse complexes of the pair
`(sphereHeight v, X)`.

* `X` is Morse–Smale, whatever its choice, since both critical points have extremal index.
* The trajectories from the north pole to the south pole cross the middle level on the equator
  `⟪x, v⟫ = 0`. On the circle `S¹` the equator consists of two points.
* The mod-two Morse boundary vanishes. For `n ≠ 1` the indices of the two poles do not differ by
  one, so no trajectory is counted. For `n = 1` the two trajectories from the north pole to the
  south pole cancel modulo two.

So the mod-two Morse complex of the height function is the free `ZMod 2`-module on the two poles,
in degrees `n` and `0`, with zero differential. Its homology is the mod-two homology of `Sⁿ`.

The integral Morse boundary vanishes as well, for every adapted pseudo-gradient and every choice
`𝔬` of orientations of the unstable manifolds. Again only `n = 1` needs an argument: the south
pole is then the only critical point of index `0`, so the two trajectories from the north pole to
it carry opposite signs (`IsMorseSmale.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero`). So
the integral Morse complex of the height function, with coefficients in any ring `R`, is the free
`R`-module on the two poles with zero differential, and its homology is free of rank one in
degrees `0` and `n` (of rank two in degree `0` for `n = 0`) and zero elsewhere: over `ℤ` it is the
integral homology of `Sⁿ`.

## Main declarations

* `TauCeti.IsAdaptedPseudoGradient.isMorseSmale_sphereHeight`: every pseudo-gradient adapted to the
  height function is Morse–Smale.
* `TauCeti.IsAdaptedPseudoGradient.morseTrajectorySlice_sphereHeight`: the trajectories from the
  north pole to the south pole are read on the equator.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_sphereHeight`: the mod-two Morse
  boundary of the height function is zero.
* `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_sphereHeight`: its integral Morse boundary
  is zero, with coefficients in any ring.
* `TauCeti.IsAdaptedPseudoGradient.free_homology_signedMorseComplex_sphereHeight` and
  `TauCeti.IsAdaptedPseudoGradient.finrank_homology_signedMorseComplex_sphereHeight`: its integral
  Morse homology is free, of rank one in degrees `0` and `n`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex, and its computation for the height function on the sphere).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations and the integral Morse complex).
-/

public section

open Metric Module Set
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] {v : sphere (0 : E) 1}
  {X : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}

/-- **The height function is Morse–Smale for every pseudo-gradient.** Every pseudo-gradient adapted
to the height function on the sphere satisfies the Morse–Smale condition. -/
theorem isMorseSmale_sphereHeight (hX : IsAdaptedPseudoGradient (sphereHeight v) X) :
    hX.IsMorseSmale :=
  IsMorseSmale.of_manifoldMorseIndex_eq_zero_or_eq_finrank (isMorse_sphereHeight v) fun x hx ↦ by
    rcases (mfderiv_sphereHeight_eq_zero_iff v x).1 hx with rfl | rfl
    · exact Or.inr (by simp)
    · exact Or.inl (by simp)

/-- **The trajectories from the north pole to the south pole cross the equator.** The middle-level
slice of the trajectories from `v` to `-v` is the set of points of height zero. -/
theorem morseTrajectorySlice_sphereHeight (hX : IsAdaptedPseudoGradient (sphereHeight v) X) :
    hX.morseTrajectorySlice v (-v) = {x | sphereHeight v x = 0} := by
  have hv : ⟪(v : E), (v : E)⟫ = 1 := by simp
  ext x
  simp only [mem_morseTrajectorySlice, unstableSet_sphereHeight_self, stableSet_sphereHeight_neg,
    mem_compl_iff, mem_singleton_iff, mem_ofPred_eq, sphereHeight_apply, coe_neg_sphere,
    inner_neg_left, hv, add_neg_cancel, zero_div]
  refine ⟨fun h ↦ h.2.2, fun h ↦ ⟨?_, ?_, h⟩⟩ <;> rintro rfl <;> simp_all

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient (sphereHeight v) X} (h : hX.IsMorseSmale)
  (hf : IsMorse (𝓡 n) (sphereHeight v))

/-- Every coefficient of the mod-two Morse boundary of the height function on the sphere vanishes.
-/
@[simp]
theorem morseBoundaryCoeff_sphereHeight (p q : criticalPoints (𝓡 n) (sphereHeight v)) :
    h.morseBoundaryCoeff hf p q = 0 := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  by_cases hind : manifoldMorseIndex (𝓡 n) (sphereHeight v) p =
      manifoldMorseIndex (𝓡 n) (sphereHeight v) q + 1
  swap
  · exact h.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf hind
  rw [h.morseBoundaryCoeff_eq_ncard hf hind]
  rw [criticalPoints_sphereHeight, mem_insert_iff, mem_singleton_iff] at hp hq
  -- The indices `n` and `0` of the poles differ by one only from `v` to `-v`, and only for `n = 1`.
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
    simp only [manifoldMorseIndex_sphereHeight_self, manifoldMorseIndex_sphereHeight_neg]
      at hind <;> try omega
  obtain rfl : n = 1 := hind
  rw [hX.morseTrajectorySlice_sphereHeight, ncard_setOf_sphereHeight_eq_zero Fact.out _,
    ZMod.natCast_self]

/-- **The mod-two Morse boundary of the height function on the sphere is zero.** For every
pseudo-gradient adapted to the height function, the mod-two Morse complex is the free
`ZMod 2`-module on the two poles with zero differential. -/
@[simp]
theorem morseBoundary_sphereHeight : h.morseBoundary hf = 0 := by
  ext p q
  simp

end IsMorseSmale

/-! ### The integral Morse complex -/

variable {hX : IsAdaptedPseudoGradient (sphereHeight v) X}
  (𝔬 : MorseOrientation (sphereHeight v) X)

/-- Every coefficient of the integral Morse boundary of the height function on the sphere vanishes,
whatever the orientations of the unstable manifolds. -/
@[simp]
theorem signedMorseBoundaryCoeff_sphereHeight (p q : criticalPoints (𝓡 n) (sphereHeight v)) :
    hX.signedMorseBoundaryCoeff 𝔬 p q = 0 := by
  obtain ⟨q, hq⟩ := q
  by_cases hind : manifoldMorseIndex (𝓡 n) (sphereHeight v) p =
      manifoldMorseIndex (𝓡 n) (sphereHeight v) q + 1
  swap
  · exact signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hind
  have hp : (p : sphere (0 : E) 1) = v ∨ (p : sphere (0 : E) 1) = -v := by
    simpa using p.property
  rw [criticalPoints_sphereHeight, mem_insert_iff, mem_singleton_iff] at hq
  -- The indices `n` and `0` of the poles differ by one only from `v` to `-v`, and only for `n = 1`.
  obtain ⟨rfl, hn⟩ : q = -v ∧ n = 1 := by
    rcases hp with hp | hp <;> rcases hq with rfl | rfl <;>
      simp only [hp, manifoldMorseIndex_sphereHeight_self, manifoldMorseIndex_sphereHeight_neg]
        at hind <;> first | omega | exact ⟨rfl, hind⟩
  -- The south pole is then the only critical point of index `0`.
  refine (hX.isMorseSmale_sphereHeight).signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero
    (isMorse_sphereHeight v) 𝔬 (fun y hy hy0 ↦ ?_) p
  rcases (mfderiv_sphereHeight_eq_zero_iff v y).1 hy with rfl | rfl
  · simp [hn] at hy0
  · rfl

/-- **The integral Morse boundary of the height function on the sphere is zero.** For every
pseudo-gradient adapted to the height function and every choice of orientations of the unstable
manifolds, the integral Morse complex, with coefficients in any ring, is the free module on the two
poles with zero differential. -/
@[simp]
theorem signedMorseBoundary_sphereHeight (hf : IsMorse (𝓡 n) (sphereHeight v)) (R : Type*)
    [Ring R] : hX.signedMorseBoundary 𝔬 hf R = 0 := by
  ext p q
  simp

/-- **The integral Morse homology of the sphere is free.** For every pseudo-gradient adapted to the
height function and every choice of orientations, the integral Morse homology, with coefficients in
any ring, is a free module in each degree, since the integral Morse boundary vanishes. -/
theorem free_homology_signedMorseComplex_sphereHeight (hf : IsMorse (𝓡 n) (sphereHeight v))
    {R : Type*} [Ring R]
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) (k : ℕ) :
    Module.Free R ((hX.signedMorseComplex 𝔬 hf R hsq).homology k) :=
  free_homology_signedMorseComplex_of_signedMorseBoundary_eq_zero hsq
    (signedMorseBoundary_sphereHeight 𝔬 hf R) k

/-- **The integral Morse homology of the sphere.** For every pseudo-gradient adapted to the height
function on `Sⁿ` and every choice of orientations of the unstable manifolds, the integral Morse
homology, with coefficients in any ring with the strong rank condition such as `ℤ`, has rank one in
degrees `0` and `n` and vanishes in every other degree; for `n = 0` it has rank two in degree `0`.
Over `ℤ` it is the integral homology of `Sⁿ`. -/
theorem finrank_homology_signedMorseComplex_sphereHeight (hf : IsMorse (𝓡 n) (sphereHeight v))
    {R : Type*} [Ring R] [StrongRankCondition R]
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) (k : ℕ) :
    finrank R ((hX.signedMorseComplex 𝔬 hf R hsq).homology k) =
      (if k = n then 1 else 0) + if k = 0 then 1 else 0 := by
  rw [finrank_homology_signedMorseComplex_of_signedMorseBoundary_eq_zero hsq
    (signedMorseBoundary_sphereHeight 𝔬 hf R), criticalCount_sphereHeight]
  split_ifs <;> norm_num

end IsAdaptedPseudoGradient

end TauCeti

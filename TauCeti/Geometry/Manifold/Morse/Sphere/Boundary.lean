/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
public import TauCeti.Geometry.Manifold.Morse.Sphere.PseudoGradient

/-!
# The mod-two Morse complex of the height function on the sphere

Let `v` be a unit vector in an `(n + 1)`-dimensional real inner product space and `X` any
pseudo-gradient adapted to the height function `sphereHeight v` on the unit sphere `Sⁿ`. The
critical points of the height function are the north pole `v`, of index `n`, and the south pole
`-v`, of index `0`. This file computes the mod-two Morse complex of the pair `(sphereHeight v, X)`.

* `X` is Morse–Smale, whatever its choice, since both critical points have extremal index.
* The trajectories from the north pole to the south pole cross the middle level on the equator
  `⟪x, v⟫ = 0`. On the circle `S¹` the equator consists of two points.
* The mod-two Morse boundary vanishes. For `n ≠ 1` the indices of the two poles do not differ by
  one, so no trajectory is counted. For `n = 1` the two trajectories from the north pole to the
  south pole cancel modulo two.

So the mod-two Morse complex of the height function is the free `ZMod 2`-module on the two poles,
in degrees `n` and `0`, with zero differential. Its homology is the mod-two homology of `Sⁿ`.

## Main declarations

* `TauCeti.criticalPoints_sphereHeight`: the critical points of the height function are the poles.
* `TauCeti.ncard_setOf_sphereHeight_eq_zero`: the equator of the circle has two points.
* `TauCeti.IsAdaptedPseudoGradient.isMorseSmale_sphereHeight`: every pseudo-gradient adapted to the
  height function is Morse–Smale.
* `TauCeti.IsAdaptedPseudoGradient.morseTrajectorySlice_sphereHeight`: the trajectories from the
  north pole to the south pole are read on the equator.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_sphereHeight`: the mod-two Morse
  boundary of the height function is zero.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex, and its computation for the height function on the sphere).
-/

public section

open Metric Module Set
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The critical points of the height function on the sphere are the north pole `v` and the south
pole `-v`. -/
@[simp]
theorem criticalPoints_sphereHeight (v : sphere (0 : E) 1) :
    criticalPoints (𝓡 n) (sphereHeight v) = {v, -v} := by
  ext x
  simp

omit [Fact (finrank ℝ E = n + 1)] in
/-- **The equator of the circle has two points.** In a two-dimensional real inner product space,
exactly two points of the unit circle have height zero in the direction of a unit vector `v`. -/
theorem ncard_setOf_sphereHeight_eq_zero (hE : finrank ℝ E = 2) (v : sphere (0 : E) 1) :
    {x | sphereHeight v x = 0}.ncard = 2 := by
  have : Fact (finrank ℝ E = 1 + 1) := ⟨hE⟩
  -- The equator is the unit circle of the line `K = (ℝ ∙ v)ᗮ`, which is `{w, -w}` for a unit `w`.
  set K := (ℝ ∙ (v : E))ᗮ
  have hK : finrank ℝ K = 1 :=
    Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere v)
  have : Nontrivial K := Module.nontrivial_of_finrank_eq_succ hK
  obtain ⟨w, hw⟩ := exists_norm_eq K zero_le_one
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hwK : ⟪(w : E), (v : E)⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.1 w.2
  let u : sphere (0 : E) 1 := ⟨w, by simpa using hw⟩
  rw [ncard_eq_two]
  refine ⟨u, -u, ne_neg_of_mem_unit_sphere ℝ u, ?_⟩
  ext x
  simp only [mem_ofPred_eq, sphereHeight_apply, mem_insert_iff, mem_singleton_iff]
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' w hw0).1 hK
      ⟨x, Submodule.mem_orthogonal_singleton_iff_inner_left.2 hx⟩
    have hcx : c • (w : E) = x := congrArg Subtype.val hc
    have hc1 : |c| = 1 := by
      have := congrArg norm hcx
      rwa [norm_smul, Submodule.norm_coe, hw, mul_one, Real.norm_eq_abs,
        norm_eq_of_mem_sphere] at this
    rcases abs_eq zero_le_one |>.1 hc1 with rfl | rfl
    · exact Or.inl (Subtype.ext (by simpa [u] using hcx.symm))
    · exact Or.inr (Subtype.ext (by simpa [u] using hcx.symm))
  · rintro (rfl | rfl)
    · exact hwK
    · simp [u, hwK]

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
theorem morseBoundary_sphereHeight : h.morseBoundary hf = 0 := by
  ext p q
  simp

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti

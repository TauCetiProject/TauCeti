/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.UniqueExtremum
public import TauCeti.Geometry.Manifold.Morse.Sphere.PseudoGradient

/-!
# The Morse boundary and trajectory signs of the height function on the sphere

Let `v` be a unit vector in an `(n + 1)`-dimensional real inner product space and `X` any
pseudo-gradient adapted to the height function `sphereHeight v` on the unit sphere `Sⁿ`. The
critical points of the height function are the north pole `v`, of index `n`, and the south pole
`-v`, of index `0`. This file computes the mod-two Morse complex and the signed trajectory counts
of the pair `(sphereHeight v, X)`.

* `X` is Morse–Smale, whatever its choice, since both critical points have extremal index.
* The trajectories from the north pole to the south pole cross the middle level on the equator
  `⟪x, v⟫ = 0`. On the circle `S¹` the equator consists of two points.
* The mod-two Morse boundary vanishes. For `n ≠ 1` the indices of the two poles do not differ by
  one, so no trajectory is counted. For `n = 1` the two trajectories from the north pole to the
  south pole cancel modulo two.
* With orientations of the unstable manifolds, for `n = 1` the two trajectories on `S¹` from `v`
  to `-v` carry opposite signs `+1` and `-1`, so the signed trajectory count vanishes for every
  `n`.

So both the mod-two and the integral Morse differentials of the height function vanish, recovering
the homology of `Sⁿ` in degrees `n` and `0`.

## Main declarations

* `TauCeti.IsAdaptedPseudoGradient.isMorseSmale_sphereHeight`: every pseudo-gradient adapted to the
  height function is Morse–Smale.
* `TauCeti.IsAdaptedPseudoGradient.morseTrajectorySlice_sphereHeight`: the trajectories from the
  north pole to the south pole are read on the equator.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.morseBoundary_sphereHeight`: the mod-two Morse
  boundary of the height function is zero.
* `TauCeti.IsAdaptedPseudoGradient.exists_trajectorySign_sphereHeight_eq_one_and_eq_neg_one` and
  `TauCeti.IsAdaptedPseudoGradient.signedTrajectoryCount_sphereHeight`: between any
  consecutive-index critical points on `Sⁿ` (which occurs only for `n = 1`, `p = v`, and `q = -v`),
  the two trajectories carry opposite signs `+1` and `-1`, and every signed trajectory count
  vanishes.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex, and its computation for the height function on the sphere).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations and signed trajectory counts on `S¹` and
  `Sⁿ`).
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

omit [FiniteDimensional ℝ E] in
private theorem eq_poles_of_manifoldMorseIndex_eq_add_one {p q : sphere (0 : E) 1}
    (hp : mfderiv (𝓡 n) 𝓘(ℝ) (sphereHeight v) p = 0)
    (hq : mfderiv (𝓡 n) 𝓘(ℝ) (sphereHeight v) q = 0)
    (hpq : manifoldMorseIndex (𝓡 n) (sphereHeight v) p =
      manifoldMorseIndex (𝓡 n) (sphereHeight v) q + 1) :
    p = v ∧ q = -v ∧ n = 1 := by
  rcases (mfderiv_sphereHeight_eq_zero_iff v p).1 hp with hpv | hpv <;>
    rcases (mfderiv_sphereHeight_eq_zero_iff v q).1 hq with hqv | hqv <;>
    simp only [hpv, hqv, manifoldMorseIndex_sphereHeight_self,
      manifoldMorseIndex_sphereHeight_neg] at hpq <;>
    try omega
  exact ⟨hpv, hqv, hpq⟩

/-- **Opposite trajectory signs on the sphere.** Between any critical points `p` and `q` of
consecutive index for `sphereHeight v` on `Sⁿ` (which occurs only for `n = 1`, `p = v`, and
`q = -v`), the two trajectories from `p` to `q` carry opposite signs `+1` and `-1` for any Morse
charts in which `X` is linear and any orientations. -/
theorem exists_trajectorySign_sphereHeight_eq_one_and_eq_neg_one
    (hX : IsAdaptedPseudoGradient (sphereHeight v) X) {p q : sphere (0 : E) 1}
    {φp : MorseChart (EuclideanSpace ℝ (Fin n)) (sphereHeight v) p}
    {φq : MorseChart (EuclideanSpace ℝ (Fin n)) (sphereHeight v) q}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hφq : ∀ y ∈ φq.toChart.source,
      φq.coord (mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) φq.toChart y (X y)) =
        fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex (𝓡 n) (sphereHeight v) p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex (𝓡 n) (sphereHeight v) q)))
    (hpq : manifoldMorseIndex (𝓡 n) (sphereHeight v) p =
      manifoldMorseIndex (𝓡 n) (sphereHeight v) q + 1) :
    ∃ y₁ ∈ hX.morseTrajectorySlice p q, ∃ y₂ ∈ hX.morseTrajectorySlice p q,
      hX.trajectorySign φp φq op oq hpq y₁ = 1 ∧ hX.trajectorySign φp φq op oq hpq y₂ = -1 := by
  obtain ⟨hpv, hqv, rfl⟩ := eq_poles_of_manifoldMorseIndex_eq_add_one
    ((φp.mfderiv_eq_zero_iff φp.mem_source).2 rfl)
    ((φq.mfderiv_eq_zero_iff φq.mem_source).2 rfl) hpq
  subst p q
  refine (hX.isMorseSmale_sphereHeight
    ).exists_trajectorySign_eq_one_and_eq_neg_one_of_unique_index_zero
    (isMorse_sphereHeight v) hφp hφq op oq (manifoldMorseIndex_sphereHeight_neg v) hpq
    fun y hy hy0 ↦ ?_
  rcases (mfderiv_sphereHeight_eq_zero_iff v y).1 hy with rfl | rfl
  · simp only [manifoldMorseIndex_sphereHeight_self] at hy0
    omega
  · rfl

/-- **Signed trajectory counts of the height function on the sphere vanish.** Between any critical
points `p` and `q` of consecutive index on `Sⁿ` (which occurs only for `n = 1`, `p = v`, and
`q = -v`), the signed count of trajectories of `sphereHeight v` vanishes. -/
theorem signedTrajectoryCount_sphereHeight (hX : IsAdaptedPseudoGradient (sphereHeight v) X)
    {p q : sphere (0 : E) 1}
    {φp : MorseChart (EuclideanSpace ℝ (Fin n)) (sphereHeight v) p}
    {φq : MorseChart (EuclideanSpace ℝ (Fin n)) (sphereHeight v) q}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) φp.toChart y (X y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex (𝓡 n) (sphereHeight v) p)))
    (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex (𝓡 n) (sphereHeight v) q)))
    (hpq : manifoldMorseIndex (𝓡 n) (sphereHeight v) p =
      manifoldMorseIndex (𝓡 n) (sphereHeight v) q + 1) :
    hX.signedTrajectoryCount φp φq op oq hpq = 0 := by
  obtain ⟨hpv, hqv, rfl⟩ := eq_poles_of_manifoldMorseIndex_eq_add_one
    ((φp.mfderiv_eq_zero_iff φp.mem_source).2 rfl)
    ((φq.mfderiv_eq_zero_iff φq.mem_source).2 rfl) hpq
  subst p q
  exact hX.signedTrajectoryCount_eq_zero_of_mem_stableSet (φ := φp) (φq := φq) (op := op)
    (oq := oq) (hpq := hpq) hφp (isMorse_sphereHeight v) (manifoldMorseIndex_sphereHeight_self v)
    fun _ _ hy ↦ by simpa [stableSet_sphereHeight_neg] using hy

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
  -- The indices `n` and `0` of the poles differ by one only from `v` to `-v`, and only for `n = 1`.
  obtain ⟨hpv, hqv, rfl⟩ := eq_poles_of_manifoldMorseIndex_eq_add_one
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 hp)
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 hq) hind
  subst p q
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

end IsAdaptedPseudoGradient

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.MaslovIndex
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

/-!
# Nice Heegaard diagrams and the index of their positive domains

A pointed Heegaard diagram is *nice* (Sarkar–Wang) when every region containing no basepoint is
a bigon or a square: a disk with two or four corners. In a nice diagram the hat differential
counts positive domains of Maslov index one avoiding the basepoints, and each of them is an empty
embedded bigon or an empty embedded rectangle, so the chain complex is computed combinatorially.
This file proves the index estimate behind this, for the abstract region incidence data
`TauCeti.HeegaardRegionSystem` with region Euler characteristics `χ`.

Lipshitz's formula `μ(D) = e(D) + n_x(D) + n_y(D)` (`TauCeti.HeegaardRegionSystem.maslovIndex`)
splits the index into an Euler measure and two point measures. For a nonnegative domain `D` from
`x` to `y`, each `α`-curve on which `x` and `y` have different points contributes a corner of `D`
at the point of `x` and one at the point of `y`, so it contributes at least `1 / 4` to each of
`n_x(D)` and `n_y(D)`. In a nice diagram a bigon has Euler measure `1 / 2` and a square has Euler
measure `0`, so `e(D) ≥ 0` when `D` avoids the basepoints. Hence, if `x` and `y` differ on `m`
curves, then `μ(D) ≥ m / 2`. The point-measure half of this estimate,
`TauCeti.HeegaardRegionSystem.IsDomainBetween.eulerMeasure_add_half_hammingDist_le_maslovIndex`,
holds in every diagram; niceness supplies the sign of the Euler measure.

In particular, in a nice diagram a positive domain of index at most one avoiding the basepoints
moves at most two points. If the diagram is also weakly admissible, the only such domain of index
at most zero is zero, so one of index one moves exactly one point, as a bigon does, or exactly
two, as a rectangle does.

The index budget then pins down such a domain near the points of `x` and `y`. The Euler measure
of a domain avoiding the basepoints is half its total multiplicity on the bigons
(`TauCeti.HeegaardRegionSystem.IsNice.eulerMeasure_eq`). If the domain moves two points, the
estimate `μ(D) ≥ e(D) + m / 2` is an equality: the domain has multiplicity zero on every bigon,
it is a convex corner at each of the four moved points, and it vanishes on the four corners at
every other point of `x`. These are the corners and the emptiness of a rectangle. If the domain
moves one point, its total multiplicity on the bigons is at most one, and when it meets a bigon
the estimate is again an equality, with the same consequences at the two moved points and at the
other points of `x`, which are those of a bigon. The equality case itself is
`TauCeti.HeegaardRegionSystem.IsDomainBetween.pointMeasure_point_left_eq_inv_four_of_maslovIndex_le`
and its companions in `TauCeti.LowDimTopology.Heegaard.MaslovIndex`. That such a domain is an
embedded rectangle or bigon, with multiplicities zero and one, is a statement about the surface
and is not proved here; neither is the remaining bigon case of a domain made of squares only.

## Main definitions

* `TauCeti.HeegaardRegionSystem.IsNice`: every region containing no basepoint is a bigon or a
  square.

## Main results

* `TauCeti.HeegaardRegionSystem.IsNice.eulerMeasure_nonneg`: in a nice diagram, a nonnegative
  domain avoiding the basepoints has nonnegative Euler measure.
* `TauCeti.HeegaardRegionSystem.IsNice.hammingDist_le_two_mul_maslovIndex`: in a nice diagram,
  `m ≤ 2 μ(D)` for a nonnegative domain `D` from `x` to `y` avoiding the basepoints, where `m`
  is the Hamming distance between the points of `x` and `y`: the number of `α`-curves on which
  they differ.
* `TauCeti.HeegaardRegionSystem.IsNice.maslovIndex_nonneg`: in a nice diagram, a nonnegative
  domain avoiding the basepoints has nonnegative Maslov index between any two generators.
* `TauCeti.HeegaardRegionSystem.IsNice.hammingDist_le_two_of_maslovIndex_le_one`: in a nice
  diagram, a nonnegative domain from `x` to `y` avoiding the basepoints of index at most one
  moves at most two points.
* `TauCeti.HeegaardRegionSystem.IsNice.hammingDist_eq_one_or_eq_two_of_maslovIndex_eq_one`: in
  a weakly admissible nice diagram, such a domain of index one moves exactly one or two points.
* `TauCeti.HeegaardRegionSystem.IsNice.eq_zero_of_maslovIndex_nonpos`: in a weakly admissible
  nice diagram, such a domain of index at most zero is zero.
* `TauCeti.HeegaardRegionSystem.IsNice.eulerMeasure_eq`: in a nice diagram, the Euler measure of
  a domain avoiding the basepoints is half its multiplicity on the bigons.
* `TauCeti.HeegaardRegionSystem.IsNice.eulerMeasure_eq_zero_iff`: such a nonnegative domain has
  Euler measure zero exactly when it avoids the bigons.
* `IsNice.maslovIndex_le_eulerMeasure_add_half_hammingDist_of_hammingDist_eq_two`
  and `TauCeti.HeegaardRegionSystem.IsNice.eulerMeasure_eq_zero_of_hammingDist_eq_two`: a domain
  of index at most one moving two points attains the index estimate and avoids the bigons.
* `TauCeti.HeegaardRegionSystem.IsNice.sum_cornerCount_eq_two_le_one_of_ne`: a domain of index
  at most one between distinct generators has total multiplicity at most one on the bigons.
* `IsNice.maslovIndex_le_eulerMeasure_add_half_hammingDist_of_cornerCount_eq_two`:
  a domain of index at most one meeting a bigon attains the index estimate.

## References

* S. Sarkar and J. Wang, *An algorithm for computing some Heegaard Floer homologies*, Ann. of
  Math. **171** (2010), [arXiv:math/0607777](https://arxiv.org/abs/math/0607777), §3 (nice
  diagrams, and the index estimate in the classification of their index-one positive domains).
* R. Lipshitz, *A cylindrical reformulation of Heegaard Floer homology*, Geom. Topol. **10**
  (2006), [arXiv:math/0502404](https://arxiv.org/abs/math/0502404), §4 (the index formula).
* P. Ozsváth, A. Stipsicz and Z. Szabó, *Combinatorial Heegaard Floer homology and nice Heegaard
  diagrams*, Adv. Math. **231** (2012), [arXiv:0912.0830](https://arxiv.org/abs/0912.0830)
  (nice diagrams with several basepoints).
-/

public section

namespace TauCeti

namespace HeegaardRegionSystem

universe u v w

variable {n : ℕ} {Point : Type u} {Region : Type v} {Basepoint : Type w}
  {H : HeegaardRegionSystem n Point Region Basepoint} {x y : H.Generator} {D : Region → ℤ}

open Finset

section Nice

variable [Fintype Point] [DecidableEq Region]

variable (H) in
/-- A pointed Heegaard diagram, with region Euler characteristics `χ`, is *nice* when every
region containing no basepoint is a bigon or a square: a disk, of Euler characteristic one, with
two or four corners. -/
def IsNice (χ : Region → ℤ) : Prop :=
  ∀ r, (∀ z, H.basepoint z ≠ r) → χ r = 1 ∧ (H.cornerCount r = 2 ∨ H.cornerCount r = 4)

variable {χ : Region → ℤ}

/-- Unfolding `TauCeti.HeegaardRegionSystem.IsNice`. -/
theorem isNice_iff : H.IsNice χ ↔
    ∀ r, (∀ z, H.basepoint z ≠ r) → χ r = 1 ∧ (H.cornerCount r = 2 ∨ H.cornerCount r = 4) :=
  Iff.rfl

variable [Fintype Region]

/-- In a nice diagram, the Euler measure of a domain avoiding the basepoints is half its total
multiplicity on the bigons, the regions with two corners: a bigon has Euler measure `1 / 2` and
a square has Euler measure `0`. -/
theorem IsNice.eulerMeasure_eq (h : H.IsNice χ) (hz : ∀ z, D (H.basepoint z) = 0) :
    H.eulerMeasure χ D = (∑ r with H.cornerCount r = 2, (D r : ℚ)) / 2 := by
  rw [eulerMeasure_apply, sum_filter, sum_div]
  refine sum_congr rfl fun r _ => ?_
  by_cases hr : ∃ z, H.basepoint z = r
  · obtain ⟨z, rfl⟩ := hr
    simp [hz z]
  · push Not at hr
    obtain ⟨hχ, hk | hk⟩ := h r hr
    · simp [hχ, hk]
      ring
    · simp [hχ, hk]

/-- In a nice diagram, a nonnegative domain avoiding the basepoints has nonnegative Euler
measure: bigons have Euler measure `1 / 2` and squares have Euler measure `0`. -/
theorem IsNice.eulerMeasure_nonneg (h : H.IsNice χ) (hD0 : 0 ≤ D)
    (hz : ∀ z, D (H.basepoint z) = 0) : 0 ≤ H.eulerMeasure χ D := by
  rw [h.eulerMeasure_eq hz]
  exact div_nonneg (sum_nonneg fun r _ => by exact_mod_cast hD0 r) zero_le_two

/-- In a nice diagram, a nonnegative domain avoiding the basepoints has Euler measure zero
exactly when it has multiplicity zero on every bigon. -/
theorem IsNice.eulerMeasure_eq_zero_iff (h : H.IsNice χ) (hD0 : 0 ≤ D)
    (hz : ∀ z, D (H.basepoint z) = 0) :
    H.eulerMeasure χ D = 0 ↔ ∀ r, H.cornerCount r = 2 → D r = 0 := by
  rw [h.eulerMeasure_eq hz, div_eq_zero_iff, or_iff_left two_ne_zero,
    sum_eq_zero_iff_of_nonneg fun r _ => by exact_mod_cast hD0 r]
  simp

/-- In a nice diagram, a nonnegative domain from `x` to `y` avoiding the basepoints has Maslov
index at least half the number of `α`-curves on which `x` and `y` differ. -/
theorem IsNice.hammingDist_le_two_mul_maslovIndex [DecidableEq Point] (h : H.IsNice χ)
    (hD : H.IsDomainBetween x y D) (hD0 : 0 ≤ D) (hz : ∀ z, D (H.basepoint z) = 0) :
    (hammingDist (H.point x) (H.point y) : ℚ) ≤ 2 * H.maslovIndex χ x y D := by
  have := hD.eulerMeasure_add_half_hammingDist_le_maslovIndex χ hD0
  linarith [h.eulerMeasure_nonneg hD0 hz]

/-- In a nice diagram, a nonnegative domain avoiding the basepoints has nonnegative Maslov
index. -/
theorem IsNice.maslovIndex_nonneg (h : H.IsNice χ) (hD0 : 0 ≤ D)
    (hz : ∀ z, D (H.basepoint z) = 0) : 0 ≤ H.maslovIndex χ x y D := by
  rw [maslovIndex_apply]
  linarith [h.eulerMeasure_nonneg hD0 hz, H.generatorPointMeasure_nonneg hD0 x,
    H.generatorPointMeasure_nonneg hD0 y]

/-- In a nice diagram, a nonnegative domain from `x` to `y` avoiding the basepoints with Maslov
index at most one moves the points of `x` on at most two `α`-curves. -/
theorem IsNice.hammingDist_le_two_of_maslovIndex_le_one [DecidableEq Point] (h : H.IsNice χ)
    (hD : H.IsDomainBetween x y D) (hD0 : 0 ≤ D) (hz : ∀ z, D (H.basepoint z) = 0)
    (hμ : H.maslovIndex χ x y D ≤ 1) : hammingDist (H.point x) (H.point y) ≤ 2 := by
  have hcard : (hammingDist (H.point x) (H.point y) : ℚ) ≤ 2 := by
    linarith [h.hammingDist_le_two_mul_maslovIndex hD hD0 hz]
  exact_mod_cast hcard

/-- In a nice diagram, a nonnegative domain from `x` to `y` avoiding the basepoints with Maslov
index at most zero connects `x` to itself. -/
theorem IsNice.eq_of_maslovIndex_nonpos (h : H.IsNice χ) (hD : H.IsDomainBetween x y D)
    (hD0 : 0 ≤ D) (hz : ∀ z, D (H.basepoint z) = 0) (hμ : H.maslovIndex χ x y D ≤ 0) :
    x = y := by
  classical
  have hcard : (hammingDist (H.point x) (H.point y) : ℚ) ≤ 0 := by
    linarith [h.hammingDist_le_two_mul_maslovIndex hD hD0 hz]
  exact H.point_injective (hammingDist_eq_zero.mp (Nat.le_zero.mp (by exact_mod_cast hcard)))

/-- In a weakly admissible nice diagram, a nonnegative domain avoiding the basepoints with
Maslov index at most zero is the zero domain. -/
theorem IsNice.eq_zero_of_maslovIndex_nonpos (h : H.IsNice χ) (hW : H.WeaklyAdmissible)
    (hD : H.IsDomainBetween x y D) (hD0 : 0 ≤ D) (hz : ∀ z, D (H.basepoint z) = 0)
    (hμ : H.maslovIndex χ x y D ≤ 0) : D = 0 := by
  obtain rfl := h.eq_of_maslovIndex_nonpos hD hD0 hz hμ
  exact weaklyAdmissible_iff.mp hW D (isDomainBetween_self_iff.mp ⟨hD, hz⟩) hD0

/-- In a weakly admissible nice diagram, a nonnegative domain from `x` to `y` avoiding the
basepoints with Maslov index one moves the points of `x` on exactly one `α`-curve, as a bigon
does, or on exactly two, as a rectangle does. -/
theorem IsNice.hammingDist_eq_one_or_eq_two_of_maslovIndex_eq_one [DecidableEq Point]
    (h : H.IsNice χ) (hW : H.WeaklyAdmissible) (hD : H.IsDomainBetween x y D) (hD0 : 0 ≤ D)
    (hz : ∀ z, D (H.basepoint z) = 0) (hμ : H.maslovIndex χ x y D = 1) :
    hammingDist (H.point x) (H.point y) = 1 ∨ hammingDist (H.point x) (H.point y) = 2 := by
  have hle := h.hammingDist_le_two_of_maslovIndex_le_one hD hD0 hz hμ.le
  have hpos : hammingDist (H.point x) (H.point y) ≠ 0 := by
    intro hcard
    obtain rfl := H.point_injective (hammingDist_eq_zero.mp hcard)
    have hD' := weaklyAdmissible_iff.mp hW D (isDomainBetween_self_iff.mp ⟨hD, hz⟩) hD0
    simp [hD'] at hμ
  omega

/-! ### Rectangles and bigons -/

/-- **Rectangles are tight.** In a nice diagram, a nonnegative domain from `x` to `y` avoiding the
basepoints, with Maslov index at most one, that moves the points of `x` on two `α`-curves has
`μ(D) ≤ e(D) + m / 2`, the equality case of the index estimate. Hence it has point measure
`1 / 4` at the four moved points, where it is a convex corner, and point measure zero at the
other points of `x`
(`IsDomainBetween.pointMeasure_point_left_eq_inv_four_of_maslovIndex_le`,
`IsDomainBetween.pointMeasure_point_right_eq_inv_four_of_maslovIndex_le`,
`TauCeti.HeegaardRegionSystem.IsDomainBetween.pointMeasure_point_eq_zero_of_maslovIndex_le`). -/
theorem IsNice.maslovIndex_le_eulerMeasure_add_half_hammingDist_of_hammingDist_eq_two
    [DecidableEq Point] (h : H.IsNice χ) (hD0 : 0 ≤ D) (hz : ∀ z, D (H.basepoint z) = 0)
    (hm : hammingDist (H.point x) (H.point y) = 2) (hμ : H.maslovIndex χ x y D ≤ 1) :
    H.maslovIndex χ x y D ≤ H.eulerMeasure χ D + hammingDist (H.point x) (H.point y) / 2 := by
  rw [hm]
  linarith [h.eulerMeasure_nonneg hD0 hz]

/-- In a nice diagram, a nonnegative domain from `x` to `y` avoiding the basepoints, with Maslov
index at most one, that moves the points of `x` on two `α`-curves has Euler measure zero, so
multiplicity zero on every bigon
(`TauCeti.HeegaardRegionSystem.IsNice.eulerMeasure_eq_zero_iff`): it is made of squares. -/
theorem IsNice.eulerMeasure_eq_zero_of_hammingDist_eq_two [DecidableEq Point] (h : H.IsNice χ)
    (hD : H.IsDomainBetween x y D) (hD0 : 0 ≤ D) (hz : ∀ z, D (H.basepoint z) = 0)
    (hm : hammingDist (H.point x) (H.point y) = 2) (hμ : H.maslovIndex χ x y D ≤ 1) :
    H.eulerMeasure χ D = 0 := by
  have := hD.eulerMeasure_add_half_hammingDist_le_maslovIndex χ hD0
  rw [hm] at this
  linarith [h.eulerMeasure_nonneg hD0 hz]

/-- In a nice diagram, a nonnegative domain from `x` to `y ≠ x` avoiding the basepoints, with
Maslov index at most one, has total multiplicity at most one on the bigons. When it moves the
points of `x` on two `α`-curves, this total is zero
(`TauCeti.HeegaardRegionSystem.IsNice.eulerMeasure_eq_zero_of_hammingDist_eq_two`). -/
theorem IsNice.sum_cornerCount_eq_two_le_one_of_ne (h : H.IsNice χ)
    (hD : H.IsDomainBetween x y D) (hD0 : 0 ≤ D) (hz : ∀ z, D (H.basepoint z) = 0) (hxy : x ≠ y)
    (hμ : H.maslovIndex χ x y D ≤ 1) :
    ∑ r with H.cornerCount r = 2, D r ≤ 1 := by
  classical
  have := hD.eulerMeasure_add_half_hammingDist_le_maslovIndex χ hD0
  have hm : (1 : ℚ) ≤ hammingDist (H.point x) (H.point y) := by
    exact_mod_cast hammingDist_pos.mpr (H.point_injective.ne hxy)
  rw [h.eulerMeasure_eq hz] at this
  have h1 : ((∑ r with H.cornerCount r = 2, D r : ℤ) : ℚ) ≤ 1 := by
    push_cast
    linarith
  exact_mod_cast h1

/-- **Domains through a bigon are tight.** In a nice diagram, a nonnegative domain from `x` to
`y ≠ x` avoiding the basepoints, with Maslov index at most one, that has nonzero multiplicity on
some bigon has `μ(D) ≤ e(D) + m / 2`, the equality case of the index estimate. Hence it has point
measure `1 / 4` at the moved points, where it is a convex corner, and point measure zero at the
other points of `x`
(`IsDomainBetween.pointMeasure_point_left_eq_inv_four_of_maslovIndex_le`,
`IsDomainBetween.pointMeasure_point_right_eq_inv_four_of_maslovIndex_le`,
`TauCeti.HeegaardRegionSystem.IsDomainBetween.pointMeasure_point_eq_zero_of_maslovIndex_le`). -/
theorem IsNice.maslovIndex_le_eulerMeasure_add_half_hammingDist_of_cornerCount_eq_two
    [DecidableEq Point] (h : H.IsNice χ) (hD0 : 0 ≤ D) (hz : ∀ z, D (H.basepoint z) = 0)
    (hxy : x ≠ y) (hμ : H.maslovIndex χ x y D ≤ 1) {r : Region} (hr : H.cornerCount r = 2)
    (hDr : D r ≠ 0) :
    H.maslovIndex χ x y D ≤ H.eulerMeasure χ D + hammingDist (H.point x) (H.point y) / 2 := by
  have hm : (1 : ℚ) ≤ hammingDist (H.point x) (H.point y) := by
    exact_mod_cast hammingDist_pos.mpr (H.point_injective.ne hxy)
  have hsum : (D r : ℚ) ≤ ∑ r with H.cornerCount r = 2, (D r : ℚ) :=
    single_le_sum (f := fun r => (D r : ℚ)) (fun r _ => by exact_mod_cast hD0 r)
      (mem_filter.mpr ⟨mem_univ r, hr⟩)
  have hDr1 : (1 : ℚ) ≤ D r := by exact_mod_cast lt_of_le_of_ne (hD0 r) (Ne.symm hDr)
  rw [h.eulerMeasure_eq hz]
  linarith

end Nice

end HeegaardRegionSystem

end TauCeti

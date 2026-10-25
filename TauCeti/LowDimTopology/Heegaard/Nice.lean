/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Heegaard.MaslovIndex
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

/-- In a nice diagram, a nonnegative domain avoiding the basepoints has nonnegative Euler
measure: bigons have Euler measure `1 / 2` and squares have Euler measure `0`. -/
theorem IsNice.eulerMeasure_nonneg (h : H.IsNice χ) (hD0 : 0 ≤ D)
    (hz : ∀ z, D (H.basepoint z) = 0) : 0 ≤ H.eulerMeasure χ D := by
  rw [eulerMeasure_apply]
  refine sum_nonneg fun r _ => ?_
  by_cases hr : ∃ z, H.basepoint z = r
  · obtain ⟨z, rfl⟩ := hr
    simp [hz z]
  · push Not at hr
    have hDr : (0 : ℚ) ≤ D r := by exact_mod_cast hD0 r
    obtain ⟨hχ, hk | hk⟩ := h r hr <;>
    · rw [hχ, hk]
      exact mul_nonneg hDr (by norm_num)

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

end Nice

end HeegaardRegionSystem

end TauCeti

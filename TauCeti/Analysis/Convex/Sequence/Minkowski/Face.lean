/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Minkowski.Basic

import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# Supporting faces of Minkowski sums

Supporting faces of a min-convolution are sums of supporting faces at the same slope.
In particular, finite faces have additive absolute endpoints, and the minimising split
at either endpoint is unique. These statements isolate the geometric input to the unique
dominant-term arguments for coefficient products.

Convexity is not needed once supporting lines and their contact sets are given. Thus the
results also apply directly to coefficient heights, before taking a convex envelope.
Singleton faces are included; no assertion is made about endpoints of infinite faces.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter IV §3.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  §1, Proposition 1.
-/

public section

namespace TauCeti

variable {h g : ℕ → WithTop ℝ} {σ c d : ℝ}

/-- Supporting lines of a common slope add to a supporting line of the Minkowski sum. -/
theorem IsSupportingLine.minkowskiSum (hc : IsSupportingLine h σ c)
    (hd : IsSupportingLine g σ d) : IsSupportingLine (minkowskiSum h g) σ (c + d) := by
  refine isSupportingLine_iff_forall.mpr fun n => ?_
  refine le_minkowskiSum_iff.mpr fun i j hij => ?_
  rw [← hij, Nat.cast_add]
  calc
    ((c + d + σ * (i + j) : ℝ) : WithTop ℝ) =
        ((c + σ * i : ℝ) : WithTop ℝ) + ((d + σ * j : ℝ) : WithTop ℝ) := by
      rw [← WithTop.coe_add, WithTop.coe_eq_coe]
      ring
    _ ≤ h i + g j := add_le_add (isSupportingLine_iff_forall.mp hc i)
      (isSupportingLine_iff_forall.mp hd j)

/-- At a contact index of the sum, a split is minimising exactly when both its indices
are contacts with the given supporting lines. -/
theorem minkowskiSum_add_eq_add_iff_of_mem_supportingFace
    (hc : IsSupportingLine h σ c) (hd : IsSupportingLine g σ d) {i j : ℕ}
    (hn : i + j ∈ supportingFace (minkowskiSum h g) σ (c + d)) :
    minkowskiSum h g (i + j) = h i + g j ↔
      i ∈ supportingFace h σ c ∧ j ∈ supportingFace g σ d := by
  refine ⟨fun heq => ?_, fun ⟨hi, hj⟩ =>
    minkowskiSum_add_eq_of_mem_supportingFace hc hi hd hj⟩
  rw [mem_supportingFace] at hn
  have hfinite : h i ≠ ⊤ ∧ g j ≠ ⊤ := WithTop.add_ne_top.mp (by
    rw [← heq, hn]
    exact WithTop.coe_ne_top)
  have hi := isSupportingLine_iff_forall.mp hc i
  have hj := isSupportingLine_iff_forall.mp hd j
  rw [← WithTop.coe_untop₀_of_ne_top hfinite.1, WithTop.coe_le_coe] at hi
  rw [← WithTop.coe_untop₀_of_ne_top hfinite.2, WithTop.coe_le_coe] at hj
  rw [heq, ← WithTop.coe_untop₀_of_ne_top hfinite.1,
    ← WithTop.coe_untop₀_of_ne_top hfinite.2, ← WithTop.coe_add,
    WithTop.coe_eq_coe, Nat.cast_add] at hn
  constructor
  · rw [mem_supportingFace, ← WithTop.coe_untop₀_of_ne_top hfinite.1,
      WithTop.coe_eq_coe]
    nlinarith
  · rw [mem_supportingFace, ← WithTop.coe_untop₀_of_ne_top hfinite.2,
      WithTop.coe_eq_coe]
    nlinarith

-- Prefer the split characterization to the generic `mem_supportingFace` simp rule.
/-- A supporting face of the Minkowski sum consists exactly of sums of contact indices
for the two supporting lines of the same slope. -/
@[simp 1100] theorem mem_supportingFace_minkowskiSum_iff (hc : IsSupportingLine h σ c)
    (hd : IsSupportingLine g σ d) {n : ℕ} :
    n ∈ supportingFace (minkowskiSum h g) σ (c + d) ↔
      ∃ i j, i + j = n ∧ i ∈ supportingFace h σ c ∧ j ∈ supportingFace g σ d := by
  constructor
  · intro hn
    obtain ⟨i, j, rfl, heq⟩ := exists_minkowskiSum_eq h g n
    exact ⟨i, j, rfl,
      (minkowskiSum_add_eq_add_iff_of_mem_supportingFace hc hd hn).mp heq⟩
  · rintro ⟨i, j, rfl, hi, hj⟩
    rw [mem_supportingFace,
      minkowskiSum_add_eq_of_mem_supportingFace hc hi hd hj]
    rw [mem_supportingFace] at hi hj
    rw [hi, hj, ← WithTop.coe_add, WithTop.coe_eq_coe, Nat.cast_add]
    ring

namespace IsFiniteFace

variable {l u l' u' : ℕ}

/-- Finite faces at a common slope add, with both absolute endpoints adding. -/
theorem minkowskiSum (hf : IsFiniteFace h σ l u) (hg : IsFiniteFace g σ l' u') :
    IsFiniteFace (minkowskiSum h g) σ (l + l') (u + u') := by
  obtain ⟨c, hc, hface⟩ := hf.exists_intercept
  obtain ⟨d, hd, gface⟩ := hg.exists_intercept
  refine isFiniteFace_iff.mpr ⟨Nat.add_le_add hf.left_le_right hg.left_le_right, c + d,
    hc.minkowskiSum hd, ?_⟩
  ext n
  rw [mem_supportingFace_minkowskiSum_iff hc hd, hface, gface,
    ← Set.Icc_add_Icc hf.left_le_right hg.left_le_right]
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    exact Set.mem_add.mpr ⟨i, hi, j, hj, hij⟩
  · intro hn
    obtain ⟨i, hi, j, hj, hij⟩ := Set.mem_add.mp hn
    exact ⟨i, j, hij, hi, hj⟩

/-- At the left endpoint of the sum face, the only minimising split uses the two left
endpoints. All indices here are absolute, not measured from the polygon's anchor. -/
theorem minkowskiSum_left_eq_iff (hf : IsFiniteFace h σ l u)
    (hg : IsFiniteFace g σ l' u') {i j : ℕ} (hij : i + j = l + l') :
    TauCeti.minkowskiSum h g (l + l') = h i + g j ↔ i = l ∧ j = l' := by
  obtain ⟨c, hc, hface⟩ := hf.exists_intercept
  obtain ⟨d, hd, gface⟩ := hg.exists_intercept
  have hl : l ∈ supportingFace h σ c := hface.symm.subset ⟨le_rfl, hf.left_le_right⟩
  have hl' : l' ∈ supportingFace g σ d := gface.symm.subset ⟨le_rfl, hg.left_le_right⟩
  have hn := (mem_supportingFace_minkowskiSum_iff hc hd).mpr ⟨l, l', rfl, hl, hl'⟩
  rw [← hij] at hn ⊢
  rw [minkowskiSum_add_eq_add_iff_of_mem_supportingFace hc hd hn]
  simp only [hface, gface, Set.mem_Icc]
  have := hf.left_le_right
  have := hg.left_le_right
  omega

/-- At the right endpoint of the sum face, the only minimising split uses the two right
endpoints. This also applies when one or both faces are singletons. -/
theorem minkowskiSum_right_eq_iff (hf : IsFiniteFace h σ l u)
    (hg : IsFiniteFace g σ l' u') {i j : ℕ} (hij : i + j = u + u') :
    TauCeti.minkowskiSum h g (u + u') = h i + g j ↔ i = u ∧ j = u' := by
  obtain ⟨c, hc, hface⟩ := hf.exists_intercept
  obtain ⟨d, hd, gface⟩ := hg.exists_intercept
  have hu : u ∈ supportingFace h σ c := hface.symm.subset ⟨hf.left_le_right, le_rfl⟩
  have hu' : u' ∈ supportingFace g σ d := gface.symm.subset ⟨hg.left_le_right, le_rfl⟩
  have hn := (mem_supportingFace_minkowskiSum_iff hc hd).mpr ⟨u, u', rfl, hu, hu'⟩
  rw [← hij] at hn ⊢
  rw [minkowskiSum_add_eq_add_iff_of_mem_supportingFace hc hd hn]
  simp only [hface, gface, Set.mem_Icc]
  have := hf.left_le_right
  have := hg.left_le_right
  omega

end IsFiniteFace

end TauCeti

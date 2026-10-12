/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic

import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# Real radii of values at points of the closed polydisc

A point of a closed polydisc need not have a real-valued valuation. Nevertheless, the value of
each element with value in `(0, 1]` determines a cut among the norms of constants.
This cut has a positive real boundary at most one. The value compares with constants either
at that boundary, just above it, or just below it.

`TauCeti.ValuationSpectrum.exists_radius_trichotomy` gives the two comparison rules in each
case. In the strict boundary cases the radius is the norm of a nonzero scalar; in the above case
it is strictly less than one. No rank-one hypothesis is imposed on the point. Neither
completeness nor algebraic closedness of the base field is needed for the comparison rules.
When the norms of nonzero scalars are dense in the positive reals, the two strict boundary
cases describe infinitesimal deviations. Without density the theorem asserts only the stated
comparisons with constants.

Power-bounded elements have value at most one at every point of the polydisc. For the closed
unit disc, apply the theorem to `T - a` at a centre with `‖a‖ ≤ 1`. When the
centre minimises the values of the linear polynomials, these are the radius conditions that
distinguish the Gauss points from the two infinitesimal points in the classification of disc
points. Finding a minimising centre is a separate question.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber Topology

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NonarchimedeanRing K] {k : ℕ}

local notation "𝒯" => weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set K))
  isWeightFamily_one_weight
local notation "C" => weightedC (fun _ : Fin k ↦ ({1} : Set K)) isWeightFamily_one_weight

/-- The infimum of norms of constants above `x(f)` separates the constants strictly away
from the boundary. Continuity ensures that this boundary is positive. -/
private theorem exists_radius_bounds (x : closedPolydisc k K) {f : 𝒯}
    (hle : x.1.valuation f ≤ 1) (hne : x.1.valuation f ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      (∀ c : K, ‖c‖ < r → x.1.valuation (C c) < x.1.valuation f) ∧
      (∀ c : K, r < ‖c‖ → x.1.valuation f < x.1.valuation (C c)) := by
  let S : Set ℝ := {s | ∃ c : K, ‖c‖ = s ∧ x.1.valuation f ≤ x.1.valuation (C c)}
  have hconst (c d : K) : x.1.valuation (C c) ≤ x.1.valuation (C d) ↔ ‖c‖ ≤ ‖d‖ := by
    rw [valuation_le_iff, closedPolydisc_vle_weightedC_iff]
  have hconst_lt (c d : K) : x.1.valuation (C c) < x.1.valuation (C d) ↔ ‖c‖ < ‖d‖ := by
    simp only [lt_iff_le_not_ge, hconst]
  have hS : (1 : ℝ) ∈ S := ⟨1, norm_one, by simpa using hle⟩
  have hneS : S.Nonempty := ⟨1, hS⟩
  have hbdd : BddBelow S := ⟨0, by rintro s ⟨c, rfl, _⟩; exact norm_nonneg c⟩
  -- Powers of a small nonzero constant eventually lie strictly below `x(f)`.
  obtain ⟨d, hd₀, hd₁⟩ := NormedField.exists_norm_lt K one_pos
  have hdNil : IsTopologicallyNilpotent d := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hd₁
  have hnil : IsTopologicallyNilpotent (C d) :=
    hdNil.map (continuous_weightedC isWeightFamily_one_weight)
  have hcont : x.1.valuation.IsContinuous :=
    (isContinuous_def x.1).mp (((mem_closedPolydisc_iff k K x.1).mp x.2).1)
  obtain ⟨n, hn⟩ := Valuation.exists_pow_lt_of_isTopologicallyNilpotent
    ((Valuation.isContinuous_def.mp hcont f).mem_nhds
      (by rw [Set.mem_ofPred_eq, map_zero]; exact zero_lt_iff.mpr hne)) hnil
  have he : x.1.valuation (C (d ^ n)) < x.1.valuation f := by
    simpa using hn
  have hpos : 0 < sInf S := (pow_pos hd₀ n).trans_le (by
    rw [← norm_pow]
    refine le_csInf hneS ?_
    rintro s ⟨c, rfl, hc⟩
    exact ((hconst_lt _ _).mp (he.trans_le hc)).le)
  refine ⟨sInf S, hpos, csInf_le hbdd hS, ?_, ?_⟩
  · intro c hc
    exact lt_of_not_ge fun h ↦ hc.not_ge (csInf_le hbdd ⟨c, rfl, h⟩)
  · intro c hc
    obtain ⟨s, ⟨d, rfl, hd⟩, hdc⟩ := exists_lt_of_csInf_lt hneS hc
    exact hd.trans_lt ((hconst_lt d c).mpr hdc)

/-- **Radius trichotomy at a point of the closed polydisc.** A value in `(0, 1]` compares
with constants either at a real radius, strictly above its boundary constants, or strictly
below them. The strict alternatives have radius in the value group
of the base field, and the above alternative cannot occur at radius one.

For the classification of closed-disc points over an algebraically closed complete field,
take `f = T - a` at a minimising centre. The first alternative gives the radius comparisons
for `η_{a,r}`, the second for `η_{a,r⁺}`, and
the third for `η_{a,r⁻}`. -/
theorem exists_radius_trichotomy (x : closedPolydisc k K) {f : 𝒯}
    (hle : x.1.valuation f ≤ 1) (hne : x.1.valuation f ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ((∀ c : K, x.1.toValuativeRel.vle f (C c) ↔ r ≤ ‖c‖) ∧
        (∀ c : K, x.1.toValuativeRel.vle (C c) f ↔ ‖c‖ ≤ r) ∨
      (r < 1 ∧ (∃ c : K, ‖c‖ = r) ∧
        (∀ c : K, x.1.toValuativeRel.vle f (C c) ↔ r < ‖c‖) ∧
        (∀ c : K, x.1.toValuativeRel.vle (C c) f ↔ ‖c‖ ≤ r)) ∨
      ((∃ c : K, ‖c‖ = r) ∧
        (∀ c : K, x.1.toValuativeRel.vle f (C c) ↔ r ≤ ‖c‖) ∧
        (∀ c : K, x.1.toValuativeRel.vle (C c) f ↔ ‖c‖ < r))) := by
  classical
  obtain ⟨r, hr₀, hr₁, hlo, hhi⟩ := exists_radius_bounds x hle hne
  refine ⟨r, hr₀, hr₁, ?_⟩
  simp only [← valuation_le_iff]
  have hconst (c d : K) (h : ‖c‖ = ‖d‖) : x.1.valuation (C c) = x.1.valuation (C d) := by
    apply le_antisymm <;> rw [valuation_le_iff, closedPolydisc_vle_weightedC_iff]
    · exact h.le
    · exact h.ge
  -- An attained boundary value gives both non-strict comparison rules immediately.
  by_cases heq : ∃ d : K, ‖d‖ = r ∧ x.1.valuation f = x.1.valuation (C d)
  · obtain ⟨d, hd, hdf⟩ := heq
    refine Or.inl ⟨?_, ?_⟩
    · intro c
      rw [hdf, valuation_le_iff, closedPolydisc_vle_weightedC_iff, hd]
    · intro c
      rw [hdf, valuation_le_iff, closedPolydisc_vle_weightedC_iff, hd]
  -- Constants of the same norm have the same value, so one strict comparison settles
  -- every boundary constant. The bound `x(f) ≤ 1` excludes the above case at radius one.
  by_cases habove : ∃ d : K, ‖d‖ = r ∧ x.1.valuation (C d) < x.1.valuation f
  · obtain ⟨d, hd, hdf⟩ := habove
    have hboundary (c : K) (hc : ‖c‖ = r) : x.1.valuation (C c) < x.1.valuation f := by
      rw [hconst c d (hc.trans hd.symm)]
      exact hdf
    have hlt_one : r < 1 := by
      refine lt_of_le_of_ne hr₁ ?_
      intro h
      have := hboundary 1 (by simpa using h.symm)
      have hgt : 1 < x.1.valuation f := by simpa using this
      exact hgt.not_ge hle
    refine Or.inr (Or.inl ⟨hlt_one, ⟨d, hd⟩, ?_, ?_⟩)
    all_goals
      intro c
      have hl := hlo c
      have hh := hhi c
      have hb := hboundary c
      grind only
  -- If a boundary constant exists, the remaining possibility is strictly below it.
  -- Otherwise both non-strict rules follow from the strict separation away from `r`.
  by_cases hboundary_exists : ∃ d : K, ‖d‖ = r
  · obtain ⟨d, hd⟩ := hboundary_exists
    have hboundary (c : K) (hc : ‖c‖ = r) : x.1.valuation f < x.1.valuation (C c) := by
      refine lt_of_le_of_ne (le_of_not_gt fun h ↦ habove ⟨c, hc, h⟩) ?_
      exact fun h ↦ heq ⟨c, hc, h⟩
    refine Or.inr (Or.inr ⟨⟨d, hd⟩, ?_, ?_⟩)
    all_goals
      intro c
      have hl := hlo c
      have hh := hhi c
      have hb := hboundary c
      grind only
  · refine Or.inl ⟨?_, ?_⟩
    all_goals
      intro c
      have hl := hlo c
      have hh := hhi c
      have hn : ‖c‖ ≠ r := fun h ↦ hboundary_exists ⟨c, h⟩
      grind only

end TauCeti.ValuationSpectrum

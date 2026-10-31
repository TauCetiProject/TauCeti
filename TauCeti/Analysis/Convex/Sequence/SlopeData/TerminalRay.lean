/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.SlopeData.Compressed
public import Mathlib.Order.Filter.EventuallyConst

/-!
# Normalized slope data with a terminal ray

`TerminalRaySlopeData` represents a finite compressed prefix followed by an infinite
straight ray. Every prefix segment has positive finite length, and its slope is strictly
less than the separately stored ray slope. Thus a final prefix segment collinear with the
ray is absorbed into the ray. An empty prefix is allowed and represents a ray from the
anchor, not an empty polygon or a singleton.

Expansion gives `InfiniteSlopeData`. Conversely every eventually constant nondecreasing
unit-slope sequence has a unique normalized presentation of this form. Both round trips
hold. For real slopes the represented heights are convex, and equality of heights
determines the presentation. These constructions concern geometry only: no condition is
imposed on how often a coefficient sequence contacts the ray.

The prefix compression uses the existing finite compressed slope data and Mathlib's
multiset/finitely-supported-function dictionary.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter IV §3.
-/

public section

namespace TauCeti

/-- A normalized finite compressed prefix followed by a terminal ray. Every prefix
slope is strictly below the ray slope, so no redundant final segment is stored. -/
@[ext]
structure TerminalRaySlopeData (Γ : Type*) [LinearOrder Γ] where
  /-- The finite compressed prefix, including the anchor. -/
  «prefix» : FiniteCompressedSlopeData Γ
  /-- The finite slope of the infinite terminal ray. -/
  raySlope : Γ
  /-- Normalization absorbs all segments collinear with the ray into the ray. -/
  lt_raySlope : ∀ m ∈ «prefix».lengths.support, m < raySlope

namespace TerminalRaySlopeData

variable {Γ : Type*} [LinearOrder Γ] (d : TerminalRaySlopeData Γ)

/-- Every unit edge of the prefix has slope strictly less than the ray. -/
theorem prefix_slope_lt (i : Fin d.prefix.expand.length) :
    d.prefix.expand.slope i < d.raySlope := by
  apply d.lt_raySlope
  rw [← Finsupp.mem_toMultiset, ← d.prefix.slopeMultiset_expand]
  exact FiniteSlopeData.mem_slopeMultiset.mpr ⟨i, rfl⟩

/-- Expand the finite prefix and continue with the constant ray slope forever. -/
noncomputable def expand : InfiniteSlopeData Γ where
  start := d.prefix.start
  initialHeight := d.prefix.initialHeight
  slope i := if hi : i < d.prefix.expand.length then d.prefix.expand.slope ⟨i, hi⟩
    else d.raySlope
  monotone i j hij := by
    dsimp only
    split_ifs with hi hj
    · exact d.prefix.expand.monotone hij
    · exact (d.prefix_slope_lt ⟨i, hi⟩).le
    · omega
    · exact le_rfl

@[simp]
theorem expand_start : d.expand.start = d.prefix.start := (rfl)

@[simp]
theorem expand_initialHeight : d.expand.initialHeight = d.prefix.initialHeight := (rfl)

/-- Before the join, expansion gives the prefix unit slopes. -/
@[simp]
theorem expand_slope_of_lt {i : ℕ} (hi : i < d.prefix.expand.length) :
    d.expand.slope i = d.prefix.expand.slope ⟨i, hi⟩ := by
  simp [expand, hi]

/-- At and after the join, expansion gives the ray slope. -/
@[simp]
theorem expand_slope_of_le {i : ℕ} (hi : d.prefix.expand.length ≤ i) :
    d.expand.slope i = d.raySlope := by
  simp [expand, not_lt.mpr hi]

/-- The prefix consists exactly of the unit slopes strictly smaller than the ray slope. -/
theorem expand_slope_lt_raySlope_iff (i : ℕ) :
    d.expand.slope i < d.raySlope ↔ i < d.prefix.expand.length := by
  by_cases hi : i < d.prefix.expand.length
  · simp only [d.expand_slope_of_lt hi, hi, iff_true]
    exact d.prefix_slope_lt ⟨i, hi⟩
  · simp [d.expand_slope_of_le (le_of_not_gt hi), hi]

/-- The expanded unit-slope sequence is eventually constant. -/
theorem eventuallyConst_slope_expand : Filter.EventuallyConst d.expand.slope Filter.atTop :=
  Filter.eventuallyConst_atTop.mpr ⟨d.prefix.expand.length, fun i hi => by
    rw [d.expand_slope_of_le hi, d.expand_slope_of_le le_rfl]⟩

/-- Normalized terminal-ray data is determined by its expanded unit slopes and anchor. -/
theorem expand_injective : Function.Injective (expand : TerminalRaySlopeData Γ → _) := by
  intro d e h
  have hr : d.raySlope = e.raySlope := by
    have := congrArg (fun s => s.slope (max d.prefix.expand.length e.prefix.expand.length)) h
    simpa only [d.expand_slope_of_le (le_max_left _ _),
      e.expand_slope_of_le (le_max_right _ _)] using this
  have hdom (i : ℕ) : i < d.prefix.expand.length ↔ i < e.prefix.expand.length := by
    rw [← d.expand_slope_lt_raySlope_iff, ← e.expand_slope_lt_raySlope_iff, h, hr]
  have hl : d.prefix.expand.length = e.prefix.expand.length := by
    have := hdom d.prefix.expand.length
    have := hdom e.prefix.expand.length
    omega
  have hp : d.prefix.expand = e.prefix.expand := by
    apply FiniteSlopeData.eq_of_slopeMultiset_eq
    · simpa only [FiniteCompressedSlopeData.expand_start, expand_start] using
        congrArg InfiniteSlopeData.start h
    · simpa only [FiniteCompressedSlopeData.expand_initialHeight, expand_initialHeight] using
        congrArg InfiniteSlopeData.initialHeight h
    · simp only [FiniteSlopeData.slopeMultiset_def]
      congr 1
      rw [List.ofFn_congr hl]
      congr 1
      funext i
      have hi : (i : ℕ) < d.prefix.expand.length := by omega
      exact (d.expand_slope_of_lt hi).symm.trans
        ((congrArg (fun s => s.slope i) h).trans (e.expand_slope_of_lt i.isLt))
  have hp' := congrArg FiniteSlopeData.compress hp
  simp only [FiniteCompressedSlopeData.compress_expand] at hp'
  exact TerminalRaySlopeData.ext hp' hr

section AddCommMonoid

variable [AddCommMonoid Γ]

/-- Heights of the finite prefix followed by its terminal ray, infinite before the anchor. -/
noncomputable def heights (d : TerminalRaySlopeData Γ) : ℕ → WithTop Γ := d.expand.heights

/-- Heights are reconstructed from the expanded infinite unit-slope sequence. -/
theorem heights_def : d.heights = d.expand.heights := (rfl)

/-- The finite domain is the half-line beginning at the prefix anchor. -/
theorem heights_ne_top_iff {n : ℕ} : d.heights n ≠ ⊤ ↔ d.prefix.start ≤ n := by
  rw [heights_def, InfiniteSlopeData.heights_ne_top_iff, expand_start]

/-- Heights are infinite exactly before the anchor. -/
@[simp]
theorem heights_eq_top_iff {n : ℕ} : d.heights n = ⊤ ↔ n < d.prefix.start := by
  rw [heights_def, InfiniteSlopeData.heights_eq_top_iff, expand_start]

/-- The anchor height is the initial height of the prefix, also when the prefix is empty. -/
@[simp]
theorem heights_start : d.heights d.prefix.start = (d.prefix.initialHeight : WithTop Γ) := by
  rw [heights_def, ← expand_start, InfiniteSlopeData.heights_start, expand_initialHeight]

private theorem sum_range_expand_slope {k : ℕ} (hk : k ≤ d.prefix.expand.length) :
    ∑ i ∈ Finset.range k, d.expand.slope i = prefixSum k d.prefix.expand.slope := by
  have hs := prefixSum_eq_sum_range (n := d.prefix.expand.length) k d.expand.slope
  have he : (fun i : Fin d.prefix.expand.length => d.expand.slope i) =
      d.prefix.expand.slope := funext fun i => d.expand_slope_of_lt i.isLt
  rw [he, min_eq_left hk] at hs
  exact hs.symm

/-- On the prefix interval, the heights agree with the finite compressed prefix. -/
theorem heights_eq_prefix {k : ℕ} (hk : k ≤ d.prefix.expand.length) :
    d.heights (d.prefix.start + k) = d.prefix.heights (d.prefix.start + k) := by
  rw [heights_def, ← expand_start, InfiniteSlopeData.heights_start_add,
    FiniteCompressedSlopeData.heights_def, expand_start,
    ← FiniteCompressedSlopeData.expand_start, FiniteSlopeData.heights_start_add _ hk,
    FiniteCompressedSlopeData.expand_initialHeight, expand_initialHeight,
    d.sum_range_expand_slope hk]

/-- Beyond the join, each further step adds the ray slope to the endpoint height
of the finite prefix. The offset `k` is relative to the join, not the anchor. -/
theorem heights_ray (k : ℕ) :
    d.heights (d.prefix.start + d.prefix.expand.length + k) =
      d.prefix.heights (d.prefix.start + d.prefix.expand.length) +
        ((k • d.raySlope : Γ) : WithTop Γ) := by
  rw [heights_def, Nat.add_assoc, ← expand_start, InfiniteSlopeData.heights_start_add,
    Finset.sum_range_add, expand_start, FiniteCompressedSlopeData.heights_def,
    ← FiniteCompressedSlopeData.expand_start, FiniteSlopeData.heights_start_add _ le_rfl,
    FiniteCompressedSlopeData.expand_initialHeight, expand_initialHeight,
    d.sum_range_expand_slope le_rfl, prefixSum_of_le le_rfl]
  have ht : (∑ i ∈ Finset.range k, d.expand.slope (d.prefix.expand.length + i)) =
      k • d.raySlope := by
    simp only [d.expand_slope_of_le (Nat.le_add_right _ _), Finset.sum_const,
      Finset.card_range]
  simp only [ht, ← WithTop.coe_add, add_assoc]

end AddCommMonoid

/-- Heights determine normalized terminal-ray data over a cancellative value monoid. -/
theorem heights_injective [AddCancelCommMonoid Γ] :
    Function.Injective (heights : TerminalRaySlopeData Γ → ℕ → WithTop Γ) := by
  intro d e h
  exact expand_injective (InfiniteSlopeData.heights_injective h)

/-- Real terminal-ray slope data represents a convex height sequence. -/
theorem isConvexSeq_heights (d : TerminalRaySlopeData ℝ) : IsConvexSeq d.heights :=
  d.expand.isConvexSeq_heights

/-- The genuine unit slopes, indexed relative to the anchor, are the expanded slopes. -/
@[simp]
theorem unitSlope_heights (d : TerminalRaySlopeData ℝ) (i : ℕ) :
    unitSlope d.heights (d.prefix.start + i) = d.expand.slope i := by
  rw [heights_def, ← expand_start, InfiniteSlopeData.unitSlope_heights]

end TerminalRaySlopeData

namespace InfiniteSlopeData

variable {Γ : Type*} [LinearOrder Γ] (d : InfiniteSlopeData Γ)

/-- An infinite unit-slope presentation has normalized finite-prefix-and-ray data
exactly when its slope sequence is eventually constant. -/
theorem exists_terminalRay_expand_eq_iff :
    (∃ r : TerminalRaySlopeData Γ, r.expand = d) ↔
      Filter.EventuallyConst d.slope Filter.atTop := by
  constructor
  · rintro ⟨r, rfl⟩
    exact r.eventuallyConst_slope_expand
  · intro hd
    let : DecidablePred (fun n => ∀ j, n ≤ j → d.slope j = d.slope n) :=
      Classical.decPred _
    have hex := Filter.eventuallyConst_atTop.mp hd
    let n := Nat.find hex
    have hn : ∀ j, n ≤ j → d.slope j = d.slope n := Nat.find_spec hex
    have hlt (i : Fin n) : d.slope i < d.slope n := by
      apply lt_of_le_of_ne (d.monotone i.isLt.le)
      intro heq
      have hi : ∀ j, (i : ℕ) ≤ j → d.slope j = d.slope i := by
        intro j hij
        by_cases hj : j ≤ n
        · exact le_antisymm ((d.monotone hj).trans_eq heq.symm) (d.monotone hij)
        · exact (hn j (by omega)).trans heq.symm
      have := Nat.find_min' hex hi
      omega
    let f : FiniteSlopeData Γ :=
      ⟨d.start, d.initialHeight, n, fun i => d.slope i, fun _ _ h => d.monotone h⟩
    let r : TerminalRaySlopeData Γ :=
      { «prefix» := f.compress
        raySlope := d.slope n
        lt_raySlope := by
          intro m hm
          have hm' : 0 < f.slopeMultiset.count m := by
            simpa only [FiniteSlopeData.compress_lengths] using
              Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hm)
          obtain ⟨i, rfl⟩ := FiniteSlopeData.mem_slopeMultiset.mp (Multiset.count_pos.mp hm')
          exact hlt i }
    refine ⟨r, InfiniteSlopeData.ext (by simp [r, f]) (by simp [r, f]) ?_⟩
    funext i
    have hlen : r.prefix.expand.length = n := by simp [r, f]
    by_cases hi : i < n
    · rw [r.expand_slope_of_lt (hlen ▸ hi)]
      have hp : r.prefix.expand = f := FiniteSlopeData.expand_compress f
      have hs : ∀ j : Fin r.prefix.expand.length, r.prefix.expand.slope j = d.slope j := by
        rw [hp]
        exact fun _ => rfl
      exact hs _
    · rw [r.expand_slope_of_le (by omega)]
      exact (hn i (by omega)).symm

/-- Normalize an eventually constant infinite slope presentation by compressing the finite
prefix strictly below its final slope and storing that slope as a separate ray. -/
noncomputable def toTerminalRay (hd : Filter.EventuallyConst d.slope Filter.atTop) :
    TerminalRaySlopeData Γ := (d.exists_terminalRay_expand_eq_iff.mpr hd).choose

/-- Expansion after normalization recovers the infinite unit-slope presentation. -/
@[simp]
theorem expand_toTerminalRay (hd : Filter.EventuallyConst d.slope Filter.atTop) :
    (d.toTerminalRay hd).expand = d :=
  (d.exists_terminalRay_expand_eq_iff.mpr hd).choose_spec

/-- Normalization preserves the represented heights. -/
@[simp]
theorem heights_toTerminalRay [AddCommMonoid Γ]
    (hd : Filter.EventuallyConst d.slope Filter.atTop) :
    (d.toTerminalRay hd).heights = d.heights := by
  rw [TerminalRaySlopeData.heights_def, expand_toTerminalRay]

end InfiniteSlopeData

namespace TerminalRaySlopeData

variable {Γ : Type*} [LinearOrder Γ]

/-- Normalization after expansion recovers the original normalized terminal-ray data. -/
@[simp]
theorem toTerminalRay_expand (d : TerminalRaySlopeData Γ) :
    d.expand.toTerminalRay d.eventuallyConst_slope_expand = d :=
  expand_injective (d.expand.expand_toTerminalRay _)

/-- Normalized terminal-ray data is equivalent to eventually constant infinite slope data. -/
noncomputable def equivEventuallyConst : TerminalRaySlopeData Γ ≃
    {d : InfiniteSlopeData Γ // Filter.EventuallyConst d.slope Filter.atTop} where
  toFun d := ⟨d.expand, d.eventuallyConst_slope_expand⟩
  invFun d := d.val.toTerminalRay d.property
  left_inv := toTerminalRay_expand
  right_inv d := Subtype.ext (d.val.expand_toTerminalRay d.property)

@[simp]
theorem equivEventuallyConst_apply (d : TerminalRaySlopeData Γ) :
    equivEventuallyConst d = ⟨d.expand, d.eventuallyConst_slope_expand⟩ := (rfl)

@[simp]
theorem equivEventuallyConst_symm_apply
    (d : {d : InfiniteSlopeData Γ // Filter.EventuallyConst d.slope Filter.atTop}) :
    equivEventuallyConst.symm d = d.val.toTerminalRay d.property := (rfl)

end TerminalRaySlopeData

end TauCeti

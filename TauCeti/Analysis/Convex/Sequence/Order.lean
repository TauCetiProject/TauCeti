/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.SlopeData

/-!
# The order on height sequences and partial sums of slopes

Height sequences `ℕ → WithTop Γ` are compared by the pointwise order, with the value `⊤`
outside their finite domains. So `h ≤ g` forces the finite domain of `g` into that of `h`;
equality of domains or of endpoints is an additional hypothesis whenever it is needed.

For two slope presentations with the same anchor and the same domain, the represented heights
compare exactly when every partial sum of unit slopes does. This is weaker than comparing the
slopes one by one: on `[0, 2]` the slopes `(0, 2)` lie below the slopes `(1, 1)`, although the
second slope is larger. For an arbitrary height sequence `a`, the heights of slope data lie
below `a` exactly when `a` is infinite outside the domain of the slope data and bounded below by
the cumulative slope sums on it. The corresponding interfaces for lower-convex-envelope
comparisons are `le_lowerConvexEnvelope_iff` and `isConvexSeq_heights`.

## Main results

* `setOf_ne_top_subset_of_le`: the reversal of finite domains forced by the order.
* `add_coe_le_add_coe_iff`, `add_affine_le_add_affine_iff`: common finite shifts, in particular
  height translations and shears, preserve and reflect the order.
* `le_iff_forall_sum_unitSlope_le`: two height sequences with the same anchor and the same
  finite domain compare exactly when their partial sums of unit slopes do.
* `FiniteSlopeData.heights_le_heights_iff`, `InfiniteSlopeData.heights_le_heights_iff`: the
  partial-sum criterion for slope presentations with the same anchor and domain.
* `FiniteSlopeData.heights_le_iff`, `InfiniteSlopeData.heights_le_iff`: the heights of slope
  data lie below a height sequence exactly when the cumulative slope sums bound it.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter IV §3.
-/

public section

open Finset

namespace TauCeti

/-! ### Height sequences -/

/-- With the value `⊤` outside finite domains, a smaller height sequence has a larger finite
domain. -/
theorem setOf_ne_top_subset_of_le {α : Type*} [LE α] {h g : ℕ → WithTop α}
    (hhg : h ≤ g) : {n | g n ≠ ⊤} ⊆ {n | h n ≠ ⊤} :=
  fun n (hn : g n ≠ ⊤) (hh : h n = ⊤) => hn (WithTop.top_le_iff.mp (hh ▸ hhg n))

/-- Adding a common finite-valued function to two height sequences does not change how they
compare. -/
theorem add_coe_le_add_coe_iff {Γ : Type*} [AddCommMonoid Γ] [Preorder Γ]
    [IsOrderedCancelAddMonoid Γ] {h g : ℕ → WithTop Γ} (f : ℕ → Γ) :
    ((fun n => h n + (f n : WithTop Γ)) ≤ fun n => g n + (f n : WithTop Γ)) ↔ h ≤ g :=
  by simp only [Pi.le_def, WithTop.add_le_add_iff_right WithTop.coe_ne_top]

/-- Adding a common real affine function to two height sequences does not change how they
compare. With `m = 0` this is a common height translation; with `c = 0` a common shear. -/
theorem add_affine_le_add_affine_iff {h g : ℕ → WithTop ℝ} (c m : ℝ) :
    ((fun n => h n + ((c + m * n : ℝ) : WithTop ℝ)) ≤
      fun n => g n + ((c + m * n : ℝ) : WithTop ℝ)) ↔ h ≤ g :=
  add_coe_le_add_coe_iff fun n => c + m * n

/-- Two height sequences with the same finite domain and the same height at a lower bound `l`
of that domain compare exactly when, at every finite index `l + j`, the sum of the first `j`
unit slopes from `l` compares. No convexity is needed. For convex sequences these sums are
partial sums of the slopes of the polygon, and the criterion is not termwise comparison of
slopes. -/
theorem le_iff_forall_sum_unitSlope_le {h g : ℕ → WithTop ℝ} {l : ℕ}
    (hdom : ∀ n, h n ≠ ⊤ ↔ g n ≠ ⊤) (hl : h l = g l) (hlow : ∀ n, h n ≠ ⊤ → l ≤ n) :
    h ≤ g ↔ ∀ j, h (l + j) ≠ ⊤ →
      ∑ i ∈ range j, unitSlope h (l + i) ≤ ∑ i ∈ range j, unitSlope g (l + i) := by
  have key (j : ℕ) (hj : h (l + j) ≠ ⊤) : h (l + j) ≤ g (l + j) ↔
      ∑ i ∈ range j, unitSlope h (l + i) ≤ ∑ i ∈ range j, unitSlope g (l + i) := by
    rw [eq_coe_add_sum_unitSlope hj (Nat.le_add_right l j),
      eq_coe_add_sum_unitSlope ((hdom _).1 hj) (Nat.le_add_right l j)]
    simp [hl, sum_Ico_eq_sum_range]
  refine ⟨fun hhg j hj => (key j hj).1 (hhg _), fun H n => ?_⟩
  by_cases hn : h n = ⊤
  · rw [hn, not_ne_iff.mp ((hdom n).not.mp (not_not.mpr hn))]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (hlow n hn)
    exact (key j hn).2 (H j hn)

/-! ### Finite slope data -/

namespace FiniteSlopeData

variable {Γ : Type*} [AddCommMonoid Γ]

/-- The heights of finite slope data lie below a height sequence `a` exactly when `a` is
infinite outside `[start, start + length]` and, on it, bounded below by the cumulative slope
sums. -/
theorem heights_le_iff [Preorder Γ] {d : FiniteSlopeData Γ} {a : ℕ → WithTop Γ} :
    d.heights ≤ a ↔ (∀ n, n < d.start ∨ d.start + d.length < n → a n = ⊤) ∧
      ∀ k ≤ d.length,
        ((d.initialHeight + prefixSum k d.slope : Γ) : WithTop Γ) ≤ a (d.start + k) := by
  refine ⟨fun hda => ⟨fun n hn => WithTop.top_le_iff.mp ((d.heights_eq_top_iff.mpr hn).symm.trans_le
    (hda n)), fun k hk => (d.heights_start_add hk).symm.trans_le (hda _)⟩,
    fun ⟨hout, hin⟩ n => ?_⟩
  by_cases hn : d.start ≤ n ∧ n ≤ d.start + d.length
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn.1
    rw [d.heights_start_add (by omega)]
    exact hin k (by omega)
  · rw [hout n (by omega)]
    exact le_top

variable [Preorder Γ] [IsOrderedCancelAddMonoid Γ]

/-- **Partial-sum criterion.** For finite slope data with the same anchor and length,
`d.heights ≤ e.heights` exactly when each partial sum of `d`'s slopes is at most the corresponding
partial sum of `e`'s. The slopes themselves need not compare termwise. -/
theorem heights_le_heights_iff {d e : FiniteSlopeData Γ} (hstart : d.start = e.start)
    (hheight : d.initialHeight = e.initialHeight) (hlength : d.length = e.length) :
    d.heights ≤ e.heights ↔ ∀ k, prefixSum k d.slope ≤ prefixSum k e.slope := by
  rw [heights_le_iff]
  refine ⟨fun ⟨_, hin⟩ k => ?_, fun H => ⟨fun n hn => ?_, fun k hk => ?_⟩⟩
  · have hin' := hin (min k d.length) (min_le_right _ _)
    rw [hstart, e.heights_start_add (le_trans (min_le_right k d.length) hlength.le)] at hin'
    have hde : prefixSum (min k d.length) d.slope ≤ prefixSum (min k d.length) e.slope := by
      simpa only [WithTop.coe_le_coe, hheight, add_le_add_iff_left] using hin'
    calc
      prefixSum k d.slope = prefixSum (min k d.length) d.slope := (prefixSum_min _ _).symm
      _ ≤ prefixSum (min k d.length) e.slope := hde
      _ = prefixSum k e.slope := by rw [congrArg (min k) hlength, prefixSum_min]
  · rw [e.heights_eq_top_iff]
    omega
  · rw [hstart, e.heights_start_add (hlength ▸ hk), WithTop.coe_le_coe, hheight]
    exact (add_le_add_iff_left _).2 (H k)

end FiniteSlopeData

/-! ### Infinite slope data -/

namespace InfiniteSlopeData

variable {Γ : Type*} [AddCommMonoid Γ]

/-- The heights of infinite slope data lie below a height sequence `a` exactly when `a` is
infinite before `start` and, from `start` on, bounded below by the cumulative slope sums. -/
theorem heights_le_iff [Preorder Γ] {d : InfiniteSlopeData Γ} {a : ℕ → WithTop Γ} :
    d.heights ≤ a ↔ (∀ n < d.start, a n = ⊤) ∧
      ∀ k, ((d.initialHeight + ∑ i ∈ range k, d.slope i : Γ) : WithTop Γ) ≤ a (d.start + k) := by
  refine ⟨fun hda => ⟨fun n hn => WithTop.top_le_iff.mp ((d.heights_eq_top_iff.mpr hn).symm.trans_le
    (hda n)), fun k => (d.heights_start_add k).symm.trans_le (hda _)⟩,
    fun ⟨hout, hin⟩ n => ?_⟩
  by_cases hn : d.start ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [d.heights_start_add]
    exact hin k
  · rw [hout n (by omega)]
    exact le_top

variable [Preorder Γ] [IsOrderedCancelAddMonoid Γ]

/-- **Partial-sum criterion.** For infinite slope data with the same anchor,
`d.heights ≤ e.heights` exactly when each partial sum of `d`'s slopes is at most the corresponding
partial sum of `e`'s. The slopes themselves need not compare termwise. -/
theorem heights_le_heights_iff {d e : InfiniteSlopeData Γ} (hstart : d.start = e.start)
    (hheight : d.initialHeight = e.initialHeight) :
    d.heights ≤ e.heights ↔ ∀ k, ∑ i ∈ range k, d.slope i ≤ ∑ i ∈ range k, e.slope i := by
  rw [heights_le_iff]
  refine ⟨fun ⟨_, hin⟩ k => ?_, fun H => ⟨fun n hn => ?_, fun k => ?_⟩⟩
  · have := hin k
    rwa [hstart, e.heights_start_add, WithTop.coe_le_coe, hheight, add_le_add_iff_left] at this
  · rw [e.heights_eq_top_iff]
    omega
  · rw [hstart, e.heights_start_add, WithTop.coe_le_coe, hheight]
    exact (add_le_add_iff_left _).2 (H k)

end InfiniteSlopeData

end TauCeti

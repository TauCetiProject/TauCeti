/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Vertex

/-!
# First breaks of convex height sequences

Let `h` be a height sequence whose first finite index is `l`. It has a *first break* at `j > l`
with slope `σ` (`TauCeti.IsFirstBreak h σ l j`) when its first segment runs from `l` to `j`: every
unit edge from `l` to `j` is finite of slope `σ`, and at `j` either the finite domain ends or the
next unit slope is strictly larger than `σ`. A segment ending at the last finite index counts, so
the last segment of a polygon with bounded finite domain, such as that of a polynomial, may be its
first segment.

For a convex sequence a first break at `j` is exactly a finite face of slope `σ` of positive
width whose left endpoint is the first finite index (`TauCeti.IsConvexSeq.isFirstBreak_iff`).
For the lower convex envelope of point heights `a`, the finite-face criterion
`TauCeti.IsLowerConvexEnvelope.isFiniteFace_iff` turns this into a criterion on the points alone
(`TauCeti.IsLowerConvexEnvelope.isFirstBreak_iff`): the points are infinite before `l`, some line of
slope `σ` supports the points and passes through the points at `l` and `j`, and the line through
the point at `j` with some strictly larger slope also supports the points.

The last condition cannot be weakened to the points beyond `j` lying strictly above the line of
slope `σ`. For an infinite sequence these points may approach the line, and then the envelope
continues along it past `j`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
-/

public section

namespace TauCeti

/-- A height sequence `h` has a **first break** at `j` with slope `σ`, starting from its first
finite index `l`, when `h` is infinite before `l`, finite from `l` to `j > l`, every unit edge from
`l` to `j` has slope `σ`, and either `h` is infinite at `j + 1` or the unit slope at `j` is
strictly larger than `σ`. -/
structure IsFirstBreak (h : ℕ → WithTop ℝ) (σ : ℝ) (l j : ℕ) : Prop where
  /-- The first segment has positive length. -/
  lt : l < j
  /-- Every height before `l` is infinite. -/
  eq_top_of_lt : ∀ n < l, h n = ⊤
  /-- Every height from `l` to `j` is finite. -/
  ne_top : ∀ n, l ≤ n → n ≤ j → h n ≠ ⊤
  /-- Every unit edge from `l` to `j` has slope `σ`. -/
  unitSlope_eq : ∀ i, l ≤ i → i < j → unitSlope h i = σ
  /-- After `j` the slope increases strictly, unless the finite domain ends at `j`. -/
  lt_unitSlope : h (j + 1) ≠ ⊤ → σ < unitSlope h j

namespace IsFirstBreak

variable {h : ℕ → WithTop ℝ} {σ : ℝ} {l j : ℕ}

/-- The height at the first finite index is finite. -/
theorem left_ne_top (hb : IsFirstBreak h σ l j) : h l ≠ ⊤ :=
  hb.ne_top l le_rfl hb.lt.le

/-- The height at a first break is finite. -/
theorem right_ne_top (hb : IsFirstBreak h σ l j) : h j ≠ ⊤ :=
  hb.ne_top j hb.lt.le le_rfl

/-- Up to a first break, the heights lie on the line of slope `σ` through the first point. -/
theorem eq_coe (hb : IsFirstBreak h σ l j) {n : ℕ} (hln : l ≤ n) (hnj : n ≤ j) :
    h n = (((h l).untop₀ - σ * l + σ * n : ℝ) : WithTop ℝ) := by
  rw [eq_coe_add_sum_unitSlope (hb.ne_top n hln hnj) hln,
    Finset.sum_congr rfl fun i hi => hb.unitSlope_eq i (Finset.mem_Ico.mp hi).1
      ((Finset.mem_Ico.mp hi).2.trans_le hnj),
    Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hln]
  congr 1
  ring

/-- A first break of a convex sequence is the right endpoint of a finite face of slope `σ`
whose left endpoint is the first finite index. -/
theorem isFiniteFace (hb : IsFirstBreak h σ l j) (hh : IsConvexSeq h) :
    IsFiniteFace h σ l j := by
  have hl := hb.left_ne_top
  have hc : IsSupportingLine h σ ((h l).untop₀ - σ * l) :=
    (hh.isSupportingLine_iff_unitSlope hl σ).mpr
      ⟨fun i hi hi' => absurd (hb.eq_top_of_lt i (by omega)) hi',
        fun _ => (hb.unitSlope_eq l le_rfl hb.lt).ge⟩
  refine isFiniteFace_iff.mpr ⟨hb.lt.le, _, hc, Set.Subset.antisymm (fun n hn => ?_)
    fun n hn => mem_supportingFace.mpr (hb.eq_coe hn.1 hn.2)⟩
  rw [mem_supportingFace] at hn
  have hn' : h n ≠ ⊤ := hn ▸ WithTop.coe_ne_top
  refine ⟨le_of_not_gt fun hnl => hn' (hb.eq_top_of_lt n hnl), le_of_not_gt fun hjn => ?_⟩
  -- Past `j` the sequence follows a strictly steeper edge, so it leaves the line.
  have hj1 : h (j + 1) ≠ ⊤ := hh.ne_top_of_le_of_le hb.right_ne_top hn' (Nat.le_succ j) hjn
  have hs := hb.lt_unitSlope hj1
  have hle := hh.supportingLine_le hb.right_ne_top hj1 n
  rw [hn, hb.eq_coe hb.lt.le le_rfl, WithTop.untop₀_coe, WithTop.coe_le_coe] at hle
  have hjn' : (j : ℝ) < n := Nat.cast_lt.mpr hjn
  nlinarith

end IsFirstBreak

variable {h : ℕ → WithTop ℝ} {σ : ℝ} {l j : ℕ}

/-- A finite face of positive width of a convex sequence, starting at its first finite index, ends
at a first break. -/
theorem IsFiniteFace.isFirstBreak (hf : IsFiniteFace h σ l j) (hh : IsConvexSeq h) (hlj : l < j)
    (hl : ∀ n < l, h n = ⊤) : IsFirstBreak h σ l j :=
  ⟨hlj, hl, fun _ hln hnj => hh.ne_top_of_le_of_le hf.left_ne_top hf.right_ne_top hln hnj,
    fun _ hli hij => hf.unitSlope_eq hli hij,
    fun hj => hf.lt_unitSlope hh (mem_finiteEdges.mpr ⟨hf.right_ne_top, hj⟩) le_rfl⟩

/-- A convex sequence has a first break at `j` with slope `σ` exactly when it has a finite face of
slope `σ` from its first finite index `l` to `j > l`. -/
theorem IsConvexSeq.isFirstBreak_iff (hh : IsConvexSeq h) :
    IsFirstBreak h σ l j ↔ l < j ∧ (∀ n < l, h n = ⊤) ∧ IsFiniteFace h σ l j :=
  ⟨fun hb => ⟨hb.lt, hb.eq_top_of_lt, hb.isFiniteFace hh⟩,
    fun ⟨hlj, hl, hf⟩ => hf.isFirstBreak hh hlj hl⟩

/-- **First-break criterion.** The lower convex envelope of point heights `a` has a first break
at `j` with slope `σ`, starting from the first finite index `l < j`, exactly when the points are
infinite before `l`, some line of slope `σ` supports the points and passes through the points at
`l` and `j`, and the line through the point at `j` with some strictly larger slope also supports
the points.

The steeper line cannot be replaced by asking the points beyond `j` to lie strictly above the line
of slope `σ`: infinitely many points may approach that line, and the envelope then follows it. -/
theorem IsLowerConvexEnvelope.isFirstBreak_iff {a : ℕ → WithTop ℝ}
    (hh : IsLowerConvexEnvelope a h) :
    IsFirstBreak h σ l j ↔ l < j ∧ (∀ n < l, a n = ⊤) ∧ ∃ c : ℝ, IsSupportingLine a σ c ∧
      l ∈ supportingFace a σ c ∧ j ∈ supportingFace a σ c ∧
      ∃ τ > σ, IsSupportingLine a τ (c + (σ - τ) * j) := by
  rw [hh.isConvexSeq.isFirstBreak_iff, hh.isFiniteFace_iff]
  constructor
  · rintro ⟨hlj, hl, -, c, hc, hlc, hjc, -, hτ⟩
    exact ⟨hlj, fun n hn => top_unique ((hl n hn).symm.trans_le (hh.le n)), c, hc, hlc, hjc, hτ⟩
  · rintro ⟨hlj, hl, c, hc, hlc, hjc, hτ⟩
    refine ⟨hlj, fun n hn => ?_, hlj.le, c, hc, hlc, hjc,
      ⟨σ - 1, by linarith, isSupportingLine_iff_forall.mpr fun n => ?_⟩, hτ⟩
    · rw [hh.eq_lowerConvexEnvelope]
      exact lowerConvexEnvelope_eq_top_of_forall_le fun i hi => hl i (by omega)
    · -- Before `l` the points are infinite, and from `l` on the flatter line lies below the
      -- supporting line of slope `σ`.
      rcases lt_or_ge n l with hnl | hln
      · simp [hl n hnl]
      · refine le_trans ?_ (isSupportingLine_iff_forall.mp hc n)
        rw [WithTop.coe_le_coe]
        have : (l : ℝ) ≤ n := Nat.cast_le.mpr hln
        linarith

end TauCeti

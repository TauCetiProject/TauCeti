/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Face
import TauCeti.Analysis.Convex.Sequence.Vertex

/-!
# The first break of a convex height sequence

A height sequence `h : ℕ → WithTop ℝ` has its *first break* at `j`, with first slope `m`, when
its finite domain starts at some `a < j`, every unit edge from `a` to `j` is finite of slope `m`,
and the unit edge leaving `j` is either missing or has slope strictly greater than `m`. Thus the
first segment of the polygon ends at `j`, and the slope genuinely increases there unless `j` is
the last point of a finite domain, as for the endpoint of the Newton polygon of a polynomial.
The first break and its slope are unique.

For a convex sequence, a first break at `j` of slope `m` is the same as a finite face of slope
`m` running from the first finite index `a` to `j`. For the lower convex envelope of an arbitrary
point set `y` whose first finite point is `a`, this gives the coefficient-line criterion
`IsLowerConvexEnvelope.isFirstBreak_iff`: the envelope has its first break at `j` with slope `m`
exactly when `a < j`, some line of slope `m` supports `y` and passes through the points at `a`
and `j`, and some line of strictly larger slope through the point at `j` supports `y` at every
index after `j`. The second line cannot be replaced by pointwise strict inequalities after `j`:
points lying strictly above the line of slope `m` after `j` but approaching it allow the envelope
to continue along a ray of slope `m` beyond `j`.

## Main definitions

* `TauCeti.IsFirstBreak h m j`: the height sequence `h` has its first break at `j`, with first
  slope `m`.

## Main results

* `TauCeti.IsFirstBreak.unique`: the first break and its slope are unique.
* `TauCeti.IsFirstBreak.exists_gt_isSupportingLine`: after a first break of slope `m`, a convex
  sequence has a supporting line of strictly larger slope.
* `TauCeti.IsConvexSeq.isFirstBreak_iff_isFiniteFace`: for a convex sequence, a first break at
  `j` of slope `m` is a finite face of slope `m` from the first finite index to `j`.
* `TauCeti.IsLowerConvexEnvelope.isFirstBreak_iff`: the coefficient-line criterion for a first
  break of a lower convex envelope.
* `TauCeti.IsLowerConvexEnvelope.isFirstBreak_iff_of_finite`: for finitely many finite points,
  the steeper line may be replaced by pointwise strict inequalities after `j`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §§3–4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

namespace TauCeti

/-- The height sequence `h` has its *first break* at `j`, with first slope `m`: its finite domain
starts at some `a < j`, every unit edge from `a` to `j` is finite of slope `m`, and the unit edge
leaving `j`, if finite, has slope strictly greater than `m`. A missing edge after `j` is allowed,
so the last point of a finite domain can be a first break. -/
def IsFirstBreak (h : ℕ → WithTop ℝ) (m : ℝ) (j : ℕ) : Prop :=
  ∃ a < j, (∀ n < a, h n = ⊤) ∧ (∀ i ∈ Set.Ico a j, i ∈ finiteEdges h ∧ unitSlope h i = m) ∧
    (j ∈ finiteEdges h → m < unitSlope h j)

/-- Unfolding of `IsFirstBreak`. -/
theorem isFirstBreak_iff {h : ℕ → WithTop ℝ} {m : ℝ} {j : ℕ} :
    IsFirstBreak h m j ↔ ∃ a < j, (∀ n < a, h n = ⊤) ∧
      (∀ i ∈ Set.Ico a j, i ∈ finiteEdges h ∧ unitSlope h i = m) ∧
      (j ∈ finiteEdges h → m < unitSlope h j) :=
  Iff.rfl

/-- A height sequence has at most one first break, and its first slope is determined. -/
theorem IsFirstBreak.unique {h : ℕ → WithTop ℝ} {m m' : ℝ} {j j' : ℕ}
    (hb : IsFirstBreak h m j) (hb' : IsFirstBreak h m' j') : m = m' ∧ j = j' := by
  obtain ⟨a, haj, hpre, hedge, hnext⟩ := hb
  obtain ⟨a', haj', hpre', hedge', hnext'⟩ := hb'
  -- Both breaks start at the first finite index.
  have ha : a = a' := by
    have hfa := (mem_finiteEdges.mp (hedge a ⟨le_rfl, haj⟩).1).1
    have hfa' := (mem_finiteEdges.mp (hedge' a' ⟨le_rfl, haj'⟩).1).1
    exact le_antisymm (not_lt.mp fun h ↦ hfa' (hpre a' h)) (not_lt.mp fun h ↦ hfa (hpre' a h))
  subst a'
  have hm : m = m' := (hedge a ⟨le_rfl, haj⟩).2.symm.trans (hedge' a ⟨le_rfl, haj'⟩).2
  subst m'
  refine ⟨rfl, ?_⟩
  -- An earlier break would be an edge of the other first segment, of the same slope.
  rcases lt_trichotomy j j' with hjj | rfl | hjj
  · obtain ⟨hj, hjm⟩ := hedge' j ⟨haj.le, hjj⟩
    exact absurd (hnext hj) (by rw [hjm]; exact lt_irrefl m)
  · rfl
  · obtain ⟨hj, hjm⟩ := hedge j' ⟨haj'.le, hjj⟩
    exact absurd (hnext' hj) (by rw [hjm]; exact lt_irrefl m)

/-- For a convex height sequence, a first break at `j` of slope `m` is exactly a finite face of
slope `m` running from the first finite index `a < j` to `j`. -/
theorem IsConvexSeq.isFirstBreak_iff_isFiniteFace {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h)
    {m : ℝ} {j : ℕ} :
    IsFirstBreak h m j ↔ ∃ a < j, (∀ n < a, h n = ⊤) ∧ IsFiniteFace h m a j := by
  constructor
  · rintro ⟨a, haj, hpre, hedge, hnext⟩
    have ha : h a ≠ ⊤ := (mem_finiteEdges.mp (hedge a ⟨le_rfl, haj⟩).1).1
    -- Every point from `a` to `j` lies on the line of slope `m` through `(a, h a)`.
    have hline : ∀ n ∈ Set.Icc a j, h n = (((h a).untop₀ - m * a + m * n : ℝ) : WithTop ℝ) := by
      rintro n ⟨han, hnj⟩
      have hn : h n ≠ ⊤ := by
        rcases han.eq_or_lt with rfl | han
        · exact ha
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt han
        exact (mem_finiteEdges.mp (hedge (a + k) ⟨by omega, by omega⟩).1).2
      rw [eq_coe_add_sum_unitSlope hn han,
        Finset.sum_congr rfl fun i hi ↦ (hedge i (Set.mem_Ico.mpr
          ⟨(Finset.mem_Ico.mp hi).1, (Finset.mem_Ico.mp hi).2.trans_le hnj⟩)).2,
        Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub han]
      ring_nf
    have hsupp : IsSupportingLine h m ((h a).untop₀ - m * a) :=
      (hh.isSupportingLine_iff_unitSlope ha m).mpr
        ⟨fun i hi hfi ↦ absurd (hpre i (by omega)) hfi,
          fun _ ↦ (hedge a ⟨le_rfl, haj⟩).2.ge⟩
    refine ⟨a, haj, hpre, isFiniteFace_iff.mpr
      ⟨haj.le, _, hsupp, Set.Subset.antisymm (fun n hn ↦ ?_)
        fun n hn ↦ mem_supportingFace.mpr (hline n hn)⟩⟩
    rw [mem_supportingFace] at hn
    have hnf : h n ≠ ⊤ := by rw [hn]; exact WithTop.coe_ne_top
    refine ⟨not_lt.mp fun hna ↦ hnf (hpre n hna), not_lt.mp fun hjn ↦ ?_⟩
    -- After `j` the next edge is finite and steeper, so `h n` lies strictly above the line.
    have hj := hline j ⟨haj.le, le_rfl⟩
    have hjf : h j ≠ ⊤ := by rw [hj]; exact WithTop.coe_ne_top
    have hedge_j : j ∈ finiteEdges h :=
      mem_finiteEdges.mpr ⟨hjf, hh.ne_top_of_le_of_le hjf hnf (Nat.le_succ j) hjn⟩
    have hs := hh.mul_slope_le_sub hnf hjf hjn.le le_rfl
    rw [hn, hj, WithTop.untop₀_coe, WithTop.untop₀_coe, Nat.cast_sub hjn.le] at hs
    have hpos : (0 : ℝ) < n - j := sub_pos.mpr (Nat.cast_lt.mpr hjn)
    nlinarith [hnext hedge_j]
  · rintro ⟨a, haj, hpre, hf⟩
    refine ⟨a, haj, hpre, fun i hi ↦ ⟨mem_finiteEdges.mpr
      ⟨hh.ne_top_of_le_of_le hf.left_ne_top hf.right_ne_top hi.1 hi.2.le,
        hh.ne_top_of_le_of_le hf.left_ne_top hf.right_ne_top (hi.1.trans (Nat.le_succ i)) hi.2⟩,
      hf.unitSlope_eq hi.1 hi.2⟩, fun hj ↦ hf.lt_unitSlope hh hj le_rfl⟩

/-- After a first break of slope `m`, a convex height sequence has a supporting line of some
strictly larger slope: the line through the edge leaving the break, or any line when the finite
domain ends at the break. -/
theorem IsFirstBreak.exists_gt_isSupportingLine {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h)
    {m : ℝ} {j : ℕ} (hb : IsFirstBreak h m j) : ∃ τ > m, ∃ d : ℝ, IsSupportingLine h τ d := by
  obtain ⟨a, haj, -, hedge, hnext⟩ := hb
  by_cases hj : j ∈ finiteEdges h
  · refine ⟨unitSlope h j, hnext hj, (h j).untop₀ - unitSlope h j * j,
      isSupportingLine_iff_forall.mpr fun k ↦ ?_⟩
    refine le_trans (le_of_eq (congrArg _ ?_))
      (hh.supportingLine_le (mem_finiteEdges.mp hj).1 (mem_finiteEdges.mp hj).2 k)
    ring
  -- Otherwise the finite domain ends at `j`, so lines of every slope support `h`.
  have hja : h j ≠ ⊤ := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt haj
    exact (mem_finiteEdges.mp (hedge (a + k) ⟨by omega, by omega⟩).1).2
  have hfin : {n | h n ≠ ⊤}.Finite := (Set.finite_Iic j).subset fun n hn ↦
    Set.mem_Iic.mpr <| not_lt.mp fun hjn ↦
      hj (mem_finiteEdges.mpr ⟨hja, hh.ne_top_of_le_of_le hja hn (Nat.le_succ j) hjn⟩)
  obtain ⟨d, hd⟩ := supportingValue_ne_bot_iff.mp (supportingValue_ne_bot_of_finite hfin (m + 1))
  exact ⟨m + 1, by linarith, d, isSupportingLine_iff_forall.mpr hd⟩

namespace IsLowerConvexEnvelope

variable {y h : ℕ → WithTop ℝ}

/-- The lower convex envelope of `y` is infinite before the first finite point of `y`. -/
private theorem eq_top_of_lt (hh : IsLowerConvexEnvelope y h) {a : ℕ}
    (hpre : ∀ n < a, y n = ⊤) {n : ℕ} (hn : n < a) : h n = ⊤ := by
  rw [hh.eq_lowerConvexEnvelope]
  exact lowerConvexEnvelope_eq_top_of_forall_le fun i hi ↦ hpre i (hi.trans_lt hn)

/-- If a line of slope `m` supports `y` and passes through the first point `a` of `y` and the
point at `j > a`, and a line of strictly larger slope through the point at `j` supports `y` from
`j` on, then the envelope has the finite face `[a, j]` of slope `m`. -/
private theorem isFiniteFace_of_isSupportingLine (hh : IsLowerConvexEnvelope y h) {a : ℕ}
    (hpre : ∀ n < a, y n = ⊤) {m c τ : ℝ} {j : ℕ} (haj : a < j) (hc : IsSupportingLine y m c)
    (hca : a ∈ supportingFace y m c) (hcj : j ∈ supportingFace y m c) (hτ : m < τ)
    (hτc : IsSupportingLine (fun n ↦ y (j + n)) τ (c + m * j)) : IsFiniteFace h m a j := by
  have hch : IsSupportingLine h m c := hh.isSupportingLine_iff.mpr hc
  -- The maximum of the two lines is a convex minorant of `y`, hence lies below `h`.
  have hmax : (fun n : ℕ ↦ ((c + m * n : ℝ) : WithTop ℝ)) ⊔
      (fun n : ℕ ↦ ((c + m * j - τ * j + τ * n : ℝ) : WithTop ℝ)) ≤ h := by
    refine hh.greatest ((isConvexSeq_affine _ _).sup (isConvexSeq_affine _ _)) fun n ↦ ?_
    refine sup_le (isSupportingLine_iff_forall.mp hc n) ?_
    rcases le_or_gt j n with hjn | hnj
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hjn
      refine le_trans (le_of_eq (congrArg _ ?_)) (isSupportingLine_iff_forall.mp hτc k)
      push_cast
      ring
    · refine le_trans ?_ (isSupportingLine_iff_forall.mp hc n)
      rw [WithTop.coe_le_coe]
      have : (n : ℝ) < j := Nat.cast_lt.mpr hnj
      nlinarith
  refine isFiniteFace_iff.mpr ⟨haj.le, c, hch, Set.Subset.antisymm (fun n hn ↦ ?_) ?_⟩
  · rw [mem_supportingFace] at hn
    refine ⟨not_lt.mp fun hna ↦ ?_, not_lt.mp fun hjn ↦ ?_⟩
    · rw [hh.eq_top_of_lt hpre hna] at hn
      exact WithTop.top_ne_coe hn
    · have h2 := le_trans le_sup_right (hmax n)
      rw [hn, WithTop.coe_le_coe] at h2
      have : (j : ℝ) < n := Nat.cast_lt.mpr hjn
      nlinarith
  · exact (hh.isConvexSeq.ordConnected_supportingFace hch).out
      (hh.supportingFace_subset hc hca) (hh.supportingFace_subset hc hcj)

/-- **Coefficient-line criterion for a first break.** Let `h` be the lower convex envelope of
`y`, and let `a` be the first index with `y a` finite. Then `h` has its first break at `j` with
slope `m` if and only if `a < j`, some line of slope `m` supports `y` and passes through the
points of `y` at `a` and at `j`, and some line of strictly larger slope `τ` through the point at
`j` lies below `y` at every index from `j` on. The last condition is stated for the shifted
sequence `n ↦ y (j + n)`, whose supporting line of slope `τ` has intercept `c + m * j`. -/
theorem isFirstBreak_iff (hh : IsLowerConvexEnvelope y h) {a : ℕ} (hya : y a ≠ ⊤)
    (hpre : ∀ n < a, y n = ⊤) {m : ℝ} {j : ℕ} :
    IsFirstBreak h m j ↔ a < j ∧ ∃ c : ℝ, IsSupportingLine y m c ∧
      a ∈ supportingFace y m c ∧ j ∈ supportingFace y m c ∧
      ∃ τ > m, IsSupportingLine (fun n ↦ y (j + n)) τ (c + m * j) := by
  have hha : h a = y a := by
    rw [hh.eq_lowerConvexEnvelope]
    exact lowerConvexEnvelope_eq_of_forall_lt hh.isAdmissible hpre
  rw [hh.isConvexSeq.isFirstBreak_iff_isFiniteFace]
  constructor
  · rintro ⟨a', ha'j, hpre', hf⟩
    -- The face starts at the first finite index of `h`, which is that of `y`.
    obtain rfl : a' = a := le_antisymm
      (not_lt.mp fun h' ↦ (hha ▸ hya) (hpre' a h'))
      (not_lt.mp fun h' ↦ hf.left_ne_top (hh.eq_top_of_lt hpre h'))
    obtain ⟨c, hc, hleast, hgreatest⟩ :=
      hh.exists_isSupportingLine_isLeast_isGreatest_of_isFiniteFace hf
    refine ⟨ha'j, c, hc, hleast.1, hgreatest.1, ?_⟩
    have hjc : h j = ((c + m * j : ℝ) : WithTop ℝ) := by
      rw [hh.eq_right_of_isFiniteFace hf]
      exact mem_supportingFace.mp hgreatest.1
    by_cases hj : j ∈ finiteEdges h
    · -- The edge leaving `j` is steeper, and its line supports the envelope.
      refine ⟨unitSlope h j, hf.lt_unitSlope hh.isConvexSeq hj le_rfl,
        isSupportingLine_iff_forall.mpr fun n ↦ ?_⟩
      have hl := hh.isConvexSeq.supportingLine_le (mem_finiteEdges.mp hj).1
        (mem_finiteEdges.mp hj).2 (j + n)
      rw [hjc, WithTop.untop₀_coe] at hl
      refine le_trans (le_of_eq (congrArg _ ?_)) (hl.trans (hh.le _))
      push_cast
      ring
    · -- No point of `y` lies after `j`, so any steeper line works.
      have hj' : h (j + 1) = ⊤ := by
        by_contra hj'
        exact hj (mem_finiteEdges.mpr ⟨hf.right_ne_top, hj'⟩)
      refine ⟨m + 1, by linarith, isSupportingLine_iff_forall.mpr fun n ↦ ?_⟩
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using (mem_supportingFace.mp hgreatest.1).ge
      · have hyn : y (j + n) = ⊤ := by
          by_contra hyn
          exact hh.isConvexSeq.ne_top_of_le_of_le hf.right_ne_top
            (ne_top_of_le_ne_top hyn (hh.le _)) (Nat.le_succ j) (by omega) hj'
        rw [hyn]
        exact le_top
  · rintro ⟨haj, c, hc, hca, hcj, τ, hτ, hτc⟩
    exact ⟨a, haj, fun n hn ↦ hh.eq_top_of_lt hpre hn,
      hh.isFiniteFace_of_isSupportingLine hpre haj hc hca hcj hτ hτc⟩

/-- A line of slope `m` through `(j, c + m * j)` lying strictly below finitely many points after
`j` can be rotated about that point to a line of strictly larger slope that still lies below
them. -/
private theorem exists_gt_isSupportingLine_of_finite {y : ℕ → WithTop ℝ}
    (hfin : {n | y n ≠ ⊤}.Finite) {m c : ℝ} {j : ℕ} (hj : y j = ((c + m * j : ℝ) : WithTop ℝ))
    (hlt : ∀ n, j < n → ((c + m * n : ℝ) : WithTop ℝ) < y n) :
    ∃ τ > m, IsSupportingLine (fun n ↦ y (j + n)) τ (c + m * j) := by
  classical
  -- The admissible increase of slope at a finite point `n > j`.
  let δ : ℕ → ℝ := fun n ↦ ((y n).untop₀ - (c + m * n)) / (n - j)
  let S := (hfin.toFinset.filter (j < ·))
  have hδ : ∀ n ∈ S, 0 < δ n := fun n hn ↦ by
    obtain ⟨hn, hjn⟩ := Finset.mem_filter.mp hn
    have hy := hlt n hjn
    rw [← WithTop.coe_untop₀_of_ne_top (hfin.mem_toFinset.mp hn), WithTop.coe_lt_coe] at hy
    exact div_pos (by linarith) (sub_pos.mpr (Nat.cast_lt.mpr hjn))
  obtain ⟨ε, hε, hεδ⟩ : ∃ ε > 0, ∀ n ∈ S, ε ≤ δ n := by
    rcases S.eq_empty_or_nonempty with hS | hS
    · exact ⟨1, one_pos, by simp [hS]⟩
    · exact ⟨S.inf' hS δ, (Finset.lt_inf'_iff hS).mpr hδ, fun n hn ↦ Finset.inf'_le δ hn⟩
  refine ⟨m + ε, by linarith, isSupportingLine_iff_forall.mpr fun k ↦ ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [hj]
  by_cases hyk : y (j + k) = ⊤
  · rw [hyk]
    exact le_top
  have hmem : j + k ∈ S := Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hyk, by omega⟩
  have hε' := hεδ _ hmem
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  rw [← WithTop.coe_untop₀_of_ne_top hyk, WithTop.coe_le_coe]
  simp only [δ, Nat.cast_add, add_sub_cancel_left] at hε'
  rw [le_div_iff₀ hk'] at hε'
  nlinarith

/-- **Coefficient-line criterion for a first break, finitely many points.** If `y` has only
finitely many finite points, as for the coefficient heights of a polynomial, the steeper line of
`IsLowerConvexEnvelope.isFirstBreak_iff` may be replaced by pointwise strict inequalities: the
envelope has its first break at `j` with slope `m` if and only if `a < j`, some line of slope `m`
supports `y` and passes through the points at `a` and at `j`, and every point after `j` lies
strictly above that line. Without finiteness the strict inequalities do not suffice. -/
theorem isFirstBreak_iff_of_finite (hh : IsLowerConvexEnvelope y h)
    (hfin : {n | y n ≠ ⊤}.Finite) {a : ℕ} (hya : y a ≠ ⊤) (hpre : ∀ n < a, y n = ⊤) {m : ℝ}
    {j : ℕ} :
    IsFirstBreak h m j ↔ a < j ∧ ∃ c : ℝ, IsSupportingLine y m c ∧
      a ∈ supportingFace y m c ∧ j ∈ supportingFace y m c ∧
      ∀ n, j < n → ((c + m * n : ℝ) : WithTop ℝ) < y n := by
  rw [hh.isFirstBreak_iff hya hpre]
  refine and_congr_right fun _ ↦ exists_congr fun c ↦ and_congr_right fun _ ↦
    and_congr_right fun _ ↦ and_congr_right fun hj ↦ ⟨?_, fun hlt ↦
      exists_gt_isSupportingLine_of_finite hfin (mem_supportingFace.mp hj) hlt⟩
  rintro ⟨τ, hτ, hτc⟩ n hjn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hjn
  refine lt_of_lt_of_le ?_ (isSupportingLine_iff_forall.mp hτc (k + 1))
  rw [WithTop.coe_lt_coe]
  push_cast
  nlinarith

end IsLowerConvexEnvelope

end TauCeti

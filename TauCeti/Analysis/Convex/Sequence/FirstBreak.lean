/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Vertex

/-!
# First breaks of convex height sequences

Let `h` be a height sequence whose finite domain begins at the index `i`. It has a *first break*
at `j` with slope `σ`, written `TauCeti.IsFirstBreak h σ j`, when its first segment has slope `σ`
and ends at `j`: we have `i < j`, every unit edge from `i` to `j` is finite of slope `σ`, and the
slope genuinely increases at `j`. The increase means that the unit edge starting at `j` is either
missing, as at the last coefficient of a polynomial, or finite of slope strictly greater than `σ`.
A singleton domain has no first break, and neither has a polygon whose first piece is an infinite
ray.

For a convex sequence a first break at `j` with slope `σ` is exactly a finite face of slope `σ`
of positive width that starts at the first finite index and ends at `j`
(`TauCeti.IsConvexSeq.isFirstBreak_iff_isFiniteFace`). The slope and the endpoint of a first
break are unique, and some line of slope strictly greater than `σ` through the endpoint supports
the sequence.

For the lower convex envelope of point heights `a` beginning at `i`, this gives a criterion in
terms of the points alone (`TauCeti.isFirstBreak_lowerConvexEnvelope_iff`). The envelope has a
first break at `j` with slope `σ` exactly when `i < j`, the line of slope `σ` through the first
point `(i, a i)` lies below every point and passes through `(j, a j)`, and every point after `j`
lies above a line of some strictly larger slope through `(j, a j)`. The last condition cannot be
replaced by the points after `j` lying strictly above the first line: the points
`0, 0, 1/2, 1/3, 1/4, …` lie strictly above the horizontal axis after the index `1`, but their
envelope has no first break at `1` (`TauCeti.exists_supportingFace_eq_Icc_and_not_isFirstBreak`).

Applied to the coefficient heights of a polynomial or power series, this is the first-break
criterion for Newton polygons; its translation into Gauss norms and Weierstrass preparation is in
`TauCeti.NumberTheory.NewtonPolygon.FirstBreak`.

## Main definitions

* `TauCeti.IsFirstBreak h σ j`: the first segment of `h` has slope `σ` and ends at `j`, where the
  slope increases or the finite domain ends.

## Main results

* `TauCeti.IsFirstBreak.unique`: a height sequence has at most one first break.
* `TauCeti.IsConvexSeq.isFirstBreak_iff_isFiniteFace`: for a convex sequence beginning at `i`,
  a first break at `j` is a finite face from `i` to `j` with `i < j`.
* `TauCeti.IsFirstBreak.exists_lt_isSupportingLine`: a line of strictly larger slope through the
  endpoint of a first break supports the sequence.
* `TauCeti.isFirstBreak_lowerConvexEnvelope_iff`: the first-break criterion in terms of points.
* `TauCeti.exists_supportingFace_eq_Icc_and_not_isFirstBreak`: points strictly above the first
  line after `j` need not give a first break at `j`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §§3–4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

namespace TauCeti

/-- A height sequence `h` has a *first break* at `j` with slope `σ` when its finite domain begins
at some index `i < j`, every unit edge from `i` to `j` is finite of slope `σ`, and the slope
genuinely increases at `j`: the unit edge starting at `j` is either missing, as at the endpoint of
a polynomial, or of slope strictly greater than `σ`. -/
def IsFirstBreak (h : ℕ → WithTop ℝ) (σ : ℝ) (j : ℕ) : Prop :=
  ∃ i < j, (∀ n < i, h n = ⊤) ∧
    (∀ n, i ≤ n → n < j → n ∈ finiteEdges h ∧ unitSlope h n = σ) ∧
    (j ∈ finiteEdges h → σ < unitSlope h j)

/-- Unfolding of `TauCeti.IsFirstBreak`: the finite domain begins at some `i < j`, the unit edges
from `i` to `j` are finite of slope `σ`, and the edge starting at `j`, if finite, is steeper. -/
theorem isFirstBreak_iff {h : ℕ → WithTop ℝ} {σ : ℝ} {j : ℕ} :
    IsFirstBreak h σ j ↔ ∃ i < j, (∀ n < i, h n = ⊤) ∧
      (∀ n, i ≤ n → n < j → n ∈ finiteEdges h ∧ unitSlope h n = σ) ∧
      (j ∈ finiteEdges h → σ < unitSlope h j) :=
  Iff.rfl

namespace IsFirstBreak

variable {h : ℕ → WithTop ℝ} {σ : ℝ} {j : ℕ}

/-- The endpoint of a first break has finite height. -/
theorem ne_top (hb : IsFirstBreak h σ j) : h j ≠ ⊤ := by
  obtain ⟨i, hij, -, hseg, -⟩ := hb
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  exact (mem_finiteEdges.mp (hseg (i + k) (by omega) (by omega)).1).2

/-- A height sequence has at most one first break: its slope and its endpoint are determined by
the sequence. -/
theorem unique (hb : IsFirstBreak h σ j) {σ' : ℝ} {j' : ℕ} (hb' : IsFirstBreak h σ' j') :
    σ = σ' ∧ j = j' := by
  obtain ⟨i, hij, hfirst, hseg, hnext⟩ := hb
  obtain ⟨i', hij', hfirst', hseg', hnext'⟩ := hb'
  have hi : h i ≠ ⊤ := (mem_finiteEdges.mp (hseg i le_rfl hij).1).1
  have hi' : h i' ≠ ⊤ := (mem_finiteEdges.mp (hseg' i' le_rfl hij').1).1
  obtain rfl : i = i' := le_antisymm (le_of_not_gt fun hlt => hi' (hfirst i' hlt))
    (le_of_not_gt fun hlt => hi (hfirst' i hlt))
  have hσ : σ = σ' := (hseg i le_rfl hij).2.symm.trans (hseg' i le_rfl hij').2
  subst σ'
  refine ⟨rfl, le_antisymm (le_of_not_gt fun hlt => ?_) (le_of_not_gt fun hlt => ?_)⟩
  · obtain ⟨hedge, hslope⟩ := hseg j' hij'.le hlt
    exact (hnext' hedge).ne' hslope
  · obtain ⟨hedge, hslope⟩ := hseg' j hij.le hlt
    exact (hnext hedge).ne' hslope

end IsFirstBreak

/-- For a convex height sequence whose finite domain begins at `i`, a first break at `j` with
slope `σ` is exactly a finite face of slope `σ` from `i` to `j` with `i < j`. -/
theorem IsConvexSeq.isFirstBreak_iff_isFiniteFace {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h)
    {i : ℕ} (hi : h i ≠ ⊤) (hfirst : ∀ n < i, h n = ⊤) {σ : ℝ} {j : ℕ} :
    IsFirstBreak h σ j ↔ i < j ∧ IsFiniteFace h σ i j := by
  constructor
  · rintro ⟨i', hij, hfirst', hseg, hnext⟩
    have hi' : h i' ≠ ⊤ := (mem_finiteEdges.mp (hseg i' le_rfl hij).1).1
    obtain rfl : i' = i := le_antisymm (le_of_not_gt fun hlt => hi (hfirst' i hlt))
      (le_of_not_gt fun hlt => hi' (hfirst i' hlt))
    have hj : h j ≠ ⊤ := IsFirstBreak.ne_top ⟨i', hij, hfirst', hseg, hnext⟩
    set c := (h i').untop₀ - σ * i' with hc_def
    -- The line of slope `σ` through the first point supports `h`: no edge precedes `i'`.
    have hc : IsSupportingLine h σ c := by
      refine (hh.isSupportingLine_iff_unitSlope hi' σ).mpr ⟨fun k hk hkf => ?_, fun _ => ?_⟩
      · exact absurd (hfirst' k (by omega)) hkf
      · exact (hseg i' le_rfl hij).2.ge
    have hi'_mem : i' ∈ supportingFace h σ c := by
      rw [mem_supportingFace, hc_def, sub_add_cancel, WithTop.coe_untop₀_of_ne_top hi']
    have hj_mem : j ∈ supportingFace h σ c := by
      have hsum : ∑ n ∈ Finset.Ico i' j, unitSlope h n = ∑ _n ∈ Finset.Ico i' j, σ :=
        Finset.sum_congr rfl fun n hn => by
          obtain ⟨hn₁, hn₂⟩ := Finset.mem_Ico.mp hn
          exact (hseg n hn₁ hn₂).2
      rw [mem_supportingFace, eq_coe_add_sum_unitSlope hj hij.le, hsum, Finset.sum_const,
        Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hij.le, WithTop.coe_eq_coe, hc_def]
      ring
    refine ⟨hij, isFiniteFace_iff.mpr ⟨hij.le, c, hc, Set.Subset.antisymm (fun n hn => ?_)
      ((hh.ordConnected_supportingFace hc).out hi'_mem hj_mem)⟩⟩
    have hn_top : h n ≠ ⊤ := by
      rw [mem_supportingFace.mp hn]
      exact WithTop.coe_ne_top
    refine ⟨le_of_not_gt fun hlt => hn_top (hfirst' n hlt), le_of_not_gt fun hjn => ?_⟩
    -- After `j` the next edge is finite, so its slope exceeds `σ` and the height leaves the line.
    have hj1 : h (j + 1) ≠ ⊤ := hh.ne_top_of_le_of_le hj hn_top (Nat.le_succ j) hjn
    have hσ := hnext (mem_finiteEdges.mpr ⟨hj, hj1⟩)
    have hs := hh.mul_slope_le_sub hn_top hj hjn.le le_rfl
    rw [Nat.cast_sub hjn.le, mem_supportingFace.mp hn, WithTop.untop₀_coe,
      mem_supportingFace.mp hj_mem, WithTop.untop₀_coe] at hs
    have hjn' : (j : ℝ) < n := Nat.cast_lt.mpr hjn
    nlinarith
  · rintro ⟨hij, hf⟩
    refine ⟨i, hij, hfirst, fun n hin hnj => ⟨mem_finiteEdges.mpr
      ⟨hh.ne_top_of_le_of_le hf.left_ne_top hf.right_ne_top hin hnj.le,
        hh.ne_top_of_le_of_le hf.left_ne_top hf.right_ne_top (hin.trans (Nat.le_succ n)) hnj⟩,
      hf.unitSlope_eq hin hnj⟩, fun hj => hf.lt_unitSlope hh hj le_rfl⟩

/-- At a first break of a convex height sequence, some line of slope strictly greater than `σ`
through the endpoint supports the sequence. -/
theorem IsFirstBreak.exists_lt_isSupportingLine {h : ℕ → WithTop ℝ} {σ : ℝ} {j : ℕ}
    (hb : IsFirstBreak h σ j) (hh : IsConvexSeq h) :
    ∃ τ, σ < τ ∧ IsSupportingLine h τ ((h j).untop₀ - τ * j) := by
  have hj := hb.ne_top
  obtain ⟨i, hij, -, hseg, hnext⟩ := hb
  have hleft {τ : ℝ} (hτ : σ ≤ τ) :
      ∀ k, k + 1 = j → h k ≠ ⊤ → unitSlope h k ≤ τ := fun k hk _ => by
    rw [(hseg k (by omega) (by omega)).2]
    exact hτ
  by_cases hje : j ∈ finiteEdges h
  · exact ⟨unitSlope h j, hnext hje, (hh.isSupportingLine_iff_unitSlope hj _).mpr
      ⟨hleft (hnext hje).le, fun _ => le_rfl⟩⟩
  · exact ⟨σ + 1, lt_add_one σ, (hh.isSupportingLine_iff_unitSlope hj _).mpr
      ⟨hleft (by linarith), fun hj1 => absurd (mem_finiteEdges.mpr ⟨hj, hj1⟩) hje⟩⟩

/-- The lower convex envelope of admissible points beginning at `i` begins at `i`, where it agrees
with the points. -/
private theorem isLowerConvexEnvelope_and_eq_and_eq_top {a : ℕ → WithTop ℝ} (ha : IsAdmissible a)
    {i : ℕ} (hfirst : ∀ n < i, a n = ⊤) :
    IsLowerConvexEnvelope a (lowerConvexEnvelope a) ∧ lowerConvexEnvelope a i = a i ∧
      ∀ n < i, lowerConvexEnvelope a n = ⊤ :=
  ⟨isLowerConvexEnvelope_lowerConvexEnvelope ha, lowerConvexEnvelope_eq_of_forall_lt ha hfirst,
    fun _ hn => lowerConvexEnvelope_eq_top_of_forall_le fun k hk => hfirst k (by omega)⟩

/-- The forward direction of `TauCeti.isFirstBreak_lowerConvexEnvelope_iff`: the first segment
lies on a supporting line of the points through the first point, and the next supporting slope
through its endpoint is strictly larger. -/
private theorem isSupportingLine_of_isFirstBreak_lowerConvexEnvelope {a : ℕ → WithTop ℝ} {i : ℕ}
    (hi : a i ≠ ⊤) (hfirst : ∀ n < i, a n = ⊤) {σ : ℝ} {j : ℕ}
    (hb : IsFirstBreak (lowerConvexEnvelope a) σ j) :
    i < j ∧ IsSupportingLine a σ ((a i).untop₀ - σ * i) ∧
      a j = (((a i).untop₀ + σ * ((j : ℝ) - i) : ℝ) : WithTop ℝ) ∧
      ∃ τ, σ < τ ∧
        ∀ n, j ≤ n → (((a j).untop₀ + τ * ((n : ℝ) - j) : ℝ) : WithTop ℝ) ≤ a n := by
  obtain ⟨hh, hHi, hHfirst⟩ := isLowerConvexEnvelope_and_eq_and_eq_top
    (isAdmissible_of_lowerConvexEnvelope_ne_top hb.ne_top) hfirst
  obtain ⟨hij, hface⟩ := (hh.isConvexSeq.isFirstBreak_iff_isFiniteFace (hHi ▸ hi) hHfirst).mp hb
  have hHj := hh.eq_right_of_isFiniteFace hface
  have hrise := hface.mul_width_eq_sub
  rw [hHi, hHj, Nat.cast_sub hij.le] at hrise
  refine ⟨hij, ?_, ?_, ?_⟩
  · rw [← hHi]
    exact hh.isSupportingLine_iff.mp
      (hface.isSupportingLine_untop₀_sub ⟨le_rfl, hface.left_le_right⟩)
  · rw [← WithTop.coe_untop₀_of_ne_top (hHj ▸ hface.right_ne_top : a j ≠ ⊤),
      WithTop.coe_eq_coe]
    linarith
  · obtain ⟨τ, hστ, hτ⟩ := hb.exists_lt_isSupportingLine hh.isConvexSeq
    refine ⟨τ, hστ, fun n _ => ?_⟩
    have hn := isSupportingLine_iff_forall.mp (hh.isSupportingLine_iff.mp hτ) n
    rw [hHj] at hn
    convert hn using 2
    ring

/-- The reverse direction of `TauCeti.isFirstBreak_lowerConvexEnvelope_iff`: lines of slopes
`σ < τ` through the first point and through `(j, a j)` as there give a first break at `j`. -/
private theorem isFirstBreak_lowerConvexEnvelope_of_isSupportingLine {a : ℕ → WithTop ℝ} {i : ℕ}
    (hi : a i ≠ ⊤) (hfirst : ∀ n < i, a n = ⊤) {σ τ : ℝ} {j : ℕ} (hij : i < j)
    (hsupp : IsSupportingLine a σ ((a i).untop₀ - σ * i))
    (hj : a j = (((a i).untop₀ + σ * ((j : ℝ) - i) : ℝ) : WithTop ℝ)) (hστ : σ < τ)
    (htail : ∀ n, j ≤ n → (((a j).untop₀ + τ * ((n : ℝ) - j) : ℝ) : WithTop ℝ) ≤ a n) :
    IsFirstBreak (lowerConvexEnvelope a) σ j := by
  obtain ⟨hh, hHi, hHfirst⟩ := isLowerConvexEnvelope_and_eq_and_eq_top hsupp.isAdmissible hfirst
  -- The line of slope `τ` through `(j, a j)` supports all the points, since before `j` it runs
  -- below the first line. The contact set of the first line with the envelope is then cut off
  -- before `i` by the finite domain and after `j` by the steeper line.
  set c := (a i).untop₀ - σ * i with hc_def
  set d := (a j).untop₀ - τ * j with hd_def
  -- The two lines cross at `j`: the first is above the second before `j` and below after it.
  have hcross (n : ℕ) : (c + σ * n) - (d + τ * n) = (τ - σ) * ((j : ℝ) - n) := by
    rw [hc_def, hd_def, hj, WithTop.untop₀_coe]
    ring
  have hd : IsSupportingLine a τ d := isSupportingLine_iff_forall.mpr fun n => by
    rcases le_or_gt j n with hjn | hnj
    · convert htail n hjn using 2
      rw [hd_def]
      ring
    · refine le_trans ?_ (isSupportingLine_iff_forall.mp hsupp n)
      rw [WithTop.coe_le_coe]
      have hnj' : (n : ℝ) < j := Nat.cast_lt.mpr hnj
      nlinarith [hcross n]
  have hcH := hh.isSupportingLine_iff.mpr hsupp
  have hi_mem : i ∈ supportingFace (lowerConvexEnvelope a) σ c :=
    hh.supportingFace_subset hsupp (by
      rw [mem_supportingFace, hc_def, sub_add_cancel, WithTop.coe_untop₀_of_ne_top hi])
  have hj_mem : j ∈ supportingFace (lowerConvexEnvelope a) σ c :=
    hh.supportingFace_subset hsupp (by
      rw [mem_supportingFace, hj, WithTop.coe_eq_coe, hc_def]
      ring)
  refine (hh.isConvexSeq.isFirstBreak_iff_isFiniteFace (hHi ▸ hi) hHfirst).mpr
    ⟨hij, isFiniteFace_iff.mpr ⟨hij.le, c, hcH, Set.Subset.antisymm (fun n hn => ?_)
      ((hh.isConvexSeq.ordConnected_supportingFace hcH).out hi_mem hj_mem)⟩⟩
  have hn := mem_supportingFace.mp hn
  refine ⟨le_of_not_gt fun hlt => ?_, le_of_not_gt fun hjn => ?_⟩
  · rw [hHfirst n hlt] at hn
    exact WithTop.top_ne_coe hn
  · have hle := isSupportingLine_iff_forall.mp (hh.isSupportingLine_iff.mpr hd) n
    rw [hn, WithTop.coe_le_coe] at hle
    have hjn' : (j : ℝ) < n := Nat.cast_lt.mpr hjn
    nlinarith [hcross n]

/-- **First-break criterion.** Let the point heights `a` begin at the index `i`. Their lower convex
envelope has a first break at `j` with slope `σ` exactly when `i < j`, the line of slope `σ` through
the first point `(i, a i)` lies below every point and passes through `(j, a j)`, and every point
after `j` lies above a line of some strictly larger slope `τ` through `(j, a j)`. Admissibility of
`a` is not assumed: each side implies it. -/
theorem isFirstBreak_lowerConvexEnvelope_iff {a : ℕ → WithTop ℝ} {i : ℕ} (hi : a i ≠ ⊤)
    (hfirst : ∀ n < i, a n = ⊤) {σ : ℝ} {j : ℕ} :
    IsFirstBreak (lowerConvexEnvelope a) σ j ↔
      i < j ∧ IsSupportingLine a σ ((a i).untop₀ - σ * i) ∧
        a j = (((a i).untop₀ + σ * ((j : ℝ) - i) : ℝ) : WithTop ℝ) ∧
        ∃ τ, σ < τ ∧
          ∀ n, j ≤ n → (((a j).untop₀ + τ * ((n : ℝ) - j) : ℝ) : WithTop ℝ) ≤ a n :=
  ⟨isSupportingLine_of_isFirstBreak_lowerConvexEnvelope hi hfirst,
    fun ⟨hij, hsupp, hj, _, hστ, htail⟩ =>
      isFirstBreak_lowerConvexEnvelope_of_isSupportingLine hi hfirst hij hsupp hj hστ htail⟩

/-- Points lying strictly above the first line after its last contact `j` need not give a first
break at `j`. For the points `0, 0, 1/2, 1/3, 1/4, …` the horizontal axis supports them and
touches them exactly at the indices `0` and `1`, but their lower convex envelope has no first break
at `1`, of any slope. -/
theorem exists_supportingFace_eq_Icc_and_not_isFirstBreak :
    ∃ a : ℕ → WithTop ℝ, IsSupportingLine a 0 0 ∧ supportingFace a 0 0 = Set.Icc 0 1 ∧
      ∀ σ, ¬IsFirstBreak (lowerConvexEnvelope a) σ 1 := by
  set a : ℕ → WithTop ℝ := fun n => (((if n ≤ 1 then 0 else (n : ℝ)⁻¹) : ℝ) : WithTop ℝ) with ha
  have ha0 : a 0 = ((0 : ℝ) : WithTop ℝ) := by simp [ha]
  refine ⟨a, isSupportingLine_iff_forall.mpr fun n => ?_, ?_, fun σ hb => ?_⟩
  · simp only [ha, zero_mul, add_zero, WithTop.coe_le_coe]
    split_ifs <;> positivity
  · ext n
    simp only [ha, mem_supportingFace, zero_mul, add_zero, WithTop.coe_eq_coe, Set.mem_Icc,
      zero_le, true_and]
    split_ifs with hn
    · exact iff_of_true rfl hn
    · exact iff_of_false (inv_ne_zero (by exact_mod_cast (by omega : n ≠ 0))) hn
  obtain ⟨-, -, hj, τ, hστ, htail⟩ :=
    (isFirstBreak_lowerConvexEnvelope_iff (i := 0) (by simp [ha0]) (by simp)).mp hb
  -- The second point forces `σ = 0`, and no line of positive slope through `(1, 0)` stays below
  -- the points `1 / n`.
  have hσ : σ = 0 := by simpa [ha, ha0] using hj
  subst hσ
  set n := ⌈τ⁻¹⌉₊ + 2 with hn
  have hle := htail n (by omega)
  have hn1 : ¬n ≤ 1 := by omega
  simp only [ha, hn1, ↓reduceIte, le_refl, WithTop.untop₀_coe, zero_add,
    WithTop.coe_le_coe, Nat.cast_one] at hle
  have hceil : τ⁻¹ ≤ (⌈τ⁻¹⌉₊ : ℝ) := Nat.le_ceil _
  have hτ1 : 1 ≤ τ * ⌈τ⁻¹⌉₊ := by
    calc (1 : ℝ) = τ * τ⁻¹ := (mul_inv_cancel₀ hστ.ne').symm
      _ ≤ τ * ⌈τ⁻¹⌉₊ := mul_le_mul_of_nonneg_left hceil hστ.le
  have hncast : (n : ℝ) = ⌈τ⁻¹⌉₊ + 2 := by rw [hn]; push_cast; ring
  have hinv : (n : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [hncast, inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num
  rw [hncast] at hle hinv
  nlinarith

end TauCeti

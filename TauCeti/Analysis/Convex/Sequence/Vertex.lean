/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Face

/-!
# Contact at vertices of a lower convex envelope

An interior vertex of a convex height sequence is a strict increase between two
adjacent finite unit slopes. For a lower convex envelope, every such vertex is
an original point of the sequence. Equivalently, at a noncontact interior index
the two adjacent slopes agree. Thus subdividing a straight segment does not
introduce geometric vertices, and a missing coefficient cannot be a vertex. The endpoints
of every finite face, including a singleton, are original points as well, whether they are
interior vertices or boundaries of the finite domain.

This gives a criterion for finite faces in terms of the original points alone
(`IsLowerConvexEnvelope.isFiniteFace_iff`): a line of slope `σ` supports the points and passes
through the points at `l` and `u`, and the lines through these two points with some strictly
smaller slope at `l` and some strictly larger slope at `u` also support the points.

The stronger local characterization `IsLowerConvexEnvelope.eq_min_of_finite_neighbors`
says that each interior height is the minimum of its coefficient height and the
average of its two neighboring heights. All results allow unbounded finite domains
and infinite coefficient heights.
-/

public section

namespace TauCeti

namespace IsLowerConvexEnvelope

variable {a h : ℕ → WithTop ℝ}

/-- At an index with two finite neighbors, an envelope height is the minimum of
the original point height and the neighboring average. In particular it can lie
strictly below the original point only along a straight segment. -/
theorem eq_min_of_finite_neighbors (hh : IsLowerConvexEnvelope a h) {n : ℕ}
    (hn : h n ≠ ⊤) (hn₂ : h (n + 2) ≠ ⊤) :
    h (n + 1) = min (a (n + 1))
      (((h n).untop₀ + (h (n + 2)).untop₀) / 2 : ℝ) := by
  have hn₁ : h (n + 1) ≠ ⊤ :=
    hh.isConvexSeq.ne_top_of_le_of_le hn hn₂ (by omega) (by omega)
  have hmid := (isConvexSeq_iff_two_mul_le.mp hh.isConvexSeq).2 n hn hn₂
  have havg : h (n + 1) ≤
      ((((h n).untop₀ + (h (n + 2)).untop₀) / 2 : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_untop₀_of_ne_top hn₁, WithTop.coe_le_coe]
    linarith
  let z := min (a (n + 1))
    ((((h n).untop₀ + (h (n + 2)).untop₀) / 2 : ℝ) : WithTop ℝ)
  have hz : z ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  lift z to ℝ using hz with y hy
  have hlow : h (n + 1) ≤ (y : WithTop ℝ) := by
    rw [hy]
    exact le_min (hh.le _) havg
  have hhigh : (y : WithTop ℝ) ≤
      ((((h n).untop₀ + (h (n + 2)).untop₀) / 2 : ℝ) : WithTop ℝ) := by
    rw [hy]
    exact min_le_right _ _
  have hcv := hh.isConvexSeq.update_of_le (y := y) hn hn₂
    (by rwa [← WithTop.coe_untop₀_of_ne_top hn₁, WithTop.coe_le_coe] at hlow)
    (by rw [WithTop.coe_le_coe] at hhigh; linarith)
  have hle : Function.update h (n + 1) (y : WithTop ℝ) ≤ a :=
    update_le_iff.mpr ⟨by rw [hy]; exact min_le_left _ _, fun k _ => hh.le k⟩
  have hmax := hh.greatest hcv hle (n + 1)
  simp only [Function.update_self] at hmax
  simpa only [hy] using le_antisymm hlow hmax

/-- Every interior strict slope change of a lower convex envelope is an original
point. Both slopes are genuine finite edges; there are no endpoint sentinels. -/
theorem eq_of_unitSlope_lt (hh : IsLowerConvexEnvelope a h) {n : ℕ}
    (hn : h n ≠ ⊤) (hn₂ : h (n + 2) ≠ ⊤)
    (hs : unitSlope h n < unitSlope h (n + 1)) : h (n + 1) = a (n + 1) := by
  have hn₁ : h (n + 1) ≠ ⊤ :=
    hh.isConvexSeq.ne_top_of_le_of_le hn hn₂ (by omega) (by omega)
  have hstrict : h (n + 1) <
      ((((h n).untop₀ + (h (n + 2)).untop₀) / 2 : ℝ) : WithTop ℝ) := by
    rw [← WithTop.coe_untop₀_of_ne_top hn₁, WithTop.coe_lt_coe]
    simp only [unitSlope_def, Nat.add_assoc] at hs
    linarith
  have heq := hh.eq_min_of_finite_neighbors hn hn₂
  by_cases hle : a (n + 1) ≤
      ((((h n).untop₀ + (h (n + 2)).untop₀) / 2 : ℝ) : WithTop ℝ)
  · simpa only [min_eq_left hle] using heq
  · rw [min_eq_right (le_of_not_ge hle)] at heq
    exact False.elim ((ne_of_lt hstrict) heq)

/-- At a noncontact interior index the two neighboring finite slopes agree.
This also applies when the original point height is infinite. The neighbors of a noncontact
index are automatically finite. -/
theorem unitSlope_eq_of_lt (hh : IsLowerConvexEnvelope a h) {n : ℕ}
    (ha : h (n + 1) < a (n + 1)) : unitSlope h n = unitSlope h (n + 1) := by
  have hn₁ : h (n + 1) ≠ ⊤ := ne_top_of_lt (ha.trans_le le_top)
  have hn : h n ≠ ⊤ := by
    intro hn
    refine ha.ne ?_
    have hfirst : ∀ k < n + 1, a k = ⊤ := by
      intro k hkl
      by_contra hk
      exact (hh.isConvexSeq.ne_top_of_le_of_le (j := n) (ne_top_of_le_ne_top hk (hh.le k)) hn₁
        (by omega) (by omega)) hn
    rw [hh.eq_lowerConvexEnvelope]
    exact lowerConvexEnvelope_eq_of_forall_lt hh.isAdmissible hfirst
  have hn₂ : h (n + 2) ≠ ⊤ := by
    intro hn₂
    refine ha.ne ?_
    have hlast : ∀ k, n + 1 < k → a k = ⊤ := by
      intro k hlk
      by_contra hk
      exact (hh.isConvexSeq.ne_top_of_le_of_le (j := n + 2) hn₁ (ne_top_of_le_ne_top hk (hh.le k))
        (by omega) (by omega)) hn₂
    rw [hh.eq_lowerConvexEnvelope]
    exact lowerConvexEnvelope_eq_of_forall_gt hlast
  have hmono := hh.isConvexSeq.monotoneOn (a := n) (b := n + 1)
    (mem_finiteEdges.mpr ⟨hn, hn₁⟩) (mem_finiteEdges.mpr ⟨hn₁, hn₂⟩) (by omega)
  exact hmono.eq_of_not_lt fun hs => (ne_of_lt ha) (hh.eq_of_unitSlope_lt hn hn₂ hs)

/-- The left endpoint of a finite face, including a singleton, is an original point.
The finite domain of the envelope need not be bounded. -/
theorem eq_left_of_isFiniteFace (hh : IsLowerConvexEnvelope a h) {σ : ℝ} {l u : ℕ}
    (hf : IsFiniteFace h σ l u) : h l = a l := by
  have hl := hf.left_ne_top
  by_cases hnext : h (l + 1) = ⊤
  · have hlast : ∀ k, l < k → a k = ⊤ := by
      intro k hlk
      by_contra hk
      have hk' := ne_top_of_le_ne_top hk (hh.le k)
      exact (hh.isConvexSeq.ne_top_of_le_of_le (j := l + 1) hl hk'
        (by omega) (by omega)) hnext
    rw [hh.eq_lowerConvexEnvelope]
    exact lowerConvexEnvelope_eq_of_forall_gt hlast
  by_cases hprev : ∃ i, i + 1 = l ∧ h i ≠ ⊤
  · obtain ⟨i, rfl, hi⟩ := hprev
    have hs := hf.unitSlope_lt hh.isConvexSeq (mem_finiteEdges.mpr ⟨hi, hl⟩) (Nat.lt_succ_self i)
    have hbound := ((hh.isConvexSeq.isSupportingLine_iff_unitSlope hl σ).mp
      (hf.isSupportingLine_untop₀_sub ⟨le_rfl, hf.left_le_right⟩)).2 hnext
    exact hh.eq_of_unitSlope_lt hi hnext (hs.trans_le hbound)
  · have hfirst : ∀ k < l, a k = ⊤ := by
      intro k hkl
      by_contra hk
      have hk' := ne_top_of_le_ne_top hk (hh.le k)
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
      exact hprev ⟨i, rfl, hh.isConvexSeq.ne_top_of_le_of_le hk' hl
        (by omega) (by omega)⟩
    rw [hh.eq_lowerConvexEnvelope]
    exact lowerConvexEnvelope_eq_of_forall_lt hh.isAdmissible hfirst

/-- The right endpoint of a finite face, including a singleton, is an original point.
An unbounded terminal ray is excluded by the finite-face hypothesis. -/
theorem eq_right_of_isFiniteFace (hh : IsLowerConvexEnvelope a h) {σ : ℝ} {l u : ℕ}
    (hf : IsFiniteFace h σ l u) : h u = a u := by
  rcases eq_or_lt_of_le hf.left_le_right with rfl | hlu
  · exact hh.eq_left_of_isFiniteFace hf
  have hu := hf.right_ne_top
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
  have hi := hh.isConvexSeq.ne_top_of_le_of_le (j := i) hf.left_ne_top hu (by omega) (by omega)
  by_cases hnext : h (i + 2) = ⊤
  · have hlast : ∀ k, i + 1 < k → a k = ⊤ := by
      intro k huk
      by_contra hk
      have hk' := ne_top_of_le_ne_top hk (hh.le k)
      exact (hh.isConvexSeq.ne_top_of_le_of_le (j := i + 2) hu hk'
        (by omega) (by omega)) hnext
    rw [hh.eq_lowerConvexEnvelope]
    exact lowerConvexEnvelope_eq_of_forall_gt hlast
  · have hs := hf.lt_unitSlope hh.isConvexSeq (mem_finiteEdges.mpr ⟨hu, hnext⟩) le_rfl
    have heq := hf.unitSlope_eq (by omega) (Nat.lt_succ_self i)
    exact hh.eq_of_unitSlope_lt hi hnext (by simpa only [heq] using hs)

/-- The absolute endpoints of a finite envelope face are the first and last original
points touching its supporting line. Interior original points need not lie on the line. -/
theorem exists_isSupportingLine_isLeast_isGreatest_of_isFiniteFace
    (hh : IsLowerConvexEnvelope a h) {σ : ℝ} {l u : ℕ}
    (hf : IsFiniteFace h σ l u) :
    ∃ c : ℝ, IsSupportingLine a σ c ∧
      IsLeast (supportingFace a σ c) l ∧ IsGreatest (supportingFace a σ c) u := by
  obtain ⟨c, hc, hface⟩ := hf.exists_intercept
  have hac : IsSupportingLine a σ c := isSupportingLine_iff_forall.mpr
    fun n => (isSupportingLine_iff_forall.mp hc n).trans (hh.le n)
  have hsub : supportingFace a σ c ⊆ Set.Icc l u :=
    (hh.supportingFace_subset hac).trans hface.subset
  refine ⟨c, hac, ⟨?_, fun n hn => (hsub hn).1⟩, ⟨?_, fun n hn => (hsub hn).2⟩⟩
  · rw [mem_supportingFace, ← hh.eq_left_of_isFiniteFace hf]
    exact mem_supportingFace.mp (hface.symm.subset ⟨le_rfl, hf.left_le_right⟩)
  · rw [mem_supportingFace, ← hh.eq_right_of_isFiniteFace hf]
    exact mem_supportingFace.mp (hface.symm.subset ⟨hf.left_le_right, le_rfl⟩)

/-- Sufficiency in the finite-face criterion: if a line of slope `σ` supports the point heights
and passes through the points at `l ≤ u`, and the lines through these two points with some
strictly smaller slope at `l` and some strictly larger slope at `u` also support the point
heights, then the envelope has a finite face of slope `σ` from `l` to `u`. -/
theorem isFiniteFace_of_isSupportingLine (hh : IsLowerConvexEnvelope a h) {σ c τ₁ τ₂ : ℝ}
    {l u : ℕ} (hlu : l ≤ u) (hc : IsSupportingLine a σ c) (hl : l ∈ supportingFace a σ c)
    (hu : u ∈ supportingFace a σ c) (hτ₁ : τ₁ < σ)
    (hc₁ : IsSupportingLine a τ₁ (c + (σ - τ₁) * l)) (hτ₂ : σ < τ₂)
    (hc₂ : IsSupportingLine a τ₂ (c + (σ - τ₂) * u)) : IsFiniteFace h σ l u := by
  have hch := hh.isSupportingLine_iff.mpr hc
  refine isFiniteFace_iff.mpr ⟨hlu, c, hch, Set.Subset.antisymm (fun n hn => ?_) fun n hn => ?_⟩
  · -- Off `[l, u]` one of the two tilted lines lies strictly above the line of slope `σ`.
    rw [mem_supportingFace] at hn
    have h₁ := isSupportingLine_iff_forall.mp (hh.isSupportingLine_iff.mpr hc₁) n
    have h₂ := isSupportingLine_iff_forall.mp (hh.isSupportingLine_iff.mpr hc₂) n
    rw [hn, WithTop.coe_le_coe] at h₁ h₂
    refine ⟨Nat.cast_le.mp (le_of_not_gt fun (hnl : (n : ℝ) < l) => ?_),
      Nat.cast_le.mp (le_of_not_gt fun (hun : (u : ℝ) < n) => ?_)⟩
    · nlinarith [mul_pos (sub_pos.mpr hτ₁) (sub_pos.mpr hnl)]
    · nlinarith [mul_pos (sub_pos.mpr hτ₂) (sub_pos.mpr hun)]
  · exact mem_supportingFace.mpr <| hh.isConvexSeq.eq_affine_of_affine_le
      (mem_supportingFace.mp (hh.supportingFace_subset hc hl))
      (mem_supportingFace.mp (hh.supportingFace_subset hc hu)) hn.1 hn.2
      (isSupportingLine_iff_forall.mp hch n)

/-- **Finite-face criterion.** A lower convex envelope has a finite face of slope `σ` from `l` to
`u` exactly when some line of slope `σ` supports the point heights and passes through the points
at `l` and `u`, and the lines through these two points with some strictly smaller slope at `l` and
some strictly larger slope at `u` also support the point heights.

The tilted lines cannot be replaced by asking the other points to lie strictly above the line of
slope `σ`: infinitely many points may approach that line, and the envelope then follows it. -/
theorem isFiniteFace_iff (hh : IsLowerConvexEnvelope a h) {σ : ℝ} {l u : ℕ} :
    IsFiniteFace h σ l u ↔ l ≤ u ∧ ∃ c : ℝ, IsSupportingLine a σ c ∧
      l ∈ supportingFace a σ c ∧ u ∈ supportingFace a σ c ∧
      (∃ τ < σ, IsSupportingLine a τ (c + (σ - τ) * l)) ∧
      ∃ τ > σ, IsSupportingLine a τ (c + (σ - τ) * u) := by
  refine ⟨fun hf => ?_, fun ⟨hlu, c, hc, hl, hu, ⟨τ₁, hτ₁, hc₁⟩, τ₂, hτ₂, hc₂⟩ =>
    hh.isFiniteFace_of_isSupportingLine hlu hc hl hu hτ₁ hc₁ hτ₂ hc₂⟩
  obtain ⟨c, hc, hl, hu⟩ := hh.exists_isSupportingLine_isLeast_isGreatest_of_isFiniteFace hf
  have hl' : h l = ((c + σ * l : ℝ) : WithTop ℝ) :=
    (hh.eq_left_of_isFiniteFace hf).trans (mem_supportingFace.mp hl.1)
  have hu' : h u = ((c + σ * u : ℝ) : WithTop ℝ) :=
    (hh.eq_right_of_isFiniteFace hf).trans (mem_supportingFace.mp hu.1)
  obtain ⟨ε₁, hε₁, hc₁⟩ := hf.exists_pos_isSupportingLine_left hh.isConvexSeq
  obtain ⟨ε₂, hε₂, hc₂⟩ := hf.exists_pos_isSupportingLine_right hh.isConvexSeq
  have hc₁' := hc₁ (σ - ε₁) ⟨le_rfl, by linarith⟩
  have hc₂' := hc₂ (σ + ε₂) ⟨by linarith, le_rfl⟩
  rw [hl', WithTop.untop₀_coe] at hc₁'
  rw [hu', WithTop.untop₀_coe] at hc₂'
  refine ⟨hf.left_le_right, c, hc, hl.1, hu.1, ⟨σ - ε₁, by linarith, ?_⟩, σ + ε₂, by linarith, ?_⟩
  · convert hh.isSupportingLine_iff.mp hc₁' using 1
    ring
  · convert hh.isSupportingLine_iff.mp hc₂' using 1
    ring

end IsLowerConvexEnvelope

end TauCeti

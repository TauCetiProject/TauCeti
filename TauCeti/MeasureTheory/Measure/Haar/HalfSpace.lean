/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.MeasureTheory.Covering.EssentialBoundary
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Sets stable under a half-space of translations

Let `ν` be a vector of a real inner product space `E`. A set `S ⊆ E` with `S + h ⊆ S` for every
`h` with `⟪h, ν⟫ ≤ 0` is determined by the values of `⟪·, ν⟫` on it, and these form a lower set of
`ℝ`. Hence `S` is empty, the whole space, an open half-space `{y | ⟪y, ν⟫ < c}` or a closed
half-space `{y | ⟪y, ν⟫ ≤ c}` (`TauCeti.eq_setOf_inner_lt_or_le_of_forall_inner_nonpos`).

The measure-theoretic form holds against an additive Haar measure `μ` on a finite-dimensional
space. If a null-measurable set `s` satisfies `x + h ∈ s` for `μ`-almost every `x ∈ s`, for each
such `h` separately, then `s` agrees almost everywhere with `∅`, with `univ` or with an open
half-space `{y | ⟪y, ν⟫ < c}` (`TauCeti.ae_eq_setOf_inner_lt_of_forall_inner_nonpos`). The
exceptional null sets may depend on `h`. The proof replaces `s` by its essential interior, which is
a.e. equal to `s` by Lebesgue's density theorem and commutes with translations, so it is stable
under the translations exactly. A hyperplane is null, so the open and closed half-spaces agree
almost everywhere.

This is how a set of locally finite perimeter with a constant outer normal is identified with a
half-space, the rigidity step in the blow-up of sets of finite perimeter at points of the
reduced boundary.

A nontrivial half-space has density one half at every point of its boundary hyperplane. Its
essential interior and exterior are the two strict half-spaces, and its essential boundary is
exactly the hyperplane. Thus these measure-theoretic sets also identify the boundary of any
almost-everywhere representative of a half-space.

## Main declarations

* `TauCeti.eq_setOf_inner_lt_or_le_of_forall_inner_nonpos`: the exact classification.
* `TauCeti.ae_eq_setOf_inner_lt_of_forall_inner_nonpos`: the almost-everywhere classification.
* `MeasureTheory.Measure.addHaar_setOf_inner_lt_inter_closedBall`: the exact half-ball measure.
* `TauCeti.hasDensityAt_setOf_inner_lt`: density one half on the boundary hyperplane.
* `TauCeti.essentialBoundary_setOf_inner_lt`: the essential boundary is the hyperplane.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.2.
-/

public section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ν : E}

/-- **Sets stable under a half-space of translations.** If `x + h ∈ S` whenever `x ∈ S` and
`⟪h, ν⟫ ≤ 0`, then `S` is empty, the whole space, or a half-space `{y | ⟪y, ν⟫ < c}` or
`{y | ⟪y, ν⟫ ≤ c}`. -/
theorem eq_setOf_inner_lt_or_le_of_forall_inner_nonpos {S : Set E}
    (hS : ∀ h, ⟪h, ν⟫ ≤ 0 → ∀ x ∈ S, x + h ∈ S) :
    S = ∅ ∨ S = univ ∨ ∃ c, S = {y | ⟪y, ν⟫ < c} ∨ S = {y | ⟪y, ν⟫ ≤ c} := by
  rcases eq_or_ne ν 0 with rfl | hν
  · -- For `ν = 0` every translation preserves `S`, so it is empty or the whole space.
    rcases S.eq_empty_or_nonempty with hS0 | ⟨x, hx⟩
    · exact Or.inl hS0
    · exact Or.inr (Or.inl (eq_univ_of_forall fun y => by simpa using hS (y - x) (by simp) x hx))
  set T := (fun y => ⟪y, ν⟫) '' S
  have hν2 : ⟪ν, ν⟫ ≠ 0 := inner_self_ne_zero.2 hν
  -- Membership in `S` only depends on `⟪·, ν⟫`, whose values on `S` form a lower set.
  have hmem (y : E) : y ∈ S ↔ ⟪y, ν⟫ ∈ T := by
    refine ⟨fun hy => ⟨y, hy, rfl⟩, ?_⟩
    rintro ⟨x, hx, hxy⟩
    simpa using hS (y - x) (by simp [inner_sub_left, ← hxy]) x hx
  have hlow {t t' : ℝ} (htt' : t ≤ t') (ht' : t' ∈ T) : t ∈ T := by
    obtain ⟨x, hx, rfl⟩ := ht'
    refine ⟨x + ((t - ⟪x, ν⟫) / ⟪ν, ν⟫) • ν, hS _ ?_ x hx, ?_⟩
    · rw [real_inner_smul_left, div_mul_cancel₀ _ hν2]
      linarith
    · simp only [inner_add_left, real_inner_smul_left, div_mul_cancel₀ _ hν2]
      ring
  rcases T.eq_empty_or_nonempty with hT | hT
  · exact Or.inl (eq_empty_of_forall_notMem fun y hy => by simpa [hT] using (hmem y).1 hy)
  by_cases hbdd : BddAbove T
  · refine Or.inr (Or.inr ⟨sSup T, ?_⟩)
    by_cases hc : sSup T ∈ T
    · refine Or.inr (ext fun y => ?_)
      rw [hmem, mem_ofPred_eq]
      exact ⟨fun h => le_csSup hbdd h, fun h => hlow h hc⟩
    · refine Or.inl (ext fun y => ?_)
      rw [hmem, mem_ofPred_eq]
      refine ⟨fun h => (le_csSup hbdd h).lt_of_ne fun he => hc (he ▸ h), fun h => ?_⟩
      obtain ⟨t, ht, hlt⟩ := exists_lt_of_lt_csSup hT h
      exact hlow hlt.le ht
  · refine Or.inr (Or.inl (eq_univ_of_forall fun y => (hmem y).2 ?_))
    obtain ⟨t, ht, hlt⟩ := not_bddAbove_iff.1 hbdd ⟪y, ν⟫
    exact hlow hlt.le ht

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

/-- For `ν ≠ 0`, a closed half-space agrees almost everywhere with the open one, since the
hyperplane `{y | ⟪y, ν⟫ = c}` is null for an additive Haar measure. -/
theorem setOf_inner_le_ae_eq_setOf_inner_lt (hν : ν ≠ 0) (c : ℝ) :
    {y : E | ⟪y, ν⟫ ≤ c} =ᵐ[μ] {y | ⟪y, ν⟫ < c} := by
  refine ae_eq_set.2 ⟨measure_mono_null (fun y hy => ?_) (Measure.addHaar_setOf_inner_eq μ hν c),
    measure_mono_null (fun y hy => ?_) measure_empty⟩
  · exact le_antisymm hy.1 (not_lt.1 hy.2)
  · simp only [mem_sdiff, mem_ofPred_eq, not_le] at hy
    linarith [hy.1, hy.2]

/-- **Sets almost stable under a half-space of translations.** Let `μ` be an additive Haar
measure and `s` a null-measurable set such that, for every `h` with `⟪h, ν⟫ ≤ 0`, almost every
`x ∈ s` has `x + h ∈ s`. Then `s` agrees almost everywhere with `∅`, with `univ` or with an open
half-space `{y | ⟪y, ν⟫ < c}`. -/
theorem ae_eq_setOf_inner_lt_of_forall_inner_nonpos {s : Set E} (hs : NullMeasurableSet s μ)
    (H : ∀ h, ⟪h, ν⟫ ≤ 0 → ∀ᵐ x ∂μ, x ∈ s → x + h ∈ s) :
    s =ᵐ[μ] (∅ : Set E) ∨ s =ᵐ[μ] (univ : Set E) ∨ ∃ c : ℝ, s =ᵐ[μ] {y | ⟪y, ν⟫ < c} := by
  set S := essentialInterior μ s
  have hSs : s =ᵐ[μ] S := (essentialInterior_ae_eq hs).symm
  -- The essential interior is stable under these translations, without exceptional sets.
  have hS (h : E) (hh : ⟪h, ν⟫ ≤ 0) (x : E) (hx : x ∈ S) : x + h ∈ S := by
    have hle : s ≤ᵐ[μ] (· + h) ⁻¹' s := H h hh
    simpa [S, essentialInterior_preimage_add_right] using essentialInterior_mono_ae hle hx
  rcases eq_setOf_inner_lt_or_le_of_forall_inner_nonpos hS with h0 | h1 | ⟨c, hc | hc⟩
  · exact Or.inl (hSs.trans (h0 ▸ Filter.EventuallyEq.rfl))
  · exact Or.inr (Or.inl (hSs.trans (h1 ▸ Filter.EventuallyEq.rfl)))
  · exact Or.inr (Or.inr ⟨c, hSs.trans (hc ▸ Filter.EventuallyEq.rfl)⟩)
  rcases eq_or_ne ν 0 with rfl | hν
  · -- For `ν = 0` the closed half-space `{y | 0 ≤ c}` is empty or the whole space.
    by_cases hc0 : 0 ≤ c
    · exact Or.inr (Or.inl (hSs.trans (by simp [hc, hc0])))
    · exact Or.inl (hSs.trans (by simp [hc, hc0]))
  · exact Or.inr (Or.inr ⟨c, (hSs.trans (hc ▸ Filter.EventuallyEq.rfl)).trans
      (setOf_inner_le_ae_eq_setOf_inner_lt hν c)⟩)

/-! ### Density and essential boundary -/

open Filter Metric
open scoped ENNReal Topology

/-- A half-space cuts every closed ball centred on its boundary hyperplane into two equal parts,
for any additive Haar measure. -/
theorem _root_.MeasureTheory.Measure.addHaar_setOf_inner_lt_inter_closedBall
    (μ : Measure E) [μ.IsAddHaarMeasure] {ν x : E} {c r : ℝ} (hν : ν ≠ 0)
    (hx : ⟪x, ν⟫ = c) :
    μ ({y | ⟪y, ν⟫ < c} ∩ closedBall x r) = μ (closedBall x r) / 2 := by
  let A := {y | ⟪y, ν⟫ < c} ∩ closedBall x r
  let B := {y | c < ⟪y, ν⟫} ∩ closedBall x r
  have hB : MeasurableSet B :=
    (isOpen_lt continuous_const (continuous_id.inner continuous_const)).measurableSet.inter
      measurableSet_closedBall
  -- Central reflection about `x` preserves the ball and exchanges its two half-spaces.
  have hpre : (fun y => x + x - y) ⁻¹' B = A := by
    ext y
    simp only [A, B, mem_preimage, mem_inter_iff, mem_ofPred_eq, mem_closedBall,
      dist_eq_norm, inner_sub_left, inner_add_left, hx]
    have hn : ‖x + x - y - x‖ = ‖y - x‖ := by
      have hvec : x + x - y - x = -(y - x) := by abel
      rw [hvec, norm_neg]
    rw [hn]
    constructor <;> rintro ⟨h, hy⟩ <;> exact ⟨by linarith, hy⟩
  have hAB : μ A = μ B := by
    rw [← hpre]
    exact (μ.measurePreserving_sub_left (x + x)).measure_preimage hB.nullMeasurableSet
  have hdis : Disjoint A B := by
    rw [disjoint_left]
    intro y hyA hyB
    have ha : ⟪y, ν⟫ < c := hyA.1
    have hb : c < ⟪y, ν⟫ := hyB.1
    exact (lt_trans ha hb).false
  have hunion : A ∪ B = closedBall x r \ {y | ⟪y, ν⟫ = c} := by
    ext y
    simp only [A, B, mem_union, mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff]
    constructor
    · rintro (⟨hy, hr⟩ | ⟨hy, hr⟩)
      · exact ⟨hr, ne_of_lt hy⟩
      · exact ⟨hr, ne_of_gt hy⟩
    · rintro ⟨hr, hy⟩
      exact (lt_or_gt_of_ne hy).elim (fun h => .inl ⟨h, hr⟩) (fun h => .inr ⟨h, hr⟩)
  have hsum : μ A + μ A = μ (closedBall x r) := by
    have hu : μ A + μ B = μ (closedBall x r) := by
      rw [← measure_union hdis hB, hunion,
        measure_sdiff_null (μ.addHaar_setOf_inner_eq hν c)]
    simpa only [← hAB] using hu
  exact (ENNReal.eq_div_iff (by norm_num) (by norm_num)).2 (by
    simpa only [two_mul] using hsum)

/-- At every point of the boundary hyperplane of a half-space with nonzero normal, its
density with respect to any additive Haar measure is one half. -/
theorem hasDensityAt_setOf_inner_lt {x : E} {c : ℝ} (hν : ν ≠ 0) (hx : ⟪x, ν⟫ = c) :
    HasDensityAt μ {y | ⟪y, ν⟫ < c} x (1 / 2) := by
  rw [hasDensityAt_iff]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_measure_closedBall_ne_zero_ne_top μ x] with r hμ
  rw [μ.addHaar_setOf_inner_lt_inter_closedBall hν hx, ENNReal.div_right_comm,
    ENNReal.div_self hμ.1 hμ.2]

/-- The essential interior of a strict half-space with nonzero normal is the half-space
itself. -/
@[simp]
theorem essentialInterior_setOf_inner_lt {c : ℝ} (hν : ν ≠ 0) :
    essentialInterior μ {y | ⟪y, ν⟫ < c} = {y | ⟪y, ν⟫ < c} := by
  have hopen : IsOpen {y : E | ⟪y, ν⟫ < c} :=
    isOpen_lt (continuous_id.inner continuous_const) continuous_const
  have hopen' : IsOpen {y : E | c < ⟪y, ν⟫} :=
    isOpen_lt continuous_const (continuous_id.inner continuous_const)
  apply Subset.antisymm
  · intro x hx
    rcases lt_trichotomy ⟪x, ν⟫ c with h | h | h
    · exact h
    · have heq := (mem_essentialInterior.1 hx).unique (hasDensityAt_setOf_inner_lt hν h)
      exact ((ne_of_gt (ENNReal.inv_lt_one.2 (by norm_num : (1 : ℝ≥0∞) < 2)))
        (by simpa using heq)).elim
    · have hu : x ∈ essentialInterior μ {y | ⟪y, ν⟫ < c}ᶜ := by
        apply interior_subset_essentialInterior
        have hin : x ∈ interior {y | c < ⟪y, ν⟫} := by rwa [hopen'.interior_eq]
        have hsub : {y : E | c < ⟪y, ν⟫} ⊆ {y | ⟪y, ν⟫ < c}ᶜ := by
          intro y hy
          simp only [mem_compl_iff, mem_ofPred_eq] at *
          exact not_lt.2 (le_of_lt hy)
        exact interior_mono hsub hin
      have hx' : x ∈ essentialExterior μ {y | ⟪y, ν⟫ < c} :=
        (essentialInterior_compl hopen.measurableSet.nullMeasurableSet).subset hu
      exact (disjoint_left.1 disjoint_essentialInterior_essentialExterior hx hx').elim
  · simpa only [hopen.interior_eq] using
      (interior_subset_essentialInterior (μ := μ) (s := {y | ⟪y, ν⟫ < c}))

/-- The essential exterior of a strict half-space with nonzero normal is the opposite
strict half-space. -/
@[simp]
theorem essentialExterior_setOf_inner_lt {c : ℝ} (hν : ν ≠ 0) :
    essentialExterior μ {y | ⟪y, ν⟫ < c} = {y | c < ⟪y, ν⟫} := by
  have hae : {y : E | ⟪y, ν⟫ < c}ᶜ =ᵐ[μ] {y | ⟪y, -ν⟫ < -c} := by
    simpa only [compl_ofPred, not_lt, inner_neg_right, neg_le_neg_iff, neg_lt_neg_iff] using
      (setOf_inner_le_ae_eq_setOf_inner_lt (μ := μ) (neg_ne_zero.2 hν) (-c))
  have hsm : NullMeasurableSet {y : E | ⟪y, ν⟫ < c} μ :=
    (isOpen_lt (continuous_id.inner continuous_const)
      continuous_const).measurableSet.nullMeasurableSet
  rw [← essentialInterior_compl hsm,
    essentialInterior_congr_ae hae, essentialInterior_setOf_inner_lt (neg_ne_zero.2 hν)]
  ext y
  simp

/-- The essential boundary of a half-space with nonzero normal is exactly its boundary
hyperplane. -/
@[simp]
theorem essentialBoundary_setOf_inner_lt {c : ℝ} (hν : ν ≠ 0) :
    essentialBoundary μ {y | ⟪y, ν⟫ < c} = {y | ⟪y, ν⟫ = c} := by
  rw [essentialBoundary_def, essentialInterior_setOf_inner_lt hν,
    essentialExterior_setOf_inner_lt hν]
  ext y
  simp only [mem_compl_iff, mem_union, mem_ofPred_eq, not_or, not_lt]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

end TauCeti

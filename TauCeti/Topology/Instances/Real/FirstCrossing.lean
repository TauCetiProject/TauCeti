/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.MetricSpace.Lebesgue

/-!
# First self-intersections and first crossings of curves

Two compactness arguments extract simple closed curves from curves parametrized by compact
intervals of `ℝ`.

* A curve `σ`, continuous on `[c, d]` and injective near each parameter of `[c, d]` (on the
  trace on `[c, d]` of a neighbourhood), which is not injective on `[c, d]`, has a first return:
  there are `a < b` in `[c, d]` with `σ a = σ b` and `σ` injective on `[c, b)`. Then `σ` on
  `[a, b]` is a simple closed curve. Local injectivity, made uniform by the Lebesgue number
  lemma, keeps the pairs of parameters with the same image away from the diagonal, so the set of
  such pairs is compact and its second coordinate attains its minimum.
* Two injective arcs `α, β` on `[0, 1]` with common endpoints that do not meet for small
  positive parameters have a first crossing: a pair `(a, b)` with `a, b > 0` and `α a = β b`,
  such that `α` on `(0, a)` does not meet `β` on `[0, 1]`. Then `α` on `[0, a]` followed by `β`
  on `[0, b]` backwards is a simple closed curve. The first coordinate is minimized on the
  compact set of crossings away from `(0, 0)`.

## Main results

* `TauCeti.exists_eq_injOn_Ico_of_not_injOn`: the first self-intersection of a locally injective
  curve on a compact interval.
* `TauCeti.exists_first_crossing`: the first crossing of two arcs with common endpoints.
-/

public section

open Filter Metric Set
open scoped Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- **First self-intersection of a locally injective curve.** A curve continuous on `[c, d]`,
injective on the trace on `[c, d]` of a neighbourhood of each parameter of `[c, d]` but not
injective on `[c, d]`, returns to an earlier point at a first time `b`: there is `a < b` with
`σ a = σ b`, and `σ` is injective on `[c, b)`. -/
theorem exists_eq_injOn_Ico_of_not_injOn [T2Space X] {σ : ℝ → X} {c d : ℝ}
    (hσ : ContinuousOn σ (Icc c d)) (hloc : ∀ t ∈ Icc c d, ∃ U ∈ 𝓝 t, InjOn σ (U ∩ Icc c d))
    (hnot : ¬ InjOn σ (Icc c d)) :
    ∃ a b, c ≤ a ∧ a < b ∧ b ≤ d ∧ σ a = σ b ∧ InjOn σ (Ico c b) := by
  choose! U hU hinj using hloc
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric_of_mem_nhds
    (isCompact_Icc (a := c) (b := d)) (c := fun i : Icc c d ↦ U i)
    (fun t ht ↦ ⟨⟨t, ht⟩, hU t ht⟩)
  have hnear {s t : ℝ} (hs : s ∈ Icc c d) (ht : t ∈ Icc c d) (hst : |t - s| < δ)
      (heq : σ s = σ t) : s = t := by
    obtain ⟨i, hi⟩ := hball s hs
    exact hinj i i.2 ⟨hi (mem_ball_self hδ), hs⟩ ⟨hi (by rwa [mem_ball, Real.dist_eq]), ht⟩ heq
  set K := (Icc c d ×ˢ Icc c d) ∩ {z : ℝ × ℝ | σ z.1 = σ z.2} ∩ {z | z.1 + δ ≤ z.2}
  have hmem {s t : ℝ} (hs : s ∈ Icc c d) (ht : t ∈ Icc c d) (hst : s < t) (heq : σ s = σ t) :
      (s, t) ∈ K := by
    have hδst : s + δ ≤ t := le_of_not_gt fun hlt ↦
      hst.ne (hnear hs ht (by rw [abs_of_pos (sub_pos.2 hst)]; linarith) heq)
    exact ⟨⟨⟨hs, ht⟩, heq⟩, hδst⟩
  have hKc : IsCompact K := (isCompact_Icc.prod_inter_setOf_eq isCompact_Icc hσ hσ).inter_right
    (isClosed_le (continuous_fst.add continuous_const) continuous_snd)
  have hne : K.Nonempty := by
    simp only [InjOn, not_forall] at hnot
    obtain ⟨s, hs, t, ht, heq, hst⟩ := hnot
    rcases lt_or_gt_of_ne hst with h | h
    · exact ⟨_, hmem hs ht h heq⟩
    · exact ⟨_, hmem ht hs h heq.symm⟩
  obtain ⟨⟨a, b⟩, ⟨⟨⟨ha, hb⟩, heq⟩, hlt⟩, hmin⟩ :=
    hKc.exists_isMinOn hne continuous_snd.continuousOn
  have hδb : a + δ ≤ b := hlt
  refine ⟨a, b, ha.1, by linarith, hb.2, heq, fun s hs t ht h ↦ ?_⟩
  have hsub : Ico c b ⊆ Icc c d := Ico_subset_Icc_self.trans (Icc_subset_Icc_right hb.2)
  have hkey {s t : ℝ} (hs : s ∈ Ico c b) (ht : t ∈ Ico c b) (hst : s < t) (h : σ s = σ t) :
      False :=
    ht.2.not_ge (hmin (hmem (hsub hs) (hsub ht) hst h))
  by_contra hst
  rcases lt_or_gt_of_ne hst with h' | h'
  · exact hkey hs ht h' h
  · exact hkey ht hs h' h.symm

/-- **First crossing of two arcs.** Let `α` and `β` be continuous injective arcs on `[0, 1]`
with the same initial point and the same final point, which do not meet for small positive
parameters. Then there are `a, b ∈ (0, 1]` with `α a = β b` such that `α` on `(0, a)` does not
meet `β` on `[0, 1]`. -/
theorem exists_first_crossing [T2Space X] {α β : ℝ → X}
    (hα : ContinuousOn α (Icc 0 1)) (hβ : ContinuousOn β (Icc 0 1))
    (hαi : InjOn α (Icc 0 1)) (hβi : InjOn β (Icc 0 1)) (h0 : α 0 = β 0) (h1 : α 1 = β 1)
    {ε : ℝ} (hε : 0 < ε) (hsep : ∀ a ∈ Ioo 0 ε, ∀ b ∈ Ioo 0 ε, α a ≠ β b) :
    ∃ a b, 0 < a ∧ a ≤ 1 ∧ 0 < b ∧ b ≤ 1 ∧ α a = β b ∧
      ∀ s ∈ Ioo 0 a, ∀ t ∈ Icc (0 : ℝ) 1, α s ≠ β t := by
  set η := min (ε / 2) 1
  have hη0 : 0 < η := lt_min (half_pos hε) one_pos
  have hηε : η < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  set K := (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ {z : ℝ × ℝ | α z.1 = β z.2} ∩
    {z | η ≤ max z.1 z.2}
  have hzero {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (heq : α s = β t) :
      s = 0 ↔ t = 0 := by
    constructor
    · rintro rfl
      exact (hβi ht (left_mem_Icc.2 zero_le_one) (heq.symm.trans h0))
    · rintro rfl
      exact hαi hs (left_mem_Icc.2 zero_le_one) (heq.trans h0.symm)
  have hmem {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hs0 : 0 < s)
      (heq : α s = β t) : (s, t) ∈ K := by
    have ht0 : 0 < t := lt_of_le_of_ne ht.1 fun h ↦ hs0.ne' ((hzero hs ht heq).2 h.symm)
    have hηst : η ≤ max s t := le_of_not_gt fun hlt ↦ hsep s
      ⟨hs0, (max_lt_iff.1 hlt).1.trans hηε⟩ t ⟨ht0, (max_lt_iff.1 hlt).2.trans hηε⟩ heq
    exact ⟨⟨⟨hs, ht⟩, heq⟩, hηst⟩
  have hKc : IsCompact K := (isCompact_Icc.prod_inter_setOf_eq isCompact_Icc hα hβ).inter_right
    (isClosed_le continuous_const (continuous_fst.max continuous_snd))
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.2 zero_le_one
  obtain ⟨⟨a, b⟩, ⟨⟨⟨ha, hb⟩, heq⟩, hmax⟩, hmin⟩ :=
    hKc.exists_isMinOn ⟨_, hmem h1mem h1mem one_pos h1⟩ continuous_fst.continuousOn
  replace ha : a ∈ Icc (0 : ℝ) 1 := ha
  replace hb : b ∈ Icc (0 : ℝ) 1 := hb
  replace heq : α a = β b := heq
  have hηab : η ≤ max a b := hmax
  have ha0 : 0 < a := by
    refine lt_of_le_of_ne ha.1 fun h ↦ ?_
    rw [← h, (hzero ha hb heq).1 h.symm, max_self] at hηab
    exact hη0.not_ge hηab
  have hb0 : 0 < b := lt_of_le_of_ne hb.1 fun h ↦ ha0.ne' ((hzero ha hb heq).2 h.symm)
  refine ⟨a, b, ha0, ha.2, hb0, hb.2, heq, fun s hs t ht hst ↦ ?_⟩
  exact hs.2.not_ge (hmin (hmem ⟨hs.1.le, hs.2.le.trans ha.2⟩ ht hs.1 hst))

end TauCeti

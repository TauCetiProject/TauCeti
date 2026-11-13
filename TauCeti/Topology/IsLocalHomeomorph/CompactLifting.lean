/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Topology.IsLocalHomeomorph.Lifting
public import Mathlib.Topology.Order.Compact

public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.Linarith

/-!
# Compact continuation of interval lifts

A curve lifts through a local homeomorphism on a closed real interval if every lifted
prefix has its endpoint in one fixed compact set. An accumulation point supplies a local
inverse at the supremum of the times admitting a lift. Neither space needs to be complete,
and the source need not be Hausdorff. Continuity of the curve is required only on the interval.

This is the continuation step for bounded lifts in a precompact exponential ball, used in
noncollapse-to-injectivity arguments.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Theorem 1.36.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set Filter Function
open scoped Topology

namespace IsLocalHomeomorph

/-- Compact confinement of every lifted prefix gives a lift on the full
closed interval. An accumulation point supplies the inverse branch at the
supremum time, even if the source itself is incomplete. -/
private theorem exists_lift_Icc_of_compact_prefixes_of_continuous
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : IsLocalHomeomorph f) {c : ℝ → Y} (hc : Continuous c)
    {a b : ℝ} (hab : a ≤ b) {q : X} (hq : f q = c a) {K : Set X} (hK : IsCompact K)
    (htrap : ∀ t ∈ Icc a b, ∀ l : ℝ → X,
      ContinuousOn l (Icc a t) → l a = q → EqOn (f ∘ l) c (Icc a t) → l t ∈ K) :
    ∃ l : ℝ → X, ContinuousOn l (Icc a b) ∧ l a = q ∧ EqOn (f ∘ l) c (Icc a b) := by
  classical
  let A : Set ℝ := {t | t ∈ Icc a b ∧
    ∃ l : ℝ → X, ContinuousOn l (Icc a t) ∧ l a = q ∧ EqOn (f ∘ l) c (Icc a t)}
  have hmono : ∀ t' ∈ A, ∀ t, a ≤ t → t ≤ t' → t ∈ A := by
    rintro t' ⟨ht', l, hl, h0, hproj⟩ t ht0 htt'
    exact ⟨⟨ht0, htt'.trans ht'.2⟩, l, hl.mono (Icc_subset_Icc le_rfl htt'), h0,
      hproj.mono (Icc_subset_Icc le_rfl htt')⟩
  have h0A : a ∈ A := by
    refine ⟨⟨le_rfl, hab⟩, fun _ ↦ q, continuousOn_const, rfl, ?_⟩
    intro t ht
    have : t = a := le_antisymm ht.2 ht.1
    simpa only [this, comp_apply] using hq
  have hne : A.Nonempty := ⟨a, h0A⟩
  have hbdd : BddAbove A := ⟨b, fun t ht ↦ ht.1.2⟩
  let T : ℝ := sSup A
  have hT0 : a ≤ T := le_csSup hbdd h0A
  have hT1 : T ≤ b := csSup_le hne (fun t ht ↦ ht.1.2)
  have hbefore : ∀ t, a ≤ t → t < T → t ∈ A := by
    intro t ht0 htT
    obtain ⟨t', ht'A, htt'⟩ := exists_lt_of_lt_csSup hne htT
    exact hmono t' ht'A t ht0 htt'.le
  have hTA : T ∈ A := by
    rcases eq_or_lt_of_le hT0 with hz | hpos
    · rwa [← hz]
    have hev : ∀ᶠ t in 𝓝[<] T, t ∈ Ico a T := by
      filter_upwards [Ioo_mem_nhdsLT hpos] with t ht using ⟨ht.1.le, ht.2⟩
    let x : ℝ → X := fun t ↦
      if ht : t ∈ Ico a T then (hbefore t ht.1 ht.2).2.choose t else q
    have hx (t : ℝ) (ht : t ∈ Ico a T) :
        x t = (hbefore t ht.1 ht.2).2.choose t := dite_eq_left ht
    have hxproj (t : ℝ) (ht : t ∈ Ico a T) : f (x t) = c t := by
      rw [hx t ht]
      exact (hbefore t ht.1 ht.2).2.choose_spec.2.2 ⟨ht.1, le_rfl⟩
    have hxK (t : ℝ) (ht : t ∈ Ico a T) : x t ∈ K := by
      rw [hx t ht]
      have hs := (hbefore t ht.1 ht.2).2.choose_spec
      exact htrap t ⟨ht.1, ht.2.le.trans hT1⟩ _ hs.1 hs.2.1 hs.2.2
    have hmapK : map x (𝓝[<] T) ≤ principal K := by
      rw [le_principal_iff, mem_map]
      filter_upwards [hev] with t ht using hxK t ht
    obtain ⟨r, _, hcl⟩ := hK.exists_clusterPt hmapK
    have hprojlim : Tendsto (fun t ↦ f (x t)) (𝓝[<] T) (𝓝 (c T)) := by
      apply ((hc.tendsto T).mono_left nhdsWithin_le_nhds).congr'
      filter_upwards [hev] with t ht using (hxproj t ht).symm
    have hclmap : ClusterPt (f r) (𝓝 (c T)) :=
      hcl.map hf.continuous.continuousAt (tendsto_map'_iff.mpr hprojlim)
    have hfr : f r = c T := eq_of_nhds_neBot hclmap.neBot
    obtain ⟨e, hr, he⟩ := hf r
    have htarget : c T ∈ e.target := by rw [← hfr, he]; exact e.map_source hr
    obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.mp
      (hc.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds htarget))
    have hfreq : ∃ᶠ t in 𝓝[<] T, x t ∈ e.source := by
      have h := hcl.frequently (e.open_source.mem_nhds hr)
      exact frequently_map.mp h
    have hclose : ∀ᶠ t in 𝓝[<] T, T - t < η := by
      filter_upwards [Ioo_mem_nhdsLT (show T - η < T by linarith)] with t ht
      linarith [ht.1]
    obtain ⟨t', hsrc, ht', hdist⟩ := (hfreq.and_eventually (hev.and hclose)).exists
    let l₁ : ℝ → X := (hbefore t' ht'.1 ht'.2).2.choose
    have hs₁ := (hbefore t' ht'.1 ht'.2).2.choose_spec
    let l₂ : ℝ → X := e.symm ∘ c
    have hmaps : MapsTo c (Icc t' T) e.target := by
      intro u hu
      apply hηsub
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hu.2)]
      linarith [hu.1]
    have hl₂ : ContinuousOn l₂ (Icc t' T) := e.continuousOn_symm.comp hc.continuousOn hmaps
    have hproj₂ : EqOn (f ∘ l₂) c (Icc t' T) := by
      intro u hu
      dsimp only [l₂, comp_apply]
      rw [he]
      exact e.right_inv (hmaps hu)
    have hjoin : l₂ t' = l₁ t' := by
      dsimp only [l₂, comp_apply]
      calc
        e.symm (c t') = x t' := by
          rw [← hxproj t' ht', he]
          exact e.left_inv hsrc
        _ = l₁ t' := hx t' ht'
    obtain ⟨l, hl, heq, hproj⟩ :=
      ContinuousOn.exists_lift_piecewise_Icc hs₁.1 hl₂ hjoin.symm hs₁.2.2 hproj₂
    exact ⟨⟨hT0, hT1⟩, l, hl, (heq ⟨le_rfl, ht'.1⟩).trans hs₁.2.1, hproj⟩
  have hT : T = b := by
    rcases eq_or_lt_of_le hT1 with h | h
    · exact h
    exfalso
    obtain ⟨_, l, hl, h0, hproj⟩ := hTA
    obtain ⟨δ, hδ, l', hl', heq, hproj'⟩ :=
      exists_extend_lift_Icc hf hc hT0 hl hproj
    have hnext : T < min (T + δ) b := lt_min (by linarith) h
    have hnextA : min (T + δ) b ∈ A := by
      refine ⟨⟨hT0.trans hnext.le, min_le_right _ _⟩, l',
        hl'.mono (Icc_subset_Icc le_rfl (min_le_left _ _)), ?_, ?_⟩
      · exact (heq ⟨le_rfl, hT0⟩).trans h0
      · intro t ht
        exact hproj' ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
    exact (not_lt_of_ge (le_csSup hbdd hnextA)) hnext
  obtain ⟨_, l, hl, h0, hproj⟩ := hTA
  rw [hT] at hl hproj
  exact ⟨l, hl, h0, hproj⟩

/-- A continuous curve on a closed interval admits a lift from `q` if the endpoints of
all its lifted prefixes stay in a fixed compact set. Compact confinement replaces any
completeness or properness assumption on the spaces or the local homeomorphism. -/
theorem exists_lift_Icc_of_compact_prefixes
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : IsLocalHomeomorph f) {c : ℝ → Y} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn c (Icc a b)) {q : X} (hq : f q = c a)
    {K : Set X} (hK : IsCompact K)
    (htrap : ∀ t ∈ Icc a b, ∀ l : ℝ → X,
      ContinuousOn l (Icc a t) → l a = q → EqOn (f ∘ l) c (Icc a t) → l t ∈ K) :
    ∃ l : ℝ → X, ContinuousOn l (Icc a b) ∧ l a = q ∧ EqOn (f ∘ l) c (Icc a b) := by
  let c' : ℝ → Y := IccExtend hab (fun t : Icc a b ↦ c t)
  have hc' : Continuous c' := hc.domRestrict.Icc_extend'
  have heq : EqOn c' c (Icc a b) := fun t ht ↦ IccExtend_of_mem hab _ ht
  obtain ⟨l, hl, h0, hproj⟩ := exists_lift_Icc_of_compact_prefixes_of_continuous hf hc' hab
    (hq.trans (heq (left_mem_Icc.mpr hab)).symm) hK (by
      intro t ht l hl h0 hp
      exact htrap t ht l hl h0 (hp.trans (heq.mono (Icc_subset_Icc le_rfl ht.2))))
  exact ⟨l, hl, h0, hproj.trans heq⟩

end IsLocalHomeomorph

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.GDelta.MetrizableSpace

/-!
# A Baire category separation criterion on the real line

Let an open preconnected set `T ⊆ ℝ` be covered by two sets `P` and `N`, each covered by countably
many closed sets disjoint from the other. If no point of a closed piece of `P` is followed, on
either side, by a segment contained in `N`, and symmetrically, then `T` misses `P` or misses `N`
(`TauCeti.disjoint_or_disjoint_of_isPreconnected_of_closed_covers`). The proof applies the Baire
category theorem to the `G_δ` set of points of `T` in the closures of both `P` and `N`, which is
completely metrizable: one closed piece has nonempty interior there, and from a point of that
interior one walks along the line to the last point of the closure of `P`.

## Main results

* `TauCeti.disjoint_or_disjoint_of_isPreconnected_of_closed_covers`: the separation criterion.
-/

public section

open Set Metric
open scoped Pointwise

namespace TauCeti

/-- If `t₀ < o`, `t₀` lies in the closure of `P` but `o` does not, and `[t₀, o]` is covered by
`P` and `N`, then some point `a ∈ [t₀, o]` lies in both closures, and a segment to the right of `a`
lies in `N`. -/
private theorem exists_mem_forall_add_mem_of_lt (P N g : Set ℝ) {t₀ o : ℝ} (hto : t₀ < o)
    (ht₀ : t₀ ∈ closure P) (ho : o ∉ closure P) (hcover : Icc t₀ o ⊆ P ∪ N)
    (hg : ∀ t ∈ Icc t₀ o, t ∈ closure P → t ∈ closure N → t ∈ g) :
    ∃ a ∈ g, ∃ δ > 0, ∀ τ ∈ Ioo 0 δ, a + τ ∈ N := by
  set K := closure P ∩ Icc t₀ o
  have hKbdd : BddAbove K := ⟨o, fun t ht => ht.2.2⟩
  have haK : sSup K ∈ K := (isClosed_closure.inter isClosed_Icc).csSup_mem
    ⟨t₀, ht₀, left_mem_Icc.2 hto.le⟩ hKbdd
  have hao : sSup K < o := lt_of_le_of_ne haK.2.2 fun h => ho (h ▸ haK.1)
  have hN : Ioc (sSup K) o ⊆ N := fun t ht => by
    have htI : t ∈ Icc t₀ o := ⟨haK.2.1.trans ht.1.le, ht.2⟩
    have htP : t ∉ closure P := fun h => (not_le.2 ht.1) (le_csSup hKbdd ⟨h, htI⟩)
    exact (hcover htI).resolve_left fun h => htP (subset_closure h)
  refine ⟨sSup K, hg _ haK.2 haK.1 ?_, o - sSup K, sub_pos.2 hao,
    fun τ hτ => hN ⟨by linarith [hτ.1], by linarith [hτ.2]⟩⟩
  have : sSup K ∈ closure (Ioo (sSup K) o) := by
    rw [closure_Ioo hao.ne]
    exact left_mem_Icc.2 hao.le
  exact closure_mono (Ioo_subset_Ioc_self.trans hN) this

/-- The mirror image of `exists_mem_forall_add_mem_of_lt`. -/
private theorem exists_mem_forall_sub_mem_of_lt (P N g : Set ℝ) {t₀ o : ℝ} (hot : o < t₀)
    (ht₀ : t₀ ∈ closure P) (ho : o ∉ closure P) (hcover : Icc o t₀ ⊆ P ∪ N)
    (hg : ∀ t ∈ Icc o t₀, t ∈ closure P → t ∈ closure N → t ∈ g) :
    ∃ a ∈ g, ∃ δ > 0, ∀ τ ∈ Ioo 0 δ, a + -1 * τ ∈ N := by
  obtain ⟨a, ha, δ, hδ, h⟩ := exists_mem_forall_add_mem_of_lt (-P) (-N) (-g) (neg_lt_neg hot)
    (by rwa [← neg_closure, Set.mem_neg, neg_neg]) (by rwa [← neg_closure, Set.mem_neg, neg_neg])
    (fun t ht => by
      simpa using hcover (show -t ∈ Icc o t₀ from ⟨by linarith [ht.2], by linarith [ht.1]⟩))
    (fun t ht h1 h2 => by
      rw [← neg_closure] at h1 h2
      exact hg (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ h1 h2)
  refine ⟨-a, ha, δ, hδ, fun τ hτ => ?_⟩
  have := h τ hτ
  rw [Set.mem_neg] at this
  convert this using 1
  ring

/-- Let `P` and `N` cover an open set `T`, and let `W` be open. If every point of `T ∩ W` in the
closures of both `P` and `N` lies in a set `g` disjoint from `N`, and there is such a point, then
some point of `g` is followed, on one side, by a segment contained in `N`. -/
private theorem exists_mem_forall_add_mul_mem (T W P N g : Set ℝ) (hT : IsOpen T) (hW : IsOpen W)
    (hTPN : T ⊆ P ∪ N) (hgN : Disjoint g N)
    (hZ : T ∩ (closure P ∩ closure N) ∩ W ⊆ g) {t₀ : ℝ}
    (ht₀ : t₀ ∈ T ∩ (closure P ∩ closure N) ∩ W) :
    ∃ a ∈ g, ∃ δ > 0, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ τ ∈ Ioo 0 δ, a + σ * τ ∈ N := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hT.inter hW) t₀ ⟨ht₀.1.1, ht₀.2⟩
  obtain ⟨o, hoN, hdo⟩ := Metric.mem_closure_iff.1 ht₀.1.2.2 ε hε
  have hg' (t : ℝ) (ht : t ∈ ball t₀ ε) (h1 : t ∈ closure P) (h2 : t ∈ closure N) : t ∈ g :=
    hZ ⟨⟨(hball ht).1, h1, h2⟩, (hball ht).2⟩
  have hoP : o ∉ closure P := fun h =>
    hgN.ne_of_mem (hg' o (by rwa [mem_ball, dist_comm]) h (subset_closure hoN)) hoN rfl
  have hoball : o ∈ ball t₀ ε := by rwa [mem_ball, dist_comm]
  have hIcc {u v : ℝ} (hu : u ∈ ball t₀ ε) (hv : v ∈ ball t₀ ε) : Icc u v ⊆ ball t₀ ε :=
    (convex_ball t₀ ε).ordConnected.out hu hv
  have hcov (t : ℝ) (ht : t ∈ ball t₀ ε) : t ∈ P ∪ N := hTPN (hball ht).1
  have ht₀g : t₀ ∈ g := hZ ht₀
  rcases lt_trichotomy t₀ o with h | rfl | h
  · obtain ⟨a, ha, δ, hδ, hN⟩ := exists_mem_forall_add_mem_of_lt P N g h ht₀.1.2.1 hoP
      (fun t ht => hcov t (hIcc (mem_ball_self hε) hoball ht))
      (fun t ht => hg' t (hIcc (mem_ball_self hε) hoball ht))
    exact ⟨a, ha, δ, hδ, 1, Or.inl rfl, by simpa using hN⟩
  · exact absurd hoN (hgN.notMem_of_mem_left ht₀g)
  · obtain ⟨a, ha, δ, hδ, hN⟩ := exists_mem_forall_sub_mem_of_lt P N g h ht₀.1.2.1 hoP
      (fun t ht => hcov t (hIcc hoball (mem_ball_self hε) ht))
      (fun t ht => hg' t (hIcc hoball (mem_ball_self hε) ht))
    exact ⟨a, ha, δ, hδ, -1, Or.inr rfl, hN⟩

/-- **A Baire category argument on a line.** Let an open preconnected set `T ⊆ ℝ` be covered by
sets `P` and `N`, and cover `P` and `N` by countably many closed sets `gP k`, disjoint from `N`,
and `gN k`, disjoint from `P`. If no point of a `gP k` is followed on either side by a segment in
`N`, and no point of a `gN k` by a segment in `P`, then `T` misses `P` or misses `N`. -/
theorem disjoint_or_disjoint_of_isPreconnected_of_closed_covers {T P N : Set ℝ} (hT : IsOpen T)
    (hTc : IsPreconnected T) (hTPN : T ⊆ P ∪ N) (gP gN : ℕ → Set ℝ)
    (hgP : ∀ k, IsClosed (gP k)) (hgN : ∀ k, IsClosed (gN k)) (hPg : P ⊆ ⋃ k, gP k)
    (hNg : N ⊆ ⋃ k, gN k) (hdP : ∀ k, Disjoint (gP k) N) (hdN : ∀ k, Disjoint (gN k) P)
    (hbP : ∀ k a δ σ, a ∈ gP k → 0 < δ → (σ = 1 ∨ σ = -1) → ¬ ∀ τ ∈ Ioo 0 δ, a + σ * τ ∈ N)
    (hbN : ∀ k a δ σ, a ∈ gN k → 0 < δ → (σ = 1 ∨ σ = -1) → ¬ ∀ τ ∈ Ioo 0 δ, a + σ * τ ∈ P) :
    Disjoint T P ∨ Disjoint T N := by
  by_contra! h
  obtain ⟨⟨p, hpT, hpP⟩, ⟨q, hqT, hqN⟩⟩ :=
    And.intro (not_disjoint_iff.1 h.1) (not_disjoint_iff.1 h.2)
  set Z := T ∩ (closure P ∩ closure N)
  obtain ⟨z₀, hz₀⟩ : Z.Nonempty := isPreconnected_closed_iff.1 hTc _ _ isClosed_closure
    isClosed_closure (hTPN.trans (union_subset_union subset_closure subset_closure))
    ⟨p, hpT, subset_closure hpP⟩ ⟨q, hqT, subset_closure hqN⟩
  have hZG : IsGδ Z := hT.isGδ.inter (isClosed_closure.inter isClosed_closure).isGδ
  have := hZG.isCompletelyMetrizableSpace
  have : Nonempty Z := ⟨⟨z₀, hz₀⟩⟩
  have hfc : ∀ i, IsClosed (Sum.elim (fun k => ((↑) : Z → ℝ) ⁻¹' gP k)
      (fun k => ((↑) : Z → ℝ) ⁻¹' gN k) i) := by
    rintro (k | k)
    exacts [(hgP k).preimage continuous_subtypeVal, (hgN k).preimage continuous_subtypeVal]
  have hfU : ⋃ i, Sum.elim (fun k => ((↑) : Z → ℝ) ⁻¹' gP k)
      (fun k => ((↑) : Z → ℝ) ⁻¹' gN k) i = univ := by
    refine eq_univ_of_forall fun z => mem_iUnion.2 ?_
    rcases hTPN z.property.1 with hz | hz
    · obtain ⟨k, hk⟩ := mem_iUnion.1 (hPg hz)
      exact ⟨Sum.inl k, hk⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.1 (hNg hz)
      exact ⟨Sum.inr k, hk⟩
  obtain ⟨i, z, hz⟩ := nonempty_interior_of_iUnion_of_closed hfc hfU
  obtain ⟨V, hVf, hVo, hzV⟩ := mem_interior.1 hz
  obtain ⟨W, hWo, rfl⟩ := isOpen_induced_iff.1 hVo
  rcases i with k | k
  · obtain ⟨a, ha, δ, hδ, σ, hσ, haN⟩ := exists_mem_forall_add_mul_mem T W P N (gP k) hT hWo
      hTPN (hdP k) (fun t ht => hVf (show (⟨t, ht.1⟩ : Z) ∈ (↑) ⁻¹' W from ht.2)) ⟨z.property, hzV⟩
    exact hbP k a δ σ ha hδ hσ haN
  · obtain ⟨a, ha, δ, hδ, σ, hσ, haP⟩ := exists_mem_forall_add_mul_mem T W N P (gN k) hT hWo
      (by rwa [union_comm]) (hdN k)
      (fun t ht => hVf (show (⟨t, ht.1.1, ht.1.2.2, ht.1.2.1⟩ : Z) ∈ (↑) ⁻¹' W from ht.2))
      ⟨⟨z.property.1, z.property.2.2, z.property.2.1⟩, hzV⟩
    exact hbN k a δ σ ha hδ hσ haP

end TauCeti

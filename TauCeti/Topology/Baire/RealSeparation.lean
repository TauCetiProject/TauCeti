/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.GDelta.MetrizableSpace
import TauCeti.Topology.Order.IntermediateValue

/-!
# A Baire category separation criterion on the real line

Let an open preconnected set `T ⊆ ℝ` be covered by two sets `P` and `N`, each covered by countably
many closed sets disjoint from the other. If no point of a closed piece of `P` is followed, on
either side, by a segment contained in `N`, and symmetrically, then `T` misses `P` or misses `N`
(`TauCeti.disjoint_or_disjoint_of_isPreconnected_of_closed_covers`). The proof applies the Baire
category theorem to the `G_δ` set of points of `T` in the closures of both `P` and `N`, which is
completely metrizable: one closed piece has nonempty interior there, and from a point of that
interior one walks along the line to a point of the closures of `P` and `N` followed by a segment
in `N` (`TauCeti.exists_mem_closure_inter_closure_Ioc_subset`).

## Main results

* `TauCeti.disjoint_or_disjoint_of_isPreconnected_of_closed_covers`: the separation criterion.
-/

public section

open Set Metric

namespace TauCeti

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
  · obtain ⟨a, ha, haPN, hN⟩ := exists_mem_closure_inter_closure_Ioc_subset h ht₀.1.2.1 hoP
      (fun t ht => hcov t (hIcc (mem_ball_self hε) hoball ht))
    refine ⟨a, hg' a (hIcc (mem_ball_self hε) hoball (Ico_subset_Icc_self ha)) haPN.1 haPN.2,
      o - a, sub_pos.2 ha.2, 1, Or.inl rfl, fun τ hτ => hN ⟨?_, ?_⟩⟩ <;> linarith [hτ.1, hτ.2]
  · exact absurd hoN (hgN.notMem_of_mem_left ht₀g)
  · obtain ⟨a, ha, haPN, hN⟩ := exists_mem_closure_inter_closure_Ico_subset h ht₀.1.2.1 hoP
      (fun t ht => hcov t (hIcc hoball (mem_ball_self hε) ht))
    refine ⟨a, hg' a (hIcc hoball (mem_ball_self hε) (Ioc_subset_Icc_self ha)) haPN.1 haPN.2,
      a - o, sub_pos.2 ha.1, -1, Or.inr rfl, fun τ hτ => hN ⟨?_, ?_⟩⟩ <;> linarith [hτ.1, hτ.2]

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
  -- the closed pieces `gP k` and `gN k`, as one family indexed by `ℕ ⊕ ℕ`, cover `Z`
  have hfc (i : ℕ ⊕ ℕ) : IsClosed (((↑) : Z → ℝ) ⁻¹' Sum.elim gP gN i) := by
    rcases i with k | k
    exacts [(hgP k).preimage continuous_subtypeVal, (hgN k).preimage continuous_subtypeVal]
  have hfU : ⋃ i, ((↑) : Z → ℝ) ⁻¹' Sum.elim gP gN i = univ := by
    refine eq_univ_of_forall fun z => mem_iUnion.2 ?_
    rcases hTPN z.property.1 with hz | hz
    · obtain ⟨k, hk⟩ := mem_iUnion.1 (hPg hz)
      exact ⟨Sum.inl k, hk⟩
    · obtain ⟨k, hk⟩ := mem_iUnion.1 (hNg hz)
      exact ⟨Sum.inr k, hk⟩
  obtain ⟨i, z, hz⟩ := nonempty_interior_of_iUnion_of_closed hfc hfU
  obtain ⟨V, hVf, hVo, hzV⟩ := mem_interior.1 hz
  obtain ⟨W, hWo, rfl⟩ := isOpen_induced_iff.1 hVo
  -- the points of `Z ∩ W` all lie in the piece `Sum.elim gP gN i`
  have hZW : T ∩ (closure P ∩ closure N) ∩ W ⊆ Sum.elim gP gN i := fun t ht => by
    have h := hVf (a := ⟨t, ht.1⟩) (mem_preimage.2 ht.2)
    rwa [mem_preimage] at h
  rcases i with k | k
  · rw [Sum.elim_inl] at hZW
    obtain ⟨a, ha, δ, hδ, σ, hσ, haN⟩ := exists_mem_forall_add_mul_mem T W P N (gP k) hT hWo
      hTPN (hdP k) hZW ⟨z.property, hzV⟩
    exact hbP k a δ σ ha hδ hσ haN
  · rw [Sum.elim_inr, inter_comm (closure P)] at hZW
    obtain ⟨a, ha, δ, hδ, σ, hσ, haP⟩ := exists_mem_forall_add_mul_mem T W N P (gN k) hT hWo
      (by rwa [union_comm]) (hdN k) hZW
      ⟨⟨z.property.1, (inter_comm (closure P) (closure N)).subset z.property.2⟩, hzV⟩
    exact hbN k a δ σ ha hδ hσ haP

end TauCeti

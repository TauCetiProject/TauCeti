/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Trivializations of bundle maps from trivializations of the model fibre map

Let `p₁ : Z₁ → B` and `p₂ : Z₂ → B` be maps over a base `B`, trivialized by charts
`e₁ : Trivialization F₁ p₁` and `e₂ : Trivialization F₂ p₂`, and let `q : Z₁ → Z₂` be a continuous
map over `B` (`p₂ ∘ q = p₁`) that reads in `(e₁, e₂)` over `e₁.baseSet ∩ e₂.baseSet` as a fixed map
`g : F₁ → F₂` of the model fibres. Then any chart `t : Trivialization F g` of `g` lifts to a chart
`Bundle.Trivialization.ofFiberMap` of `q : Z₁ → Z₂` with fibre `F`, over the open subset of `Z₂`
lying over `e₁.baseSet ∩ e₂.baseSet` whose fibre coordinate in `e₂` belongs to `t.baseSet`.

Consequently, when `p₁` and `p₂` admit compatible local trivializations around every point of `B`
and the model map `g : F₁ → F₂` is locally trivial with fibre `F`, the map `q : Z₁ → Z₂` is locally
trivial with fibre `F` (`TauCeti.exists_trivialization_of_fiberMap`). For instance, projecting an
orthonormal `(k + 1)`-frame of a Riemannian vector bundle to its first vector in the unit sphere
bundle is locally modelled on the Stiefel projection `V_{k+1}(ℝ^{n+1}) → Sⁿ`, so local triviality
of the latter yields local triviality of the vertical frame fibration over the sphere bundle.

## Main declarations

* `Bundle.Trivialization.ofFiberMap`: lifts a chart of the model fibre map `g : F₁ → F₂` through
  compatible charts of `p₁ : Z₁ → B` and `p₂ : Z₂ → B` to a chart of `q : Z₁ → Z₂`.
* `TauCeti.exists_trivialization_of_fiberMap`: local triviality of `q : Z₁ → Z₂` from compatible
  charts over `B` and local triviality of the model fibre map `g : F₁ → F₂`.

## References

* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §9 (factorings of
  bundle projections).
-/

public section

open Bundle Set

namespace Bundle.Trivialization

variable {B F₁ F₂ F Z₁ Z₂ : Type*} [TopologicalSpace B] [TopologicalSpace F₁]
  [TopologicalSpace F₂] [TopologicalSpace F] [TopologicalSpace Z₁] [TopologicalSpace Z₂]
  {p₁ : Z₁ → B} {p₂ : Z₂ → B} (e₁ : Trivialization F₁ p₁) (e₂ : Trivialization F₂ p₂)
  {q : Z₁ → Z₂} (hq : Continuous q) (hpq : ∀ z, p₂ (q z) = p₁ z)
  {g : F₁ → F₂} (heq : ∀ z, p₁ z ∈ e₁.baseSet → p₁ z ∈ e₂.baseSet → (e₂ (q z)).2 = g (e₁ z).2)
  (t : Trivialization F g)

/-- The base set of `Bundle.Trivialization.ofFiberMap`: points of `e₂.source` lying over
`e₁.baseSet ∩ e₂.baseSet` whose fibre coordinate in `e₂` lies in `t.baseSet`. -/
private def fiberMapBaseSet : Set Z₂ :=
  e₂.source ∩ e₂ ⁻¹' ((e₁.baseSet ∩ e₂.baseSet) ×ˢ t.baseSet)

private theorem isOpen_fiberMapBaseSet : IsOpen (fiberMapBaseSet e₁ e₂ t) :=
  e₂.continuousOn_toFun.isOpen_inter_preimage e₂.open_source
    ((e₁.open_baseSet.inter e₂.open_baseSet).prod t.open_baseSet)

private theorem mem_fiberMapBaseSet_iff {y : Z₂} :
    y ∈ fiberMapBaseSet e₁ e₂ t ↔
      p₂ y ∈ e₁.baseSet ∧ p₂ y ∈ e₂.baseSet ∧ (e₂ y).2 ∈ t.baseSet := by
  refine ⟨fun ⟨hys, hy⟩ ↦ ?_, fun ⟨h₁, h₂, ht⟩ ↦ ?_⟩
  · rw [mem_preimage, mem_prod, e₂.coe_fst hys] at hy
    exact ⟨hy.1.1, hy.1.2, hy.2⟩
  · have hys : y ∈ e₂.source := e₂.mem_source.2 h₂
    exact ⟨hys, by rw [mem_preimage, mem_prod, e₂.coe_fst hys]; exact ⟨⟨h₁, h₂⟩, ht⟩⟩

include hpq heq in
/-- Applying `q` to the candidate inverse of `ofFiberMap` recovers the point of `Z₂`. -/
private theorem fiberMap_proj_symm {y : Z₂} (hy : y ∈ fiberMapBaseSet e₁ e₂ t) (v : F) :
    q (e₁.toOpenPartialHomeomorph.symm
      ((e₂ y).1, t.toOpenPartialHomeomorph.symm ((e₂ y).2, v))) = y := by
  obtain ⟨h₁, h₂, ht⟩ := (mem_fiberMapBaseSet_iff e₁ e₂ t).1 hy
  have hys : y ∈ e₂.source := hy.1
  have hb : (e₂ y).1 = p₂ y := e₂.coe_fst hys
  have hb₁ : (e₂ y).1 ∈ e₁.baseSet := hb.symm ▸ h₁
  have hb₂ : (e₂ y).1 ∈ e₂.baseSet := hb.symm ▸ h₂
  set w := t.toOpenPartialHomeomorph.symm ((e₂ y).2, v)
  set z := e₁.toOpenPartialHomeomorph.symm ((e₂ y).1, w)
  have hp₁z : p₁ z = (e₂ y).1 := e₁.proj_symm_apply' hb₁
  have he₁z : e₁ z = ((e₂ y).1, w) := e₁.right_inv (e₁.mem_target.2 hb₁)
  have hgw : g w = (e₂ y).2 := t.proj_symm_apply' ht
  have hqz_src : q z ∈ e₂.source := e₂.mem_source.2 (by rw [hpq, hp₁z]; exact hb₂)
  refine e₂.injOn hqz_src hys (Prod.ext ?_ ?_)
  · simp only [coe_coe]
    rw [e₂.coe_fst hqz_src, hpq, hp₁z]
  · simp only [coe_coe]
    rw [heq z (hp₁z ▸ hb₁) (hp₁z ▸ hb₂), he₁z, hgw]

/-- **Chart of a bundle map from a chart of the model fibre map.** Given charts `e₁` of
`p₁ : Z₁ → B` and `e₂` of `p₂ : Z₂ → B`, a continuous map `q : Z₁ → Z₂` over `B` whose fibre
action in `(e₁, e₂)` over `e₁.baseSet ∩ e₂.baseSet` is `g : F₁ → F₂`, and a chart `t` of `g` with
fibre `F`, this is the induced chart of `q` with fibre `F`. Over its source it sends `z` to
`(q z, (t (e₁ z).2).2)`, with inverse `(y, v) ↦ e₁⁻¹ (p₂ y, t⁻¹ ((e₂ y).2, v))`. -/
noncomputable def ofFiberMap : Trivialization F q where
  toFun z := (q z, (t (e₁ z).2).2)
  invFun p := e₁.toOpenPartialHomeomorph.symm
    ((e₂ p.1).1, t.toOpenPartialHomeomorph.symm ((e₂ p.1).2, p.2))
  source := q ⁻¹' fiberMapBaseSet e₁ e₂ t
  target := fiberMapBaseSet e₁ e₂ t ×ˢ univ
  map_source' _ hz := ⟨hz, mem_univ _⟩
  map_target' p hp := by
    rw [mem_preimage, fiberMap_proj_symm e₁ e₂ hpq heq t hp.1]
    exact hp.1
  left_inv' z hz := by
    obtain ⟨h₁, h₂, ht⟩ := (mem_fiberMapBaseSet_iff e₁ e₂ t).1 hz
    have hqz_src : q z ∈ e₂.source := hz.1
    rw [hpq] at h₁ h₂
    have hz_src : z ∈ e₁.source := e₁.mem_source.2 h₁
    have hw_src : (e₁ z).2 ∈ t.source := t.mem_source.2 (by rwa [← heq z h₁ h₂])
    have htw : (e₂ (q z)).2 = (t (e₁ z).2).1 := (heq z h₁ h₂).trans (t.coe_fst hw_src).symm
    have htsymm : t.toOpenPartialHomeomorph.symm ((e₂ (q z)).2, (t (e₁ z).2).2) = (e₁ z).2 := by
      rw [htw, Prod.mk.eta]
      exact t.left_inv hw_src
    have he₂fst : (e₂ (q z)).1 = (e₁ z).1 :=
      (e₂.coe_fst hqz_src).trans ((hpq z).trans (e₁.coe_fst hz_src).symm)
    rw [htsymm, he₂fst, Prod.mk.eta]
    exact e₁.left_inv hz_src
  right_inv' p hp := by
    obtain ⟨h₁, -, ht⟩ := (mem_fiberMapBaseSet_iff e₁ e₂ t).1 hp.1
    have hb : (e₂ p.1).1 = p₂ p.1 := e₂.coe_fst hp.1.1
    have hb₁ : (e₂ p.1).1 ∈ e₁.baseSet := hb.symm ▸ h₁
    set w := t.toOpenPartialHomeomorph.symm ((e₂ p.1).2, p.2)
    have he₁z : e₁ (e₁.toOpenPartialHomeomorph.symm ((e₂ p.1).1, w)) = ((e₂ p.1).1, w) :=
      e₁.right_inv (e₁.mem_target.2 hb₁)
    have htw : t w = ((e₂ p.1).2, p.2) := t.right_inv (t.mem_target.2 ht)
    refine Prod.ext (fiberMap_proj_symm e₁ e₂ hpq heq t hp.1 p.2) ?_
    rw [he₁z, htw]
  open_source := (isOpen_fiberMapBaseSet e₁ e₂ t).preimage hq
  open_target := (isOpen_fiberMapBaseSet e₁ e₂ t).prod isOpen_univ
  continuousOn_toFun := by
    have he₁ : ContinuousOn (fun z ↦ (e₁ z).2) (q ⁻¹' fiberMapBaseSet e₁ e₂ t) :=
      continuous_snd.comp_continuousOn (e₁.continuousOn_toFun.mono fun z hz ↦ by
        obtain ⟨h₁, -, -⟩ := (mem_fiberMapBaseSet_iff e₁ e₂ t).1 hz
        exact e₁.mem_source.2 (hpq z ▸ h₁))
    refine hq.continuousOn.prodMk (continuous_snd.comp_continuousOn
      (t.continuousOn_toFun.comp he₁ fun z hz ↦ ?_))
    obtain ⟨h₁, h₂, ht⟩ := (mem_fiberMapBaseSet_iff e₁ e₂ t).1 hz
    rw [hpq] at h₁ h₂
    exact t.mem_source.2 (by rwa [← heq z h₁ h₂])
  continuousOn_invFun := by
    have he₂ : ContinuousOn (fun p : Z₂ × F ↦ e₂ p.1) (fiberMapBaseSet e₁ e₂ t ×ˢ univ) :=
      e₂.continuousOn_toFun.comp continuousOn_fst fun _ hp ↦ hp.1.1
    have ht_symm : ContinuousOn
        (fun p : Z₂ × F ↦ t.toOpenPartialHomeomorph.symm ((e₂ p.1).2, p.2))
        (fiberMapBaseSet e₁ e₂ t ×ˢ univ) :=
      t.toOpenPartialHomeomorph.continuousOn_symm.comp (he₂.snd.prodMk continuousOn_snd)
        fun _ hp ↦ t.mem_target.2 hp.1.2.2
    exact e₁.toOpenPartialHomeomorph.continuousOn_symm.comp (he₂.fst.prodMk ht_symm)
      fun _ hp ↦ e₁.mem_target.2 hp.1.2.1.1
  baseSet := fiberMapBaseSet e₁ e₂ t
  open_baseSet := isOpen_fiberMapBaseSet e₁ e₂ t
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- Membership in the base set of `Bundle.Trivialization.ofFiberMap`. -/
@[simp]
theorem mem_ofFiberMap_baseSet {y : Z₂} :
    y ∈ (ofFiberMap e₁ e₂ hq hpq heq t).baseSet ↔
      p₂ y ∈ e₁.baseSet ∧ p₂ y ∈ e₂.baseSet ∧ (e₂ y).2 ∈ t.baseSet :=
  mem_fiberMapBaseSet_iff e₁ e₂ t

/-- Forward map of `Bundle.Trivialization.ofFiberMap`. -/
@[simp]
theorem ofFiberMap_apply (z : Z₁) :
    ofFiberMap e₁ e₂ hq hpq heq t z = (q z, (t (e₁ z).2).2) := by
  rw [ofFiberMap]
  -- After unfolding `ofFiberMap`, `toFun z` is `(q z, (t (e₁ z).2).2)`.
  rfl

/-- Inverse map of `Bundle.Trivialization.ofFiberMap`. -/
@[simp]
theorem ofFiberMap_symm_apply (p : Z₂ × F) :
    (ofFiberMap e₁ e₂ hq hpq heq t).toOpenPartialHomeomorph.symm p =
      e₁.toOpenPartialHomeomorph.symm
        ((e₂ p.1).1, t.toOpenPartialHomeomorph.symm ((e₂ p.1).2, p.2)) := by
  rw [ofFiberMap]
  -- After unfolding `ofFiberMap`, `invFun p` applies `t⁻¹` then `e₁⁻¹`.
  rfl

end Bundle.Trivialization

namespace TauCeti

/-- **Local triviality of a bundle map from local triviality of its model fibre map.** Let
`q : Z₁ → Z₂` be a continuous map over `B` (`p₂ ∘ q = p₁`). If around every point of `B` there are
charts `e₁` of `p₁` and `e₂` of `p₂` in which `q` reads on fibres as a locally trivial map
`g : F₁ → F₂` with fibre `F`, then `q` is locally trivial with fibre `F`. -/
theorem exists_trivialization_of_fiberMap {B F₁ F₂ F Z₁ Z₂ : Type*} [TopologicalSpace B]
    [TopologicalSpace F₁] [TopologicalSpace F₂] [TopologicalSpace F]
    [TopologicalSpace Z₁] [TopologicalSpace Z₂] {p₁ : Z₁ → B} {p₂ : Z₂ → B}
    {q : Z₁ → Z₂} (hq : Continuous q) (hpq : ∀ z, p₂ (q z) = p₁ z) {g : F₁ → F₂}
    (hB : ∀ b : B, ∃ (e₁ : Trivialization F₁ p₁) (e₂ : Trivialization F₂ p₂),
      b ∈ e₁.baseSet ∧ b ∈ e₂.baseSet ∧
        ∀ z, p₁ z ∈ e₁.baseSet → p₁ z ∈ e₂.baseSet → (e₂ (q z)).2 = g (e₁ z).2)
    (hg : ∀ w : F₂, ∃ t : Trivialization F g, w ∈ t.baseSet) (y : Z₂) :
    ∃ e : Trivialization F q, y ∈ e.baseSet := by
  obtain ⟨e₁, e₂, hb₁, hb₂, heq⟩ := hB (p₂ y)
  obtain ⟨t, ht⟩ := hg (e₂ y).2
  exact ⟨Bundle.Trivialization.ofFiberMap e₁ e₂ hq hpq heq t,
    (Bundle.Trivialization.mem_ofFiberMap_baseSet e₁ e₂ hq hpq heq t).2 ⟨hb₁, hb₂, ht⟩⟩

end TauCeti

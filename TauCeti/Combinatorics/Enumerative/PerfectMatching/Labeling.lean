/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.PerfectMatching

/-!
# Perfect matchings as two-to-one labellings

A two-to-one map `M : α → β` from a type of points to a type of labels pairs up the
points: each label is carried by exactly two points. This is the form in which matchings appear
in bordered Floer homology, as the matching `M : a → [2k]` of a pointed matched circle. Its
*partner* perfect matching exchanges the two points carrying each label.

## Main definitions

* `TauCeti.PerfectMatching.Labeling α β`: a labelled perfect matching, a two-to-one map from a
  type `α` of points to a type `β` of labels.
* `TauCeti.PerfectMatching.Labeling.partner`: the perfect matching exchanging the two points of
  each matched pair.
* `TauCeti.PerfectMatching.Labeling.ofPartner`: the labelled perfect matching with given labels
  and a given partner map.
* `TauCeti.PerfectMatching.Labeling.comp`: the pullback of a labelled perfect matching along a
  bijection of the points.

## Main results

* `TauCeti.PerfectMatching.Labeling.partner_eq_iff`: the partner of a point is the other point
  with its label.
* `TauCeti.PerfectMatching.Labeling.apply_eq_apply_iff`: two points have the same label exactly
  when they are equal or partners.
* `TauCeti.PerfectMatching.Labeling.partner_comp`: the partner of a pullback is the transported
  partner.
-/

public section

open Finset Equiv

namespace TauCeti

/-- A *labelled perfect matching* of a type `α` of points by a type `β` of labels: a map `α → β`
each of whose fibres has exactly two elements, so that it pairs up the points, each pair carrying
its own label. Equivalently, a perfect matching of `α` together with a bijection between its pairs
and `β`. This is the matching `M : a → [2k]` of a pointed matched circle. -/
structure PerfectMatching.Labeling (α β : Type*) where
  /-- The label of each point. -/
  toFun : α → β
  /-- Each label is carried by exactly two points. -/
  ncard_preimage_singleton_eq_two' : ∀ b, (toFun ⁻¹' {b}).ncard = 2

namespace PerfectMatching.Labeling

variable {α β γ : Type*}

instance : FunLike (Labeling α β) α β where
  coe M := M.toFun
  coe_injective M N h := by cases M; cases N; congr

@[simp]
theorem toFun_eq_coe (M : Labeling α β) : M.toFun = ⇑M := rfl

@[ext]
theorem ext {M N : Labeling α β} (h : ∀ a, M a = N a) : M = N :=
  DFunLike.ext _ _ h

variable (M : Labeling α β)

theorem ncard_preimage_singleton_eq_two (b : β) : (M ⁻¹' {b}).ncard = 2 :=
  M.ncard_preimage_singleton_eq_two' b

theorem card_filter_eq_two [Fintype α] [DecidableEq β] (b : β) : #{a | M a = b} = 2 := by
  rw [← Set.ncard_coe_finset, coe_filter_univ]
  exact M.ncard_preimage_singleton_eq_two b

/-- A type admitting a labelled perfect matching with a point has at least two points. -/
theorem two_le_card [Fintype α] (M : Labeling α β) (a : α) : 2 ≤ Fintype.card α := by
  classical
  rw [← M.card_filter_eq_two (M a)]
  exact card_le_univ _

/-- A type admitting a labelled perfect matching with a point is nontrivial. -/
theorem nontrivial (M : Labeling α β) (a : α) : Nontrivial α :=
  have ⟨x, y, hxy, _⟩ := Set.ncard_eq_two.1 (M.ncard_preimage_singleton_eq_two (M a))
  ⟨x, y, hxy⟩

private theorem existsUnique_ne_and_apply_eq (a : α) : ∃! b, b ≠ a ∧ M b = M a := by
  obtain ⟨x, y, hxy, hM⟩ := Set.ncard_eq_two.1 (M.ncard_preimage_singleton_eq_two (M a))
  have hmem (b : α) : M b = M a ↔ b = x ∨ b = y := by
    simpa using Set.ext_iff.1 hM b
  rcases (hmem a).1 rfl with rfl | rfl
  · exact ⟨y, ⟨hxy.symm, (hmem y).2 (.inr rfl)⟩, fun b hb => ((hmem b).1 hb.2).resolve_left hb.1⟩
  · exact ⟨x, ⟨hxy, (hmem x).2 (.inl rfl)⟩, fun b hb => ((hmem b).1 hb.2).resolve_right hb.1⟩

/-- The partner of a point: the other point with the same label. -/
private noncomputable def partnerFun (a : α) : α :=
  (M.existsUnique_ne_and_apply_eq a).exists.choose

private theorem ne_and_apply_eq_iff {a b : α} : b ≠ a ∧ M b = M a ↔ b = M.partnerFun a :=
  ⟨fun hb => (M.existsUnique_ne_and_apply_eq a).unique hb
    (M.existsUnique_ne_and_apply_eq a).exists.choose_spec,
    fun hb => hb ▸ (M.existsUnique_ne_and_apply_eq a).exists.choose_spec⟩

private theorem partnerFun_involutive : Function.Involutive M.partnerFun := fun a => by
  have h := M.ne_and_apply_eq_iff.2 (rfl : M.partnerFun a = M.partnerFun a)
  exact (M.ne_and_apply_eq_iff.1 ⟨h.1.symm, h.2.symm⟩).symm

private theorem partnerFun_ne (a : α) : M.partnerFun a ≠ a :=
  (M.ne_and_apply_eq_iff.2 rfl).1

/-- The *partner* perfect matching of a labelled perfect matching, exchanging the two points of
each matched pair. -/
noncomputable def partner : PerfectMatching α :=
  .ofInvolutive M.partnerFun_involutive M.partnerFun_ne

/-- The partner of `a` is `b` exactly when `b` is the other point carrying the label of `a`. -/
theorem partner_eq_iff {a b : α} : M.partner.val a = b ↔ b ≠ a ∧ M b = M a := by
  rw [partner, PerfectMatching.ofInvolutive_apply, ne_and_apply_eq_iff, eq_comm]

@[simp]
theorem apply_partner (a : α) : M (M.partner.val a) = M a :=
  (M.partner_eq_iff.1 rfl).2

/-- Two points have the same label exactly when they are equal or partners. -/
theorem apply_eq_apply_iff {a b : α} : M b = M a ↔ b = a ∨ b = M.partner.val a := by
  rw [eq_comm (a := b) (b := M.partner.val a), partner_eq_iff]
  by_cases h : b = a <;> simp [h]

/-- The labelled perfect matching with labels `f`, given a fixed-point-free map `g` such that two
points have the same label exactly when they are equal or one is the image of the other under
`g`. Every label must be used. Its partner involution is `g`
(`TauCeti.PerfectMatching.Labeling.partner_ofPartner`). -/
def ofPartner (f : α → β) (g : α → α) (hg : ∀ a, g a ≠ a)
    (hfg : ∀ a b, f b = f a ↔ b = a ∨ b = g a) (hf : Function.Surjective f) : Labeling α β where
  toFun := f
  ncard_preimage_singleton_eq_two' b := by
    obtain ⟨a, rfl⟩ := hf b
    rw [show f ⁻¹' {f a} = {a, g a} by ext; simp [hfg]]
    exact Set.ncard_pair (hg a).symm

@[simp]
theorem coe_ofPartner (f : α → β) (g : α → α) (hg : ∀ a, g a ≠ a)
    (hfg : ∀ a b, f b = f a ↔ b = a ∨ b = g a) (hf : Function.Surjective f) :
    ⇑(ofPartner f g hg hfg hf) = f := (rfl)

@[simp]
theorem partner_ofPartner (f : α → β) (g : α → α) (hg : ∀ a, g a ≠ a)
    (hfg : ∀ a b, f b = f a ↔ b = a ∨ b = g a) (hf : Function.Surjective f) (a : α) :
    (ofPartner f g hg hfg hf).partner.val a = g a := by
  rw [partner_eq_iff]
  exact ⟨hg a, ((hfg a (g a)).2 (Or.inr rfl))⟩

/-- The labelled perfect matching `M` pulled back along a bijection `e : γ ≃ α` of the points. -/
def comp (e : γ ≃ α) : Labeling γ β where
  toFun := M ∘ e
  ncard_preimage_singleton_eq_two' b := by
    rw [Set.preimage_comp, ← e.image_symm_eq_preimage,
      Set.ncard_image_of_injective _ e.symm.injective]
    exact M.ncard_preimage_singleton_eq_two b

@[simp]
theorem comp_apply (e : γ ≃ α) (c : γ) : M.comp e c = M (e c) := (rfl)

/-- The partner of a pulled-back labelled perfect matching is the partner of `M` transported back
along `e`. -/
@[simp]
theorem partner_comp (e : γ ≃ α) : (M.comp e).partner = PerfectMatching.congr e.symm M.partner :=
  Subtype.ext <| Equiv.ext fun c => by
    rw [partner_eq_iff, PerfectMatching.congr_val_apply, symm_symm]
    exact ⟨fun h => M.partner.apply_ne (e c) (e.symm_apply_eq.1 h), by simp⟩

end PerfectMatching.Labeling

end TauCeti

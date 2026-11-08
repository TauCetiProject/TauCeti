/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.IntermediateValue

/-!
# Order consequences of the intermediate value theorem

Consequences of the intermediate value theorem on a preconnected set `s`, phrased as
uniform order statements:

* `IsPreconnected.forall_lt_or_forall_lt`: two continuous functions which never agree on `s` are
  strictly ordered on all of `s`, one way or the other.
* `IsPreconnected.forall_le_or_forall_lt`, `IsPreconnected.forall_lt_of_lt`: the same for two
  continuous functions which either agree on all of `s` or never agree there.
* `IsPreconnected.forall_le_or_forall_ge`: a continuous function on `s` which never takes a value
  in the open interval `Ioo a b`, with `a < b`, lies below `a` on all of `s` or above `b` on all
  of `s`.
-/

public section

open Set

variable {X α : Type*} [TopologicalSpace X] [LinearOrder α] [TopologicalSpace α]
  [OrderClosedTopology α] {s : Set X}

/-- Two continuous functions on a preconnected set which never agree there are strictly ordered on
the whole set. -/
theorem IsPreconnected.forall_lt_or_forall_lt (hs : IsPreconnected s) {f g : X → α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (hfg : ∀ x ∈ s, f x ≠ g x) :
    (∀ x ∈ s, f x < g x) ∨ ∀ x ∈ s, g x < f x := by
  by_contra! h
  obtain ⟨⟨a, ha, hga⟩, ⟨b, hb, hfb⟩⟩ := h
  obtain ⟨x, hx, hfgx⟩ := hs.intermediate_value₂ hb ha hf hg hfb hga
  exact hfg x hx hfgx

/-- Two continuous functions on a preconnected set which either agree on the whole set or never
agree there satisfy `f ≤ g` on the whole set or `g < f` on the whole set. -/
theorem IsPreconnected.forall_le_or_forall_lt (hs : IsPreconnected s) {f g : X → α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (hfg : EqOn f g s ∨ ∀ x ∈ s, f x ≠ g x) :
    (∀ x ∈ s, f x ≤ g x) ∨ ∀ x ∈ s, g x < f x := by
  rcases hfg with he | hne
  · exact .inl fun x hx ↦ (he hx).le
  · exact (hs.forall_lt_or_forall_lt hf hg hne).imp (fun h x hx ↦ (h x hx).le) id

/-- Two continuous functions on a preconnected set which either agree on the whole set or never
agree there, and satisfy `f < g` at one point of the set, satisfy `f < g` on the whole set. -/
theorem IsPreconnected.forall_lt_of_lt (hs : IsPreconnected s) {f g : X → α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (hfg : EqOn f g s ∨ ∀ x ∈ s, f x ≠ g x)
    {x : X} (hx : x ∈ s) (hlt : f x < g x) : ∀ y ∈ s, f y < g y :=
  (hs.forall_le_or_forall_lt hg hf (hfg.imp EqOn.symm fun h y hy ↦ (h y hy).symm)).resolve_left
    fun h ↦ (h x hx).not_gt hlt

/-- A continuous function on a preconnected set which never takes a value in `Ioo a b`, where
`a < b`, lies below `a` on the whole set or above `b` on the whole set. -/
theorem IsPreconnected.forall_le_or_forall_ge (hs : IsPreconnected s)
    {f : X → α} (hf : ContinuousOn f s) {a b : α} (hab : a < b) (h : ∀ x ∈ s, f x ∉ Ioo a b) :
    (∀ x ∈ s, f x ≤ a) ∨ ∀ x ∈ s, b ≤ f x := by
  have hcover : f '' s ⊆ Iic a ∪ Ici b := by
    rintro _ ⟨x, hx, rfl⟩
    rcases le_or_gt (f x) a with hxa | hax
    · exact .inl hxa
    · exact .inr (not_lt.1 fun hxb ↦ h x hx ⟨hax, hxb⟩)
  have hdisj : f '' s ∩ (Iic a ∩ Ici b) = ∅ :=
    eq_empty_of_forall_notMem fun y ⟨_, hya, hby⟩ ↦ (hab.trans_le hby).not_ge hya
  exact (isPreconnected_iff_subset_of_disjoint_closed.1 (hs.image f hf) _ _ isClosed_Iic
    isClosed_Ici hcover hdisj).imp (fun h x hx ↦ h (mem_image_of_mem f hx))
    fun h x hx ↦ h (mem_image_of_mem f hx)

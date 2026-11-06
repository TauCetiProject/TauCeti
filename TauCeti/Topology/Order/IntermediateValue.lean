/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.IntermediateValue

/-!
# Order consequences of the intermediate value theorem

Two consequences of the intermediate value theorem on a preconnected set `s`, phrased as
uniform order statements:

* `IsPreconnected.forall_lt_or_forall_lt`: two continuous functions which never agree on `s` are
  strictly ordered on all of `s`, one way or the other.
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

/-- A continuous function on a preconnected set which never takes a value in `Ioo a b`, where
`a < b`, lies below `a` on the whole set or above `b` on the whole set. -/
theorem IsPreconnected.forall_le_or_forall_ge [DenselyOrdered α] (hs : IsPreconnected s)
    {f : X → α} (hf : ContinuousOn f s) {a b : α} (hab : a < b) (h : ∀ x ∈ s, f x ∉ Ioo a b) :
    (∀ x ∈ s, f x ≤ a) ∨ ∀ x ∈ s, b ≤ f x := by
  by_contra! hc
  obtain ⟨⟨y, hy, hay⟩, ⟨z, hz, hzb⟩⟩ := hc
  have hy' : b ≤ f y := not_lt.1 fun hlt ↦ h y hy ⟨hay, hlt⟩
  have hz' : f z ≤ a := not_lt.1 fun hlt ↦ h z hz ⟨hlt, hzb⟩
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  obtain ⟨x, hx, rfl⟩ := hs.intermediate_value hz hy hf ⟨hz'.trans hac.le, hcb.le.trans hy'⟩
  exact h x hx ⟨hac, hcb⟩

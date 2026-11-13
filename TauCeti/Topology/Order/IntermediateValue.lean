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
* `IsPreconnected.subsingleton_of_interior_eq_empty`: a preconnected subset of a linearly ordered
  space with empty interior has at most one point.
* `IsPreconnected.subsingleton_image_of_interior_eq_empty`: a continuous function on `s` with values
  in a set with empty interior, for instance a null set of `ℝ`, is constant on `s`.

A continuous function on `Ioo a b` which lies above `c` just to the right of `a` and is at most
`c` somewhere in `Ioo a b` has a least such point, `ContinuousOn.exists_mem_Ioo_le_and_forall_gt`.
-/

public section

open Set
open scoped Topology

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

/-- A function continuous on `Ioo a b`, eventually above `c` to the right of `a` and at most `c`
somewhere in `Ioo a b`, has a least such point `t₁ ∈ Ioo a b`: `f t₁ ≤ c` and `c < f` on
`Ioo a t₁`. -/
theorem ContinuousOn.exists_mem_Ioo_le_and_forall_gt
    [ConditionallyCompleteLinearOrder X] [OrderTopology X] {f : X → α} {a b : X} {c : α}
    (hf : ContinuousOn f (Ioo a b)) (hpos : ∀ᶠ r in 𝓝[>] a, c < f r)
    (hne : ∃ t ∈ Ioo a b, f t ≤ c) : ∃ t₁ ∈ Ioo a b, f t₁ ≤ c ∧ ∀ r ∈ Ioo a t₁, c < f r := by
  obtain ⟨t, ht, hft⟩ := hne
  set Z := Ioo a b ∩ {t | f t ≤ c}
  have hZ : Z.Nonempty := ⟨t, ht, hft⟩
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' (ht.1.trans ht.2)).1 hpos
  have hbdd : BddBelow Z := ⟨a, fun z hz ↦ hz.1.1.le⟩
  have hut₁ : u ≤ sInf Z := le_csInf hZ fun z hz ↦ le_of_not_gt fun h ↦
    hz.2.not_gt (hsub ⟨hz.1.1, h⟩)
  have ht₁ : sInf Z ∈ Ioo a b :=
    ⟨lt_of_lt_of_le hu hut₁, (csInf_le hbdd ⟨ht, hft⟩).trans_lt ht.2⟩
  refine ⟨sInf Z, ht₁, ?_, fun r hr ↦ lt_of_not_ge fun h ↦
    hr.2.not_ge (csInf_le hbdd ⟨⟨hr.1, hr.2.trans ht₁.2⟩, h⟩)⟩
  exact ContinuousWithinAt.closure_le (csInf_mem_closure hZ hbdd)
    ((hf _ ht₁).mono inter_subset_left) continuousWithinAt_const fun _ hz ↦ hz.2

/-- A preconnected subset with empty interior of a linearly ordered space has at most one
point. -/
theorem IsPreconnected.subsingleton_of_interior_eq_empty {t : Set α} (ht : IsPreconnected t)
    (h : interior t = ∅) : t.Subsingleton := by
  intro a ha b hb
  by_contra hne
  wlog hab : a < b generalizing a b
  · exact this hb ha (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hab) (Ne.symm hne))
  -- The open sets `Iio b` and `Ioi a` cover `t`, so `t` meets `Ioo a b`; then the nonempty open
  -- interval `Ioo a b ⊆ Icc a b ⊆ t` lies in the interior of `t`.
  obtain ⟨c, -, hcb, hac⟩ := ht (Iio b) (Ioi a) isOpen_Iio isOpen_Ioi
    (fun x _ ↦ (lt_or_ge x b).imp id hab.trans_le) ⟨a, ha, hab⟩ ⟨b, hb, hab⟩
  have hsub : Ioo a b ⊆ interior t :=
    interior_maximal (Ioo_subset_Icc_self.trans (ht.Icc_subset ha hb)) isOpen_Ioo
  rw [h] at hsub
  exact hsub ⟨hac, hcb⟩

/-- A continuous function on a preconnected set, with values in a subset `t` of a linearly ordered
space whose interior is empty, is constant on the set. -/
theorem IsPreconnected.subsingleton_image_of_interior_eq_empty (hs : IsPreconnected s) {f : X → α}
    (hf : ContinuousOn f s) {t : Set α} (hft : MapsTo f s t) (ht : interior t = ∅) :
    (f '' s).Subsingleton :=
  (hs.image f hf).subsingleton_of_interior_eq_empty
    (subset_empty_iff.1 (ht ▸ interior_mono (image_subset_iff.2 hft)))

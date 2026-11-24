/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Order consequences of the intermediate value theorem

Consequences of the intermediate value theorem on a preconnected set `s`, phrased as
uniform order statements:

* `IsPreconnected.forall_lt_or_forall_lt`: two continuous functions which never agree on `s` are
  strictly ordered on all of `s`, one way or the other.
* `IsPreconnected.forall_le_or_forall_lt`, `IsPreconnected.forall_lt_of_lt`: the same for two
  continuous functions which either agree on all of `s` or never agree there.
* `IsPreconnected.forall_mem_Ioo_of_mem_Icc`: a continuous function on `s` which takes neither
  the value `a` nor the value `b`, and lies in `Icc a b` at one point, lies in `Ioo a b` on all
  of `s`.
* `IsPreconnected.forall_le_or_forall_ge`: a continuous function on `s` which never takes a value
  in the open interval `Ioo a b`, with `a < b`, lies below `a` on all of `s` or above `b` on all
  of `s`.
* `IsPreconnected.subsingleton_of_interior_eq_empty`: a preconnected subset of a linearly ordered
  space with empty interior has at most one point.
* `IsPreconnected.subsingleton_image_of_interior_eq_empty`: a continuous function on `s` with values
  in a set with empty interior, for instance a null set of `ℝ`, is constant on `s`.

A continuous function on `Ioo a b` which lies above `c` just to the right of `a` and is at most
`c` somewhere in `Ioo a b` has a least such point, `ContinuousOn.exists_mem_Ioo_le_and_forall_gt`.

A continuous function with values in `Icc l u` near `a⁺` that tends neither to `l` nor to `u` at
`a⁺` takes values in a fixed subinterval `Icc c d`, with `l < c` and `d < u`, arbitrarily close to
`a`, `ContinuousOn.exists_frequently_mem_Icc_of_not_tendsto`. For instance, the proportion of a set
in small balls takes intermediate values at arbitrarily small radii unless it tends to `0` or `1`.

A function continuous and strictly monotone on a neighbourhood `s` of `x` maps it onto a
neighbourhood of `f x`, `StrictMonoOn.image_mem_nhds`.

A continuous antiperiodic function, `f (x + c) = -f x`, vanishes somewhere on `[[a, a + c]]` for
every `a`, `Function.Antiperiodic.exists_mem_uIcc_eq_zero`.
-/

public section

open Filter Set
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

/-- A continuous function on a preconnected set which takes neither the value `a` nor the value
`b` there, and lies in `Icc a b` at one point of the set, lies in `Ioo a b` on the whole set. -/
theorem IsPreconnected.forall_mem_Ioo_of_mem_Icc (hs : IsPreconnected s) {f : X → α}
    (hf : ContinuousOn f s) {a b : α} (hne : ∀ x ∈ s, f x ≠ a ∧ f x ≠ b) {x : X} (hx : x ∈ s)
    (hfx : f x ∈ Icc a b) : ∀ y ∈ s, f y ∈ Ioo a b := by
  have ha := hs.forall_lt_of_lt continuousOn_const hf (.inr fun y hy ↦ (hne y hy).1.symm) hx
    (hfx.1.lt_of_ne (hne x hx).1.symm)
  have hb := hs.forall_lt_of_lt hf continuousOn_const (.inr fun y hy ↦ (hne y hy).2) hx
    (hfx.2.lt_of_ne (hne x hx).2)
  exact fun y hy ↦ ⟨ha y hy, hb y hy⟩

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

/-- A function continuous on `Ioi a`, with values eventually in `Icc l u` to the right of `a`,
which tends neither to `l` nor to `u` at `a⁺`, takes values in a fixed interval `Icc c d` with
`l < c` and `d < u` at points arbitrarily close to `a` from the right. -/
theorem ContinuousOn.exists_frequently_mem_Icc_of_not_tendsto [OrderTopology α]
    [DenselyOrdered α] [ConditionallyCompleteLinearOrder X] [OrderTopology X] [DenselyOrdered X]
    [NoMaxOrder X] {f : X → α} {a : X} {l u : α} (hf : ContinuousOn f (Ioi a))
    (hlu : ∀ᶠ x in 𝓝[>] a, f x ∈ Icc l u) (hl : ¬Tendsto f (𝓝[>] a) (𝓝 l))
    (hu : ¬Tendsto f (𝓝[>] a) (𝓝 u)) :
    ∃ c d, l < c ∧ d < u ∧ ∃ᶠ x in 𝓝[>] a, f x ∈ Icc c d := by
  -- If `u ≤ l`, then `f` is eventually equal to `l`.
  by_cases hlu' : l < u
  swap
  · exact absurd (tendsto_nhds_of_eventually_eq
      (hlu.mono fun x hx => le_antisymm (hx.2.trans (not_lt.1 hlu')) hx.1)) hl
  obtain ⟨p, hlp, hpu⟩ := exists_between hlu'
  obtain ⟨q, hpq, hqu⟩ := exists_between hpu
  by_contra! H
  -- Near `a`, `f` avoids `Ioo p q`, so by connectedness it stays on one side of it.
  obtain ⟨ε, hε, hεH⟩ := (nhdsGT_basis a).eventually_iff.1 (H p q hlp hqu)
  rcases isPreconnected_Ioo.forall_le_or_forall_ge (hf.mono Ioo_subset_Ioi_self) hpq
    (fun x hx hxpq => hεH hx (Ioo_subset_Icc_self hxpq)) with hle | hge
  · refine hl (tendsto_order.2 ⟨fun b hb => hlu.mono fun x hx => hb.trans_le hx.1, fun b hb => ?_⟩)
    filter_upwards [H (min b p) q (lt_min hb hlp) hqu, Ioo_mem_nhdsGT hε] with x hx hxε
    exact lt_of_not_ge fun hbx => hx ⟨(min_le_left _ _).trans hbx, (hle x hxε).trans hpq.le⟩
  · refine hu (tendsto_order.2 ⟨fun b hb => ?_, fun b hb => hlu.mono fun x hx => hx.2.trans_lt hb⟩)
    filter_upwards [H p (max b q) hlp (max_lt hb hqu), Ioo_mem_nhdsGT hε] with x hx hxε
    exact lt_of_not_ge fun hxb => hx ⟨hpq.le.trans (hge x hxε), hxb.trans (le_max_left _ _)⟩

/-- A function continuous and strictly monotone on a neighbourhood `s` of `x` maps `s` onto a
neighbourhood of `f x`. -/
theorem StrictMonoOn.image_mem_nhds [ConditionallyCompleteLinearOrder X] [OrderTopology X]
    [DenselyOrdered X] [NoMinOrder X] [NoMaxOrder X] {f : X → α} (hf : StrictMonoOn f s)
    (hcont : ContinuousOn f s) {x : X} (hs : s ∈ 𝓝 x) : f '' s ∈ 𝓝 (f x) := by
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1 hs
  obtain ⟨a, hla, hax⟩ := exists_between hl
  obtain ⟨b, hxb, hbu⟩ := exists_between hu
  have hab : Icc a b ⊆ s := fun y hy ↦ hsub ⟨hla.trans_le hy.1, hy.2.trans_lt hbu⟩
  have hx : x ∈ s := mem_of_mem_nhds hs
  exact Filter.mem_of_superset (Icc_mem_nhds (hf (hab ⟨le_rfl, (hax.trans hxb).le⟩) hx hax)
    (hf hx (hab ⟨(hax.trans hxb).le, le_rfl⟩) hxb))
    ((intermediate_value_Icc (hax.trans hxb).le (hcont.mono hab)).trans (image_mono hab))

/-- A function `f` with `f (x + c) = -f x` for all `x`, with values in an ordered additive group,
vanishes somewhere on `[[a, a + c]]` if it is continuous there. -/
theorem Function.Antiperiodic.exists_mem_uIcc_eq_zero [ConditionallyCompleteLinearOrder X]
    [OrderTopology X] [DenselyOrdered X] [Add X] [AddGroup α] [AddLeftMono α] {f : X → α} {c : X}
    (h : Function.Antiperiodic f c) (a : X) (hf : ContinuousOn f (uIcc a (a + c))) :
    ∃ x ∈ uIcc a (a + c), f x = 0 := by
  -- The values at the two ends are negatives of each other.
  have h0 : (0 : α) ∈ uIcc (f a) (f (a + c)) := by
    rw [h a, mem_uIcc]
    rcases le_total 0 (f a) with h' | h'
    · exact .inr ⟨Left.neg_nonpos_iff.2 h', h'⟩
    · exact .inl ⟨h', Left.nonneg_neg_iff.2 h'⟩
  exact intermediate_value_uIcc hf h0

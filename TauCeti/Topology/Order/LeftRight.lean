/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.LeftRightNhds
import TauCeti.Topology.Closure

/-!
# Right-continuous functions on dense subsets

A function `g` that is right-continuous at every point before `T` exceeds a level `a` at some
time `t ≤ T` only if it already exceeds `a` at `T`, at some point of a given dense set `D` below
`T`, or at some point below `T` isolated on the right. So the supremum of `g` over `(-∞, T]` is
its supremum over `{T} ∪ ((D ∪ C) ∩ (-∞, T])`, where `C` is the set of points isolated on the
right. In a second countable space `D` may be taken countable and `C` is countable, so this
replaces a supremum over uncountably many times by a countable one. Likewise, for a function into
a regular space that is eventually right-continuous along `𝓝[>] a`, convergence along `𝓝[>] a` is
equivalent to convergence along `𝓝[(D ∪ C) ∩ (a, ∞)] a`.

For an arbitrary topological codomain, right-continuity at `u` into a neighbourhood `U` of `f u`
together with nontriviality of `𝓝[>] u` puts `f x ∈ U` at a dense point `x ∈ D ∩ (u, v)`. On a
densely ordered linear order with the order topology, this implies that a function right-continuous
on `[a, t)` visits an open set `U` somewhere in `[a, t]` if and only if either `f t ∈ U` or `f`
visits `U` at some point of `D ∩ [a, t]`.

## Main declarations

* `Dense.exists_mem_insert_inter_Iic_lt`: a value of `g` above `a` at a time `t ≤ T` is matched
  by a value above `a` at `T` or at a point of `(D ∪ C) ∩ (-∞, T]`.
* `TopologicalSpace.exists_countable_subset_Iic_exists_mem_lt`: in a second countable space,
  one countable set of times `≤ T` serves for every function right-continuous before `T`.
* `TopologicalSpace.exists_countable_subset_Iic_biSup_eq`: in a second countable space, the
  supremum over `(-∞, T]` of any function into a complete linear order with closed lower rays that
  is right-continuous before `T` equals its supremum over that countable set.
* `Dense.tendsto_nhdsGT_iff`: for `g` eventually right-continuous along `𝓝[>] a` into a regular
  space, convergence to `c` along `𝓝[>] a` is equivalent to convergence along
  `𝓝[(D ∪ C) ∩ Ioi a] a`.
* `TopologicalSpace.exists_countable_subset_tendsto_nhdsGT_iff`: in a second countable space,
  every `s ∈ 𝓝[>] a` contains a countable `S ⊆ s ∩ Ioi a` with `(𝓝[S] a).NeBot ↔ (𝓝[>] a).NeBot`
  along which convergence of any eventually right-continuous function is equivalent to convergence
  along `𝓝[>] a`.
* `Dense.exists_mem_Ioo_apply_mem`: right-continuity at `u` pushes membership in a neighbourhood of
  `f u` onto a point of a dense set `D` in `(u, v)`.
* `Dense.exists_mem_Icc_apply_mem_iff_of_isOpen`: on a densely ordered space, visiting an open set
  `U` on `[a, t]` is equivalent to visiting `U` at `t` or at a point of `D ∩ [a, t]`.
* `TopologicalSpace.exists_denseRange_isCofinal`: every nonempty separable linear order with closed
  lower rays admits a sequence with dense, cofinal range.
* `TauCeti.le_of_forall_rat_add_le`: a function right-continuous at `t + h` that does not
  increase along rational increments from `t` does not increase along the real increment `h`.
-/

public section

open Set

section OrderTopology

variable {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]

section LinearOrder

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [ClosedIicTopology α]

/-- If `g` is right-continuous at every time before `T` and `a < g t` for some `t ≤ T`, then
`a < g s` for some `s` in `{T} ∪ ((D ∪ C) ∩ (-∞, T])`, for any dense set `D`, where `C` is the
set of points isolated on the right, that is, covered by some point. -/
theorem Dense.exists_mem_insert_inter_Iic_lt {D : Set ι} (hD : Dense D) {g : ι → α} {T t : ι}
    (hg : ∀ t < T, ContinuousWithinAt g (Ioi t) t) (htT : t ≤ T) {a : α} (ha : a < g t) :
    ∃ s ∈ insert T ((D ∪ {x | ∃ y, x ⋖ y}) ∩ Iic T), a < g s := by
  rcases htT.lt_or_eq with htT | rfl
  · obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' htT).1
      ((hg t htT).preimage_mem_nhdsWithin (Ioi_mem_nhds ha))
    by_cases hne : (Ioo t (min u T)).Nonempty
    · obtain ⟨s, hs, hsD⟩ := hD.inter_open_nonempty _ isOpen_Ioo hne
      exact ⟨s, Or.inr ⟨Or.inl hsD, hs.2.le.trans (min_le_right _ _)⟩,
        hsub ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩⟩
    · exact ⟨t, Or.inr ⟨Or.inr ⟨_, covBy_iff_Ioo_eq.2
        ⟨lt_min hu htT, not_nonempty_iff_eq_empty.1 hne⟩⟩, htT.le⟩, ha⟩
  · exact ⟨t, mem_insert _ _, ha⟩

/-- In a second countable space, every `T` has a countable set `S` of points `≤ T` such that
whenever `g` is right-continuous at every point before `T` and `a < g t` for some `t ≤ T`, also
`a < g s` for some `s ∈ S`. One may take `S = {T} ∪ ((D ∪ C) ∩ (-∞, T])` for a countable dense
set `D` and the countable set `C` of points isolated on the right. -/
theorem TopologicalSpace.exists_countable_subset_Iic_exists_mem_lt [SecondCountableTopology ι]
    (T : ι) :
    ∃ S : Set ι, S.Countable ∧ S ⊆ Iic T ∧ ∀ ⦃g : ι → α⦄,
      (∀ t < T, ContinuousWithinAt g (Ioi t) t) →
        ∀ ⦃t⦄, t ≤ T → ∀ ⦃a⦄, a < g t → ∃ s ∈ S, a < g s :=
  let ⟨D, hDc, hD⟩ := exists_countable_dense ι
  ⟨insert T ((D ∪ {x | ∃ y, x ⋖ y}) ∩ Iic T),
    ((hDc.union countable_setOfPred_covBy_right).mono inter_subset_left).insert T,
    insert_subset_iff.2 ⟨le_rfl, inter_subset_right⟩,
    fun _ hg _ htT _ ha ↦ hD.exists_mem_insert_inter_Iic_lt hg htT ha⟩

end LinearOrder

section CompleteLinearOrder

variable {α : Type*} [CompleteLinearOrder α] [TopologicalSpace α] [ClosedIicTopology α]

/-- In a second countable space, every `T` has a countable set `S` of points `≤ T` such that
for every function `g` into a complete linear order with closed lower rays that is right-continuous
at every point before `T`, its supremum over `(-∞, T]` equals its supremum over `S`. -/
theorem TopologicalSpace.exists_countable_subset_Iic_biSup_eq [SecondCountableTopology ι]
    (T : ι) :
    ∃ S : Set ι, S.Countable ∧ S ⊆ Iic T ∧ ∀ ⦃g : ι → α⦄,
      (∀ t < T, ContinuousWithinAt g (Ioi t) t) → (⨆ s ∈ S, g s) = ⨆ t ≤ T, g t := by
  obtain ⟨S, hSc, hST, hS⟩ := exists_countable_subset_Iic_exists_mem_lt (α := α) T
  refine ⟨S, hSc, hST, fun g hg => le_antisymm ?_ ?_⟩
  · exact iSup₂_le fun s hs => le_iSup₂_of_le s (hST hs) le_rfl
  · refine iSup₂_le fun t ht => le_of_forall_lt fun a ha => ?_
    obtain ⟨s, hs, has⟩ := hS hg ht ha
    exact has.trans_le (le_iSup₂ (f := fun s _ => g s) s hs)

end CompleteLinearOrder

section RegularSpace

open Filter
open scoped Topology

/-- If `g : ι → E` into a regular space is eventually right-continuous along `𝓝[>] a` and `D` is
dense in `ι`, then `g` tends to `c` along `𝓝[>] a` if and only if it tends to `c` along
`𝓝[(D ∪ C) ∩ Ioi a] a`, where `C = {x | ∃ y, x ⋖ y}` is the set of points isolated on the
right. -/
theorem Dense.tendsto_nhdsGT_iff {E : Type*} [TopologicalSpace E] [RegularSpace E]
    {D : Set ι} (hD : Dense D) {a : ι} {g : ι → E} {c : E}
    (hg : ∀ᶠ r in 𝓝[>] a, ContinuousWithinAt g (Ioi r) r) :
    Tendsto g (𝓝[>] a) (𝓝 c) ↔
      Tendsto g (𝓝[(D ∪ {x | ∃ y, x ⋖ y}) ∩ Ioi a] a) (𝓝 c) := by
  refine ⟨fun h ↦ h.mono_left (nhdsWithin_mono a inter_subset_right), fun h ↦ ?_⟩
  obtain hbot | hne := eq_or_neBot (𝓝[>] a)
  · simp [hbot]
  obtain ⟨b₀, hb₀⟩ := Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a) (s := Ioi a))
  obtain ⟨b, hb, hrc⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hb₀).1 hg
  refine (closed_nhds_basis c).tendsto_right_iff.2 ?_
  rintro V ⟨hVc, hVclosed⟩
  obtain ⟨W, hW, hWV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (h hVc)
  obtain ⟨u, hu, huW⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hb).1 (mem_nhdsWithin_of_mem_nhds hW)
  set m : ι := min u b
  refine mem_of_superset (Ioo_mem_nhdsGT (lt_min hu hb)) fun r hr ↦ ?_
  by_contra hrV
  have hr_rc : ContinuousWithinAt g (Ioi r) r :=
    hrc ⟨hr.1, hr.2.trans_le (min_le_right u b)⟩
  obtain ⟨v, hv, hvV⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hr.2).1
    (hr_rc.preimage_mem_nhdsWithin (hVclosed.isOpen_compl.mem_nhds hrV))
  by_cases hne_Ioo : (Ioo r (min v m)).Nonempty
  · obtain ⟨d, hd, hdD⟩ := hD.inter_open_nonempty _ isOpen_Ioo hne_Ioo
    have hd_u : d ∈ Ioo a u :=
      ⟨hr.1.trans hd.1, (hd.2.trans_le (min_le_right v m)).trans_le (min_le_left u b)⟩
    exact hvV ⟨hd.1, hd.2.trans_le (min_le_left v m)⟩ (hWV ⟨huW hd_u, Or.inl hdD, hd_u.1⟩)
  · have hcov : r ⋖ min v m :=
      covBy_iff_Ioo_eq.2 ⟨lt_min hv hr.2, not_nonempty_iff_eq_empty.1 hne_Ioo⟩
    have hr_u : r ∈ Ioo a u := ⟨hr.1, hr.2.trans_le (min_le_left u b)⟩
    exact hrV (hWV ⟨huW hr_u, Or.inr ⟨_, hcov⟩, hr.1⟩)

/-- In a second countable linear order with the order topology, every set `s ∈ 𝓝[>] a` contains a
countable subset `S ⊆ s ∩ Ioi a` such that `(𝓝[S] a).NeBot ↔ (𝓝[>] a).NeBot` and, for every
function `g : ι → E` into a regular space that is eventually right-continuous along `𝓝[>] a`,
convergence to `c` along `𝓝[>] a` is equivalent to convergence along `𝓝[S] a`. -/
theorem TopologicalSpace.exists_countable_subset_tendsto_nhdsGT_iff [SecondCountableTopology ι]
    {E : Type*} [TopologicalSpace E] [RegularSpace E] {a : ι} {s : Set ι} (hs : s ∈ 𝓝[>] a) :
    ∃ S : Set ι, S.Countable ∧ S ⊆ s ∩ Ioi a ∧ ((𝓝[S] a).NeBot ↔ (𝓝[>] a).NeBot) ∧
      ∀ ⦃g : ι → E⦄, (∀ᶠ r in 𝓝[>] a, ContinuousWithinAt g (Ioi r) r) →
        ∀ {c : E}, Tendsto g (𝓝[>] a) (𝓝 c) ↔ Tendsto g (𝓝[S] a) (𝓝 c) := by
  obtain hbot | hne := eq_or_neBot (𝓝[>] a)
  · refine ⟨∅, countable_empty, empty_subset _, by simp [hbot], fun _ _ _ ↦ by simp [hbot]⟩
  obtain ⟨b₀, hb₀⟩ := Filter.nonempty_of_mem (self_mem_nhdsWithin (a := a) (s := Ioi a))
  obtain ⟨r₀, hr₀, hr₀s⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hb₀).1 hs
  obtain ⟨D, hDc, hD⟩ := exists_countable_dense ι
  let S : Set ι := (D ∪ {x | ∃ y, x ⋖ y}) ∩ Ioo a r₀
  have hS_eq : S = (D ∪ {x | ∃ y, x ⋖ y}) ∩ Ioi a ∩ Iio r₀ := by
    ext; simp [S, Ioo, and_assoc]
  have hnhds : 𝓝[S] a = 𝓝[(D ∪ {x | ∃ y, x ⋖ y}) ∩ Ioi a] a := by
    rw [hS_eq, nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds (Iio_mem_nhds hr₀))]
  refine ⟨S, (hDc.union countable_setOfPred_covBy_right).mono inter_subset_left,
    subset_inter (inter_subset_right.trans hr₀s) (inter_subset_right.trans Ioo_subset_Ioi_self),
    iff_of_true ?_ hne, fun g hg c ↦ ?_⟩
  · rw [hnhds, ← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff]
    intro o ho hao
    obtain ⟨d, ⟨hdo, hda⟩, hdD⟩ := hD.inter_open_nonempty _ (ho.inter isOpen_Ioi)
      (mem_closure_iff.1 (mem_closure_iff_nhdsWithin_neBot.2 hne) o ho hao)
    exact ⟨d, hdo, Or.inl hdD, hda⟩
  · rw [hnhds]
    exact hD.tendsto_nhdsGT_iff hg

end RegularSpace

end OrderTopology

section OpenTarget

open scoped Topology

/-- If `D` is dense, `𝓝[>] u` is nontrivial, `u < v`, and `f` is right-continuous at `u`, then
every neighbourhood `U` of `f u` contains `f x` for some `x ∈ D` with `x ∈ Ioo u v`. -/
theorem Dense.exists_mem_Ioo_apply_mem {ι α : Type*} [LinearOrder ι] [TopologicalSpace ι]
    [ClosedIicTopology ι] [ClosedIciTopology ι] [TopologicalSpace α] {D : Set ι} (hD : Dense D)
    {f : ι → α} {u v : ι} [(𝓝[>] u).NeBot] (huv : u < v)
    (hf : ContinuousWithinAt f (Ioi u) u) {U : Set α} (hU : U ∈ 𝓝 (f u)) :
    ∃ x ∈ D, x ∈ Ioo u v ∧ f x ∈ U :=
  ((hD.frequently_mem_nhdsWithin isOpen_Ioi).and_eventually
    (Filter.inter_mem (Ioo_mem_nhdsGT huv) (hf hU))).exists

/-- On a densely ordered linear order with the order topology, a function right-continuous on
`[a, t)` visits an open set `U` somewhere in `[a, t]` if and only if either `f t ∈ U` or `f x ∈ U`
at some point `x ∈ D` with `x ∈ [a, t]`, for any dense set `D`. -/
theorem Dense.exists_mem_Icc_apply_mem_iff_of_isOpen {ι α : Type*} [LinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [DenselyOrdered ι] [TopologicalSpace α]
    {D : Set ι} (hD : Dense D) {f : ι → α} {a t : ι} (hat : a ≤ t)
    (hf : ∀ u ∈ Ico a t, ContinuousWithinAt f (Ioi u) u) {U : Set α} (hU : IsOpen U) :
    (∃ u ∈ Icc a t, f u ∈ U) ↔ f t ∈ U ∨ ∃ x ∈ D, x ∈ Icc a t ∧ f x ∈ U := by
  constructor
  · rintro ⟨u, ⟨hau, hut⟩, hu⟩
    rcases hut.eq_or_lt with rfl | hut
    · exact Or.inl hu
    · have : (𝓝[>] u).NeBot := nhdsGT_neBot_of_exists_gt ⟨t, hut⟩
      obtain ⟨x, hxD, hx, hfx⟩ :=
        hD.exists_mem_Ioo_apply_mem hut (hf u ⟨hau, hut⟩) (hU.mem_nhds hu)
      exact Or.inr ⟨x, hxD, ⟨hau.trans hx.1.le, hx.2.le⟩, hfx⟩
  · rintro (ht | ⟨x, -, hx, hfx⟩)
    · exact ⟨t, ⟨hat, le_rfl⟩, ht⟩
    · exact ⟨x, hx, hfx⟩

/-- Every nonempty separable linear order with closed lower rays admits a sequence with dense,
cofinal range. -/
theorem TopologicalSpace.exists_denseRange_isCofinal {ι : Type*} [LinearOrder ι]
    [TopologicalSpace ι] [ClosedIicTopology ι] [TopologicalSpace.SeparableSpace ι] [Nonempty ι] :
    ∃ d : ℕ → ι, DenseRange d ∧ IsCofinal (range d) := by
  classical
  by_cases h : ∃ m : ι, IsMax m
  · obtain ⟨m, hm⟩ := h
    exact ⟨fun n ↦ Nat.casesOn n m (TopologicalSpace.denseSeq ι),
      (TopologicalSpace.denseRange_denseSeq ι).mono (by rintro _ ⟨n, rfl⟩; exact ⟨n + 1, rfl⟩),
      fun x ↦ ⟨m, ⟨0, rfl⟩, hm.isTop x⟩⟩
  · have : NoMaxOrder ι := ⟨fun x ↦ not_isMax_iff.mp fun hx ↦ h ⟨x, hx⟩⟩
    exact ⟨TopologicalSpace.denseSeq ι, TopologicalSpace.denseRange_denseSeq ι,
      Dense.exists_ge (TopologicalSpace.denseRange_denseSeq ι)⟩

end OpenTarget

section Rational

open Filter
open scoped Topology

/-- A function that is right-continuous at `t + h` and does not increase along rational
increments from `t` does not increase along the real increment `h ≥ 0`. -/
theorem TauCeti.le_of_forall_rat_add_le {β : Type*} [Preorder β] [TopologicalSpace β]
    [ClosedIicTopology β] {G : ℝ → β} {t h : ℝ} (hh : 0 ≤ h)
    (hG : Tendsto G (𝓝[>] (t + h)) (𝓝 (G (t + h))))
    (hanti : ∀ q : ℚ, 0 ≤ q → G (t + q) ≤ G t) : G (t + h) ≤ G t := by
  obtain ⟨r, -, hr, hid⟩ := Real.exists_seq_rat_strictAnti_tendsto h
  have hshift : Tendsto (fun n => t + (r n : ℝ)) atTop (𝓝[>] (t + h)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_const_nhds.add hid) (Eventually.of_forall fun n => ?_)
    exact mem_Ioi.2 (by linarith [hr n])
  refine le_of_tendsto (hG.comp hshift) (Eventually.of_forall fun n => ?_)
  exact hanti (r n) (by exact_mod_cast (hh.trans (hr n).le))

end Rational

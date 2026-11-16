/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Sets.Opens
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Separation.Hausdorff

/-!
# Local compactness from local data, and lifting compact sets along open maps

A space in which every point has a locally compact neighbourhood is locally compact
(`TauCeti.locallyCompactSpace_of_forall_exists_mem_nhds`).

Along an open map out of a weakly locally compact space, every compact subset of the range lies in
the image of a compact set (`IsOpenMap.exists_isCompact_subset_image`). This is how a compactness
statement about a quotient, such as a group modulo a kernel, is pulled back to the group.

A continuous injection out of a weakly locally compact space into a Hausdorff space is a
topological embedding on an open neighbourhood of any compact set
(`Continuous.exists_opens_isEmbedding_restrict`).

In a locally compact Hausdorff space, let `q` be continuous, above `a` off a compact set `Z`, and
such that every point is joined to `Z` by a preconnected set on which `q` does not increase. Then
for each open neighbourhood `U` of `Z`, the sublevels of `q` just above `a` lie in `U`, and their
closed versions are compact (`TauCeti.exists_gt_setOf_lt_subset_and_isCompact`). For instance,
the sublevels of `s + 2t` near the common zero set of `s, t ≥ 0` are compact when rescalings of
`s` and `t` contract every point to that set
(`TauCeti.exists_pos_setOf_add_two_mul_lt_subset_and_isCompact`).
-/

public section

open Set Topology

namespace TauCeti

/-- A space in which every point has a locally compact neighbourhood is locally compact. -/
theorem locallyCompactSpace_of_forall_exists_mem_nhds {X : Type*} [TopologicalSpace X]
    (h : ∀ x : X, ∃ U ∈ 𝓝 x, LocallyCompactSpace U) : LocallyCompactSpace X := by
  refine ⟨fun x W hW ↦ ?_⟩
  obtain ⟨U, hU, _⟩ := h x
  have hmap := IsInducing.subtypeVal.map_nhds_of_mem (⟨x, mem_of_mem_nhds hU⟩ : U)
    (by simpa using hU)
  rw [← hmap] at hW ⊢
  obtain ⟨K, hKx, hKW, hKc⟩ := local_compact_nhds hW
  exact ⟨(↑) '' K, Filter.image_mem_map hKx, image_subset_iff.mpr hKW,
    hKc.image continuous_subtype_val⟩

/-- Let `q` be a continuous function which is above `a` off a compact set `Z`, and suppose every
point `x` lies in a preconnected set meeting `Z` on which `q ≤ q x`. Then for every open
neighbourhood `U` of `Z` there is `m > a` such that the sublevel `{q < m}` lies in `U` and the
closed sublevels `{q ≤ δ}`, `δ < m`, are compact: they lie in a compact neighbourhood of `Z`
inside `U`, on whose boundary `q ≥ m`. -/
theorem exists_gt_setOf_lt_subset_and_isCompact {X α : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] [NoMaxOrder α] {Z U : Set X} (hZ : IsCompact Z) (hU : IsOpen U)
    (hZU : Z ⊆ U) {q : X → α} (hq : Continuous q) {a : α} (hqZ : ∀ x, q x ≤ a → x ∈ Z)
    (hpath : ∀ x, ∃ C : Set X, IsPreconnected C ∧ x ∈ C ∧ (C ∩ Z).Nonempty ∧ ∀ y ∈ C, q y ≤ q x) :
    ∃ m, a < m ∧ {x | q x < m} ⊆ U ∧ ∀ δ < m, IsCompact {x | q x ≤ δ} := by
  obtain ⟨N, hNc, hZN, hNU⟩ := exists_compact_between hZ hU hZU
  obtain ⟨m, hm, hmN⟩ : ∃ m, a < m ∧ ∀ x ∈ N \ interior N, m ≤ q x :=
    (hNc.diff isOpen_interior).exists_forall_le' hq.continuousOn fun x hx ↦
      not_le.1 fun hle ↦ hx.2 (hZN (hqZ x hle))
  -- A point with `q < m` is joined to `Z` without crossing the boundary of `N`.
  have hqN (x : X) (hx : q x < m) : x ∈ interior N := by
    obtain ⟨C, hC, hxC, hCZ, hCq⟩ := hpath x
    refine hC.subset_left_of_subset_union isOpen_interior hNc.isClosed.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) (fun y hy ↦ ?_)
      (hCZ.mono (inter_subset_inter_right _ hZN)) hxC
    by_cases hyN : y ∈ N
    · exact Or.inl (by_contra fun hint ↦ (hmN y ⟨hyN, hint⟩).not_gt ((hCq y hy).trans_lt hx))
    · exact Or.inr hyN
  refine ⟨m, hm, fun x hx ↦ hNU (interior_subset (hqN x hx)), fun δ hδ ↦ ?_⟩
  exact hNc.of_isClosed_subset (isClosed_le hq continuous_const) fun x hx ↦
    interior_subset (hqN x (lt_of_le_of_lt hx hδ))

/-- Let the continuous functions `s, t ≥ 0` on a locally compact Hausdorff space vanish together
only on a compact set `Z`, and let the maps `σ a b`, continuous jointly in `a`, `b` and the point,
rescale `s` by `a²` and `t` by `b²`, with `σ 1 1` the identity and `σ 0 0` mapping into `Z`. Then
for every open neighbourhood `U` of `Z` there is `m > 0` such that `{s + 2t < m}` lies in `U` and
the sublevels `{s + 2t ≤ δ}`, `δ < m`, are compact: the rays `a ↦ σ a a x`, `a ∈ [0, 1]`, join
each point `x` to `Z` without increasing `s + 2t`. -/
theorem exists_pos_setOf_add_two_mul_lt_subset_and_isCompact {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] {s t : X → ℝ} (hs : Continuous s) (ht : Continuous t)
    (hs₀ : ∀ x, 0 ≤ s x) (ht₀ : ∀ x, 0 ≤ t x) {Z U : Set X} (hZ : IsCompact Z) (hU : IsOpen U)
    (hZU : Z ⊆ U) (hstZ : ∀ x, s x = 0 → t x = 0 → x ∈ Z) (σ : ℝ → ℝ → X → X)
    (hσ : Continuous fun p : (ℝ × ℝ) × X ↦ σ p.1.1 p.1.2 p.2)
    (hσs : ∀ a b x, s (σ a b x) = a ^ 2 * s x) (hσt : ∀ a b x, t (σ a b x) = b ^ 2 * t x)
    (hσ₁ : ∀ x, σ 1 1 x = x) (hσZ : ∀ x, σ 0 0 x ∈ Z) :
    ∃ m > 0, {x | s x + 2 * t x < m} ⊆ U ∧ ∀ δ < m, IsCompact {x | s x + 2 * t x ≤ δ} :=
  exists_gt_setOf_lt_subset_and_isCompact hZ hU hZU
    (hs.add (continuous_const.mul ht)) (q := fun x ↦ s x + 2 * t x)
    (fun x (hx : s x + 2 * t x ≤ 0) ↦
      hstZ x (by linarith [hs₀ x, ht₀ x]) (by linarith [hs₀ x, ht₀ x]))
    fun x ↦ ⟨(fun a ↦ σ a a x) '' Icc 0 1, isPreconnected_Icc.image _
      (hσ.comp ((continuous_id.prodMk continuous_id).prodMk continuous_const)).continuousOn,
      ⟨1, ⟨zero_le_one, le_rfl⟩, hσ₁ x⟩, ⟨σ 0 0 x, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩, hσZ x⟩, by
        rintro _ ⟨a, ha, rfl⟩
        have ha2 : a ^ 2 ≤ 1 := pow_le_one₀ ha.1 ha.2
        simp only [hσs, hσt]
        nlinarith [hs₀ x, ht₀ x]⟩

end TauCeti

/-- Along an open map out of a weakly locally compact space, every compact subset of the range is
contained in the image of a compact set. -/
theorem IsOpenMap.exists_isCompact_subset_image {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [WeaklyLocallyCompactSpace X] {f : X → Y} (hf : IsOpenMap f)
    {K : Set Y} (hK : IsCompact K) (hKf : K ⊆ range f) :
    ∃ L : Set X, IsCompact L ∧ K ⊆ f '' L := by
  choose s hc hmem using fun x : X ↦ exists_compact_mem_nhds x
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x ↦ f '' interior (s x))
    (fun x ↦ hf _ isOpen_interior) fun _ hy ↦ by
      obtain ⟨x, rfl⟩ := hKf hy
      exact mem_iUnion.2 ⟨x, mem_image_of_mem f (mem_interior_iff_mem_nhds.2 (hmem x))⟩
  refine ⟨⋃ x ∈ t, s x, t.isCompact_biUnion fun x _ ↦ hc x, ht.trans ?_⟩
  rw [image_iUnion₂]
  exact iUnion₂_mono fun x _ ↦ image_mono interior_subset

/-- A continuous injection from a weakly locally compact space into a Hausdorff space restricts
to a topological embedding on some open neighbourhood of any compact set. -/
theorem Continuous.exists_opens_isEmbedding_restrict {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [WeaklyLocallyCompactSpace X] [T2Space Y] {f : X → Y}
    (hf : Continuous f) (hinj : Function.Injective f) {K : Set X} (hK : IsCompact K) :
    ∃ W : TopologicalSpace.Opens X, K ⊆ W ∧ IsEmbedding fun q : W => f q := by
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have h : IsEmbedding fun q : L => f q :=
    ((hf.comp continuous_subtype_val).isClosedEmbedding
      (hinj.comp Subtype.val_injective)).isEmbedding
  exact ⟨⟨interior L, isOpen_interior⟩, hKL, h.comp (IsEmbedding.inclusion interior_subset)⟩

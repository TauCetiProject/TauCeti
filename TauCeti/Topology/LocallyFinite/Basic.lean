/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PartitionOfUnity
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Locally finite families

A locally finite family of sets stays locally finite when it is reindexed along the first
projection `ι × κ → ι` with `κ` finite (`LocallyFinite.comp_fst`), and more generally along
`(Σ i, κ i) → ι` with every `κ i` finite (`LocallyFinite.comp_sigma_fst`). Together with
`LocallyFinite.subset`, this makes a family indexed by `ι × κ` whose `(i, k)`-th member lies in
the `i`-th member of a locally finite family locally finite. Dually, the pointwise union of
finitely many locally finite families is locally finite (`LocallyFinite.iUnion`), as is the family
of all pairwise intersections of two locally finite families (`LocallyFinite.inter`). A compact set
has a neighbourhood meeting only finitely many members of a locally finite family
(`LocallyFinite.exists_mem_nhdsSet_finite`), so the images of the members under a closed map with
compact fibres, such as a proper map, again form a locally finite family
(`LocallyFinite.image_of_isClosedMap`). The topological support of a locally finite sum of
functions lies in the union of their topological supports (`LocallyFinite.tsupport_finsum_subset`).

In a pseudometric space, a locally finite family of closed sets has the following useful local
description: around each point there is a ball such that every member of the family meeting the
ball contains the centre.

On a normal paracompact space, positive continuous functions on the members of a locally finite
closed family admit a single positive continuous strict minorant. This allows local error
tolerances to be assembled without a uniform lower bound on a noncompact space. The minorant is
constructed with Mathlib's `exists_continuous_forall_mem_convex_of_local_const`.
-/

public section

open Set Topology

namespace LocallyFinite

variable {ι κ X : Type*} [TopologicalSpace X] {f : ι → Set X}

/-- A locally finite family stays locally finite when reindexed along the first projection
`(Σ i, κ i) → ι`, for finite fibres `κ i`. -/
theorem comp_sigma_fst {κ : ι → Type*} [∀ i, Finite (κ i)] (hf : LocallyFinite f) :
    LocallyFinite fun p : (Σ i, κ i) ↦ f p.1 :=
  fun x ↦
    let ⟨U, hU, hfin⟩ := hf x
    ⟨U, hU, (hfin.biUnion fun i _ ↦ finite_range (Sigma.mk i)).subset
      fun ⟨_, k⟩ hp ↦ mem_biUnion hp ⟨k, rfl⟩⟩

/-- A locally finite family stays locally finite when reindexed along the first projection
`ι × κ → ι`, for `κ` finite. -/
theorem comp_fst [Finite κ] (hf : LocallyFinite f) : LocallyFinite fun p : ι × κ ↦ f p.1 :=
  (Equiv.locallyFinite_comp_iff (Equiv.sigmaEquivProd ι κ).symm).mpr
    (hf.comp_sigma_fst (κ := fun _ ↦ κ))

/-- The pairwise intersections of two locally finite families form a locally finite family.
The index set includes all pairs, whether or not the two families are the same. -/
protected theorem inter {s : ι → Set X} {t : κ → Set X}
    (hs : LocallyFinite s) (ht : LocallyFinite t) :
    LocallyFinite fun p : ι × κ ↦ s p.1 ∩ t p.2 := by
  intro x
  obtain ⟨U, hU, hsU⟩ := hs x
  obtain ⟨V, hV, htV⟩ := ht x
  refine ⟨U ∩ V, Filter.inter_mem hU hV, (hsU.prod htV).subset ?_⟩
  rintro ⟨i, j⟩ ⟨y, ⟨hys, hyt⟩, hyU, hyV⟩
  exact ⟨⟨y, hys, hyU⟩, ⟨y, hyt, hyV⟩⟩

/-- Positive continuous tolerances on a locally finite family of closed sets admit a positive
continuous strict minorant on the whole space. No covering or compactness assumption is needed. -/
theorem exists_continuous_pos_lt [NormalSpace X] [ParacompactSpace X]
    (hf : LocallyFinite f) (hclosed : ∀ i, IsClosed (f i)) {ε : ι → X → ℝ}
    (hε : ∀ i, ContinuousOn (ε i) (f i)) (hpos : ∀ i, ∀ x ∈ f i, 0 < ε i x) :
    ∃ δ : C(X, ℝ), (∀ x, 0 < δ x) ∧ ∀ i, ∀ x ∈ f i, δ x < ε i x := by
  classical
  let t (x : X) : Set ℝ := Ioi 0 ∩ ⋂ i, ⋂ (_ : x ∈ f i), Iio (ε i x)
  have hconv (x : X) : Convex ℝ (t x) :=
    (convex_Ioi (0 : ℝ)).inter (convex_iInter fun i ↦
      convex_iInter fun _ ↦ convex_Iio (ε i x))
  have hlocal (x : X) : ∃ c : ℝ, ∀ᶠ y in nhds x, c ∈ t y := by
    -- Finitely many constraints are active at x. Each admits a local positive constant.
    have hi (i : ι) (hx : x ∈ f i) :
        ∃ c > 0, ∀ᶠ y in nhds x, y ∈ f i → c < ε i y := by
      refine ⟨ε i x / 2, half_pos (hpos i x hx), ?_⟩
      have := (hε i x hx).eventually (Ioi_mem_nhds (half_lt_self (hpos i x hx)))
      exact eventually_nhdsWithin_iff.mp this
    have hfinite (s : Finset ι) (hs : ∀ i ∈ s, x ∈ f i) :
        ∃ c > 0, ∀ᶠ y in nhds x, ∀ i ∈ s, y ∈ f i → c < ε i y := by
      induction s using Finset.induction_on with
      | empty => exact ⟨1, one_pos, Filter.Eventually.of_forall (by simp)⟩
      | @insert i s his ih =>
        obtain ⟨a, ha, hya⟩ := hi i (hs i (by simp))
        obtain ⟨b, hb, hyb⟩ := ih (fun j hj ↦ hs j (by simp [hj]))
        refine ⟨min a b, lt_min ha hb, ?_⟩
        filter_upwards [hya, hyb] with y hya hyb j hj hy
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact (min_le_left _ _).trans_lt (hya hy)
        · exact (min_le_right _ _).trans_lt (hyb j hj hy)
    obtain ⟨c, hc, hyc⟩ := hfinite (hf.point_finite x).toFinset (by simp)
    refine ⟨c, ?_⟩
    filter_upwards [hyc, hf.eventually_subset hclosed x] with y hy hsub
    exact ⟨hc, by simpa only [mem_iInter, mem_Iio] using
      (fun i hi ↦ hy i (by simpa using hsub hi) hi)⟩
  obtain ⟨δ, hδ⟩ := exists_continuous_forall_mem_convex_of_local_const hconv hlocal
  refine ⟨δ, fun x ↦ (hδ x).1, fun i x hx ↦ ?_⟩
  exact mem_iInter.mp (mem_iInter.mp (hδ x).2 i) hx

/-- The pointwise union of finitely many locally finite families is locally finite. -/
protected theorem iUnion [Finite κ] {f : κ → ι → Set X} (hf : ∀ k, LocallyFinite (f k)) :
    LocallyFinite fun i ↦ ⋃ k, f k i := by
  simp_rw [locallyFinite_iff_smallSets] at hf ⊢
  intro x
  filter_upwards [Filter.eventually_all.2 fun k ↦ hf k x] with t ht
  simpa only [iUnion_inter, nonempty_iUnion, ofPred_exists] using finite_iUnion ht

/-- A locally finite family has, around every compact set, a neighbourhood meeting only finitely
many of its members. -/
theorem exists_mem_nhdsSet_finite (hf : LocallyFinite f) {K : Set X} (hK : IsCompact K) :
    ∃ W ∈ 𝓝ˢ K, {i | (f i ∩ W).Nonempty}.Finite := by
  refine hK.induction_on ⟨∅, by simp, by simp⟩ (fun s t hst ⟨W, hW, hfin⟩ ↦
    ⟨W, nhdsSet_mono hst hW, hfin⟩) (fun s t ⟨W, hW, hfin⟩ ⟨W', hW', hfin'⟩ ↦
    ⟨W ∪ W', union_mem_nhdsSet hW hW', (hfin.union hfin').subset fun i ↦ by
      simp [inter_union_distrib_left]⟩)
    fun x _ ↦ ?_
  obtain ⟨U, hU, hfin⟩ := hf x
  exact ⟨interior U, mem_nhdsWithin_of_mem_nhds (interior_mem_nhds.2 hU), interior U,
    isOpen_interior.mem_nhdsSet.2 subset_rfl,
    hfin.subset fun i ⟨y, hyi, hyU⟩ ↦ ⟨y, hyi, interior_subset hyU⟩⟩

/-- The image of a locally finite family under a closed map with compact fibres is locally finite.
This applies in particular to proper maps. -/
theorem image_of_isClosedMap {Y : Type*} [TopologicalSpace Y] {g : X → Y} (hf : LocallyFinite f)
    (hg : IsClosedMap g) (hfib : ∀ y, IsCompact (g ⁻¹' {y})) :
    LocallyFinite fun i ↦ g '' f i := by
  intro y
  obtain ⟨W, hW, hfin⟩ := hf.exists_mem_nhdsSet_finite (hfib y)
  obtain ⟨V, hV, hVW⟩ := Filter.mem_comap.1 (hg.comap_nhds_le hW)
  exact ⟨V, hV, hfin.subset fun i ⟨_, ⟨x, hx, rfl⟩, hxV⟩ ↦ ⟨x, hx, hVW hxV⟩⟩

/-- The topological multiplicative support of a product of functions with locally finite
multiplicative supports lies in the union of their topological multiplicative supports. -/
@[to_additive /-- The topological support of a sum of functions with locally finite supports lies
in the union of their topological supports. -/]
theorem mulTSupport_finprod_subset {M : Type*} [CommMonoid M] {b : ι → X → M}
    (hb : LocallyFinite fun i ↦ Function.mulSupport (b i)) :
    mulTSupport (fun x ↦ ∏ᶠ i, b i x) ⊆ ⋃ i, mulTSupport (b i) := by
  refine (closure_mono fun x hx ↦ ?_).trans hb.closure_iUnion.subset
  by_contra h
  exact hx (finprod_eq_one_of_forall_eq_one fun i ↦
    Function.notMem_mulSupport.1 fun hi ↦ h (mem_iUnion.2 ⟨i, hi⟩))

end LocallyFinite

namespace TauCeti

open Metric Set

/-- Around each point there is a ball such that every member of a locally finite family of closed
sets that meets the ball contains the centre. -/
theorem exists_pos_forall_mem_of_mem_ball {X ι : Type*} [PseudoMetricSpace X]
    {s : ι → Set X} (hs : ∀ i, IsClosed (s i)) (hlf : LocallyFinite s) (x : X) :
    ∃ r > 0, ∀ i, ∀ y ∈ ball x r, y ∈ s i → x ∈ s i := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hlf.eventually_subset hs x)
  exact ⟨r, hr, fun i y hy hys ↦ hball y hy hys⟩

end TauCeti

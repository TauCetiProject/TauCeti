/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Basic

/-!
# Products of Haar measures with values in a ring

Let `G` and `H` be Hausdorff topological groups and `μ`, `ν` Haar measures on them with values in
a semiring `A`. This file constructs the product Haar measure `μ.prod ν` on `G × H`, the unique
finitely additive volume on the compact open subsets of `G × H` with
`(μ.prod ν) (U ×ˢ V) = μ U * ν V` for all compact open `U ⊆ G` and `V ⊆ H`.

A compact open set `K ⊆ G × H` has compact open slices `K_g = {h | (g, h) ∈ K}`, and `g ↦ K_g` is
locally constant. So the finitely many nonempty slices `T` cut `G` into the compact open sets
`{g | K_g = T}`, and `K` is the disjoint union of the rectangles `{g | K_g = T} ×ˢ T`. The volume
of `K` is `∑ T, μ {g | K_g = T} * ν T`. Any presentation of `K` as a union of rectangles
`W i ×ˢ S i` with pairwise disjoint `W i` gives the same sum `∑ i, μ (W i) * ν (S i)`, which proves
additivity and invariance.

## Main definitions

* `TopologicalSpace.CompactOpens.slice`: the slice `{y | (x, y) ∈ K}` of a compact open set
  `K ⊆ X × Y` at `x : X`.
* `TauCeti.HaarMeasureWithValues.prod`: the product of two `A`-valued Haar measures.

## Main results

* `TopologicalSpace.CompactOpens.isLocallyConstant_slice`: the slices of a compact open subset of
  a product of Hausdorff spaces are locally constant.
* `TauCeti.HaarMeasureWithValues.prod_apply_prod`: `(μ.prod ν) (U ×ˢ V) = μ U * ν V`.
* `TauCeti.HaarMeasureWithValues.eq_prod_of_apply_prod`: an `A`-valued Haar measure on `G × H`
  with these volumes on rectangles is `μ.prod ν`.
-/

public section

open Set TopologicalSpace
open scoped Pointwise

namespace TopologicalSpace.CompactOpens

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The slice `{y | (x, y) ∈ K}` of a compact open subset `K` of `X × Y` at `x : X`, a compact open
subset of `Y` when the points of `X` are closed. -/
def slice [T1Space X] (K : CompactOpens (X × Y)) (x : X) : CompactOpens Y where
  carrier := Prod.mk x ⁻¹' K
  isCompact' := (isInducing_prodMkRight x).isCompact_preimage
    (isClosedMap_prodMk_left x).isClosed_range K.isCompact
  isOpen' := K.isOpen.preimage (Continuous.prodMk_right x)

@[simp]
theorem mem_slice [T1Space X] {K : CompactOpens (X × Y)} {x : X} {y : Y} :
    y ∈ K.slice x ↔ (x, y) ∈ K :=
  Iff.rfl

/-- The slices of a compact open subset of a product of Hausdorff spaces are locally constant. -/
theorem isLocallyConstant_slice [T2Space X] [T2Space Y] (K : CompactOpens (X × Y)) :
    IsLocallyConstant K.slice := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ ↦ ?_
  -- A tube around `{x₀} ×ˢ K_{x₀}` inside `K`, and one around the rest of `{x₀} ×ˢ (snd '' K)`
  -- outside `K`.
  obtain ⟨u, v, hu, -, hxu, hv, huv⟩ := generalized_tube_lemma isCompact_singleton
    (K.slice x₀).isCompact K.isOpen fun p hp ↦ by
      obtain ⟨hx, hy⟩ := mem_prod.1 hp
      rw [← Prod.mk.eta (p := p), mem_singleton_iff.1 hx]
      exact hy
  obtain ⟨u', v', hu', -, hxu', hv', huv'⟩ := generalized_tube_lemma isCompact_singleton
    ((K.isCompact.image continuous_snd).diff (K.slice x₀).isOpen)
    K.isCompact.isClosed.isOpen_compl fun p hp ↦ by
      obtain ⟨hx, -, hy⟩ := mem_prod.1 hp
      rw [← Prod.mk.eta (p := p), mem_singleton_iff.1 hx]
      exact hy
  filter_upwards [hu.mem_nhds (hxu (mem_singleton x₀)), hu'.mem_nhds (hxu' (mem_singleton x₀))]
    with x hx hx'
  refine CompactOpens.ext (Set.ext fun y ↦ ⟨fun hy ↦ ?_, fun hy ↦ huv ⟨hx, hv hy⟩⟩)
  by_contra hy₀
  exact huv' ⟨hx', hv' ⟨⟨_, hy, rfl⟩, hy₀⟩⟩ hy

/-- The slice of a compact open subset `K` of `X × Y` at a point outside the projection of `K` is
empty. -/
theorem slice_eq_bot_of_notMem [T1Space X] {K : CompactOpens (X × Y)} {x : X}
    (hx : x ∉ Prod.fst '' (K : Set (X × Y))) : K.slice x = ⊥ :=
  CompactOpens.ext <| Set.eq_empty_of_forall_notMem fun _ hy ↦ hx ⟨_, hy, rfl⟩

end TopologicalSpace.CompactOpens

namespace TauCeti.HaarMeasureWithValues

/-! ### Fibers of locally constant functions -/

section Fiber

variable {X β : Type*} [TopologicalSpace X]

/-- A locally constant function takes finitely many values on a compact set. -/
private theorem finite_image_of_isLocallyConstant {f : X → β} (hf : IsLocallyConstant f)
    {c : Set X} (hc : IsCompact c) : (f '' c).Finite := by
  have := isCompact_iff_compactSpace.1 hc
  rw [image_eq_range]
  exact (hf.comp_continuous continuous_subtypeVal).range_finite

/-- The fiber of a locally constant function `f` over a value `b` other than the value `b₀` that
`f` takes off a compact set, as a compact open set; it is empty for `b = b₀`. -/
private def fiber {f : X → β} (hf : IsLocallyConstant f) {c : Set X} (hc : IsCompact c) {b₀ : β}
    (hfc : ∀ x ∉ c, f x = b₀) (b : β) : CompactOpens X where
  carrier := {x | f x = b ∧ b ≠ b₀}
  isCompact' := hc.of_isClosed_subset ((hf.isClosed_fiber b).inter isClosed_const)
    fun x hx ↦ by_contra fun hxc ↦ hx.2 (hx.1 ▸ hfc x hxc)
  isOpen' := (hf.isOpen_fiber b).inter isOpen_const

variable {f : X → β} (hf : IsLocallyConstant f) {c : Set X} (hc : IsCompact c) {b₀ : β}
  (hfc : ∀ x ∉ c, f x = b₀)

private theorem mem_fiber {b : β} {x : X} : x ∈ fiber hf hc hfc b ↔ f x = b ∧ b ≠ b₀ :=
  Iff.rfl

private theorem pairwiseDisjoint_fiber (s : Set β) :
    s.PairwiseDisjoint fun b ↦ (fiber hf hc hfc b : Set X) :=
  fun _ _ _ _ hbb' ↦ Set.disjoint_left.2 fun _ hx hx' ↦ hbb' (hx.1.symm.trans hx'.1)

end Fiber

/-! ### Presentations of compact open sets as unions of rectangles -/

section Presentation

variable {G H : Type*} [TopologicalSpace G] [TopologicalSpace H]

/-- If `K` is the union of the rectangles `W i ×ˢ S i` with pairwise disjoint `W i`, then the
slice of `K` at a point of `W i` is `S i`. -/
private theorem eq_slice [T1Space G] {K : CompactOpens (G × H)} {ι : Type*} {s : Finset ι}
    {W : ι → CompactOpens G} {S : ι → CompactOpens H}
    (hW : (s : Set ι).PairwiseDisjoint fun i ↦ (W i : Set G))
    (hK : ∀ g h, (g, h) ∈ K ↔ ∃ i ∈ s, g ∈ W i ∧ h ∈ S i) {i : ι} (hi : i ∈ s) {g : G}
    (hg : g ∈ W i) : S i = K.slice g := by
  refine CompactOpens.ext (Set.ext fun h ↦ ?_)
  simp only [SetLike.mem_coe, CompactOpens.mem_slice, hK]
  refine ⟨fun hh ↦ ⟨i, hi, hg, hh⟩, ?_⟩
  rintro ⟨j, hj, hgj, hhj⟩
  rwa [hW.elim_set hi hj g hg hgj]

/-- The canonical presentation of `K` by the fibers of its slices. -/
private theorem mem_iff_exists_fiber {β : Type*} {f : G → β} (hf : IsLocallyConstant f) {c : Set G}
    (hc : IsCompact c) {b₀ : β} (hfc : ∀ x ∉ c, f x = b₀) (π : β → CompactOpens H)
    (hπ : π b₀ = ⊥) {K : CompactOpens (G × H)} (hK : ∀ g h, (g, h) ∈ K ↔ h ∈ π (f g))
    {P : Finset β} (hP : ∀ g ∈ c, f g ∈ P) (g : G) (h : H) :
    (g, h) ∈ K ↔ ∃ p ∈ P, g ∈ fiber hf hc hfc p ∧ h ∈ π p := by
  rw [hK]
  refine ⟨fun hh ↦ ?_, fun ⟨p, _, hgp, hh⟩ ↦ (mem_fiber hf hc hfc).1 hgp |>.1 ▸ hh⟩
  have hb : f g ≠ b₀ := fun hb ↦ by
    rw [hb, hπ] at hh
    exact hh
  exact ⟨f g, hP g (by_contra fun hg ↦ hb (hfc g hg)), (mem_fiber hf hc hfc).2 ⟨rfl, hb⟩, hh⟩

/-- The finitely many slices of `K` at the points of its projection to `G`. -/
private noncomputable def slices [T2Space G] [T2Space H] (K : CompactOpens (G × H)) :
    Finset (CompactOpens H) :=
  (finite_image_of_isLocallyConstant K.isLocallyConstant_slice
    (K.isCompact.image continuous_fst)).toFinset

private theorem slice_eq_bot [T1Space G] (K : CompactOpens (G × H)) :
    ∀ g ∉ Prod.fst '' (K : Set (G × H)), K.slice g = ⊥ :=
  fun _ ↦ CompactOpens.slice_eq_bot_of_notMem

/-- The compact open set of points of `G` at which `K` has slice `T`, for `T` nonempty. -/
private noncomputable def sliceFiber [T2Space G] [T2Space H] (K : CompactOpens (G × H))
    (T : CompactOpens H) : CompactOpens G :=
  fiber K.isLocallyConstant_slice (K.isCompact.image continuous_fst) (slice_eq_bot K) T

private theorem mem_iff_exists_sliceFiber [T2Space G] [T2Space H] (K : CompactOpens (G × H))
    (g : G) (h : H) :
    (g, h) ∈ K ↔ ∃ T ∈ slices K, g ∈ sliceFiber K T ∧ h ∈ T :=
  mem_iff_exists_fiber _ _ _ id rfl (fun _ _ ↦ Iff.rfl)
    (fun _ hg ↦ (Set.Finite.mem_toFinset _).2 (mem_image_of_mem _ hg)) g h

private theorem pairwiseDisjoint_sliceFiber [T2Space G] [T2Space H] (K : CompactOpens (G × H)) :
    ((slices K : Finset (CompactOpens H)) : Set (CompactOpens H)).PairwiseDisjoint
      fun T ↦ (sliceFiber K T : Set G) :=
  pairwiseDisjoint_fiber _ _ _ _

private theorem exists_mem_of_ne_bot {T : CompactOpens H} (hT : T ≠ ⊥) : ∃ h, h ∈ T := by
  by_contra! hT'
  exact hT (CompactOpens.ext (Set.eq_empty_of_forall_notMem hT'))

variable {A : Type*} [Group G] [IsTopologicalGroup G] [Group H] [IsTopologicalGroup H]
  [NonUnitalNonAssocSemiring A] (μ : HaarMeasureWithValues A G) (ν : HaarMeasureWithValues A H)

/-- Refining a presentation of `K` by a second one leaves the sum of volumes of its rectangles
unchanged. -/
private theorem sum_eq_sum_sum_inf [T2Space G] {K : CompactOpens (G × H)} {ι κ : Type*}
    {s : Finset ι}
    {W : ι → CompactOpens G} {S : ι → CompactOpens H}
    (hK : ∀ g h, (g, h) ∈ K ↔ ∃ i ∈ s, g ∈ W i ∧ h ∈ S i) {t : Finset κ}
    {W' : κ → CompactOpens G} {S' : κ → CompactOpens H}
    (hW' : (t : Set κ).PairwiseDisjoint fun j ↦ (W' j : Set G))
    (hK' : ∀ g h, (g, h) ∈ K ↔ ∃ j ∈ t, g ∈ W' j ∧ h ∈ S' j) :
    ∑ i ∈ s, μ (W i) * ν (S i) = ∑ i ∈ s, ∑ j ∈ t, μ (W i ⊓ W' j) * ν (S i) := by
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  by_cases hS : S i = ⊥
  · simp [hS]
  obtain ⟨h, hh⟩ := exists_mem_of_ne_bot hS
  -- Every point of `W i` lies in some `W' j`, since `(g, h) ∈ K`.
  have hWi : W i = t.sup fun j ↦ W i ⊓ W' j := by
    refine CompactOpens.ext (Set.ext fun g ↦ ?_)
    simp only [CompactOpens.coe_finsetSup, CompactOpens.coe_inf, mem_iUnion, mem_inter_iff,
      SetLike.mem_coe, exists_prop]
    refine ⟨fun hg ↦ ?_, fun ⟨_, _, hg, _⟩ ↦ hg⟩
    obtain ⟨j, hj, hgj, -⟩ := (hK' g h).1 ((hK g h).2 ⟨i, hi, hg, hh⟩)
    exact ⟨j, hj, hg, hgj⟩
  rw [← Finset.sum_mul, ← μ.apply_finsetSup (hW'.mono fun j ↦ inter_subset_right), ← hWi]

/-- **Independence of the presentation.** Any two presentations of `K` as a union of rectangles
with pairwise disjoint bases give the same sum of products of volumes. -/
private theorem sum_eq_sum [T2Space G] {K : CompactOpens (G × H)} {ι κ : Type*} {s : Finset ι}
    {W : ι → CompactOpens G} {S : ι → CompactOpens H}
    (hW : (s : Set ι).PairwiseDisjoint fun i ↦ (W i : Set G))
    (hK : ∀ g h, (g, h) ∈ K ↔ ∃ i ∈ s, g ∈ W i ∧ h ∈ S i) {t : Finset κ}
    {W' : κ → CompactOpens G} {S' : κ → CompactOpens H}
    (hW' : (t : Set κ).PairwiseDisjoint fun j ↦ (W' j : Set G))
    (hK' : ∀ g h, (g, h) ∈ K ↔ ∃ j ∈ t, g ∈ W' j ∧ h ∈ S' j) :
    ∑ i ∈ s, μ (W i) * ν (S i) = ∑ j ∈ t, μ (W' j) * ν (S' j) := by
  rw [sum_eq_sum_sum_inf μ ν hK hW' hK', sum_eq_sum_sum_inf μ ν hK' hW hK, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj ↦ Finset.sum_congr rfl fun i hi ↦ ?_
  rw [inf_comm (W' j)]
  by_cases hWW : W i ⊓ W' j = ⊥
  · simp [hWW]
  obtain ⟨g, hg⟩ := exists_mem_of_ne_bot hWW
  rw [eq_slice hW hK hi hg.1, eq_slice hW' hK' hj hg.2]

end Presentation

/-! ### The product measure -/

variable {A G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [NonUnitalNonAssocSemiring A]
  (μ : HaarMeasureWithValues A G) (ν : HaarMeasureWithValues A H)

/-- The product volume of a compact open set `K ⊆ G × H`: the sum over the nonempty slices `T` of
`K` of the volume of `{g | K_g = T}` times that of `T`. -/
private noncomputable def prodVolume (K : CompactOpens (G × H)) : A :=
  ∑ T ∈ slices K, μ (sliceFiber K T) * ν T

/-- The product volume of `K` is the sum of products of volumes over any presentation of `K` as a
union of rectangles with pairwise disjoint bases. -/
private theorem prodVolume_eq_sum {K : CompactOpens (G × H)} {ι : Type*} {s : Finset ι}
    {W : ι → CompactOpens G} {S : ι → CompactOpens H}
    (hW : (s : Set ι).PairwiseDisjoint fun i ↦ (W i : Set G))
    (hK : ∀ g h, (g, h) ∈ K ↔ ∃ i ∈ s, g ∈ W i ∧ h ∈ S i) :
    prodVolume μ ν K = ∑ i ∈ s, μ (W i) * ν (S i) :=
  sum_eq_sum μ ν (pairwiseDisjoint_sliceFiber K) (mem_iff_exists_sliceFiber K) hW hK

/-- The product volume is additive on disjoint compact open sets. -/
private theorem prodVolume_sup (K L : CompactOpens (G × H)) (hKL : Disjoint (K : Set (G × H)) L) :
    prodVolume μ ν (K ⊔ L) = prodVolume μ ν K + prodVolume μ ν L := by
  -- Present `K`, `L` and `K ⊔ L` over the fibers of the pair of slices `g ↦ (K_g, L_g)`.
  have hf := K.isLocallyConstant_slice.prodMk L.isLocallyConstant_slice
  have hc := (K.isCompact.image continuous_fst).union (L.isCompact.image continuous_fst)
  have hfc : ∀ g ∉ Prod.fst '' (K : Set (G × H)) ∪ Prod.fst '' (L : Set (G × H)),
      (K.slice g, L.slice g) = (⊥, ⊥) := fun g hg ↦ by
    rw [mem_union, not_or] at hg
    rw [slice_eq_bot K g hg.1, slice_eq_bot L g hg.2]
  have hP := finite_image_of_isLocallyConstant hf hc
  have hmem : ∀ g ∈ Prod.fst '' (K : Set (G × H)) ∪ Prod.fst '' (L : Set (G × H)),
      (K.slice g, L.slice g) ∈ hP.toFinset :=
    fun g hg ↦ (Set.Finite.mem_toFinset _).2 (mem_image_of_mem _ hg)
  have hW := pairwiseDisjoint_fiber hf hc hfc (hP.toFinset : Set _)
  rw [prodVolume_eq_sum μ ν hW (mem_iff_exists_fiber hf hc hfc (fun p ↦ p.1 ⊔ p.2) (bot_sup_eq _)
      (fun _ _ ↦ Iff.rfl) hmem),
    prodVolume_eq_sum μ ν hW (mem_iff_exists_fiber hf hc hfc Prod.fst rfl (fun _ _ ↦ Iff.rfl) hmem),
    prodVolume_eq_sum μ ν hW (mem_iff_exists_fiber hf hc hfc Prod.snd rfl (fun _ _ ↦ Iff.rfl) hmem),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hp : fiber hf hc hfc p = ⊥
  · simp [hp]
  obtain ⟨g, hg⟩ := exists_mem_of_ne_bot hp
  obtain ⟨rfl, -⟩ := (mem_fiber hf hc hfc).1 hg
  rw [ν.apply_sup (Set.disjoint_left.2 fun h hK hL ↦ Set.disjoint_left.1 hKL hK hL), mul_add]

/-- The product volume is invariant under left translation. -/
private theorem prodVolume_smul (x : G × H) (K : CompactOpens (G × H)) :
    prodVolume μ ν (x • K) = prodVolume μ ν K := by
  have hW : ((slices K : Finset (CompactOpens H)) : Set (CompactOpens H)).PairwiseDisjoint
      fun T ↦ ((x.1 • sliceFiber K T : CompactOpens G) : Set G) :=
    fun T hT T' hT' hTT' ↦ by
      simpa only [CompactOpens.coe_smul] using
        Set.disjoint_smul_set.2 (pairwiseDisjoint_sliceFiber K hT hT' hTT')
  rw [prodVolume_eq_sum μ ν hW (S := fun T ↦ x.2 • T) fun g h ↦ ?_]
  · simp only [apply_smul]
    rfl
  obtain ⟨a, b⟩ := x
  simp only [CompactOpens.mem_smul_iff_inv_smul_mem, Prod.inv_mk, smul_eq_mul, Prod.mk_mul_mk,
    mem_iff_exists_sliceFiber K]

/-- The **product** of an `A`-valued Haar measure `μ` on `G` and an `A`-valued Haar measure `ν` on
`H`: the `A`-valued Haar measure on `G × H` giving a compact open rectangle `U ×ˢ V` volume
`μ U * ν V` (`TauCeti.HaarMeasureWithValues.prod_apply_prod`), and determined by these volumes
(`TauCeti.HaarMeasureWithValues.eq_prod_of_apply_prod`). -/
noncomputable def prod : HaarMeasureWithValues A (G × H) where
  toFun := prodVolume μ ν
  map_bot' := by
    rw [prodVolume_eq_sum μ ν (s := (∅ : Finset Unit)) (W := fun _ ↦ ⊥) (S := fun _ ↦ ⊥)
      (by simp) fun g h ↦ ?_]
    · simp
    simp only [Finset.notMem_empty, false_and, exists_false, iff_false]
    exact id
  map_sup' := prodVolume_sup μ ν
  map_smul' := prodVolume_smul μ ν

/-- The product measure gives a compact open rectangle `U ×ˢ V` volume `μ U * ν V`. -/
@[simp]
theorem prod_apply_prod (U : CompactOpens G) (V : CompactOpens H) :
    μ.prod ν (U ×ˢ V) = μ U * ν V := by
  change prodVolume μ ν _ = _
  rw [prodVolume_eq_sum μ ν (s := Finset.univ) (W := fun _ : Unit ↦ U) (S := fun _ ↦ V)
    (by simp) fun g h ↦ by
      rw [← SetLike.mem_coe, CompactOpens.coe_prod]
      simp]
  simp

/-- **Uniqueness of the product measure.** An `A`-valued Haar measure on `G × H` that gives every
compact open rectangle `U ×ˢ V` volume `μ U * ν V` is the product measure `μ.prod ν`. -/
theorem eq_prod_of_apply_prod (ρ : HaarMeasureWithValues A (G × H))
    (hρ : ∀ U V, ρ (U ×ˢ V) = μ U * ν V) : ρ = μ.prod ν := by
  refine ext fun K ↦ ?_
  have hK : K = (slices K).sup fun T ↦ sliceFiber K T ×ˢ T := by
    refine CompactOpens.ext (Set.ext fun ⟨g, h⟩ ↦ ?_)
    simp only [CompactOpens.coe_finsetSup, CompactOpens.coe_prod, mem_iUnion, mem_prod,
      SetLike.mem_coe, exists_prop]
    exact mem_iff_exists_sliceFiber K g h
  change ρ K = prodVolume μ ν K
  conv_lhs => rw [hK]
  rw [ρ.apply_finsetSup fun T hT T' hT' hTT' ↦ ?_]
  · simp only [hρ]
    rfl
  simpa only [CompactOpens.coe_prod] using
    Set.disjoint_prod.2 (Or.inl (pairwiseDisjoint_sliceFiber K hT hT' hTT'))

end TauCeti.HaarMeasureWithValues

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Basic
public import TauCeti.Topology.Sets.CompactOpens
public import TauCeti.Topology.Sets.Compacts

/-!
# Products of Haar measures with values in a ring

Let `G` and `H` be Hausdorff topological groups and `μ`, `ν` Haar measures on them with values in
a semiring `A`. This file constructs the product Haar measure `μ.prod ν` on `G × H`, the unique
`A`-valued Haar measure on `G × H` with `(μ.prod ν) (U ×ˢ V) = μ U * ν V` for all compact open
`U ⊆ G` and `V ⊆ H`.

A compact open set `K ⊆ G × H` has compact open slices `K_g = {h | (g, h) ∈ K}`
(`TopologicalSpace.CompactOpens.slice`), and `g ↦ K_g` is locally constant. So the finitely many
nonempty slices `T` cut `G` into the compact open sets `{g | K_g = T}`, and `K` is the disjoint
union of the rectangles `{g | K_g = T} ×ˢ T`. The volume of `K` is `∑ T, μ {g | K_g = T} * ν T`.
Any presentation of `K` as a union of rectangles `W i ×ˢ S i` with pairwise disjoint `W i` gives
the same sum `∑ i, μ (W i) * ν (S i)`, which proves additivity and invariance.

## Main definitions

* `TauCeti.HaarMeasureWithValues.prod`: the product of two `A`-valued Haar measures.

## Main results

* `TauCeti.HaarMeasureWithValues.prod_apply_prod`: `(μ.prod ν) (U ×ˢ V) = μ U * ν V`.
* `TauCeti.HaarMeasureWithValues.prod_apply_eq_sum_slices`,
  `TauCeti.HaarMeasureWithValues.prod_apply_eq_sum`: the volume of a general compact open set, as a
  sum over its slices or over any presentation by rectangles with pairwise disjoint bases.
* `TauCeti.HaarMeasureWithValues.eq_prod_of_apply_prod`: an `A`-valued Haar measure on `G × H`
  with these volumes on rectangles is `μ.prod ν`.
* `TauCeti.HaarMeasureWithValues.prod_apply_swap`: for a commutative `A`, exchanging the factors
  carries `ν.prod μ` to `μ.prod ν`, `(ν.prod μ) (K.swap) = (μ.prod ν) K`.

## References

* C. J. Bushnell and G. Henniart, *The Local Langlands Conjecture for GL(2)*, §3.2, pp. 28–29, for
  products of Haar measures on locally profinite groups; the ring-valued version here follows the
  same decomposition of compact open sets into finitely many rectangles.
-/

public section

open Set TopologicalSpace
open scoped Pointwise

namespace TauCeti.HaarMeasureWithValues

/-! ### Presentations of compact open sets as unions of rectangles -/

section Presentation

variable {A G H : Type*} [TopologicalSpace G] [TopologicalSpace H] [Group G] [ContinuousMul G]
  [Group H] [ContinuousMul H] [NonUnitalNonAssocSemiring A]
  (μ : HaarMeasureWithValues A G) (ν : HaarMeasureWithValues A H)

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
  obtain ⟨h, hh⟩ := CompactOpens.coe_nonempty.2 hS
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
  obtain ⟨g, hg⟩ := CompactOpens.coe_nonempty.2 hWW
  rw [← CompactOpens.slice_eq_of_mem hW hK hi hg.1,
    ← CompactOpens.slice_eq_of_mem hW' hK' hj hg.2]

end Presentation

/-! ### The product measure -/

section Prod

variable {A G H : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [T2Space G]
  [Group H] [TopologicalSpace H] [ContinuousMul H] [T2Space H] [NonUnitalNonAssocSemiring A]
  (μ : HaarMeasureWithValues A G) (ν : HaarMeasureWithValues A H)

/-- The product volume of a compact open set `K ⊆ G × H`: the sum over the nonempty slices `T` of
`K` of the volume of `{g | K_g = T}` times that of `T`. -/
private noncomputable def prodVolume (K : CompactOpens (G × H)) : A :=
  ∑ T ∈ K.slices, μ (K.sliceFiber T) * ν T

/-- The product volume of `K` is the sum of products of volumes over any presentation of `K` as a
union of rectangles with pairwise disjoint bases. -/
private theorem prodVolume_eq_sum {K : CompactOpens (G × H)} {ι : Type*} {s : Finset ι}
    {W : ι → CompactOpens G} {S : ι → CompactOpens H}
    (hW : (s : Set ι).PairwiseDisjoint fun i ↦ (W i : Set G))
    (hK : ∀ g h, (g, h) ∈ K ↔ ∃ i ∈ s, g ∈ W i ∧ h ∈ S i) :
    prodVolume μ ν K = ∑ i ∈ s, μ (W i) * ν (S i) :=
  sum_eq_sum μ ν K.pairwiseDisjoint_sliceFiber K.mem_iff_exists_sliceFiber hW hK

/-- The product volume is additive on disjoint compact open sets. -/
private theorem prodVolume_sup (K L : CompactOpens (G × H)) (hKL : Disjoint (K : Set (G × H)) L) :
    prodVolume μ ν (K ⊔ L) = prodVolume μ ν K + prodVolume μ ν L := by
  -- Present `K`, `L` and `K ⊔ L` over the fibers of the pair of slices `g ↦ (K_g, L_g)`.
  have hf := K.isLocallyConstant_slice.prodMk L.isLocallyConstant_slice
  have hc := (K.isCompact.image continuous_fst).union (L.isCompact.image continuous_fst)
  have hfc : ∀ g ∉ Prod.fst '' (K : Set (G × H)) ∪ Prod.fst '' (L : Set (G × H)),
      (K.slice g, L.slice g) = (⊥, ⊥) := fun g hg ↦ by
    rw [mem_union, not_or] at hg
    rw [CompactOpens.slice_eq_bot_of_notMem hg.1, CompactOpens.slice_eq_bot_of_notMem hg.2]
  have hP := hf.finite_image_of_isCompact hc
  have hmem : ∀ g ∈ Prod.fst '' (K : Set (G × H)) ∪ Prod.fst '' (L : Set (G × H)),
      (K.slice g, L.slice g) ∈ hP.toFinset :=
    fun g hg ↦ (Set.Finite.mem_toFinset _).2 (mem_image_of_mem _ hg)
  have hW := hf.pairwiseDisjoint_fiberCompactOpens hc hfc (hP.toFinset : Set _)
  rw [prodVolume_eq_sum μ ν hW (hf.mem_iff_exists_fiberCompactOpens hc hfc (fun p ↦ p.1 ⊔ p.2)
      (bot_sup_eq _)
      (fun _ _ ↦ by rw [← CompactOpens.slice_sup, CompactOpens.mem_slice]) hmem),
    prodVolume_eq_sum μ ν hW (hf.mem_iff_exists_fiberCompactOpens hc hfc Prod.fst rfl
      (fun _ _ ↦ CompactOpens.mem_slice.symm) hmem),
    prodVolume_eq_sum μ ν hW (hf.mem_iff_exists_fiberCompactOpens hc hfc Prod.snd rfl
      (fun _ _ ↦ CompactOpens.mem_slice.symm) hmem),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hp : hf.fiberCompactOpens hc hfc p = ⊥
  · simp [hp]
  obtain ⟨g, hg⟩ := CompactOpens.coe_nonempty.2 hp
  obtain ⟨rfl, -⟩ := (hf.mem_fiberCompactOpens hc hfc).1 hg
  rw [ν.apply_sup (Set.disjoint_left.2 fun h hK hL ↦
    Set.disjoint_left.1 hKL (CompactOpens.mem_slice.1 hK) (CompactOpens.mem_slice.1 hL)), mul_add]

/-- The product volume is invariant under left translation. -/
private theorem prodVolume_smul (x : G × H) (K : CompactOpens (G × H)) :
    prodVolume μ ν (x • K) = prodVolume μ ν K := by
  have hW : ((K.slices : Finset (CompactOpens H)) : Set (CompactOpens H)).PairwiseDisjoint
      fun T ↦ ((x.1 • K.sliceFiber T : CompactOpens G) : Set G) :=
    fun T hT T' hT' hTT' ↦ by
      simpa only [CompactOpens.coe_smul] using
        Set.disjoint_smul_set.2 (K.pairwiseDisjoint_sliceFiber hT hT' hTT')
  rw [prodVolume_eq_sum μ ν hW (S := fun T ↦ x.2 • T) fun g h ↦ ?_]
  · simp only [apply_smul, prodVolume]
  obtain ⟨a, b⟩ := x
  simp only [CompactOpens.mem_smul_iff_inv_smul_mem, Prod.inv_mk, smul_eq_mul, Prod.mk_mul_mk,
    K.mem_iff_exists_sliceFiber]

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
    simp [← SetLike.mem_coe]
  map_sup' := prodVolume_sup μ ν
  map_smul' := prodVolume_smul μ ν

private theorem prod_apply (K : CompactOpens (G × H)) : μ.prod ν K = prodVolume μ ν K := by
  rw [prod, coe_mk]

/-- The product measure of a compact open set `K ⊆ G × H` is the sum over the slices `T` of `K` of
the volume of `{g | K_g = T}` times that of `T`. -/
theorem prod_apply_eq_sum_slices (K : CompactOpens (G × H)) :
    μ.prod ν K = ∑ T ∈ K.slices, μ (K.sliceFiber T) * ν T := by
  rw [prod_apply, prodVolume]

/-- The product measure of a compact open set `K ⊆ G × H` is the sum of products of volumes over
any presentation of `K` as a union of rectangles with pairwise disjoint bases. -/
theorem prod_apply_eq_sum {K : CompactOpens (G × H)} {ι : Type*} {s : Finset ι}
    {W : ι → CompactOpens G} {S : ι → CompactOpens H}
    (hW : (s : Set ι).PairwiseDisjoint fun i ↦ (W i : Set G))
    (hK : ∀ g h, (g, h) ∈ K ↔ ∃ i ∈ s, g ∈ W i ∧ h ∈ S i) :
    μ.prod ν K = ∑ i ∈ s, μ (W i) * ν (S i) := by
  rw [prod_apply, prodVolume_eq_sum μ ν hW hK]

/-- The product measure gives a compact open rectangle `U ×ˢ V` volume `μ U * ν V`. -/
@[simp]
theorem prod_apply_prod (U : CompactOpens G) (V : CompactOpens H) :
    μ.prod ν (U ×ˢ V) = μ U * ν V := by
  rw [prod_apply_eq_sum μ ν (s := Finset.univ) (W := fun _ : Unit ↦ U) (S := fun _ ↦ V)
    (by simp) fun g h ↦ by
      rw [← SetLike.mem_coe, CompactOpens.coe_prod]
      simp]
  simp

/-- **Uniqueness of the product measure.** An `A`-valued Haar measure on `G × H` that gives every
compact open rectangle `U ×ˢ V` volume `μ U * ν V` is the product measure `μ.prod ν`. -/
theorem eq_prod_of_apply_prod (ρ : HaarMeasureWithValues A (G × H))
    (hρ : ∀ U V, ρ (U ×ˢ V) = μ U * ν V) : ρ = μ.prod ν := by
  refine ext fun K ↦ ?_
  rw [prod_apply_eq_sum_slices]
  conv_lhs => rw [K.eq_finsetSup_sliceFiber_prod]
  rw [ρ.apply_finsetSup fun T hT T' hT' hTT' ↦ ?_]
  · simp only [hρ]
  simpa only [CompactOpens.coe_prod] using
    Set.disjoint_prod.2 (Or.inl (K.pairwiseDisjoint_sliceFiber hT hT' hTT'))

@[simp]
theorem zero_prod : (0 : HaarMeasureWithValues A G).prod ν = 0 :=
  (eq_prod_of_apply_prod _ _ 0 fun _ _ ↦ by simp).symm

@[simp]
theorem prod_zero : μ.prod (0 : HaarMeasureWithValues A H) = 0 :=
  (eq_prod_of_apply_prod _ _ 0 fun _ _ ↦ by simp).symm

end Prod

/-! ### Exchanging the factors -/

section Swap

variable {A G H : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [T2Space G]
  [Group H] [TopologicalSpace H] [ContinuousMul H] [T2Space H] [NonUnitalNonAssocCommSemiring A]

/-- The volume `K ↦ (ν.prod μ)(K.swap)` on `G × H`, an `A`-valued Haar measure. -/
private noncomputable def swapProd (μ : HaarMeasureWithValues A G)
    (ν : HaarMeasureWithValues A H) : HaarMeasureWithValues A (G × H) where
  toFun K := ν.prod μ K.swap
  map_bot' := (congrArg (ν.prod μ) CompactOpens.swap_bot).trans (apply_bot _)
  map_sup' K L hKL := (congrArg (ν.prod μ) (CompactOpens.swap_sup K L)).trans <|
    apply_sup _ (by simpa only [CompactOpens.coe_swap] using hKL.preimage Prod.swap)
  map_smul' x K := (congrArg (ν.prod μ) (CompactOpens.swap_smul x K)).trans (apply_smul _ _ _)

private theorem swapProd_apply (μ : HaarMeasureWithValues A G) (ν : HaarMeasureWithValues A H)
    (K : CompactOpens (G × H)) : swapProd μ ν K = ν.prod μ K.swap := by
  rw [swapProd, coe_mk]

/-- **Exchanging the factors of a product measure.** For a commutative `A`, the volume under
`ν.prod μ` of the image `K.swap` of `K ⊆ G × H` under `(g, h) ↦ (h, g)` is the volume of `K` under
`μ.prod ν`. -/
theorem prod_apply_swap (μ : HaarMeasureWithValues A G) (ν : HaarMeasureWithValues A H)
    (K : CompactOpens (G × H)) : ν.prod μ K.swap = μ.prod ν K := by
  -- `K ↦ (ν.prod μ)(K.swap)` is a Haar measure on `G × H` with the volumes of `μ.prod ν` on
  -- rectangles.
  rw [← swapProd_apply, eq_prod_of_apply_prod μ ν (swapProd μ ν) fun U V ↦ by
    rw [swapProd_apply, CompactOpens.swap_prod, prod_apply_prod, mul_comm]]

end Swap

end TauCeti.HaarMeasureWithValues

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import TauCeti.Analysis.Normed.Ring.InfiniteProd

/-!
# Locally uniform infinite products `∏' i, (1 + u i x)` in normed rings

Extensions of Mathlib's `Summable.hasProdUniformlyOn_one_add`
(`Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn`), `tprod_one_add_ne_zero_of_summable`
(`Mathlib.Analysis.SpecialFunctions.Log.Summable`), and `TauCeti.Analysis.Normed.Ring.InfiniteProd`
for families `u : ι → α → R` admitting summable cofinite majorants on compact subsets of `U ⊆ α`.

## Main results

* `TauCeti.exists_summable_cofinite_subtype`, `TauCeti.summable_norm_of_forall_compact`:
  subtype restriction and pointwise absolute summability from compact-set cofinite majorants.
* `TauCeti.hasProdLocallyUniformlyOn_one_add_of_forall_compact`: locally uniform convergence of
  `∏' i, (1 + u i x)` on an open set from compact-set cofinite majorants.
* `TauCeti.hasProdUniformlyOn_one_add_of_summable_sSup`,
  `TauCeti.exists_summable_cofinite_of_summable_sSup`,
  `TauCeti.hasProdLocallyUniformlyOn_one_add_of_summable_sSup`: uniform and locally uniform
  convergence from compact-supremum summability `∑' i, sup_{x ∈ K} ‖u i x‖ < ∞`.
* `TauCeti.tprod_one_add_eq_zero_iff`, `TauCeti.finite_one_add_eq_zero`,
  `TauCeti.tprod_one_add_compl_ne_zero`: pointwise vanishing, finiteness of vanishing factors, and
  nonvanishing of complementary tail products at each `x ∈ U`.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {ι α R : Type*}

/-- Passing to any subtype of the index type preserves the existence of summable cofinite majorants
on compact subsets. -/
theorem exists_summable_cofinite_subtype [TopologicalSpace α] [SeminormedAddCommGroup R]
    {U : Set α} {u : ι → α → R}
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ x ∈ K, ‖u i x‖ ≤ v i) (p : ι → Prop) :
    ∀ K ⊆ U, IsCompact K → ∃ v : Subtype p → ℝ, Summable v ∧
      ∀ᶠ i : Subtype p in cofinite, ∀ x ∈ K, ‖u i x‖ ≤ v i := by
  intro K hKU hK
  obtain ⟨v, hv, hbound⟩ := hsum K hKU hK
  exact ⟨fun i ↦ v i, hv.subtype p, Subtype.val_injective.tendsto_cofinite.eventually hbound⟩

/-- Compact-set cofinite majorants imply pointwise absolute summability at every point of `U`. -/
theorem summable_norm_of_forall_compact [TopologicalSpace α] [SeminormedAddCommGroup R]
    {U : Set α} {u : ι → α → R}
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ x ∈ K, ‖u i x‖ ≤ v i) {x : α} (hx : x ∈ U) :
    Summable fun i ↦ ‖u i x‖ := by
  obtain ⟨v, hv, hbound⟩ := hsum {x} (singleton_subset_iff.mpr hx) isCompact_singleton
  refine hv.of_norm_bounded_eventually ?_
  filter_upwards [hbound] with i hi
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact hi x (mem_singleton x)

/-- If continuous functions `u i` on an open set `U` in a locally compact space admit a summable
cofinite majorant on every compact subset of `U`, then `∏' i, (1 + u i x)` converges locally
uniformly on `U`. -/
theorem hasProdLocallyUniformlyOn_one_add_of_forall_compact [TopologicalSpace α]
    [LocallyCompactSpace α] [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {U : Set α} (hU : IsOpen U) {u : ι → α → R} (hcts : ∀ i, ContinuousOn (u i) U)
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ x ∈ K, ‖u i x‖ ≤ v i) :
    HasProdLocallyUniformlyOn (fun i x ↦ 1 + u i x) (fun x ↦ ∏' i, (1 + u i x)) U := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hU
  intro K hKU hK
  obtain ⟨v, hv, hbound⟩ := hsum K hKU hK
  exact hv.hasProdUniformlyOn_one_add hK hbound fun i ↦ (hcts i).mono hKU

/-- Summability of `sSup ((fun x ↦ ‖u i x‖) '' K)` for continuous `u i` on a compact set `K`
gives uniform convergence of `∏' i, (1 + u i x)` on `K`. -/
theorem hasProdUniformlyOn_one_add_of_summable_sSup [TopologicalSpace α]
    [NormedCommRing R] [NormOneClass R] [CompleteSpace R] {K : Set α} (hK : IsCompact K)
    {u : ι → α → R} (hcts : ∀ i, ContinuousOn (u i) K)
    (hsum : Summable fun i ↦ sSup ((fun x ↦ ‖u i x‖) '' K)) :
    HasProdUniformlyOn (fun i x ↦ 1 + u i x) (fun x ↦ ∏' i, (1 + u i x)) K :=
  hsum.hasProdUniformlyOn_one_add hK
    (Eventually.of_forall fun i _ hx ↦
      le_csSup (hK.image_of_continuousOn (hcts i).norm).bddAbove (mem_image_of_mem _ hx))
    hcts

/-- Summability of `sSup ((fun x ↦ ‖u i x‖) '' K)` on every compact subset `K ⊆ U` supplies a
summable majorant on every compact subset of `U`. -/
theorem exists_summable_cofinite_of_summable_sSup [TopologicalSpace α]
    [SeminormedAddCommGroup R] {U : Set α} {u : ι → α → R} (hcts : ∀ i, ContinuousOn (u i) U)
    (hsum : ∀ K ⊆ U, IsCompact K → Summable fun i ↦ sSup ((fun x ↦ ‖u i x‖) '' K)) :
    ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ x ∈ K, ‖u i x‖ ≤ v i :=
  fun K hKU hK ↦ ⟨_, hsum K hKU hK, Eventually.of_forall fun i _ hx ↦
    le_csSup (hK.image_of_continuousOn ((hcts i).mono hKU).norm).bddAbove (mem_image_of_mem _ hx)⟩

/-- If continuous functions `u i` on an open set `U` in a locally compact space satisfy
`∑' i, sup_{x ∈ K} ‖u i x‖ < ∞` on every compact `K ⊆ U`, then `∏' i, (1 + u i x)` converges
locally uniformly on `U`. -/
theorem hasProdLocallyUniformlyOn_one_add_of_summable_sSup [TopologicalSpace α]
    [LocallyCompactSpace α] [NormedCommRing R] [NormOneClass R] [CompleteSpace R]
    {U : Set α} (hU : IsOpen U) {u : ι → α → R} (hcts : ∀ i, ContinuousOn (u i) U)
    (hsum : ∀ K ⊆ U, IsCompact K → Summable fun i ↦ sSup ((fun x ↦ ‖u i x‖) '' K)) :
    HasProdLocallyUniformlyOn (fun i x ↦ 1 + u i x) (fun x ↦ ∏' i, (1 + u i x)) U :=
  hasProdLocallyUniformlyOn_one_add_of_forall_compact hU hcts
    (exists_summable_cofinite_of_summable_sSup hcts hsum)

/-- At each point `x ∈ U`, the product `∏' i, (1 + u i x)` vanishes if and only if some factor
`1 + u i x` vanishes. -/
theorem tprod_one_add_eq_zero_iff [TopologicalSpace α] [NormedCommRing R] [NormOneClass R]
    [NormMulClass R] [CompleteSpace R] {U : Set α} {u : ι → α → R}
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ y ∈ K, ‖u i y‖ ≤ v i) {x : α} (hx : x ∈ U) :
    (∏' i, (1 + u i x)) = 0 ↔ ∃ i, 1 + u i x = 0 :=
  tprod_one_add_eq_zero_iff_of_summable (summable_norm_of_forall_compact hsum hx)

/-- At each point `x ∈ U`, only finitely many factors `1 + u i x` vanish. -/
theorem finite_one_add_eq_zero [TopologicalSpace α] [NormedCommRing R] [NormOneClass R]
    {U : Set α} {u : ι → α → R}
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ y ∈ K, ‖u i y‖ ≤ v i) {x : α} (hx : x ∈ U) :
    {i | 1 + u i x = 0}.Finite :=
  finite_one_add_eq_zero_of_summable (summable_norm_of_forall_compact hsum hx)

/-- After extracting a finite set `s` containing all indices whose factor vanishes at `x ∈ U`, the
complementary product is nonzero at `x`. -/
theorem tprod_one_add_compl_ne_zero [TopologicalSpace α] [NormedCommRing R] [NormOneClass R]
    [NormMulClass R] [CompleteSpace R] {U : Set α} {u : ι → α → R}
    (hsum : ∀ K ⊆ U, IsCompact K → ∃ v : ι → ℝ, Summable v ∧
      ∀ᶠ i in cofinite, ∀ y ∈ K, ‖u i y‖ ≤ v i)
    {s : Finset ι} {x : α} (hx : x ∈ U) (hs : ∀ i, 1 + u i x = 0 → i ∈ s) :
    (∏' i : {i // i ∉ s}, (1 + u i x)) ≠ 0 :=
  tprod_one_add_compl_ne_zero_of_summable (summable_norm_of_forall_compact hsum hx) hs

end TauCeti

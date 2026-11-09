/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic

/-!
# Composites of covering maps

A composite of two covering maps need not be a covering map, but it is one as soon as the second
map has finite fibres. This holds pointwise: if `x` is evenly covered by `q : Y → X` with finite
fibre and every point over `x` is evenly covered by `p : E → Y`, then `x` is evenly covered by
`q ∘ p`. Over an evenly covered neighbourhood `U` of `x` for `q`, the finitely many sheets of `q`
over `U` each contain a point over `x`; each such point has an evenly covered neighbourhood for
`p`. Since there are finitely many sheets, `U` can be shrunk to
an open `W ∋ x` whose lifts to the sheets all land in those neighbourhoods. Each sheet of `p` over
the part of a sheet of `q` above `W` is then mapped homeomorphically onto `W` by `q ∘ p`.

No separation axiom is needed. The argument goes through the description of an evenly covered
neighbourhood by its sheets, `IsEvenlyCovered.exists_sheets`, and Mathlib's
`IsOpen.trivializationDiscrete`, which rebuilds a trivialization from such sheets.

## Main results

* `IsEvenlyCovered.exists_sheets`: an evenly covered neighbourhood is the disjoint union of open
  sheets, one for each element of the fibre type, each mapped homeomorphically onto it.
* `IsEvenlyCovered.comp`: a point evenly covered, with finite fibre, by the second map, all of
  whose lifts are evenly covered by the first map, is evenly covered by the composite.
* `IsCoveringMap.comp`: a covering map followed by a covering map with finite fibres is a
  covering map.
-/

public section

open Function Set Topology

namespace TauCeti

variable {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y] [TopologicalSpace X]

/-- An evenly covered neighbourhood is the disjoint union of its **sheets**: if `x` is evenly
covered by `f` with fibre `I`, then some open `U ∋ x` has preimage the union of pairwise disjoint
open sets `S i`, one for each `i : I`, each of which `f` maps homeomorphically onto `U`: `f` is
injective on `S i` with image `U`, and a subset `W ⊆ U` is open exactly when its preimage in
`S i` is. -/
theorem _root_.IsEvenlyCovered.exists_sheets {f : E → X} {x : X} {I : Type*}
    [TopologicalSpace I] (h : IsEvenlyCovered f x I) :
    ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ ∃ S : I → Set E, (∀ i, IsOpen (S i)) ∧
      (∀ i, (S i).InjOn f) ∧ (∀ i, f '' S i = U) ∧
      (∀ i, ∀ W ⊆ U, IsOpen W ↔ IsOpen (f ⁻¹' W ∩ S i)) ∧ Pairwise (Disjoint on S) ∧
        f ⁻¹' U = ⋃ i, S i := by
  obtain ⟨_, U, hxU, hU, hfU, H, hH⟩ := h
  -- The sheet indexed by `i` is the part of `f ⁻¹' U` that `H` sends to `U × {i}`.
  refine ⟨U, hxU, hU, fun i ↦ Subtype.val '' (H ⁻¹' (Prod.snd ⁻¹' {i})), fun i ↦ ?_, fun i ↦ ?_,
    fun i ↦ ?_, fun i W hW ↦ ?_, fun i j hij ↦ ?_, ?_⟩
  · exact hfU.isOpenMap_subtype_val _
      (((isOpen_discrete {i}).preimage continuous_snd).preimage H.continuous)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    refine congrArg Subtype.val (H.injective (Prod.ext (Subtype.ext ?_) ?_))
    · rw [hH, hH]
      exact hab
    · exact (mem_singleton_iff.mp ha).trans (mem_singleton_iff.mp hb).symm
  · ext u
    refine ⟨?_, fun hu ↦ ⟨_, ⟨H.symm (⟨u, hu⟩, i), by simp, rfl⟩, by simp [← hH]⟩⟩
    rintro ⟨_, ⟨a, -, rfl⟩, rfl⟩
    exact hH a ▸ (H a).1.2
  · have : f ⁻¹' W ∩ Subtype.val '' (H ⁻¹' (Prod.snd ⁻¹' {i})) =
        Subtype.val '' (H ⁻¹' ((Subtype.val ⁻¹' W) ×ˢ {i})) := by
      ext e
      simp [hH]
    rw [this, ← hfU.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen, H.isOpen_preimage,
      hU.isOpenEmbedding_subtypeVal.isOpen_iff_preimage_isOpen (by simpa using hW)]
    exact ⟨fun h ↦ h.prod (isOpen_discrete _), fun h ↦ by simpa using h.preimage (.prodMk_left i)⟩
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
    rw [Subtype.ext hba] at hb
    exact hij ((mem_singleton_iff.mp ha).symm.trans (mem_singleton_iff.mp hb))
  · ext e
    simp only [mem_preimage, mem_iUnion, mem_image, mem_singleton_iff]
    refine ⟨fun he ↦ ⟨_, ⟨e, he⟩, rfl, rfl⟩, ?_⟩
    rintro ⟨_, a, -, rfl⟩
    exact a.2

/-- **Evenly covered points compose along finite fibres.** If `x` is evenly covered by `q` with
finite fibre `I`, and every point of `Y` over `x` is evenly covered by `p`, then `x` is evenly
covered by `q ∘ p`. -/
theorem _root_.IsEvenlyCovered.comp {q : Y → X} {p : E → Y} {x : X} {I : Type*}
    [TopologicalSpace I] [Finite I] (hq : IsEvenlyCovered q x I)
    (hp : ∀ y, q y = x → IsEvenlyCovered p y (p ⁻¹' {y})) :
    IsEvenlyCovered (q ∘ p) x ((q ∘ p) ⁻¹' {x}) := by
  -- The sheets `S i` of `q` over `U ∋ x`, and the point `y i` of `S i` over `x`.
  obtain ⟨U, hxU, hU, S, hSo, hSi, hSim, hSiff, hSd, hSU⟩ := hq.exists_sheets
  have hy : ∀ i, ∃ y ∈ S i, q y = x := fun i ↦ by
    rw [← mem_image, hSim i]
    exact hxU
  choose y hyS hyx using hy
  -- The sheets `T i j` of `p` over `V i ∋ y i`.
  choose V hyV hV T hTo hTi hTim hTiff hTd hTV using fun i ↦ (hp (y i) (hyx i)).exists_sheets
  -- Shrink `U` to `W`, over which the lift of `W` to each `S i` lies in `V i`.
  let W := U ∩ ⋂ i, q '' (S i ∩ V i)
  have hWo : IsOpen W := hU.inter <| isOpen_iInter_of_finite fun i ↦ by
    rw [hSiff i _ (hSim i ▸ image_mono inter_subset_left),
      (hSi i).preimage_image_inter inter_subset_left]
    exact (hSo i).inter (hV i)
  have hxW : x ∈ W := ⟨hxU, mem_iInter.mpr fun i ↦ ⟨y i, ⟨hyS i, hyV i⟩, hyx i⟩⟩
  have key : ∀ i, ∀ z ∈ S i, q z ∈ W → z ∈ V i := by
    intro i z hz hw
    obtain ⟨z', ⟨hz'S, hz'V⟩, hz'⟩ := mem_iInter.mp hw.2 i
    rwa [← hSi i hz'S hz hz']
  -- The sheets of `q ∘ p` over `W` are indexed by the pairs `(i, j)`.
  let R : (Σ i, p ⁻¹' {y i}) → Set E := fun k ↦ T k.1 k.2 ∩ p ⁻¹' S k.1
  have hexh : (q ∘ p) ⁻¹' W ⊆ ⋃ k, R k := by
    intro e he
    have hpe : p e ∈ q ⁻¹' U := he.1
    rw [hSU, mem_iUnion] at hpe
    obtain ⟨i, hi⟩ := hpe
    have hpV : e ∈ p ⁻¹' V i := key i _ hi he
    rw [hTV, mem_iUnion] at hpV
    obtain ⟨j, hj⟩ := hpV
    exact mem_iUnion.mpr ⟨⟨i, j⟩, hj, hi⟩
  rcases isEmpty_or_nonempty (Σ i, p ⁻¹' {y i}) with hι | hι
  · exact IsEvenlyCovered.to_isEvenlyCovered_preimage <| .of_preimage_eq_empty Empty
      (hWo.mem_nhds hxW) (eq_empty_of_subset_empty (hexh.trans (iUnion_of_empty R).le))
  let _ : TopologicalSpace (Σ i, p ⁻¹' {y i}) := ⊥
  have : DiscreteTopology (Σ i, p ⁻¹' {y i}) := ⟨rfl⟩
  have : Nonempty E := let ⟨⟨_, j⟩⟩ := hι; ⟨j.1⟩
  have hsurj : ∀ k, (R k).SurjOn (q ∘ p) W := by
    intro k w hw
    obtain ⟨z, ⟨hzS, hzV⟩, rfl⟩ := mem_iInter.mp hw.2 k.1
    obtain ⟨e, he, rfl⟩ : z ∈ p '' T k.1 k.2 := (hTim k.1 k.2).symm ▸ hzV
    exact ⟨e, ⟨he, hzS⟩, rfl⟩
  refine (IsEvenlyCovered.of_trivialization (t := hWo.trivializationDiscrete R W
    (fun k W' hW' ↦ ?_) (fun k ↦ ?_) hsurj (fun k k' hkk' ↦ ?_) hexh)
    hxW).to_isEvenlyCovered_preimage
  · -- An open subset of `W` lifts to an open subset of `S k.1` inside `V k.1`, and then to an
    -- open subset of the sheet `T k.1 k.2`.
    have hsub : q ⁻¹' W' ∩ S k.1 ⊆ V k.1 := fun z hz ↦ key k.1 z hz.2 (hW' hz.1)
    rw [hSiff k.1 _ (hW'.trans inter_subset_left), hTiff k.1 k.2 _ hsub]
    congr! 1
    ext e
    simp only [R, mem_inter_iff, mem_preimage, comp_apply]
    tauto
  · rintro e ⟨heT, heS⟩ e' ⟨heT', heS'⟩ hee'
    exact hTi _ _ heT heT' (hSi _ heS heS' hee')
  · obtain ⟨i, j⟩ := k
    obtain ⟨i', j'⟩ := k'
    by_cases hii' : i = i'
    · subst hii'
      have hjj' : j ≠ j' := fun h ↦ hkk' (h ▸ rfl)
      exact (hTd i hjj').mono inter_subset_left inter_subset_left
    · exact ((hSd hii').preimage p).mono inter_subset_right inter_subset_right

/-- **A covering map followed by a covering map with finite fibres is a covering map.** -/
theorem _root_.IsCoveringMap.comp {q : Y → X} {p : E → Y} (hq : IsCoveringMap q)
    (hp : IsCoveringMap p) (hfin : ∀ x, (q ⁻¹' {x}).Finite) : IsCoveringMap (q ∘ p) := fun x ↦
  have := (hfin x).to_subtype
  (hq x).comp fun y _ ↦ hp y

end TauCeti

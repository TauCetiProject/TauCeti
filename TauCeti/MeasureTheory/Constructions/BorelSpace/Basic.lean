/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Borel measurability and proper pushforwards

For an inducing map `f : α → β` between Borel spaces, the Borel σ-algebra of `α` is the
pullback of the Borel σ-algebra of `β` along `f`. Hence a map `g` into `α` is measurable exactly
when `f ∘ g` is. Unlike `MeasurableEmbedding.measurable_comp_iff`, this needs no measurability
of the range of `f`: a topological embedding with non-measurable range still detects
measurability of maps into its domain.

The units of a topological group with zero with continuous inversion embed into it, so the
measurable structure that Mathlib puts on them, pulled back along `Units.val`, is their Borel
structure. For any measurable structure with measurable singletons on a group with zero,
`Units.val` is a measurable embedding, since its range is the complement of `0`.

Pushforward along a proper map preserves finiteness on compact sets. In particular,
proper embeddings and translations can transport locally finite measures.

A local homeomorphism out of a Lindelöf space maps measurable sets to measurable sets: the image
is a countable union of images under open embeddings of chart domains. If it is surjective, a map
out of its codomain is therefore measurable exactly when its composite with it is, and it has
a measurable section, given over the target of each of countably many charts by the inverse chart.

## Main results

* `ContinuousOn.measurableSet_preimage_inter`
* `Topology.IsInducing.comap_borel`
* `Topology.IsInducing.measurable_comp_iff`
* `Units.borelSpace₀`
* `Units.measurableEmbedding_val₀`
* `IsLocalHomeomorph.measurableSet_image`
* `IsLocalHomeomorph.measurable_comp_iff`
* `IsLocalHomeomorph.exists_measurable_rightInverse`
* `MeasureTheory.Measure.isFiniteMeasureOnCompacts_map_of_isProperMap`
-/

public section

open MeasureTheory Topology

/-- The preimage of a measurable set under a map continuous on a measurable carrier is
measurable after intersecting with that carrier. -/
theorem ContinuousOn.measurableSet_preimage_inter {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {f : X → Y} {s : Set X} {A : Set Y} (hc : ContinuousOn f s)
    (hs : MeasurableSet s) (hA : MeasurableSet A) : MeasurableSet (f ⁻¹' A ∩ s) := by
  rw [Set.inter_comm, ← Subtype.image_preimage_coe]
  apply (MeasurableEmbedding.subtypeVal hs).measurableSet_image.mpr
  rw [← Set.preimage_comp, ← Set.domRestrict_eq]
  exact hc.domRestrict.measurable hA

/-- The Borel σ-algebra of the domain of an inducing map is the pullback of the Borel σ-algebra
of its codomain. -/
theorem Topology.IsInducing.comap_borel {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {f : α → β} (hf : IsInducing f) : (borel β).comap f = borel α := by
  rw [← borel_comap, hf.eq_induced]

/-- For an inducing map `f` between Borel spaces, a map `g` into the domain of `f` is measurable
exactly when `f ∘ g` is. -/
theorem Topology.IsInducing.measurable_comp_iff {α β γ : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    [MeasurableSpace γ] {f : α → β} (hf : IsInducing f) {g : γ → α} :
    Measurable (f ∘ g) ↔ Measurable g := by
  rw [measurable_iff_comap_le, measurable_iff_comap_le, ← MeasurableSpace.comap_comp,
    BorelSpace.measurable_eq (α := α), BorelSpace.measurable_eq (α := β), hf.comap_borel]

/-- The measurable structure on the units of a topological group with zero with continuous
inversion, pulled back along `Units.val`, is the Borel structure: `Units.val` is a topological
embedding (`Units.isEmbedding_val₀`). -/
instance Units.borelSpace₀ {G₀ : Type*} [GroupWithZero G₀] [TopologicalSpace G₀]
    [ContinuousInv₀ G₀] [MeasurableSpace G₀] [BorelSpace G₀] : BorelSpace G₀ˣ :=
  ⟨by rw [← Units.isEmbedding_val₀.isInducing.comap_borel, ← BorelSpace.measurable_eq]; rfl⟩

/-- The inclusion `Units.val : G₀ˣ → G₀` of the units of a group with zero is a measurable
embedding, for the measurable structure on `G₀ˣ` pulled back along it: its range is the
complement of `0`. -/
theorem Units.measurableEmbedding_val₀ {G₀ : Type*} [GroupWithZero G₀] [MeasurableSpace G₀]
    [MeasurableSingletonClass G₀] : MeasurableEmbedding (Units.val : G₀ˣ → G₀) where
  injective := Units.val_injective
  measurable := Measurable.of_comap_le le_rfl
  measurableSet_image' := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Set.image_preimage_eq_inter_range]
    refine ht.inter ?_
    have : Set.range (Units.val : G₀ˣ → G₀) = {0}ᶜ := by
      ext x
      exact ⟨by rintro ⟨u, rfl⟩; exact u.ne_zero, fun hx ↦ ⟨Units.mk0 x hx, rfl⟩⟩
    rw [this]
    exact (measurableSet_singleton 0).compl

/-- A local homeomorphism out of a Lindelöf space maps measurable sets to measurable sets. -/
theorem IsLocalHomeomorph.measurableSet_image {α β : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [LindelofSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] {f : α → β} (hf : IsLocalHomeomorph f) {s : Set α}
    (hs : MeasurableSet s) : MeasurableSet (f '' s) := by
  choose e he hfe using hf
  obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover (fun x ↦ (e x).source)
    fun x ↦ (e x).open_source.mem_nhds (he x)
  rw [← Set.inter_univ s, ← hcover, Set.inter_iUnion₂, Set.image_iUnion₂]
  refine .biUnion ht fun x _ ↦ ?_
  -- On the source of `e x`, the map `f` is the open embedding `(e x).source.domRestrict (e x)`.
  rw [hfe x, ← Set.image_domRestrict]
  exact (e x).isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image'
    (measurable_subtypeVal hs)

/-- For a surjective local homeomorphism `f` out of a Lindelöf space, a map `g` out of the
codomain of `f` is measurable exactly when `g ∘ f` is. -/
theorem IsLocalHomeomorph.measurable_comp_iff {α β γ : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [LindelofSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] [MeasurableSpace γ] {f : α → β}
    (hf : IsLocalHomeomorph f) (hsurj : Function.Surjective f) {g : β → γ} :
    Measurable (g ∘ f) ↔ Measurable g := by
  refine ⟨fun hg s hs ↦ ?_, fun hg ↦ hg.comp hf.continuous.measurable⟩
  rw [← hsurj.image_preimage (g ⁻¹' s)]
  exact hf.measurableSet_image (hg hs)

/-- A surjective local homeomorphism out of a Lindelöf space has a measurable section: a
measurable map `s` with `f (s y) = y` for every `y`. -/
theorem IsLocalHomeomorph.exists_measurable_rightInverse {α β : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [LindelofSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] {f : α → β} (hf : IsLocalHomeomorph f)
    (hsurj : Function.Surjective f) :
    ∃ s : β → α, Measurable s ∧ Function.RightInverse s f := by
  classical
  cases isEmpty_or_nonempty α with
  | inl _ =>
    have : IsEmpty β := ⟨fun y ↦ isEmptyElim (hsurj y).choose⟩
    exact ⟨isEmptyElim, measurable_of_subsingleton_codomain _, isEmptyElim⟩
  | inr hα =>
    obtain ⟨x₀⟩ := hα
    choose e he hfe using hf
    -- Countably many chart sources `(e (c n)).source` cover `α`, so their targets cover `β`.
    obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover (fun x ↦ (e x).source)
      fun x ↦ (e x).open_source.mem_nhds (he x)
    obtain ⟨c, rfl⟩ : ∃ c : ℕ → α, t = Set.range c := by
      obtain ⟨x, hx, -⟩ := Set.mem_iUnion₂.1 (hcover.ge (Set.mem_univ x₀))
      exact ht.exists_eq_range ⟨x, hx⟩
    have hmem (y : β) : ∃ n, y ∈ (e (c n)).target := by
      obtain ⟨x, rfl⟩ := hsurj y
      obtain ⟨n, hn⟩ : ∃ n, x ∈ (e (c n)).source := by
        simpa using hcover.ge (Set.mem_univ x)
      exact ⟨n, hfe (c n) ▸ (e (c n)).map_source hn⟩
    -- Over the target of the first chart containing `y`, take the inverse of that chart.
    refine ⟨fun y ↦ (e (c (Nat.find (hmem y)))).target.piecewise (e (c (Nat.find (hmem y)))).symm
      (fun _ ↦ x₀) y, ?_, fun y ↦ ?_⟩
    · exact Measurable.find (fun n ↦ (e (c n)).continuousOn_symm.measurable_piecewise
        continuousOn_const (e (c n)).open_target.measurableSet)
        (fun n ↦ (e (c n)).open_target.measurableSet) hmem
    · have hy := Nat.find_spec (hmem y)
      simp only [Set.piecewise_eq_of_mem _ _ _ hy]
      rw [hfe (c (Nat.find (hmem y)))]
      exact (e _).right_inv hy

namespace MeasureTheory.Measure

/-- A proper continuous pushforward preserves finiteness on compact sets. -/
theorem isFiniteMeasureOnCompacts_map_of_isProperMap {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [T2Space Y]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {f : X → Y} (hf : IsProperMap f) :
    IsFiniteMeasureOnCompacts (μ.map f) where
  lt_top_of_isCompact K hK := by
    by_cases hfm : AEMeasurable f μ
    · rw [Measure.map_apply_of_aemeasurable hfm hK.measurableSet]
      exact (hf.isCompact_preimage hK).measure_lt_top
    · by_cases hμ : μ = 0
      · simp [hμ]
      · rw [Measure.map_of_not_aemeasurable_of_ne_zero hfm hμ]
        exact @measure_lt_top _ _ _ isFiniteMeasure_dirac _

end MeasureTheory.Measure

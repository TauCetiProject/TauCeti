/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.AtomlessStandardBorel.Transport
public import TauCeti.MeasureTheory.OptimalTransport.GraphPlan.Basic

/-!
# Realizing a coupling along a source partition

A coupling with atomless source can be realized by a single measurable transport map at the
resolution of any countable measurable source partition. For each cell `A i`, its graph plan
agrees with the coupling on every rectangle `A i × B`, retaining the entire target law within
that cell, rather than just the masses of a chosen target partition.

The construction transports the restricted source on each cell to the second marginal of the
coupling restricted to that cell, then glues the maps. The gluing step,
`TauCeti.IsCoupling.exists_measurePreserving_restrict`, applies to any disjoint measurable pieces
covering the coupling and any disjoint source sets of matching masses. This is the
measure-theoretic step in approximating couplings by graph plans: increasingly fine source
partitions retain increasingly more information about the original coupling. No topology is
needed for this step.

## References

* A. Pratelli, *On the equality between Monge's infimum and Kantorovich's minimum in optimal
  mass transportation*, Ann. I. H. Poincaré Probab. Statist. 43 (2007), §1.1, for the role of
  graph-plan density in the bounded continuous-cost problem.
-/

public section

open Function MeasureTheory Set

namespace TauCeti.IsCoupling

variable {X Y ι : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y] [Countable ι]
  {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)}
  [IsFiniteMeasure μ] [NullSingletonClass μ]

/-- Let `π` be concentrated on a union of disjoint measurable pieces `S i`, and let `Z i` be
disjoint measurable source sets with `μ (Z i) = π (S i)`. Then one transport map sends `μ`
restricted to each `Z i` to the second marginal of `π` restricted to `S i`, and the sets `Z i`
exhaust `μ`. -/
theorem exists_measurePreserving_restrict (hπ : IsCoupling π μ ν) {S : ι → Set (X × Y)}
    (hSm : ∀ i, MeasurableSet (S i)) (hSd : Pairwise (Disjoint on S))
    (hScov : ∀ᵐ z ∂π, z ∈ ⋃ i, S i) {Z : ι → Set X} (hZm : ∀ i, MeasurableSet (Z i))
    (hZd : Pairwise (Disjoint on Z)) (hZμ : ∀ i, μ (Z i) = π (S i)) :
    ∃ T : X → Y, MeasurePreserving T μ ν ∧
      (∀ i, MeasurePreserving T (μ.restrict (Z i)) (π.restrict (S i)).snd) ∧
      μ (⋃ i, Z i)ᶜ = 0 := by
  have hπS : π.restrict (⋃ i, S i) = π := Measure.restrict_eq_self_of_ae_mem hScov
  have hZcov : μ (⋃ i, Z i)ᶜ = 0 := by
    have hS : π (⋃ i, S i) = π univ := by
      conv_rhs => rw [← hπS, Measure.restrict_apply_univ]
    have h : μ (⋃ i, Z i) = μ univ := by
      rw [measure_iUnion hZd hZm, tsum_congr hZμ, ← measure_iUnion hSd hSm, hS,
        hπ.measure_univ_left]
    rw [measure_compl (MeasurableSet.iUnion hZm) (measure_ne_top _ _), h, tsub_self]
  -- The null remainder of the source becomes one more cell, carrying the zero law.
  let A : Option ι → Set X := fun o ↦ o.elim (⋃ i, Z i)ᶜ Z
  let ν' : Option ι → Measure Y := extend some (fun i ↦ (π.restrict (S i)).snd) 0
  have hAm (o : Option ι) : MeasurableSet (A o) := by
    cases o
    exacts [(MeasurableSet.iUnion hZm).compl, hZm _]
  have hAd : Pairwise (Disjoint on A) := by
    rintro (_ | i) (_ | j) hij
    · exact absurd rfl hij
    · exact disjoint_compl_left_iff_subset.2 (subset_iUnion Z j)
    · exact (disjoint_compl_left_iff_subset.2 (subset_iUnion Z i)).symm
    · exact hZd fun h ↦ hij (congrArg some h)
  have hAu : ⋃ o, A o = univ := by
    rw [iUnion_option]
    exact compl_union_self _
  have hmass (o : Option ι) : μ (A o) = ν' o univ := by
    cases o
    · simpa [A, ν', extend_apply'] using hZcov
    · simp [A, ν', (Option.some_injective ι).extend_apply, hZμ, Measure.snd_univ]
  obtain ⟨T, hT, hTA⟩ := μ.exists_measurePreserving_sum_of_nullSingleton hAm hAd hAu ν' hmass
  have hsum : Measure.sum ν' = ν := by
    rw [Measure.sum_extend_zero (Option.some_injective ι), ← Measure.snd_sum,
      ← Measure.restrict_iUnion hSd hSm, hπS, hπ.snd_eq]
  refine ⟨T, hsum ▸ hT, fun i ↦ ?_, hZcov⟩
  simpa [A, ν', (Option.some_injective ι).extend_apply] using hTA (some i)

/-- The countable case of `TauCeti.IsCoupling.exists_measurePreserving_graphPlan_prod_eq`. -/
private theorem exists_measurePreserving_graphPlan_prod_eq_of_countable (hπ : IsCoupling π μ ν)
    {A : ι → Set X} (hAm : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (Disjoint on A)) (hAu : (⋃ i, A i) = univ) :
    ∃ T : X → Y, MeasurePreserving T μ ν ∧
      ∀ i B, MeasurableSet B → graphPlan T μ (A i ×ˢ B) = π (A i ×ˢ B) := by
  have hdu : (⋃ i, A i ×ˢ (univ : Set Y)) = univ := by
    rw [← iUnion_prod_const, hAu, univ_prod_univ]
  obtain ⟨T, hT, hcell, -⟩ := hπ.exists_measurePreserving_restrict
    (fun i ↦ (hAm i).prod MeasurableSet.univ)
    (fun i j hij ↦ disjoint_prod.mpr (Or.inl (hAd hij))) (by simp [hdu]) hAm hAd
    fun i ↦ (hπ.measure_prod_univ (hAm i)).symm
  refine ⟨T, hT, fun i B hB ↦ ?_⟩
  rw [graphPlan_prod hT.aemeasurable (hAm i) hB, inter_comm,
    ← Measure.restrict_apply (hT.measurable hB), (hcell i).measure_preimage hB.nullMeasurableSet,
    Measure.snd_apply hB, Measure.restrict_apply (measurable_snd hB)]
  congr 1
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
  exact and_comm

omit [Countable ι] in
/-- A coupling with atomless source has a graph-plan realization on every family of disjoint
measurable source cells. The map preserves the full target law and the mass of every rectangle
whose source side is a cell. Zero-mass cells are allowed, only countably many cells carry mass,
and the cells need not cover the source. -/
theorem exists_measurePreserving_graphPlan_prod_eq (hπ : IsCoupling π μ ν)
    {A : ι → Set X} (hAm : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (Disjoint on A)) :
    ∃ T : X → Y, MeasurePreserving T μ ν ∧
      ∀ i B, MeasurableSet B → graphPlan T μ (A i ×ˢ B) = π (A i ×ˢ B) := by
  -- Only countably many cells carry mass; the null cells are merged into one remainder cell.
  let I : Set ι := {i | 0 < μ (A i)}
  have hI : I.Countable := Measure.countable_meas_pos_of_disjoint_iUnion hAm hAd
  have : Countable I := hI.to_subtype
  let A' : Option I → Set X := fun o ↦ o.elim (⋃ i : I, A i)ᶜ fun i ↦ A i
  have hA'm (o : Option I) : MeasurableSet (A' o) := by
    cases o
    exacts [(MeasurableSet.iUnion fun i : I ↦ hAm i).compl, hAm _]
  have hA'd : Pairwise (Disjoint on A') := by
    rintro (_ | i) (_ | j) hij
    · exact absurd rfl hij
    · exact disjoint_compl_left_iff_subset.2 (subset_iUnion (fun i : I ↦ A i) j)
    · exact (disjoint_compl_left_iff_subset.2 (subset_iUnion (fun i : I ↦ A i) i)).symm
    · exact hAd fun h ↦ hij (congrArg some (Subtype.ext h))
  have hA'u : ⋃ o, A' o = univ := by
    rw [iUnion_option]
    exact compl_union_self _
  obtain ⟨T, hT, hcell⟩ :=
    hπ.exists_measurePreserving_graphPlan_prod_eq_of_countable hA'm hA'd hA'u
  refine ⟨T, hT, fun i B hB ↦ ?_⟩
  by_cases hi : 0 < μ (A i)
  · exact hcell (some ⟨i, hi⟩) B hB
  · have h0 : μ (A i) = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hi)
    rw [graphPlan_prod hT.aemeasurable (hAm i) hB,
      measure_mono_null inter_subset_left h0, eq_comm]
    refine measure_mono_null (prod_mono_right (subset_univ B)) ?_
    rw [hπ.measure_prod_univ (hAm i), h0]

/-- After observing the source through a countable-valued measurable map `q`, every coupling
with atomless source is exactly the joint law of `q` and a measurable transport map. Thus the
coupling and its graph-plan realization have identical pushforwards under `Prod.map q id`. -/
theorem exists_measurePreserving_map_graphPlan_eq (hπ : IsCoupling π μ ν)
    [MeasurableSpace ι] {q : X → ι} (hq : Measurable q) :
    ∃ T : X → Y, MeasurePreserving T μ ν ∧
      (graphPlan T μ).map (Prod.map q id) = π.map (Prod.map q id) := by
  -- The cells are the preimages of the measurable atoms of `ι`, which are measurable as `ι` is
  -- countable and which generate its measurable sets.
  let κ : Type _ := range (measurableAtom : ι → Set ι)
  have : Countable κ := (countable_range _).to_subtype
  have hκm (a : κ) : MeasurableSet (q ⁻¹' a.1) := by
    obtain ⟨i, hi⟩ := a.2
    exact hq (hi ▸ MeasurableSet.measurableAtom_of_countable i)
  have hκd : Pairwise (Disjoint on fun a : κ ↦ q ⁻¹' a.1) := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩ hij
    refine (disjoint_measurableAtom_of_notMem fun h ↦ hij ?_).preimage q
    exact Subtype.ext (measurableAtom_eq_of_mem h)
  obtain ⟨T, hT, hcell⟩ := hπ.exists_measurePreserving_graphPlan_prod_eq hκm hκd
  refine ⟨T, hT, Measure.ext_prod fun {s t} hs ht ↦ ?_⟩
  have hm : Measurable (Prod.map q (id : Y → Y)) := hq.prodMap measurable_id
  rw [Measure.map_apply hm (hs.prod ht), Measure.map_apply hm (hs.prod ht)]
  simp only [Set.preimage_prod_map_prod, Set.preimage_id]
  have hu : (q ⁻¹' s) ×ˢ t = ⋃ a : {a : κ // a.1 ⊆ s}, (q ⁻¹' a.1.1) ×ˢ t := by
    ext z
    refine ⟨fun ⟨hz, hzt⟩ ↦ mem_iUnion.2 ⟨⟨⟨measurableAtom (q z.1), q z.1, rfl⟩,
      measurableAtom_subset hs hz⟩, mem_measurableAtom_self _, hzt⟩, fun hz ↦ ?_⟩
    obtain ⟨a, haq, hzt⟩ := mem_iUnion.1 hz
    exact ⟨a.2 haq, hzt⟩
  have hd : Pairwise (Disjoint on fun a : {a : κ // a.1 ⊆ s} ↦ (q ⁻¹' a.1.1) ×ˢ t) := by
    intro a b hab
    exact disjoint_prod.mpr <| Or.inl <| hκd fun h ↦ hab (Subtype.ext h)
  have hmcell (a : {a : κ // a.1 ⊆ s}) : MeasurableSet ((q ⁻¹' a.1.1) ×ˢ t) :=
    (hκm a.1).prod ht
  rw [hu, measure_iUnion hd hmcell, measure_iUnion hd hmcell]
  exact tsum_congr fun a ↦ hcell a.1 t ht

end TauCeti.IsCoupling

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Baire.BaireMeasurable
public import Mathlib.Topology.Baire.CompleteMetrizable
public import TauCeti.MeasureTheory.Constructions.Polish.Perfect
public import TauCeti.Topology.Baire.Perfect
public import TauCeti.Topology.MetricSpace.Polish.Pi
public import TauCeti.Topology.Perfect

/-!
# Baire-measurable maps are continuous on a comeagre set

A map `f : X → Y` into a second countable space whose preimages of open sets have the Baire
property is continuous on a comeagre `Gδ` subset of `X`. Each basic open set `t` of `Y` has a
preimage that differs from an open set `u t` of `X` by a meagre set; off the countably many meagre
differences, the preimage of every basic open set is relatively open. Borel maps between Borel
spaces satisfy the hypothesis, since Borel sets have the Baire property.

On a nonempty perfect Polish space a comeagre set is uncountable, and a comeagre `Gδ` set is Borel,
so by the perfect set theorem for Borel sets it contains a copy of Cantor space. Hence countably
many Baire-measurable maps become continuous simultaneously after restriction to a copy of Cantor
space. In particular, countably many Borel maps from Cantor space to countable discrete spaces
become continuous on a Cantor subcopy, which lets Borel labellings of Cantor space be replaced by
continuous ones.

## Main results

* `TauCeti.exists_isGδ_mem_residual_continuousOn`: a map into a second countable space whose open
  preimages have the Baire property is continuous on a comeagre `Gδ` set.
* `Measurable.exists_isGδ_mem_residual_continuousOn`: the same for Borel maps.
* `TauCeti.exists_nat_bool_injection_forall_continuous_comp`: on a nonempty perfect Polish space,
  countably many such maps are continuous along one continuous injection of Cantor space.
* `TauCeti.exists_cantor_subcopy_continuous`: countably many maps from Cantor space to countable
  discrete spaces with Borel fibres become continuous after composing with one continuous injection
  of Cantor space into itself.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 8.38 (Baire-measurable maps are continuous on a comeagre `Gδ` set).
* The statement of the Cantor-subcopy theorem follows
  `InfinitaryLogic/Descriptive/CantorStabilization.lean` in `cameronfreer/infinitary-logic`
  (Apache-2.0, commit `518a366`); here it is derived from the comeagre-continuity theorem for
  general Baire-measurable maps.
-/

public section

open Set Function Filter Topology TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

namespace TauCeti

/-- A comeagre set contains a comeagre `Gδ` set. No Baire hypothesis is needed: the countable
intersection of dense open sets inside a comeagre set is itself comeagre, though it need not be
dense. -/
theorem exists_isGδ_subset_mem_residual {s : Set X} (hs : s ∈ residual X) :
    ∃ t ⊆ s, IsGδ t ∧ t ∈ residual X := by
  obtain ⟨S, hSo, hSd, hSc, hSs⟩ := mem_residual_iff.1 hs
  exact ⟨⋂₀ S, hSs, ⟨S, hSo, hSc, rfl⟩,
    (countable_sInter_mem hSc).2 fun t ht => residual_of_dense_open (hSo t ht) (hSd t ht)⟩

/-- **Baire-measurable maps are continuous on a comeagre set.** If `Y` is second countable and
the preimage under `f` of every open set has the Baire property, then `f` is continuous on a
comeagre `Gδ` subset of `X`. -/
theorem exists_isGδ_mem_residual_continuousOn [SecondCountableTopology Y] {f : X → Y}
    (hf : ∀ U, IsOpen U → BaireMeasurableSet (f ⁻¹' U)) :
    ∃ G, IsGδ G ∧ G ∈ residual X ∧ ContinuousOn f G := by
  have hB := isBasis_countableBasis Y
  -- each basic open set has a preimage that is an open set up to a meagre set
  choose! u hu hfu using fun t (ht : t ∈ countableBasis Y) =>
    (hf t (hB.isOpen ht)).residualEq_isOpen
  have hres : {x | ∀ t ∈ countableBasis Y, (x ∈ f ⁻¹' t ↔ x ∈ u t)} ∈ residual X := by
    simpa only [ofPred_forall] using
      (countable_bInter_mem (countable_countableBasis Y)).2 fun t ht =>
        eventuallyEqSet_iff.1 (hfu t ht)
  obtain ⟨G, hGs, hG, hGr⟩ := exists_isGδ_subset_mem_residual hres
  refine ⟨G, hG, hGr, hB.continuousOn_iff.2 fun t ht => ⟨u t, hu t ht, ?_⟩⟩
  ext x
  simp only [mem_inter_iff, and_congr_left_iff]
  exact fun hx => hGs hx t ht

end TauCeti

/-- **Borel maps are continuous on a comeagre set.** A Borel map from a Borel space to a second
countable space is continuous on a comeagre `Gδ` set. -/
theorem Measurable.exists_isGδ_mem_residual_continuousOn [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y] {f : X → Y}
    (hf : Measurable f) : ∃ G, IsGδ G ∧ G ∈ residual X ∧ ContinuousOn f G :=
  TauCeti.exists_isGδ_mem_residual_continuousOn fun _ hU =>
    (hf hU.measurableSet).baireMeasurableSet

namespace TauCeti

/-- **Baire-measurable maps are continuous on a Cantor set.** On a nonempty perfect Polish space
`X`, countably many maps `g i` into second countable spaces whose open preimages have the Baire
property are simultaneously continuous along one continuous injection of Cantor space into `X`. -/
theorem exists_nat_bool_injection_forall_continuous_comp [PolishSpace X] [PerfectSpace X]
    [Nonempty X] {ι : Type*} [Countable ι] {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    [∀ i, SecondCountableTopology (Y i)] {g : ∀ i, X → Y i}
    (hg : ∀ i U, IsOpen U → BaireMeasurableSet (g i ⁻¹' U)) :
    ∃ e : (ℕ → Bool) → X, Continuous e ∧ Injective e ∧ ∀ i, Continuous (g i ∘ e) := by
  borelize X
  choose G hG hGr hgG using fun i => exists_isGδ_mem_residual_continuousOn (hg i)
  -- the common continuity set is comeagre, hence uncountable, and Borel
  have hr : (⋂ i, G i) ∈ residual X := countable_iInter_mem.2 hGr
  obtain ⟨e, he, hec, hei⟩ :=
    (IsGδ.iInter hG).measurableSet.exists_nat_bool_injection_of_not_countable
      (not_countable_of_mem_residual hr)
  exact ⟨e, hec, hei, fun i =>
    ((hgG i).mono (iInter_subset G i)).comp_continuous hec fun y => he (mem_range_self y)⟩

/-- **Cantor subcopies with continuous colorings.** Countably many maps from Cantor space to
countable discrete spaces, each with Borel fibres, become continuous after composing with one
continuous injection of Cantor space into itself. -/
theorem exists_cantor_subcopy_continuous {ι : Type*} [Countable ι] {Z : ι → Type*}
    [∀ i, Countable (Z i)] [∀ i, TopologicalSpace (Z i)] [∀ i, DiscreteTopology (Z i)]
    {g : ∀ i, (ℕ → Bool) → Z i} (hg : ∀ i z, MeasurableSet (g i ⁻¹' {z})) :
    ∃ e : (ℕ → Bool) → (ℕ → Bool), Continuous e ∧ Injective e ∧ ∀ i, Continuous (g i ∘ e) :=
  exists_nat_bool_injection_forall_continuous_comp fun i U _ => by
    rw [← biUnion_preimage_singleton]
    exact (MeasurableSet.biUnion U.to_countable fun z _ => hg i z).baireMeasurableSet

end TauCeti

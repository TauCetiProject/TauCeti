/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Continuous functions and the product σ-algebra

A continuous function on a product need not be measurable for the product of the Borel
σ-algebras: that σ-algebra can be smaller than the Borel σ-algebra of the product. Nevertheless,
a continuous function with values in a metrizable space is product-measurable when both factors
are σ-compact and the second is Hausdorff, or when the first is σ-compact and the second is compact
without separation assumptions. Neither factor needs to be second countable.

We first treat a compact second factor. Currying gives a continuous map into the metrizable
space of continuous functions on that factor. Its σ-compact range is separable; evaluation on
this range is measurable by Mathlib's Carathéodory theorem
`MeasureTheory.measurable_uncurry_of_continuous_of_measurable`. A countable compact cover of the
second factor then gives the general result.

In particular, on a σ-compact Hausdorff topological group, the scalar function
`(x, y) ↦ f (y⁻¹ * x)` is product-measurable for continuous real `f`. This supplies the
continuous-generator step in measurable convolution arguments, without asserting that group
multiplication itself is measurable for the product Borel σ-algebra.

We also record `OpensMeasurableSpace.of_prod_left`: if the product `X × Y` with a nonempty second
factor is an `OpensMeasurableSpace` for the product σ-algebra, then so is `X`.
-/

public section

open Set MeasureTheory TopologicalSpace

/-- A continuous map from a product to a metrizable space is measurable for
the product σ-algebra if the first factor is σ-compact and the second is compact. No separation
assumption on either factor is needed. -/
theorem Continuous.measurable_prod_of_sigmaCompact_of_compact
    {X Y E : Type*} [TopologicalSpace X] [SigmaCompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] [TopologicalSpace E] [MetrizableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {f : X × Y → E} (hf : Continuous f) : Measurable f := by
  let := TopologicalSpace.metrizableSpaceMetric E
  let F : C(X, C(Y, E)) := (⟨f, hf⟩ : C(X × Y, E)).curry
  have hsep : IsSeparable (range F) := by
    obtain ⟨K, hK, hcover⟩ := isSigmaCompact_range F.continuous
    rw [← hcover]
    exact .iUnion fun n => (hK n).isSeparable
  let S := range F
  have : SecondCountableTopology S := hsep.secondCountableTopology
  have hF : Measurable (Set.rangeFactorization F) :=
    (F.continuous.subtype_mk (fun x => mem_range_self x)).measurable
  have heval : Measurable (fun p : S × Y => (p.1 : C(Y, E)) p.2) :=
    measurable_uncurry_of_continuous_of_measurable (ι := S)
      (fun y => by fun_prop)
      (fun u => (u : C(Y, E)).continuous.measurable)
  exact heval.comp ((hF.comp measurable_fst).prodMk measurable_snd)

/-- A continuous map from a product of σ-compact spaces to a metrizable space
is measurable for the product σ-algebra. Only the second factor needs to be Hausdorff. In
particular this does not require equality of the product and Borel σ-algebras on the domain. -/
theorem Continuous.measurable_prod_of_sigmaCompact
    {X Y E : Type*} [TopologicalSpace X] [SigmaCompactSpace X]
    [TopologicalSpace Y] [SigmaCompactSpace Y] [T2Space Y]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] [TopologicalSpace E] [MetrizableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {f : X × Y → E} (hf : Continuous f) : Measurable f := by
  obtain ⟨K, hK, hcover⟩ := isSigmaCompact_univ (X := Y)
  have hlocal (n : ℕ) : Measurable (fun p : X × K n => f (p.1, p.2)) := by
    have := isCompact_iff_compactSpace.1 (hK n)
    exact Continuous.measurable_prod_of_sigmaCompact_of_compact
      (hf.comp (continuous_id.prodMap continuous_subtype_val))
  intro s hs
  have heq : f ⁻¹' s = ⋃ n : ℕ,
      (fun p : X × K n => (p.1, (p.2 : Y))) ''
        ((fun p : X × K n => f (p.1, p.2)) ⁻¹' s) := by
    ext p
    simp only [mem_preimage, mem_iUnion, mem_image, Prod.exists]
    constructor
    · intro hp
      have hpK : p.2 ∈ ⋃ n, K n := hcover.symm ▸ mem_univ p.2
      obtain ⟨n, hn⟩ := mem_iUnion.1 hpK
      exact ⟨n, p.1, ⟨p.2, hn⟩, hp, rfl⟩
    · rintro ⟨n, x, y, hp, rfl⟩
      exact hp
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    (MeasurableEmbedding.id.prodMap
      (MeasurableEmbedding.subtype_coe (hK n).measurableSet)).measurableSet_image'
        (hlocal n hs)

/-- If the product of two topological spaces, the second nonempty, has the Borel property
`OpensMeasurableSpace` for the product σ-algebra, so does the first factor: an open set `s` is
the preimage of the measurable open set `s ×ˢ univ` under `x ↦ (x, b)`. -/
theorem OpensMeasurableSpace.of_prod_left {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [Nonempty Y] [OpensMeasurableSpace (X × Y)] :
    OpensMeasurableSpace X := by
  obtain ⟨b⟩ := ‹Nonempty Y›
  refine opensMeasurableSpace_iff_forall_measurableSet.2 fun s hs => ?_
  have : s = (fun x => (x, b)) ⁻¹' (s ×ˢ univ) := by simp
  rw [this]
  exact (hs.prod isOpen_univ).measurableSet.preimage (measurable_prodMk_right)

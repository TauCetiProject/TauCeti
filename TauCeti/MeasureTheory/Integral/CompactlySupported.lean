/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.Topology.ContinuousMap.CompactlySupported
public import TauCeti.Topology.PartitionOfUnity.Approximation
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Integrals of compactly supported functions: cutoffs and finite-rank approximation

A compactly supported continuous function with values in a real normed space can be
approximated in integral norm by finite sums of real compactly supported scalar functions
times vectors from any prescribed dense subset. Only finiteness of the measure on compact
sets is needed. In particular, no global finiteness or countability assumption is imposed.

This is the partition-of-unity approximation used to lift convolution coefficients through
dense coefficient maps. We use Mathlib's compactly supported partitions of unity.

The integral of the extension by zero of `f` along an open embedding `e` against a measure `μ` is
the integral of `f` against the pullback `μ.comap e`
(`CompactlySupportedContinuousMap.integral_extendZero`). This compares integrals of test
functions on an open subspace with integrals on the ambient space. In particular the uniqueness
part of the Riesz–Markov–Kakutani theorem localizes to an open set `s` of a second countable
locally compact Hausdorff space: two measures that vanish off `s` and are finite on its compact
subsets are equal as soon as they give the same integral to the compactly supported continuous
functions supported in `s`
(`MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported_of_isOpen`). Such measures need
not be finite on compact subsets of the whole space, as a density blowing up at the boundary of `s`
shows, so Mathlib's `MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported` does not apply
to them directly.

On a locally compact `R1Space` with measurable open sets, a compact set `K` inside an open set
`U` has a compactly supported Urysohn cutoff whose integral against every measure is at most the
mass of `U`, and at least the mass of `K` for measures finite on compact sets.

## Main declarations

* `CompactlySupportedContinuousMap.exists_integral_norm_sub_sum_smul_lt`: finite-rank
  approximation in integral norm.
* `IsCompact.exists_compactlySupported_measure_le_integral_le`: a compactly supported cutoff
  whose integral lies between the masses of a compact set and of an open neighbourhood of it.
* `CompactlySupportedContinuousMap.integral_extendZero`: integrals of extensions by zero along
  open embeddings are integrals against pullback measures.
* `MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported_of_isOpen`: measures carried by
  an open set and finite on its compact subsets are determined by the integrals of the compactly
  supported continuous functions supported in it.
-/

public section

open MeasureTheory Set Metric
open scoped CompactlySupported ENNReal

namespace CompactlySupportedContinuousMap

section ExtendZero

open Topology

variable {X Y E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrating the extension by zero of `f` along an open embedding `e` against `μ` is
integrating `f` against the pullback of `μ` along `e`. -/
theorem integral_extendZero {e : X → Y} (he : IsOpenEmbedding e) (f : C_c(X, E))
    (μ : Measure Y) : ∫ y, f.extendZero he y ∂μ = ∫ x, f x ∂μ.comap e := by
  have hme := he.measurableEmbedding
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦
    f.extendZero_apply_of_notMem_range he hy, ← hme.map_comap, hme.integral_map]
  simp

/-- **Riesz uniqueness on an open set.** On a second countable locally compact Hausdorff space,
two measures that vanish off an open set `s`, are finite on the compact subsets of `s` and give
the same integral to every compactly supported continuous function supported in `s` are equal. -/
theorem _root_.MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported_of_isOpen
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] {s : Set X} (hs : IsOpen s)
    {μ ν : Measure X} (hμ : μ sᶜ = 0) (hν : ν sᶜ = 0)
    (hμK : ∀ K, IsCompact K → K ⊆ s → μ K < ∞) (hνK : ∀ K, IsCompact K → K ⊆ s → ν K < ∞)
    (h : ∀ g : C_c(X, ℝ), tsupport g ⊆ s → ∫ x, g x ∂μ = ∫ x, g x ∂ν) : μ = ν := by
  -- Both measures are pushed forward from their pullbacks to `s`, which are finite on compact sets
  -- and hence regular, so that `Measure.ext_of_integral_eq_on_compactlySupported` applies on `s`.
  have hsm := hs.measurableSet
  have hemb : IsOpenEmbedding ((↑) : s → X) := hs.isOpenEmbedding_subtypeVal
  have hmap : ∀ ρ : Measure X, ρ sᶜ = 0 → (ρ.comap ((↑) : s → X)).map (↑) = ρ := fun ρ hρ ↦ by
    rw [map_comap_subtypeVal hsm, Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hρ)]
  have hfin : ∀ ρ : Measure X, (∀ K, IsCompact K → K ⊆ s → ρ K < ∞) →
      IsFiniteMeasureOnCompacts (ρ.comap ((↑) : s → X)) := fun ρ hρ ↦ ⟨fun K hK ↦ by
    rw [comap_subtypeVal_apply hsm]
    exact hρ _ (hK.image continuous_subtypeVal) (Subtype.coe_image_subset _ _)⟩
  have : LocallyCompactSpace s := hs.locallyCompactSpace
  have := hfin μ hμK
  have := hfin ν hνK
  have := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (μ.comap ((↑) : s → X))
  have := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (ν.comap ((↑) : s → X))
  rw [← hmap μ hμ, ← hmap ν hν]
  congr 1
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
  rw [← integral_extendZero hemb, ← integral_extendZero hemb]
  exact h _ ((tsupport_extendZero hemb f).trans_subset (Subtype.coe_image_subset _ _))

end ExtendZero

variable {X E : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite sums of scalar compactly supported functions times vectors from a dense set
approximate every compactly supported continuous function in integral norm. -/
theorem exists_integral_norm_sub_sum_smul_lt (f : C_c(X, E)) (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] {S : Set E} (hS : Dense S) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset S) (φ : s → C_c(X, ℝ)),
      (∫ x, ‖f x - ∑ i : s, φ i x • (i.val.val : E)‖ ∂μ) < ε := by
  classical
  -- A fixed compact neighbourhood bounds the measures of all the approximation supports.
  obtain ⟨K, hK, hfK⟩ := exists_compact_superset f.hasCompactSupport
  let δ := ε / (μ.real K + 1)
  have hδ : 0 < δ := by positivity
  obtain ⟨s, ρ, hρc, hρ⟩ := exists_partitionOfUnity_dist_lt f hS hfK hδ
  let φ (i : s) : C_c(X, ℝ) := ⟨ρ i, hρc i⟩
  refine ⟨s, φ, ?_⟩
  have hbound (x : X) : ‖f x - ∑ i : s, φ i x • (i.val.val : E)‖ ≤ δ :=
    ρ.norm_sub_sum_smul_le f (fun i => (i.val.val : E)) hδ.le (fun i x hx => by
      simpa only [dist_eq_norm] using (hρ i x hx).2.le) x
  have hout (x : X) (hx : x ∉ K) : f x - ∑ i : s, φ i x • (i.val.val : E) = 0 := by
    have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
      hx (interior_subset (hfK h))
    have hφ (i : s) : φ i x = 0 := by
      by_contra hi
      exact hx (interior_subset (hρ i x hi).1)
    simp [hfx, hφ]
  -- Integrate the uniform error only on that fixed compact neighbourhood.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
    (fun x hx => by rw [hout x hx, norm_zero])]
  calc
    (∫ x in K, ‖f x - ∑ i : s, φ i x • (i.val.val : E)‖ ∂μ)
        ≤ δ * μ.real K := by
      exact (le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs, abs_norm] using
          norm_setIntegral_le_of_norm_le_const (μ := μ)
            (f := fun x => ‖f x - ∑ i : s, φ i x • (i.val.val : E)‖)
            hK.measure_lt_top (fun x _ => by simpa only [norm_norm] using hbound x))
    _ < ε := by
      dsimp [δ]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [measureReal_nonneg (μ := μ) (s := K)]

end CompactlySupportedContinuousMap

section Cutoff

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [R1Space X] [LocallyCompactSpace X]
  [OpensMeasurableSpace X]

/-- A compactly supported continuous function whose integral against every measure lies between
the mass of a compact set `K` and the mass of an open neighbourhood `U` of `K`; the lower bound
needs the measure to be finite on compact sets. -/
theorem IsCompact.exists_compactlySupported_measure_le_integral_le {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : C_c(X, ℝ), (∀ (ρ : Measure X) [IsFiniteMeasureOnCompacts ρ],
      ρ K ≤ ENNReal.ofReal (∫ x, f x ∂ρ)) ∧
      ∀ ρ : Measure X, ENNReal.ofReal (∫ x, f x ∂ρ) ≤ ρ U := by
  obtain ⟨f, hf1, hfc, hfU, hfr⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  refine ⟨⟨f, hfc⟩, fun ρ _ ↦ ?_, fun ρ ↦ ?_⟩
  · exact (CompactlySupportedContinuousMap.integrable ⟨f, hfc⟩).measure_le_integral
      (ae_of_all _ fun x ↦ (hfr x).1) fun _ hx ↦ (hf1 hx).ge
  · exact integral_le_measure (fun x _ ↦ (hfr x).2) fun x hx ↦
      (image_eq_zero_of_notMem_tsupport fun h ↦ hx (hfU h)).le

end Cutoff

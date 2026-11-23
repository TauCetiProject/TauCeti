/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.Topology.PartitionOfUnity.Approximation

/-!
# Integrals of compactly supported functions: cutoffs and finite-rank approximation

A compactly supported continuous function with values in a real normed space can be
approximated in integral norm by finite sums of real compactly supported scalar functions
times vectors from any prescribed dense subset. Only finiteness of the measure on compact
sets is needed. In particular, no global finiteness or countability assumption is imposed.

This is the partition-of-unity approximation used to lift convolution coefficients through
dense coefficient maps. We use Mathlib's compactly supported partitions of unity.

On a locally compact `R1Space` with measurable open sets, a compact set `K` inside an open set
`U` has a compactly supported Urysohn cutoff whose integral against every measure is at most the
mass of `U`, and at least the mass of `K` for measures finite on compact sets.

## Main declarations

* `CompactlySupportedContinuousMap.exists_integral_norm_sub_sum_smul_lt`: finite-rank
  approximation in integral norm.
* `IsCompact.exists_compactlySupported_measure_le_integral_le`: a compactly supported cutoff
  whose integral lies between the masses of a compact set and of an open neighbourhood of it.
-/

public section

open MeasureTheory Set Metric
open scoped CompactlySupported

namespace CompactlySupportedContinuousMap

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

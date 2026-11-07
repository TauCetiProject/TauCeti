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
# Finite-rank approximation of compactly supported functions

A compactly supported continuous function with values in a real normed space can be
approximated in integral norm by finite sums of real compactly supported scalar functions
times vectors from any prescribed dense subset. Only finiteness of the measure on compact
sets is needed. In particular, no global finiteness or countability assumption is imposed.

This is the partition-of-unity approximation used to lift convolution coefficients through
dense coefficient maps. We use Mathlib's compactly supported partitions of unity.
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
  obtain ⟨s, ρ, hρc, hρ⟩ := exists_partitionOfUnity_norm_sub_lt f hS hfK hδ
  let φ (i : s) : C_c(X, ℝ) := ⟨ρ i, hρc i⟩
  refine ⟨s, φ, ?_⟩
  have hbound (x : X) : ‖f x - ∑ i : s, φ i x • (i.val.val : E)‖ ≤ δ :=
    ρ.norm_sub_sum_smul_le f (fun i => (i.val.val : E)) hδ.le (fun i x hx => (hρ i x hx).2.le) x
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

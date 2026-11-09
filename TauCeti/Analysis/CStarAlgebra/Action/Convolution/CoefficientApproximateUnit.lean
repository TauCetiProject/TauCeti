/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Multiplier
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnit

/-!
# Coefficient approximate units on the convolution algebra

An increasing approximate unit of the coefficient C⋆-algebra acts as the identity in the limit
on compactly supported convolution coefficients, in the L¹ norm. Uniform convergence on the
compact range of a coefficient function controls the error on its fixed compact support.
This is the dense-subalgebra approximation used to prove nondegeneracy of the canonical
coefficient map into crossed-product multipliers.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2. We use
`Filter.IsIncreasingApproximateUnit.tendstoUniformlyOn_mul_right` for the compact-range estimate.
-/

public section

open Filter MeasureTheory Topology
open scoped CompactlySupported

namespace TauCeti.CStarAction.ConvolutionAlgebra

variable {G A : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [OpensMeasurableSpace G] [NonUnitalCStarAlgebra A] [PartialOrder A]
  {α : CStarAction G A} {μ : Measure G} [IsFiniteMeasureOnCompacts μ]

/-- An increasing coefficient approximate unit acts on every compact-support coefficient
function as the identity in the L¹ limit. No Haar invariance is required. -/
theorem tendsto_coefficientMul {l : Filter A} (hl : l.IsIncreasingApproximateUnit)
    (f : ConvolutionAlgebra α μ) :
    Tendsto (fun e => coefficientMul e f) l (𝓝 f) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let K := tsupport f.ofConv
  have hK : IsCompact K := f.ofConv.hasCompactSupport
  let δ := ε / (μ.real K + 1)
  have hδ : 0 < δ := by positivity
  have he := Metric.tendstoUniformlyOn_iff.1
    (hl.tendstoUniformlyOn_mul_right
      (f.ofConv.hasCompactSupport.isCompact_range f.ofConv.continuous)) δ hδ
  filter_upwards [he] with e he
  have hb (s : G) : ‖e * f.ofConv s - f.ofConv s‖ ≤ δ := by
    simpa only [id_eq, dist_eq_norm, norm_sub_rev] using (he _ (Set.mem_range_self s)).le
  have hz (s : G) (hs : s ∉ K) : ‖e * f.ofConv s - f.ofConv s‖ = 0 := by
    simp [image_eq_zero_of_notMem_tsupport hs]
  rw [dist_eq_norm, norm_eq_integral_norm]
  simp only [ofConv_sub, ofConv_coefficientMul, CompactlySupportedContinuousMap.sub_apply,
    CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
  calc
    (∫ s, ‖e * f.ofConv s - f.ofConv s‖ ∂μ)
        = ∫ s in K, ‖e * f.ofConv s - f.ofConv s‖ ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm
    _ ≤ δ * μ.real K := by
      have h := norm_setIntegral_le_of_norm_le_const
        (f := fun s => ‖e * f.ofConv s - f.ofConv s‖) (hK.measure_lt_top (μ := μ))
        (fun s (_ : s ∈ K) => by simpa only [norm_norm] using hb s)
      rwa [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at h
    _ < ε := by
      dsimp [δ]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [measureReal_nonneg (μ := μ) (s := K)]

end TauCeti.CStarAction.ConvolutionAlgebra

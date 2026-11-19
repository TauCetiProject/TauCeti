/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.Functoriality
public import TauCeti.MeasureTheory.Integral.CompactlySupported

/-!
# Dense range of equivariant convolution maps

An equivariant coefficient homomorphism with dense range induces a map with dense range
on the compact-support convolution algebras in the L¹ norm, and on their L¹ completions.
In particular, this applies to surjective coefficient maps. This supplies the density input
for surjectivity of maps on full crossed products, whose homomorphisms have closed range.

The argument approximates compact-support coefficients by finite sums `s ↦ φ s • a`,
with `a` in the range of the coefficient map, then lifts those finitely many coefficients.
No continuous section of the coefficient map is needed.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2, for the dense coefficient
algebras used in crossed-product functoriality. The approximation uses Mathlib's compactly
supported partitions of unity through
`CompactlySupportedContinuousMap.exists_integral_norm_sub_sum_smul_lt`.
-/

public section

noncomputable section

open MeasureTheory UniformSpace
open scoped CompactlySupported CStarAlgebra

namespace TauCeti.CStarAction.Hom

variable {G A B : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [OpensMeasurableSpace G]
  [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  {α : CStarAction G A} {β : CStarAction G B}
  (φ : Hom α β) (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

/-- A dense coefficient map induces a dense map of compact-support convolution algebras
with their L¹ norms. This requires neither Haar invariance nor full support of the measure. -/
theorem denseRange_convolutionMap (hφ : DenseRange φ) :
    DenseRange (φ.convolutionMap μ) := by
  classical
  rw [Metric.denseRange_iff]
  intro f ε hε
  obtain ⟨s, χ, hχ⟩ := f.ofConv.exists_integral_norm_sub_sum_smul_lt μ hφ hε
  choose a ha using fun i : s => i.val.property
  let g : ConvolutionAlgebra α μ := ∑ i : s, ConvolutionAlgebra.smulRight (χ i) (a i)
  refine ⟨g, ?_⟩
  rw [dist_eq_norm, ConvolutionAlgebra.norm_eq_integral_norm]
  convert hχ using 1
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  simp only [ConvolutionAlgebra.ofConv_sub, CompactlySupportedContinuousMap.sub_apply,
    convolutionMap_apply]
  have hg : g.ofConv = ∑ i : s, (ConvolutionAlgebra.smulRight (χ i) (a i) :
      ConvolutionAlgebra α μ).ofConv := by
    simpa only [ConvolutionAlgebra.linearEquiv_apply] using
      map_sum (ConvolutionAlgebra.linearEquiv α μ)
        (fun i : s => ConvolutionAlgebra.smulRight (χ i) (a i)) Finset.univ
  simp only [hg, CompactlySupportedContinuousMap.sum_apply,
    ConvolutionAlgebra.ofConv_smulRight_apply, map_sum]
  simp only [← Complex.coe_smul, map_smul, ha]

variable [BorelSpace G] [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- The induced map on twisted L¹ completions has dense range whenever the coefficient map
does. -/
theorem denseRange_convolutionMapL1 (hφ : DenseRange φ) :
    DenseRange (φ.convolutionMapL1 μ) := by
  have hd : DenseRange (fun f : ConvolutionAlgebra α μ =>
      (φ.convolutionMap μ f : Completion (ConvolutionAlgebra β μ))) :=
    Completion.denseRange_coe.comp (φ.denseRange_convolutionMap μ hφ)
      (Completion.continuous_coe _)
  exact hd.mono (by
    rintro _ ⟨f, rfl⟩
    exact ⟨(f : Completion (ConvolutionAlgebra α μ)), by simp⟩)

end TauCeti.CStarAction.Hom

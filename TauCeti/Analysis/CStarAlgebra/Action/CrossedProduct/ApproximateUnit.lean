/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Full
public import TauCeti.Analysis.CStarAlgebra.Action.Convolution.ApproximateUnit
public import TauCeti.Analysis.Normed.Ring.ApproximateUnit

/-!
# Coefficient-compatible approximate units of the full crossed product

The elementary functions `s ↦ φ s • e`, where `φ` has integral one and support shrinking to the
identity and `e` runs through an increasing approximate unit of the coefficient algebra, remain
an approximate unit after passage to the full crossed product. Their images are eventually in
the closed unit ball. Thus these particular compact-support approximants, not just an abstract
approximate unit of the completed C⋆-algebra, approximate every crossed-product element on both
sides. This supplies the approximation used to study nondegenerate integrated representations.

The transfer theorem also applies to any bounded approximate unit of the L¹-normed convolution
algebra. The argument uses the dense canonical map and its norm bound; no faithful coefficient
representation, separability, or global σ-finiteness is needed.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Chapter 2.
The compact-support approximate units are constructed in
`TauCeti.Analysis.CStarAlgebra.Action.Convolution.ApproximateUnit`.
-/

public section

noncomputable section

open Filter MeasureTheory Topology
open scoped CompactlySupported

namespace TauCeti.CStarAction.FullCrossedProduct

variable {G A : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [NonUnitalCStarAlgebra A] {α : CStarAction G A} {μ : Measure G}
  [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G] [μ.IsHaarMeasure]

/-- The elementary approximate unit of the full crossed product is eventually contractive. -/
theorem eventually_norm_of_smulRight_le_one [PartialOrder A] {ι : Type*} {l : Filter ι}
    {φ : ι → C_c(G, ℝ)} (hφ : ∀ᶠ i in l, 0 ≤ φ i)
    (hφ1 : ∀ᶠ i in l, ∫ s, φ i s ∂μ = 1) {lA : Filter A}
    (hlA : lA.IsIncreasingApproximateUnit) :
    ∀ᶠ p : ι × A in l ×ˢ lA, ‖of α μ (ConvolutionAlgebra.smulRight (φ p.1) p.2)‖ ≤ 1 := by
  filter_upwards [ConvolutionAlgebra.eventually_norm_smulRight_le_one
    (α := α) hφ hφ1 hlA] with p hp
  exact (norm_of_le _).trans hp

/-- Elementary compact-support functions built from a normalized shrinking bump and an
increasing coefficient approximate unit form an approximate unit of the full crossed product. -/
theorem isApproximateUnit_map_smulRight [PartialOrder A] {ι : Type*} {l : Filter ι}
    [l.NeBot] {φ : ι → C_c(G, ℝ)} (hφ : ∀ᶠ i in l, 0 ≤ φ i)
    (hφ1 : ∀ᶠ i in l, ∫ s, φ i s ∂μ = 1)
    (hφs : Tendsto (fun i => tsupport (φ i)) l (𝓝 1).smallSets) {lA : Filter A}
    (hlA : lA.IsIncreasingApproximateUnit) :
    (map (fun p : ι × A => of α μ (ConvolutionAlgebra.smulRight (φ p.1) p.2))
      (l ×ˢ lA)).IsApproximateUnit := by
  have h := (ConvolutionAlgebra.isApproximateUnit_map_smulRight
    (α := α) hφ hφ1 hφs hlA).map_of_denseRange (of α μ) continuous_of denseRange_of
      (eventually_map.2 (eventually_norm_of_smulRight_le_one hφ hφ1 hlA))
  simpa only [map_map, Function.comp_def] using h

end TauCeti.CStarAction.FullCrossedProduct

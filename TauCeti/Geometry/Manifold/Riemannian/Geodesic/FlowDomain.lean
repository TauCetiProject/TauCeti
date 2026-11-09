/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Flow
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability of prefixes of the geodesic flow domain

Let `Z : P → TM` be a continuous family of initial tangent vectors, `D ⊆ M` a closed set and
`u` a real number. The parameters `p` whose maximal geodesic is defined on `[0, u]` and stays in
`D` there form a measurable set, for any measurable structure on `P` containing the open sets.

The condition that `u` lies in the maximal geodesic interval is open in `p`, because the domain of
the geodesic flow is open (`TauCeti.Manifold.isOpen_setOfPred_mem_geodesicInterval`). On this open
set the whole interval `[0, u]` lies in the maximal interval, the geodesic at each fixed time
depends continuously on `p` (`TauCeti.Manifold.contMDiffOn_maximalGeodesic`), and staying in `D`
up to time `u` is an intersection of relatively closed conditions. Neither a common lifetime for
all parameters nor geodesics that stay in `D` for all times are needed.

This is the measurability input for times, such as cut times, defined as suprema of the times up to
which a geodesic stays in a closed set and satisfies a measurable condition.
-/

public section

open Bundle Manifold Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {P : Type*} [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]

/-- For a continuous family `Z` of initial tangent vectors and a closed set `D`, the parameters
whose maximal geodesic is defined on `[0, u]` and maps `[0, u]` into `D` form a measurable set. -/
theorem measurableSet_setOfPred_Icc_subset_geodesicInterval_and_mapsTo
    {Z : P → TangentBundle I M} (hZ : Continuous Z) {D : Set M} (hD : IsClosed D) (u : ℝ) :
    MeasurableSet {p | Icc 0 u ⊆ geodesicInterval I M (Z p).proj (Z p).2 ∧
      MapsTo (maximalGeodesic I M (Z p).proj (Z p).2) (Icc 0 u) D} := by
  rcases lt_or_ge u 0 with hu | hu
  · simp [Icc_eq_empty_of_lt hu, mapsTo_empty]
  let A : Set P := {p | u ∈ geodesicInterval I M (Z p).proj (Z p).2}
  have hA : IsOpen A := isOpen_setOfPred_mem_geodesicInterval.preimage
    (hZ.prodMk continuous_const)
  have htime (p : A) : Icc 0 u ⊆ geodesicInterval I M (Z p.val).proj (Z p.val).2 :=
    ordConnected_geodesicInterval.out zero_mem_geodesicInterval p.property
  have hflow (s : Icc (0 : ℝ) u) :
      Continuous fun p : A ↦ maximalGeodesic I M (Z p.val).proj (Z p.val).2 s.val :=
    contMDiffOn_maximalGeodesic.continuousOn.comp_continuous
      ((hZ.comp continuous_subtype_val).prodMk continuous_const) fun p ↦ htime p s.property
  let B : Set A := ⋂ s : Icc (0 : ℝ) u,
    (fun p : A ↦ maximalGeodesic I M (Z p.val).proj (Z p.val).2 s.val) ⁻¹' D
  have hB : IsClosed B := isClosed_iInter fun s ↦ hD.preimage (hflow s)
  obtain ⟨C, hC, hBC⟩ :=
    (IsEmbedding.subtypeVal (p := (· ∈ A))).isInducing.image_eq_isClosed_inter_range hB
  have heq : {p | Icc 0 u ⊆ geodesicInterval I M (Z p).proj (Z p).2 ∧
      MapsTo (maximalGeodesic I M (Z p).proj (Z p).2) (Icc 0 u) D} =
        (Subtype.val : A → P) '' B := by
    ext p
    constructor
    · rintro ⟨hp, hpD⟩
      exact ⟨⟨p, hp (right_mem_Icc.mpr hu)⟩, mem_iInter.2 fun s ↦ hpD s.property, rfl⟩
    · rintro ⟨p, hpB, rfl⟩
      exact ⟨htime p, fun t ht ↦ mem_iInter.1 hpB ⟨t, ht⟩⟩
  rw [heq, hBC]
  exact hC.measurableSet.inter (by simpa only [Subtype.range_val] using hA.measurableSet)

end TauCeti.Manifold

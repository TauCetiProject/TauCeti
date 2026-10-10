/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Coordinates
public import TauCeti.Analysis.Calculus.QuotientRange
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Fixed complementary coordinates for intrinsic normal spaces

Near a point of a smooth embedding, the intrinsic normal fibres can all be identified with
one closed subspace of the ambient model. These identifications take tangent-chart coordinates
of an ambient representative and then project along the moving tangent range. Their inverse
uses the fixed complementary representative in the same tangent chart.

The coordinate operators have one less derivative than the embedding. At a point this includes
smooth and analytic regularity; for finite or analytic regularity we also obtain one open
neighbourhood on which the operators have that regularity. Smoothness at a point alone does not
supply a single neighbourhood for all derivative orders. These are fibre coordinates, independent
of any topology or atlas on the total normal bundle, and supply local models for constructing it.

The construction composes `normalSpaceEquivInTangentCoordinates` with
`ContinuousLinearMap.quotientRangeEquiv`. Local existence uses the fixed-complement theorem
`ContinuousAt.exists_isInvertible_coprod_subtypeL` and Mathlib's regularity of the differential
in tangent coordinates.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, the
normal-bundle construction preceding Theorem 6.24.
-/

public section

noncomputable section

open Set Filter Topology Bundle
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {n : ℕ∞ω}

section Coordinates

variable {P : Type*} [TopologicalSpace P] [AddCommGroup P] [Module 𝕜 P]

/-- Intrinsic normal coordinates in a fixed complementary parameter space. The complement
is specified by `B`; invertibility says it complements the coordinate differential's range. -/
def normalSpaceEquivOfComplement (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    {x₀ x : M} (hx : x ∈ (chartAt H x₀).source)
    (hy : f x ∈ (chartAt G (f x₀)).source) (B : P →L[𝕜] F)
    (hB : ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible) :
    f.NormalSpace x hn ≃L[𝕜] P :=
  (f.normalSpaceEquivInTangentCoordinates hn hx hy).trans
    ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x).quotientRangeEquiv B hB)

/-- On ambient tangent representatives, normal coordinates take the complementary component
of tangent-chart coordinates. -/
@[simp] theorem normalSpaceEquivOfComplement_normalClass
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    {x₀ x : M} (hx : x ∈ (chartAt H x₀).source)
    (hy : f x ∈ (chartAt G (f x₀)).source) (B : P →L[𝕜] F)
    (hB : ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible)
    (v : TangentSpace J (f x)) :
    f.normalSpaceEquivOfComplement hn hx hy B hB (f.normalClass x hn v) =
      (inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₀ x).quotientRangeCoordinate B
        ((trivializationAt F (TangentSpace J) (f x₀)) ⟨f x, v⟩).2 := by
  simp [normalSpaceEquivOfComplement]

/-- Inverse normal coordinates use the chosen complementary vector in the inverse ambient
tangent chart and take its normal class. -/
@[simp] theorem normalSpaceEquivOfComplement_symm_apply
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    {x₀ x : M} (hx : x ∈ (chartAt H x₀).source)
    (hy : f x ∈ (chartAt G (f x₀)).source) (B : P →L[𝕜] F)
    (hB : ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible) (w : P) :
    (f.normalSpaceEquivOfComplement hn hx hy B hB).symm w =
      f.normalClass x hn ((trivializationAt F (TangentSpace J) (f x₀)).symm (f x) (B w)) := by
  simp [normalSpaceEquivOfComplement]

/-- Changing the complement and the ambient tangent chart gives the normal-coordinate
transition by applying the ambient tangent transition to the old complementary representative. -/
theorem normalSpaceEquivOfComplement_apply_symm
    {P' : Type*} [TopologicalSpace P'] [AddCommGroup P'] [Module 𝕜 P']
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0) {x₀ x₁ x : M}
    (hx₀ : x ∈ (chartAt H x₀).source) (hy₀ : f x ∈ (chartAt G (f x₀)).source)
    (hx₁ : x ∈ (chartAt H x₁).source) (hy₁ : f x ∈ (chartAt G (f x₁)).source)
    (B : P →L[𝕜] F) (C : P' →L[𝕜] F)
    (hB : ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x).coprod B).IsInvertible)
    (hC : ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₁ x).coprod C).IsInvertible) (w : P) :
    f.normalSpaceEquivOfComplement hn hx₁ hy₁ C hC
        ((f.normalSpaceEquivOfComplement hn hx₀ hy₀ B hB).symm w) =
      (inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₁ x).quotientRangeCoordinate C
        (((trivializationAt F (TangentSpace J) (f x₀)).coordChangeL 𝕜
          (trivializationAt F (TangentSpace J) (f x₁)) (f x)) (B w)) := by
  rw [normalSpaceEquivOfComplement_symm_apply, normalSpaceEquivOfComplement_normalClass,
    Trivialization.coordChangeL_apply _ _ (by simpa using And.intro hy₀ hy₁)]

end Coordinates

variable [CompleteSpace F] {P : Type*} [NormedAddCommGroup P] [NormedSpace 𝕜 P]

/-- For any valid fixed complement, the normal-coordinate operator is `C^m` at the chart
centre when the embedding is `C^(m+1)` there. This includes smooth and analytic regularity. -/
theorem contMDiffAt_normalSpaceComplementCoordinate
    (f : SmoothEmbedding I J n M N) {m : ℕ∞ω} (hm : m + 1 ≤ n) (x₀ : M)
    (B : P →L[𝕜] F)
    (hB : ((inTangentCoordinates I J _root_.id (f : M → N)
      (mfderiv I J (f : M → N)) x₀ x₀).coprod B).IsInvertible) :
    ContMDiffAt I 𝓘(𝕜, F →L[𝕜] P) m
      (fun x => (inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₀ x).quotientRangeCoordinate B) x₀ := by
  obtain ⟨e, he⟩ := hB
  have : CompleteSpace (E × P) :=
    (e.isUniformEmbedding.completeSpace_congr e.surjective).mpr inferInstance
  have hq : ContDiffAt 𝕜 m (fun L : E →L[𝕜] F => L.quotientRangeCoordinate B)
      (inTangentCoordinates I J _root_.id (f : M → N)
        (mfderiv I J (f : M → N)) x₀ x₀) :=
    (contDiffAt_id (𝕜 := 𝕜)).quotientRangeCoordinate B ⟨e, he⟩
  exact hq.comp_contMDiffAt (f.contMDiff.contMDiffAt.mfderiv_const hm)

/-- A positive-regularity embedding has a fixed closed complementary model for its intrinsic
normal fibres near each point. For every finite or analytic order `m` with `m + 1 ≤ n`, the
complementary coordinate operators are `C^m` on one open neighbourhood contained in the
source and ambient tangent-chart domains. No metric or finite-dimensionality is required. -/
theorem exists_contMDiffOn_normalSpaceComplementCoordinate
    {m : ℕ∞ω} [IsManifold I m M]
    (f : SmoothEmbedding I J n M N) (hm : m + 1 ≤ n) (hm' : m ≠ ∞)
    (x₀ : M) :
    ∃ Q : Submodule 𝕜 F, IsClosed (Q : Set F) ∧
      ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
        U ⊆ (chartAt H x₀).source ∩ f ⁻¹' (chartAt G (f x₀)).source ∧
        (∀ x ∈ U, ((inTangentCoordinates I J _root_.id (f : M → N)
          (mfderiv I J (f : M → N)) x₀ x).coprod Q.subtypeL).IsInvertible) ∧
        ContMDiffOn I 𝓘(𝕜, F →L[𝕜] Q) m
          (fun x => (inTangentCoordinates I J _root_.id (f : M → N)
            (mfderiv I J (f : M → N)) x₀ x).quotientRangeCoordinate Q.subtypeL) U := by
  have hn : n ≠ 0 := ENat.one_le_iff_ne_zero_withTop.mp ((le_add_left le_rfl).trans hm)
  let A := inTangentCoordinates I J _root_.id (f : M → N)
    (mfderiv I J (f : M → N)) x₀
  have hA : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] F) m A x₀ :=
    f.contMDiff.contMDiffAt.mfderiv_const hm
  obtain ⟨Q, hQ, W, hW, hxW, hInv⟩ := hA.continuousAt.exists_isInvertible_coprod_subtypeL
    (f.hasLeftInverse_inTangentCoordinates_mfderiv hn (mem_chart_source H x₀)
      (mem_chart_source G (f x₀)))
  obtain ⟨V, hV, hAV⟩ := (contMDiffAt_iff_contMDiffOn_nhds hm').mp hA
  let S := (chartAt H x₀).source ∩ f ⁻¹' (chartAt G (f x₀)).source
  have hS : IsOpen S := (chartAt H x₀).open_source.inter
    ((chartAt G (f x₀)).open_source.preimage f.contMDiff.continuous)
  have hxS : x₀ ∈ S := ⟨mem_chart_source H x₀, mem_chart_source G (f x₀)⟩
  obtain ⟨V', hV'sub, hV', hxV'⟩ := mem_nhds_iff.mp hV
  obtain ⟨e, _⟩ := hInv x₀ hxW
  have : CompleteSpace (E × Q) :=
    (e.isUniformEmbedding.completeSpace_congr e.surjective).mpr inferInstance
  refine ⟨Q, hQ, W ∩ V' ∩ S, (hW.inter hV').inter hS,
    ⟨⟨hxW, hxV'⟩, hxS⟩, inter_subset_right,
    (fun x hx => hInv x hx.1.1), ?_⟩
  intro x hx
  have hq : ContDiffAt 𝕜 m (fun L : E →L[𝕜] F => L.quotientRangeCoordinate Q.subtypeL)
      (A x) := (contDiffAt_id (𝕜 := 𝕜)).quotientRangeCoordinate Q.subtypeL (hInv x hx.1.1)
  exact hq.contMDiffAt.comp_contMDiffWithinAt x
    ((hAV x (hV'sub hx.1.2)).mono (fun _ hy => hV'sub hy.1.2))

end TauCeti.SmoothEmbedding

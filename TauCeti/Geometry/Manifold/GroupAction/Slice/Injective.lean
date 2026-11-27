/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.GroupAction.Slice.Theorem
public import TauCeti.Topology.Covering.BalancedProduct.SliceInjective

/-!
# The slice map of a proper action is injective after shrinking the slice

Let a finite-dimensional real Lie group `G` act smoothly and properly on a manifold `M`, let `K`
be the stabilizer of a point `x`, and let `ι : Z → M` be a smooth `K`-equivariant transverse slice
at a `K`-fixed point `z₀` with `ι z₀ = x`. The descended action map `[g, z] ↦ g • ι z` of
`G ×_K Z` is a local diffeomorphism at `[1, z₀]`
(`TauCeti.BalancedProduct.isLocalDiffeomorphAt_liftRightTranslation_one`), hence injective near
`[1, z₀]`. By properness it is then injective on `G ×_K V` for a neighbourhood `V` of `z₀`
(`TauCeti.BalancedProduct.exists_mem_nhds_injOn_liftRightTranslation`). This is the injectivity
half of the slice theorem `G ×_K V ≅ G • ι(V)` (Meinrenken, Theorem 1.25).

## Main results

* `TauCeti.BalancedProduct.exists_mem_nhds_injOn_liftRightTranslation_of_isCompl`: injectivity of
  the descended action map on `G ×_K V` for a transverse slice at a point of a proper action.

## References

* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Theorem 1.25 and its proof.
-/

public section

open Function Set Manifold MulAction Module Topology
open scoped ContDiff Manifold

namespace TauCeti.BalancedProduct

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {G : Type*} [Group G] {K : Subgroup G} {Z : Type*} [MulAction K Z]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace G]
  [ChartedSpace H G] [LieGroup I ∞ G] [IsClosed (K : Set G)]
  {EZ HZ : Type*} [NormedAddCommGroup EZ] [NormedSpace ℝ EZ] [FiniteDimensional ℝ EZ]
  [TopologicalSpace HZ] {IZ : ModelWithCorners ℝ EZ HZ} [IZ.Boundaryless] [TopologicalSpace Z]
  [ChartedSpace HZ Z] [IsManifold IZ ∞ Z] [T2Space Z]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [ChartedSpace F K] [LieGroup 𝓘(ℝ, F) ∞ K] [ContMDiffSMul 𝓘(ℝ, F) I ∞ K G]
  [ContMDiffSMul 𝓘(ℝ, F) IZ ∞ K Z]
  {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M] [IsManifold IM ∞ M] [MulAction G M] [ContMDiffSMul I IM ∞ G M]
  {ι : Z →ₑ[((↑) : K → G)] M}

/-- **The slice map of a proper action is injective after shrinking the slice.** Let `G` act
properly on `M`, let `K` be the stabilizer of `ι z₀` for a smooth `K`-equivariant `ι : Z → M` at a
`K`-fixed point `z₀`, whose differential at `z₀` is injective with range a complement of the orbit
tangent space `𝔤 · ι z₀`, and let `dim K = dim 𝔤_{ι z₀}`. Then `[g, z] ↦ g • ι z` is injective on
the classes `[g, z]` with `z` in some neighbourhood `V` of `z₀`. -/
theorem exists_mem_nhds_injOn_liftRightTranslation_of_isCompl [CompleteSpace EM] [ProperSMul G M]
    (hι : ContMDiff IZ IM ∞ ι) {z₀ : Z} (hz₀ : ∀ k : K, k • z₀ = z₀)
    (hK : (K : Set G) = MulAction.stabilizer G (ι z₀)) (hinj : Injective (mfderiv IZ IM ι z₀))
    (hcompl : IsCompl ((InfinitesimalAction.fundamental I G IM M).orbitTangent (ι z₀))
      (LinearMap.range (mfderiv IZ IM ι z₀).toLinearMap))
    (hF : finrank ℝ F = finrank ℝ ((InfinitesimalAction.fundamental I G IM M).isotropy (ι z₀))) :
    ∃ V ∈ 𝓝 z₀, InjOn (liftRightTranslation ι)
      {y | ∃ g, ∃ z ∈ V, y = mk K (K.toRightTranslation g) z} := by
  let _ := rightTranslationChartedSpace K Z I IZ F
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  have := ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, F)) (I' := IZ) (G := K) (M := Z) ∞
  have hf := isLocalDiffeomorphAt_liftRightTranslation_one hι hinj hcompl hF
  refine exists_mem_nhds_injOn_liftRightTranslation hz₀ hK hι.continuous.continuousAt
    (hf.localInverse.open_target.mem_nhds hf.localInverse_mem_target) fun a ha b hb hab ↦ ?_
  rw [← hf.localInverse_left_inv ha, hab, hf.localInverse_left_inv hb]

end TauCeti.BalancedProduct

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Distance
public import TauCeti.Topology.UniformSpace.Complete
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic

/-!
# Completeness through a closed embedded map

A closed embedded map into a complete Riemannian manifold transfers completeness to its
domain when its differential has a global norm bound. In particular, this applies to the
intrinsic metric induced on a closed embedded submanifold.

Source references: https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public section

open Bundle Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti.IsRiemannianManifold

variable {E F H K M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [EMetricSpace M] [EMetricSpace N] [ChartedSpace H M] [ChartedSpace K N]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [RiemannianBundle (TangentSpace J : N → Type _)]
  [IsRiemannianManifold I M] [IsRiemannianManifold J N] [CompleteSpace N]

/-- A closed embedded map with globally bounded differential into a complete Riemannian
manifold has complete domain. The domain carries its intrinsic Riemannian distance. -/
theorem completeSpace_of_isClosedEmbedding_of_norm_mfderiv_le {ι : M → N}
    (hι : ContMDiff I J 1 ι) (hemb : Topology.IsClosedEmbedding ι) (C : NNReal)
    (hnorm : ∀ x (v : TangentSpace I x), ‖mfderiv I J ι x v‖ ≤ C * ‖v‖) :
    CompleteSpace M := by
  have hLip : LipschitzWith (C + 1) ι := by
    apply lipschitzWith_of_norm_mfderiv_le hι (by positivity)
    intro x v
    apply (hnorm x v).trans
    simp only [NNReal.coe_add, NNReal.coe_one, add_mul, one_mul]
    exact le_add_of_nonneg_right (norm_nonneg v)
  exact hemb.completeSpace_of_uniformContinuous hLip.uniformContinuous

end TauCeti.IsRiemannianManifold

namespace TauCeti.IsRiemannianManifold

variable {E F H K M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [EMetricSpace N] [ChartedSpace H M] [ChartedSpace K N]
  [IsManifold I 1 M] [IsManifold J 1 N]
  [RiemannianBundle (TangentSpace J : N → Type _)]
  [IsRiemannianManifold J N] [CompleteSpace N] {n : ℕ∞ω}
  [IsContMDiffRiemannianBundle J n F (TangentSpace J : N → Type _)]

/-- The actual pullback metric on a closed embedded immersion into a complete Riemannian
manifold is intrinsically complete. The uniformity is explicitly the one induced by that metric. -/
theorem completeSpace_pullback_of_isClosedEmbedding {ι : M → N}
    (hι : ContMDiff I J (n + 1) ι)
    (hinj : ∀ x, Injective (mfderiv I J ι x)) (hemb : Topology.IsClosedEmbedding ι) :
    letI : T3Space M := hemb.isEmbedding.t3Space
    let g := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
      (IB := J) (n := n) (F := F) (V := (TangentSpace J : N → Type _))
    let gM := g.pullback ι hι hinj
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨gM.toRiemannianMetric⟩
    letI := Bundle.instIsContMDiffRiemannianBundle gM
    letI := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
      (IB := I) (n := n) (F := E) (V := (TangentSpace I : M → Type _))
    let eM := EMetricSpace.ofRiemannianMetric I M
    @CompleteSpace M eM.toUniformSpace := by
  let : T3Space M := hemb.isEmbedding.t3Space
  let g := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := J) (n := n) (F := F) (V := (TangentSpace J : N → Type _))
  let gM := g.pullback ι hι hinj
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨gM.toRiemannianMetric⟩
  let := Bundle.instIsContMDiffRiemannianBundle gM
  let := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := n) (F := E) (V := (TangentSpace I : M → Type _))
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  apply completeSpace_of_isClosedEmbedding_of_norm_mfderiv_le
    (hι.of_le (by simp)) hemb 1
  intro x v
  simp only [NNReal.coe_one, one_mul]
  apply le_of_eq
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
  rw [ContMDiffRiemannianMetric.inner_riemannianBundle gM x v v]
  exact congrArg Real.sqrt
    (ContMDiffRiemannianMetric.pullback_ofIsContMDiffRiemannianBundle_inner
      ι hι hinj x v v).symm

end TauCeti.IsRiemannianManifold

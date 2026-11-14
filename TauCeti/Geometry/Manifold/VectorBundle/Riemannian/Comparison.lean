/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import TauCeti.Topology.VectorBundle.Riemannian.Comparison

/-!
# Uniform comparison of differentiable metrics

Two differentiable metrics on a finite-rank real vector bundle have uniform positive two-sided
comparison constants on a compact set. In particular every metric on a compact manifold is
uniformly comparable to a chosen reference metric. These bounds allow one to use a fixed metric
for estimates while varying another metric. The statements use the preexisting fibre topology,
but require no fibre norm, inner-product, or `RiemannianBundle` instances.

The metrics may have different regularity, and models with corners are allowed. The compact-set
statement also applies on a noncompact base; no global comparison is asserted there.
-/

public section

open Bundle Set
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {m n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousConstSMul ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- Two differentiable metrics are uniformly comparable on a compact subset, with strictly
positive constants valid for every fibre vector. The reference metric may have a different
regularity from the metric being estimated. -/
theorem exists_pos_mul_inner_self_le_and_le_of_isCompact (g : ContMDiffRiemannianMetric IB n F E)
    (g₀ : ContMDiffRiemannianMetric IB m F E) {K : Set B} (hK : IsCompact K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ K, ∀ v : E x,
      c * g₀.inner x v v ≤ g.inner x v v ∧ g.inner x v v ≤ C * g₀.inner x v v :=
  g.toContinuousRiemannianMetric.exists_pos_mul_inner_self_le_and_le_of_isCompact
    g₀.toContinuousRiemannianMetric hK

/-- On a compact base, any two differentiable metrics have global positive two-sided comparison
constants. This includes smooth metrics on a closed manifold, in every dimension. -/
theorem exists_pos_mul_inner_self_le_and_le_of_compactSpace [CompactSpace B]
    (g : ContMDiffRiemannianMetric IB n F E) (g₀ : ContMDiffRiemannianMetric IB m F E) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, ∀ v : E x,
      c * g₀.inner x v v ≤ g.inner x v v ∧ g.inner x v v ≤ C * g₀.inner x v v :=
  g.toContinuousRiemannianMetric.exists_pos_mul_inner_self_le_and_le_of_compactSpace
    g₀.toContinuousRiemannianMetric

end Bundle.ContMDiffRiemannianMetric

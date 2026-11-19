/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Lowering the smoothness of a Riemannian metric

A `C^n` Riemannian metric on a vector bundle is in particular a `C^m` Riemannian metric for every
`m ≤ n`. This lets a metric built with more regularity than needed, such as an analytic model
metric, be used by results stated for smooth metrics.

In a `C^n` Riemannian bundle the squared fibre norm is a `C^n` function on the total space, the
smooth counterpart of `TauCeti.continuous_norm_bundle`.

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.ofLE`: a `C^n` metric regarded as a `C^m` metric, `m ≤ n`.

## Main results

* `TauCeti.contMDiff_norm_sq_bundle`: the squared fibre norm `z ↦ ‖z.2‖²` is `C^n` on the total
  space of a `C^n` Riemannian bundle.
-/

public section

open Bundle
open scoped Manifold ContDiff

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {m n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- A `C^n` Riemannian metric regarded as a `C^m` Riemannian metric, for `m ≤ n`. -/
def ofLE (g : ContMDiffRiemannianMetric IB n F E) (h : m ≤ n) :
    ContMDiffRiemannianMetric IB m F E :=
  { g with contMDiff := g.contMDiff.of_le h }

/-- Lowering the smoothness of a metric does not change its inner products. -/
@[simp]
theorem ofLE_inner (g : ContMDiffRiemannianMetric IB n F E) (h : m ≤ n) :
    (g.ofLE h).inner = g.inner :=
  (rfl)

/-- Lowering the smoothness of a metric does not change the underlying Riemannian metric. -/
@[simp]
theorem toRiemannianMetric_ofLE (g : ContMDiffRiemannianMetric IB n F E) (h : m ≤ n) :
    (g.ofLE h).toRiemannianMetric = g.toRiemannianMetric :=
  (rfl)

/-- Forgetting regularity to the same order leaves a metric unchanged. -/
@[simp]
theorem ofLE_refl (g : ContMDiffRiemannianMetric IB n F E) (h : n ≤ n) :
    g.ofLE h = g := (rfl)

/-- The native fibre inner product installed from a metric evaluates to that metric. -/
theorem inner_eq [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousConstSMul ℝ (E x)]
    (g : ContMDiffRiemannianMetric IB n F E) (x : B) (v w : E x) :
    letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
    Inner.inner ℝ v w = g.inner x v w := by
  rfl

/-- The squared fibre norm installed from a metric is its diagonal value. -/
theorem norm_sq [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousConstSMul ℝ (E x)]
    (g : ContMDiffRiemannianMetric IB n F E) (x : B) (v : E x) :
    letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
    ‖v‖ ^ 2 = g.inner x v v := by
  let : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
  exact norm_sq_eq_re_inner (𝕜 := ℝ) v

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContMDiffRiemannianBundle IB n F E]

variable (IB n F E) in
/-- In a `C^n` Riemannian bundle, the squared fibre norm is a `C^n` function on the total
space. -/
theorem contMDiff_norm_sq_bundle :
    ContMDiff (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) n fun z : TotalSpace F E ↦ ‖z.2‖ ^ 2 := by
  have hid : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) n
      fun z : TotalSpace F E ↦ (⟨z.proj, z.2⟩ : TotalSpace F E) := contMDiff_id
  simpa only [real_inner_self_eq_norm_sq] using hid.inner_bundle hid

end TauCeti

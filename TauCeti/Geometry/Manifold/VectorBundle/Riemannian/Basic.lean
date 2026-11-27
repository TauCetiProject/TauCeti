/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Basic API for `C^n` Riemannian metrics on vector bundles

A `C^n` Riemannian metric on a vector bundle is in particular a `C^m` Riemannian metric for every
`m ≤ n`. This lets a metric built with more regularity than needed, such as an analytic model
metric, be used by results stated for smooth metrics. The file also evaluates the fibre inner
product space structure that `RiemannianBundle` installs from a `C^n` metric `g`: its inner
product is `g.inner` (`Bundle.ContMDiffRiemannianMetric.inner_eq`) and its squared norm is the
diagonal value `g.inner x v v` (`Bundle.ContMDiffRiemannianMetric.norm_sq`). Over the base set of
an atlas trivialization of a `C^n` vector bundle with finite-dimensional model fibre, a `C^n`
metric reads as a `C^n` family of bilinear forms on the model fibre
(`Bundle.ContMDiffRiemannianMetric.exists_contMDiffOn_apply_eq_inner_symm`).

In a `C^n` Riemannian bundle the squared fibre norm is a `C^n` function on the total space, the
smooth counterpart of `TauCeti.continuous_norm_bundle`.

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.ofLE`: a `C^n` metric regarded as a `C^m` metric, `m ≤ n`.

## Main results

* `TauCeti.contMDiff_norm_sq_bundle`: the squared fibre norm `z ↦ ‖z.snd‖²` is `C^n` on the total
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

/-- The continuous metric underlying a `C^n` metric has the same inner products. -/
@[simp]
theorem toContinuousRiemannianMetric_inner (g : ContMDiffRiemannianMetric IB n F E) :
    g.toContinuousRiemannianMetric.inner = g.inner :=
  (rfl)

/-- Lowering the smoothness of a metric does not change the underlying continuous metric. -/
@[simp]
theorem toContinuousRiemannianMetric_ofLE (g : ContMDiffRiemannianMetric IB n F E) (h : m ≤ n) :
    (g.ofLE h).toContinuousRiemannianMetric = g.toContinuousRiemannianMetric :=
  (rfl)

/-- Forgetting regularity to the same order leaves a metric unchanged. -/
@[simp]
theorem ofLE_refl (g : ContMDiffRiemannianMetric IB n F E) (h : n ≤ n) :
    g.ofLE h = g := (rfl)

/-- On an empty base manifold, `C^n` Riemannian metrics form a subsingleton. -/
instance subsingleton_of_isEmpty [IsEmpty B] : Subsingleton (ContMDiffRiemannianMetric IB n F E) :=
  ⟨fun g₁ g₂ ↦ by cases g₁; cases g₂; congr; exact funext isEmptyElim⟩

/-- The native fibre inner product installed from a metric evaluates to that metric. -/
theorem inner_eq [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousConstSMul ℝ (E x)]
    (g : ContMDiffRiemannianMetric IB n F E) (x : B) (v w : E x) :
    letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
    Inner.inner ℝ v w = g.inner x v w := by
  -- By construction: Mathlib's scoped fibre `InnerProductSpace` instance for `RiemannianBundle`
  -- is built from `RiemannianMetric.toCore`, whose inner product unfolds to `g.inner`.
  rfl

/-- The squared fibre norm installed from a metric is its diagonal value. -/
theorem norm_sq [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousConstSMul ℝ (E x)]
    (g : ContMDiffRiemannianMetric IB n F E) (x : B) (v : E x) :
    letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
    ‖v‖ ^ 2 = g.inner x v v := by
  let : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
  exact (real_inner_self_eq_norm_sq v).symm.trans (g.inner_eq x v v)

/-- **A `C^n` metric read in a trivialization.** Over the base set of a trivialization `e` in the
atlas of a `C^n` vector bundle with finite-dimensional model fibre `F`, a `C^n` metric `g` reads as
a `C^n` family `G` of bilinear forms on `F`, `G x u v = g (e.symm x u, e.symm x v)`. This is
`Bundle.Trivialization.contMDiffOn_compl₁₂_symmₗ` for the field of inner products of `g`. -/
theorem exists_contMDiffOn_apply_eq_inner_symm [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle n F E IB] (g : ContMDiffRiemannianMetric IB n F E)
    (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    ∃ G : B → F →L[ℝ] F →L[ℝ] ℝ, ContMDiffOn IB 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) n G e.baseSet ∧
      ∀ x ∈ e.baseSet, ∀ u v, G x u v = g.toRiemannianMetric.inner x (e.symm x u) (e.symm x v) :=
  ⟨fun x ↦ ((g.inner x).toLinearMap₁₂.compl₁₂ (e.symmₗ ℝ x) (e.symmₗ ℝ x)).toContinuousBilinearMap,
    e.contMDiffOn_compl₁₂_symmₗ g.contMDiff.contMDiffOn, fun x hx u v ↦ by
      simp only [LinearMap.toContinuousBilinearMap_apply, LinearMap.compl₁₂_apply,
        ContinuousLinearMap.toLinearMap₁₂_apply, e.symmₗ_apply hx]
      -- The underlying metric of `g` has the inner products of `g`, by definition.
      rfl⟩

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
    ContMDiff (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) n fun z : TotalSpace F E ↦ ‖z.snd‖ ^ 2 := by
  have hid : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F)) n
      fun z : TotalSpace F E ↦ (⟨z.proj, z.snd⟩ : TotalSpace F E) := contMDiff_id
  simpa only [real_inner_self_eq_norm_sq] using hid.inner_bundle hid

end TauCeti

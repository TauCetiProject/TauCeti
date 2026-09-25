/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Topology.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Basic Riemannian bundle constructions

This file provides conversions between Mathlib's Riemannian bundle classes and bundled
Riemannian metrics, and records that the Riemannian norm of the differential of a `C¹` map, applied
to a fixed vector, depends continuously on the base point.

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle`: package the metric of a
  `C^n` Riemannian bundle.
* `Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner`: the packaged metric is
  the bundle's inner product.
* `Bundle.IsContinuousRiemannianBundle.toIsContMDiffZero`: view a continuous Riemannian bundle as
  a `C^0` Riemannian bundle.
* `IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle`: conversely, view a `C^n`
  Riemannian bundle as a continuous Riemannian bundle.
* `ContMDiffOn.continuousOn_norm_mfderiv`: for a `C¹` map `f` from an open subset of a normed space
  to a Riemannian manifold, `z ↦ ‖df_z ξ‖` is continuous.
-/

public section

open Bundle Manifold
open scoped Bundle ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, TopologicalSpace (V b)] [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousConstSMul ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Package the metric of a `C^n` Riemannian bundle as a `C^n` Riemannian metric. -/
noncomputable def ofIsContMDiffRiemannianBundle
    [RiemannianBundle V] [IsContMDiffRiemannianBundle IB n F V] :
    ContMDiffRiemannianMetric IB n F V where
  inner := RiemannianBundle.g.inner
  symm := RiemannianBundle.g.symm
  pos := RiemannianBundle.g.pos
  isVonNBounded := RiemannianBundle.g.isVonNBounded
  contMDiff := by
    obtain ⟨g, hg, hinner⟩ :=
      IsContMDiffRiemannianBundle.exists_contMDiff (IB := IB) (n := n) (F := F) (E := V)
    convert hg using 1
    funext x
    congr 1
    ext v w
    exact hinner x v w

/-- The Riemannian metric packaged from a `C^n` Riemannian bundle is its inner product. -/
@[simp]
theorem ofIsContMDiffRiemannianBundle_inner
    [RiemannianBundle V] [IsContMDiffRiemannianBundle IB n F V]
    (x : B) (v w : V x) :
    (ofIsContMDiffRiemannianBundle (IB := IB) (n := n) (F := F) (V := V)).inner x v w =
      RiemannianBundle.g.inner x v w := by
  rfl

end Bundle.ContMDiffRiemannianMetric

namespace Bundle.IsContinuousRiemannianBundle

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- A continuous Riemannian bundle is a `C^0` Riemannian bundle. This is deliberately a theorem,
not an instance, because Mathlib avoids the corresponding inference path. -/
theorem toIsContMDiffZero [IsContinuousRiemannianBundle F V] :
    IsContMDiffRiemannianBundle IB 0 F V := by
  obtain ⟨g, hg, hinner⟩ := IsContinuousRiemannianBundle.exists_continuous (F := F) (E := V)
  exact ⟨g, contMDiff_zero_iff.mpr hg, hinner⟩

end Bundle.IsContinuousRiemannianBundle

namespace IsContMDiffRiemannianBundle

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- A `C^n` Riemannian bundle is a continuous Riemannian bundle. Like
`Bundle.IsContinuousRiemannianBundle.toIsContMDiffZero`, this is a theorem rather than an instance:
the model `IB` and the smoothness `n` do not appear in its conclusion. -/
theorem toIsContinuousRiemannianBundle [IsContMDiffRiemannianBundle IB n F V] :
    IsContinuousRiemannianBundle F V := by
  obtain ⟨g, hg, hinner⟩ :=
    IsContMDiffRiemannianBundle.exists_contMDiff (IB := IB) (n := n) (F := F) (E := V)
  exact ⟨⟨g, hg.continuous, hinner⟩⟩

end IsContMDiffRiemannianBundle

section NormMFDeriv

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Let `f` be a `C^n` map, `1 ≤ n`, from an open subset `U` of a real normed space to a manifold
whose tangent spaces carry a continuous Riemannian metric. For each fixed vector `ξ`, the
Riemannian norm of `df_z ξ` depends continuously on `z ∈ U`. -/
theorem ContMDiffOn.continuousOn_norm_mfderiv {f : F → M} {U : Set F} {n : ℕ∞ω}
    (hf : ContMDiffOn 𝓘(ℝ, F) I n f U) (hn : 1 ≤ n) (hU : IsOpen U) (ξ : F) :
    ContinuousOn (fun z ↦ ‖mfderiv 𝓘(ℝ, F) I f z ξ‖) U := by
  -- read `z ↦ df_z ξ` as the bundled differential of `f` evaluated at `(z, ξ)`
  have hnorm := (TauCeti.continuous_norm_bundle E (fun x : M ↦ TangentSpace I x)).comp_continuousOn
    (hf.continuousOn_tangentMapWithin hn hU.uniqueMDiffOn)
  have hmk : Continuous fun z : F ↦ (⟨z, ξ⟩ : TangentBundle 𝓘(ℝ, F) F) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, F)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  refine (hnorm.comp hmk.continuousOn fun z hz ↦ hz).congr fun z hz ↦ ?_
  simp only [Function.comp_apply, tangentMapWithin, mfderivWithin_of_isOpen hU hz]
  -- the two sides differ only in presenting the fibre of `TM` at `f z` as the second component
  -- of a point of the total space
  rfl

end NormMFDeriv

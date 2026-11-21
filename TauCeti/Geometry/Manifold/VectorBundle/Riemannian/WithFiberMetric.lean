/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Riemannian.WithFiberMetric
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Smooth sections of the fibre copy carrying a metric

The copy `TauCeti.WithFiberMetric g` of a vector bundle `E` has the same total-space topology and
bundle structure as `E`, so a `C^n` vector-bundle structure on `E` is one on the copy. Fibrewise
transport `TauCeti.WithFiberMetric.toWithFiberMetric` then identifies the `C^n` sections of `E`
with those of the copy (`TauCeti.WithFiberMetric.contMDiffSectionEquiv`), preserving supports.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace TauCeti

namespace WithFiberMetric

variable {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {n : ℕ∞ω} (g : ContinuousRiemannianMetric F E)

/-- The copy carrying a metric inherits the `C^n` vector-bundle structure of `E`. -/
instance [ContMDiffVectorBundle n F E IB] :
    ContMDiffVectorBundle n F (WithFiberMetric g) IB :=
  inferInstanceAs (ContMDiffVectorBundle n F E IB)

/-- Fibrewise transport identifies `C^n` sections of `E` with `C^n` sections of the copy
carrying the metric `g`. -/
def contMDiffSectionEquiv : Cₛ^n⟮IB; F, E⟯ ≃ₗ[ℝ] Cₛ^n⟮IB; F, WithFiberMetric g⟯ where
  toFun s := ⟨fun b ↦ (s b : E b), s.contMDiff⟩
  invFun s := ⟨fun b ↦ (s b : WithFiberMetric g b), s.contMDiff⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- Transport of a section evaluates fibrewise by `toWithFiberMetric`. -/
@[simp]
theorem contMDiffSectionEquiv_apply (s : Cₛ^n⟮IB; F, E⟯) (b : B) :
    contMDiffSectionEquiv g s b = toWithFiberMetric g b (s b) :=
  (toWithFiberMetric_apply g b (s b)).symm

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- Inverse transport of a section evaluates fibrewise by the inverse of `toWithFiberMetric`. -/
@[simp]
theorem contMDiffSectionEquiv_symm_apply (s : Cₛ^n⟮IB; F, WithFiberMetric g⟯) (b : B) :
    (contMDiffSectionEquiv g).symm s b = (toWithFiberMetric g b).symm (s b) :=
  (toWithFiberMetric_symm_apply g b (s b)).symm

end WithFiberMetric

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Basic
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Basic

/-!
# Changing the metric of a Riemannian vector bundle

Let `E → B` be a continuous Riemannian vector bundle with finite-dimensional fibres, and let `h` be
a second continuous Riemannian metric on `E`. In each fibre, the inverse square root of the Riesz
operator of `h` for the given inner product, `(h.inner b).metricChangeTransport`, is an isometry
from the given inner product to `h`
(`Bundle.ContinuousRiemannianMetric.inner_metricChangeTransport_metricChangeTransport`). It
therefore carries orthonormal frames of the given metric to orthonormal frames of `h`, and its
inverse is the square root of the same Riesz operator.

This file proves that these fibrewise transports form a continuous family: applying them in every
fibre is a continuous map of the total space
(`Bundle.ContinuousRiemannianMetric.continuous_metricChangeTransport`), and so is applying their
inverses. Together they give a homeomorphism of the total space over the identity of `B`
(`Bundle.ContinuousRiemannianMetric.metricChangeHomeomorph`), linear on each fibre, which is an
isometry from the given metric to `h`. The construction uses no chart: it is defined fibrewise from
the two metrics alone, over an arbitrary topological base.

Continuity is checked in the Gram–Schmidt orthonormal frames of linear trivializations. Read in such
a frame `σ`, the transport of `h` is the transport of the bilinear form `h` read in `σ`, by the
naturality `ContinuousLinearMap.metricChangeTransport_bilinearComp`; that bilinear form varies
continuously with the base point, and the transport is continuous in it
(`ContinuousLinearMap.continuousOn_metricChangeTransport`).

## Main declarations

* `Bundle.ContinuousRiemannianMetric.inner_metricChangeTransport_metricChangeTransport`: the
  fibrewise transport is an isometry from the given metric to `h`.
* `Bundle.ContinuousRiemannianMetric.continuous_metricChangeTransport`: the transport is continuous
  on the total space.
* `Bundle.ContinuousRiemannianMetric.metricChangeHomeomorph`: the transport as a homeomorphism of
  the total space, with inverse the fibrewise square root.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, Princeton University Press, 1974, §2
  (Euclidean vector bundles and their orthonormal frames).
-/

public section

open Bundle InnerProductSpace TauCeti
open scoped InnerProductSpace Topology

/-- The Riesz operator of a real bilinear form, written as Mathlib's `InnerProductSpace.Dual`
writes it. -/
local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

namespace Bundle.ContinuousRiemannianMetric

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [∀ b, FiniteDimensional ℝ (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]
  (h : ContinuousRiemannianMetric F E)

omit [IsContinuousRiemannianBundle F E] in
/-- The Riesz operator of a continuous Riemannian metric on each fibre, for the given inner
product, is strictly positive. -/
theorem isStrictlyPositive_continuousLinearMapOfBilin_inner (b : B) :
    IsStrictlyPositive (h.inner b)♯ :=
  isStrictlyPositive_continuousLinearMapOfBilin_iff.2 ⟨h.symm b, h.pos b⟩

omit [IsContinuousRiemannianBundle F E] in
/-- The metric change transport of `h` is an isometry from the given metric to `h`. -/
@[simp]
theorem inner_metricChangeTransport_metricChangeTransport (b : B) (u v : E b) :
    h.inner b ((h.inner b).metricChangeTransport u) ((h.inner b).metricChangeTransport v) =
      ⟪u, v⟫_ℝ :=
  ContinuousLinearMap.apply_metricChangeTransport_metricChangeTransport
    (h.isStrictlyPositive_continuousLinearMapOfBilin_inner b) u v

omit [∀ b, FiniteDimensional ℝ (E b)] in
/-- Read in a local orthonormal frame, the metric `h` is a continuous family of bilinear forms on
the model. -/
private theorem continuous_inner_bilinearComp_orthonormalFrame (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {n : ℕ} (c : Module.Basis (Fin n) ℝ F) :
    Continuous fun y : e.baseSet ↦ (h.inner y).bilinearComp
      (e.orthonormalFrame c (EuclideanSpace.basisFun (Fin n) ℝ) y :
        EuclideanSpace ℝ (Fin n) →L[ℝ] E y)
      (e.orthonormalFrame c (EuclideanSpace.basisFun (Fin n) ℝ) y :
        EuclideanSpace ℝ (Fin n) →L[ℝ] E y) := by
  let σ := e.orthonormalFrame c (EuclideanSpace.basisFun (Fin n) ℝ)
  have hσ (w : EuclideanSpace ℝ (Fin n)) :
      Continuous fun y : e.baseSet ↦ TotalSpace.mk' F (y : B) (σ y w) :=
    (OrthonormalFrameBundle.continuous_totalSpaceMk_frame w).comp
      (e.continuous_orthonormalFrame c _)
  refine continuous_clm_apply.2 fun w ↦ continuous_clm_apply.2 fun w' ↦ ?_
  -- The values of `h` on two continuous sections form a continuous section of the trivial bundle.
  have : Continuous fun y : e.baseSet ↦
      TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (y : B) (h.inner y (σ y w) (σ y w')) :=
    (h.continuous.comp continuous_subtype_val).clm_bundle_apply₂ (F₁ := F) (F₂ := F)
      (hσ w) (hσ w')
  exact continuous_snd.comp ((Bundle.Trivial.homeomorphProd B ℝ).continuous.comp this)

omit [∀ b, FiniteDimensional ℝ (E b)] [IsContinuousRiemannianBundle F E] in
/-- Read in an orthonormal frame, `h` is again an inner product. -/
private theorem isStrictlyPositive_inner_bilinearComp {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {b : B} (σ : V ≃ₗᵢ[ℝ] E b) :
    IsStrictlyPositive ((h.inner b).bilinearComp (σ : V →L[ℝ] E b) (σ : V →L[ℝ] E b))♯ :=
  isStrictlyPositive_continuousLinearMapOfBilin_iff.2
    ⟨fun _ _ ↦ h.symm b _ _, fun _ hw ↦ h.pos b _ (σ.map_ne_zero_iff.2 hw)⟩

/-- **Continuity of the metric change transport.** Applying in each fibre the metric change
transport of a second continuous Riemannian metric `h` is a continuous map of the total space. -/
theorem continuous_metricChangeTransport :
    Continuous fun p : TotalSpace F E ↦
      (⟨p.proj, (h.inner p.proj).metricChangeTransport p.2⟩ : TotalSpace F E) := by
  refine continuous_totalSpaceMk_apply_of_orthonormalFrame
    (A := fun b ↦ (h.inner b).metricChangeTransport) fun e _ n c ↦ ?_
  -- Read in a local orthonormal frame, the transport of `h` is the transport of `h` read in the
  -- frame, by naturality.
  refine (ContinuousLinearMap.continuousOn_metricChangeTransport.comp_continuous
    (h.continuous_inner_bilinearComp_orthonormalFrame e c)
    fun y ↦ h.isStrictlyPositive_inner_bilinearComp _).congr fun y ↦ ?_
  ext w
  simp [ContinuousLinearMap.metricChangeTransport_bilinearComp _
    (h.isStrictlyPositive_continuousLinearMapOfBilin_inner y)]

/-- The inverse transport, the square root of the Riesz operator of `h` in each fibre, is a
continuous map of the total space. -/
private theorem continuous_sqrt_continuousLinearMapOfBilin_inner :
    Continuous fun p : TotalSpace F E ↦
      (⟨p.proj, CFC.sqrt (h.inner p.proj)♯ p.2⟩ : TotalSpace F E) := by
  refine continuous_totalSpaceMk_apply_of_orthonormalFrame (A := fun b ↦ CFC.sqrt (h.inner b)♯)
    fun e _ n c ↦ ?_
  refine (ContinuousLinearMap.continuousOn_sqrt_continuousLinearMapOfBilin.comp_continuous
    (h.continuous_inner_bilinearComp_orthonormalFrame e c)
    fun y ↦ (h.isStrictlyPositive_inner_bilinearComp _).nonneg).congr fun y ↦ ?_
  ext w
  simp [ContinuousLinearMap.sqrt_continuousLinearMapOfBilin_bilinearComp _
    (h.isStrictlyPositive_continuousLinearMapOfBilin_inner y).nonneg]

/-- The **metric change homeomorphism** of a second continuous Riemannian metric `h`: the
homeomorphism of the total space applying in each fibre the metric change transport of `h`, a
linear isometry from the given metric to `h` (`inner_metricChangeTransport_metricChangeTransport`).
Its inverse applies the square root of the Riesz operator of `h` in each fibre. -/
noncomputable def metricChangeHomeomorph : TotalSpace F E ≃ₜ TotalSpace F E where
  toFun p := ⟨p.proj, (h.inner p.proj).metricChangeTransport p.2⟩
  invFun p := ⟨p.proj, CFC.sqrt (h.inner p.proj)♯ p.2⟩
  left_inv p := TotalSpace.ext rfl <| heq_of_eq
    congr($(ContinuousLinearMap.sqrt_mul_metricChangeTransport
      (h.isStrictlyPositive_continuousLinearMapOfBilin_inner p.proj)) p.2)
  right_inv p := TotalSpace.ext rfl <| heq_of_eq
    congr($(ContinuousLinearMap.metricChangeTransport_mul_sqrt
      (h.isStrictlyPositive_continuousLinearMapOfBilin_inner p.proj)) p.2)
  continuous_toFun := h.continuous_metricChangeTransport
  continuous_invFun := h.continuous_sqrt_continuousLinearMapOfBilin_inner

/-- The metric change homeomorphism applies the metric change transport of `h` in each fibre. -/
@[simp]
theorem metricChangeHomeomorph_apply (p : TotalSpace F E) :
    h.metricChangeHomeomorph p = ⟨p.proj, (h.inner p.proj).metricChangeTransport p.2⟩ :=
  (rfl)

/-- The inverse of the metric change homeomorphism applies the square root of the Riesz operator of
`h` in each fibre. -/
@[simp]
theorem metricChangeHomeomorph_symm_apply (p : TotalSpace F E) :
    h.metricChangeHomeomorph.symm p = ⟨p.proj, CFC.sqrt (h.inner p.proj)♯ p.2⟩ :=
  (rfl)

end Bundle.ContinuousRiemannianMetric

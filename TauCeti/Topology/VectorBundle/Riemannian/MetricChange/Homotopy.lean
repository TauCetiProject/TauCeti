/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Homotopy
public import TauCeti.Topology.VectorBundle.Riemannian.MetricChange.Between

/-!
# Homotopy compatibility of metric transport on vector bundles

Canonical positive transports between metrics do not generally compose literally. For two
continuous positive metrics `h` and `k` on a continuous Riemannian vector bundle, this file
constructs a homotopy from direct transport to `k` to transport through `h` and then to `k`.
Every intermediate map covers the identity of the base and is a fibrewise linear isometry
from the reference metric to `k`. Thus the comparison applies to continuously varying frames,
without choosing a global trivialization.

The intermediate metric at time `t` is `(1 - t) k + t h`. The homotopy uses the intrinsic
inverse-square-root transport in every fibre. Its continuity is checked in bundle
charts, using Gram–Schmidt frames and the isometric coordinate-change formula for the
fixed-space composition homotopy. Both time and the bundle point vary in this comparison.

## Main declarations

* `Bundle.ContinuousRiemannianMetric.metricChangeCompositionHomotopy`: the homotopy on the
  original total space from direct to successive transport.
* `Bundle.ContinuousRiemannianMetric.inner_metricChangeCompositionTransport`: every time slice
  preserves the reference inner product with values in the final metric.

## References

* R. Bhatia, *Positive Definite Matrices*, Princeton University Press, 2007, Chapter 1
  (positive square roots and congruences of inner products).
* J. Milnor and J. Stasheff, *Characteristic Classes*, Princeton University Press, 1974, §2
  (Euclidean vector bundles).
-/

public noncomputable section

open Bundle InnerProductSpace TauCeti
open scoped Topology unitInterval

namespace Bundle.ContinuousRiemannianMetric

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [∀ b, FiniteDimensional ℝ (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E]
  (h k : ContinuousRiemannianMetric F E)

/-- The linear transport at time `t` from the reference metric to `k`, through the
intermediate metric `(1 - t) k + t h`, in the fibre over `b`. -/
def metricChangeCompositionTransport (t : unitInterval) (b : B) : E b →L[ℝ] E b :=
  (AffineMap.lineMap (k.inner b) (h.inner b) (t : ℝ)).metricChangeBetween (k.inner b) *
    (AffineMap.lineMap (k.inner b) (h.inner b) (t : ℝ)).metricChangeTransport

-- Keep evaluation as a named rewrite: expanding it automatically would hide the linear-map
-- structure from rules for addition and scalar multiplication.
/-- The fibrewise linear transport agrees with the intrinsic composition homotopy. -/
theorem metricChangeCompositionTransport_apply (t : unitInterval) (b : B) (v : E b) :
    h.metricChangeCompositionTransport k t b v =
      ContinuousLinearMap.metricChangeCompositionHomotopy (h.inner b) (k.inner b)
        (h.isStrictlyPositive_continuousLinearMapOfBilin_inner b)
        (k.isStrictlyPositive_continuousLinearMapOfBilin_inner b) (t, v) := by
  rw [metricChangeCompositionTransport,
    ContinuousLinearMap.metricChangeCompositionHomotopy_eq_metricChangeBetween,
    mul_apply_eq_comp]

/-- The composition transport starts at direct transport to the final metric. -/
@[simp]
theorem metricChangeCompositionTransport_zero (b : B) :
    h.metricChangeCompositionTransport k 0 b = (k.inner b).metricChangeTransport := by
  ext v
  simp [metricChangeCompositionTransport_apply]

/-- The composition transport ends at successive transport through `h` to `k`. -/
@[simp]
theorem metricChangeCompositionTransport_one (b : B) :
    h.metricChangeCompositionTransport k 1 b =
      (h.inner b).metricChangeBetween (k.inner b) * (h.inner b).metricChangeTransport := by
  simp [metricChangeCompositionTransport]

/-- At each time the composition transport is an isometry from the reference metric to `k`. -/
@[simp]
theorem inner_metricChangeCompositionTransport (t : unitInterval) (b : B) (u v : E b) :
    k.inner b (h.metricChangeCompositionTransport k t b u)
      (h.metricChangeCompositionTransport k t b v) = @Inner.inner ℝ _ _ u v := by
  simp only [metricChangeCompositionTransport_apply]
  exact ContinuousLinearMap.apply_metricChangeCompositionHomotopy _ _ _ _ t u v


section Continuity

variable [ContinuousFiberNorm F E]

/-- The fibrewise composition homotopy is jointly continuous in time and the bundle point. -/
theorem continuous_metricChangeCompositionHomotopy :
    Continuous fun p : unitInterval × TotalSpace F E ↦
      (⟨p.2.proj, ContinuousLinearMap.metricChangeCompositionHomotopy
        (h.inner p.2.proj) (k.inner p.2.proj)
        (h.isStrictlyPositive_continuousLinearMapOfBilin_inner p.2.proj)
        (k.isStrictlyPositive_continuousLinearMapOfBilin_inner p.2.proj) (p.1, p.2.snd)⟩ :
          TotalSpace F E) := by
  suffices hc : Continuous fun p : unitInterval × TotalSpace F E ↦
      (⟨p.2.proj, h.metricChangeCompositionTransport k p.1 p.2.proj p.2.snd⟩ : TotalSpace F E) by
    simpa only [metricChangeCompositionTransport_apply] using hc
  refine continuous_totalSpaceMk_apply_of_orthonormalFrame
    (A := h.metricChangeCompositionTransport k) fun e _ n c ↦ ?_
  let frame := e.orthonormalFrame c (EuclideanSpace.basisFun (Fin n) ℝ)
  refine continuous_clm_apply.2 fun w ↦ ?_
  have hc := continuous_fst.metricChangeCompositionHomotopy
    ((h.continuous_inner_bilinearComp_orthonormalFrame e c).comp continuous_snd)
    ((k.continuous_inner_bilinearComp_orthonormalFrame e c).comp continuous_snd)
    (continuous_const (y := w))
    (fun p ↦ ContinuousLinearMap.isStrictlyPositive_continuousLinearMapOfBilin_bilinearComp_equiv
      (h.inner p.2) (frame p.2).toContinuousLinearEquiv
      (h.isStrictlyPositive_continuousLinearMapOfBilin_inner p.2))
    (fun p ↦ ContinuousLinearMap.isStrictlyPositive_continuousLinearMapOfBilin_bilinearComp_equiv
      (k.inner p.2) (frame p.2).toContinuousLinearEquiv
      (k.isStrictlyPositive_continuousLinearMapOfBilin_inner p.2))
  refine hc.congr fun p ↦ ?_
  simp only [Function.comp_apply]
  rw [ContinuousLinearMap.metricChangeCompositionHomotopy_bilinearComp
    (h.inner p.2) (k.inner p.2) (frame p.2)
    (h.isStrictlyPositive_continuousLinearMapOfBilin_inner p.2)
    (k.isStrictlyPositive_continuousLinearMapOfBilin_inner p.2)]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'',
    metricChangeCompositionTransport_apply, frame]

end Continuity

variable [IsContinuousRiemannianBundle F E]

/-- Direct canonical transport to `k` is homotopic, over the identity of the base, to canonical
transport first to `h` and then to `k`. At every time the map is a fibrewise linear isometry
from the reference metric to `k`. -/
def metricChangeCompositionHomotopy :
    ContinuousMap.Homotopy ⟨k.metricChangeHomeomorph, k.metricChangeHomeomorph.continuous⟩
      ⟨(h.metricChangeBetweenHomeomorph k) ∘ h.metricChangeHomeomorph,
        (h.metricChangeBetweenHomeomorph k).continuous.comp
          h.metricChangeHomeomorph.continuous⟩ where
  toFun p := ⟨p.2.proj, ContinuousLinearMap.metricChangeCompositionHomotopy
    (h.inner p.2.proj) (k.inner p.2.proj)
    (h.isStrictlyPositive_continuousLinearMapOfBilin_inner p.2.proj)
    (k.isStrictlyPositive_continuousLinearMapOfBilin_inner p.2.proj) (p.1, p.2.snd)⟩
  continuous_toFun := h.continuous_metricChangeCompositionHomotopy k
  map_zero_left p := by simp
  map_one_left p := by simp [Function.comp_def, metricChangeBetweenHomeomorph_apply]

/-- The bundle homotopy applies the fibrewise linear composition transport. -/
theorem metricChangeCompositionHomotopy_apply (t : unitInterval) (p : TotalSpace F E) :
    h.metricChangeCompositionHomotopy k (t, p) =
      ⟨p.proj, h.metricChangeCompositionTransport k t p.proj p.snd⟩ := by
  rw [metricChangeCompositionTransport_apply]
  rfl

/-- The entire composition homotopy preserves the base point. -/
@[simp]
theorem proj_metricChangeCompositionHomotopy (t : unitInterval) (p : TotalSpace F E) :
    (h.metricChangeCompositionHomotopy k (t, p)).proj = p.proj := (rfl)

end Bundle.ContinuousRiemannianMetric

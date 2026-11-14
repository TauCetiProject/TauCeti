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

private theorem continuous_metricChangeCompositionHomotopy_chart
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {n : ℕ} (c : Module.Basis (Fin n) ℝ F) :
    Continuous fun p : unitInterval × (TotalSpace.proj ⁻¹' e.baseSet : Set (TotalSpace F E)) ↦
      (⟨p.2.1.proj, ContinuousLinearMap.metricChangeCompositionHomotopy
        (h.inner p.2.1.proj) (k.inner p.2.1.proj)
        (h.isStrictlyPositive_continuousLinearMapOfBilin_inner p.2.1.proj)
        (k.isStrictlyPositive_continuousLinearMapOfBilin_inner p.2.1.proj) (p.1, p.2.1.2)⟩ :
          TotalSpace F E) := by
  let frame := e.orthonormalFrame c (EuclideanSpace.basisFun (Fin n) ℝ)
  have hframe (w : EuclideanSpace ℝ (Fin n)) :
      Continuous fun y : e.baseSet ↦ TotalSpace.mk' F (y : B) (frame y w) :=
    (OrthonormalFrameBundle.continuous_totalSpaceMk_frame w).comp
      (e.continuous_orthonormalFrame c (EuclideanSpace.basisFun (Fin n) ℝ))
  let h' (y : e.baseSet) := (h.inner y).bilinearComp
    (frame y : EuclideanSpace ℝ (Fin n) →L[ℝ] E y)
    (frame y : EuclideanSpace ℝ (Fin n) →L[ℝ] E y)
  let k' (y : e.baseSet) := (k.inner y).bilinearComp
    (frame y : EuclideanSpace ℝ (Fin n) →L[ℝ] E y)
    (frame y : EuclideanSpace ℝ (Fin n) →L[ℝ] E y)
  have hh : Continuous h' := h.continuous_inner_bilinearComp _ hframe
  have hk : Continuous k' := k.continuous_inner_bilinearComp _ hframe
  have hp (y : e.baseSet) :=
    ContinuousLinearMap.isStrictlyPositive_continuousLinearMapOfBilin_bilinearComp_equiv
      (h.inner y) (frame y).toContinuousLinearEquiv
      (h.isStrictlyPositive_continuousLinearMapOfBilin_inner y)
  have kp (y : e.baseSet) :=
    ContinuousLinearMap.isStrictlyPositive_continuousLinearMapOfBilin_bilinearComp_equiv
      (k.inner y) (frame y).toContinuousLinearEquiv
      (k.isStrictlyPositive_continuousLinearMapOfBilin_inner y)
  let base (p : unitInterval × (TotalSpace.proj ⁻¹' e.baseSet : Set (TotalSpace F E))) :
      e.baseSet := ⟨p.2.1.proj, p.2.2⟩
  have hb : Continuous base :=
    ((FiberBundle.continuous_proj F E).comp
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  have hv : Continuous fun p :
      unitInterval × (TotalSpace.proj ⁻¹' e.baseSet : Set (TotalSpace F E)) ↦
        (frame (base p)).symm p.2.1.2 :=
    (e.continuous_orthonormalFrame_symm_apply c
      (EuclideanSpace.basisFun (Fin n) ℝ)).comp continuous_snd
  have ht : Continuous (Prod.fst :
      unitInterval × (TotalSpace.proj ⁻¹' e.baseSet : Set (TotalSpace F E)) → unitInterval) :=
    continuous_fst
  have hc := ht.metricChangeCompositionHomotopy
    (hh.comp hb) (hk.comp hb) hv (fun p ↦ hp (base p)) (fun p ↦ kp (base p))
  refine (OrthonormalFrameBundle.continuous_totalSpaceMk_frame_apply.comp
    (((e.continuous_orthonormalFrame c (EuclideanSpace.basisFun (Fin n) ℝ)).comp hb).prodMk
      hc)).congr fun p ↦ ?_
  simp only [Function.comp_apply, h', k']
  rw [ContinuousLinearMap.metricChangeCompositionHomotopy_bilinearComp
    (h.inner (base p)) (k.inner (base p)) (frame (base p))
    (h.isStrictlyPositive_continuousLinearMapOfBilin_inner (base p))
    (k.isStrictlyPositive_continuousLinearMapOfBilin_inner (base p))]
  simp only [LinearIsometryEquiv.apply_symm_apply, frame, base]

/-- The fibrewise composition homotopy is jointly continuous in time and the bundle point. -/
theorem continuous_metricChangeCompositionHomotopy :
    Continuous fun p : unitInterval × TotalSpace F E ↦
      (⟨p.2.proj, ContinuousLinearMap.metricChangeCompositionHomotopy
        (h.inner p.2.proj) (k.inner p.2.proj)
        (h.isStrictlyPositive_continuousLinearMapOfBilin_inner p.2.proj)
        (k.isStrictlyPositive_continuousLinearMapOfBilin_inner p.2.proj) (p.1, p.2.2)⟩ :
          TotalSpace F E) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  let e := trivializationAt F E p₀.2.proj
  have he : p₀.2.proj ∈ e.baseSet := mem_baseSet_trivializationAt F E p₀.2.proj
  have : FiniteDimensional ℝ F :=
    (e.continuousLinearEquivAt ℝ p₀.2.proj he).toLinearEquiv.finiteDimensional
  let U : Set (unitInterval × TotalSpace F E) := {p | p.2.proj ∈ e.baseSet}
  have hU : U ∈ 𝓝 p₀ :=
    (e.open_baseSet.preimage ((FiberBundle.continuous_proj F E).comp continuous_snd)).mem_nhds he
  refine ContinuousOn.continuousAt ?_ hU
  rw [continuousOn_iff_continuous_domRestrict]
  exact (h.continuous_metricChangeCompositionHomotopy_chart k e (Module.finBasis ℝ F)).comp
    (((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk fun p : U ↦ p.2)))

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
    (k.isStrictlyPositive_continuousLinearMapOfBilin_inner p.2.proj) (p.1, p.2.2)⟩
  continuous_toFun := h.continuous_metricChangeCompositionHomotopy k
  map_zero_left p := by simp
  map_one_left p := by simp [Function.comp_def, metricChangeBetweenHomeomorph_apply]

/-- The bundle homotopy applies the fibrewise linear composition transport. -/
theorem metricChangeCompositionHomotopy_apply (t : unitInterval) (p : TotalSpace F E) :
    h.metricChangeCompositionHomotopy k (t, p) =
      ⟨p.proj, h.metricChangeCompositionTransport k t p.proj p.2⟩ := by
  rw [metricChangeCompositionTransport_apply]
  rfl

/-- The entire composition homotopy preserves the base point. -/
@[simp]
theorem proj_metricChangeCompositionHomotopy (t : unitInterval) (p : TotalSpace F E) :
    (h.metricChangeCompositionHomotopy k (t, p)).proj = p.proj := (rfl)

end Bundle.ContinuousRiemannianMetric

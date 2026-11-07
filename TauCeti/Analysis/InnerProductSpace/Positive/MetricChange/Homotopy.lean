/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Orientation
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Homotopy.Basic

/-!
# Homotopy compatibility of canonical metric changes

Successive inverse-square-root changes of metric need not equal the direct change. Their
orthogonal discrepancy nevertheless has a canonical path to the identity in the special
orthogonal group. Interpolate the intermediate metric from the final metric to the chosen
intermediate metric, and take the composition correction throughout this interpolation.

The correction depends continuously on both metrics. Consequently the path works for continuous
families of metrics, not merely for individual pairs. Multiplying it by the direct transport
gives a homotopy between direct and successive transport through linear isometries into the
final metric. No commutation of Riesz operators, choice of eigenbasis, or positive-dimension
hypothesis is required.

The constructions use `ContinuousLinearMap.metricChangeCompositionCorrection` and the native
operator-norm topology on `TauCeti.specialOrthogonalGroup`.

## References

* R. Bhatia, *Positive Definite Matrices*, Princeton University Press, 2007, Chapter 1
  (positive square roots and congruences of inner products).
-/

public section

open InnerProductSpace
open scoped unitInterval

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

/-- Positive-definite real bilinear forms form a convex set. -/
theorem convex_setOf_isStrictlyPositive_continuousLinearMapOfBilin :
    Convex ℝ {h : E →L[ℝ] E →L[ℝ] ℝ | IsStrictlyPositive h♯} := by
  intro h hh k hk a b ha hb hab
  obtain ⟨hsym, hpos⟩ := isStrictlyPositive_continuousLinearMapOfBilin_iff.1 hh
  obtain ⟨ksym, kpos⟩ := isStrictlyPositive_continuousLinearMapOfBilin_iff.1 hk
  apply isStrictlyPositive_continuousLinearMapOfBilin_iff.2
  refine ⟨fun u v ↦ by simp [hsym u v, ksym u v], fun u hu ↦ ?_⟩
  simp only [add_apply, smul_apply, smul_eq_mul]
  have hp := hpos u hu
  have kp := kpos u hu
  rcases lt_or_eq_of_le ha with ha | rfl
  · exact add_pos_of_pos_of_nonneg (mul_pos ha hp) (mul_nonneg hb kp.le)
  · simp_all

/-- The composition correction varies continuously with two continuous positive metrics,
with values in the native unitary group of the operator algebra. -/
theorem _root_.Continuous.metricChangeCompositionCorrection
    {X : Type*} [TopologicalSpace X] {h k : X → E →L[ℝ] E →L[ℝ] ℝ}
    (hh : Continuous h) (hk : Continuous k)
    (hpos : ∀ x, IsStrictlyPositive (h x)♯) (kpos : ∀ x, IsStrictlyPositive (k x)♯) :
    Continuous fun x ↦ Unitary.linearIsometryEquiv.symm
      ((h x).metricChangeCompositionCorrection (k x) (hpos x) (kpos x)) := by
  have hT := continuousOn_metricChangeTransport.comp_continuous hh hpos
  have hP : Continuous fun x ↦
      (k x).bilinearComp (h x).metricChangeTransport (h x).metricChangeTransport := by
    refine continuous_clm_apply.2 fun u ↦ continuous_clm_apply.2 fun v ↦ ?_
    exact (hk.clm_apply (hT.clm_apply continuous_const)).clm_apply
      (hT.clm_apply continuous_const)
  have hPT := continuousOn_metricChangeTransport.comp_continuous hP fun x ↦
    isStrictlyPositive_bilinearComp_metricChangeTransport (h x) (k x) (hpos x) (kpos x)
  have hS := continuousOn_sqrt_continuousLinearMapOfBilin.comp_continuous hk
    fun x ↦ (kpos x).nonneg
  apply Topology.IsInducing.subtypeVal.continuous_iff.2
  refine ((hS.mul hT).mul hPT).congr fun x ↦ ?_
  ext u
  simp [Unitary.coe_symm_linearIsometryEquiv_apply]

/-- The affine interpolation of positive metrics remains positive, including at its endpoints. -/
theorem isStrictlyPositive_lineMap (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) (t : unitInterval) :
    IsStrictlyPositive (AffineMap.lineMap h k (t : ℝ))♯ := by
  rw [AffineMap.lineMap_apply_module]
  exact convex_setOf_isStrictlyPositive_continuousLinearMapOfBilin hH hK
    (sub_nonneg.mpr t.2.2) t.2.1 (sub_add_cancel 1 (t : ℝ))

/-- The canonical path from the identity to the discrepancy between successive transport
through `h` and direct transport to `k`. At time `t`, its intermediate metric is
`(1 - t) • k + t • h`. The entire path lies in the special orthogonal group. -/
noncomputable def metricChangeCompositionCorrectionPath (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) :
    Path (1 : TauCeti.specialOrthogonalGroup E)
      ⟨Unitary.linearIsometryEquiv.symm (h.metricChangeCompositionCorrection k hH hK),
        metricChangeCompositionCorrection_mem_specialOrthogonalGroup h k hH hK⟩ where
  toFun t := ⟨Unitary.linearIsometryEquiv.symm
    ((AffineMap.lineMap k h (t : ℝ)).metricChangeCompositionCorrection k
      (isStrictlyPositive_lineMap k h hK hH t) hK),
    metricChangeCompositionCorrection_mem_specialOrthogonalGroup _ _ _ _⟩
  continuous_toFun := ((Path.segment k h).continuous.metricChangeCompositionCorrection
    continuous_const (isStrictlyPositive_lineMap k h hK hH) (fun _ ↦ hK)).subtype_mk _
  source' := by
    apply Subtype.ext
    simp [← LinearIsometryEquiv.one_def]
  target' := by
    apply Subtype.ext
    simp

/-- Evaluation of the canonical correction path, as an operator on vectors. -/
@[simp]
theorem metricChangeCompositionCorrectionPath_apply (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) (t : unitInterval) (v : E) :
    (((metricChangeCompositionCorrectionPath h k hH hK t : TauCeti.specialOrthogonalGroup E) :
      unitary (E →L[ℝ] E)) : E →L[ℝ] E) v =
      (AffineMap.lineMap k h (t : ℝ)).metricChangeCompositionCorrection k
        (isStrictlyPositive_lineMap k h hK hH t) hK v :=
  (rfl)

/-- The canonical correction paths depend jointly continuously on time and on a continuous
family of positive metrics. This permits their use in local bundle coordinates. -/
theorem _root_.Continuous.metricChangeCompositionCorrectionPath
    {X : Type*} [TopologicalSpace X] {h k : X → E →L[ℝ] E →L[ℝ] ℝ}
    (hh : Continuous h) (hk : Continuous k)
    (hpos : ∀ x, IsStrictlyPositive (h x)♯) (kpos : ∀ x, IsStrictlyPositive (k x)♯) :
    Continuous fun p : unitInterval × X ↦
      metricChangeCompositionCorrectionPath (h p.2) (k p.2) (hpos p.2) (kpos p.2) p.1 := by
  have hline : Continuous fun p : unitInterval × X ↦
      AffineMap.lineMap (k p.2) (h p.2) (p.1 : ℝ) := by
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  exact (hline.metricChangeCompositionCorrection (hk.comp continuous_snd)
    (fun p ↦ isStrictlyPositive_lineMap (k p.2) (h p.2) (kpos p.2) (hpos p.2) p.1)
    (fun p ↦ kpos p.2)).subtype_mk _

/-- No correction path is introduced when the intermediate and final metrics agree. -/
@[simp]
theorem metricChangeCompositionCorrectionPath_self_apply (h : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (t : unitInterval) :
    metricChangeCompositionCorrectionPath h h hH hH t = 1 := by
  ext v
  simp [metricChangeCompositionCorrectionPath_apply]

/-- A homotopy from direct transport to `k` to successive transport through `h`, obtained
by composing the canonical special-orthogonal correction path with the direct transport. -/
noncomputable def metricChangeCompositionHomotopy (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) :
    ContinuousMap.Homotopy
      ⟨k.metricChangeTransport, k.metricChangeTransport.continuous⟩
      ⟨fun v ↦ h.metricChangeBetween k (h.metricChangeTransport v),
        (h.metricChangeBetween k).continuous.comp h.metricChangeTransport.continuous⟩ where
  toFun p := k.metricChangeTransport
    ((metricChangeCompositionCorrectionPath h k hH hK p.1).1.1 p.2)
  continuous_toFun := k.metricChangeTransport.continuous.comp
    ((continuous_subtype_val.comp (continuous_subtype_val.comp
      ((metricChangeCompositionCorrectionPath h k hH hK).continuous.comp continuous_fst))).clm_apply
        continuous_snd)
  map_zero_left v := by simp
  map_one_left v := by
    simpa only [Path.target, Unitary.coe_symm_linearIsometryEquiv_apply,
      LinearIsometryEquiv.coe_coe'', mul_apply_eq_comp, ContinuousMap.coe_mk] using
      congrArg (fun A : E →L[ℝ] E ↦ A v)
        (metricChangeBetween_mul_metricChangeTransport h k hH hK).symm

/-- Evaluation of the transport-composition homotopy. -/
@[simp]
theorem metricChangeCompositionHomotopy_apply (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) (t : unitInterval) (v : E) :
    metricChangeCompositionHomotopy h k hH hK (t, v) =
      k.metricChangeTransport
        (((metricChangeCompositionCorrectionPath h k hH hK t).1 : E →L[ℝ] E) v) :=
  (rfl)

/-- Every slice of the composition homotopy is an isometry from the reference inner product
to `k`, not merely a linear homotopy of maps. -/
theorem apply_metricChangeCompositionHomotopy (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯)
    (t : unitInterval) (u v : E) :
    k (metricChangeCompositionHomotopy h k hH hK (t, u))
      (metricChangeCompositionHomotopy h k hH hK (t, v)) = ⟪u, v⟫_ℝ := by
  simp only [metricChangeCompositionHomotopy_apply, metricChangeCompositionCorrectionPath_apply,
    apply_metricChangeTransport_metricChangeTransport hK]
  exact LinearIsometryEquiv.inner_map_map _ u v

end ContinuousLinearMap

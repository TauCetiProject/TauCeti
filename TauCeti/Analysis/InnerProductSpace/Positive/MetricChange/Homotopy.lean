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
orthogonal discrepancy nevertheless has a canonical path to the identity in the orthogonal
group of a real Hilbert space, and in the special orthogonal group in finite dimension.
Interpolate the intermediate metric from the final metric to the chosen intermediate metric,
and take the composition correction throughout this interpolation.

The correction depends continuously on both metrics. Consequently the path works for continuous
families of metrics, not merely for individual pairs. Multiplying it by the direct transport
gives a homotopy between direct and successive transport through linear isometries into the
final metric. No commutation of Riesz operators, choice of eigenbasis, or positive-dimension
hypothesis is required.

The constructions use `ContinuousLinearMap.metricChangeCompositionCorrection` and the native
operator-norm topology on `unitary (E →L[ℝ] E)`. In finite dimension,
`metricChangeCompositionCorrectionSpecialOrthogonalPath` restricts this path to
`TauCeti.specialOrthogonalGroup`.

## References

* R. Bhatia, *Positive Definite Matrices*, Princeton University Press, 2007, Chapter 1
  (positive square roots and congruences of inner products).
-/

public section

open InnerProductSpace
open scoped unitInterval

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

variable [CompleteSpace E]

/-- The canonical path from the identity to the discrepancy between successive transport
through `h` and direct transport to `k`. At time `t`, its intermediate metric is
`(1 - t) • k + t • h`. The entire path consists of orthogonal operators. -/
noncomputable def metricChangeCompositionCorrectionPath (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) :
    Path (1 : unitary (E →L[ℝ] E))
      (Unitary.linearIsometryEquiv.symm (h.metricChangeCompositionCorrection k hH hK)) where
  toFun t := Unitary.linearIsometryEquiv.symm
    ((AffineMap.lineMap k h (t : ℝ)).metricChangeCompositionCorrection k
      (isStrictlyPositive_lineMap k h hK hH t t.2) hK)
  continuous_toFun := (Path.segment k h).continuous.metricChangeCompositionCorrection
    continuous_const (fun t ↦ isStrictlyPositive_lineMap k h hK hH t t.2) (fun _ ↦ hK)
  source' := by simp [← LinearIsometryEquiv.one_def]
  target' := by simp

/-- Evaluation of the canonical correction path, as an operator on vectors. -/
@[simp]
theorem metricChangeCompositionCorrectionPath_apply (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) (t : unitInterval) (v : E) :
    (metricChangeCompositionCorrectionPath h k hH hK t : E →L[ℝ] E) v =
      (AffineMap.lineMap k h (t : ℝ)).metricChangeCompositionCorrection k
        (isStrictlyPositive_lineMap k h hK hH t t.2) hK v :=
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
    (fun p ↦ isStrictlyPositive_lineMap (k p.2) (h p.2) (kpos p.2) (hpos p.2) p.1 p.1.2)
    (fun p ↦ kpos p.2))

/-- No correction path is introduced when the intermediate and final metrics agree. -/
@[simp]
theorem metricChangeCompositionCorrectionPath_self_apply (h : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (t : unitInterval) :
    metricChangeCompositionCorrectionPath h h hH hH t = 1 := by
  ext v
  simp [metricChangeCompositionCorrectionPath_apply]

/-- A homotopy from direct transport to `k` to successive transport through `h`, obtained
by composing the canonical orthogonal correction path with the direct transport. -/
noncomputable def metricChangeCompositionHomotopy (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) :
    ContinuousMap.Homotopy
      ⟨k.metricChangeTransport, k.metricChangeTransport.continuous⟩
      ⟨fun v ↦ h.metricChangeBetween k (h.metricChangeTransport v),
        (h.metricChangeBetween k).continuous.comp h.metricChangeTransport.continuous⟩ where
  toFun p := k.metricChangeTransport
    ((metricChangeCompositionCorrectionPath h k hH hK p.1).1 p.2)
  continuous_toFun := k.metricChangeTransport.continuous.comp
    ((continuous_subtype_val.comp
      ((metricChangeCompositionCorrectionPath h k hH hK).continuous.comp continuous_fst)).clm_apply
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
        ((metricChangeCompositionCorrectionPath h k hH hK t : E →L[ℝ] E) v) :=
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

/-- In finite dimension the canonical orthogonal correction path lands in the special
orthogonal group, giving the oriented comparison between direct and successive transport. -/
noncomputable def metricChangeCompositionCorrectionSpecialOrthogonalPath
    [FiniteDimensional ℝ E] (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) :
    Path (1 : TauCeti.specialOrthogonalGroup E)
      ⟨Unitary.linearIsometryEquiv.symm (h.metricChangeCompositionCorrection k hH hK),
        metricChangeCompositionCorrection_mem_specialOrthogonalGroup h k hH hK⟩ where
  toFun t := ⟨metricChangeCompositionCorrectionPath h k hH hK t,
    metricChangeCompositionCorrection_mem_specialOrthogonalGroup _ _ _ _⟩
  continuous_toFun := (metricChangeCompositionCorrectionPath h k hH hK).continuous.subtype_mk _
  source' := Subtype.ext (Path.source _)
  target' := Subtype.ext (Path.target _)

/-- Forgetting the determinant condition recovers the Hilbert-space correction path. -/
@[simp]
theorem metricChangeCompositionCorrectionSpecialOrthogonalPath_coe
    [FiniteDimensional ℝ E] (h k : E →L[ℝ] E →L[ℝ] ℝ)
    (hH : IsStrictlyPositive h♯) (hK : IsStrictlyPositive k♯) (t : unitInterval) :
    (metricChangeCompositionCorrectionSpecialOrthogonalPath h k hH hK t :
      unitary (E →L[ℝ] E)) = metricChangeCompositionCorrectionPath h k hH hK t := by
  rfl

end ContinuousLinearMap

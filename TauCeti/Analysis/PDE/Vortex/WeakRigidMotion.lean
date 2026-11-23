/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.RightInverse
public import TauCeti.Analysis.PDE.Vortex.Symmetry
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import TauCeti.Analysis.Complex.RigidMotion
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Rigid motions of the weak solutions and the weak right inverse of the vortex operator

The orientation-preserving isometries `z ↦ u z + a` of the plane, `u` on the unit circle, act on
plane vortex fields by `rotateField u ∘ translateField a` and on the target `ℝ ⊕ ℝ ⊕ ℂ` of the
gauge-fixed operator `L_x = d₀* ⊕ d₁` by `rotateTarget u ∘ translateField a`
(`TauCeti.Analysis.PDE.Vortex.Symmetry`). The formal adjoint `L_x*` intertwines these actions on
test fields (`TauCeti.Vortex.gaugeFixedAdjoint_translateField`,
`TauCeti.Vortex.gaugeFixedAdjoint_rotateField`), both act on values by linear isometries, and the
motion preserves every additive Haar measure on `ℂ`
(`AffineIsometryEquiv.measurePreserving_addHaar`). This file carries the action to the weak
`L²` theory of `L_x` of `TauCeti.Analysis.PDE.Vortex.RightInverse`, against any additive Haar
measure `μ`.

Write `x' = rotateField u (translateField a x)`, and let `f'` and `y'` be square-integrable
fields agreeing almost everywhere with `rotateTarget u (translateField a f)` and
`rotateField u (translateField a y)`.

* **Weak solutions.** `y'` is a weak solution of `L_{x'} y' = f'` exactly when `y` is a weak
  solution of `L_x y = f`
  (`TauCeti.Vortex.isGaugeFixedWeakSolution_rotateField_translateField_iff`), in the sense of
  `TauCeti.Vortex.IsGaugeFixedWeakSolution`; the test field `η` at `x` is traded for its moved
  target `rotateTarget u (translateField a η)` at `x'`. With `f = 0`, the motion carries the weak
  kernel of `L_x` onto that of `L_{x'}`
  (`TauCeti.Vortex.isGaugeFixedWeakSolution_zero_rotateField_translateField_iff`).
* **Minimal weak solutions.** Likewise `y'` is a minimal weak solution at `x'` exactly when `y` is
  one at `x`
  (`TauCeti.Vortex.isMinimalGaugeFixedWeakSolution_rotateField_translateField_iff`), in the sense
  of `TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution`.
* **The weak right inverse.** At a continuous field the minimal weak solution is unique
  (`TauCeti.Vortex.IsMinimalGaugeFixedWeakSolution.unique`). So if `Q` and `Q'` send every `f` to
  a minimal weak solution at `x` and at `x'`, as the weak right inverses of
  `TauCeti.Vortex.exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution` do, then `Q' f'` is
  the moved `Q f` almost everywhere
  (`TauCeti.Vortex.apply_ae_eq_rotateField_translateField_apply`). This is the translation and
  rotation law of the weak right inverse; `u = 1` and `a = 0` give the two separately.

The gauge laws, including the line-frame laws for constant gauges, are in
`TauCeti.Analysis.PDE.Vortex.FramedGauge.WeakKernel`, and the rigid-motion laws of the `H¹`
realization of `L_x` in `TauCeti.Analysis.PDE.Vortex.RigidMotion`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

namespace TauCeti.Vortex

open MeasureTheory
open scoped RealInnerProductSpace

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### Moving fields by an affine isometry of the plane -/

/-- The field `z ↦ R (v (g z))`: `v` pulled back by the affine isometry `g` of the plane, with
values moved by the linear isometry `R`. -/
private def motion (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) (v : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : EuclideanSpace ℝ (Fin 4) :=
  R (v (g z))

private theorem motion_apply (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) (v : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    motion R g v z = R (v (g z)) := (rfl)

private theorem rotateField_translateField_eq_motion (u : Circle) (a : ℂ)
    (v : ℂ → EuclideanSpace ℝ (Fin 4)) :
    rotateField u (translateField a v) = motion (fieldRotation u) (u.rigidMotion a) v :=
  funext fun z ↦ by
    rw [rotateField_apply_eq_fieldRotation, translateField_apply, motion_apply,
      Circle.rigidMotion_apply]

private theorem rotateTarget_translateField_eq_motion (u : Circle) (a : ℂ)
    (η : ℂ → EuclideanSpace ℝ (Fin 4)) :
    rotateTarget u (translateField a η) = motion (targetRotation u) (u.rigidMotion a) η :=
  funext fun z ↦ by
    rw [rotateTarget_apply_eq_targetRotation, translateField_apply, motion_apply,
      Circle.rigidMotion_apply]

private theorem motion_motion_symm (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) (v : ℂ → EuclideanSpace ℝ (Fin 4)) :
    motion R g (motion R.symm g.symm v) = v :=
  funext fun z ↦ by simp only [motion_apply, AffineIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.apply_symm_apply]

private theorem contDiff_motion {n : WithTop ℕ∞}
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g : ℂ ≃ᵃⁱ[ℝ] ℂ)
    {v : ℂ → EuclideanSpace ℝ (Fin 4)} (hv : ContDiff ℝ n v) : ContDiff ℝ n (motion R g v) :=
  R.toContinuousLinearEquiv.contDiff.comp
    (hv.comp g.toAffineIsometry.toContinuousAffineMap.contDiff)

private theorem hasCompactSupport_motion
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g : ℂ ≃ᵃⁱ[ℝ] ℂ)
    {v : ℂ → EuclideanSpace ℝ (Fin 4)} (hv : HasCompactSupport v) :
    HasCompactSupport (motion R g v) :=
  (hv.comp_homeomorph g.toHomeomorph).comp_left (g := R) (map_zero R)

private theorem memLp_motion (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) {v : ℂ → EuclideanSpace ℝ (Fin 4)} (hv : MemLp v 2 μ) :
    MemLp (motion R g v) 2 μ :=
  R.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp'
    (hv.comp_measurePreserving (g.measurePreserving_addHaar μ))

private theorem motion_ae_eq (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    (g : ℂ ≃ᵃⁱ[ℝ] ℂ) {v w : ℂ → EuclideanSpace ℝ (Fin 4)} (h : v =ᵐ[μ] w) :
    motion R g v =ᵐ[μ] motion R g w :=
  ((g.measurePreserving_addHaar μ).quasiMeasurePreserving.ae_eq_comp h).mono fun z hz ↦ by
    rw [motion_apply, motion_apply]
    exact congrArg R hz

/-- Moving both fields by the same motion preserves their `L²` pairing. -/
private theorem integral_inner_motion
    (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g : ℂ ≃ᵃⁱ[ℝ] ℂ)
    {v w v' w' : ℂ → EuclideanSpace ℝ (Fin 4)} (hv : v' =ᵐ[μ] motion R g v)
    (hw : w' =ᵐ[μ] motion R g w) :
    ∫ z, ⟪v' z, w' z⟫ ∂μ = ∫ z, ⟪v z, w z⟫ ∂μ := by
  refine (integral_congr_ae ?_).trans ((g.measurePreserving_addHaar μ).integral_comp
    g.toHomeomorph.measurableEmbedding fun z ↦ ⟪v z, w z⟫)
  filter_upwards [hv, hw] with z h₁ h₂
  rw [h₁, h₂, motion_apply, motion_apply, LinearIsometryEquiv.inner_map_map]

/-- The formal adjoint at the moved field of the moved target of a `C¹` test field is the moved
formal adjoint. -/
private theorem gaugeFixedAdjoint_rotateField_translateField (u : Circle) (a : ℂ)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 1 η) :
    gaugeFixedAdjoint (rotateField u (translateField a x)) (rotateTarget u (translateField a η)) =
      motion (fieldRotation u) (u.rigidMotion a) (gaugeFixedAdjoint x η) := by
  funext z
  have hd (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ translateField a η w i) (u * z) :=
    (contDiff_euclidean.1 (contDiff_translateField a hη) i).differentiable_one _
  rw [gaugeFixedAdjoint_rotateField (hd 2) (hd 3), rotateField_apply_eq_fieldRotation,
    gaugeFixedAdjoint_translateField, motion_apply, Circle.rigidMotion_apply]

/-! ### Weak solutions -/

/-- **Rigid motions of weak solutions.** Let `f'` and `y'` agree almost everywhere with
`rotateTarget u (translateField a f)` and `rotateField u (translateField a y)`. Then `y'` is a
weak solution of `L_{x'} y' = f'` at the moved field `x' = rotateField u (translateField a x)`
exactly when `y` is a weak solution of `L_x y = f`. -/
theorem isGaugeFixedWeakSolution_rotateField_translateField_iff (u : Circle) (a : ℂ)
    {f y f' y' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hf : ⇑f' =ᵐ[μ] rotateTarget u (translateField a f))
    (hy : ⇑y' =ᵐ[μ] rotateField u (translateField a y)) :
    IsGaugeFixedWeakSolution μ (rotateField u (translateField a x)) f' y' ↔
      IsGaugeFixedWeakSolution μ x f y := by
  rw [rotateTarget_translateField_eq_motion] at hf
  rw [rotateField_translateField_eq_motion] at hy
  -- Testing at `x'` against the moved target of `η` is testing at `x` against `η`.
  have key {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 2 η) :
      (∫ z, ⟪y' z, gaugeFixedAdjoint (rotateField u (translateField a x))
          (rotateTarget u (translateField a η)) z⟫ ∂μ =
        ∫ z, ⟪f' z, rotateTarget u (translateField a η) z⟫ ∂μ) ↔
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ := by
    rw [gaugeFixedAdjoint_rotateField_translateField u a x (hη.of_le one_le_two),
      rotateTarget_translateField_eq_motion, integral_inner_motion _ _ hy .rfl,
      integral_inner_motion _ _ hf .rfl]
  rw [isGaugeFixedWeakSolution_iff, isGaugeFixedWeakSolution_iff]
  refine ⟨fun h η hη hηc ↦ (key hη).1 ?_, fun h ν hν hνc ↦ ?_⟩
  · have h' := h _ (contDiff_motion (targetRotation u) (u.rigidMotion a) hη)
      (hasCompactSupport_motion _ _ hηc)
    rwa [← rotateTarget_translateField_eq_motion] at h'
  · -- The test field `ν` at `x'` is the moved target of a test field at `x`.
    have hT : rotateTarget u (translateField a
        (motion (targetRotation u).symm (u.rigidMotion a).symm ν)) = ν := by
      rw [rotateTarget_translateField_eq_motion, motion_motion_symm]
    have hη := contDiff_motion (targetRotation u).symm (u.rigidMotion a).symm hν
    have h' := (key hη).2 (h _ hη (hasCompactSupport_motion _ _ hνc))
    rwa [hT] at h'

/-- The rigid motions on weak solutions: if `y` is a weak solution of `L_x y = f`, then a
square-integrable field agreeing almost everywhere with `rotateField u (translateField a y)` is a
weak solution at `rotateField u (translateField a x)`, with data agreeing almost everywhere with
`rotateTarget u (translateField a f)`. -/
theorem IsGaugeFixedWeakSolution.rotateField_translateField
    {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} (h : IsGaugeFixedWeakSolution μ x f y) (u : Circle)
    (a : ℂ) {f' y' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hf : ⇑f' =ᵐ[μ] rotateTarget u (translateField a f))
    (hy : ⇑y' =ᵐ[μ] rotateField u (translateField a y)) :
    IsGaugeFixedWeakSolution μ (rotateField u (translateField a x)) f' y' :=
  (isGaugeFixedWeakSolution_rotateField_translateField_iff u a hf hy).2 h

/-! ### Minimal weak solutions -/

/-- **Rigid motions of the weak kernel.** If `w'` agrees almost everywhere with
`rotateField u (translateField a w)`, then `w'` is a weak solution of `L_{x'} w' = 0` at the moved
field `x' = rotateField u (translateField a x)` exactly when `w` is a weak solution of
`L_x w = 0`. -/
theorem isGaugeFixedWeakSolution_zero_rotateField_translateField_iff (u : Circle) (a : ℂ)
    {w w' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hw : ⇑w' =ᵐ[μ] rotateField u (translateField a w)) :
    IsGaugeFixedWeakSolution μ (rotateField u (translateField a x)) 0 w' ↔
      IsGaugeFixedWeakSolution μ x 0 w := by
  refine isGaugeFixedWeakSolution_rotateField_translateField_iff u a ?_ hw
  rw [rotateTarget_translateField_eq_motion]
  have h₀ : (0 : ℂ → EuclideanSpace ℝ (Fin 4)) = motion (targetRotation u) (u.rigidMotion a) 0 :=
    funext fun z ↦ by rw [motion_apply, Pi.zero_apply, Pi.zero_apply, map_zero]
  exact (Lp.coeFn_zero _ 2 μ).trans
    ((Filter.EventuallyEq.of_eq h₀).trans (motion_ae_eq _ _ (Lp.coeFn_zero _ 2 μ).symm))

/-- **Rigid motions of minimal weak solutions.** Let `f'` and `y'` agree almost everywhere with
`rotateTarget u (translateField a f)` and `rotateField u (translateField a y)`. Then `y'` is a
minimal weak solution of `L_{x'} y' = f'` at the moved field
`x' = rotateField u (translateField a x)` exactly when `y` is a minimal weak solution of
`L_x y = f`. -/
theorem isMinimalGaugeFixedWeakSolution_rotateField_translateField_iff (u : Circle) (a : ℂ)
    {f y f' y' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hf : ⇑f' =ᵐ[μ] rotateTarget u (translateField a f))
    (hy : ⇑y' =ᵐ[μ] rotateField u (translateField a y)) :
    IsMinimalGaugeFixedWeakSolution μ (rotateField u (translateField a x)) f' y' ↔
      IsMinimalGaugeFixedWeakSolution μ x f y := by
  rw [isMinimalGaugeFixedWeakSolution_iff, isMinimalGaugeFixedWeakSolution_iff,
    isGaugeFixedWeakSolution_rotateField_translateField_iff u a hf hy]
  refine and_congr_right fun _ ↦ ?_
  have hy' := hy
  rw [rotateField_translateField_eq_motion] at hy'
  refine ⟨fun h w hw ↦ ?_, fun h w' hw' ↦ ?_⟩
  · -- Move a weak solution of `L_x w = 0` to `x'`.
    have hm := memLp_motion (fieldRotation u) (u.rigidMotion a) (Lp.memLp w)
    have hw' : ⇑hm.toLp =ᵐ[μ] rotateField u (translateField a w) := by
      rw [rotateField_translateField_eq_motion]
      exact hm.coeFn_toLp
    rw [← integral_inner_motion _ _ hy' hm.coeFn_toLp]
    exact h _ ((isGaugeFixedWeakSolution_zero_rotateField_translateField_iff u a hw').2 hw)
  · -- Move a weak solution of `L_{x'} w' = 0` back to `x`.
    have hm := memLp_motion (fieldRotation u).symm (u.rigidMotion a).symm (Lp.memLp w')
    have hw : ⇑w' =ᵐ[μ] motion (fieldRotation u) (u.rigidMotion a) hm.toLp := by
      refine (motion_ae_eq (fieldRotation u) (u.rigidMotion a) hm.coeFn_toLp).mono fun z hz ↦ ?_
      rw [hz, motion_motion_symm]
    rw [integral_inner_motion _ _ hy' hw]
    refine h _ ((isGaugeFixedWeakSolution_zero_rotateField_translateField_iff u a ?_).1 hw')
    rwa [rotateField_translateField_eq_motion]

/-- The rigid motions on minimal weak solutions: if `y` is a minimal weak solution of `L_x y = f`,
then a square-integrable field agreeing almost everywhere with
`rotateField u (translateField a y)` is a minimal weak solution at
`rotateField u (translateField a x)`, with data agreeing almost everywhere with
`rotateTarget u (translateField a f)`. -/
theorem IsMinimalGaugeFixedWeakSolution.rotateField_translateField
    {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} (h : IsMinimalGaugeFixedWeakSolution μ x f y)
    (u : Circle) (a : ℂ) {f' y' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hf : ⇑f' =ᵐ[μ] rotateTarget u (translateField a f))
    (hy : ⇑y' =ᵐ[μ] rotateField u (translateField a y)) :
    IsMinimalGaugeFixedWeakSolution μ (rotateField u (translateField a x)) f' y' :=
  (isMinimalGaugeFixedWeakSolution_rotateField_translateField_iff u a hf hy).2 h

/-! ### The weak right inverse -/

/-- **Rigid motions of the minimal weak solution.** At a continuous field `x`, if `y` is the
minimal weak solution of `L_x y = f` and `y'` is the minimal weak solution at
`rotateField u (translateField a x)` with data agreeing almost everywhere with
`rotateTarget u (translateField a f)`, then `y'` agrees almost everywhere with
`rotateField u (translateField a y)`. -/
theorem IsMinimalGaugeFixedWeakSolution.ae_eq_rotateField_translateField (hx : Continuous x)
    {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} (h : IsMinimalGaugeFixedWeakSolution μ x f y)
    {u : Circle} {a : ℂ} {f' y' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hf : ⇑f' =ᵐ[μ] rotateTarget u (translateField a f))
    (h' : IsMinimalGaugeFixedWeakSolution μ (rotateField u (translateField a x)) f' y') :
    ⇑y' =ᵐ[μ] rotateField u (translateField a y) := by
  have hm := memLp_motion (fieldRotation u) (u.rigidMotion a) (Lp.memLp y)
  rw [rotateField_translateField_eq_motion]
  have hy : ⇑hm.toLp =ᵐ[μ] rotateField u (translateField a y) := by
    rw [rotateField_translateField_eq_motion]
    exact hm.coeFn_toLp
  have hx' : Continuous (rotateField u (translateField a x)) :=
    contDiff_zero.1 (contDiff_rotateField u (contDiff_translateField a (contDiff_zero.2 hx)))
  rw [h'.unique hx' (h.rotateField_translateField u a hf hy)]
  exact hm.coeFn_toLp

/-- **Rigid motions of the weak right inverse.** Let `x` be a continuous field and
`x' = rotateField u (translateField a x)`. If `Q f` is a minimal weak solution of `L_x y = f` and
`Q' f` one of `L_{x'} y = f` for every `f`, as for the weak right inverses of
`TauCeti.Vortex.exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution`, then for data `f'`
agreeing almost everywhere with `rotateTarget u (translateField a f)`, `Q' f'` agrees almost
everywhere with `rotateField u (translateField a (Q f))`. -/
theorem apply_ae_eq_rotateField_translateField_apply (hx : Continuous x) {u : Circle} {a : ℂ}
    {Q Q' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ → Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hQ : ∀ f, IsMinimalGaugeFixedWeakSolution μ x f (Q f))
    (hQ' : ∀ f, IsMinimalGaugeFixedWeakSolution μ (rotateField u (translateField a x)) f (Q' f))
    {f f' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hf : ⇑f' =ᵐ[μ] rotateTarget u (translateField a f)) :
    ⇑(Q' f') =ᵐ[μ] rotateField u (translateField a (Q f)) :=
  (hQ f).ae_eq_rotateField_translateField hx hf (hQ' f')

end TauCeti.Vortex

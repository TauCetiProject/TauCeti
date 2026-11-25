/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RigidMotion
public import TauCeti.Analysis.PDE.Vortex.RightInverse
public import TauCeti.Analysis.PDE.Vortex.Symmetry
public import TauCeti.MeasureTheory.Function.Lp.CompMeasurePreserving.AffineIsometry
import TauCeti.MeasureTheory.Integral.Bochner.MeasurePreserving
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

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

Write `x' = rotateField u (translateField a x)`. On `L²(μ; ℝ⁴)` the motion acts by the linear
isometry equivalences `MeasureTheory.Lp.rigidMotionₗᵢ μ 2 (targetRotation u) (u.rigidMotion a)` on
data and `MeasureTheory.Lp.rigidMotionₗᵢ μ 2 (fieldRotation u) (u.rigidMotion a)` on solutions,
sending the classes of `f` and `y` to those of `rotateTarget u (translateField a f)` and
`rotateField u (translateField a y)`. Write `f'` and `y'` for these moved classes.

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
  the moved `Q f` (`TauCeti.Vortex.apply_rigidMotionₗᵢ_eq_rigidMotionₗᵢ_apply`). This is the
  translation and rotation law of the weak right inverse; `u = 1` and `a = 0` give the two
  separately.

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

/-! ### Moving fields by an affine isometry of the plane

Smooth test fields `v` are moved pointwise to `R ∘ v ∘ g`; square-integrable classes are moved by
`MeasureTheory.Lp.rigidMotionₗᵢ`, which is almost everywhere `R ∘ f ∘ g`
(`MeasureTheory.Lp.coeFn_rigidMotionₗᵢ`). Pairings of moved fields are compared by
`MeasureTheory.MeasurePreserving.integral_inner_comp_comp`. -/

private theorem rotateTarget_translateField_eq_comp (u : Circle) (a : ℂ)
    (η : ℂ → EuclideanSpace ℝ (Fin 4)) :
    rotateTarget u (translateField a η) = targetRotation u ∘ η ∘ u.rigidMotion a :=
  funext fun z ↦ by
    rw [rotateTarget_apply_eq_targetRotation, translateField_apply, Function.comp_apply,
      Function.comp_apply, Circle.rigidMotion_apply]

/-- The formal adjoint at the moved field of the moved target of a `C¹` test field is the moved
formal adjoint. -/
private theorem gaugeFixedAdjoint_rotateField_translateField (u : Circle) (a : ℂ)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 1 η) :
    gaugeFixedAdjoint (rotateField u (translateField a x)) (rotateTarget u (translateField a η)) =
      fieldRotation u ∘ gaugeFixedAdjoint x η ∘ u.rigidMotion a := by
  funext z
  have hd (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ translateField a η w i) (u * z) :=
    (contDiff_euclidean.1 (contDiff_translateField a hη) i).differentiable_one _
  rw [gaugeFixedAdjoint_rotateField (hd 2) (hd 3), rotateField_apply_eq_fieldRotation,
    gaugeFixedAdjoint_translateField, Function.comp_apply, Function.comp_apply,
    Circle.rigidMotion_apply]

/-! ### Weak solutions -/

/-- **Rigid motions of weak solutions.** The moved field
`Lp.rigidMotionₗᵢ μ 2 (fieldRotation u) (u.rigidMotion a) y` is a weak solution of
`L_{x'} y' = f'` at the moved field `x' = rotateField u (translateField a x)` with the moved
data `f' = Lp.rigidMotionₗᵢ μ 2 (targetRotation u) (u.rigidMotion a) f` exactly when `y` is a
weak solution of `L_x y = f`. These are the classes of
`rotateField u (translateField a y)` and `rotateTarget u (translateField a f)`. -/
theorem isGaugeFixedWeakSolution_rotateField_translateField_iff (u : Circle) (a : ℂ)
    {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} :
    IsGaugeFixedWeakSolution μ (rotateField u (translateField a x))
        (Lp.rigidMotionₗᵢ μ 2 (targetRotation u) (u.rigidMotion a) f)
        (Lp.rigidMotionₗᵢ μ 2 (fieldRotation u) (u.rigidMotion a) y) ↔
      IsGaugeFixedWeakSolution μ x f y := by
  have hg := (u.rigidMotion a).measurePreserving_addHaar μ
  have hge := (u.rigidMotion a).toHomeomorph.measurableEmbedding
  -- Pairing a moved class with a moved test field is pairing the class with the test field.
  have pair {R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)}
      {v' v : ℂ → EuclideanSpace ℝ (Fin 4)} (hv : v' =ᵐ[μ] fun z ↦ R (v (u.rigidMotion a z)))
      (w : ℂ → EuclideanSpace ℝ (Fin 4)) :
      ∫ z, ⟪v' z, (R ∘ w ∘ u.rigidMotion a) z⟫ ∂μ = ∫ z, ⟪v z, w z⟫ ∂μ :=
    (integral_congr_ae (hv.comp₂ _ .rfl)).trans
      (hg.integral_inner_comp_comp hge R.toLinearIsometry v w)
  -- Testing at `x'` against the moved target of `η` is testing at `x` against `η`.
  have key {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 2 η) :
      (∫ z, ⟪Lp.rigidMotionₗᵢ μ 2 (fieldRotation u) (u.rigidMotion a) y z,
          gaugeFixedAdjoint (rotateField u (translateField a x))
            (rotateTarget u (translateField a η)) z⟫ ∂μ =
        ∫ z, ⟪Lp.rigidMotionₗᵢ μ 2 (targetRotation u) (u.rigidMotion a) f z,
          rotateTarget u (translateField a η) z⟫ ∂μ) ↔
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ := by
    rw [gaugeFixedAdjoint_rotateField_translateField u a x (hη.of_le one_le_two),
      rotateTarget_translateField_eq_comp, pair (Lp.coeFn_rigidMotionₗᵢ _ _ y),
      pair (Lp.coeFn_rigidMotionₗᵢ _ _ f)]
  -- A moved test field is a test field.
  have hmove (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) (g : ℂ ≃ᵃⁱ[ℝ] ℂ)
      {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
      ContDiff ℝ 2 (R ∘ η ∘ g) ∧ HasCompactSupport (R ∘ η ∘ g) :=
    ⟨R.toContinuousLinearEquiv.contDiff.comp
        (hη.comp g.toAffineIsometry.toContinuousAffineMap.contDiff),
      (hηc.comp_homeomorph g.toHomeomorph).comp_left (g := R) (map_zero R)⟩
  rw [isGaugeFixedWeakSolution_iff, isGaugeFixedWeakSolution_iff]
  refine ⟨fun h η hη hηc ↦ (key hη).1 ?_, fun h ν hν hνc ↦ ?_⟩
  · obtain ⟨hη', hηc'⟩ := hmove (targetRotation u) (u.rigidMotion a) hη hηc
    rw [rotateTarget_translateField_eq_comp]
    exact h _ hη' hηc'
  · -- The test field `ν` at `x'` is the moved target of a test field at `x`.
    have hT : rotateTarget u (translateField a
        ((targetRotation u).symm ∘ ν ∘ (u.rigidMotion a).symm)) = ν := by
      rw [rotateTarget_translateField_eq_comp]
      funext z
      simp only [Function.comp_apply, AffineIsometryEquiv.symm_apply_apply,
        LinearIsometryEquiv.apply_symm_apply]
    obtain ⟨hη, hηc⟩ := hmove (targetRotation u).symm (u.rigidMotion a).symm hν hνc
    have h' := (key hη).2 (h _ hη hηc)
    rwa [hT] at h'

/-- The rigid motions on weak solutions: if `y` is a weak solution of `L_x y = f`, then the moved
`y` is a weak solution at `rotateField u (translateField a x)` with the moved data. -/
theorem IsGaugeFixedWeakSolution.rotateField_translateField
    {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} (h : IsGaugeFixedWeakSolution μ x f y) (u : Circle)
    (a : ℂ) :
    IsGaugeFixedWeakSolution μ (rotateField u (translateField a x))
      (Lp.rigidMotionₗᵢ μ 2 (targetRotation u) (u.rigidMotion a) f)
      (Lp.rigidMotionₗᵢ μ 2 (fieldRotation u) (u.rigidMotion a) y) :=
  (isGaugeFixedWeakSolution_rotateField_translateField_iff u a).2 h

/-! ### Minimal weak solutions -/

/-- **Rigid motions of the weak kernel.** The moved field
`Lp.rigidMotionₗᵢ μ 2 (fieldRotation u) (u.rigidMotion a) w` is a weak solution of `L_{x'} w' = 0`
at the moved field `x' = rotateField u (translateField a x)` exactly when `w` is a weak solution
of `L_x w = 0`. -/
theorem isGaugeFixedWeakSolution_zero_rotateField_translateField_iff (u : Circle) (a : ℂ)
    {w : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} :
    IsGaugeFixedWeakSolution μ (rotateField u (translateField a x)) 0
        (Lp.rigidMotionₗᵢ μ 2 (fieldRotation u) (u.rigidMotion a) w) ↔
      IsGaugeFixedWeakSolution μ x 0 w := by
  simpa only [map_zero] using
    isGaugeFixedWeakSolution_rotateField_translateField_iff (x := x) u a (f := 0) (y := w)

/-- **Rigid motions of minimal weak solutions.**
`Lp.rigidMotionₗᵢ μ 2 (fieldRotation u) (u.rigidMotion a) y` is a minimal weak solution of
`L_{x'} y' = f'` at the moved field `x' = rotateField u (translateField a x)` with the moved data
`f' = Lp.rigidMotionₗᵢ μ 2 (targetRotation u) (u.rigidMotion a) f` exactly when `y` is a minimal
weak solution of `L_x y = f`. -/
theorem isMinimalGaugeFixedWeakSolution_rotateField_translateField_iff (u : Circle) (a : ℂ)
    {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} :
    IsMinimalGaugeFixedWeakSolution μ (rotateField u (translateField a x))
        (Lp.rigidMotionₗᵢ μ 2 (targetRotation u) (u.rigidMotion a) f)
        (Lp.rigidMotionₗᵢ μ 2 (fieldRotation u) (u.rigidMotion a) y) ↔
      IsMinimalGaugeFixedWeakSolution μ x f y := by
  rw [isMinimalGaugeFixedWeakSolution_iff, isMinimalGaugeFixedWeakSolution_iff,
    isGaugeFixedWeakSolution_rotateField_translateField_iff u a]
  refine and_congr_right fun _ ↦ ?_
  -- Every weak solution of `L_{x'} w' = 0` is the moved weak solution of `L_x w = 0`.
  rw [(Lp.rigidMotionₗᵢ μ 2 (fieldRotation u) (u.rigidMotion a)).surjective.forall]
  refine forall_congr' fun w ↦ ?_
  rw [isGaugeFixedWeakSolution_zero_rotateField_translateField_iff u a,
    (integral_congr_ae
        ((Lp.coeFn_rigidMotionₗᵢ _ _ y).comp₂ _ (Lp.coeFn_rigidMotionₗᵢ _ _ w))).trans
      (((u.rigidMotion a).measurePreserving_addHaar μ).integral_inner_comp_comp
        (u.rigidMotion a).toHomeomorph.measurableEmbedding (fieldRotation u).toLinearIsometry y w)]

/-- The rigid motions on minimal weak solutions: if `y` is a minimal weak solution of `L_x y = f`,
then the moved `y` is a minimal weak solution at `rotateField u (translateField a x)` with the
moved data. -/
theorem IsMinimalGaugeFixedWeakSolution.rotateField_translateField
    {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} (h : IsMinimalGaugeFixedWeakSolution μ x f y)
    (u : Circle) (a : ℂ) :
    IsMinimalGaugeFixedWeakSolution μ (rotateField u (translateField a x))
      (Lp.rigidMotionₗᵢ μ 2 (targetRotation u) (u.rigidMotion a) f)
      (Lp.rigidMotionₗᵢ μ 2 (fieldRotation u) (u.rigidMotion a) y) :=
  (isMinimalGaugeFixedWeakSolution_rotateField_translateField_iff u a).2 h

/-! ### The weak right inverse -/

/-- **Rigid motions of the minimal weak solution.** At a continuous field `x`, if `y` is the
minimal weak solution of `L_x y = f` and `y'` is the minimal weak solution at
`rotateField u (translateField a x)` with the moved data
`Lp.rigidMotionₗᵢ μ 2 (targetRotation u) (u.rigidMotion a) f`, then `y'` is the moved `y`. -/
theorem IsMinimalGaugeFixedWeakSolution.eq_rigidMotionₗᵢ (hx : Continuous x)
    {f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ} (h : IsMinimalGaugeFixedWeakSolution μ x f y)
    {u : Circle} {a : ℂ} {y' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (h' : IsMinimalGaugeFixedWeakSolution μ (rotateField u (translateField a x))
      (Lp.rigidMotionₗᵢ μ 2 (targetRotation u) (u.rigidMotion a) f) y') :
    y' = Lp.rigidMotionₗᵢ μ 2 (fieldRotation u) (u.rigidMotion a) y :=
  h'.unique (contDiff_zero.1 (contDiff_rotateField u (contDiff_translateField a
    (contDiff_zero.2 hx)))) (h.rotateField_translateField u a)

/-- **Rigid motions of the weak right inverse.** Let `x` be a continuous field and
`x' = rotateField u (translateField a x)`. If `Q f` is a minimal weak solution of `L_x y = f` and
`Q' f` one of `L_{x'} y = f` for every `f`, as for the weak right inverses of
`TauCeti.Vortex.exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution`, then `Q'` sends the
moved data to the moved `Q f`. -/
theorem apply_rigidMotionₗᵢ_eq_rigidMotionₗᵢ_apply (hx : Continuous x) {u : Circle} {a : ℂ}
    {Q Q' : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ → Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hQ : ∀ f, IsMinimalGaugeFixedWeakSolution μ x f (Q f))
    (hQ' : ∀ f, IsMinimalGaugeFixedWeakSolution μ (rotateField u (translateField a x)) f (Q' f))
    (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
    Q' (Lp.rigidMotionₗᵢ μ 2 (targetRotation u) (u.rigidMotion a) f) =
      Lp.rigidMotionₗᵢ μ 2 (fieldRotation u) (u.rigidMotion a) (Q f) :=
  (hQ f).eq_rigidMotionₗᵢ hx (hQ' _)

end TauCeti.Vortex

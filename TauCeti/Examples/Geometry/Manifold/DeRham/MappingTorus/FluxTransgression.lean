/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.MappingTorus.FluxTransgression
public import TauCeti.Geometry.Manifold.DifferentialForm.AddCircle

/-!
# Examples: the flux transgression on the torus

The flux transgression of loops of seamed paths (`TauCeti.MappingTorus.fluxTransgression`) is
evaluated here for the identity of the torus `T² = ℝ² / ℤ²`, whose seamed paths are its loops and
whose mapping torus is `T² × S¹`. The coordinate one-forms are `dx` and `dy`, the time forms of the
two circles pulled back along the projections (`TauCeti.Examples.SeamedFlux.dx`,
`TauCeti.Examples.SeamedFlux.dy`). For the constant symplectic vector field `X = ∂_x` of the area
form `dx ∧ dy`, the flux one-form is `ι_X (dx ∧ dy) = dy`.

The loop of loops `γ_s(t) = ([t], [s])` (`TauCeti.Examples.SeamedFlux.horizontalLoop`) sweeps out
the torus `(t, s) ↦ [γ_s(t), t]`, and its loop of start points is the vertical circle
`s ↦ ([0], [s])`. So the flux transgression of `dy` on its torus class is `∫ dy = 1` along that
circle (`TauCeti.Examples.SeamedFlux.fluxTransgression_dy_horizontalLoop`), while that of `dx` is
`0` (`TauCeti.Examples.SeamedFlux.fluxTransgression_dx_horizontalLoop`): the flux measures how far
the loop of start points winds in the direction dual to `X`.
-/

public section

noncomputable section

open Set Function TauCeti
open scoped Manifold ContDiff

namespace TauCeti.Examples.SeamedFlux

/-- The torus `T² = ℝ² / ℤ²`. -/
abbrev T2 : Type := UnitAddCircle × UnitAddCircle

/-- The coordinate one-form `dx` of the torus, the time form of the first circle. -/
def dx : SmoothForm (𝓘(ℝ).prod 𝓘(ℝ)) T2 ℝ 1 :=
  SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm 1)

/-- The coordinate one-form `dy` of the torus, the time form of the second circle. -/
def dy : SmoothForm (𝓘(ℝ).prod 𝓘(ℝ)) T2 ℝ 1 :=
  SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm 1)

/-- The coordinate one-form `dx` is closed. -/
theorem isClosed_dx : dx.IsClosed :=
  (AddCircle.isClosed_timeForm 1).mpullback _ _

/-- The coordinate one-form `dy` is closed. -/
theorem isClosed_dy : dy.IsClosed :=
  (AddCircle.isClosed_timeForm 1).mpullback _ _

/-- The loop of seamed paths `s ↦ (t ↦ ([t], [s]))` of the identity of the torus: each path runs
once around the first circle, at the height `[s]` in the second. -/
def horizontalLoop : C(UnitAddCircle, SeamedPath (Homeomorph.refl T2)) where
  toFun s := ⟨⟨fun t ↦ (((t : ℝ) : UnitAddCircle), s), by fun_prop⟩, by simp⟩
  continuous_toFun :=
    (ContinuousMap.continuous_of_continuous_uncurry _
      (by fun_prop : Continuous fun p : UnitAddCircle × unitInterval ↦
        (((p.2 : ℝ) : UnitAddCircle), p.1))).subtype_mk fun _ ↦ by simp

/-- The paths of the loop `TauCeti.Examples.SeamedFlux.horizontalLoop`. -/
theorem horizontalLoop_apply (s : UnitAddCircle) (t : unitInterval) :
    (horizontalLoop s).val t = (((t : ℝ) : UnitAddCircle), s) :=
  (rfl)

/-- The vertical circles `s ↦ ([t], [s])` of the torus are smooth. -/
private theorem contMDiff_verticalCircle (t : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) 1 fun s : ℝ ↦ ((t : UnitAddCircle), (s : UnitAddCircle)) :=
  contMDiff_const.prodMk (AddCircle.contMDiff_coe 1 1)

/-- The flux transgression of a closed one-form on the torus class of the horizontal loop is its
integral along the vertical circle `s ↦ ([0], [s])` of start points. -/
private theorem fluxTransgression_horizontalLoop {θ : SmoothForm (𝓘(ℝ).prod 𝓘(ℝ)) T2 ℝ 1}
    (hθ : θ.IsClosed) :
    MappingTorus.fluxTransgression (Homeomorph.refl T2) θ.val
        (ContinuousMap.singularHomologyMap ℤ 2
          ((SeamedPath.sectionFamily _ horizontalLoop).comp ContinuousMap.prodSwap)
          (addCircleProdFundamentalClass 1 1)) =
      pathIntegral θ.val (fun s : ℝ ↦ (((0 : ℝ) : UnitAddCircle), (s : UnitAddCircle))) 0 1 :=
  MappingTorus.fluxTransgression_singularHomologyMap_sectionFamily _
    (θ.isSmoothForm.of_le (by simp)) ((SmoothForm.isClosed_def θ).1 hθ) horizontalLoop 0
    (contMDiff_verticalCircle 0) fun _ ↦ rfl

/-- **The flux of `dy` along the horizontal loop is one.** For the identity of `T²` and the closed
one-form `dy = ι_{∂_x} (dx ∧ dy)`, the loop of seamed paths `γ_s(t) = ([t], [s])` has flux
transgression `1`: its loop of start points runs once around the second circle. -/
theorem fluxTransgression_dy_horizontalLoop :
    MappingTorus.fluxTransgression (Homeomorph.refl T2) dy.val
        (ContinuousMap.singularHomologyMap ℤ 2
          ((SeamedPath.sectionFamily _ horizontalLoop).comp ContinuousMap.prodSwap)
          (addCircleProdFundamentalClass 1 1)) = 1 := by
  rw [fluxTransgression_horizontalLoop isClosed_dy, dy, SmoothForm.coe_mpullback,
    pathIntegral_mpullback _ (fun _ _ ↦ mdifferentiableAt_snd)
      (fun _ _ ↦ (contMDiff_verticalCircle 0).mdifferentiableAt one_ne_zero)]
  exact (AddCircle.pathIntegral_timeForm_coe 1 0 1).trans (sub_zero 1)

/-- **The flux of `dx` along the horizontal loop is zero.** For the identity of `T²` and the closed
one-form `dx`, the loop of seamed paths `γ_s(t) = ([t], [s])` has flux transgression `0`: its loop
of start points stays at `[0]` in the first circle. -/
theorem fluxTransgression_dx_horizontalLoop :
    MappingTorus.fluxTransgression (Homeomorph.refl T2) dx.val
        (ContinuousMap.singularHomologyMap ℤ 2
          ((SeamedPath.sectionFamily _ horizontalLoop).comp ContinuousMap.prodSwap)
          (addCircleProdFundamentalClass 1 1)) = 0 := by
  rw [fluxTransgression_horizontalLoop isClosed_dx, dx, SmoothForm.coe_mpullback,
    pathIntegral_mpullback _ (fun _ _ ↦ mdifferentiableAt_fst)
      (fun _ _ ↦ (contMDiff_verticalCircle 0).mdifferentiableAt one_ne_zero)]
  exact pathIntegral_const_curve _ _ 0 1

end TauCeti.Examples.SeamedFlux

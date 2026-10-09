/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.UnitInterval

/-!
# Homeomorphisms onto the unit balls of normed spaces

A continuous linear equivalence `L : E ≃L[ℝ] F` of real normed spaces carries the closed unit ball
of `E` onto a convex body of `F`, which is usually not the closed unit ball of `F`.  Rescaling
each ray through the origin by the ratio of the gauges of the two convex bodies, which is Mathlib's
`gaugeRescaleHomeomorph`, corrects this: the result
`ContinuousLinearEquiv.unitBallHomeomorph L : E ≃ₜ F` is a homeomorphism carrying the open unit
ball, the closed unit ball and the unit sphere of `E` onto those of `F`.

The typical use compares the closed unit ball of the sup norm on `Fin n → ℝ`, which is the domain
of the characteristic maps of a CW complex, with the Euclidean unit disk.

Mathlib's radial homeomorphism `Homeomorph.unitBall : E ≃ₜ ball 0 1` of a real seminormed space onto
its open unit ball, followed by the inclusion of the open unit ball in the closed unit ball, is an
open embedding of `E` into the closed unit ball. It lets a chart valued in `E` be read as a chart
valued in the closed unit ball.

## Main declarations

* `ContinuousLinearEquiv.unitBallHomeomorph`: the rescaled homeomorphism.
* `ContinuousLinearEquiv.image_unitBallHomeomorph_closedBall`,
  `ContinuousLinearEquiv.image_unitBallHomeomorph_ball` and
  `ContinuousLinearEquiv.image_unitBallHomeomorph_sphere`: it matches the closed unit balls, the
  open unit balls and the unit spheres.
* `TauCeti.isOpenEmbedding_inclusion_comp_unitBall`: `E` embeds openly in its closed unit ball.
* `Homeomorph.unitBall_symm_apply_coe`: the inverse radial map in explicit coordinates.
* `TauCeti.nonempty_homeomorph_cube_closedBall`: the closed unit ball of a real normed space of
  finite dimension `k` is homeomorphic to the cube `Iᵏ`.
* `TauCeti.sphereHomeomorphOfFinrankEq`: the unit spheres of two finite-dimensional real normed
  spaces of the same dimension are homeomorphic.
-/

public section

noncomputable section

open Metric Set Topology

variable {W : Type*} [SeminormedAddCommGroup W] [NormedSpace ℝ W]

/-- The inverse of `unitBall` in explicit radial coordinates. -/
theorem _root_.Homeomorph.unitBall_symm_apply_coe (y : ball (0 : W) 1) :
    (Homeomorph.unitBall.symm y : W) =
      (Real.sqrt (1 - ‖y.1‖ ^ 2))⁻¹ • y.1 := by
  exact (Homeomorph.unitBall_symm_apply y).trans
    ((OpenPartialHomeomorph.toHomeomorphSourceTarget_symm_apply_coe
      (OpenPartialHomeomorph.univUnitBall (E := W)) y).trans
      (OpenPartialHomeomorph.univUnitBall_symm_apply y.1))

namespace ContinuousLinearEquiv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] (L : E ≃L[ℝ] F)

/-- The homeomorphism `E ≃ₜ F` obtained from a continuous linear equivalence `L : E ≃L[ℝ] F` by
rescaling each ray through the origin so that the image `L '' closedBall 0 1` of the closed unit
ball of `E` lands on the closed unit ball of `F` (`gaugeRescaleHomeomorph`). -/
def unitBallHomeomorph : E ≃ₜ F :=
  L.toHomeomorph.trans <| gaugeRescaleHomeomorph (L '' closedBall 0 1) (closedBall 0 1)
    ((convex_closedBall 0 1).linear_image L.toLinearMap)
    (by simpa using
      L.toHomeomorph.isOpenMap.image_mem_nhds (closedBall_mem_nhds (0 : E) one_pos))
    ((NormedSpace.isVonNBounded_closedBall ℝ E 1).image L.toContinuousLinearMap)
    (convex_closedBall 0 1) (closedBall_mem_nhds 0 one_pos)
    (NormedSpace.isVonNBounded_closedBall ℝ F 1)

lemma unitBallHomeomorph_apply (x : E) :
    L.unitBallHomeomorph x = gaugeRescale (L '' closedBall 0 1) (closedBall 0 1) (L x) :=
  (rfl)

/-- `ContinuousLinearEquiv.unitBallHomeomorph L` carries the closed unit ball onto the closed unit
ball. -/
@[simp]
theorem image_unitBallHomeomorph_closedBall :
    L.unitBallHomeomorph '' closedBall 0 1 = closedBall 0 1 := by
  have h := image_gaugeRescaleHomeomorph_closure
    (s := L '' closedBall 0 1) (t := closedBall (0 : F) 1)
    ((convex_closedBall 0 1).linear_image L.toLinearMap)
    (by simpa using
      L.toHomeomorph.isOpenMap.image_mem_nhds (closedBall_mem_nhds (0 : E) one_pos))
    ((NormedSpace.isVonNBounded_closedBall ℝ E 1).image L.toContinuousLinearMap)
    (convex_closedBall 0 1)
    (closedBall_mem_nhds (0 : F) one_pos) (NormedSpace.isVonNBounded_closedBall ℝ F 1)
  have hcl : IsClosed (L '' closedBall (0 : E) 1) :=
    L.toHomeomorph.isClosedMap _ isClosed_closedBall
  rw [hcl.closure_eq, closure_closedBall] at h
  rw [← h, image_image]
  -- `unitBallHomeomorph L` is by definition `L` followed by the gauge rescaling.
  rfl

/-- `ContinuousLinearEquiv.unitBallHomeomorph L` carries the open unit ball onto the open unit
ball. -/
@[simp]
theorem image_unitBallHomeomorph_ball :
    L.unitBallHomeomorph '' ball 0 1 = ball 0 1 := by
  simpa only [interior_closedBall _ one_ne_zero, image_unitBallHomeomorph_closedBall] using
    L.unitBallHomeomorph.image_interior (closedBall 0 1)

/-- `ContinuousLinearEquiv.unitBallHomeomorph L` carries the unit sphere onto the unit sphere. -/
@[simp]
theorem image_unitBallHomeomorph_sphere :
    L.unitBallHomeomorph '' sphere 0 1 = sphere 0 1 := by
  simpa only [frontier_closedBall _ one_ne_zero, image_unitBallHomeomorph_closedBall] using
    L.unitBallHomeomorph.image_frontier (closedBall 0 1)

end ContinuousLinearEquiv

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial homeomorphism `Homeomorph.unitBall` of `E` onto its open unit ball, followed by the
inclusion of the open unit ball in the closed unit ball, is an open embedding of `E` into the
closed unit ball. -/
theorem isOpenEmbedding_inclusion_comp_unitBall :
    IsOpenEmbedding (inclusion (ball_subset_closedBall (x := (0 : E)) (ε := 1)) ∘
      Homeomorph.unitBall) :=
  (IsOpenEmbedding.inclusion _ (isOpen_ball.preimage continuous_subtype_val)).comp
    Homeomorph.unitBall.isOpenEmbedding

open unitInterval in
/-- **The closed unit ball of a finite-dimensional real normed space is a cube.** The closed unit
ball of a real normed space of finite dimension `k` is homeomorphic to the cube `Iᵏ`. -/
theorem nonempty_homeomorph_cube_closedBall (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] :
    Nonempty ((Fin (Module.finrank ℝ F) → I) ≃ₜ closedBall (0 : F) 1) := by
  set k := Module.finrank ℝ F
  let L : (Fin k → ℝ) ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq (by simp [k])
  let e : closedBall (0 : Fin k → ℝ) 1 ≃ₜ closedBall (0 : F) 1 :=
    (L.unitBallHomeomorph.image _).trans
      (Homeomorph.setCongr L.image_unitBallHomeomorph_closedBall)
  -- Apply the affine interval homeomorphism coordinatewise, then identify the product of
  -- intervals with the closed unit ball of the sup norm.
  let a : (Fin k → I) ≃ₜ (Fin k → Icc (-1 : ℝ) 1) :=
    Homeomorph.piCongrRight fun _ ↦ (iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm
  let b : (Fin k → Icc (-1 : ℝ) 1) ≃ₜ univ.pi (fun _ : Fin k ↦ Icc (-1 : ℝ) 1) :=
    { toEquiv := (Equiv.Set.univPi _).symm
      continuous_toFun := by fun_prop
      continuous_invFun := continuous_pi fun i ↦
        ((continuous_apply i).comp continuous_subtype_val).subtype_mk _ }
  have h : univ.pi (fun _ : Fin k ↦ Icc (-1 : ℝ) 1) = closedBall (0 : Fin k → ℝ) 1 := by
    simp [closedBall_pi _ zero_le_one, Real.closedBall_eq_Icc]
  exact ⟨a.trans <| b.trans <| (Homeomorph.setCongr h).trans e⟩

section Sphere

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The unit spheres of two finite-dimensional real normed spaces of the same dimension are
homeomorphic, through `ContinuousLinearEquiv.unitBallHomeomorph` applied to
`ContinuousLinearEquiv.ofFinrankEq`. -/
def sphereHomeomorphOfFinrankEq (hEF : Module.finrank ℝ E = Module.finrank ℝ F) :
    sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1 :=
  let L : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq hEF
  (L.unitBallHomeomorph.image _).trans (Homeomorph.setCongr L.image_unitBallHomeomorph_sphere)

/-- `TauCeti.sphereHomeomorphOfFinrankEq` is the restriction of
`ContinuousLinearEquiv.unitBallHomeomorph` to the unit sphere. -/
@[simp]
theorem coe_sphereHomeomorphOfFinrankEq_apply (hEF : Module.finrank ℝ E = Module.finrank ℝ F)
    (x : sphere (0 : E) 1) :
    (sphereHomeomorphOfFinrankEq hEF x : F) =
      (ContinuousLinearEquiv.ofFinrankEq hEF).unitBallHomeomorph x :=
  (rfl)

end Sphere

end TauCeti

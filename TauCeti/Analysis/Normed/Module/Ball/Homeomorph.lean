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
* `ContinuousLinearEquiv.norm_unitBallHomeomorph_le_one_iff` and its variants: the same
  statements read pointwise on norms, for the homeomorphism and its inverse.
* `TauCeti.isOpenEmbedding_inclusion_comp_unitBall`: `E` embeds openly in its closed unit ball.
* `Homeomorph.unitBall_symm_apply_coe`: the inverse radial map in explicit coordinates.
* `TauCeti.cubeHomeomorphClosedBall`: the cube `I^N` is the closed unit ball of the sup norm on
  `N → ℝ`, through `t ↦ 2 * t - 1` in every coordinate.
* `TauCeti.nonempty_homeomorph_cube_closedBall`: the closed unit ball of a real normed space of
  finite dimension `k` is homeomorphic to the cube `Iᵏ`.
* `TauCeti.sphereHomeomorphOfFinrankEq` and `TauCeti.closedBallHomeomorphOfFinrankEq`: the unit
  spheres, and the closed unit balls, of two finite-dimensional real normed spaces of the same
  dimension are homeomorphic.
* `TauCeti.nonempty_homeomorph_closedBall_of_convex`: a compact convex set with nonempty interior
  is homeomorphic to a closed ball of the same dimension.
* `TauCeti.nonempty_homeomorph_Icc_prod_closedBall`: a nondegenerate closed rectangle is
  homeomorphic to the closed unit ball of any two-dimensional real normed space.
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

/-- `ContinuousLinearEquiv.unitBallHomeomorph L` preserves the condition `‖x‖ ≤ 1`. -/
@[simp]
theorem norm_unitBallHomeomorph_le_one_iff {x : E} :
    ‖L.unitBallHomeomorph x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  simpa using (L.unitBallHomeomorph.injective.mem_set_image.symm.trans
    (Set.ext_iff.1 L.image_unitBallHomeomorph_closedBall (L.unitBallHomeomorph x))).symm

/-- `ContinuousLinearEquiv.unitBallHomeomorph L` preserves the condition `‖x‖ < 1`. -/
@[simp]
theorem norm_unitBallHomeomorph_lt_one_iff {x : E} :
    ‖L.unitBallHomeomorph x‖ < 1 ↔ ‖x‖ < 1 := by
  simpa using (L.unitBallHomeomorph.injective.mem_set_image.symm.trans
    (Set.ext_iff.1 L.image_unitBallHomeomorph_ball (L.unitBallHomeomorph x))).symm

/-- `ContinuousLinearEquiv.unitBallHomeomorph L` preserves the condition `‖x‖ = 1`. -/
@[simp]
theorem norm_unitBallHomeomorph_eq_one_iff {x : E} :
    ‖L.unitBallHomeomorph x‖ = 1 ↔ ‖x‖ = 1 := by
  simpa using (L.unitBallHomeomorph.injective.mem_set_image.symm.trans
    (Set.ext_iff.1 L.image_unitBallHomeomorph_sphere (L.unitBallHomeomorph x))).symm

/-- The inverse of `ContinuousLinearEquiv.unitBallHomeomorph L` preserves the condition
`‖y‖ ≤ 1`. -/
@[simp]
theorem norm_unitBallHomeomorph_symm_le_one_iff {y : F} :
    ‖L.unitBallHomeomorph.symm y‖ ≤ 1 ↔ ‖y‖ ≤ 1 := by
  simpa using (L.norm_unitBallHomeomorph_le_one_iff (x := L.unitBallHomeomorph.symm y)).symm

/-- The inverse of `ContinuousLinearEquiv.unitBallHomeomorph L` preserves the condition
`‖y‖ < 1`. -/
@[simp]
theorem norm_unitBallHomeomorph_symm_lt_one_iff {y : F} :
    ‖L.unitBallHomeomorph.symm y‖ < 1 ↔ ‖y‖ < 1 := by
  simpa using (L.norm_unitBallHomeomorph_lt_one_iff (x := L.unitBallHomeomorph.symm y)).symm

/-- The inverse of `ContinuousLinearEquiv.unitBallHomeomorph L` preserves the condition
`‖y‖ = 1`. -/
@[simp]
theorem norm_unitBallHomeomorph_symm_eq_one_iff {y : F} :
    ‖L.unitBallHomeomorph.symm y‖ = 1 ↔ ‖y‖ = 1 := by
  simpa using (L.norm_unitBallHomeomorph_eq_one_iff (x := L.unitBallHomeomorph.symm y)).symm

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

section Cube

open unitInterval

variable (N : Type*) [Fintype N]

/-- The cube `I^N` is the closed unit ball of the sup norm on `N → ℝ`, through the affine
homeomorphism `t ↦ 2 * t - 1` of `I` onto `[-1, 1]` in every coordinate
(`TauCeti.coe_cubeHomeomorphClosedBall_apply`). -/
def cubeHomeomorphClosedBall : (N → I) ≃ₜ closedBall (0 : N → ℝ) 1 :=
  -- Apply the affine interval homeomorphism coordinatewise, then identify the product of
  -- intervals with the closed unit ball of the sup norm.
  let a : (N → I) ≃ₜ (N → Icc (-1 : ℝ) 1) :=
    Homeomorph.piCongrRight fun _ ↦ (iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm
  let b : (N → Icc (-1 : ℝ) 1) ≃ₜ univ.pi (fun _ : N ↦ Icc (-1 : ℝ) 1) :=
    { toEquiv := (Equiv.Set.univPi _).symm
      continuous_toFun := by fun_prop
      continuous_invFun := continuous_pi fun i ↦
        ((continuous_apply i).comp continuous_subtype_val).subtype_mk _ }
  have h : univ.pi (fun _ : N ↦ Icc (-1 : ℝ) 1) = closedBall (0 : N → ℝ) 1 := by
    simp [closedBall_pi _ zero_le_one, Real.closedBall_eq_Icc]
  a.trans <| b.trans <| Homeomorph.setCongr h

variable {N}

@[simp]
theorem coe_cubeHomeomorphClosedBall_apply (y : N → I) (i : N) :
    (cubeHomeomorphClosedBall N y : N → ℝ) i = 2 * (y i : ℝ) - 1 := by
  -- The last two homeomorphisms only forget the coordinatewise interval membership proofs.
  have h : (cubeHomeomorphClosedBall N y : N → ℝ) i =
      ((iccHomeoI (-1 : ℝ) 1 (by norm_num)).symm (y i) : ℝ) :=
    rfl
  rw [h, iccHomeoI_symm_apply_coe]
  ring

@[simp]
theorem coe_cubeHomeomorphClosedBall_symm_apply (z : closedBall (0 : N → ℝ) 1) (i : N) :
    (((cubeHomeomorphClosedBall N).symm z i : I) : ℝ) = ((z : N → ℝ) i + 1) / 2 := by
  have h := coe_cubeHomeomorphClosedBall_apply ((cubeHomeomorphClosedBall N).symm z) i
  rw [Homeomorph.apply_symm_apply] at h
  linarith

open unitInterval in
/-- **The closed unit ball of a finite-dimensional real normed space is a cube.** The closed unit
ball of a real normed space of finite dimension `k` is homeomorphic to the cube `Iᵏ`. -/
theorem nonempty_homeomorph_cube_closedBall (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] :
    Nonempty ((Fin (Module.finrank ℝ F) → I) ≃ₜ closedBall (0 : F) 1) := by
  set k := Module.finrank ℝ F
  let L : (Fin k → ℝ) ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq (by simp [k])
  exact ⟨(cubeHomeomorphClosedBall (Fin k)).trans <| (L.unitBallHomeomorph.image _).trans
    (Homeomorph.setCongr L.image_unitBallHomeomorph_closedBall)⟩

end Cube

section FinrankEq

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

/-- The closed unit balls of two finite-dimensional real normed spaces of the same dimension are
homeomorphic, through `ContinuousLinearEquiv.unitBallHomeomorph` applied to
`ContinuousLinearEquiv.ofFinrankEq`. -/
def closedBallHomeomorphOfFinrankEq (hEF : Module.finrank ℝ E = Module.finrank ℝ F) :
    closedBall (0 : E) 1 ≃ₜ closedBall (0 : F) 1 :=
  let L : E ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq hEF
  (L.unitBallHomeomorph.image _).trans (Homeomorph.setCongr L.image_unitBallHomeomorph_closedBall)

/-- `TauCeti.closedBallHomeomorphOfFinrankEq` is the restriction of
`ContinuousLinearEquiv.unitBallHomeomorph` to the closed unit ball. -/
@[simp]
theorem coe_closedBallHomeomorphOfFinrankEq_apply
    (hEF : Module.finrank ℝ E = Module.finrank ℝ F) (x : closedBall (0 : E) 1) :
    (closedBallHomeomorphOfFinrankEq hEF x : F) =
      (ContinuousLinearEquiv.ofFinrankEq hEF).unitBallHomeomorph x :=
  (rfl)

/-- **Convex bodies are balls.** A compact convex set with nonempty interior in a
finite-dimensional real normed space is homeomorphic to the closed unit ball of any real normed
space of the same dimension. -/
theorem nonempty_homeomorph_closedBall_of_convex {s : Set E} (hc : Convex ℝ s)
    (hs : IsCompact s) (hn : (interior s).Nonempty)
    (hEF : Module.finrank ℝ E = Module.finrank ℝ F) :
    Nonempty (s ≃ₜ closedBall (0 : F) 1) := by
  obtain ⟨h, -, hcl, -⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hn hs.isBounded
  rw [hs.isClosed.closure_eq] at hcl
  exact ⟨((h.image s).trans (Homeomorph.setCongr hcl)).trans
    (closedBallHomeomorphOfFinrankEq hEF)⟩

end FinrankEq

/-- A product of two nondegenerate closed real intervals is homeomorphic to the closed unit ball
of any two-dimensional real normed space. -/
theorem nonempty_homeomorph_Icc_prod_closedBall {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hF : Module.finrank ℝ F = 2) :
    Nonempty ((Icc a b ×ˢ Icc c d) ≃ₜ closedBall (0 : F) 1) :=
  nonempty_homeomorph_closedBall_of_convex ((convex_Icc _ _).prod (convex_Icc _ _))
    (isCompact_Icc.prod isCompact_Icc)
    (by rw [interior_prod_eq, interior_Icc, interior_Icc]
        exact (nonempty_Ioo.mpr hab).prod (nonempty_Ioo.mpr hcd))
    (by simp [hF])

end TauCeti

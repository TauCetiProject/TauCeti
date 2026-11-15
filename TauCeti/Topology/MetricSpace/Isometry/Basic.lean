/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Splitting off the last coordinate of a tuple is an isometry

For a pseudo-emetric space `α`, the identification `Fin.initLastIsometry α n` of
`Fin (n + 1) → α` with `(Fin n → α) × α`, sending `x` to `(Fin.init x, x (Fin.last n))`, is an
isometry for the sup distances. It is `Fin.appendIsometry n 1` read backwards, with the second
factor `Fin 1 → α` identified with `α`.

So it carries balls, closed balls and spheres around the origin onto the corresponding products: a
ball onto the product of balls, and a sphere onto the union of `sphere ×ˢ closedBall` and
`closedBall ×ˢ sphere`. This is how the characteristic map of a cell of a product with an interval
splits off the interval coordinate.

## Main declarations

* `Fin.initLastIsometry`: the isometry `(Fin (n + 1) → α) ≃ᵢ (Fin n → α) × α`.
* `Fin.image_ball_initLastIsometry`, `Fin.image_closedBall_initLastIsometry`,
  `Fin.image_sphere_initLastIsometry`, `Fin.preimage_ball_prod_initLastIsometry`: its images of
  balls, closed balls and spheres around the origin, and its preimage of a product of balls.
-/

public section

noncomputable section

open Metric Set

namespace Fin

section PseudoEMetricSpace

variable (α : Type*) [PseudoEMetricSpace α]

/-- The identification of `Fin (n + 1) → α` with `(Fin n → α) × α`, splitting off the last
coordinate; it is an isometry for the sup distances. -/
def initLastIsometry (n : ℕ) : (Fin (n + 1) → α) ≃ᵢ (Fin n → α) × α :=
  (Fin.appendIsometry n 1).symm.trans
    { toEquiv := (Equiv.refl _).prodCongr (Equiv.funUnique (Fin 1) α)
      isometry_toFun := isometry_id.prodMap (IsometryEquiv.funUnique (Fin 1) α).isometry }

variable {α}

/-- Splitting off the last coordinate sends `x` to `(Fin.init x, x (Fin.last n))`. -/
@[simp]
theorem initLastIsometry_apply {n : ℕ} (x : Fin (n + 1) → α) :
    initLastIsometry α n x = (Fin.init x, x (Fin.last n)) := by
  -- `Fin.appendIsometry` restricts `x` along `Fin.castAdd 1` and `Fin.natAdd n`; the second factor
  -- is a bare `IsometryEquiv` structure, which `simp` evaluates through its `toEquiv`.
  have hinit (i : Fin n) : Fin.castAdd 1 i = i.castSucc := Fin.ext (by simp)
  have hlast : Fin.natAdd n (0 : Fin 1) = Fin.last n := Fin.ext (by simp)
  ext i <;> simp [initLastIsometry, ← IsometryEquiv.coe_toEquiv, Fin.init, hinit, hlast]

/-- The inverse of splitting off the last coordinate appends the second component with
`Fin.snoc`. -/
@[simp]
theorem initLastIsometry_symm_apply {n : ℕ} (p : (Fin n → α) × α) :
    (initLastIsometry α n).symm p = Fin.snoc p.1 p.2 := by
  rw [IsometryEquiv.symm_apply_eq, initLastIsometry_apply, Fin.init_snoc, Fin.snoc_last]

/-- Splitting off the last coordinate sends the origin to the origin. -/
theorem initLastIsometry_zero [Zero α] (n : ℕ) : initLastIsometry α n 0 = 0 := by
  ext <;> simp [Fin.init]

end PseudoEMetricSpace

section PseudoMetricSpace

variable {α : Type*} [PseudoMetricSpace α] [Zero α]

/-- Splitting off the last coordinate carries the ball of radius `r` around the origin onto the
product of the balls of radius `r` around the origin. -/
theorem image_ball_initLastIsometry (n : ℕ) (r : ℝ) :
    initLastIsometry α n '' ball 0 r = ball 0 r ×ˢ ball 0 r := by
  rw [IsometryEquiv.image_ball, initLastIsometry_zero, ball_prod_same, Prod.zero_eq_mk]

/-- Splitting off the last coordinate carries the closed ball of radius `r` around the origin onto
the product of the closed balls of radius `r` around the origin. -/
theorem image_closedBall_initLastIsometry (n : ℕ) (r : ℝ) :
    initLastIsometry α n '' closedBall 0 r = closedBall 0 r ×ˢ closedBall 0 r := by
  rw [IsometryEquiv.image_closedBall, initLastIsometry_zero, closedBall_prod_same, Prod.zero_eq_mk]

/-- Splitting off the last coordinate carries the sphere of radius `r` around the origin onto the
union of `sphere ×ˢ closedBall` and `closedBall ×ˢ sphere` of radius `r` around the origin. -/
theorem image_sphere_initLastIsometry (n : ℕ) (r : ℝ) :
    initLastIsometry α n '' sphere 0 r =
      sphere 0 r ×ˢ closedBall 0 r ∪ closedBall 0 r ×ˢ sphere 0 r := by
  rw [IsometryEquiv.image_sphere, initLastIsometry_zero, sphere_prod, Prod.fst_zero, Prod.snd_zero]

/-- The preimage under splitting off the last coordinate of the product of the balls of radius `r`
around the origin is the ball of radius `r` around the origin. -/
theorem preimage_ball_prod_initLastIsometry (n : ℕ) (r : ℝ) :
    initLastIsometry α n ⁻¹' (ball 0 r ×ˢ ball 0 r) = ball 0 r :=
  ((initLastIsometry α n).toEquiv.preimage_eq_iff_eq_image _ _).2
    (image_ball_initLastIsometry n r).symm

end PseudoMetricSpace

end Fin

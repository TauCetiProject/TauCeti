/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Splitting tuples of coordinates is an isometry, and nearby points of an isometric image

For a pseudo-emetric space `α`, the identification `Fin.initLastIsometry α n` of
`Fin (n + 1) → α` with `(Fin n → α) × α`, sending `x` to `(Fin.init x, x (Fin.last n))`, is an
isometry for the sup distances. It is `Fin.appendIsometry n 1` read backwards, with the second
factor `Fin 1 → α` identified with `α`.

So it carries balls, closed balls and spheres around the origin onto the corresponding products: a
ball onto the product of balls, and a sphere onto the union of `sphere ×ˢ closedBall` and
`closedBall ×ˢ sphere`. This is how the characteristic map of a cell of a product with an interval
splits off the interval coordinate.

The same holds for Mathlib's splitting `(Fin.appendIsometryOfEq h).symm` of `Fin n → α` into
`(Fin m → α) × (Fin l → α)` when `m + l = n`, which splits the coordinates of a product cell.

For an isometry `ι : Z → E` and a dense set `D ⊆ Z`, every point `y : E` has a point `z ∈ D`
whose distance to each `s : Z` is at most `2 * dist (ι s) y` plus any prescribed positive slack.
This brings an approximation made in the ambient space `E` back to `D`.

## Main declarations

* `Fin.initLastIsometry`: the isometry `(Fin (n + 1) → α) ≃ᵢ (Fin n → α) × α`.
* `Fin.image_ball_initLastIsometry`, `Fin.image_closedBall_initLastIsometry`,
  `Fin.image_sphere_initLastIsometry`, `Fin.preimage_ball_prod_initLastIsometry`: its images of
  balls, closed balls and spheres around the origin, and its preimage of a product of balls.
* `Fin.image_ball_appendIsometryOfEq_symm`, `Fin.image_closedBall_appendIsometryOfEq_symm`,
  `Fin.image_sphere_appendIsometryOfEq_symm`: the same images for the splitting of `Fin n → α`
  into `(Fin m → α) × (Fin l → α)`, with the membership forms
  `Fin.mem_ball_iff_appendIsometryOfEq_symm`, `Fin.mem_closedBall_iff_appendIsometryOfEq_symm` and
  `Fin.mem_sphere_iff_appendIsometryOfEq_symm`.
* `Isometry.exists_mem_dist_le_two_mul_dist_add`: for every `y : E` and `r > 0`, a point `z ∈ D`
  with `dist s z ≤ 2 * dist (ι s) y + r` for every `s : Z`.
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

/-- Splitting `Fin n → α` into `(Fin m → α) × (Fin l → α)` sends the origin to the origin. -/
theorem appendIsometryOfEq_symm_zero [Zero α] {m l n : ℕ} (h : m + l = n) :
    (appendIsometryOfEq (α := α) h).symm 0 = 0 := by
  ext <;> simp

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

variable {m l n : ℕ} (h : m + l = n) (r : ℝ)

/-- Splitting `Fin n → α` into `(Fin m → α) × (Fin l → α)` carries the ball of radius `r` around the
origin onto the product of the balls of radius `r` around the origin. -/
theorem image_ball_appendIsometryOfEq_symm :
    (appendIsometryOfEq (α := α) h).symm '' ball 0 r = ball 0 r ×ˢ ball 0 r := by
  rw [IsometryEquiv.image_ball, appendIsometryOfEq_symm_zero, ball_prod_same, Prod.zero_eq_mk]

/-- Splitting `Fin n → α` into `(Fin m → α) × (Fin l → α)` carries the closed ball of radius `r`
around the origin onto the product of the closed balls of radius `r` around the origin. -/
theorem image_closedBall_appendIsometryOfEq_symm :
    (appendIsometryOfEq (α := α) h).symm '' closedBall 0 r = closedBall 0 r ×ˢ closedBall 0 r := by
  rw [IsometryEquiv.image_closedBall, appendIsometryOfEq_symm_zero, closedBall_prod_same,
    Prod.zero_eq_mk]

/-- Splitting `Fin n → α` into `(Fin m → α) × (Fin l → α)` carries the sphere of radius `r` around
the origin onto the union of `sphere ×ˢ closedBall` and `closedBall ×ˢ sphere` of radius `r` around
the origin. -/
theorem image_sphere_appendIsometryOfEq_symm :
    (appendIsometryOfEq (α := α) h).symm '' sphere 0 r =
      sphere 0 r ×ˢ closedBall 0 r ∪ closedBall 0 r ×ˢ sphere 0 r := by
  rw [IsometryEquiv.image_sphere, appendIsometryOfEq_symm_zero, sphere_prod, Prod.fst_zero,
    Prod.snd_zero]

variable {r}

/-- A point lies in the ball of radius `r` around the origin if and only if both parts of its
splitting into `(Fin m → α) × (Fin l → α)` do. -/
theorem mem_ball_iff_appendIsometryOfEq_symm {x : Fin n → α} :
    x ∈ ball 0 r ↔
      ((appendIsometryOfEq h).symm x).1 ∈ ball 0 r ∧
        ((appendIsometryOfEq h).symm x).2 ∈ ball 0 r := by
  rw [← mem_prod, ← image_ball_appendIsometryOfEq_symm h,
    (appendIsometryOfEq h).symm.injective.mem_set_image]

/-- A point lies in the closed ball of radius `r` around the origin if and only if both parts of
its splitting into `(Fin m → α) × (Fin l → α)` do. -/
theorem mem_closedBall_iff_appendIsometryOfEq_symm {x : Fin n → α} :
    x ∈ closedBall 0 r ↔
      ((appendIsometryOfEq h).symm x).1 ∈ closedBall 0 r ∧
        ((appendIsometryOfEq h).symm x).2 ∈ closedBall 0 r := by
  rw [← mem_prod, ← image_closedBall_appendIsometryOfEq_symm h,
    (appendIsometryOfEq h).symm.injective.mem_set_image]

/-- A point lies on the sphere of radius `r` around the origin if and only if one part of its
splitting into `(Fin m → α) × (Fin l → α)` lies on that sphere and the other in the closed ball. -/
theorem mem_sphere_iff_appendIsometryOfEq_symm {x : Fin n → α} :
    x ∈ sphere 0 r ↔
      ((appendIsometryOfEq h).symm x).1 ∈ sphere 0 r ∧
          ((appendIsometryOfEq h).symm x).2 ∈ closedBall 0 r ∨
        ((appendIsometryOfEq h).symm x).1 ∈ closedBall 0 r ∧
          ((appendIsometryOfEq h).symm x).2 ∈ sphere 0 r := by
  rw [← mem_prod, ← mem_prod, ← mem_union, ← image_sphere_appendIsometryOfEq_symm h,
    (appendIsometryOfEq h).symm.injective.mem_set_image]

end PseudoMetricSpace

end Fin

namespace Isometry

/-- For an isometry `ι : Z → E` of a nonempty space, a dense set `D ⊆ Z`, every `y : E` and every
`r > 0`, there is `z ∈ D` with `dist s z ≤ 2 * dist (ι s) y + r` for every `s : Z`. -/
theorem exists_mem_dist_le_two_mul_dist_add {Z E : Type*} [PseudoMetricSpace Z]
    [PseudoMetricSpace E] [Nonempty Z] {ι : Z → E} (hι : Isometry ι) {D : Set Z} (hD : Dense D)
    (y : E) {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ D, ∀ s, dist s z ≤ 2 * dist (ι s) y + r := by
  obtain ⟨_, ⟨s₀, rfl⟩, hs₀⟩ := (infDist_lt_iff (range_nonempty ι)).1
    (lt_add_of_pos_right (infDist y (range ι)) (half_pos hr))
  obtain ⟨z, hzD, hz⟩ := hD.exists_dist_lt s₀ (half_pos hr)
  refine ⟨z, hzD, fun s ↦ ?_⟩
  have h₁ := dist_triangle s s₀ z
  have h₂ := hι.dist_eq s s₀
  have h₃ := dist_triangle (ι s) y (ι s₀)
  have h₄ : infDist y (range ι) ≤ dist (ι s) y := by
    rw [dist_comm]
    exact infDist_le_dist_of_mem (mem_range_self s)
  linarith

end Isometry

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Analysis.Normed.Module.Ball.Radial.Push

/-!
# The radial push on the Euclidean disk

For `0 ≤ r`, the straight-line homotopy `TauCeti.radialPush r` maps the closed unit ball into
itself, so it restricts to a homotopy `TauCeti.TopCat.diskRadialPush r` of the disk
`TopCat.disk n`. It starts at the identity and, for `0 < r ≤ 1`, fixes the boundary sphere at all
times and ends by sending the shell `r ≤ ‖x‖` into the boundary sphere. Its end map
`x ↦ x / max r ‖x‖` and the reversed homotopy from it to the identity are how a map defined on the
boundary sphere is spread over the outer shell of a disk, as in cell reattachment arguments.

## Main declarations

* `TauCeti.TopCat.diskRadialPush`: the radial push `TauCeti.radialPush r` on the disk.
* `TauCeti.TopCat.diskRadialPush_diskBoundaryInclusion`: it fixes the boundary sphere.
* `TauCeti.TopCat.norm_diskRadialPush_one`: at the end it sends the shell `r ≤ ‖x‖` into the
  boundary sphere.
-/

public section

noncomputable section

open Metric unitInterval

universe u

namespace TauCeti.TopCat

variable {n : ℕ} {r : ℝ}

/-- The radial push `TauCeti.radialPush r`, for `0 ≤ r`, as a homotopy of the disk
`TopCat.disk n`: at time `t` it sends `x` to `(1 - t) • x + t • r⁻¹ • radialRetraction r x`. -/
def diskRadialPush (n : ℕ) (hr : 0 ≤ r) : C(I × TopCat.disk.{u} n, TopCat.disk.{u} n) where
  toFun p := ULift.up ⟨radialPush r p.1 p.2.down.1, mem_closedBall_zero_iff.2 <|
    norm_radialPush_le_one hr p.1 (mem_closedBall_zero_iff.1 p.2.down.2)⟩
  continuous_toFun := continuous_uliftUp.comp <| ((continuous_radialPush hr).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp
      (continuous_uliftDown.comp continuous_snd)))).subtype_mk _

@[simp]
theorem coe_diskRadialPush_apply_down (hr : 0 ≤ r) (t : I) (x : TopCat.disk.{u} n) :
    ((diskRadialPush n hr (t, x)).down : EuclideanSpace ℝ (Fin n)) = radialPush r t x.down.1 :=
  (rfl)

/-- At time `0` the radial push on the disk is the identity. -/
@[simp]
theorem diskRadialPush_zero (hr : 0 ≤ r) (x : TopCat.disk.{u} n) :
    diskRadialPush n hr (0, x) = x :=
  ULift.ext (Subtype.ext ((coe_diskRadialPush_apply_down hr 0 x).trans (radialPush_zero r _)))

/-- For `0 < r ≤ 1`, the radial push on the disk fixes the boundary sphere. -/
theorem diskRadialPush_diskBoundaryInclusion (hr : 0 < r) (hr1 : r ≤ 1) (t : I)
    (s : TopCat.diskBoundary.{u} n) :
    diskRadialPush n hr.le (t, TopCat.diskBoundaryInclusion n s) =
      TopCat.diskBoundaryInclusion n s :=
  ULift.ext (Subtype.ext ((coe_diskRadialPush_apply_down hr.le t _).trans
    (radialPush_of_norm_eq_one hr hr1 t
      ((mem_range_diskBoundaryInclusion_iff _).1 (Set.mem_range_self s)))))

/-- At the end, the radial push on the disk sends the shell `r ≤ ‖x‖` into the boundary sphere. -/
theorem norm_diskRadialPush_one (hr : 0 < r) {x : TopCat.disk.{u} n} (hx : r ≤ ‖x.down.1‖) :
    ‖(diskRadialPush n hr.le (1, x)).down.1‖ = 1 := by
  rw [coe_diskRadialPush_apply_down, norm_radialPush_one hr hx]

end TauCeti.TopCat

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk

/-!
# The antipodal map of the Euclidean disk

The antipodal map `x ↦ -x` of the closed unit ball of `EuclideanSpace ℝ (Fin n)` is an involutive
automorphism `TauCeti.diskNeg n` of the disk `TopCat.disk n`. It restricts on the boundary sphere
to the antipodal map `TauCeti.diskBoundaryNeg n` of the sphere
(`TauCeti.diskBoundaryNeg_comp_diskBoundaryInclusion`), so it is an automorphism of the pair
`(D^n, ∂D^n)`. Such automorphisms reparametrize the cells of a CW complex or a cell attachment
without changing the attached space; for `n = 1` the antipodal map is the reflection `r = -id` of
`D¹ = [-1, 1]`, which exchanges the two points of `S⁰`.

## Main declarations

* `TauCeti.diskNeg`: the antipodal automorphism of the disk.
* `TauCeti.diskBoundaryNeg_comp_diskBoundaryInclusion`: it restricts to the antipodal map of the
  boundary sphere.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace TauCeti

/-- The antipodal map `x ↦ -x` of the disk `TopCat.disk n`, as an automorphism. It restricts on
the boundary sphere to `TauCeti.diskBoundaryNeg`
(`TauCeti.diskBoundaryNeg_comp_diskBoundaryInclusion`). -/
def diskNeg (n : ℕ) : TopCat.disk.{u} n ≅ TopCat.disk.{u} n :=
  TopCat.isoOfHomeo
    { toFun x := ULift.up (-x.down)
      invFun x := ULift.up (-x.down)
      left_inv x := ULift.ext (neg_neg x.down)
      right_inv x := ULift.ext (neg_neg x.down)
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

@[simp]
lemma diskNeg_hom_apply_down {n : ℕ} (x : TopCat.disk.{u} n) :
    ((diskNeg n).hom x).down = -x.down :=
  (rfl)

/-- The antipodal map of the disk is an involution. -/
@[simp]
lemma diskNeg_inv (n : ℕ) : (diskNeg.{u} n).inv = (diskNeg n).hom :=
  (rfl)

/-- The antipodal map of the disk restricts on the boundary sphere to the antipodal map of the
sphere. -/
@[reassoc]
lemma diskBoundaryNeg_comp_diskBoundaryInclusion (n : ℕ) :
    diskBoundaryNeg n ≫ TopCat.diskBoundaryInclusion.{u} n =
      TopCat.diskBoundaryInclusion n ≫ (diskNeg n).hom := by
  ext x
  exact ULift.ext (Subtype.ext (by simp [TopCat.coe_diskBoundaryInclusion_apply_down]))

end TauCeti

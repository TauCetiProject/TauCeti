/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk

/-!
# The reflection of the Euclidean disk

The map `x ↦ -x` is a homeomorphism of the disk `TopCat.disk n` (`TauCeti.TopCat.diskNegIso`) and
of its boundary sphere (`TauCeti.TopCat.diskBoundaryNegIso`, whose underlying map is the antipodal
map `TauCeti.TopCat.diskBoundaryNeg`). The two commute with the boundary inclusion
(`TauCeti.TopCat.diskBoundaryNeg_comp_diskBoundaryInclusion`), so together they form an isomorphism
of the pair `(Dⁿ, ∂Dⁿ)`. This is the reflection used to compare cells attached along attaching maps
which differ by the antipodal map, for instance the cells of two charts at a critical point of a
function on a line.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace TauCeti.TopCat

/-- The reflection `x ↦ -x` of the disk `TopCat.disk n`. -/
private def diskNeg (n : ℕ) : TopCat.disk.{u} n ⟶ TopCat.disk.{u} n :=
  TopCat.ofHom ⟨fun x ↦ ULift.up ⟨-x.down.1, by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_neg] using x.down.2⟩, by fun_prop⟩

/-- The reflection `x ↦ -x` of the disk `TopCat.disk n`, as a homeomorphism. It is its own
inverse. -/
def diskNegIso (n : ℕ) : TopCat.disk.{u} n ≅ TopCat.disk.{u} n where
  hom := diskNeg n
  inv := diskNeg n
  hom_inv_id := by ext x; exact ULift.ext (Subtype.ext (neg_neg x.down.1))
  inv_hom_id := by ext x; exact ULift.ext (Subtype.ext (neg_neg x.down.1))

@[simp]
theorem coe_diskNegIso_hom_apply_down {n : ℕ} (x : TopCat.disk.{u} n) :
    (((diskNegIso n).hom x).down : EuclideanSpace ℝ (Fin n)) = -x.down.1 :=
  (rfl)

@[simp]
theorem coe_diskNegIso_inv_apply_down {n : ℕ} (x : TopCat.disk.{u} n) :
    (((diskNegIso n).inv x).down : EuclideanSpace ℝ (Fin n)) = -x.down.1 :=
  (rfl)

/-- The antipodal map `x ↦ -x` of the boundary sphere `TopCat.diskBoundary n`, as a
homeomorphism. It is its own inverse. -/
def diskBoundaryNegIso (n : ℕ) : TopCat.diskBoundary.{u} n ≅ TopCat.diskBoundary.{u} n where
  hom := diskBoundaryNeg n
  inv := diskBoundaryNeg n
  hom_inv_id := by ext x; exact diskBoundaryNeg_diskBoundaryNeg_apply x
  inv_hom_id := by ext x; exact diskBoundaryNeg_diskBoundaryNeg_apply x

@[simp]
theorem diskBoundaryNegIso_hom (n : ℕ) : (diskBoundaryNegIso.{u} n).hom = diskBoundaryNeg n :=
  (rfl)

@[simp]
theorem diskBoundaryNegIso_inv (n : ℕ) : (diskBoundaryNegIso.{u} n).inv = diskBoundaryNeg n :=
  (rfl)

/-- The antipodal map of the boundary sphere is the restriction of the reflection of the disk. -/
@[reassoc]
theorem diskBoundaryNeg_comp_diskBoundaryInclusion (n : ℕ) :
    diskBoundaryNeg.{u} n ≫ TopCat.diskBoundaryInclusion n =
      TopCat.diskBoundaryInclusion n ≫ (diskNegIso n).hom := by
  ext x
  refine ULift.ext (Subtype.ext ?_)
  simp only [TopCat.hom_comp, ContinuousMap.comp_apply, coe_diskBoundaryInclusion_apply_down,
    coe_diskNegIso_hom_apply_down, diskBoundaryNeg_apply_down]
  rfl

end TauCeti.TopCat

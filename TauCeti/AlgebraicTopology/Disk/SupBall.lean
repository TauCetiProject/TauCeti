/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk

/-!
# The sup-ball pair

The closed unit ball of the sup norm on `Fin n → ℝ` modulo its unit sphere
(`TauCeti.supBallBoundaryPair`) is the intermediate model of the `n`-ball between the cube
`(Iⁿ, ∂Iⁿ)` and the Euclidean disk `(Dⁿ, Sⁿ⁻¹)`:

* the affine homeomorphism `TauCeti.cubeHomeomorphClosedBall`, `t ↦ (2 tⱼ - 1)ⱼ`, is an isomorphism
  of pairs from the cube (`TauCeti.cubeBoundaryPairIsoSupBall`);
* the radial rescaling `TauCeti.diskHomeomorphClosedBall` is an isomorphism of pairs from the disk
  (`TauCeti.diskBoundaryPairIsoSupBall`), whose inverse is `x ↦ (‖x‖∞ / ‖x‖₂) x`.

The first is a diagonal affine map with positive coefficients and the second rescales each ray
from the origin by a positive factor. Their composite from the cube to the disk is the
inverse of `TauCeti.diskBoundaryPairIsoCube`
(`TauCeti.cubeBoundaryPairIsoSupBall_hom_comp_diskBoundaryPairIsoSupBall_inv`), so classes in the
relative homology of the three pairs may be compared along these explicit maps.

## Main definitions

* `TauCeti.supBallBoundaryPair n`: the closed unit ball of the sup norm on `Fin n → ℝ` and its unit
  sphere.
* `TauCeti.cubeBoundaryPairIsoSupBall n`: the cube pair is the sup-ball pair.
* `TauCeti.diskBoundaryPairIsoSupBall n`: the disk pair is the sup-ball pair.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace TauCeti

variable (n : ℕ)

/-- The closed unit ball of the sup norm on `Fin n → ℝ` and its unit sphere, as a topological pair
lifted to the universe `u`. -/
abbrev supBallBoundaryPair : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.of (ULift.{u} (Metric.closedBall (0 : Fin n → ℝ) 1)))
    {x | ‖((x.down : Metric.closedBall (0 : Fin n → ℝ) 1) : Fin n → ℝ)‖ = 1}

/-- **The cube pair is the sup-ball pair**: the affine homeomorphism
`TauCeti.cubeHomeomorphClosedBall`, `t ↦ (2 tⱼ - 1)ⱼ`, is an isomorphism of pairs
`(Iⁿ, ∂Iⁿ) ≅ (B∞ⁿ, S∞ⁿ⁻¹)`. -/
def cubeBoundaryPairIsoSupBall : cubeBoundaryPair.{u} n ≅ supBallBoundaryPair.{u} n :=
  TopPair.ofSubsetIso (Homeomorph.ulift.trans
      ((cubeHomeomorphClosedBall (Fin n)).trans Homeomorph.ulift.symm))
    -- The anonymous constructor records the membership statement in the form that
    -- `TopPair.ofSubsetIso` expects, so that its API lemmas rewrite this isomorphism.
    fun x ↦ ⟨(norm_cubeHomeomorphClosedBall_eq_one_iff x.down).2,
      (norm_cubeHomeomorphClosedBall_eq_one_iff x.down).1⟩

variable {n}

/-- On the cube, `TauCeti.cubeBoundaryPairIsoSupBall` is `TauCeti.cubeHomeomorphClosedBall`. -/
@[simp]
lemma cubeBoundaryPairIsoSupBall_hom_fst_apply_down (x : (cubeBoundaryPair.{u} n).fst) :
    (TopPair.Hom.fst (cubeBoundaryPairIsoSupBall.{u} n).hom x).down =
      cubeHomeomorphClosedBall (Fin n) x.down := by
  rw [cubeBoundaryPairIsoSupBall, TopPair.ofSubsetIso_hom]
  exact congrArg ULift.down (TopPair.ofSubsetMap_fst_apply _ _ x)

/-- On the sup-ball, the inverse of `TauCeti.cubeBoundaryPairIsoSupBall` is the inverse of
`TauCeti.cubeHomeomorphClosedBall`. -/
@[simp]
lemma cubeBoundaryPairIsoSupBall_inv_fst_apply_down (x : (supBallBoundaryPair.{u} n).fst) :
    (TopPair.Hom.fst (cubeBoundaryPairIsoSupBall.{u} n).inv x).down =
      (cubeHomeomorphClosedBall (Fin n)).symm x.down := by
  rw [cubeBoundaryPairIsoSupBall, TopPair.ofSubsetIso_inv]
  exact congrArg ULift.down (TopPair.ofSubsetMap_fst_apply _ _ x)

variable (n)

/-- **The disk pair is the sup-ball pair**: the radial rescaling `TauCeti.diskHomeomorphClosedBall`
is an isomorphism of pairs `(Dⁿ, Sⁿ⁻¹) ≅ (B∞ⁿ, S∞ⁿ⁻¹)`
(`TauCeti.diskBoundaryPairIsoSupBall_hom_fst_apply_down`). Its inverse is the map
`x ↦ (‖x‖∞ / ‖x‖₂) x` from the sup-ball onto the Euclidean disk. It is built as
`TauCeti.diskBoundaryPairIsoCube` followed by `TauCeti.cubeBoundaryPairIsoSupBall`, since
`TauCeti.diskHomeomorphCube` is the radial rescaling followed by the inverse of
`TauCeti.cubeHomeomorphClosedBall`. -/
def diskBoundaryPairIsoSupBall : diskBoundaryPair.{u} n ≅ supBallBoundaryPair.{u} n :=
  diskBoundaryPairIsoCube n ≪≫ cubeBoundaryPairIsoSupBall n

variable {n}

-- Not `@[simp]`: `TauCeti.diskBoundaryPair_fst` rewrites the implicit objects of its left side.
/-- On the disk, `TauCeti.diskBoundaryPairIsoSupBall` is the radial rescaling. -/
lemma diskBoundaryPairIsoSupBall_hom_fst_apply_down (z : (diskBoundaryPair.{u} n).fst) :
    (TopPair.Hom.fst (diskBoundaryPairIsoSupBall.{u} n).hom z).down =
      diskHomeomorphClosedBall n z := by
  rw [diskBoundaryPairIsoSupBall, Iso.trans_hom, TopPair.Hom.fst_comp, TopCat.comp_app,
    cubeBoundaryPairIsoSupBall_hom_fst_apply_down, diskBoundaryPairIsoCube_hom,
    diskBoundaryPairToCube_fst_apply_down]
  exact (congrArg _ (diskHomeomorphCube_apply z)).trans (Homeomorph.apply_symm_apply _ _)

/-- On the sup-ball, the inverse of `TauCeti.diskBoundaryPairIsoSupBall` is the inverse of the
radial rescaling. -/
lemma diskBoundaryPairIsoSupBall_inv_fst_apply (x : (supBallBoundaryPair.{u} n).fst) :
    TopPair.Hom.fst (diskBoundaryPairIsoSupBall.{u} n).inv x =
      (diskHomeomorphClosedBall n).symm x.down := by
  refine ((diskHomeomorphClosedBall n).symm_apply_eq.2 ?_).symm
  rw [← diskBoundaryPairIsoSupBall_hom_fst_apply_down, ← TopCat.comp_app, ← TopPair.Hom.fst_comp,
    Iso.inv_hom_id, TopPair.Hom.fst_id, TopCat.id_app]

variable (n)

/-- **The cube-to-disk homeomorphism factors through the sup-ball**: the affine homeomorphism of
the cube onto the sup-ball, followed by the inverse `x ↦ (‖x‖∞ / ‖x‖₂) x` of the radial
rescaling, is the inverse of `TauCeti.diskBoundaryPairIsoCube`. -/
@[reassoc (attr := simp)]
theorem cubeBoundaryPairIsoSupBall_hom_comp_diskBoundaryPairIsoSupBall_inv :
    (cubeBoundaryPairIsoSupBall.{u} n).hom ≫ (diskBoundaryPairIsoSupBall.{u} n).inv =
      (diskBoundaryPairIsoCube n).inv := by
  rw [diskBoundaryPairIsoSupBall, Iso.trans_inv, Iso.hom_inv_id_assoc]

end TauCeti

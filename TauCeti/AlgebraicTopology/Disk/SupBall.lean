/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk

/-!
# The closed unit ball of the sup norm and its boundary sphere

The characteristic maps of the cells of a CW complex are defined on the closed unit ball of the
sup norm on `Fin n → ℝ`. This file makes that ball and its boundary sphere a topological pair,
`TauCeti.supBallPair n`, and identifies it with the cube pair `(Iⁿ, ∂Iⁿ)` through the affine
homeomorphism `TauCeti.cubeHomeomorphClosedBall` (`TauCeti.cubeBoundaryPairIsoSupBall`) and with
the Euclidean disk pair `(Dⁿ, Sⁿ⁻¹)` through the radial homeomorphism
`TauCeti.diskHomeomorphClosedBall` (`TauCeti.diskBoundaryPairIsoSupBall`). The latter is defined
as the disk-to-cube isomorphism `TauCeti.diskBoundaryPairIsoCube` followed by the former, so the
three identifications are compatible.

## Main definitions

* `TauCeti.supBallPair n`: the closed unit ball of the sup norm on `Fin n → ℝ`, relative to its
  unit sphere.
* `TauCeti.cubeBoundaryPairIsoSupBall n`: `(Iⁿ, ∂Iⁿ) ≅ (Bⁿ_∞, ∂Bⁿ_∞)`, the map `t ↦ 2t - 1` in
  every coordinate.
* `TauCeti.diskBoundaryPairIsoSupBall n`: `(Dⁿ, Sⁿ⁻¹) ≅ (Bⁿ_∞, ∂Bⁿ_∞)`, the radial rescaling.
-/

public section

noncomputable section

open CategoryTheory Metric Set
open scoped unitInterval

universe u

namespace TauCeti

variable (n : ℕ)

/-- The closed unit ball `Bⁿ_∞` of the sup norm on `Fin n → ℝ`, relative to its unit sphere
`∂Bⁿ_∞`, lifted to the universe `u`. It is the domain pair of the characteristic maps of the
`n`-cells of a CW complex. -/
abbrev supBallPair : TopPair.{u} :=
  TopPair.ofSubset (X := TopCat.of (ULift.{u} (closedBall (0 : Fin n → ℝ) 1)))
    {z | ‖(z.down : Fin n → ℝ)‖ = 1}

/-- The affine homeomorphism `TauCeti.cubeHomeomorphClosedBall` carries the boundary of the cube
onto the unit sphere of the sup norm, read on the lifted ambient spaces of the two pairs. -/
private lemma mem_cubeBoundaryPair_iff_mem_supBallPair (z : ULift.{u} (Fin n → I)) :
    z ∈ ULift.down ⁻¹' Cube.boundary (Fin n) ↔
      Homeomorph.ulift.trans ((cubeHomeomorphClosedBall (Fin n)).trans Homeomorph.ulift.symm) z ∈
        {z : ULift.{u} (closedBall (0 : Fin n → ℝ) 1) | ‖(z.down : Fin n → ℝ)‖ = 1} :=
  (norm_cubeHomeomorphClosedBall_eq_one_iff z.down).symm

/-- The affine homeomorphism `TauCeti.cubeHomeomorphClosedBall` of the cube onto the closed unit
ball of the sup norm, `t ↦ 2t - 1` in every coordinate, as an isomorphism of pairs
`(Iⁿ, ∂Iⁿ) ≅ (Bⁿ_∞, ∂Bⁿ_∞)`. -/
def cubeBoundaryPairIsoSupBall : cubeBoundaryPair.{u} n ≅ supBallPair.{u} n :=
  TopPair.ofSubsetIso
    (Homeomorph.ulift.trans ((cubeHomeomorphClosedBall (Fin n)).trans Homeomorph.ulift.symm))
    (mem_cubeBoundaryPair_iff_mem_supBallPair n)

variable {n}

/-- On ambient spaces, `TauCeti.cubeBoundaryPairIsoSupBall` is `TauCeti.cubeHomeomorphClosedBall`.
-/
@[simp]
lemma cubeBoundaryPairIsoSupBall_hom_fst_apply_down (z : (cubeBoundaryPair.{u} n).fst) :
    (TopPair.Hom.fst (cubeBoundaryPairIsoSupBall.{u} n).hom z).down =
      cubeHomeomorphClosedBall (Fin n) z.down := by
  rw [cubeBoundaryPairIsoSupBall, TopPair.ofSubsetIso_hom]
  -- The ambient map of `TopPair.ofSubsetMap` is the given map, read through the universe lifts.
  exact congrArg ULift.down (TopPair.ofSubsetMap_fst_apply _ _ z)

/-- On ambient spaces, the inverse of `TauCeti.cubeBoundaryPairIsoSupBall` is the inverse of
`TauCeti.cubeHomeomorphClosedBall`. -/
@[simp]
lemma cubeBoundaryPairIsoSupBall_inv_fst_apply_down (z : (supBallPair.{u} n).fst) :
    (TopPair.Hom.fst (cubeBoundaryPairIsoSupBall.{u} n).inv z).down =
      (cubeHomeomorphClosedBall (Fin n)).symm z.down := by
  have h := congrArg (fun f : supBallPair.{u} n ⟶ supBallPair.{u} n ↦ (TopPair.Hom.fst f z).down)
    (cubeBoundaryPairIsoSupBall.{u} n).inv_hom_id
  simp only [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
    cubeBoundaryPairIsoSupBall_hom_fst_apply_down, TopPair.Hom.fst_id] at h
  exact ((cubeHomeomorphClosedBall (Fin n)).symm_apply_eq.2 h.symm).symm

variable (n)

/-- The radial homeomorphism `TauCeti.diskHomeomorphClosedBall` of the Euclidean disk onto the
closed unit ball of the sup norm, as an isomorphism of pairs `(Dⁿ, Sⁿ⁻¹) ≅ (Bⁿ_∞, ∂Bⁿ_∞)`. It is
`TauCeti.diskBoundaryPairIsoCube` followed by `TauCeti.cubeBoundaryPairIsoSupBall`, and is computed
on points by `TauCeti.diskBoundaryPairIsoSupBall_hom_fst_apply_down` and
`TauCeti.diskBoundaryPairIsoSupBall_inv_fst_apply`. -/
def diskBoundaryPairIsoSupBall : diskBoundaryPair.{u} n ≅ supBallPair.{u} n :=
  diskBoundaryPairIsoCube n ≪≫ cubeBoundaryPairIsoSupBall n

/-- `TauCeti.diskBoundaryPairIsoSupBall` is `TauCeti.diskBoundaryPairIsoCube` followed by
`TauCeti.cubeBoundaryPairIsoSupBall`. -/
lemma diskBoundaryPairIsoSupBall_hom :
    (diskBoundaryPairIsoSupBall.{u} n).hom =
      (diskBoundaryPairIsoCube n).hom ≫ (cubeBoundaryPairIsoSupBall n).hom :=
  (rfl)

variable {n}

-- The two point lemmas below are not `@[simp]`: simp rewrites the source object
-- `(diskBoundaryPair n).fst` of their left-hand sides to `TopCat.disk n` by
-- `TauCeti.diskBoundaryPair_fst`, so they are not in simp-normal form.

/-- On ambient spaces, `TauCeti.diskBoundaryPairIsoSupBall` is the radial homeomorphism
`TauCeti.diskHomeomorphClosedBall`. -/
lemma diskBoundaryPairIsoSupBall_hom_fst_apply_down (z : (diskBoundaryPair.{u} n).fst) :
    (TopPair.Hom.fst (diskBoundaryPairIsoSupBall.{u} n).hom z).down =
      diskHomeomorphClosedBall n z := by
  rw [diskBoundaryPairIsoSupBall_hom, diskBoundaryPairIsoCube_hom]
  simp only [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
    cubeBoundaryPairIsoSupBall_hom_fst_apply_down, diskBoundaryPairToCube_fst_apply_down,
    diskHomeomorphCube_apply z, Homeomorph.apply_symm_apply]

/-- On ambient spaces, the inverse of `TauCeti.diskBoundaryPairIsoSupBall` is the inverse of the
radial homeomorphism `TauCeti.diskHomeomorphClosedBall`. -/
lemma diskBoundaryPairIsoSupBall_inv_fst_apply (z : (supBallPair.{u} n).fst) :
    (TopPair.Hom.fst (diskBoundaryPairIsoSupBall.{u} n).inv z : TopCat.disk.{u} n) =
      (diskHomeomorphClosedBall n).symm z.down := by
  have h := congrArg (fun f : supBallPair.{u} n ⟶ supBallPair.{u} n ↦ (TopPair.Hom.fst f z).down)
    (diskBoundaryPairIsoSupBall.{u} n).inv_hom_id
  simp only [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply,
    diskBoundaryPairIsoSupBall_hom_fst_apply_down, TopPair.Hom.fst_id] at h
  exact ((diskHomeomorphClosedBall n).symm_apply_eq.2 h.symm).symm

end TauCeti

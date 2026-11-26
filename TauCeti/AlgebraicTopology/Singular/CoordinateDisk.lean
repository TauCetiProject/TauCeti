/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk.SupBall
public import TauCeti.AlgebraicTopology.Singular.Cubical.Triangulation.CoordinateClass
public import TauCeti.AlgebraicTopology.Singular.ReducedRelative

import TauCeti.Algebra.Ring.Parity

/-!
# The coordinate sup-ball and disk classes

The coordinate cube class `TauCeti.coordinateCubeClass` of `(Iⁿ, ∂Iⁿ)` is the coordinate-oriented
fundamental class of the cube. This file carries it to the two other standard models of the
`n`-ball along the explicit homeomorphisms of `TauCeti.AlgebraicTopology.Disk.SupBall`, a
diagonal affine map with positive coefficients and a positive radial rescaling:

* the coordinate sup-ball class (`TauCeti.coordinateSupBallClass`) of the closed unit ball of the
  sup norm on `Fin n → ℝ` modulo its unit sphere is the image of the cube class under the affine
  map `t ↦ (2 tⱼ - 1)ⱼ` (`TauCeti.cubeBoundaryPairIsoSupBall`);
* the coordinate disk class (`TauCeti.coordinateDiskClass`) of the Euclidean disk `(Dⁿ, Sⁿ⁻¹)` is
  the image of the sup-ball class under the inverse `x ↦ (‖x‖∞ / ‖x‖₂) x` of the radial rescaling
  (`TauCeti.diskBoundaryPairIsoSupBall`).

The composite of these two maps is the inverse of `TauCeti.diskBoundaryPairIsoCube`, so the disk
class is also the image of the cube class under it (`TauCeti.coordinateDiskClass_succ`). In
dimension `0` the cube, the sup-ball and the disk are points with empty boundary, and each class is
the class of the point (`TauCeti.coordinateSupBallClass_zero`, `TauCeti.coordinateDiskClass_zero`).

The **coordinate-disk comparison coefficient** is the value of the selected generator
`TauCeti.singularHomologyDiskBoundaryPairIso` of `Hₙ(Dⁿ, Sⁿ⁻¹; k)` on the coordinate disk class. It
is `(-1) ^ (n (n + 1) / 2)` in every dimension, in particular `1` in dimension `0`
(`TauCeti.singularHomologyDiskBoundaryPairIso_hom_coordinateDiskClass`), so it is a unit and the
coordinate classes generate (`TauCeti.bijective_smul_coordinateDiskClass`,
`TauCeti.bijective_smul_coordinateSupBallClass`). The coordinate classes orient the ball by its
coordinates alone, and the coefficient converts between them and the selected generator.

## Main definitions

* `TauCeti.coordinateSupBallClass k n`: the coordinate class in `Hₙ(B∞ⁿ, S∞ⁿ⁻¹; k)`.
* `TauCeti.coordinateDiskClass k n`: the coordinate class in `Hₙ(Dⁿ, Sⁿ⁻¹; k)`.

## Main results

* `TauCeti.coordinateDiskClass_succ`: the disk class is the image of the cube class.
* `TauCeti.singularHomologyDiskBoundaryPairIso_hom_coordinateDiskClass`: the comparison coefficient
  is `(-1) ^ (n (n + 1) / 2)`.
* `TauCeti.bijective_smul_coordinateDiskClass`: the coordinate disk class generates.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace TauCeti

/-! ### The coordinate classes -/

section Classes

variable (k : Type u) [Ring k]

/-- The **coordinate sup-ball class** in `Hₙ(B∞ⁿ, S∞ⁿ⁻¹; k)`: the image of the coordinate cube
class `TauCeti.coordinateCubeClass` under the affine homeomorphism `t ↦ (2 tⱼ - 1)ⱼ` of the cube
onto the sup-ball for `n ≥ 1`, and the class of the point for `n = 0`. -/
def coordinateSupBallClass : (n : ℕ) →
    (supBallBoundaryPair.{u} n).singularHomology (C := ModuleCat.{u} k) (ModuleCat.of k k) n
  | 0 => (singularHomology₀Section (ModuleCat.of k k)
        (ULift.up ⟨0, Metric.mem_closedBall_self zero_le_one⟩ : (supBallBoundaryPair.{u} 0).fst) ≫
      (supBallBoundaryPair.{u} 0).singularHomologyπ (ModuleCat.of k k) 0).hom 1
  | m + 1 => (TopPair.singularHomologyMap (cubeBoundaryPairIsoSupBall.{u} (m + 1)).hom
      (ModuleCat.of k k) (m + 1)).hom (coordinateCubeClass k m)

/-- In dimension `0` the coordinate sup-ball class is the class of the point. -/
theorem coordinateSupBallClass_zero (x : (supBallBoundaryPair.{u} 0).fst) :
    coordinateSupBallClass k 0 = (singularHomology₀Section (ModuleCat.of k k) x ≫
      (supBallBoundaryPair.{u} 0).singularHomologyπ (ModuleCat.of k k) 0).hom 1 := by
  obtain ⟨⟨y, hy⟩⟩ := x
  obtain rfl : y = 0 := Subsingleton.elim _ _
  rfl

/-- In positive dimension the coordinate sup-ball class is the image of the coordinate cube
class. -/
theorem coordinateSupBallClass_succ (m : ℕ) :
    coordinateSupBallClass k (m + 1) =
      (TopPair.singularHomologyMap (cubeBoundaryPairIsoSupBall.{u} (m + 1)).hom
        (ModuleCat.of k k) (m + 1)).hom (coordinateCubeClass k m) :=
  (rfl)

/-- The **coordinate disk class** in `Hₙ(Dⁿ, Sⁿ⁻¹; k)`: the image of the coordinate sup-ball class
under the homeomorphism `x ↦ (‖x‖∞ / ‖x‖₂) x` of the sup-ball onto the Euclidean disk. -/
def coordinateDiskClass (n : ℕ) :
    (diskBoundaryPair.{u} n).singularHomology (C := ModuleCat.{u} k) (ModuleCat.of k k) n :=
  (TopPair.singularHomologyMap (diskBoundaryPairIsoSupBall.{u} n).inv (ModuleCat.of k k) n).hom
    (coordinateSupBallClass k n)

theorem coordinateDiskClass_def (n : ℕ) :
    coordinateDiskClass k n =
      (TopPair.singularHomologyMap (diskBoundaryPairIsoSupBall.{u} n).inv
        (ModuleCat.of k k) n).hom (coordinateSupBallClass k n) :=
  (rfl)

/-- The radial rescaling of the disk onto the sup-ball carries the coordinate disk class to the
coordinate sup-ball class. -/
@[simp]
theorem singularHomologyMap_diskBoundaryPairIsoSupBall_hom_coordinateDiskClass (n : ℕ) :
    (TopPair.singularHomologyMap (diskBoundaryPairIsoSupBall.{u} n).hom
        (ModuleCat.of k k) n).hom (coordinateDiskClass k n) = coordinateSupBallClass k n := by
  rw [coordinateDiskClass_def, ← ModuleCat.comp_apply, ← TopPair.singularHomologyMap_comp,
    Iso.inv_hom_id, TopPair.singularHomologyMap_id, ModuleCat.id_apply]

/-- **The coordinate disk class is the image of the coordinate cube class** under the inverse of
the homeomorphism `TauCeti.diskHomeomorphCube` of the disk onto the cube. -/
theorem coordinateDiskClass_succ (m : ℕ) :
    coordinateDiskClass k (m + 1) =
      (TopPair.singularHomologyMap (diskBoundaryPairIsoCube.{u} (m + 1)).inv
        (ModuleCat.of k k) (m + 1)).hom (coordinateCubeClass k m) := by
  rw [coordinateDiskClass_def, coordinateSupBallClass_succ, ← ModuleCat.comp_apply,
    ← TopPair.singularHomologyMap_comp,
    cubeBoundaryPairIsoSupBall_hom_comp_diskBoundaryPairIsoSupBall_inv]

/-- In dimension `0` the coordinate disk class is the class of the centre of the disk. -/
theorem coordinateDiskClass_zero :
    coordinateDiskClass k 0 = (singularHomology₀Section (ModuleCat.of k k) (diskCenter.{u} 0) ≫
      (diskBoundaryPair.{u} 0).singularHomologyπ (ModuleCat.of k k) 0).hom 1 :=
  ConcreteCategory.congr_hom (TopPair.singularHomology₀Section_singularHomologyMap _
    (ModuleCat.of k k) (diskBoundaryPairIsoSupBall.{u} 0).inv _ _
      (Subsingleton.elim (α := TopCat.disk.{u} 0) _ _)) 1

/-- **The coordinate-disk comparison coefficient**: the selected generator
`TauCeti.singularHomologyDiskBoundaryPairIso` of `Hₙ(Dⁿ, Sⁿ⁻¹; k)` takes the value
`(-1) ^ (n (n + 1) / 2)` on the coordinate disk class, in particular `1` in dimension `0`. -/
theorem singularHomologyDiskBoundaryPairIso_hom_coordinateDiskClass (n : ℕ) :
    (singularHomologyDiskBoundaryPairIso (ModuleCat.of k k) n).hom (coordinateDiskClass k n) =
      (-1 : k) ^ (n * (n + 1) / 2) := by
  cases n with
  | zero =>
    rw [coordinateDiskClass_zero, ← singularHomologyDiskBoundaryPairIso_zero_inv,
      ModuleCat.hom_inv_apply]
    simp
  | succ m =>
    rw [← singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass,
      coordinateDiskClass_succ, singularHomologyCubeBoundaryPairIso_hom, ModuleCat.comp_apply]

/-- The coordinate-disk comparison coefficient is a unit. -/
theorem isUnit_singularHomologyDiskBoundaryPairIso_hom_coordinateDiskClass (n : ℕ) :
    IsUnit ((singularHomologyDiskBoundaryPairIso (ModuleCat.of k k) n).hom
      (coordinateDiskClass k n)) := by
  rw [singularHomologyDiskBoundaryPairIso_hom_coordinateDiskClass]
  exact isUnit_neg_one.pow _

/-- **The coordinate disk class generates**: `a ↦ a • [Dⁿ, Sⁿ⁻¹]` is a bijection from `k` onto
`Hₙ(Dⁿ, Sⁿ⁻¹; k)`. -/
theorem bijective_smul_coordinateDiskClass (n : ℕ) :
    Function.Bijective fun a : k ↦ a • coordinateDiskClass k n := by
  have hε : ((-1 : k) ^ (n * (n + 1) / 2)) * (-1) ^ (n * (n + 1) / 2) = 1 :=
    neg_one_pow_mul_neg_one_pow _
  have he : (singularHomologyDiskBoundaryPairIso (ModuleCat.of k k) n).hom ∘
      (fun a : k ↦ a • coordinateDiskClass k n) = Units.mulRight ⟨_, _, hε, hε⟩ := by
    ext a
    rw [Function.comp_apply, map_smul,
      singularHomologyDiskBoundaryPairIso_hom_coordinateDiskClass, Units.mulRight_apply,
      Units.val_mk, smul_eq_mul]
  exact (Function.Bijective.of_comp_iff'
    (singularHomologyDiskBoundaryPairIso (ModuleCat.of k k) n).toLinearEquiv.bijective _).1
    (he ▸ (Units.mulRight _).bijective)

/-- **The coordinate sup-ball class generates**: `a ↦ a • [B∞ⁿ, S∞ⁿ⁻¹]` is a bijection from `k`
onto `Hₙ(B∞ⁿ, S∞ⁿ⁻¹; k)`. -/
theorem bijective_smul_coordinateSupBallClass (n : ℕ) :
    Function.Bijective fun a : k ↦ a • coordinateSupBallClass k n := by
  set f := TopPair.singularHomologyMapIso (ModuleCat.of k k) (diskBoundaryPairIsoSupBall.{u} n) n
  have hf : (fun a : k ↦ a • coordinateSupBallClass k n) =
      f.hom ∘ fun a : k ↦ a • coordinateDiskClass k n := by
    ext a
    simp [f, map_smul]
  exact hf ▸ f.toLinearEquiv.bijective.comp (bijective_smul_coordinateDiskClass k n)

end Classes

end TauCeti

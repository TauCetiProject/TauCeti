/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Triangulation.Comparison
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Cube.Generator
public import TauCeti.AlgebraicTopology.Disk.SupBall

import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.Algebra.Ring.Parity

/-!
# The coordinate cube, disk and sup-ball classes

The positive ordered triangulation `TauCeti.SingularCube.orderedChain` of the identity cube of
`Iⁿ` is a relative singular cycle of the pair `(Iⁿ, ∂Iⁿ)`. With integer coefficients it is the
`n`-fold iterated shuffle product of the interval chain `t ↦ t` taken in coordinate order
(`TauCeti.iteratedIntegralShuffle_eq_orderedChain`), so its class is the coordinate-oriented
fundamental class of the cube. This file computes that class: it is `(-1) ^ (n (n + 1) / 2)` times
the selected generator `TauCeti.singularHomologyCubeBoundaryPairIso` of `Hₙ(Iⁿ, ∂Iⁿ; k)`, over
every ring `k` (`TauCeti.singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass`). In
particular it generates `Hₙ(Iⁿ, ∂Iⁿ; k)` (`TauCeti.bijective_smul_coordinateCubeClass`), and in
dimension one it is the class of `t ↦ t`, whose boundary is `[1] - [0]`
(`TauCeti.coordinateCubeClass_zero`).

The computation compares the triangulation with the acyclic-models comparison
`TauCeti.cubicalToSingular`, whose value on the identity cube is calibrated in
`TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Cube.Generator`: by
`TopPair.singularCubicalHomologyIso_inv_homologyπ_cubicalCycleOfCube` the coordinate cube class
is `(-1) ^ n` times the image of the cubical class of the identity cube.

The cube is identified with the closed unit ball of the sup norm by the affine map
`t ↦ 2t - 1` (`TauCeti.cubeBoundaryPairIsoSupBall`), and that ball with the Euclidean disk by a
radial rescaling (`TauCeti.diskBoundaryPairIsoSupBall`). Both maps rescale every coordinate
direction positively, and they transport the coordinate cube class to the coordinate sup-ball
class `[Bⁿ_∞, ∂Bⁿ_∞]` and the coordinate disk class `[Dⁿ, Sⁿ⁻¹]`; in dimension zero these are the
classes of the point. The sup-ball is the domain of the characteristic maps of the cells of a CW
complex. The **coordinate-disk comparison
coefficient**, the value of the selected generator `TauCeti.singularHomologyDiskBoundaryPairIso`
of `Hₙ(Dⁿ, Sⁿ⁻¹; k)` on the disk class, is the unit `(-1) ^ (n (n + 1) / 2)`, and `1` in dimension
zero (`TauCeti.singularHomologyDiskBoundaryPairIso_hom_coordinateDiskClass`).

## Main definitions

* `TauCeti.coordinateCubeClass k m`: the coordinate cube class in `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; k)`.
* `TauCeti.coordinateDiskClass k n`: the coordinate disk class in `Hₙ(Dⁿ, Sⁿ⁻¹; k)`.
* `TauCeti.coordinateSupBallClass k n`: the coordinate sup-ball class in `Hₙ(Bⁿ_∞, ∂Bⁿ_∞; k)`.

## Main results

* `TauCeti.singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass`: the coordinate of the
  cube class is `(-1) ^ ((m + 1) (m + 2) / 2)`.
* `TauCeti.bijective_smul_coordinateCubeClass`: the coordinate cube class generates.
* `TauCeti.singularHomologyDiskBoundaryPairIso_hom_coordinateDiskClass`: the coordinate-disk
  comparison coefficient is `(-1) ^ (n (n + 1) / 2)`.
* `TauCeti.bijective_smul_coordinateDiskClass`, `TauCeti.bijective_smul_coordinateSupBallClass`:
  the disk and sup-ball classes generate.
* `TauCeti.singularHomologyMap_diskBoundaryPairToCube_coordinateDiskClass`,
  `TauCeti.coordinateSupBallClass_succ` and their inverse forms: the three classes correspond
  under the identifications of the three pairs.

## References

* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
* A. Hatcher, *Algebraic Topology*, Proposition 3B.1 and the relative cross product after
  Theorem 3B.6.
-/

public section

noncomputable section

open CategoryTheory Limits Set

universe u

namespace TauCeti

variable (k : Type u) [Ring k]

/-! ### The coordinate cube class -/

/-- The **coordinate cube class** `[Iᵐ⁺¹, ∂Iᵐ⁺¹]` in `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; k)`: the class of the
positive ordered triangulation of the identity cube, the signed sum over the coordinate orderings
of the simplices from the origin to the far vertex. With integer coefficients its chain is the
iterated shuffle product of the interval chain `t ↦ t` in coordinate order
(`TauCeti.iteratedIntegralShuffle_eq_orderedChain`). -/
def coordinateCubeClass (m : ℕ) :
    (cubeBoundaryPair.{u} (m + 1)).singularHomology (C := ModuleCat.{u} k) (ModuleCat.of k k)
      (m + 1) :=
  ((cubeBoundaryPair.{u} (m + 1)).singularChainComplex (ModuleCat.of k k)).homologyπ (m + 1)
    (TopPair.orderedCycleOfCube k
      (upCube.{u} (m + 1) : SingularCube (cubeBoundaryPair.{u} (m + 1)).fst (m + 1))
      (mapsTo_upCube_boundary (m + 1)))

theorem coordinateCubeClass_def (m : ℕ) :
    coordinateCubeClass k m =
      ((cubeBoundaryPair.{u} (m + 1)).singularChainComplex (ModuleCat.of k k)).homologyπ (m + 1)
        (TopPair.orderedCycleOfCube k
          (upCube.{u} (m + 1) : SingularCube (cubeBoundaryPair.{u} (m + 1)).fst (m + 1))
          (mapsTo_upCube_boundary (m + 1))) :=
  (rfl)

/-- The coordinate cube class is `(-1) ^ (m + 1)` times the cubical class of the identity cube. -/
theorem coordinateCubeClass_eq_neg_one_pow_smul (m : ℕ) :
    coordinateCubeClass k m =
      (-1 : k) ^ (m + 1) • (TopPair.singularCubicalHomologyIso k (cubeBoundaryPair.{u} (m + 1))
        (m + 1)).inv (((cubeBoundaryPair.{u} (m + 1)).cubicalChainComplex k).homologyπ (m + 1)
          (cubeBoundaryPairCycle k m)) := by
  have hz : cubeBoundaryPairCycle k m = TopPair.cubicalCycleOfCube k
      (upCube.{u} (m + 1) : SingularCube (cubeBoundaryPair.{u} (m + 1)).fst (m + 1))
      (mapsTo_upCube_boundary (m + 1)) :=
    HomologicalComplex.moduleCat_iCycles_injective _ (m + 1)
      ((iCycles_cubeBoundaryPairCycle k m).trans (TopPair.iCycles_cubicalCycleOfCube ..).symm)
  have h := congrArg ((-1 : k) ^ (m + 1) • ·)
    (TopPair.singularCubicalHomologyIso_inv_homologyπ_cubicalCycleOfCube (k := k)
      (P := cubeBoundaryPair.{u} (m + 1)) _ (mapsTo_upCube_boundary (m + 1)))
  rw [hz]
  -- The ambient space of the cube pair is the cube model only up to unfolding `Arrow.mk`, so the
  -- relative formula is combined with equations rather than rewritten.
  exact (h.trans ((smul_smul _ _ _).trans
    ((congrArg (fun a : k ↦ a • coordinateCubeClass k m)
      (neg_one_pow_mul_neg_one_pow (m + 1))).trans (one_smul k _)))).symm

/-- **The coordinate of the cube class**: under `TauCeti.singularHomologyCubeBoundaryPairIso`, the
coordinate cube class of `Iⁿ`, `n = m + 1`, is `(-1) ^ (n (n + 1) / 2)`. -/
theorem singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass (m : ℕ) :
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (m + 1)).hom (coordinateCubeClass k m) =
      (-1 : k) ^ ((m + 1) * (m + 2) / 2) := by
  rw [coordinateCubeClass_eq_neg_one_pow_smul, map_smul,
    singularHomologyCubeBoundaryPairIso_hom_cubeBoundaryPairCycle, smul_eq_mul, ← pow_add]
  congr 1
  have h : (m + 1) * (m + 2) = m * (m + 1) + 2 * (m + 1) := by ring
  rw [h, Nat.add_mul_div_left _ _ two_pos, add_comm]

/-- The selected generator of `Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; k)` is `(-1) ^ ((m + 1) (m + 2) / 2)` times the
coordinate cube class. -/
theorem singularHomologyCubeBoundaryPairIso_inv_apply_one (m : ℕ) :
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (m + 1)).inv (1 : k) =
      (-1 : k) ^ ((m + 1) * (m + 2) / 2) • coordinateCubeClass k m := by
  apply (ModuleCat.mono_iff_injective
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (m + 1)).hom).1 inferInstance
  rw [ModuleCat.hom_inv_apply, map_smul,
    singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass, smul_eq_mul,
    neg_one_pow_mul_neg_one_pow]

/-- **The coordinate cube class generates**: `a ↦ a • [Iᵐ⁺¹, ∂Iᵐ⁺¹]` is a bijection from `k` onto
`Hₘ₊₁(Iᵐ⁺¹, ∂Iᵐ⁺¹; k)`. -/
theorem bijective_smul_coordinateCubeClass (m : ℕ) :
    Function.Bijective fun a : k ↦ a • coordinateCubeClass k m :=
  (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) (m + 1)).toLinearEquiv
    |>.bijective_smul_of_isUnit_apply <| by
      rw [Iso.toLinearEquiv_apply, singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass]
      exact isUnit_neg_one.pow _

/-- In dimension one the coordinate cube class is the class of the singular simplex `t ↦ t`, whose
boundary is `[1] - [0]` (`TauCeti.cubeRelClass_singularHomologyδ`). -/
theorem coordinateCubeClass_zero :
    coordinateCubeClass k 0 = (cubeRelClass.{u} (ModuleCat.of k k)).hom (1 : k) := by
  apply (ModuleCat.mono_iff_injective
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) 1).hom).1 inferInstance
  have h := congrArg (fun φ ↦ ((singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) 1).hom)
    (φ.hom (1 : k))) (singularHomologyCubeBoundaryPairIso_one_inv (ModuleCat.of k k))
  simp only [ModuleCat.hom_neg, LinearMap.neg_apply, map_neg] at h
  rw [singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass, ← neg_eq_iff_eq_neg.2 h]
  norm_num

/-! ### The coordinate disk and sup-ball classes -/

/-- The **coordinate disk class** `[Dⁿ, Sⁿ⁻¹]` in `Hₙ(Dⁿ, Sⁿ⁻¹; k)`. For `n ≥ 1` it is the image
of the coordinate cube class `TauCeti.coordinateCubeClass` under the inverse of the disk-to-cube
isomorphism `TauCeti.diskBoundaryPairIsoCube`, whose radial and diagonal factors are positive
rescalings, so the class carries the ordered coordinate orientation
(`TauCeti.coordinateDiskClass_succ`). For `n = 0` the disk is a point with empty boundary, and the
class is the class of that point (`TauCeti.coordinateDiskClass_zero`). -/
def coordinateDiskClass :
    (n : ℕ) → (diskBoundaryPair.{u} n).singularHomology (C := ModuleCat.{u} k) (ModuleCat.of k k) n
  | 0 => ((diskBoundaryPair.{u} 0).singularHomologyπ (ModuleCat.of k k) 0).hom
      ((singularHomology₀Section (ModuleCat.of k k) (diskCenter.{u} 0)).hom 1)
  | m + 1 => (TopPair.singularHomologyMap (diskBoundaryPairIsoCube.{u} (m + 1)).inv
      (ModuleCat.of k k) (m + 1)).hom (coordinateCubeClass k m)

/-- The coordinate disk class of the `0`-disk is the class of its point. -/
theorem coordinateDiskClass_zero :
    coordinateDiskClass k 0 = ((diskBoundaryPair.{u} 0).singularHomologyπ (ModuleCat.of k k) 0).hom
      ((singularHomology₀Section (ModuleCat.of k k) (diskCenter.{u} 0)).hom 1) :=
  (rfl)

/-- In positive dimension, the coordinate disk class is the image of the coordinate cube class
under the inverse of `TauCeti.diskBoundaryPairIsoCube`. -/
theorem coordinateDiskClass_succ (m : ℕ) :
    coordinateDiskClass k (m + 1) = (TopPair.singularHomologyMap
      (diskBoundaryPairIsoCube.{u} (m + 1)).inv (ModuleCat.of k k) (m + 1)).hom
        (coordinateCubeClass k m) :=
  (rfl)

/-- The disk-to-cube homeomorphism `TauCeti.diskBoundaryPairToCube` carries the coordinate disk
class to the coordinate cube class. -/
@[simp]
theorem singularHomologyMap_diskBoundaryPairToCube_coordinateDiskClass (m : ℕ) :
    (TopPair.singularHomologyMap (diskBoundaryPairToCube.{u} (m + 1)) (ModuleCat.of k k)
      (m + 1)).hom (coordinateDiskClass k (m + 1)) = coordinateCubeClass k m := by
  rw [coordinateDiskClass_succ, ← ModuleCat.comp_apply, ← diskBoundaryPairIsoCube_hom,
    ← TopPair.singularHomologyMap_comp,
    Iso.inv_hom_id, TopPair.singularHomologyMap_id, ModuleCat.id_apply]

/-- **The coordinate-disk comparison coefficient**: under the selected identification
`TauCeti.singularHomologyDiskBoundaryPairIso` of `Hₙ(Dⁿ, Sⁿ⁻¹; k)` with `k`, the coordinate disk
class is the unit `(-1) ^ (n (n + 1) / 2)`. In dimension zero it is `1`: the identification is the
augmentation, which sends the class of a point to `1`. -/
theorem singularHomologyDiskBoundaryPairIso_hom_coordinateDiskClass (n : ℕ) :
    (singularHomologyDiskBoundaryPairIso (ModuleCat.of k k) n).hom (coordinateDiskClass k n) =
      (-1 : k) ^ (n * (n + 1) / 2) := by
  cases n with
  | zero =>
    have h : coordinateDiskClass k 0 =
        (singularHomologyDiskBoundaryPairIso (ModuleCat.of k k) 0).inv (1 : k) := by
      rw [singularHomologyDiskBoundaryPairIso_zero_inv, coordinateDiskClass_zero]
      -- The composite is type-correct only up to unfolding the relative homology of `D⁰`.
      exact (ModuleCat.comp_apply _ _ _).symm
    rw [h, Iso.inv_hom_id_apply]
    norm_num
  | succ m =>
    rw [coordinateDiskClass_succ, ← ModuleCat.comp_apply,
      ← singularHomologyCubeBoundaryPairIso_hom,
      singularHomologyCubeBoundaryPairIso_hom_coordinateCubeClass]

/-- The selected generator of `Hₙ(Dⁿ, Sⁿ⁻¹; k)` is `(-1) ^ (n (n + 1) / 2)` times the coordinate
disk class. -/
theorem singularHomologyDiskBoundaryPairIso_inv_apply_one (n : ℕ) :
    (singularHomologyDiskBoundaryPairIso (ModuleCat.of k k) n).inv (1 : k) =
      (-1 : k) ^ (n * (n + 1) / 2) • coordinateDiskClass k n := by
  apply (ModuleCat.mono_iff_injective
    (singularHomologyDiskBoundaryPairIso (ModuleCat.of k k) n).hom).1 inferInstance
  rw [ModuleCat.hom_inv_apply, map_smul,
    singularHomologyDiskBoundaryPairIso_hom_coordinateDiskClass, smul_eq_mul,
    neg_one_pow_mul_neg_one_pow]

/-- **The coordinate disk class generates**: `a ↦ a • [Dⁿ, Sⁿ⁻¹]` is a bijection from `k` onto
`Hₙ(Dⁿ, Sⁿ⁻¹; k)`. -/
theorem bijective_smul_coordinateDiskClass (n : ℕ) :
    Function.Bijective fun a : k ↦ a • coordinateDiskClass k n :=
  (singularHomologyDiskBoundaryPairIso (ModuleCat.of k k) n).toLinearEquiv
    |>.bijective_smul_of_isUnit_apply <| by
      rw [Iso.toLinearEquiv_apply, singularHomologyDiskBoundaryPairIso_hom_coordinateDiskClass]
      exact isUnit_neg_one.pow _

/-- The **coordinate sup-ball class** `[Bⁿ_∞, ∂Bⁿ_∞]` in the relative homology of the closed unit
ball of the sup norm on `Fin n → ℝ` modulo its unit sphere: the image of the coordinate disk class
under the radial identification `TauCeti.diskBoundaryPairIsoSupBall`. For `n ≥ 1` it is also the
image of the coordinate cube class under the affine identification
`TauCeti.cubeBoundaryPairIsoSupBall` (`TauCeti.coordinateSupBallClass_succ`). -/
def coordinateSupBallClass (n : ℕ) :
    (supBallPair.{u} n).singularHomology (C := ModuleCat.{u} k) (ModuleCat.of k k) n :=
  (TopPair.singularHomologyMap (diskBoundaryPairIsoSupBall.{u} n).hom (ModuleCat.of k k) n).hom
    (coordinateDiskClass k n)

/-- The coordinate sup-ball class is the image of the coordinate disk class under the radial
identification `TauCeti.diskBoundaryPairIsoSupBall`. -/
theorem coordinateSupBallClass_def (n : ℕ) :
    coordinateSupBallClass k n =
      (TopPair.singularHomologyMap (diskBoundaryPairIsoSupBall.{u} n).hom (ModuleCat.of k k)
        n).hom (coordinateDiskClass k n) :=
  (rfl)

/-- In positive dimension, the coordinate sup-ball class is the image of the coordinate cube class
under the affine identification `TauCeti.cubeBoundaryPairIsoSupBall`. -/
theorem coordinateSupBallClass_succ (m : ℕ) :
    coordinateSupBallClass k (m + 1) = (TopPair.singularHomologyMap
      (cubeBoundaryPairIsoSupBall.{u} (m + 1)).hom (ModuleCat.of k k) (m + 1)).hom
        (coordinateCubeClass k m) := by
  rw [coordinateSupBallClass_def, diskBoundaryPairIsoSupBall_hom,
    TopPair.singularHomologyMap_comp, ModuleCat.comp_apply, diskBoundaryPairIsoCube_hom,
    singularHomologyMap_diskBoundaryPairToCube_coordinateDiskClass]

/-- The inverse of the radial identification `TauCeti.diskBoundaryPairIsoSupBall` carries the
coordinate sup-ball class to the coordinate disk class. -/
@[simp]
theorem singularHomologyMap_diskBoundaryPairIsoSupBall_inv_coordinateSupBallClass (n : ℕ) :
    (TopPair.singularHomologyMap (diskBoundaryPairIsoSupBall.{u} n).inv (ModuleCat.of k k) n).hom
      (coordinateSupBallClass k n) = coordinateDiskClass k n := by
  rw [coordinateSupBallClass_def, ← ModuleCat.comp_apply, ← TopPair.singularHomologyMap_comp,
    Iso.hom_inv_id, TopPair.singularHomologyMap_id, ModuleCat.id_apply]

/-- The inverse of the affine identification `TauCeti.cubeBoundaryPairIsoSupBall` carries the
coordinate sup-ball class to the coordinate cube class. -/
@[simp]
theorem singularHomologyMap_cubeBoundaryPairIsoSupBall_inv_coordinateSupBallClass (m : ℕ) :
    (TopPair.singularHomologyMap (cubeBoundaryPairIsoSupBall.{u} (m + 1)).inv (ModuleCat.of k k)
      (m + 1)).hom (coordinateSupBallClass k (m + 1)) = coordinateCubeClass k m := by
  rw [coordinateSupBallClass_succ, ← ModuleCat.comp_apply, ← TopPair.singularHomologyMap_comp,
    Iso.hom_inv_id, TopPair.singularHomologyMap_id, ModuleCat.id_apply]

/-- **The coordinate sup-ball class generates**: `a ↦ a • [Bⁿ_∞, ∂Bⁿ_∞]` is a bijection from `k`
onto the relative homology of the sup-norm ball modulo its boundary sphere in degree `n`. -/
theorem bijective_smul_coordinateSupBallClass (n : ℕ) :
    Function.Bijective fun a : k ↦ a • coordinateSupBallClass k n := by
  let e := TopPair.singularHomologyMapIso (ModuleCat.of k k) (diskBoundaryPairIsoSupBall.{u} n) n
  have h : (fun a : k ↦ a • coordinateSupBallClass k n) =
      e.hom.hom ∘ fun a : k ↦ a • coordinateDiskClass k n := by
    ext a
    simp [e, coordinateSupBallClass_def]
  rw [h]
  exact e.toLinearEquiv.bijective.comp (bijective_smul_coordinateDiskClass k n)

end TauCeti

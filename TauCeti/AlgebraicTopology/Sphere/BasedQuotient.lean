/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.AlgebraicTopology.Sphere.CubeQuotient
public import TauCeti.Topology.Category.TopPair.Quotient
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.AlgebraicTopology.Sphere.Zero

/-!
# Based sphere quotients of disks and cubes

This file equips the native sphere `TopCat.sphere n` with its positive first-coordinate basepoint
`TauCeti.sphereBasepoint n` (`e₀`) and antipode `TauCeti.sphereAntiBasepoint n` (`-e₀`), and
constructs the canonical pointed homeomorphisms identifying both the cube quotient
`(TauCeti.cubeBoundaryPair n).ordinaryPairQuotient` and the disk quotient
`(TauCeti.diskBoundaryPair n).ordinaryPairQuotient` with `TopCat.sphere n` in every dimension
`n ≥ 0`.

`TauCeti.cubeToSphere` and `TauCeti.closedBallToSphere` land on the unit sphere with north pole
`e_last`. To move `e_last` to `e₀` while preserving positive orientation in every positive
dimension, `TauCeti.spherePoleLinearIsometry n` applies the linear isometry
`(x₀, x₁, …, xₙ) ↦ (xₙ, -x₀, x₁, …, xₙ₋₁)` for `n ≥ 1` (of determinant `(-1) ^ (n + 1)`) and the
identity for `n = 0`. In dimension `0`, the unique point of `D⁰` and `I⁰` goes to `-e₀` and the
collapsed empty boundary (the added basepoint of `D⁰₊` and `I⁰₊`) goes to `e₀`.

## Main declarations

* `TauCeti.sphereBasepoint`, `TauCeti.sphereAntiBasepoint`: the positive and negative
  first-coordinate poles `±e₀` of `TopCat.sphere n`.
* `TauCeti.spherePoleLinearIsometry`: the coordinate linear isometry moving `e_last` to `e₀`, with
  `TauCeti.det_spherePoleLinearIsometry`.
* `TauCeti.basedCubeToSphere`, `TauCeti.basedDiskToSphere`: the based collapse maps `Iⁿ → Sⁿ` and
  `Dⁿ ⟶ Sⁿ` sending the boundary to `sphereBasepoint n` and the centre to `sphereAntiBasepoint n`.
* `TauCeti.cubeQuotientSphereHomeomorph`: the pointed homeomorphism `Iⁿ / ∂Iⁿ ≃ₜ Sⁿ` for all `n`.
* `TauCeti.diskQuotientSphereHomeomorph`: the pointed homeomorphism `Dⁿ / ∂Dⁿ ≃ₜ Sⁿ` for all `n`,
  compatible with `TauCeti.diskBoundaryPairIsoCube`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 and Section 2.1.
-/

public section

noncomputable section

open CategoryTheory Metric Set Topology
open scoped unitInterval

universe u

namespace TauCeti.TopCat

/-- The `n`-sphere `TopCat.sphere n` is compact. -/
instance compactSpace_sphere (n : ℕ) : CompactSpace (TopCat.sphere.{u} n) :=
  inferInstanceAs (CompactSpace (TopCat.diskBoundary.{u} (n + 1)))

/-- The `n`-sphere `TopCat.sphere n` is Hausdorff. -/
instance t2Space_sphere (n : ℕ) : T2Space (TopCat.sphere.{u} n) :=
  TauCeti.t2Space_diskBoundary (n + 1)

/-- The `0`-sphere `TopCat.sphere 0` is finite. -/
instance finite_sphere_zero : Finite (TopCat.sphere.{u} 0) :=
  have : Finite (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
    TauCeti.finite_sphere_of_finrank_eq_one finrank_euclideanSpace_fin 0 1
  Equiv.ulift.finite_iff.2 inferInstance

/-- The `0`-sphere `TopCat.sphere 0` has the discrete topology. -/
instance discreteTopology_sphere_zero : DiscreteTopology (TopCat.sphere.{u} 0) :=
  Finite.instDiscreteTopology

end TauCeti.TopCat

namespace TauCeti

/-! ### Basepoint and antipode of `TopCat.sphere n` -/

/-- The positive first-coordinate pole `e₀` of `TopCat.sphere n`. -/
def sphereBasepoint (n : ℕ) : TopCat.sphere.{u} n :=
  (ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩ :
    ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))

@[simp]
lemma coe_sphereBasepoint_down (n : ℕ) :
    (((sphereBasepoint.{u} n : TopCat.sphere.{u} n) :
      ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).down :
        EuclideanSpace ℝ (Fin (n + 1))) = EuclideanSpace.single 0 1 := (rfl)

/-- The negative first-coordinate pole `-e₀` of `TopCat.sphere n`, antipodal to
`TauCeti.sphereBasepoint`. -/
def sphereAntiBasepoint (n : ℕ) : TopCat.sphere.{u} n :=
  diskBoundaryNeg (n + 1) (sphereBasepoint n)

@[simp]
lemma coe_sphereAntiBasepoint_down (n : ℕ) :
    (((sphereAntiBasepoint.{u} n : TopCat.sphere.{u} n) :
      ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).down :
        EuclideanSpace ℝ (Fin (n + 1))) = -EuclideanSpace.single 0 1 :=
  congrArg Subtype.val (diskBoundaryNeg_apply_down (sphereBasepoint.{u} n))

/-- The basepoint `e₀` and its antipode `-e₀` on `TopCat.sphere n` are distinct. -/
lemma sphereBasepoint_ne_sphereAntiBasepoint (n : ℕ) :
    sphereBasepoint.{u} n ≠ sphereAntiBasepoint.{u} n := by
  intro h
  have h0 := congrArg (fun s : TopCat.sphere.{u} n ↦
    (((s : ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).down :
      EuclideanSpace ℝ (Fin (n + 1))) 0)) h
  simp only [coe_sphereBasepoint_down, coe_sphereAntiBasepoint_down, PiLp.neg_apply,
    PiLp.single_apply, ↓reduceIte] at h0
  norm_num at h0

/-- Every point of `TopCat.sphere 0` is either `sphereBasepoint 0` or `sphereAntiBasepoint 0`. -/
lemma eq_sphereBasepoint_or_eq_sphereAntiBasepoint (s : TopCat.sphere.{u} 0) :
    s = sphereBasepoint.{u} 0 ∨ s = sphereAntiBasepoint.{u} 0 := by
  have hp : (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) ∈
      sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by simp
  have hs : (((s : ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)).down :
      EuclideanSpace ℝ (Fin 1))) ∈
      ({EuclideanSpace.single 0 1, -EuclideanSpace.single 0 1} :
        Set (EuclideanSpace ℝ (Fin 1))) := by
    rw [← sphere_eq_pair_of_finrank_eq_one finrank_euclideanSpace_fin hp]
    exact (s : ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin 1)) 1)).down.2
  rcases mem_insert_iff.1 hs with hs | hs
  · exact Or.inl (ULift.ext (Subtype.ext hs))
  · exact Or.inr (ULift.ext (Subtype.ext
      ((mem_singleton_iff.1 hs).trans (coe_sphereAntiBasepoint_down 0).symm)))

/-! ### The pole-normalizing linear isometry -/

/-- The coordinate linear isometry of `ℝⁿ⁺¹` moving `e_last` to `e₀`: the identity for `n = 0`,
and `(x₀, x₁, …, xₙ) ↦ (xₙ, -x₀, x₁, …, xₙ₋₁)` for `n ≥ 1`. -/
def spherePoleLinearIsometry (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (LinearIsometryEquiv.piLpCongrRight 2 fun i : Fin (n + 1) ↦
    if i = 0 ∧ n ≠ 0 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finRotate (n + 1)))

@[simp]
lemma spherePoleLinearIsometry_zero :
    spherePoleLinearIsometry 0 = LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 1)) := by
  ext x i
  rw [Fin.eq_zero i]
  simp [spherePoleLinearIsometry]

@[simp]
lemma spherePoleLinearIsometry_apply_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    spherePoleLinearIsometry n x 0 = x (Fin.last n) := by
  have hrot : (finRotate (n + 1)).symm 0 = Fin.last n :=
    (finRotate (n + 1)).symm_apply_eq.2 finRotate_last.symm
  simp only [spherePoleLinearIsometry, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', Equiv.coe_fn_mk]
  rw [hrot]
  simp

@[simp]
lemma spherePoleLinearIsometry_succ_apply_one (m : ℕ) (x : EuclideanSpace ℝ (Fin (m + 2))) :
    spherePoleLinearIsometry (m + 1) x 1 = -x 0 := by
  have hrot : (finRotate (m + 2)).symm 1 = 0 :=
    (finRotate (m + 2)).symm_apply_eq.2 finRotate_apply_zero.symm
  simp only [spherePoleLinearIsometry, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', Equiv.coe_fn_mk]
  rw [hrot]
  simp

@[simp]
lemma spherePoleLinearIsometry_succ_apply_succ_succ (m : ℕ) (x : EuclideanSpace ℝ (Fin (m + 2)))
    (j : Fin m) :
    spherePoleLinearIsometry (m + 1) x j.succ.succ = x j.succ.castSucc := by
  have hrot : (finRotate (m + 2)).symm j.succ.succ = j.succ.castSucc :=
    (finRotate (m + 2)).symm_apply_eq.2 (finRotate_of_lt (Nat.succ_lt_succ j.isLt)).symm
  simp only [spherePoleLinearIsometry, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', Equiv.coe_fn_mk]
  rw [hrot]
  simp

@[simp]
lemma spherePoleLinearIsometry_single_last (n : ℕ) (r : ℝ) :
    spherePoleLinearIsometry n (EuclideanSpace.single (Fin.last n) r) =
      EuclideanSpace.single 0 r := by
  rw [spherePoleLinearIsometry, LinearIsometryEquiv.trans_apply]
  have h1 : (LinearIsometryEquiv.piLpCongrRight 2 fun i : Fin (n + 1) ↦
      if i = 0 ∧ n ≠ 0 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
      (EuclideanSpace.single (Fin.last n) r) = EuclideanSpace.single (Fin.last n) r := by
    simp [EuclideanSpace.single]
  rw [h1, EuclideanSpace.piLpCongrLeft_single, finRotate_last]

lemma spherePoleLinearIsometry_sphereNorthPole (n : ℕ) :
    spherePoleLinearIsometry n (sphereNorthPole n) = EuclideanSpace.single 0 1 :=
  (congrArg (spherePoleLinearIsometry n) (coe_sphereNorthPole n)).trans
    (spherePoleLinearIsometry_single_last n 1)

lemma det_spherePoleLinearIsometry_zero :
    LinearMap.det (spherePoleLinearIsometry 0).toLinearMap = 1 := by
  simp

/-- In positive dimension `n ≥ 1`, `TauCeti.spherePoleLinearIsometry n` has determinant
`(-1) ^ (n + 1)`. -/
lemma det_spherePoleLinearIsometry (n : ℕ) [NeZero n] :
    LinearMap.det (spherePoleLinearIsometry n).toLinearMap = (-1 : ℝ) ^ (n + 1) := by
  have hn : n ≠ 0 := NeZero.ne n
  let b := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  let M := Matrix.diagonal fun k : Fin (n + 1) ↦ if k = 0 then (-1 : ℝ) else 1
  rw [← LinearMap.det_toMatrix b]
  have hM : LinearMap.toMatrix b b (spherePoleLinearIsometry n).toLinearMap =
      M.submatrix (finRotate (n + 1)).symm id := by
    ext i j
    rw [Matrix.submatrix_apply, id_eq]
    rcases eq_or_ne i (finRotate (n + 1) j) with rfl | hi
    · rw [Equiv.symm_apply_apply]
      by_cases hj : j = 0 <;>
        simp [b, M, spherePoleLinearIsometry, hn, hj, LinearMap.toMatrix_apply,
          EuclideanSpace.basisFun_apply]
    · have hij : (finRotate (n + 1)).symm i ≠ j := mt (finRotate (n + 1)).symm_apply_eq.mp hi
      simp_all [b, M, spherePoleLinearIsometry, LinearMap.toMatrix_apply,
        EuclideanSpace.basisFun_apply]
  have hsign : Equiv.Perm.sign (finRotate (n + 1)).symm = (-1) ^ n := by
    rw [← Equiv.Perm.inv_def, map_inv, Int.units_inv_eq_self, sign_finRotate, Nat.add_sub_cancel]
  rw [hM, Matrix.det_permute, hsign, Matrix.det_diagonal, Fin.prod_univ_succ]
  simp
  ring

/-! ### Based collapse maps from cubes and disks -/

/-- The based cube-to-sphere collapse map `Iⁿ → TopCat.sphere n`, sending `∂Iⁿ` to
`TauCeti.sphereBasepoint n` (`e₀`) and the centre of the cube to `TauCeti.sphereAntiBasepoint n`
(`-e₀`). -/
def basedCubeToSphere (n : ℕ) : C(I^(Fin n), TopCat.sphere.{u} n) :=
  ((spherePoleLinearIsometry n).diskBoundaryIso.{u}.hom).hom.comp
    ⟨fun y ↦ (ULift.up (cubeToSphere n y) : TopCat.sphere.{u} n),
      continuous_uliftUp.comp (cubeToSphere n).continuous⟩

@[simp]
lemma coe_basedCubeToSphere_down (n : ℕ) (y : I^(Fin n)) :
    (((basedCubeToSphere.{u} n y : TopCat.sphere.{u} n) :
      ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).down :
        EuclideanSpace ℝ (Fin (n + 1))) = spherePoleLinearIsometry n (cubeToSphere n y) :=
  (spherePoleLinearIsometry n).coe_diskBoundaryIso_hom_apply_down (ULift.up (cubeToSphere n y))

/-- `TauCeti.basedCubeToSphere` sends a point of `Iⁿ` to `sphereBasepoint n` iff it lies in
`∂Iⁿ`. -/
@[simp]
lemma basedCubeToSphere_eq_sphereBasepoint_iff {n : ℕ} {y : I^(Fin n)} :
    basedCubeToSphere.{u} n y = sphereBasepoint.{u} n ↔ y ∈ Cube.boundary (Fin n) := by
  rw [← cubeToSphere_eq_sphereNorthPole_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ULift.ext (Subtype.ext ?_)⟩
  · have hv := congrArg (fun s : TopCat.sphere.{u} n ↦
      (((s : ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).down :
        EuclideanSpace ℝ (Fin (n + 1))))) h
    simp only [coe_basedCubeToSphere_down, coe_sphereBasepoint_down,
      ← spherePoleLinearIsometry_sphereNorthPole n] at hv
    exact Subtype.ext ((spherePoleLinearIsometry n).injective hv)
  · simp [h]

lemma basedCubeToSphere_of_mem_boundary {n : ℕ} {y : I^(Fin n)} (hy : y ∈ Cube.boundary (Fin n)) :
    basedCubeToSphere.{u} n y = sphereBasepoint.{u} n :=
  basedCubeToSphere_eq_sphereBasepoint_iff.2 hy

/-- `TauCeti.basedCubeToSphere` identifies exactly the points of `∂Iⁿ`. -/
lemma basedCubeToSphere_eq_iff {n : ℕ} {y z : I^(Fin n)} :
    basedCubeToSphere.{u} n y = basedCubeToSphere.{u} n z ↔
      y = z ∨ y ∈ Cube.boundary (Fin n) ∧ z ∈ Cube.boundary (Fin n) := by
  rw [← cubeToSphere_eq_cubeToSphere_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ULift.ext (Subtype.ext ?_)⟩
  · have hv := congrArg (fun s : TopCat.sphere.{u} n ↦
      (((s : ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).down :
        EuclideanSpace ℝ (Fin (n + 1))))) h
    simp only [coe_basedCubeToSphere_down] at hv
    exact Subtype.ext ((spherePoleLinearIsometry n).injective hv)
  · simp [h]

/-- `TauCeti.basedCubeToSphere` covers `TopCat.sphere n` off `sphereBasepoint n` in every
dimension `n ≥ 0`. -/
lemma exists_basedCubeToSphere_eq_of_ne {n : ℕ} {s : TopCat.sphere.{u} n}
    (hs : s ≠ sphereBasepoint.{u} n) : ∃ y, basedCubeToSphere.{u} n y = s := by
  let s' : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    ⟨(spherePoleLinearIsometry n).symm
      ((s : ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).down :
        EuclideanSpace ℝ (Fin (n + 1))), by simp⟩
  have hs' : s' ≠ sphereNorthPole n := by
    intro h
    refine hs (ULift.ext (Subtype.ext ?_))
    have hv := congrArg (fun t : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
      spherePoleLinearIsometry n (t : EuclideanSpace ℝ (Fin (n + 1)))) h
    simpa [s'] using hv
  obtain ⟨y, hy⟩ := exists_cubeToSphere_eq_of_ne hs'
  refine ⟨y, ULift.ext (Subtype.ext ?_)⟩
  simp [coe_basedCubeToSphere_down, hy, s']

@[simp]
lemma basedCubeToSphere_zero_apply (y : I^(Fin 0)) :
    basedCubeToSphere.{u} 0 y = sphereAntiBasepoint.{u} 0 := by
  rcases eq_sphereBasepoint_or_eq_sphereAntiBasepoint (basedCubeToSphere.{u} 0 y) with h | h
  · rw [basedCubeToSphere_eq_sphereBasepoint_iff, Cube.boundary_eq_empty] at h
    exact False.elim h
  · exact h

/-- The based disk-to-sphere collapse map `TopCat.disk n ⟶ TopCat.sphere n`, defined as the
composite of `TauCeti.diskHomeomorphCube n` and `TauCeti.basedCubeToSphere n`. -/
def basedDiskToSphere (n : ℕ) : TopCat.disk.{u} n ⟶ TopCat.sphere.{u} n :=
  TopCat.ofHom ((basedCubeToSphere.{u} n).comp
    (diskHomeomorphCube.{u} n : C(TopCat.disk.{u} n, I^(Fin n))))

lemma basedDiskToSphere_apply (n : ℕ) (z : TopCat.disk.{u} n) :
    basedDiskToSphere.{u} n z = basedCubeToSphere.{u} n (diskHomeomorphCube.{u} n z) := (rfl)

/-- On the underlying closed Euclidean ball, `TauCeti.basedDiskToSphere n` is
`TauCeti.closedBallToSphere n` followed by `TauCeti.spherePoleLinearIsometry n`. -/
lemma coe_basedDiskToSphere_down (n : ℕ) (z : TopCat.disk.{u} n) :
    (((basedDiskToSphere.{u} n z : TopCat.sphere.{u} n) :
      ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).down :
        EuclideanSpace ℝ (Fin (n + 1))) =
      spherePoleLinearIsometry n
        (closedBallToSphere n
          ((z : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down)) := by
  let z₀ : TopCat.disk.{0} n :=
    ULift.up ((z : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down)
  have hcb : diskHomeomorphClosedBall.{u} n z = diskHomeomorphClosedBall.{0} n z₀ :=
    Subtype.ext ((coe_diskHomeomorphClosedBall_apply z).trans
      (coe_diskHomeomorphClosedBall_apply z₀).symm)
  have hcube : diskHomeomorphCube.{u} n z = diskHomeomorphCube.{0} n z₀ := by
    rw [diskHomeomorphCube_apply, diskHomeomorphCube_apply, hcb]
  simp only [basedDiskToSphere_apply, coe_basedCubeToSphere_down, cubeToSphere_apply, hcube,
    Homeomorph.symm_apply_apply]
  rfl

@[simp]
lemma basedDiskToSphere_eq_sphereBasepoint_iff {n : ℕ} {z : TopCat.disk.{u} n} :
    basedDiskToSphere.{u} n z = sphereBasepoint.{u} n ↔
      z ∈ range (TopCat.diskBoundaryInclusion.{u} n) := by
  rw [basedDiskToSphere_apply, basedCubeToSphere_eq_sphereBasepoint_iff,
    diskHomeomorphCube_mem_boundary_iff]

@[simp]
lemma basedDiskToSphere_diskBoundaryInclusion (n : ℕ) (s : TopCat.diskBoundary.{u} n) :
    basedDiskToSphere.{u} n (TopCat.diskBoundaryInclusion.{u} n s) = sphereBasepoint.{u} n :=
  basedDiskToSphere_eq_sphereBasepoint_iff.2 ⟨s, rfl⟩

@[simp]
lemma basedDiskToSphere_diskCenter (n : ℕ) :
    basedDiskToSphere.{u} n (diskCenter.{u} n) = sphereAntiBasepoint.{u} n := by
  refine ULift.ext (Subtype.ext ?_)
  rw [coe_basedDiskToSphere_down, coe_sphereAntiBasepoint_down]
  have h0 : ((diskCenter.{u} n : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
      closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) = 0 :=
    Subtype.ext (coe_diskCenter_down n)
  have hc : (closedBallToSphere n (0 : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
      EuclideanSpace ℝ (Fin (n + 1))) = EuclideanSpace.single (Fin.last n) (-1) := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp
    · simp [Fin.castSucc_ne_last]
  rw [h0, hc, spherePoleLinearIsometry_single_last]
  ext i
  by_cases hi : i = 0 <;> simp [hi]

/-! ### Pointed homeomorphisms `Iⁿ / ∂Iⁿ ≃ₜ Sⁿ` and `Dⁿ / ∂Dⁿ ≃ₜ Sⁿ` -/

private def cubeQuotientToSphereHom (n : ℕ) :
    (cubeBoundaryPair.{u} n).ordinaryPairQuotient ⟶ TopCat.sphere.{u} n :=
  (cubeBoundaryPair.{u} n).ordinaryPairQuotientDesc
    (TopCat.ofHom ((basedCubeToSphere.{u} n).comp ⟨ULift.down, continuous_uliftDown⟩))
    (sphereBasepoint.{u} n)
    fun b ↦ basedCubeToSphere_of_mem_boundary b.2

private lemma bijective_cubeQuotientToSphereHom (n : ℕ) :
    Function.Bijective (cubeQuotientToSphereHom.{u} n) := by
  have hπ (y : (cubeBoundaryPair.{u} n).fst) :
      cubeQuotientToSphereHom.{u} n ((cubeBoundaryPair.{u} n).ordinaryPairQuotientπ y) =
        basedCubeToSphere.{u} n y.down :=
    (cubeBoundaryPair.{u} n).ordinaryPairQuotientπ_desc_apply _ _ _ y
  have hbase :
      cubeQuotientToSphereHom.{u} n (cubeBoundaryPair.{u} n).ordinaryPairQuotientBasepoint =
        sphereBasepoint.{u} n :=
    (cubeBoundaryPair.{u} n).ordinaryPairQuotientDesc_basepoint _ _ _
  refine ⟨fun p q hpq ↦ ?_, fun s ↦ ?_⟩
  · induction p using TopPair.ordinaryPairQuotient_ind with
    | hbase =>
      induction q using TopPair.ordinaryPairQuotient_ind with
      | hbase => rfl
      | hπ z =>
        rw [hbase, hπ, eq_comm, basedCubeToSphere_eq_sphereBasepoint_iff] at hpq
        exact ((cubeBoundaryPair.{u} n).ordinaryPairQuotientπ_eq_basepoint_iff z).2
          (by rw [TopPair.range_ofSubset_map]; exact hpq) |>.symm
    | hπ y =>
      induction q using TopPair.ordinaryPairQuotient_ind with
      | hbase =>
        rw [hπ, hbase, basedCubeToSphere_eq_sphereBasepoint_iff] at hpq
        exact ((cubeBoundaryPair.{u} n).ordinaryPairQuotientπ_eq_basepoint_iff y).2
          (by rw [TopPair.range_ofSubset_map]; exact hpq)
      | hπ z =>
        rw [hπ, hπ, basedCubeToSphere_eq_iff] at hpq
        refine ((cubeBoundaryPair.{u} n).ordinaryPairQuotientπ_eq_iff y z).2 ?_
        rw [TopPair.range_ofSubset_map]
        exact hpq.imp ULift.ext id
  · by_cases hs : s = sphereBasepoint.{u} n
    · exact ⟨(cubeBoundaryPair.{u} n).ordinaryPairQuotientBasepoint, hs ▸ hbase⟩
    · obtain ⟨y, rfl⟩ := exists_basedCubeToSphere_eq_of_ne hs
      exact ⟨(cubeBoundaryPair.{u} n).ordinaryPairQuotientπ (ULift.up y), hπ (ULift.up y)⟩

instance compactSpace_cubeBoundaryPairQuotient (n : ℕ) :
    CompactSpace (cubeBoundaryPair.{u} n).ordinaryPairQuotient :=
  haveI : CompactSpace (cubeBoundaryPair.{u} n).fst :=
    inferInstanceAs (CompactSpace (ULift.{u} (I^(Fin n))))
  (cubeBoundaryPair.{u} n).compactSpace_ordinaryPairQuotient

/-- **The pointed cube quotient `Iⁿ / ∂Iⁿ` is homeomorphic to `TopCat.sphere n`** in every
dimension `n ≥ 0`, sending `y ∈ Iⁿ` to `basedCubeToSphere n y` and the collapsed boundary to
`sphereBasepoint n`. -/
def cubeQuotientSphereHomeomorph (n : ℕ) :
    (cubeBoundaryPair.{u} n).ordinaryPairQuotient ≃ₜ TopCat.sphere.{u} n :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (cubeQuotientToSphereHom.{u} n) (bijective_cubeQuotientToSphereHom n))
    (cubeQuotientToSphereHom.{u} n).hom.continuous

instance t2Space_cubeBoundaryPairQuotient (n : ℕ) :
    T2Space (cubeBoundaryPair.{u} n).ordinaryPairQuotient :=
  (cubeQuotientSphereHomeomorph.{u} n).symm.t2Space

@[simp]
lemma cubeQuotientSphereHomeomorph_π (n : ℕ) (y : ULift.{u} (I^(Fin n))) :
    cubeQuotientSphereHomeomorph.{u} n ((cubeBoundaryPair.{u} n).ordinaryPairQuotientπ y) =
      basedCubeToSphere.{u} n y.down :=
  (cubeBoundaryPair.{u} n).ordinaryPairQuotientπ_desc_apply _ _ _ y

@[simp]
lemma cubeQuotientSphereHomeomorph_basepoint (n : ℕ) :
    cubeQuotientSphereHomeomorph.{u} n (cubeBoundaryPair.{u} n).ordinaryPairQuotientBasepoint =
      sphereBasepoint.{u} n :=
  (cubeBoundaryPair.{u} n).ordinaryPairQuotientDesc_basepoint _ _ _

@[simp]
lemma cubeQuotientSphereHomeomorph_symm_sphereBasepoint (n : ℕ) :
    (cubeQuotientSphereHomeomorph.{u} n).symm (sphereBasepoint.{u} n) =
      (cubeBoundaryPair.{u} n).ordinaryPairQuotientBasepoint :=
  (cubeQuotientSphereHomeomorph.{u} n).symm_apply_eq.2
    (cubeQuotientSphereHomeomorph_basepoint n).symm

@[simp]
lemma cubeQuotientSphereHomeomorph_symm_basedCubeToSphere (n : ℕ) (y : I^(Fin n)) :
    (cubeQuotientSphereHomeomorph.{u} n).symm (basedCubeToSphere.{u} n y) =
      (cubeBoundaryPair.{u} n).ordinaryPairQuotientπ (ULift.up y) :=
  (cubeQuotientSphereHomeomorph.{u} n).symm_apply_eq.2
    (cubeQuotientSphereHomeomorph_π n (ULift.up y)).symm

/-- **The pointed disk quotient `Dⁿ / ∂Dⁿ` is homeomorphic to `TopCat.sphere n`** in every
dimension `n ≥ 0`, sending `z ∈ Dⁿ` to `basedDiskToSphere n z` and the collapsed boundary to
`sphereBasepoint n`, compatible with `TauCeti.diskBoundaryPairIsoCube`. -/
def diskQuotientSphereHomeomorph (n : ℕ) :
    (diskBoundaryPair.{u} n).ordinaryPairQuotient ≃ₜ TopCat.sphere.{u} n :=
  (TopPair.ordinaryPairQuotientHomeomorph (diskBoundaryPairIsoCube.{u} n)).trans
    (cubeQuotientSphereHomeomorph.{u} n)

instance compactSpace_diskBoundaryPairQuotient (n : ℕ) :
    CompactSpace (diskBoundaryPair.{u} n).ordinaryPairQuotient :=
  (diskQuotientSphereHomeomorph.{u} n).symm.compactSpace

instance t2Space_diskBoundaryPairQuotient (n : ℕ) :
    T2Space (diskBoundaryPair.{u} n).ordinaryPairQuotient :=
  (diskQuotientSphereHomeomorph.{u} n).symm.t2Space

lemma diskQuotientSphereHomeomorph_π (n : ℕ) (z : TopCat.disk.{u} n) :
    diskQuotientSphereHomeomorph.{u} n ((diskBoundaryPair.{u} n).ordinaryPairQuotientπ z) =
      basedDiskToSphere.{u} n z := by
  let e₁ := TopPair.ordinaryPairQuotientHomeomorph (diskBoundaryPairIsoCube.{u} n)
  have hy : TopPair.Hom.fst (diskBoundaryPairIsoCube.{u} n).hom z =
      ULift.up (diskHomeomorphCube.{u} n z) :=
    ULift.ext ((congrArg
      (fun f : diskBoundaryPair.{u} n ⟶ cubeBoundaryPair.{u} n ↦ (TopPair.Hom.fst f z).down)
      (diskBoundaryPairIsoCube_hom n)).trans (diskBoundaryPairToCube_fst_apply_down z))
  calc cubeQuotientSphereHomeomorph.{u} n (e₁ ((diskBoundaryPair.{u} n).ordinaryPairQuotientπ z))
    _ = cubeQuotientSphereHomeomorph.{u} n
          ((cubeBoundaryPair.{u} n).ordinaryPairQuotientπ
            (TopPair.Hom.fst (diskBoundaryPairIsoCube.{u} n).hom z)) :=
        congrArg (cubeQuotientSphereHomeomorph.{u} n)
          (TopPair.ordinaryPairQuotientHomeomorph_π (diskBoundaryPairIsoCube.{u} n) z)
    _ = cubeQuotientSphereHomeomorph.{u} n
          ((cubeBoundaryPair.{u} n).ordinaryPairQuotientπ
            (ULift.up (diskHomeomorphCube.{u} n z))) :=
        congrArg (fun y ↦ cubeQuotientSphereHomeomorph.{u} n
          ((cubeBoundaryPair.{u} n).ordinaryPairQuotientπ y)) hy
    _ = basedDiskToSphere.{u} n z :=
        cubeQuotientSphereHomeomorph_π n (ULift.up (diskHomeomorphCube.{u} n z))

@[simp]
lemma diskQuotientSphereHomeomorph_basepoint (n : ℕ) :
    diskQuotientSphereHomeomorph.{u} n (diskBoundaryPair.{u} n).ordinaryPairQuotientBasepoint =
      sphereBasepoint.{u} n := by
  let e₁ := TopPair.ordinaryPairQuotientHomeomorph (diskBoundaryPairIsoCube.{u} n)
  calc cubeQuotientSphereHomeomorph.{u} n
        (e₁ (diskBoundaryPair.{u} n).ordinaryPairQuotientBasepoint)
    _ = cubeQuotientSphereHomeomorph.{u} n
          (cubeBoundaryPair.{u} n).ordinaryPairQuotientBasepoint :=
        congrArg (cubeQuotientSphereHomeomorph.{u} n)
          (TopPair.ordinaryPairQuotientHomeomorph_basepoint (diskBoundaryPairIsoCube.{u} n))
    _ = sphereBasepoint.{u} n := cubeQuotientSphereHomeomorph_basepoint n

@[simp]
lemma diskQuotientSphereHomeomorph_symm_sphereBasepoint (n : ℕ) :
    (diskQuotientSphereHomeomorph.{u} n).symm (sphereBasepoint.{u} n) =
      (diskBoundaryPair.{u} n).ordinaryPairQuotientBasepoint :=
  (diskQuotientSphereHomeomorph.{u} n).symm_apply_eq.2
    (diskQuotientSphereHomeomorph_basepoint n).symm

@[simp]
lemma diskQuotientSphereHomeomorph_symm_basedDiskToSphere (n : ℕ) (z : TopCat.disk.{u} n) :
    (diskQuotientSphereHomeomorph.{u} n).symm (basedDiskToSphere.{u} n z) =
      (diskBoundaryPair.{u} n).ordinaryPairQuotientπ z :=
  (diskQuotientSphereHomeomorph.{u} n).symm_apply_eq.2
    (diskQuotientSphereHomeomorph_π n z).symm

/-- The homeomorphism induced on pointed quotients by `TauCeti.diskBoundaryPairIsoCube` commutes
with `TauCeti.diskQuotientSphereHomeomorph` and `TauCeti.cubeQuotientSphereHomeomorph`. -/
lemma ordinaryPairQuotientHomeomorph_diskBoundaryPairIsoCube_trans (n : ℕ) :
    (TopPair.ordinaryPairQuotientHomeomorph (diskBoundaryPairIsoCube.{u} n)).trans
      (cubeQuotientSphereHomeomorph.{u} n) = diskQuotientSphereHomeomorph.{u} n := (rfl)

end TauCeti

end

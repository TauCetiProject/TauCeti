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

/-!
# Based sphere quotients of disks and cubes

For `TopCat.sphere n` based at its positive first-coordinate pole `TauCeti.sphereBasepoint n`
(`e₀`), this file introduces the antipode `TauCeti.sphereAntiBasepoint n` (`-e₀`), applies the
coordinate linear isometry `TauCeti.spherePoleLinearIsometry n` moving `e_last` to `e₀` (identity in
dimension `0` and `(x₀, x₁, …, xₙ) ↦ (xₙ, -x₀, x₁, …, xₙ₋₁)` of determinant `(-1) ^ (n + 1)` for
`n ≥ 1`), and constructs the canonical pointed homeomorphisms `TauCeti.cubeQuotientSphereHomeomorph`
(`Iⁿ / ∂Iⁿ ≃ₜ Sⁿ`) and `TauCeti.diskQuotientSphereHomeomorph` (`Dⁿ / ∂Dⁿ ≃ₜ Sⁿ`) for all `n ≥ 0`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 and Section 2.1.
-/

public section

noncomputable section

open CategoryTheory Metric Set Topology
open scoped unitInterval

universe u

namespace TauCeti

private def sphereVec {n : ℕ} (s : TopCat.sphere.{u} n) : EuclideanSpace ℝ (Fin (n + 1)) :=
  ((s : ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).down :
    EuclideanSpace ℝ (Fin (n + 1)))

private lemma sphere_ext {n : ℕ} {s t : TopCat.sphere.{u} n} (h : sphereVec s = sphereVec t) :
    s = t := ULift.ext (Subtype.ext h)

/-- The negative first-coordinate pole `-e₀` of `TopCat.sphere n`, antipodal to
`TauCeti.sphereBasepoint`. -/
def sphereAntiBasepoint (n : ℕ) : TopCat.sphere.{u} n :=
  diskBoundaryNeg (n + 1) (sphereBasepoint n)

@[simp]
lemma coe_sphereAntiBasepoint_down (n : ℕ) :
    (((sphereAntiBasepoint.{u} n : TopCat.sphere.{u} n) :
      ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).down :
        EuclideanSpace ℝ (Fin (n + 1))) = -EuclideanSpace.single 0 1 :=
  (congrArg Subtype.val (diskBoundaryNeg_apply_down (sphereBasepoint.{u} n))).trans (by simp)

/-- The basepoint `e₀` and its antipode `-e₀` on `TopCat.sphere n` are distinct. -/
lemma sphereBasepoint_ne_sphereAntiBasepoint (n : ℕ) :
    sphereBasepoint.{u} n ≠ sphereAntiBasepoint.{u} n := fun h ↦ by
  have h0 := congrArg (fun s ↦ sphereVec s 0) h
  simp only [sphereVec, coe_sphereBasepoint_down, coe_sphereAntiBasepoint_down, PiLp.neg_apply,
    PiLp.single_apply, ↓reduceIte] at h0
  norm_num at h0

/-- Every point of `TopCat.sphere 0` is either `sphereBasepoint 0` or `sphereAntiBasepoint 0`. -/
lemma eq_sphereBasepoint_or_eq_sphereAntiBasepoint (s : TopCat.sphere.{u} 0) :
    s = sphereBasepoint.{u} 0 ∨ s = sphereAntiBasepoint.{u} 0 :=
  (sq_eq_one_iff.1 (sq_diskBoundary_one_eq_one s)).imp
    (fun h ↦ diskBoundary_one_ext (h.trans (by simp)))
    (fun h ↦ diskBoundary_one_ext (h.trans (by simp)))

/-- The coordinate linear isometry of `ℝⁿ⁺¹` moving `e_last` to `e₀`: the identity for `n = 0`,
and `(x₀, x₁, …, xₙ) ↦ (xₙ, -x₀, x₁, …, xₙ₋₁)` for `n ≥ 1`. -/
def spherePoleLinearIsometry (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (LinearIsometryEquiv.piLpCongrRight 2 fun i : Fin (n + 1) ↦
    if i = 0 ∧ n ≠ 0 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finRotate (n + 1)))

-- Not `@[simp]`: the concrete-index `@[simp]` lemmas below simplify `0`, `1`, and `j.succ.succ`,
-- and marking this general `if`-formula `@[simp]` would put their LHSs out of `simp` normal form.
/-- Coordinate formula for `TauCeti.spherePoleLinearIsometry`: coordinate `i` is pulled back along
`finRotate (n + 1)` and negated when `n ≠ 0` and `(finRotate (n + 1)).symm i = 0`. -/
lemma spherePoleLinearIsometry_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) :
    spherePoleLinearIsometry n x i =
      (if (finRotate (n + 1)).symm i = 0 ∧ n ≠ 0 then -1 else 1) *
        x ((finRotate (n + 1)).symm i) := by
  simp only [spherePoleLinearIsometry, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
    LinearIsometryEquiv.piLpCongrRight_apply]
  split_ifs <;> simp

@[simp]
lemma spherePoleLinearIsometry_zero :
    spherePoleLinearIsometry 0 = LinearIsometryEquiv.refl ℝ (EuclideanSpace ℝ (Fin 1)) := by
  ext x i; rw [Fin.eq_zero i]; simp [spherePoleLinearIsometry_apply]

@[simp]
lemma spherePoleLinearIsometry_apply_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    spherePoleLinearIsometry n x 0 = x (Fin.last n) := by
  rw [spherePoleLinearIsometry_apply, (finRotate (n + 1)).symm_apply_eq.2 finRotate_last.symm]
  simp

@[simp]
lemma spherePoleLinearIsometry_succ_apply_one (m : ℕ) (x : EuclideanSpace ℝ (Fin (m + 2))) :
    spherePoleLinearIsometry (m + 1) x 1 = -x 0 := by
  rw [spherePoleLinearIsometry_apply,
    (finRotate (m + 2)).symm_apply_eq.2 finRotate_apply_zero.symm]
  simp

@[simp]
lemma spherePoleLinearIsometry_succ_apply_succ_succ (m : ℕ) (x : EuclideanSpace ℝ (Fin (m + 2)))
    (j : Fin m) :
    spherePoleLinearIsometry (m + 1) x j.succ.succ = x j.succ.castSucc := by
  have hrot : (finRotate (m + 2)).symm j.succ.succ = j.succ.castSucc :=
    (finRotate (m + 2)).symm_apply_eq.2 (finRotate_of_lt (Nat.succ_lt_succ j.isLt)).symm
  rw [spherePoleLinearIsometry_apply, hrot]
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
    LinearMap.det (spherePoleLinearIsometry 0).toLinearMap = 1 := by simp

/-- In positive dimension `n ≥ 1`, `TauCeti.spherePoleLinearIsometry n` has determinant
`(-1) ^ (n + 1)`. -/
lemma det_spherePoleLinearIsometry (n : ℕ) [NeZero n] :
    LinearMap.det (spherePoleLinearIsometry n).toLinearMap = (-1 : ℝ) ^ (n + 1) := by
  have hn : n ≠ 0 := NeZero.ne n
  let b := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  let M := Matrix.diagonal fun k : Fin (n + 1) ↦ if k = 0 then (-1 : ℝ) else 1
  have hM : LinearMap.toMatrix b b (spherePoleLinearIsometry n).toLinearMap =
      M.submatrix (finRotate (n + 1)).symm id := by
    ext i j
    simp [b, M, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
      spherePoleLinearIsometry_apply, hn, Matrix.diagonal_apply]
  have hsign : Equiv.Perm.sign (finRotate (n + 1)).symm = (-1) ^ n := by
    rw [← Equiv.Perm.inv_def, map_inv, Int.units_inv_eq_self, sign_finRotate, Nat.add_sub_cancel]
  rw [← LinearMap.det_toMatrix b, hM, Matrix.det_permute, hsign, Matrix.det_diagonal,
    Fin.prod_univ_succ]
  simp [pow_succ]

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
  refine ⟨fun h ↦ ?_, fun h ↦ sphere_ext (by simp [sphereVec, h])⟩
  have hv := congrArg sphereVec h
  simp only [sphereVec, coe_basedCubeToSphere_down, coe_sphereBasepoint_down,
    ← spherePoleLinearIsometry_sphereNorthPole n] at hv
  exact Subtype.ext ((spherePoleLinearIsometry n).injective hv)

lemma basedCubeToSphere_of_mem_boundary {n : ℕ} {y : I^(Fin n)} (hy : y ∈ Cube.boundary (Fin n)) :
    basedCubeToSphere.{u} n y = sphereBasepoint.{u} n :=
  basedCubeToSphere_eq_sphereBasepoint_iff.2 hy

/-- `TauCeti.basedCubeToSphere` identifies exactly the points of `∂Iⁿ`. -/
lemma basedCubeToSphere_eq_iff {n : ℕ} {y z : I^(Fin n)} :
    basedCubeToSphere.{u} n y = basedCubeToSphere.{u} n z ↔
      y = z ∨ y ∈ Cube.boundary (Fin n) ∧ z ∈ Cube.boundary (Fin n) := by
  rw [← cubeToSphere_eq_cubeToSphere_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ sphere_ext (by simp [sphereVec, h])⟩
  have hv := congrArg sphereVec h
  simp only [sphereVec, coe_basedCubeToSphere_down] at hv
  exact Subtype.ext ((spherePoleLinearIsometry n).injective hv)

/-- `TauCeti.basedCubeToSphere` covers `TopCat.sphere n` off `sphereBasepoint n` in every
dimension `n ≥ 0`. -/
lemma exists_basedCubeToSphere_eq_of_ne {n : ℕ} {s : TopCat.sphere.{u} n}
    (hs : s ≠ sphereBasepoint.{u} n) : ∃ y, basedCubeToSphere.{u} n y = s := by
  let s' : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    ⟨(spherePoleLinearIsometry n).symm (sphereVec s), by simp [sphereVec]⟩
  have hs' : s' ≠ sphereNorthPole n := fun h ↦ hs <| sphere_ext <| by
    simpa [s', sphereVec] using congrArg (fun t : sphere _ 1 ↦ spherePoleLinearIsometry n t.val) h
  obtain ⟨y, hy⟩ := exists_cubeToSphere_eq_of_ne hs'
  exact ⟨y, sphere_ext (by simp [sphereVec, hy, s'])⟩

@[simp]
lemma basedCubeToSphere_zero_apply (y : I^(Fin 0)) :
    basedCubeToSphere.{u} 0 y = sphereAntiBasepoint.{u} 0 :=
  (eq_sphereBasepoint_or_eq_sphereAntiBasepoint _).resolve_left fun h ↦ by
    rwa [basedCubeToSphere_eq_sphereBasepoint_iff, Cube.boundary_eq_empty] at h

/-- Reindexing `TopCat.sphere a` to `TopCat.sphere b` along an equality `h : a = b` of dimensions,
via the coordinate permutation `finCongr` on `EuclideanSpace ℝ (Fin (· + 1))`. -/
def sphereCongrHomeomorph {a b : ℕ} (h : a = b) :
    TopCat.sphere.{u} a ≃ₜ TopCat.sphere.{u} b :=
  Homeomorph.ulift.trans <|
    (((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (finCongr (congrArg (· + 1) h))).toHomeomorph.subtype fun _ ↦ by simp).trans
      Homeomorph.ulift.symm)

@[simp]
lemma sphereCongrHomeomorph_rfl (a : ℕ) :
    sphereCongrHomeomorph (rfl : a = a) = Homeomorph.refl (TopCat.sphere.{u} a) := by
  -- `TopCat.sphere.{u} a` has carrier `ULift.{u} (sphere 0 1)`; stating the identity on that
  -- carrier lets `simp` reduce `finCongr rfl` and `piLpCongrLeft` by lemmas.
  have he :
      (Homeomorph.ulift.trans <|
        (((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
          (finCongr (congrArg (· + 1) (rfl : a = a)))).toHomeomorph.subtype fun _ ↦ by simp).trans
          Homeomorph.ulift.symm)) =
        Homeomorph.refl (ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin (a + 1))) 1)) := by
    ext s
    simp [Homeomorph.ulift, Homeomorph.subtype]
  exact he

@[simp]
lemma sphereCongrHomeomorph_sphereBasepoint {a b : ℕ} (h : a = b) :
    sphereCongrHomeomorph.{u} h (sphereBasepoint.{u} a) = sphereBasepoint.{u} b := by
  subst h; simp

@[simp]
lemma sphereCongrHomeomorph_basedCubeToSphere {a b : ℕ} (h : a = b) (y : I^(Fin a)) :
    sphereCongrHomeomorph.{u} h (basedCubeToSphere.{u} a y) =
      basedCubeToSphere.{u} b (y ∘ Fin.cast h.symm) := by
  subst h; simp

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
  -- `TauCeti.cubeToSphere` is fixed at universe `0`, so `diskHomeomorphCube.{u}` is compared with
  -- `diskHomeomorphCube.{0}` via `TauCeti.diskHomeomorphCube_symm_diskHomeomorphCube_down`.
  rw [basedDiskToSphere_apply, coe_basedCubeToSphere_down, cubeToSphere_apply,
    diskHomeomorphCube_symm_diskHomeomorphCube_down]

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
  refine sphere_ext ?_
  rw [sphereVec, sphereVec, coe_basedDiskToSphere_down, coe_sphereAntiBasepoint_down]
  let c0 : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := ⟨0, mem_closedBall_self zero_le_one⟩
  have h0 : ((diskCenter.{u} n : ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
      closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) = c0 := Subtype.ext (coe_diskCenter_down n)
  have hc : (closedBallToSphere n c0 : EuclideanSpace ℝ (Fin (n + 1))) =
      EuclideanSpace.single (Fin.last n) (-1) := by
    ext i; refine Fin.lastCases (by simp [c0]) (fun _ ↦ by simp [c0, Fin.castSucc_ne_last]) i
  rw [h0, hc, spherePoleLinearIsometry_single_last]
  ext i; by_cases hi : i = 0 <;> simp [hi]

private instance compactSpace_cubeBoundaryPairFst (n : ℕ) :
    CompactSpace (cubeBoundaryPair.{u} n).fst :=
  inferInstanceAs (CompactSpace (ULift.{u} (I^(Fin n))))

instance compactSpace_cubeBoundaryPairQuotient (n : ℕ) :
    CompactSpace (cubeBoundaryPair.{u} n).ordinaryPairQuotient :=
  (cubeBoundaryPair.{u} n).compactSpace_ordinaryPairQuotient

/-- **The pointed cube quotient `Iⁿ / ∂Iⁿ` is homeomorphic to `TopCat.sphere n`** in every
dimension `n ≥ 0`, sending `y ∈ Iⁿ` to `basedCubeToSphere n y` and the collapsed boundary to
`sphereBasepoint n`. -/
def cubeQuotientSphereHomeomorph (n : ℕ) :
    (cubeBoundaryPair.{u} n).ordinaryPairQuotient ≃ₜ TopCat.sphere.{u} n :=
  (cubeBoundaryPair.{u} n).ordinaryPairQuotientHomeomorph
    (TopCat.ofHom ((basedCubeToSphere.{u} n).comp ⟨ULift.down, continuous_uliftDown⟩))
    (sphereBasepoint.{u} n)
    (fun _ ↦ basedCubeToSphere_eq_sphereBasepoint_iff.trans
      (by rw [TopPair.range_ofSubset_map]; exact Set.mem_preimage.symm))
    (fun _ _ hy h ↦ ULift.ext <| (basedCubeToSphere_eq_iff.1 h).resolve_right fun hb ↦
      hy (by rw [TopPair.range_ofSubset_map]; exact Set.mem_preimage.2 hb.1))
    (fun _ hs ↦ let ⟨y, hy⟩ := exists_basedCubeToSphere_eq_of_ne hs; ⟨ULift.up y, hy⟩)

instance t2Space_cubeBoundaryPairQuotient (n : ℕ) :
    T2Space (cubeBoundaryPair.{u} n).ordinaryPairQuotient :=
  (cubeQuotientSphereHomeomorph.{u} n).symm.t2Space

@[simp]
lemma cubeQuotientSphereHomeomorph_π (n : ℕ) (y : ULift.{u} (I^(Fin n))) :
    cubeQuotientSphereHomeomorph.{u} n ((cubeBoundaryPair.{u} n).ordinaryPairQuotientπ y) =
      basedCubeToSphere.{u} n y.down :=
  (cubeBoundaryPair.{u} n).ordinaryPairQuotientHomeomorph_π _ _ _ y

@[simp]
lemma cubeQuotientSphereHomeomorph_basepoint (n : ℕ) :
    cubeQuotientSphereHomeomorph.{u} n (cubeBoundaryPair.{u} n).ordinaryPairQuotientBasepoint =
      sphereBasepoint.{u} n :=
  (cubeBoundaryPair.{u} n).ordinaryPairQuotientHomeomorph_basepoint _ _ _

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
  (TopPair.ordinaryPairQuotientCongrHomeomorph (diskBoundaryPairIsoCube.{u} n)).trans
    (cubeQuotientSphereHomeomorph.{u} n)

instance compactSpace_diskBoundaryPairQuotient (n : ℕ) :
    CompactSpace (diskBoundaryPair.{u} n).ordinaryPairQuotient :=
  (diskQuotientSphereHomeomorph.{u} n).symm.compactSpace

instance t2Space_diskBoundaryPairQuotient (n : ℕ) :
    T2Space (diskBoundaryPair.{u} n).ordinaryPairQuotient :=
  (diskQuotientSphereHomeomorph.{u} n).symm.t2Space

-- Not `@[simp]`: `TauCeti.diskBoundaryPair_fst` simplifies the implicit domain of
-- `ConcreteCategory.hom`, so `simpNF` rejects `@[simp]` on this lemma.
lemma diskQuotientSphereHomeomorph_π (n : ℕ) (z : TopCat.disk.{u} n) :
    diskQuotientSphereHomeomorph.{u} n ((diskBoundaryPair.{u} n).ordinaryPairQuotientπ z) =
      basedDiskToSphere.{u} n z := by
  have h : TopPair.Hom.fst (diskBoundaryPairIsoCube.{u} n).hom z =
      ULift.up (diskHomeomorphCube.{u} n z) :=
    ULift.ext (diskBoundaryPairIsoCube_hom_fst_apply_down z)
  simp only [diskQuotientSphereHomeomorph, Homeomorph.trans_apply,
    TopPair.ordinaryPairQuotientCongrHomeomorph_π (diskBoundaryPairIsoCube.{u} n) z, h,
    cubeQuotientSphereHomeomorph_π, basedDiskToSphere_apply]

@[simp]
lemma diskQuotientSphereHomeomorph_basepoint (n : ℕ) :
    diskQuotientSphereHomeomorph.{u} n (diskBoundaryPair.{u} n).ordinaryPairQuotientBasepoint =
      sphereBasepoint.{u} n :=
  (congrArg (cubeQuotientSphereHomeomorph.{u} n)
    (TopPair.ordinaryPairQuotientCongrHomeomorph_basepoint (diskBoundaryPairIsoCube.{u} n))).trans
    (cubeQuotientSphereHomeomorph_basepoint n)

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
lemma ordinaryPairQuotientCongrHomeomorph_diskBoundaryPairIsoCube_trans (n : ℕ) :
    (TopPair.ordinaryPairQuotientCongrHomeomorph (diskBoundaryPairIsoCube.{u} n)).trans
      (cubeQuotientSphereHomeomorph.{u} n) = diskQuotientSphereHomeomorph.{u} n := (rfl)

@[simp]
lemma ordinaryPairQuotientCongrHomeomorph_cubeBoundaryPairProdIso_π
    (m n : ℕ) (x : I^(Fin m)) (y : I^(Fin n)) :
    TopPair.ordinaryPairQuotientCongrHomeomorph (cubeBoundaryPairProdIso.{u} m n)
      ((TopPair.ofSubset (X := TopCat.of (ULift.{u} (I^(Fin m)) × ULift.{u} (I^(Fin n))))
        ((ULift.down ⁻¹' Cube.boundary (Fin m)) ×ˢ univ ∪
          univ ×ˢ (ULift.down ⁻¹' Cube.boundary (Fin n)))).ordinaryPairQuotientπ
        (ULift.up x, ULift.up y)) =
      (cubeBoundaryPair.{u} (m + n)).ordinaryPairQuotientπ (ULift.up (Fin.append x y)) :=
  (TopPair.ordinaryPairQuotientCongrHomeomorph_π (cubeBoundaryPairProdIso.{u} m n) _).trans <|
    congrArg (cubeBoundaryPair.{u} (m + n)).ordinaryPairQuotientπ
      (cubeBoundaryPairProdIso_hom_fst_apply m n (ULift.up x, ULift.up y))

end TauCeti

end

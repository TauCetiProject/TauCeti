/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Sphere
public import TauCeti.Geometry.Diffeomorphism.Covered
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Analysis.InnerProductSpace.PlaneRotation
public import TauCeti.Geometry.Manifold.Degree.Homological
public import TauCeti.Geometry.Manifold.Degree.SphereRotation
public import TauCeti.Geometry.Sphere.Connected
public import TauCeti.Topology.Grassmannian.SphereBundle.Exact
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.HomotopyGroup

/-!
# Spheres covered by rotations

A compact oriented `d`-manifold `M` is `ℓ`-covered by diffeomorphisms when some class of
`H_d(Diff(M); ℤ)` evaluates to `ℓ • [M]`
(`TauCeti.HomologicalOrientation.IsCoveredByDiffeomorphisms`). This file formalizes both proofs of
Proposition 6.34 of Barraud–Damian–Humilière–Oancea that odd-dimensional spheres are `ℓ`-covered by
diffeomorphisms for some `ℓ > 0`, using rotations of the ambient Euclidean or inner product space.

## First proof: the rotation fibration and Hurewicz

For the sphere `Sⁿ⁺¹ ⊆ ℝⁿ⁺²` the rotation group `SO(n + 2)` acts by diffeomorphisms
(`TauCeti.continuousOrthogonalToDiffSphere`) with orbit map the fibration
`SO(n + 1) → SO(n + 2) → Sⁿ⁺¹`. If `πₙ(SO(n + 1))` is a torsion group, then `Sⁿ⁺¹` is `ℓ`-covered
by diffeomorphisms for some `ℓ > 0`:

* In the exact sequence `πₙ₊₁(SO(n + 2)) → πₙ₊₁(Sⁿ⁺¹) → πₙ(SO(n + 1))` of the fibration, the
  boundary of the generator `ι` of `πₙ₊₁(Sⁿ⁺¹)` has finite order, so some positive power `ι ^ k`
  comes from a class `b` of `SO(n + 2)`
  (`TauCeti.exists_pow_mem_range_homotopyGroupMap_specialOrthogonalSphereMap_of_isOfFinOrder`).
* The Hurewicz class of `b`, pushed into `Diff(Sⁿ⁺¹)` by the action, evaluates to the Hurewicz
  class of `ι ^ k`, which is `k` times that of `ι`, by naturality of the Hurewicz map.
* The Hurewicz class of `ι` generates `Hₙ₊₁(Sⁿ⁺¹; ℤ)` (`TauCeti.isIso_hurewicz_sphereGenLoop`), so
  it is a nonzero multiple `c • [Sⁿ⁺¹]` of the fundamental class, and `ℓ = |k c|`.

The torsion hypothesis is the input that the paper's Lemma 6.35 supplies for odd spheres. It holds
for `S³`, where `π₂(SO(3)) = 0`.

The exact sequence of the fibration is stated for `SO(1 + (n + 1))` acting on the sphere of
`ℝ^(1 + (n + 1))`, based at the first coordinate vector `e₀`, while the generator `ι` lives on the
sphere of `ℝ^(n + 2)`, based at the north pole, the last coordinate vector. The two spheres are
identified by a permutation of the coordinates, and the action of `SO(1 + (n + 1))` is transported
along it.

## Second proof: the plane-rotation family and homological degree

For any `(m + 2)`-dimensional real inner product space `E` and base point `p` of its unit sphere
`Sᵐ⁺¹`, a unit vector `v` in `p^⊥` and an angle `z ∈ S¹` determine an oriented plane
`ℂ →ₗᵢ[ℝ] E` (`TauCeti.sphereRotationPlane`) and a plane rotation `LinearIsometry.planeRotation` of
`E`. Restricting to the unit sphere gives a continuous family of `C^k` diffeomorphisms
`Sᵐ × S¹ → Diff(Sᵐ⁺¹)` (`TauCeti.sphereRotationToDiff`) whose evaluation at `p` is the rotation
family `TauCeti.sphereRotationFamily p` (`TauCeti.evalAt_comp_sphereRotationToDiff`).

Since `Sᵐ⁺¹` contains a unit vector `q` orthogonal to `p`, hence distinct from `±p`, `q` is a
regular value at which `sphereRotationFamily p` has smooth degree `1 + (-1) ^ m`
(`Orientation.degreeAtRegularValue_sphereRotationFamily`). Comparing smooth and homological degrees
on the product `Sᵐ × S¹`
(`TauCeti.Manifold.Orientation.mapFundamentalClass_prod_eq_degreeAtRegularValue_smul`),
the product fundamental class pushes forward to `(1 + (-1) ^ m) • [Sᵐ⁺¹]`
(`TauCeti.mapFundamentalClass_sphereRotationFamily`), so `Sᵐ⁺¹` is `(1 + (-1) ^ m)`-covered by
diffeomorphisms (`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere`). In particular,
every odd-dimensional sphere `Sⁿ` is `2`-covered by diffeomorphisms, unconditionally and without any
homotopy-group input (`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_two_of_odd`,
`TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_sphere_of_odd`).

## Main results

* `TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_sphere_of_isMulTorsion`: if
  `πₙ(SO(n + 1))` is a torsion group, `Sⁿ⁺¹` is `ℓ`-covered by diffeomorphisms for some `ℓ > 0`
  (first proof of Proposition 6.34).
* `TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_sphere_three`: the case of
  `S³` via `π₂(SO(3)) = 0`.
* `TauCeti.sphereRotationToDiff` and `TauCeti.evalAt_comp_sphereRotationToDiff`: the plane-rotation
  family `Sᵐ × S¹ → Diff(Sᵐ⁺¹)` lifting `TauCeti.sphereRotationFamily`.
* `TauCeti.mapFundamentalClass_sphereRotationFamily`: `sphereRotationFamily p` sends `[Sᵐ × S¹]` to
  `(1 + (-1) ^ m) • [Sᵐ⁺¹]`.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere`: `Sᵐ⁺¹` is
  `(1 + (-1) ^ m)`-covered by diffeomorphisms.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_two_of_odd` and
  `TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_sphere_of_odd`: every
  odd-dimensional sphere `Sⁿ` is `2`-covered (hence `ℓ`-covered for some `ℓ > 0`) by
  diffeomorphisms (second proof of Proposition 6.34).

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3, Proposition 6.34 and Lemma 6.35.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2.
-/

public section

noncomputable section

open CategoryTheory Matrix Metric Module
open scoped Manifold ContDiff EuclideanSpace TauCeti.DiffeomorphWeakWhitney Topology.Homotopy

namespace TauCeti

variable (n : ℕ)

/-- The reindexing of coordinates `Fin (1 + (n + 1)) ≃ Fin (n + 2)` sending the first coordinate to
the last one. -/
private def firstToLast : Fin (1 + (n + 1)) ≃ Fin (n + 2) :=
  (finCongr (by omega)).trans (finRotate (n + 2)).symm

private theorem firstToLast_zero : firstToLast n 0 = Fin.last (n + 1) := by
  rw [firstToLast, Equiv.trans_apply, Equiv.symm_apply_eq, finRotate_last]
  simp

/-- The linear isometry `ℝ^(1 + (n + 1)) ≃ ℝ^(n + 2)` permuting the coordinates by
`firstToLast`, which sends the first coordinate vector to the last. -/
private def firstToLastIsometry :
    EuclideanSpace ℝ (Fin (1 + (n + 1))) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 2)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (firstToLast n)

private theorem firstToLastIsometry_single_zero :
    firstToLastIsometry n (EuclideanSpace.single 0 1) =
      EuclideanSpace.single (Fin.last (n + 1)) 1 := by
  rw [firstToLastIsometry, EuclideanSpace.piLpCongrLeft_single, firstToLast_zero]

private theorem firstToLastIsometry_symm_single_last :
    (firstToLastIsometry n).symm (EuclideanSpace.single (Fin.last (n + 1)) 1) =
      EuclideanSpace.single 0 1 := by
  rw [LinearIsometryEquiv.symm_apply_eq, firstToLastIsometry_single_zero]

/-- The restriction of `firstToLastIsometry` to the unit spheres. -/
private def firstToLastSphere :
    C(sphere (0 : EuclideanSpace ℝ (Fin (1 + (n + 1)))) 1,
      sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
  ⟨(firstToLastIsometry n).toLinearIsometry.unitSphereMap,
    LinearIsometry.continuous_unitSphereMap _⟩

/-- The restriction of the inverse of `firstToLastIsometry` to the unit spheres. -/
private def lastToFirstSphere :
    C(sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
      sphere (0 : EuclideanSpace ℝ (Fin (1 + (n + 1)))) 1) :=
  ⟨(firstToLastIsometry n).symm.toLinearIsometry.unitSphereMap,
    LinearIsometry.continuous_unitSphereMap _⟩

private theorem firstToLastSphere_comp_lastToFirstSphere :
    (firstToLastSphere n).comp (lastToFirstSphere n) = ContinuousMap.id _ := by
  ext x : 2
  simp [firstToLastSphere, lastToFirstSphere]

private theorem firstToLastSphere_one :
    firstToLastSphere n (specialOrthogonalSphereMap (n + 1) 1) = sphereNorthPole (n + 1) := by
  have h : WithLp.toLp 2 ((1 : Matrix (Fin (1 + (n + 1))) (Fin (1 + (n + 1))) ℝ).col 0) =
      EuclideanSpace.single 0 1 := by
    ext i
    simp [Matrix.one_apply]
  ext : 1
  simp [firstToLastSphere, h, firstToLastIsometry_single_zero]

private theorem lastToFirstSphere_sphereNorthPole :
    lastToFirstSphere n (sphereNorthPole (n + 1)) = specialOrthogonalSphereMap (n + 1) 1 := by
  rw [← firstToLastSphere_one]
  ext : 1
  simp [firstToLastSphere, lastToFirstSphere]

/-- The linear isometry of a rotation of `ℝ^(1 + (n + 1))`, conjugated by `firstToLastIsometry`
to a linear isometry of `ℝ^(n + 2)`, depends continuously on the rotation. -/
private theorem continuous_firstToLastIsometry_conj :
    Continuous fun A : specialOrthogonalGroup (Fin (1 + (n + 1))) ℝ ↦
      (((firstToLastIsometry n).symm.trans ((UnitaryGroup.toLinearIsometryEquiv
        ⟨A.1, A.2.1⟩).trans (firstToLastIsometry n))).toContinuousLinearEquiv :
          EuclideanSpace ℝ (Fin (n + 2)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 2))) := by
  let f := ((firstToLastIsometry n).toContinuousLinearEquiv :
    EuclideanSpace ℝ (Fin (1 + (n + 1))) →L[ℝ] EuclideanSpace ℝ (Fin (n + 2)))
  let g := ((firstToLastIsometry n).symm.toContinuousLinearEquiv :
    EuclideanSpace ℝ (Fin (n + 2)) →L[ℝ] EuclideanSpace ℝ (Fin (1 + (n + 1))))
  have h := UnitaryGroup.continuous_toLinearIsometryEquiv.comp
    (continuous_subtype_val.subtype_mk
      fun A : specialOrthogonalGroup (Fin (1 + (n + 1))) ℝ ↦ A.2.1)
  refine ((continuous_const (y := f)).clm_comp (h.clm_comp (continuous_const (y := g)))).congr
    fun A ↦ ?_
  ext x : 1
  simp [f, g]

/-- The rotations `SO(n + 2)` act on the sphere `Sⁿ⁺¹ ⊆ ℝⁿ⁺²` by diffeomorphisms, after conjugating
by `firstToLastIsometry`; this is a continuous map into `Diff(Sⁿ⁺¹)`. -/
private def rotationToDiffSphere (m : ℕ∞ω) :
    C(specialOrthogonalGroup (Fin (1 + (n + 1))) ℝ,
      Diff (𝓡 (n + 1)) (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) m) where
  toFun A := LinearIsometryEquiv.unitSphereDiffHom m ((firstToLastIsometry n).symm.trans
    ((UnitaryGroup.toLinearIsometryEquiv ⟨A.1, A.2.1⟩).trans (firstToLastIsometry n)))
  continuous_toFun := by
    refine Diffeomorph.continuous_weakWhitney_iff.mpr ?_
    simpa only [LinearIsometryEquiv.unitSphereDiffHom_apply] using
      (continuous_firstToLastIsometry_conj n).toContMDiffMap_unitSphereDiffeomorph

/-- The orbit map of the north pole under the rotation action: `A ↦ A e₀`, followed by the
reindexing of the sphere that sends `e₀` to the north pole. -/
private abbrev rotationOrbitMap :
    C(specialOrthogonalGroup (Fin (1 + (n + 1))) ℝ,
      sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
  (firstToLastSphere n).comp
    ⟨specialOrthogonalSphereMap (n + 1), continuous_specialOrthogonalSphereMap (n + 1)⟩

private theorem rotationOrbitMap_one : rotationOrbitMap n 1 = sphereNorthPole (n + 1) :=
  firstToLastSphere_one n

/-- Evaluating the rotation action at the north pole is the orbit map of the north pole. -/
private theorem evalAt_comp_rotationToDiffSphere (m : ℕ∞ω) :
    (Diffeomorph.evalAt (sphereNorthPole (n + 1))).comp (rotationToDiffSphere n m) =
      rotationOrbitMap n := by
  ext A : 2
  simp [rotationToDiffSphere, rotationOrbitMap, firstToLastSphere,
    firstToLastIsometry_symm_single_last]

/-- The generator of `πₙ₊₁(Sⁿ⁺¹)` at the north pole, the class of the collapse map of the cube. -/
private def sphereGenClass :
    HomotopyGroup (Fin (n + 1)) (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
      (sphereNorthPole (n + 1)) :=
  ⟦sphereGenLoop (n + 1)⟧

variable {n}

/-- If `πₙ(SO(n + 1))` is a torsion group, then a positive power of the generator of
`πₙ₊₁(Sⁿ⁺¹)` is the image of a class of `πₙ₊₁(SO(n + 2))` under the orbit map of the north pole.
This is the exact sequence of `SO(n + 1) → SO(n + 2) → Sⁿ⁺¹` at `πₙ₊₁(Sⁿ⁺¹)`, read through the
reindexings of the cube directions and of the coordinates. -/
private theorem exists_map_rotationOrbitMap_eq_pow [NeZero n]
    (h : IsMulTorsion (HomotopyGroup (Fin n) (specialOrthogonalGroup (Fin (n + 1)) ℝ) 1)) :
    ∃ k, 0 < k ∧ ∃ b : HomotopyGroup (Fin (n + 1)) (specialOrthogonalGroup (Fin (1 + (n + 1))) ℝ) 1,
      HomotopyGroup.map (rotationOrbitMap n) (rotationOrbitMap_one n) b =
        sphereGenClass n ^ k := by
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  -- The exact sequence models `πₙ₊₁` on the cube `I^(Option (Fin n))`.
  let e : Option (Fin n) ≃ Fin (n + 1) := (finSuccEquiv n).symm
  let ι := sphereGenClass n
  let a := (HomotopyGroup.congrMulEquiv e).symm
    (HomotopyGroup.map (lastToFirstSphere n) (lastToFirstSphere_sphereNorthPole n) ι)
  obtain ⟨k, hk, b, hb⟩ :=
    exists_pow_mem_range_homotopyGroupMap_specialOrthogonalSphereMap_of_isOfFinOrder
      (h (specialOrthogonalSphereBoundary (n + 1) (Fin n) a))
  refine ⟨k, hk, HomotopyGroup.congrMulEquiv e b, ?_⟩
  calc _ = HomotopyGroup.congrMulEquiv e (HomotopyGroup.map (firstToLastSphere n)
        (firstToLastSphere_one n) (HomotopyGroup.map _ rfl b)) := by
        rw [ContinuousMap.map_congrMulEquiv, HomotopyGroup.map_comp_apply]
    _ = HomotopyGroup.congrMulEquiv e (HomotopyGroup.map (firstToLastSphere n)
        (firstToLastSphere_one n) a) ^ k := by
        rw [hb, ← HomotopyGroup.mapHom_apply, map_pow, map_pow, HomotopyGroup.mapHom_apply]
    _ = ι ^ k := by
        rw [← ContinuousMap.map_congrMulEquiv, MulEquiv.apply_symm_apply,
          HomotopyGroup.map_map_of_comp_eq_id _ _ _ _
            (firstToLastSphere_comp_lastToFirstSphere n)]

/-- By naturality of the Hurewicz map, if the orbit map sends a class `b` of `πₙ₊₁(SO(n + 2))` to
the `k`-th power of the generator of `πₙ₊₁(Sⁿ⁺¹)`, then the Hurewicz class of the image of `b` is
`k` times that of the generator. -/
private theorem hurewicz_map_rotationOrbitMap_eq_nsmul {k : ℕ}
    {b : HomotopyGroup (Fin (n + 1)) (specialOrthogonalGroup (Fin (1 + (n + 1))) ℝ) 1}
    (hb : HomotopyGroup.map (rotationOrbitMap n) (rotationOrbitMap_one n) b =
      sphereGenClass n ^ k) :
    (HomotopyGroup.hurewicz (ModuleCat.of ℤ (ULift.{0} ℤ)) n
        (HomotopyGroup.map (rotationOrbitMap n) (rotationOrbitMap_one n) b)).hom (ULift.up 1) =
      k • (GenLoop.hurewicz (ModuleCat.of ℤ (ULift.{0} ℤ)) (sphereGenLoop (n + 1))).hom
        (ULift.up 1) := by
  rw [hb, HomotopyGroup.hurewicz_pow, sphereGenClass, HomotopyGroup.hurewicz_mk,
    ModuleCat.hom_nsmul, LinearMap.smul_apply]

/-- The Hurewicz class of the generator of `πₙ₊₁(Sⁿ⁺¹)` is nonzero. -/
private theorem hurewicz_sphereGenLoop_ne_zero :
    (GenLoop.hurewicz (ModuleCat.of ℤ (ULift.{0} ℤ)) (sphereGenLoop (n + 1))).hom (ULift.up 1) ≠
      0 := by
  have : IsIso (GenLoop.hurewicz (ModuleCat.of ℤ (ULift.{0} ℤ)) (sphereGenLoop (n + 1))) :=
    inferInstance
  have hinj := ((ConcreteCategory.isIso_iff_bijective _).1 this).1
  intro h
  rw [← map_zero (GenLoop.hurewicz (ModuleCat.of ℤ (ULift.{0} ℤ)) (sphereGenLoop (n + 1))).hom] at h
  exact one_ne_zero (congrArg ULift.down (hinj h))

/-- The statement of
`TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_sphere_of_isMulTorsion` at the
north pole, with a nonzero multiple of the fundamental class. -/
private theorem exists_ne_zero_isCoveredByDiffeomorphisms_sphereNorthPole [NeZero n]
    (h : IsMulTorsion (HomotopyGroup (Fin n) (specialOrthogonalGroup (Fin (n + 1)) ℝ) 1))
    (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
      (EuclideanSpace ℝ (Fin (n + 1))) (n + 1)) (m : ℕ∞ω) :
    ∃ ℓ : ℤ, ℓ ≠ 0 ∧
      o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin m (sphereNorthPole (n + 1)) ℓ := by
  have : ConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
    connectedSpace_euclideanSphere (by omega)
  let R := ModuleCat.of ℤ (ULift.{0} ℤ)
  obtain ⟨k, hk, b, hb⟩ := exists_map_rotationOrbitMap_eq_pow h
  -- The Hurewicz class of the generator is a multiple `c • [Sⁿ⁺¹]` of the fundamental class.
  obtain ⟨c, hc⟩ := o.exists_eq_zsmul_fundamentalClass finrank_euclideanSpace_fin
    ((GenLoop.hurewicz R (sphereGenLoop (n + 1))).hom (ULift.up 1))
  refine ⟨k * c, ?_, .of_homologyMap (rotationToDiffSphere n m)
    ((HomotopyGroup.hurewicz R n b).hom (ULift.up 1)) ?_⟩
  · refine mul_ne_zero (by exact_mod_cast hk.ne') ?_
    rintro rfl
    rw [zero_smul] at hc
    exact hurewicz_sphereGenLoop_ne_zero hc
  · -- By naturality of the Hurewicz map, the image of the class of `b` is that of the `k`-th power
    -- of the generator.
    rw [evalAt_comp_rotationToDiffSphere, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      ← HomotopyGroup.hurewicz_map R n _ (rotationOrbitMap_one n),
      hurewicz_map_rotationOrbitMap_eq_nsmul hb, o.mapFundamentalClass_id, hc]
    exact (natCast_zsmul _ k).symm.trans (mul_smul (k : ℤ) c _).symm

namespace HomologicalOrientation

/-- **Spheres covered by rotations** (the first proof of Proposition 6.34 of
Barraud–Damian–Humilière–Oancea). If `πₙ(SO(n + 1))` is a torsion group, then the sphere `Sⁿ⁺¹` is
`ℓ`-covered by diffeomorphisms for some `ℓ > 0`, at every base point, for every orientation and
every smoothness exponent.

By Lemma 6.35 of the same paper the torsion hypothesis holds whenever `n + 1` is odd. For
`n + 1 = 3` it is `π₂(SO(3)) = 0`, giving
`TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_sphere_three`. -/
theorem exists_isCoveredByDiffeomorphisms_sphere_of_isMulTorsion [NeZero n]
    (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
      (EuclideanSpace ℝ (Fin (n + 1))) (n + 1))
    (h : IsMulTorsion (HomotopyGroup (Fin n) (specialOrthogonalGroup (Fin (n + 1)) ℝ) 1))
    (m : ℕ∞ω) (x₀ : sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :
    ∃ ℓ : ℤ, 0 < ℓ ∧ o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin m x₀ ℓ := by
  have : PathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) :=
    isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_sphere (by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      exact_mod_cast (by omega : 1 < n + 2)) 0 zero_le_one)
  obtain ⟨ℓ, hℓ, hc⟩ := exists_ne_zero_isCoveredByDiffeomorphisms_sphereNorthPole h o m
  refine ⟨|ℓ|, abs_pos.2 hℓ, ?_⟩
  rw [← Int.sign_mul_self_eq_abs]
  exact ((isCoveredByDiffeomorphisms_iff_of_pathConnectedSpace _ x₀).1 hc).mul_left _

/-- **The `3`-sphere is covered by rotations**: since `π₂(SO(3)) = 0`, the sphere `S³` is
`ℓ`-covered by diffeomorphisms for some `ℓ > 0`. -/
theorem exists_isCoveredByDiffeomorphisms_sphere_three
    (o : HomologicalOrientation (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
      (EuclideanSpace ℝ (Fin 3)) 3)
    (m : ℕ∞ω) (x₀ : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
    ∃ ℓ : ℤ, 0 < ℓ ∧ o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin m x₀ ℓ := by
  have := subsingleton_homotopyGroup_specialOrthogonalGroup_three (N := Fin 2) (by simp) 1
  exact o.exists_isCoveredByDiffeomorphisms_sphere_of_isMulTorsion
    (fun g ↦ Subsingleton.elim g 1 ▸ IsOfFinOrder.one) m x₀

end HomologicalOrientation

/-! ### Plane-rotation covering of spheres -/

section PlaneRotation

open scoped RealInnerProductSpace

attribute [local instance] finrank_real_complex_fact'
attribute [local instance low] chartedSpaceProd

section Plane

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear isometry `ℂ →ₗᵢ[ℝ] E` carrying `1` to `p` and `i` to the unit tangent vector `v` of
the unit sphere of `E` at `p`: `z ↦ Re z • p + Im z • v`. -/
def sphereRotationPlane (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    ℂ →ₗᵢ[ℝ] E :=
  LinearIsometry.ofOrthonormalPair (norm_eq_of_mem_sphere p) (norm_eq_of_mem_sphere v)
    (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (v : (ℝ ∙ (p : E))ᗮ).2)

/-- `sphereRotationPlane p v` sends `z` to `Re z • p + Im z • v`. -/
@[simp]
theorem sphereRotationPlane_apply (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)
    (z : ℂ) :
    sphereRotationPlane p v z = z.re • (p : E) + z.im • ((v : (ℝ ∙ (p : E))ᗮ) : E) := by
  simp [sphereRotationPlane]

/-- `sphereRotationPlane p v` carries `1 : ℂ` to `p`. -/
theorem sphereRotationPlane_one (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    sphereRotationPlane p v 1 = p := by
  simp

/-- Every point `p` of `Sᵐ⁺¹` admits an orthogonal point `q` of `Sᵐ⁺¹`, which is in particular
distinct from both `p` and `-p`. -/
private theorem exists_ne_and_ne_neg_sphere {m : ℕ} (hm : finrank ℝ E = m + 1 + 1)
    (p : sphere (0 : E) 1) : ∃ q : sphere (0 : E) 1, q ≠ p ∧ q ≠ -p := by
  have : Fact (finrank ℝ E = m + 1 + 1) := ⟨hm⟩
  have : FiniteDimensional ℝ (ℝ ∙ (p : E))ᗮ := .of_fact_finrank_eq_succ m
  have : Nontrivial (ℝ ∙ (p : E))ᗮ := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [Fact.out (p := finrank ℝ (ℝ ∙ (p : E))ᗮ = m + 1)]
    exact Nat.succ_pos m)
  obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : (ℝ ∙ (p : E))ᗮ)) (r := 1)).2
    zero_le_one
  let v₀ : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 := ⟨v, hv⟩
  let q : sphere (0 : E) 1 :=
    ⟨((v₀ : (ℝ ∙ (p : E))ᗮ) : E), mem_sphere_zero_iff_norm.2 (norm_eq_of_mem_sphere v₀)⟩
  have hpq : ⟪(p : E), (q : E)⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 (v₀ : (ℝ ∙ (p : E))ᗮ).2
  have hpp : ⟪(p : E), (p : E)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
  refine ⟨q, fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congrArg (fun y : sphere (0 : E) 1 ↦ ⟪(p : E), (y : E)⟫) h
    linarith [hpq, hpp]
  · have := congrArg (fun y : sphere (0 : E) 1 ↦ ⟪(p : E), (y : E)⟫) h
    simp only [coe_neg_sphere, inner_neg_right] at this
    linarith [hpq, hpp]

end Plane

section DimensionSucc

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ} [Fact (finrank ℝ E = m + 1 + 1)]

/-- Rotating `E` in the oriented plane spanned by `p` and `v` by the angle of `z ∈ S¹` restricts to
a continuous family of `C^k` diffeomorphisms `Sᵐ × S¹ → Diff(Sᵐ⁺¹)`. -/
def sphereRotationToDiff (p : sphere (0 : E) 1) (k : ℕ∞ω) :
    C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1,
      Diff (𝓡 (m + 1)) (sphere (0 : E) 1) k) where
  toFun x := LinearIsometryEquiv.unitSphereDiffeomorph
    ((sphereRotationPlane p x.1).planeRotation (Circle.homeomorphSphere.symm x.2)) k
  continuous_toFun := by
    refine Diffeomorph.continuous_weakWhitney_iff.mpr ?_
    have hplane : Continuous fun x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦
        (sphereRotationPlane p x.1).toContinuousLinearMap :=
      Continuous.ofOrthonormalPair_toContinuousLinearMap continuous_const
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
        (fun _ ↦ norm_eq_of_mem_sphere p) (fun x ↦ norm_eq_of_mem_sphere x.1)
        (fun x ↦ Submodule.mem_orthogonal_singleton_iff_inner_right.1 (x.1 : (ℝ ∙ (p : E))ᗮ).2)
    have hrot : Continuous fun x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦
        (((sphereRotationPlane p x.1).planeRotation
          (Circle.homeomorphSphere.symm x.2)).toContinuousLinearEquiv : E →L[ℝ] E) :=
      hplane.planeRotation_toContinuousLinearMap
        (Circle.homeomorphSphere.symm.continuous.comp continuous_snd)
    exact hrot.toContMDiffMap_unitSphereDiffeomorph

/-- Evaluation of `TauCeti.sphereRotationToDiff` on a pair `(v, z)` in `Sᵐ × S¹`. -/
@[simp]
theorem sphereRotationToDiff_apply (p : sphere (0 : E) 1) (k : ℕ∞ω)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    sphereRotationToDiff (m := m) p k x =
      LinearIsometryEquiv.unitSphereDiffeomorph
        ((sphereRotationPlane p x.1).planeRotation (Circle.homeomorphSphere.symm x.2)) k :=
  (rfl)

/-- Evaluating the plane-rotation family of diffeomorphisms at `p` recovers
`TauCeti.sphereRotationFamily p`. -/
theorem evalAt_comp_sphereRotationToDiff (p : sphere (0 : E) 1) (k : ℕ∞ω) :
    (Diffeomorph.evalAt (I := 𝓡 (m + 1)) p).comp (sphereRotationToDiff (m := m) p k) =
      ⟨sphereRotationFamily p, (contMDiff_sphereRotationFamily (m := m) p).continuous⟩ := by
  ext x : 2
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Diffeomorph.evalAt_apply,
    sphereRotationToDiff_apply, LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply,
    coe_sphereRotationFamily]
  calc ((sphereRotationPlane p x.1).planeRotation (Circle.homeomorphSphere.symm x.2)) (p : E)
      = ((sphereRotationPlane p x.1).planeRotation (Circle.homeomorphSphere.symm x.2))
          (sphereRotationPlane p x.1 1) := by rw [sphereRotationPlane_one]
    _ = (x.2 : ℂ).re • (p : E) + (x.2 : ℂ).im • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) := by
        rw [LinearIsometry.planeRotation_apply_map, mul_one, Circle.coe_homeomorphSphere_symm_apply,
          sphereRotationPlane_apply]

/-- Pushing forward the product fundamental class of `Sᵐ × S¹` along `sphereRotationFamily p`
yields `(1 + (-1) ^ m)` times the fundamental class of `Sᵐ⁺¹`. -/
theorem mapFundamentalClass_sphereRotationFamily
    (oE : _root_.Orientation ℝ E (Fin (m + 1 + 1))) (p : sphere (0 : E) 1)
    (hdim : finrank ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 1)) = m + 1 := by
      rw [finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]) :
    (((oE.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere p)).sphereOrientation.prod
        Complex.orientation.sphereOrientation).toHomologicalOrientationProd
        hdim).mapFundamentalClass hdim
      ⟨sphereRotationFamily p, (contMDiff_sphereRotationFamily (m := m) p).continuous⟩ =
    (1 + (-1) ^ m) •
      (oE.sphereOrientation.toHomologicalOrientation finrank_euclideanSpace_fin).fundamentalClass
        finrank_euclideanSpace_fin := by
  have : ConnectedSpace (sphere (0 : E) 1) := connectedSpace_sphere (m + 1)
  obtain ⟨q, hqp, hqp'⟩ := exists_ne_and_ne_neg_sphere (m := m) Fact.out p
  refine (Manifold.Orientation.mapFundamentalClass_prod_eq_degreeAtRegularValue_smul hdim
    finrank_euclideanSpace_fin _ oE.sphereOrientation
    (isRegularValue_sphereRotationFamily p hqp hqp')).trans ?_
  rw [ContinuousMap.coe_mk, oE.degreeAtRegularValue_sphereRotationFamily p hqp hqp']
  -- `mapFundamentalClass` and `fundamentalClass` have definitionally equal carrier types
  -- (`singularHomologyFunctor` vs `SSet.homology`).
  rfl

namespace HomologicalOrientation

/-- **Spheres covered by plane rotations** (Proposition 6.34 of Barraud–Damian–Humilière–Oancea,
second proof). For an `(m + 2)`-dimensional real inner product space `E`, the unit sphere `Sᵐ⁺¹`
of `E` is `(1 + (-1) ^ m)`-covered by `C^k` diffeomorphisms at every base point, for every
orientation and every smoothness exponent `k`. -/
theorem isCoveredByDiffeomorphisms_sphere
    (o : HomologicalOrientation (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (k : ℕ∞ω) (x₀ : sphere (0 : E) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ (1 + (-1) ^ m) := by
  have : ConnectedSpace (sphere (0 : E) 1) := connectedSpace_sphere (m + 1)
  let oE : _root_.Orientation ℝ E (Fin (m + 1 + 1)) :=
    (Module.finBasisOfFinrankEq ℝ E Fact.out).orientation
  let o₀ := oE.sphereOrientation.toHomologicalOrientation finrank_euclideanSpace_fin
  have ho₀ : o₀.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ (1 + (-1) ^ m) := by
    have hdim : finrank ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 1)) = m + 1 := by
      rw [finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
    refine .of_mapFundamentalClass
      (((oE.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere x₀)).sphereOrientation.prod
        Complex.orientation.sphereOrientation).toHomologicalOrientationProd hdim)
      hdim (sphereRotationToDiff (m := m) x₀ k) ?_
    rw [evalAt_comp_sphereRotationToDiff, o₀.mapFundamentalClass_id]
    exact mapFundamentalClass_sphereRotationFamily oE x₀ hdim
  rcases o₀.eq_or_eq_neg finrank_euclideanSpace_fin o with rfl | rfl
  · exact ho₀
  · exact isCoveredByDiffeomorphisms_neg.2 ho₀

end HomologicalOrientation

end DimensionSucc

namespace HomologicalOrientation

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- **Odd-dimensional spheres are `2`-covered by diffeomorphisms** (Proposition 6.34 of
Barraud–Damian–Humilière–Oancea, second proof). For every odd `n`, the unit sphere `Sⁿ` of an
`(n + 1)`-dimensional real inner product space `E` is `2`-covered by `C^k` diffeomorphisms at every
base point, for every orientation and every smoothness exponent `k`. -/
theorem isCoveredByDiffeomorphisms_sphere_two_of_odd
    (o : HomologicalOrientation (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)) n)
    (hn : Odd n) (k : ℕ∞ω) (x₀ : sphere (0 : E) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ 2 := by
  obtain ⟨d, rfl⟩ := hn
  have h := o.isCoveredByDiffeomorphisms_sphere (m := 2 * d) k x₀
  rwa [(even_two_mul d).neg_one_pow, one_add_one_eq_two] at h

/-- **Odd-dimensional spheres are `ℓ`-covered by diffeomorphisms for some `ℓ > 0`** (Proposition
6.34 of Barraud–Damian–Humilière–Oancea, second proof). When `n` is odd, `Sⁿ` is `ℓ`-covered by
`C^k` diffeomorphisms for some `ℓ > 0`, without any torsion hypothesis on homotopy groups of
orthogonal groups. -/
theorem exists_isCoveredByDiffeomorphisms_sphere_of_odd
    (o : HomologicalOrientation (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)) n)
    (hn : Odd n) (k : ℕ∞ω) (x₀ : sphere (0 : E) 1) :
    ∃ ℓ : ℤ, 0 < ℓ ∧ o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin k x₀ ℓ :=
  ⟨2, two_pos, o.isCoveredByDiffeomorphisms_sphere_two_of_odd hn k x₀⟩

end HomologicalOrientation

end PlaneRotation

end TauCeti

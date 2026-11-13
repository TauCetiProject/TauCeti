/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Sphere
public import TauCeti.Geometry.Diffeomorphism.Covered
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Sphere.Connected
public import TauCeti.Topology.Grassmannian.SphereBundle.Exact
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
import TauCeti.Analysis.Complex.Circle
import TauCeti.Analysis.InnerProductSpace.PlaneRotation
import TauCeti.Geometry.Manifold.Degree.Homological
import TauCeti.Geometry.Manifold.Degree.SphereRotation
import TauCeti.Geometry.Manifold.Instances.EuclideanProd
import TauCeti.Geometry.Manifold.Orientation.Pullback
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.HomotopyGroup

/-!
# Spheres covered by rotations

A compact oriented `d`-manifold `M` is `ℓ`-covered by diffeomorphisms when some class of
`H_d(Diff(M); ℤ)` evaluates to `ℓ • [M]`
(`TauCeti.HomologicalOrientation.IsCoveredByDiffeomorphisms`).
For the sphere `Sⁿ⁺¹ ⊆ ℝⁿ⁺²` such classes come from rotations acting on the sphere by
diffeomorphisms. This file gives both proofs of Proposition 6.34 of
Barraud–Damian–Humilière–Oancea.

## First proof (via `πₙ(SO(n + 1))`)

The rotation group `SO(n + 2)` acts on `Sⁿ⁺¹` (`TauCeti.continuousOrthogonalToDiffSphere`) with
orbit map the fibration `SO(n + 1) → SO(n + 2) → Sⁿ⁺¹`. If `πₙ(SO(n + 1))` is a torsion group,
then `Sⁿ⁺¹` is `ℓ`-covered by diffeomorphisms for some `ℓ > 0`:

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

## Second proof (odd spheres via planar rotations)

Directly for every odd-dimensional sphere `Sᵐ⁺¹` (`Even m`) in an `(m + 2)`-dimensional real inner
product space `E`, planar rotations in the 2-planes `span {x₀, v}` (`(v, z) ∈ Sᵐ × S¹`) form a
continuous family into `Diff(Sᵐ⁺¹)` whose evaluation at `x₀` is the rotation family
`TauCeti.sphereRotationFamily x₀ : Sᵐ × S¹ → Sᵐ⁺¹`. Recharting `Sᵐ × S¹` on
`EuclideanSpace ℝ (Fin (m + 1))` (`TauCeti.prodEuclideanChartedSpace`), the rotation family has
degree `2` (`Orientation.degreeAtRegularValue_sphereRotationFamily_of_even`), so its image of the
fundamental class is `2 • [Sᵐ⁺¹]`, showing that `Sᵐ⁺¹` is `2`-covered by diffeomorphisms
(`TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_of_even`).

## Main results

* `TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_sphere_of_isMulTorsion`: if
  `πₙ(SO(n + 1))` is a torsion group, `Sⁿ⁺¹` is `ℓ`-covered by diffeomorphisms for some `ℓ > 0`.
* `TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_sphere_three`: the case of
  `S³`.
* `TauCeti.HomologicalOrientation.isCoveredByDiffeomorphisms_sphere_of_even`: every odd-dimensional
  sphere `Sᵐ⁺¹` (`Even m`) is `2`-covered by diffeomorphisms.

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

section SecondProof

attribute [local instance] finrank_real_complex_fact'

open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ} [Fact (finrank ℝ E = m + 1 + 1)]

/-- The isometric embedding `ℂ →ₗᵢ[ℝ] E` sending `1` to `p` and `i` to a unit tangent vector `v`
at `p`. -/
private def planeEmbedding (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    ℂ →ₗᵢ[ℝ] E :=
  LinearIsometry.complexOfOrthonormal (norm_eq_of_mem_sphere p) (norm_eq_of_mem_sphere v)
    (Submodule.mem_orthogonal_singleton_iff_inner_right.1 v.1.2)

omit [FiniteDimensional ℝ E] in
private theorem continuous_planeEmbedding (p : sphere (0 : E) 1) :
    Continuous fun x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦
      (planeEmbedding p x.1).toContinuousLinearMap :=
  LinearIsometry.continuous_toContinuousLinearMap_complexOfOrthonormal continuous_const
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
    (fun _ ↦ norm_eq_of_mem_sphere p) (fun x ↦ norm_eq_of_mem_sphere x.1)
    fun x ↦ Submodule.mem_orthogonal_singleton_iff_inner_right.1 x.1.1.2

/-- The planar rotations `(v, z) ↦ planeRotation (p, v) z` as a continuous map from `Sᵐ × S¹`
into `Diff(Sᵐ⁺¹)`. -/
private def rotationFamilyToDiffSphere (p : sphere (0 : E) 1) (r : ℕ∞ω) :
    C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1,
      Diff (𝓡 (m + 1)) (sphere (0 : E) 1) r) where
  toFun x := LinearIsometryEquiv.unitSphereDiffHom r
    ((planeEmbedding p x.1).planeRotation (Circle.homeomorphSphere.symm x.2))
  continuous_toFun := by
    refine Diffeomorph.continuous_weakWhitney_iff.mpr ?_
    have hc : Continuous fun x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦
        Circle.homeomorphSphere.symm x.2 :=
      Circle.homeomorphSphere.symm.continuous.comp continuous_snd
    simpa only [LinearIsometryEquiv.unitSphereDiffHom_apply] using
      (LinearIsometry.continuous_toContinuousLinearEquiv_planeRotation
        (continuous_planeEmbedding p) hc).toContMDiffMap_unitSphereDiffeomorph

/-- Evaluating the planar-rotation family at `p` yields `TauCeti.sphereRotationFamily p`. -/
private theorem evalAt_comp_rotationFamilyToDiffSphere (p : sphere (0 : E) 1) (r : ℕ∞ω) :
    (Diffeomorph.evalAt (I := 𝓡 (m + 1)) p).comp (rotationFamilyToDiffSphere p r) =
      ⟨sphereRotationFamily p, (contMDiff_sphereRotationFamily (m := m) p).continuous⟩ := by
  ext x : 2
  simp only [ContinuousMap.comp_apply, Diffeomorph.evalAt_apply, rotationFamilyToDiffSphere,
    ContinuousMap.coe_mk, LinearIsometryEquiv.unitSphereDiffHom_apply,
    LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply, coe_sphereRotationFamily]
  calc ((planeEmbedding p x.1).planeRotation (Circle.homeomorphSphere.symm x.2)) (p : E)
      = ((planeEmbedding p x.1).planeRotation (Circle.homeomorphSphere.symm x.2))
          (planeEmbedding p x.1 1) :=
        congrArg _ (LinearIsometry.complexOfOrthonormal_one (norm_eq_of_mem_sphere p)
          (norm_eq_of_mem_sphere x.1)
          (Submodule.mem_orthogonal_singleton_iff_inner_right.1 x.1.1.2)).symm
    _ = planeEmbedding p x.1 ((Circle.homeomorphSphere.symm x.2 : Circle) * (1 : ℂ)) :=
        LinearIsometry.planeRotation_apply_map _ _ _
    _ = (x.2 : ℂ).re • (p : E) + (x.2 : ℂ).im • ((x.1 : (ℝ ∙ (p : E))ᗮ) : E) := by
        rw [mul_one, planeEmbedding, LinearIsometry.complexOfOrthonormal_apply,
          Circle.coe_homeomorphSphere_symm_apply]
        rfl

namespace HomologicalOrientation

/-- **Odd spheres are `2`-covered by diffeomorphisms** (second proof of Proposition 6.34 of
Barraud–Damian–Humilière–Oancea). Directly without any homotopy-group torsion hypothesis, for
every odd-dimensional unit sphere `Sᵐ⁺¹` (`Even m`) in an `(m + 2)`-dimensional real inner product
space `E`, every homological orientation, every smoothness exponent `r`, and every base point `x₀`,
`Sᵐ⁺¹` is `2`-covered by `C^r` diffeomorphisms. -/
theorem isCoveredByDiffeomorphisms_sphere_of_even
    (o : HomologicalOrientation (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin (m + 1))) (m + 1))
    (hm : Even m) (r : ℕ∞ω) (x₀ : sphere (0 : E) 1) :
    o.IsCoveredByDiffeomorphisms finrank_euclideanSpace_fin r x₀ 2 := by
  have : ConnectedSpace (sphere (0 : E) 1) := connectedSpace_sphere (m + 1)
  -- Pick a point `q ≠ ±x₀` from a unit vector orthogonal to `x₀`.
  have : Nontrivial (ℝ ∙ (x₀ : E))ᗮ := Module.nontrivial_of_finrank_pos (R := ℝ) (by
    rw [(fact_finrank_orthogonal_span_singleton_coe_sphere (n := m) x₀).out]
    omega)
  obtain ⟨w, hw⟩ := exists_ne (0 : (ℝ ∙ (x₀ : E))ᗮ)
  let v₀ : sphere (0 : (ℝ ∙ (x₀ : E))ᗮ) 1 := ⟨‖w‖⁻¹ • w, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)]⟩
  let q : sphere (0 : E) 1 :=
    ⟨((v₀ : (ℝ ∙ (x₀ : E))ᗮ) : E), mem_sphere_zero_iff_norm.2 (norm_eq_of_mem_sphere v₀)⟩
  have hqx : q ≠ x₀ := by
    intro h
    have hin : ⟪(x₀ : E), (q : E)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 v₀.1.2
    rw [h, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere x₀, one_pow] at hin
    exact zero_ne_one hin.symm
  have hqx' : q ≠ -x₀ := by
    intro h
    have hin : ⟪(x₀ : E), (q : E)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 v₀.1.2
    rw [h] at hin
    simp only [coe_neg_sphere, inner_neg_right, real_inner_self_eq_norm_sq,
      norm_eq_of_mem_sphere x₀, one_pow] at hin
    linarith
  -- Choose a reference orientation of `E` and orient `Sᵐ⁺¹` and `Sᵐ × S¹`.
  let oE : _root_.Orientation ℝ E (Fin (m + 1 + 1)) :=
    (finBasisOfFinrankEq ℝ E Fact.out).orientation
  let oQ : Manifold.Orientation (𝓡 (m + 1)) (sphere (0 : E) 1) (Fin (m + 1)) :=
    oE.sphereOrientation
  let oP : Manifold.Orientation ((𝓡 m).prod (𝓡 1))
      (sphere (0 : (ℝ ∙ (x₀ : E))ᗮ) 1 × sphere (0 : ℂ) 1) (Fin (m + 1)) :=
    (oE.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere x₀)).sphereOrientation.prod
      Complex.orientation.sphereOrientation
  -- Rechart `Sᵐ × S¹` on `EuclideanSpace ℝ (Fin (m + 1))` and pull back `oP`.
  let := prodEuclideanChartedSpace (𝕜 := ℝ) (n := m) (m := 1)
    (M := sphere (0 : (ℝ ∙ (x₀ : E))ᗮ) 1) (N := sphere (0 : ℂ) 1)
  have := isManifold_prodEuclideanChartedSpace (𝕜 := ℝ) (n := m) (m := 1)
    (M := sphere (0 : (ℝ ∙ (x₀ : E))ᗮ) 1) (N := sphere (0 : ℂ) 1) 1
  let e := prodEuclideanDiffeomorph (𝕜 := ℝ) (n := m) (m := 1)
    (M := sphere (0 : (ℝ ∙ (x₀ : E))ᗮ) 1) (N := sphere (0 : ℂ) 1) 1
  let oP' : Manifold.Orientation (𝓡 (m + 1))
      (sphere (0 : (ℝ ∙ (x₀ : E))ᗮ) 1 × sphere (0 : ℂ) 1) (Fin (m + 1)) :=
    oP.pullback (e.contMDiff.of_le le_rfl) (fun _ ↦ e.isInvertible_mfderiv one_ne_zero)
      (by simp)
  have hreg : IsRegularValue (𝓡 (m + 1)) (𝓡 (m + 1)) (sphereRotationFamily x₀) q := by
    have hcomp := (isRegularValue_sphereRotationFamily x₀ hqx hqx').comp
      (K := 𝓡 (m + 1)) (g := e) fun p _ ↦
        isRegularPoint_iff.2 (e.isInvertible_mfderiv one_ne_zero (x := p)).surjective
    simpa [Function.comp_def, e] using hcomp
  have hdeg : degreeAtRegularValue oP' oQ (sphereRotationFamily x₀) q = 2 := by
    have hcomp := degreeAtRegularValue_comp_of_isOrientationPreservingAt oP' e.bijective
      (fun p _ ↦ ((contMDiff_sphereRotationFamily (m := m) x₀).mdifferentiable (by simp)) (e p))
      (fun p _ ↦ e.mdifferentiable one_ne_zero p)
      (fun p _ ↦ Manifold.Orientation.isOrientationPreservingAt_pullback _ _ _ _ p)
      (f := sphereRotationFamily x₀) (o := oP) (o' := oQ) (y := q)
    simp only [e, Diffeomorph.coe_toEquiv, coe_prodEuclideanDiffeomorph, Function.comp_id] at hcomp
    exact hcomp.trans (oE.degreeAtRegularValue_sphereRotationFamily_of_even x₀ hm hqx hqx')
  have hcov : (oQ.toHomologicalOrientation finrank_euclideanSpace_fin).IsCoveredByDiffeomorphisms
      finrank_euclideanSpace_fin r x₀ 2 := by
    refine .of_mapFundamentalClass (oP'.toHomologicalOrientation finrank_euclideanSpace_fin)
      finrank_euclideanSpace_fin (rotationFamilyToDiffSphere x₀ r) ?_
    rw [evalAt_comp_rotationFamilyToDiffSphere]
    exact (Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul
      finrank_euclideanSpace_fin oP' oQ hreg).trans
      ((congrArg (· • _) hdeg).trans
        (congrArg ((2 : ℤ) • ·) (mapFundamentalClass_id _ _).symm))
  rcases HomologicalOrientation.eq_or_eq_neg finrank_euclideanSpace_fin o
      (oQ.toHomologicalOrientation finrank_euclideanSpace_fin) with ho | ho
  · rw [← ho]
    exact hcov
  · have hneg : o = -(oQ.toHomologicalOrientation finrank_euclideanSpace_fin) :=
      (neg_neg o).symm.trans (congrArg Neg.neg ho.symm)
    rw [hneg, isCoveredByDiffeomorphisms_neg]
    exact hcov

end HomologicalOrientation

end SecondProof

end TauCeti

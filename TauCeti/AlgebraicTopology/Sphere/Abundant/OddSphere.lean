/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.Abundant.Basic
import TauCeti.AlgebraicTopology.Sphere.Abundant.Action
import TauCeti.AlgebraicTopology.Sphere.DoubleTangentCircle
import TauCeti.Geometry.Diffeomorphism.Sphere.RotationFamily
import TauCeti.Topology.Grassmannian.SphereBundle.Orbit

/-!
# Odd-dimensional spheres are abundant with 2-spheres

**Theorem** (Barraud–Damian–Humilière–Oancea, Proposition 6.34). For odd `n ≥ 3`, the sphere
`Sⁿ` is abundant with 2-spheres, at every base point
(`TauCeti.isAbundantWithTwoSpheres_sphere_of_odd`).

The proof is the second proof of the source, through the abundance criterion for manifolds covered
by a group action (`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_ne_zero`,
the source's Propositions 6.29 and 6.33), applied to the rotation group `SO(n + 1)` acting on
`Sⁿ ⊆ ℝⁿ⁺¹` with its orbit map `g ↦ g • x₀`. That criterion asks for three things.

* **The orbit map.** It has continuous local sections and a path-connected stabilizer
  (`TauCeti.exists_continuousOn_specialOrthogonalGroup_smul_eq`,
  `TauCeti.isPathConnected_setOf_specialOrthogonalGroup_smul_eq`).
* **A class of `SO(n + 1)` over `2 • [Sⁿ]`.** The rotations `TauCeti.sphereRotationIsometry x₀`,
  parametrized by `Sⁿ⁻¹ × S¹`, turn `x₀` by the angle of `z ∈ S¹` in the plane spanned by `x₀` and
  a unit tangent vector `v ∈ Sⁿ⁻¹`. They are rotations of determinant `1`
  (`LinearIsometry.det_planeRotation`), so they form a continuous family of special orthogonal
  matrices (`TauCeti.sphereRotationMatrix`), whose evaluation at `x₀` is the rotation family
  `TauCeti.sphereRotationFamily x₀` of the sphere
  (`TauCeti.sphereRotationMatrix_smul_self`). On odd spheres the rotation family has degree `2`
  (`Orientation.mapFundamentalClass_sphereRotationFamily`), so the image of the fundamental class
  of `Sⁿ⁻¹ × S¹` in `Hₙ(SO(n + 1); ℤ)` evaluates to `2 • [Sⁿ]`.
* **A class `α` of positive degree of `Map_*(S², Sⁿ)` with `2 • α ≠ 0`.** The double loops of
  Example 6.20 of the source on an equator `Σ ≅ Sⁿ⁻²` through `x₀` induce an isomorphism
  `Hₙ₋₂(Σ; ℤ) ≅ Hₙ₋₂(Ω²Sⁿ; ℤ)` (Proposition 6.21), so `Hₙ₋₂(Map_*(S², Sⁿ); ℤ)` is infinite cyclic
  (`TauCeti.nonempty_iso_singularHomology_basedMap_sphere`), and a generator `α` has infinite
  order. Its degree `n - 2` is positive since `n ≥ 3`.

The source's first proof replaces the rotation family by a class of `πₙ(SO(n + 1))` lying over a
multiple of the generator of `πₙ(Sⁿ)`, which exists when `πₙ₋₁(SO(n))` is a torsion group
(`TauCeti.HomologicalOrientation.exists_isCoveredByDiffeomorphisms_sphere_of_isMulTorsion`); the
second proof needs no computation of homotopy groups of orthogonal groups.

## Main results

* `TauCeti.isAbundantWithTwoSpheres_sphere_of_odd`: the unit sphere `Sⁿ` of `ℝⁿ⁺¹` is abundant
  with 2-spheres at every point, for odd `n ≥ 3`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3, Propositions 6.21, 6.29, 6.33
  and 6.34, Example 6.20.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Matrix Metric Module

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'
attribute [local instance low] chartedSpaceProd

/-- **Odd-dimensional spheres are abundant with 2-spheres** (Proposition 6.34 of
Barraud–Damian–Humilière–Oancea). For odd `n ≥ 3`, the unit sphere `Sⁿ` of `ℝⁿ⁺¹` is abundant
with 2-spheres at every point `x₀`. -/
theorem isAbundantWithTwoSpheres_sphere_of_odd {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (x₀ : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    IsAbundantWithTwoSpheres (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n x₀ := by
  -- Apply the abundance criterion for the action of `SO(n + 1)`, with the class of the rotations
  -- over `2 • [Sⁿ]` and a generator of `Hₙ₋₂(Map_*(S², Sⁿ); ℤ) ≅ ℤ`.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hm : Even (m + 2) := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k, by omega⟩
  let F := EuclideanSpace ℝ (Fin (m + 3 + 1))
  have : Fact (finrank ℝ F = m + 2 + 1 + 1) := ⟨by simp [F]⟩
  -- The outward-normal orientation of the sphere and the product orientation of `Sⁿ⁻¹ × S¹`.
  let oF : Orientation ℝ F (Fin (m + 2 + 1 + 1)) :=
    (finBasisOfFinrankEq ℝ F (Fact.out : finrank ℝ F = m + 2 + 1 + 1)).orientation
  have hdim :
      finrank ℝ (EuclideanSpace ℝ (Fin (m + 2)) × EuclideanSpace ℝ (Fin 1)) = m + 2 + 1 := by
    rw [finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
  let oP := ((oF.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere x₀)).sphereOrientation.prod
    Complex.orientation.sphereOrientation).toHomologicalOrientation hdim
  -- The orbit map of `x₀` under the rotation group.
  let π : C(specialOrthogonalGroup (Fin (m + 3 + 1)) ℝ, sphere (0 : F) 1) :=
    ⟨fun g ↦ g • x₀, by fun_prop⟩
  have hρ : π.comp (sphereRotationMatrix x₀) =
      ⟨sphereRotationFamily x₀, continuous_sphereRotationFamily x₀⟩ :=
    ContinuousMap.ext (sphereRotationMatrix_smul_self x₀)
  -- The rotations lift the rotation family through the orbit map, so they carry the fundamental
  -- class of `Sⁿ⁻¹ × S¹` to a class of `SO(n + 1)` over `(1 + (-1) ^ (n - 1)) • [Sⁿ] = 2 • [Sⁿ]`.
  have hA : (((singularHomologyFunctor (ModuleCat.{0} ℤ) (m + 2 + 1)).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom π)).hom
        (oP.mapFundamentalClass hdim (sphereRotationMatrix x₀)) =
      (1 + (-1) ^ (m + 2) : ℤ) • (oF.sphereOrientation.toHomologicalOrientation
        finrank_euclideanSpace_fin).fundamentalClass finrank_euclideanSpace_fin := by
    rw [← HomologicalOrientation.mapFundamentalClass_comp, hρ]
    exact oF.mapFundamentalClass_sphereRotationFamily x₀ hdim
  -- A generator `α` of `Hₙ₋₂(Map_*(S², Sⁿ); ℤ) ≅ ℤ`, so that `2 • α ≠ 0`.
  obtain ⟨e⟩ :=
    nonempty_iso_singularHomology_basedMap_sphere (by simp [F] : finrank ℝ F = m + 4) x₀
  have hα : (1 + (-1) ^ (m + 2) : ℤ) • e.hom.hom (ULift.up 1) ≠ 0 := by
    rw [← map_zsmul, Ne, ← map_zero e.hom.hom,
      ((ConcreteCategory.isIso_iff_bijective e.hom).1 inferInstance).1.eq_iff, hm.neg_one_pow]
    exact fun h ↦ two_ne_zero (congrArg ULift.down h)
  exact (oF.sphereOrientation.toHomologicalOrientation
    finrank_euclideanSpace_fin).isAbundantWithTwoSpheres_of_smul_ne_zero
    finrank_euclideanSpace_fin π (fun _ ↦ rfl)
    (exists_continuousOn_specialOrthogonalGroup_smul_eq (by omega) x₀)
    (isPathConnected_setOf_specialOrthogonalGroup_smul_eq x₀) hA (by omega : 0 < m + 1)
    hα

end TauCeti

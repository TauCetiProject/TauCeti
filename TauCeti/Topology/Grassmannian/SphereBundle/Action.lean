/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OrthogonalGroup
public import TauCeti.Topology.Grassmannian.SphereBundle.Basic
import TauCeti.Geometry.Sphere.Equator

/-!
# Orbit maps of the action of `SO(N)` on the unit sphere of `ℝᴺ`

The special orthogonal group `SO(N)` acts on the unit sphere `Sᴺ⁻¹` of `ℝᴺ` by matrix
multiplication (`Matrix.SpecialOrthogonalGroup.instMulActionSphere`), through the linear isometry
of a special orthogonal matrix, and this action is jointly continuous. This file records the two
properties of the action that make its orbit maps behave like the bundle
`SO(N - 1) → SO(N) → Sᴺ⁻¹` of `TauCeti.Topology.Grassmannian.SphereBundle.Basic`, at an arbitrary
base point:

* the orbit map `A ↦ A • x₀` has continuous local sections around every point of the sphere
  (`TauCeti.exists_continuousOn_smul_eq_sphere`). Around `y` take a unit vector `w` with
  `w ≠ -x₀` and `y ≠ -w`; then `z ↦ R(w, z) R(x₀, w)` is a section on the complement of `-w`,
  where `R(b, y) = TauCeti.sphereRotation b y` is the rotation taking `b` to `y ≠ -b`;
* the stabilizer of a point is path connected
  (`TauCeti.isPathConnected_stabilizer_specialOrthogonalGroup_sphere`). It is conjugate to the
  stabilizer of the first coordinate vector, which is the image of the path-connected group
  `SO(N - 1)` under `B ↦ diag(1, B)`.

The local sections need `N ≥ 2`: `SO(1)` is trivial, while the sphere `S⁰` has two points.

These are the hypotheses of the abundance criterion for 2-spheres from a group action,
`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_ne_zero`.

## Main declarations

* `TauCeti.exists_continuousOn_smul_eq_sphere`: local sections of the orbit maps.
* `TauCeti.isPathConnected_stabilizer_specialOrthogonalGroup_sphere`: path-connected stabilizers.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 (fiber bundles of
  orthogonal groups over spheres).
-/

public section

open Matrix Metric Module Set

noncomputable section

namespace TauCeti

variable {N : ℕ}

/-- **Local sections of the orbit maps of `SO(N)` on the sphere.** For `N ≥ 2`, a base point `x₀`
and a point `y` of the unit sphere of `ℝᴺ`, the orbit map `A ↦ A • x₀` has a continuous section on
an open neighbourhood of `y`. -/
theorem exists_continuousOn_smul_eq_sphere (hN : 1 < N)
    (x₀ y : sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    ∃ U : Set (sphere (0 : EuclideanSpace ℝ (Fin N)) 1), IsOpen U ∧ y ∈ U ∧
      ∃ s : sphere (0 : EuclideanSpace ℝ (Fin N)) 1 → specialOrthogonalGroup (Fin N) ℝ,
        ContinuousOn s U ∧ ∀ z ∈ U, s z • x₀ = z := by
  -- A unit vector `w` with `w ≠ -x₀` and `y ≠ -w`: `w = y` unless `y = -x₀`.
  obtain ⟨w, hwx, hyw⟩ : ∃ w : sphere (0 : EuclideanSpace ℝ (Fin N)) 1, w ≠ -x₀ ∧ y ≠ -w := by
    by_cases hy : y = -x₀
    · obtain ⟨w, hw, hw'⟩ := exists_ne_and_ne_neg_sphere (by rwa [finrank_euclideanSpace_fin]) x₀
      exact ⟨w, hw', fun h ↦ hw (neg_injective (h.symm.trans hy))⟩
    · exact ⟨y, hy, ne_neg_of_mem_unit_sphere ℝ y⟩
  refine ⟨{-w}ᶜ, isOpen_compl_singleton, hyw, fun z ↦ sphereRotation w z * sphereRotation x₀ w,
    (continuousOn_sphereRotation w).mul continuousOn_const, fun z hz ↦ ?_⟩
  rw [mul_smul, sphereRotation_smul_self hwx, sphereRotation_smul_self hz]

/-- The evaluation map `SO(1 + n) → Sⁿ` on the first coordinate vector is the orbit map of the
first coordinate vector. -/
theorem specialOrthogonalSphereMap_eq_smul {n : ℕ} (A : specialOrthogonalGroup (Fin (1 + n)) ℝ) :
    specialOrthogonalSphereMap n A = A • specialOrthogonalSphereMap n 1 :=
  Subtype.ext <| by
    simp [SpecialOrthogonalGroup.coe_smul_sphere, coe_specialOrthogonalSphereMap,
      ← col_mul_eq_mulVec_col]

/-- **The stabilizers of `SO(N)` on the sphere are path connected.** For a point `x₀` of the unit
sphere of `ℝᴺ`, the special orthogonal matrices fixing `x₀` form a path-connected set: for `N ≥ 2`
they are conjugate to `SO(N - 1)`, and for `N ≤ 1` the group `SO(N)` is trivial. -/
theorem isPathConnected_stabilizer_specialOrthogonalGroup_sphere
    (x₀ : sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    IsPathConnected (MulAction.stabilizer (specialOrthogonalGroup (Fin N) ℝ) x₀ :
      Set (specialOrthogonalGroup (Fin N) ℝ)) := by
  rcases le_or_gt N 1 with hN | hN
  · -- `SO(N)` is trivial.
    have : Subsingleton (Fin N) := Fin.subsingleton_iff_le_one.2 hN
    convert isPathConnected_singleton (1 : specialOrthogonalGroup (Fin N) ℝ)
    exact Set.eq_singleton_iff_unique_mem.2 ⟨one_mem _, fun A _ ↦ Subsingleton.elim A 1⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = 1 + n := ⟨N - 1, by omega⟩
  have : NeZero n := ⟨by omega⟩
  -- The stabilizer of `e₀` is the image of `SO(n)`, and `g` takes `e₀` to `x₀`.
  set e₀ := specialOrthogonalSphereMap n 1
  have h₀ : IsPathConnected (MulAction.stabilizer (specialOrthogonalGroup (Fin (1 + n)) ℝ) e₀ :
      Set (specialOrthogonalGroup (Fin (1 + n)) ℝ)) := by
    have h := isPathConnected_range
      (continuous_subtypeVal.comp (specialOrthogonalSphereFiberHomeomorph n).continuous)
    rw [range_comp, Homeomorph.range_coe, image_univ, Subtype.range_coe_subtype] at h
    convert h using 1
    ext B
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, mem_ofPred_eq, mem_preimage,
      mem_singleton_iff]
    rw [specialOrthogonalSphereMap_eq_smul B]
  obtain ⟨g, rfl⟩ := surjective_specialOrthogonalSphereMap (n := n) x₀
  -- Conjugation by `g` carries the stabilizer of `e₀` onto that of `g • e₀`.
  rw [specialOrthogonalSphereMap_eq_smul, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    Subgroup.coe_map]
  exact h₀.image (show Continuous fun A ↦ g * A * g⁻¹ by fun_prop)

end TauCeti

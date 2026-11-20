/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Topology.Algebra.OrthogonalGroup
import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
import TauCeti.Topology.Algebra.GroupAction.OrbitTrivialization
import TauCeti.Topology.Homotopy.SerreFibration.Connected

/-!
# Orbit maps of the rotation group on the sphere

The special orthogonal group `SO(N)` acts on the unit sphere `S^{N-1}` of `ℝᴺ` by
matrix-vector multiplication (`Matrix.coe_specialUnitaryGroup_smul_unitSphere`). For a point `x₀`
of the sphere, this file proves that the orbit map `g ↦ g • x₀` has continuous local sections and
that its fibre over `x₀`, the stabilizer of `x₀`, is path-connected.

* **Local sections.** For `N ≥ 2`, every point `y` of the sphere has an open neighbourhood with a
  continuous section of the orbit map
  (`TauCeti.exists_continuousOn_specialOrthogonalGroup_smul_eq`). For a unit vector `c ≠ -x₀`, the
  rotation `TauCeti.sphereRotation x₀ c` takes `x₀` to `c`, and the rotations
  `TauCeti.sphereRotation c z` take `c` to `z ≠ -c`, continuously in `z`; their product is a
  section over the complement of `-c`, which contains `y` when `c ≠ -y`. Such a `c` exists: `x₀`
  itself unless `y = -x₀`, and otherwise any point other than `±x₀`.
* **Connected stabilizers.** For `N ≥ 3`, the stabilizer of `x₀` is path-connected
  (`TauCeti.isPathConnected_setOf_specialOrthogonalGroup_smul_eq`). The local sections make the
  orbit map a Serre fibration (`TauCeti.orbitMap_mem_serreFibrations`), whose fibre over `x₀` is the
  stabilizer. Its total space `SO(N)` is path-connected and its base `S^{N-1}` is simply connected,
  so the fibre is path-connected
  (`TauCeti.TopCat.pathConnectedSpace_fiber_of_mem_serreFibrations`).

These are the hypotheses on the orbit map of a group action in the abundance criterion
`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_ne_zero`, which turns a class of
the group over a multiple of the fundamental class of the sphere into classes of maps of 2-spheres
living over the fundamental class.

## Main results

* `TauCeti.exists_continuousOn_specialOrthogonalGroup_smul_eq`: local sections of the orbit map.
* `TauCeti.isPathConnected_setOf_specialOrthogonalGroup_smul_eq`: the stabilizers are
  path-connected.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2.
-/

public section

open Matrix Metric

namespace TauCeti

variable {N : ℕ}

/-- **Local sections of the orbit maps of the rotation group on the sphere.** For `N ≥ 2` and
points `x₀`, `y` of the unit sphere of `ℝᴺ`, there is an open neighbourhood `U` of `y` and a map
`s : U → SO(N)`, continuous on `U`, with `s z • x₀ = z` for every `z ∈ U`. -/
theorem exists_continuousOn_specialOrthogonalGroup_smul_eq (hN : 2 ≤ N)
    (x₀ y : sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    ∃ U : Set (sphere (0 : EuclideanSpace ℝ (Fin N)) 1), IsOpen U ∧ y ∈ U ∧
      ∃ s : sphere (0 : EuclideanSpace ℝ (Fin N)) 1 → specialOrthogonalGroup (Fin N) ℝ,
        ContinuousOn s U ∧ ∀ z ∈ U, s z • x₀ = z := by
  -- A unit vector `c` with `c ≠ -x₀` and `y ≠ -c`: `x₀` itself unless `y = -x₀`.
  obtain ⟨c, hcx, hcy⟩ : ∃ c, c ≠ -x₀ ∧ y ≠ -c := by
    by_cases h : y = -x₀
    · obtain ⟨c, hc, hc'⟩ := exists_ne_and_ne_neg_sphere (by simp; omega) x₀
      exact ⟨c, hc', fun h' ↦ hc (neg_injective (h'.symm.trans h))⟩
    · exact ⟨x₀, ne_neg_of_mem_unit_sphere ℝ x₀, h⟩
  refine ⟨{-c}ᶜ, isOpen_compl_singleton, hcy, fun z ↦ sphereRotation c z * sphereRotation x₀ c,
    (continuousOn_sphereRotation c).mul continuousOn_const, fun z hz ↦ ?_⟩
  rw [mul_smul, sphereRotation_smul hcx, sphereRotation_smul hz]

/-- **The stabilizers of the rotation group on the sphere are path-connected.** For `N ≥ 3`, the
rotations of `ℝᴺ` fixing a point `x₀` of the unit sphere form a path-connected subset of
`SO(N)`. -/
theorem isPathConnected_setOf_specialOrthogonalGroup_smul_eq (hN : 3 ≤ N)
    (x₀ : sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    IsPathConnected {g : specialOrthogonalGroup (Fin N) ℝ | g • x₀ = x₀} := by
  -- The orbit map is a Serre fibration with path-connected total space over the simply connected
  -- sphere.
  have hp := orbitMap_mem_serreFibrations (G := specialOrthogonalGroup (Fin N) ℝ) x₀
    (exists_continuousOn_specialOrthogonalGroup_smul_eq (by omega) x₀)
  have hB : Subsingleton (HomotopyGroup (Fin 1) (sphere (0 : EuclideanSpace ℝ (Fin N)) 1) x₀) :=
    subsingleton_homotopyGroup_sphere_of_lt (n := N - 1) (by simp; omega) (by simp; omega) x₀
  have : Nonempty ((TopCat.ofHom ⟨fun g : specialOrthogonalGroup (Fin N) ℝ ↦ g • x₀,
      by fun_prop⟩).fiber x₀) := ⟨⟨1, one_smul _ x₀⟩⟩
  -- The fibre of the orbit map over `x₀` is the stabilizer of `x₀`.
  have hfib : (TopCat.ofHom ⟨fun g : specialOrthogonalGroup (Fin N) ℝ ↦ g • x₀,
      by fun_prop⟩ : _root_.TopCat.of _ ⟶ _root_.TopCat.of _) ⁻¹' {x₀} =
        {g | g • x₀ = x₀} := by
    ext g
    simp
  rw [← hfib]
  exact isPathConnected_iff_pathConnectedSpace.2
    (TopCat.pathConnectedSpace_fiber_of_mem_serreFibrations hp hB)

end TauCeti

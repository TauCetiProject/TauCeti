/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Topology.Algebra.OrthogonalGroup
public import TauCeti.Topology.Grassmannian.SphereBundle.Basic
import TauCeti.Geometry.Sphere.Equator

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
* **Connected stabilizers.** For every `N`, the stabilizer of `x₀` is path-connected
  (`TauCeti.isPathConnected_setOf_specialOrthogonalGroup_smul_eq`). For `N = 1 + n ≥ 2` it is
  conjugate to the stabilizer of the first coordinate vector, the orbit of which is the evaluation
  map `TauCeti.specialOrthogonalSphereMap` (`TauCeti.specialOrthogonalSphereMap_eq_smul`); that
  stabilizer is the image of the path-connected group `SO(n)` under `B ↦ diag(1, B)`
  (`TauCeti.specialOrthogonalSphereFiberHomeomorph`). For `N ≤ 1` the group `SO(N)` is trivial.

These are the hypotheses on the orbit map of a group action in the abundance criterion
`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_ne_zero`, which turns a class of
the group over a multiple of the fundamental class of the sphere into classes of maps of 2-spheres
living over the fundamental class.

## Main results

* `TauCeti.exists_continuousOn_specialOrthogonalGroup_smul_eq`: local sections of the orbit map.
* `TauCeti.specialOrthogonalSphereMap_eq_smul`: the evaluation map `SO(1 + n) → Sⁿ` on the first
  coordinate vector is the orbit map of that vector.
* `TauCeti.isPathConnected_setOf_specialOrthogonalGroup_smul_eq`: the stabilizers are
  path-connected.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2.
-/

public section

open Matrix Metric Module Set

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

/-- The evaluation map `SO(1 + n) → Sⁿ` on the first coordinate vector is the orbit map of the
first coordinate vector. -/
theorem specialOrthogonalSphereMap_eq_smul {n : ℕ} (A : specialOrthogonalGroup (Fin (1 + n)) ℝ) :
    specialOrthogonalSphereMap n A = A • specialOrthogonalSphereMap n 1 :=
  Subtype.ext <| by
    simp [coe_specialUnitaryGroup_smul_unitSphere, coe_specialOrthogonalSphereMap,
      ← col_mul_eq_mulVec_col]

/-- **The stabilizers of the rotation group on the sphere are path-connected.** For a point `x₀`
of the unit sphere of `ℝᴺ`, the rotations of `ℝᴺ` fixing `x₀` form a path-connected subset of
`SO(N)`: for `N ≥ 2` they are conjugate to `SO(N - 1)`, and for `N ≤ 1` the group `SO(N)` is
trivial. -/
theorem isPathConnected_setOf_specialOrthogonalGroup_smul_eq
    (x₀ : sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    IsPathConnected {g : specialOrthogonalGroup (Fin N) ℝ | g • x₀ = x₀} := by
  change IsPathConnected (MulAction.stabilizer (specialOrthogonalGroup (Fin N) ℝ) x₀ :
    Set (specialOrthogonalGroup (Fin N) ℝ))
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

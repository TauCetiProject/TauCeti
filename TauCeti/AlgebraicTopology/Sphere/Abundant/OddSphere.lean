/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.Abundant.Action
public import TauCeti.AlgebraicTopology.Sphere.DoubleTangentCircle
public import TauCeti.Geometry.Diffeomorphism.Sphere.RotationFamily
import TauCeti.Topology.Grassmannian.SphereBundle.Action

/-!
# Odd spheres are abundant with 2-spheres

This file proves Proposition 6.34 of Barraud–Damian–Humilière–Oancea: for odd `n ≥ 3`, the sphere
`Sⁿ` is abundant with 2-spheres at every point
(`TauCeti.isAbundantWithTwoSpheres_sphere_of_odd`). Abundance is the hypothesis of their Theorem
6.12, which concludes that the `π₁`-sensitive Hofer–Zehnder capacity of the unit codisc bundle
`D*Sⁿ` is finite.

The proof is the abundance criterion for a group action,
`TauCeti.HomologicalOrientation.isAbundantWithTwoSpheres_of_smul_ne_zero` (the argument of the
source's Propositions 6.29 and 6.33), for the action of `SO(n + 1)` on `Sⁿ ⊆ ℝⁿ⁺¹` at a point `b`.
It needs three inputs.

* **The action.** The orbit map `A ↦ A • b` has continuous local sections and the stabilizer of
  `b` is path connected (`TauCeti.exists_continuousOn_smul_eq_sphere`,
  `TauCeti.isPathConnected_stabilizer_specialOrthogonalGroup_sphere`).
* **A class `A ∈ Hₙ(SO(n + 1); ℤ)` with `π_* A = 2 • [Sⁿ]`.** The rotations in the planes through
  `b` form a family of special orthogonal matrices parametrized by `Sⁿ⁻¹ × S¹`
  (`TauCeti.sphereRotationMatrix`), whose orbit map at `b` is the rotation family of the sphere.
  That family has degree `1 + (-1)ⁿ⁻¹ = 2` for odd `n`
  (`Orientation.mapFundamentalClass_sphereRotationFamily`), so `A` is the image of the
  fundamental class of `Sⁿ⁻¹ × S¹`. This is the second, direct proof of the source; it needs no
  homotopy groups of orthogonal groups.
* **A class `α` of positive degree of `Map_*(S², Sⁿ)` with `2 • α ≠ 0`.** The double loops of
  Example 6.20 of the source induce an isomorphism `H_{n-2}(S^{n-2}; ℤ) ≅ H_{n-2}(Ω²Sⁿ; ℤ)`
  (Proposition 6.21, `TauCeti.isIso_singularHomologyFunctor_map_tangentCircleDoubleLoop`), so
  `H_{n-2}(Map_*(S², Sⁿ); ℤ)` has an element of infinite order
  (`TauCeti.exists_not_isOfFinAddOrder_homology_basedMap_sphere`). Here `n ≥ 3` is used, so that
  `n - 2 > 0`.

## Main results

* `TauCeti.isAbundantWithTwoSpheres_sphere_of_odd`: odd spheres of dimension at least `3` are
  abundant with 2-spheres.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4, Example 6.20, Propositions 6.21,
  6.33 and 6.34.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Metric Module
open scoped RealInnerProductSpace Topology.Homotopy

namespace TauCeti

section Sphere

attribute [local instance] finrank_real_complex_fact'
attribute [local instance low] chartedSpaceProd

/-- **Odd spheres are abundant with 2-spheres** (Barraud–Damian–Humilière–Oancea, Proposition
6.34). For odd `n ≥ 3`, the unit sphere `Sⁿ` of `ℝⁿ⁺¹` is abundant with 2-spheres at every
point `b`. The witness is the image of `A × α` under the action map
`SO(n + 1) × Map_*(S², Sⁿ) → Map(S², Sⁿ)`, where `A ∈ Hₙ(SO(n + 1); ℤ)` is the class of the
rotations in the planes through `b`, which evaluates at `b` to `2 • [Sⁿ]`, and `α` is a class of
infinite order of `H_{n-2}(Map_*(S², Sⁿ); ℤ)`. -/
theorem isAbundantWithTwoSpheres_sphere_of_odd {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    (b : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    IsAbundantWithTwoSpheres (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) n b := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 + 1 := ⟨n - 3, by omega⟩
  have hm : Even (m + 2) := by
    obtain ⟨k, hk⟩ := hn
    exact ⟨k, by omega⟩
  -- `Fin (m + 2 + 1 + 1)` unifies with `Fin (k + 1)` at `k = m + 3`.
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (m + 2 + 1 + 1))) = m + 3 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let oF : Orientation ℝ (EuclideanSpace ℝ (Fin (m + 2 + 1 + 1))) (Fin (m + 2 + 1 + 1)) :=
    (EuclideanSpace.basisFun (Fin (m + 2 + 1 + 1)) ℝ).toBasis.orientation
  let o := oF.sphereOrientation.toHomologicalOrientation finrank_euclideanSpace_fin
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin (m + 2)) × EuclideanSpace ℝ (Fin 1)) =
      m + 2 + 1 := by
    rw [finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
  let o' := ((oF.orthogonalSpanSingleton (ne_zero_of_mem_unit_sphere b)).sphereOrientation.prod
    Complex.orientation.sphereOrientation).toHomologicalOrientation hdim
  -- The orbit map of `b`, which sends the rotations in the planes through `b` to the rotation
  -- family of the sphere.
  let π : C(Matrix.specialOrthogonalGroup (Fin (m + 2 + 1 + 1)) ℝ,
      sphere (0 : EuclideanSpace ℝ (Fin (m + 2 + 1 + 1))) 1) :=
    ⟨fun g ↦ g • b, by fun_prop⟩
  have hπ : π.comp (sphereRotationMatrix b) =
      ⟨sphereRotationFamily b, continuous_sphereRotationFamily b⟩ := by
    ext x : 1
    exact sphereRotationMatrix_smul_self b x
  obtain ⟨α, hα⟩ := exists_not_isOfFinAddOrder_homology_basedMap_sphere
    (E := EuclideanSpace ℝ (Fin (m + 2 + 1 + 1))) (m := m) (by simp) b
  refine o.isAbundantWithTwoSpheres_of_smul_ne_zero finrank_euclideanSpace_fin π (fun _ ↦ rfl)
    (exists_continuousOn_smul_eq_sphere (by omega) b)
    (isPathConnected_stabilizer_specialOrthogonalGroup_sphere b) (ℓ := 2)
    (A := o'.mapFundamentalClass hdim (sphereRotationMatrix b)) ?_ (k := m + 1) (by omega)
    (α := α) fun h ↦ hα (isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨2, two_ne_zero, h⟩)
  -- The class of the rotations evaluates at `b` to `(1 + (-1) ^ (m + 2)) • [Sᵐ⁺³] = 2 • [Sᵐ⁺³]`.
  refine (o'.mapFundamentalClass_comp hdim π (sphereRotationMatrix b)).symm.trans ?_
  rw [hπ, oF.mapFundamentalClass_sphereRotationFamily b hdim, hm.neg_one_pow, one_add_one_eq_two]
  -- The two sides differ only in the proofs of the dimension facts.
  rfl

end Sphere

end TauCeti

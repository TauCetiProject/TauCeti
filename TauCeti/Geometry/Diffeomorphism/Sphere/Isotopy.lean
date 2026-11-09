/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Sphere
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import TauCeti.AlgebraicTopology.Singular.Sphere
import TauCeti.Geometry.Diffeomorphism.Evaluation
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
import TauCeti.Topology.Algebra.OrthogonalGroup

/-!
# Isotopy classes of orthogonal transformations of a sphere

The reference inclusion `TauCeti.orthogonalToDiffSphere : O(n + 1) → Diff(Sⁿ)` induces an
injective map on path components, for every dimension `n` and every smoothness exponent `m` of
the weak Whitney topology: two orthogonal transformations of `ℝⁿ⁺¹` are isotopic as
diffeomorphisms of `Sⁿ` exactly when they have the same determinant. A path of diffeomorphisms
is a homotopy of maps, because evaluation is continuous for the weak Whitney topology, and an
orthogonal transformation acts on the reduced homology `Hₙ(Sⁿ; ℤ) ≅ ℤ` by the sign of its
determinant; conversely matrices of equal determinant are joined in the orthogonal group
(`TauCeti.Matrix.joined_orthogonalGroup_iff_det_eq`). In particular a reflection of `Sⁿ` is not
isotopic to the identity, and `Diff(Sⁿ)` is never path-connected.

## Main results

* `TauCeti.det_eq_of_joined_orthogonalToDiffSphere`: orthogonal transformations isotopic as
  diffeomorphisms of `Sⁿ` have the same determinant.
* `TauCeti.joined_orthogonalToDiffSphere_iff`: they are isotopic exactly when their determinants
  agree.
* `TauCeti.not_joined_one_orthogonalToDiffSphere_of_det_eq_neg_one`: an orthogonal
  transformation of determinant `-1` is not isotopic to the identity.
* `TauCeti.not_pathConnectedSpace_diff_sphere`: the diffeomorphism group of a sphere is not
  path-connected.
-/

public section

open Metric CategoryTheory
open scoped Manifold ContDiff EuclideanSpace TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable {n : ℕ} {m : ℕ∞ω}

/-- **Isotopic orthogonal transformations have the same determinant.** If the restrictions of two
orthogonal transformations of `ℝⁿ⁺¹` to the unit sphere `Sⁿ` are joined by a path of `C^m`
diffeomorphisms, for the weak Whitney topology, then the two matrices have the same
determinant. -/
theorem det_eq_of_joined_orthogonalToDiffSphere {A B : Matrix.orthogonalGroup (Fin (n + 1)) ℝ}
    (h : Joined (orthogonalToDiffSphere n m A) (orthogonalToDiffSphere n m B)) :
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det =
      (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det := by
  obtain ⟨γ⟩ := h
  set eA := (orthogonalGroupToLinearIsometryEquiv A).toLinearIsometry
  set eB := (orthogonalGroupToLinearIsometryEquiv B).toLinearIsometry
  -- Evaluation is continuous on `Diff(Sⁿ)`, so the path is a homotopy of maps of the sphere.
  let H : TopCat.Homotopy (TopCat.ofHom ⟨eA.unitSphereMap, eA.continuous_unitSphereMap⟩)
      (TopCat.ofHom ⟨eB.unitSphereMap, eB.continuous_unitSphereMap⟩) :=
    { toFun := fun p ↦ γ p.1 p.2
      continuous_toFun := continuous_eval.comp (γ.continuous.prodMap continuous_id)
      map_zero_left := fun x ↦ Subtype.ext (by simp [eA])
      map_one_left := fun x ↦ Subtype.ext (by simp [eB]) }
  -- The two maps act on reduced homology `Hₙ(Sⁿ; ℤ)` by the signs of the determinants.
  have hH := reducedSingularHomologyFunctor_map_eq_of_homotopy (ModuleCat.of ℤ ℤ) H n
  rw [reducedSingularHomologyFunctor_map_unitSphereMap _ finrank_euclideanSpace_fin eA,
    reducedSingularHomologyFunctor_map_unitSphereMap _ finrank_euclideanSpace_fin eB,
    det_orthogonalGroupToLinearIsometryEquiv, det_orthogonalGroupToLinearIsometryEquiv] at hH
  -- Read both sides through the reduced-homology isomorphism `Hₙ(Sⁿ; ℤ) ≅ ℤ` and evaluate at `1`.
  let e := reducedSingularHomologySphereIso (ModuleCat.of ℤ ℤ)
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)
  have hsign := congrArg (fun φ ↦ (e.inv ≫ φ ≫ e.hom).hom (1 : ℤ)) hH
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.id_comp,
    Iso.inv_hom_id, ModuleCat.hom_zsmul, ModuleCat.hom_id, LinearMap.smul_apply,
    LinearMap.id_apply, smul_eq_mul, mul_one] at hsign
  rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup A.2 with hA | hA <;>
    rcases det_eq_one_or_neg_one_of_mem_orthogonalGroup B.2 with hB | hB <;>
    simp_all

/-- **The isotopy classes of orthogonal transformations of a sphere.** The restrictions of two
orthogonal transformations of `ℝⁿ⁺¹` to `Sⁿ` are joined by a path of `C^m` diffeomorphisms
exactly when the two matrices have the same determinant. So the map `π₀ O(n + 1) → π₀ Diff(Sⁿ)`
is injective, and its image consists of two path components. -/
theorem joined_orthogonalToDiffSphere_iff {A B : Matrix.orthogonalGroup (Fin (n + 1)) ℝ} :
    Joined (orthogonalToDiffSphere n m A) (orthogonalToDiffSphere n m B) ↔
      (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det =
        (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det :=
  ⟨det_eq_of_joined_orthogonalToDiffSphere, fun h ↦
    (Matrix.joined_orthogonalGroup_iff_det_eq.2 h).map (continuous_orthogonalToDiffSphere n m)⟩

/-- An orthogonal transformation of determinant `-1`, such as a reflection, is not isotopic to the
identity as a diffeomorphism of the sphere. -/
theorem not_joined_one_orthogonalToDiffSphere_of_det_eq_neg_one
    {A : Matrix.orthogonalGroup (Fin (n + 1)) ℝ}
    (hA : (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).det = -1) :
    ¬ Joined 1 (orthogonalToDiffSphere n m A) := by
  rw [← map_one (orthogonalToDiffSphere n m), joined_orthogonalToDiffSphere_iff, hA]
  norm_num

/-- **The diffeomorphism group of a sphere is not path-connected**, for the weak Whitney `C^m`
topology: a reflection of `Sⁿ` is not isotopic to the identity. -/
theorem not_pathConnectedSpace_diff_sphere :
    ¬ PathConnectedSpace (Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :=
  fun h ↦ not_joined_one_orthogonalToDiffSphere_of_det_eq_neg_one
    (det_orthogonalDiagonalReflection ℝ 0) (h.joined _ _)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.AlgebraicTopology.Singular.Sphere
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Spheres are not contractible, punctured spheres are

The unit sphere of a nontrivial finite-dimensional real normed space is not contractible.
This distinguishes spherical links from ball links, including the two-point zero-sphere.
No inner product on the normed space is required: the reduced homology computation is
transported from a Euclidean space of the same dimension.

The sphere has nonzero reduced singular homology with integer coefficients in its
dimension, whereas a contractible space has zero reduced homology in every degree. See Hatcher,
*Algebraic Topology*, Section 2.1, Corollary 2.14, for the homology obstruction to
contractibility of spheres.

On the other hand, removing a single point `x` from the unit sphere of a real inner product space
leaves a contractible space (`TauCeti.contractibleSpace_compl_singleton_sphere`): stereographic
projection from `x` (Mathlib's `stereographic`) identifies it with the hyperplane orthogonal to `x`.
-/

public section

open CategoryTheory Limits Metric Module

universe w

namespace TauCeti

/-- The unit sphere of a nontrivial finite-dimensional real normed space is not contractible,
including in ambient dimension one. -/
theorem not_contractibleSpace_sphere {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] :
    ¬ ContractibleSpace (sphere (0 : E) 1) := by
  intro h
  let := h
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (finrank_pos (R := ℝ) (M := E)).ne'
  let R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let F := EuclideanSpace ℝ (ULift.{w} (Fin (n + 1)))
  have hEF : finrank ℝ E = finrank ℝ F :=
    hn.trans (finrank_euclideanSpace_ulift_fin (n + 1)).symm
  let e := reducedSingularHomologySphereIsoOfFinrankEq R hEF n ≪≫
    reducedSingularHomologySphereIso R
      ((EuclideanSpace.basisFun (ULift.{w} (Fin (n + 1))) ℝ).reindex Equiv.ulift)
  have hz : IsZero R :=
    (isZero_reducedSingularHomologyFunctor_of_contractibleSpace R
      (TopCat.of (sphere (0 : E) 1)) n).of_iso e.symm
  have : Subsingleton (ULift.{w} ℤ) := ModuleCat.isZero_iff_subsingleton.mp hz
  exact zero_ne_one (Subsingleton.elim (0 : ULift.{w} ℤ) 1)

/-- **The complement of a point of a sphere is contractible**: stereographic projection from `x`
identifies it with the hyperplane orthogonal to `x`. -/
theorem contractibleSpace_compl_singleton_sphere {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : sphere (0 : E) 1) :
    ContractibleSpace ({x}ᶜ : Set (sphere (0 : E) 1)) :=
  ((Homeomorph.setCongr (stereographic_source (norm_eq_of_mem_sphere x)).symm).trans
      ((stereographic (norm_eq_of_mem_sphere x)).toHomeomorphSourceTarget.trans
        ((Homeomorph.setCongr (stereographic_target (norm_eq_of_mem_sphere x))).trans
          (Homeomorph.Set.univ _)))).contractibleSpace

end TauCeti

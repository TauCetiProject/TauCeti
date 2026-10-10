/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Sphere
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Spheres are not contractible

The unit sphere of a nontrivial finite-dimensional real normed space is not contractible.
This distinguishes spherical links from ball links, including the two-point zero-sphere.
No inner product on the normed space is required: the reduced homology computation is
transported from a Euclidean space of the same dimension.

The proof uses `reducedSingularHomologySphereIsoOfFinrankEq` and
`reducedSingularHomologySphereIso`, with integer coefficients. See Hatcher,
*Algebraic Topology*, Section 2.1, Corollary 2.14, for the homology obstruction to
contractibility of spheres.
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

end TauCeti

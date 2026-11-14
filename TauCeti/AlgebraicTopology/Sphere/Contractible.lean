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
Consequently no contractible space (in particular, no real normed space or Euclidean space) is
homotopy equivalent to such a sphere
(`TauCeti.isEmpty_homotopyEquiv_sphere_of_contractibleSpace`,
`TauCeti.isEmpty_normedSpace_homotopyEquiv_sphere`,
`TauCeti.isEmpty_euclideanSpace_homotopyEquiv_sphere`).

The sphere has nonzero reduced singular homology with integer coefficients in its
dimension, whereas a contractible space has zero reduced homology in every degree. See Hatcher,
*Algebraic Topology*, Section 2.1, Corollary 2.14, for the homology obstruction to
contractibility of spheres.
-/

public section

open CategoryTheory Limits Metric Module
open scoped ContinuousMap

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

/-- **No contractible space is homotopy equivalent to a sphere.** For any contractible space `X`
and any nontrivial finite-dimensional real normed space `F`, `X ≃ₕ sphere (0 : F) 1` is empty,
including for the two-point zero-sphere when `finrank ℝ F = 1`. -/
theorem isEmpty_homotopyEquiv_sphere_of_contractibleSpace (X : Type*) [TopologicalSpace X]
    [ContractibleSpace X] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [Nontrivial F] :
    IsEmpty (X ≃ₕ sphere (0 : F) 1) :=
  ⟨fun e ↦ not_contractibleSpace_sphere e.symm.contractibleSpace⟩

/-- **No real normed space is homotopy equivalent to a sphere.** For any real normed space `E` and
any nontrivial finite-dimensional real normed space `F`, `E ≃ₕ sphere (0 : F) 1` is empty. -/
theorem isEmpty_normedSpace_homotopyEquiv_sphere (E F : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [Nontrivial F] :
    IsEmpty (E ≃ₕ sphere (0 : F) 1) :=
  isEmpty_homotopyEquiv_sphere_of_contractibleSpace E F

/-- **No Euclidean space is homotopy equivalent to a sphere.** In particular, `ℝ³` is not homotopy
equivalent to `S³`. -/
theorem isEmpty_euclideanSpace_homotopyEquiv_sphere (ι : Type*) [Finite ι] (n : ℕ) :
    IsEmpty (EuclideanSpace ℝ ι ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  cases nonempty_fintype ι
  exact isEmpty_normedSpace_homotopyEquiv_sphere (EuclideanSpace ℝ ι)
    (EuclideanSpace ℝ (Fin (n + 1)))

end TauCeti

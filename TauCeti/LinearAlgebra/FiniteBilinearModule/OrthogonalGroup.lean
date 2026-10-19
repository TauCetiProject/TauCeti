/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Data.FunLike.Fintype
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# Orthogonal groups of finite quadratic modules

The orthogonal group `O(A)` of a finite quadratic module consists of its additive automorphisms
preserving the quadratic map. This file specializes the general quadratic-map orthogonal group to
finite quadratic modules and records its action on the underlying module and its isotropic and
Lagrangian subgroups. The imported generic orthogonal-group API transports this group across
isometries of finite quadratic modules, and `QuadraticMap.orthogonalGroupEquivIsometryEquiv`
identifies its underlying type with the type `Isometry A A` of self-isometries of `A`.

These actions are the group-theoretic interface used when discriminant-form automorphisms act on
gluing data and primitive embeddings.

## Main definitions

* `TauCeti.FiniteQuadraticModule.orthogonalGroup`: the group `O(A)`.

## Main results

* `TauCeti.FiniteQuadraticModule.finite_orthogonalGroup`: `O(A)` is finite.
* `TauCeti.FiniteQuadraticModule.isIsotropic_smul_iff` and
  `TauCeti.FiniteQuadraticModule.isLagrangian_smul_iff`: `O(A)` preserves the two classes of
  subgroups used in gluing theory.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
-/

public section

namespace TauCeti.FiniteQuadraticModule

open scoped Pointwise

/-- The orthogonal group `O(A)` of a finite quadratic module `A`. -/
abbrev orthogonalGroup (A : FiniteQuadraticModule) : Subgroup (A ≃ₗ[ℤ] A) :=
  QuadraticMap.orthogonalGroup A.quadratic

variable {A : FiniteQuadraticModule}

/-- The orthogonal group of a finite quadratic module is finite. -/
instance finite_orthogonalGroup (A : FiniteQuadraticModule) : Finite (orthogonalGroup A) := by
  have : Finite (A ≃ₗ[ℤ] A) := FunLike.finite _
  infer_instance

/-- The action of `O(A)` on `A` preserves the quadratic map. -/
@[simp]
theorem quadratic_smul (g : orthogonalGroup A) (x : A) :
    A.quadratic (g • x) = A.quadratic x :=
  QuadraticMap.map_app_of_mem_orthogonalGroup g.property x

/-- Pointwise transport of an additive subgroup by an element of `O(A)` is its image under the
corresponding self-isometry. -/
theorem smul_eq_map_toAddEquiv (g : orthogonalGroup A) (H : AddSubgroup A) :
    g • H = H.map (QuadraticMap.orthogonalGroupEquivIsometryEquiv A.quadratic g).toAddEquiv := by
  calc
    g • H = H.map (DistribMulAction.toAddMonoidEnd _ _ g) :=
      AddSubgroup.pointwise_smul_def H
    _ = H.map (QuadraticMap.orthogonalGroupEquivIsometryEquiv A.quadratic g).toAddEquiv := by
      congr 1
      ext x
      exact (congrFun (QuadraticMap.coe_orthogonalGroupEquivIsometryEquiv A.quadratic g) x).symm

/-- The orthogonal group preserves quadratic-isotropic subgroups. -/
@[simp]
theorem isIsotropic_smul_iff (g : orthogonalGroup A) (H : AddSubgroup A) :
    A.IsIsotropic (g • H) ↔ A.IsIsotropic H := by
  rw [smul_eq_map_toAddEquiv]
  exact Isometry.isIsotropic_map_iff A (QuadraticMap.orthogonalGroupEquivIsometryEquiv _ g) H

/-- The orthogonal group preserves quadratic Lagrangian subgroups. -/
@[simp]
theorem isLagrangian_smul_iff (g : orthogonalGroup A) (H : AddSubgroup A) :
    A.IsLagrangian (g • H) ↔ A.IsLagrangian H := by
  rw [smul_eq_map_toAddEquiv]
  exact Isometry.isLagrangian_map_iff A (QuadraticMap.orthogonalGroupEquivIsometryEquiv _ g) H

/-- The action of the orthogonal group commutes with taking the orthogonal complement for the
polar pairing. -/
@[simp]
theorem smul_orthogonalComplement (g : orthogonalGroup A) (H : AddSubgroup A) :
    g • A.toFiniteBilinearModule.orthogonalComplement H =
      A.toFiniteBilinearModule.orthogonalComplement (g • H) := by
  let e : Isometry A A := QuadraticMap.orthogonalGroupEquivIsometryEquiv A.quadratic g
  rw [smul_eq_map_toAddEquiv, smul_eq_map_toAddEquiv, ← e.toFiniteBilinearModule_toAddEquiv]
  exact e.toFiniteBilinearModule.map_orthogonalComplement (H := H)

end TauCeti.FiniteQuadraticModule

end

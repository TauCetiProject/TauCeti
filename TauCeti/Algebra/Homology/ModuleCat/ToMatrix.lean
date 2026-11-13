/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# Matrices of the differentials of a based complex under isomorphisms

Let `e : C ≅ D` be an isomorphism of complexes of modules over a commutative ring `R`, of any
shape. Bases `bᵢ` of `C.X i` and `bⱼ` of `C.X j` transport along `e` to bases of `D.X i` and
`D.X j`, and the matrix of the differential `D.d i j` in the transported bases is the matrix of
`C.d i j` in the bases `bᵢ` and `bⱼ` (`HomologicalComplex.toMatrix_map_isoApp_d`). This is how
invariants computed from the matrices of the differentials, such as the torsion of a based
complex, are shown to be invariant under isomorphisms of based complexes.

## Main results

* `HomologicalComplex.toMatrix_map_isoApp_d`: transporting bases along an isomorphism of
  complexes does not change the matrices of the differentials.
-/

public section

open CategoryTheory Module

namespace HomologicalComplex

variable {R : Type*} [CommRing R] {ι : Type*} {s : ComplexShape ι}
  {C D : HomologicalComplex (ModuleCat R) s} (e : C ≅ D) {i j : ι} {κ μ : Type*} [Fintype κ]
  [DecidableEq κ] [Finite μ]

/-- Transporting bases along an isomorphism of complexes `e : C ≅ D` does not change the matrices
of the differentials: the matrix of `D.d i j` in the bases transported from `bᵢ` and `bⱼ` is the
matrix of `C.d i j` in the bases `bᵢ` and `bⱼ`. -/
theorem toMatrix_map_isoApp_d (bᵢ : Basis κ R (C.X i)) (bⱼ : Basis μ R (C.X j)) :
    LinearMap.toMatrix (bᵢ.map (Hom.isoApp e i).toLinearEquiv)
        (bⱼ.map (Hom.isoApp e j).toLinearEquiv) (D.d i j).hom =
      LinearMap.toMatrix bᵢ bⱼ (C.d i j).hom := by
  ext k l
  simp only [LinearMap.toMatrix_apply, Basis.map_repr, Iso.toLinearEquiv_symm, Basis.map_apply,
    Iso.toLinearEquiv_apply, Hom.isoApp_hom, Hom.comm_apply, LinearEquiv.trans_apply, Iso.symm_hom,
    Hom.isoApp_inv]
  rw [← ConcreteCategory.comp_apply, ← comp_f, e.hom_inv_id, id_f, ConcreteCategory.id_apply]

end HomologicalComplex

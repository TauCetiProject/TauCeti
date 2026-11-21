/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.BigCell.Weyl
public import TauCeti.LinearAlgebra.Matrix.LDU

/-!
# Triangular factors and the Weyl-representative big-cell test

In a faithful Chevalley representation, a product `L * n_w * U`, with invertible block lower
triangular `L` and block upper triangular `U`, has unit leading weight-block minors exactly
when `w = 1`. Thus the matrix open set defined by these minors excludes every nonidentity
Weyl cell, independently of the triangular factors. The blocks are the actual weight spaces,
not individual basis vectors, and their order is arbitrary.

A Weyl word itself admits block LDU factorization exactly when its Weyl-group element is the
identity. The middle factor in this matrix factorization is block diagonal; it is not asserted
to be a point of the weight torus. Likewise, no Bruhat decomposition or generation of all
scheme points by root subgroups is assumed or proved here.

The tests combine the weight-action criterion
`ChevalleyDatum.isUnit_leading_weight_minors_weylWord_iff` with the matrix minor-invariance
and block LDU theorems. They hold over every nontrivial commutative ring, including rings with
nilpotents and fields of bad characteristic.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 5, Theorem 7.
* J. C. Jantzen, *Representations of Algebraic Groups*, Part II, Chapter 1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable {β : Type*} [LinearOrder β]

/-- Invertible lower and upper weight-block triangular factors do not change the Weyl-word
big-cell test: all leading weight-block minors are units exactly for the identity Weyl element.
There is no restriction on the order of the distinct weights or on their multiplicities. -/
theorem isUnit_leading_weight_minors_mul_weylWord_mul_iff
    (l : List (Fin t.rank)) (A : Type v) [CommRing A] [Nontrivial A]
    (r : Set.range D.weight ≃ β) (L U : Matrix (Fin D.dim) (Fin D.dim) A)
    (hL : L.BlockTriangular (OrderDual.toDual ∘ fun j => r ⟨D.weight j, Set.mem_range_self j⟩))
    (hU : U.BlockTriangular (fun j => r ⟨D.weight j, Set.mem_range_self j⟩))
    (hLdet : IsUnit L.det) (hUdet : IsUnit U.det) :
    (∀ a, IsUnit ((L *
      ((((l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod :
        Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A)) * U
      ).toSquareBlockProp fun j => r ⟨D.weight j, Set.mem_range_self j⟩ ≤ a).det) ↔
      t.geckWeylWordProd ht l = 1 := by
  have hminor (a : β) := Matrix.isUnit_det_toSquareBlockProp_mul_mul_iff
    (M := ((((l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod :
      Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A)))
    hL hU hLdet hUdet (p := fun j => r ⟨D.weight j, Set.mem_range_self j⟩ ≤ a)
    (fun _ _ hji hi => hji.trans hi)
  simp_rw [hminor]
  exact D.isUnit_leading_weight_minors_weylWord_iff l A r

/-- A Weyl word admits matrix block LDU factorization in the weight-space blocks exactly when
its Weyl-group element is the identity. The invertible block diagonal middle factor need not
belong to the represented torus. -/
theorem exists_blockLDU_weylWord_iff
    (l : List (Fin t.rank)) (A : Type v) [CommRing A] [Nontrivial A]
    (r : Set.range D.weight ≃ β) :
    (∃ L N U : Matrix (Fin D.dim) (Fin D.dim) A,
      L.BlockUnitriangular (OrderDual.toDual ∘ fun j => r ⟨D.weight j, Set.mem_range_self j⟩) ∧
      N.BlockTriangular (fun j => r ⟨D.weight j, Set.mem_range_self j⟩) ∧
      N.BlockTriangular (OrderDual.toDual ∘ fun j => r ⟨D.weight j, Set.mem_range_self j⟩) ∧
      U.BlockUnitriangular (fun j => r ⟨D.weight j, Set.mem_range_self j⟩) ∧ IsUnit N.det ∧
      ((((l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod :
        Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A)) =
          L * N * U) ↔ t.geckWeylWordProd ht l = 1 := by
  rw [← Matrix.exists_blockLDU_iff]
  rw [← D.isUnit_leading_weight_minors_weylWord_iff l A r]
  symm
  exact (r.surjective.comp Set.rangeFactorization_surjective).forall

end TauCeti.DynkinType.ChevalleyDatum

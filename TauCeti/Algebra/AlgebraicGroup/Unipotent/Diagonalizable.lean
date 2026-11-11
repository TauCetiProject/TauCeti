/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.GroupLike
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Triangular

/-!
# Homomorphisms from diagonalizable groups to unipotent groups are trivial

Over a field, a bialgebra whose group-like elements span it has no nonzero primitive elements
(`TauCeti.Subcoalgebra.eq_zero_of_comul_eq_of_groupLikeSetSpan_eq_top`). Hence a coalgebra
morphism to such a bialgebra that sends the diagonal coefficients of an upper-unitriangular
representation to `1` sends its whole coefficient matrix to the identity matrix
(`TauCeti.Comodule.map_coefficientMatrix_eq_one_of_isUpperUnitriangular`).

A reduced finite-type affine group over an algebraically closed field whose rational points are
unipotent has a faithful upper-unitriangular representation, whose coefficients and their
antipodes generate its coordinate algebra. Hence every homomorphism into it from a
diagonalizable group is trivial; contravariantly, every bialgebra morphism from its coordinate
algebra to a group-like-spanned bialgebra is the counit. In particular a
diagonalizable closed subgroup of such a unipotent group is trivial, with no reducedness
assumption on the subgroup: this is the scheme-theoretic form, which also sees infinitesimal
subgroups such as `μₚ`. It is the input showing that a torus of a smooth connected solvable
group meets its unipotent radical trivially.

## Main declarations

* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.eq_of_groupLikeSetSpan_eq_top`: a
  bialgebra morphism from the coordinate algebra of a reduced unipotent group to a
  group-like-spanned bialgebra is the counit.
* `TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty.bijective_algebraMap_of_surjective`:
  a diagonalizable closed subgroup of a reduced unipotent group is trivial.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 14 (unipotent groups) and Theorem 16.33.
* W. C. Waterhouse, *Introduction to Affine Group Schemes* (1979), Chapter 8.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

namespace geometricallyUnipotentPointsCommHopfAlgProperty

open Comodule

variable {k H K : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable [Ring K] [Bialgebra k K]

/-- **A homomorphism from a diagonalizable group to a reduced unipotent group is trivial.** Over
an algebraically closed field, a bialgebra morphism from the coordinate algebra of a reduced
finite-type affine group with unipotent points to a bialgebra spanned by its group-like elements
is the counit. When the target is a commutative Hopf algebra, it is the coordinate algebra of a
diagonalizable group. -/
theorem eq_of_groupLikeSetSpan_eq_top [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    (hH : geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.of k H))
    (hK : Subcoalgebra.groupLikeSetSpan (R := k) (C := K) Set.univ = ⊤)
    (φ : H →ₐc[k] K) :
    φ.toAlgHom = (Algebra.ofId k K).comp (Bialgebra.counitAlgHom k H) := by
  obtain ⟨M, n, b, hb, hsurj⟩ :=
    exists_coordinateBialgHom_surjective_of_forall_isUnipotentPoint (forall_isUnipotentPoint hH)
  have hone := map_coefficientMatrix_eq_one_of_isUpperUnitriangular (H := H) b hb hK
    φ.toCoalgHom fun i ↦ by
      rw [((Matrix.isUpperUnitriangular_def _).mp hb).2 i]
      exact map_one φ
  have hcomp : φ.toAlgHom.comp (coordinateBialgHom (H := H) b).toAlgHom =
      ((Algebra.ofId k K).comp (Bialgebra.counitAlgHom k H)).comp
        (coordinateBialgHom (H := H) b).toAlgHom := by
    apply GeneralLinear.coordinateHopfAlgebra_algHom_ext k n
    intro i j
    have h : φ (coefficientMatrix (C := H) b i j) = (1 : Matrix (Fin n) (Fin n) K) i j := by
      simpa only [Matrix.map_apply, BialgHom.toCoalgHom_apply] using congrFun (congrFun hone i) j
    simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom, coordinateBialgHom_X, h,
      Bialgebra.counitAlgHom_apply, counit_coefficientMatrix, Matrix.one_apply]
    split_ifs <;> simp
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  exact AlgHom.congr_fun hcomp y

/-- **A diagonalizable closed subgroup of a reduced unipotent group is trivial**, over an
algebraically closed field. If a surjective bialgebra morphism `H → K` exhibits the group
represented by `K` as a closed subgroup, and `K` is spanned by its group-like elements, then `K`
is the base field. No reducedness of `K` is assumed. -/
theorem bijective_algebraMap_of_surjective [IsAlgClosed k] [Algebra.FiniteType k H]
    [IsReduced H]
    (hH : geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.of k H))
    (hK : Subcoalgebra.groupLikeSetSpan (R := k) (C := K) Set.univ = ⊤)
    (φ : H →ₐc[k] K) (hφ : Function.Surjective φ) :
    Function.Bijective (algebraMap k K) := by
  have h := eq_of_groupLikeSetSpan_eq_top hH hK φ
  refine ⟨Bialgebra.algebraMap_injective K, fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hφ y
  exact ⟨Bialgebra.counitAlgHom k H x, (AlgHom.congr_fun h x).symm⟩

end geometricallyUnipotentPointsCommHopfAlgProperty

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Embedding
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Flag.Triangular

/-!
# Upper triangular embeddings from weight vectors

If every nonzero finite-dimensional representation of an affine group has a weight vector,
then a finite-type group embeds as a closed subgroup of an upper triangular general linear
group. A finite-dimensional subcomodule of the regular comodule generates the coordinate
algebra by its coefficients. The weight-vector hypothesis triangularizes this comodule, so
its faithful coordinate morphism factors through the upper triangular quotient.

This combines `Comodule.exists_finite_subcomodule_matrixCoefficientSubalgebra_eq_top` with
`Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_weight_vectors`. It applies
both to Lie--Kolchin triangularization and to triangularization of the differentiated action.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 4 and 16.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

/-- If every nonzero finite-dimensional comodule has a weight vector, the represented
finite-type affine group is a closed subgroup of some upper triangular general linear group.
The surjection runs in the contravariant coordinate direction. -/
theorem exists_upperTriangular_surjective_of_weight_vectors
    {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]
    [Algebra.FiniteType k H]
    (hweight : ∀ (V : Type u) [AddCommGroup V] [Module k V] [Comodule k H V]
      [FiniteDimensional k V] [Nontrivial V], Comodule.HasNonzeroWeightVector k H V) :
    ∃ (n : ℕ) (f : GeneralLinear.UpperTriangular.coordinateHopfAlgebra k n ⟶
      _root_.CommHopfAlgCat.of k H), Function.Surjective f.hom := by
  obtain ⟨M, hfinite, hcoeff⟩ :=
    Comodule.exists_finite_subcomodule_matrixCoefficientSubalgebra_eq_top (k := k) (C := H)
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : Module.Finite k M := hfinite
  obtain ⟨n, b, htri, -⟩ :=
    Comodule.exists_basis_coefficientMatrix_isUpperTriangular_of_weight_vectors hweight
      (M := M)
  let π := CommHopfAlgCat.ofHom (Comodule.coordinateBialgHom (H := H) b)
  have hπ : Function.Surjective π.hom.toAlgHom := by
    rw [← AlgHom.range_eq_top]
    apply top_unique
    rw [← hcoeff]
    exact Comodule.matrixCoefficientSubalgebra_le_coordinateBialgHom_range b
  have hker := GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal_le_ker k n
    π.hom.toAlgHom (fun i j hji ↦ by
      simpa only [π, CommHopfAlgCat.hom_ofHom, BialgHom.coe_toAlgHom,
        Comodule.coordinateBialgHom_X] using htri hji)
  exact ⟨n, CommHopfAlgCat.liftQuotient _ π hker,
    CommHopfAlgCat.liftQuotient_surjective_of_surjective _ π hker hπ⟩

end TauCeti

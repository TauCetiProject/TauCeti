/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Scheme
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Primitive
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.OrderedProduct
public import Mathlib.Algebra.MvPolynomial.Eval
import TauCeti.Algebra.Group.Hom.Rational
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# Integral recovery of ordered Chevalley root parameters

For a list of distinct roots positive for a common rational degree, the parameters of
an ordered product belong to every integral subalgebra containing its matrix entries.
Thus each root coordinate is an integral polynomial in the entries of the product.
This is the coordinate-algebra input for closed root-product charts.

The proof uses `Matrix.raisesDegree_list_prod_sub` to subtract the factors of smaller
degree. On an exact root weight shift the remainder is the linear root operator.
`ChevalleyDatum.exists_isPrimitive_chevalleySystem_apply` supplies an integral linear
combination of its entries equal to one. No division is needed.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Every root parameter in a distinct-root ordered product of positive degree lies in
any integral subalgebra containing the matrix entries of that product. -/
theorem parameters_mem_of_list_prod_rootSubgroupPoints_mem
    {A : Type*} [CommRing A] {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (degree : (Fin t.rank → ℤ) →+ ℚ)
    (hdegree : ∀ γ ∈ l, 0 < degree ((t.simplyConnectedRootDatum ht).root γ))
    (S : Subalgebra ℤ A) (u : Fin t.numRoots → A)
    (hprod : ∀ r s,
      (l.map fun γ ↦ ((D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ)) :
        Matrix.GeneralLinearGroup (Fin D.dim) A) :
          Matrix (Fin D.dim) (Fin D.dim) A)).prod r s ∈ S) :
    ∀ γ ∈ l, u γ ∈ S := by
  obtain ⟨n, degreeℤ, hn, hdegreeℤ'⟩ := degree.exists_pos_nat_mul_eq_intCast
  have hdegreeℤ (γ : Fin t.numRoots) (hγ : γ ∈ l) :
      0 < degreeℤ ((t.simplyConnectedRootDatum ht).root γ) := by
    have h := mul_pos (Nat.cast_pos.mpr hn : (0 : ℚ) < n) (hdegree γ hγ)
    rw [hdegreeℤ'] at h
    exact_mod_cast h
  apply parameters_mem_of_list_prod_kostantRootSubgroupMatrix_mem
    (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice
    (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator)
    (isNilpotent_apply_ι_chevalleySystem D.representation
      D.isNilpotent_representation_rootGenerator)
    (b := D.basis) (wt := D.weight) (α := (t.simplyConnectedRootDatum ht).root)
    (degree := degreeℤ) D.isCartanWeightVector_basis
    (hl.map (t.simplyConnectedRootDatum ht).root.injective)
    (fun γ _ ↦ t.lie_lieBasis_h_chevalleySystem ht γ) hdegreeℤ ?_ S u ?_
  · intro γ _
    obtain ⟨m, w, hmw, hw⟩ := D.exists_isPrimitive_chevalleySystem_apply γ
    refine ⟨m, ?_⟩
    have heq : kostantRootOperator (t.chevalleySystem ht) (t.lieBasis ht).h
        D.representation D.lattice
        (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
          D.representation_mem_lattice D.isNilpotent_representation_rootGenerator) γ m = w := by
      apply Subtype.ext
      simpa only [coe_kostantRootOperator_apply] using hmw
    exact heq.symm ▸ hw
  · have hroot (γ : Fin t.numRoots) :
        kostantRootSubgroupMatrix (t.chevalleySystem ht) (t.lieBasis ht).h
          D.representation D.lattice
          (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
            D.representation_mem_lattice D.isNilpotent_representation_rootGenerator)
          γ (isNilpotent_apply_ι_chevalleySystem D.representation
            D.isNilpotent_representation_rootGenerator γ) D.basis
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd (u γ))) =
          (D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ)) :
            Matrix.GeneralLinearGroup (Fin D.dim) A) := by
      rw [kostantRootSubgroupMatrix_eq_matrix_chevalleyRootSubgroup,
        MulEquiv.apply_symm_apply, coe_rootSubgroupPoints]
    simpa only [hroot] using hprod

/-- Positive-root parameters are integral polynomials in the entries of their ordered
product, in the form of recovery inside every integral subalgebra. -/
theorem parameters_mem_of_list_prod_rootSubgroupPoints_mem_of_posRoots
    {A : Type*} [CommRing A] {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (hpos : ∀ γ ∈ l, γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (S : Subalgebra ℤ A) (u : Fin t.numRoots → A)
    (hprod : ∀ r s, (l.map fun γ ↦
      ((D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ)) :
        Matrix.GeneralLinearGroup (Fin D.dim) A) :
          Matrix (Fin D.dim) (Fin D.dim) A)).prod r s ∈ S) :
    ∀ γ ∈ l, u γ ∈ S :=
  D.parameters_mem_of_list_prod_rootSubgroupPoints_mem hl (t.weightDegree ht)
    (fun γ hγ ↦ t.weightDegree_root_pos ht (hpos γ hγ)) S u hprod

/-- Negative-root parameters are integral polynomials in the entries of their ordered
product, in the form of recovery inside every integral subalgebra. -/
theorem parameters_mem_of_list_prod_rootSubgroupPoints_mem_of_negRoots
    {A : Type*} [CommRing A] {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (hneg : ∀ γ ∈ l, γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (S : Subalgebra ℤ A) (u : Fin t.numRoots → A)
    (hprod : ∀ r s, (l.map fun γ ↦
      ((D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ)) :
        Matrix.GeneralLinearGroup (Fin D.dim) A) :
          Matrix (Fin D.dim) (Fin D.dim) A)).prod r s ∈ S) :
    ∀ γ ∈ l, u γ ∈ S :=
  D.parameters_mem_of_list_prod_rootSubgroupPoints_mem hl (-(t.weightDegree ht))
    (fun γ hγ ↦ neg_pos.mpr (t.weightDegree_root_neg ht (hneg γ hγ))) S u hprod

/-- The entries of the universal ordered root product generate the entire polynomial
parameter ring over `ℤ`. There is one variable for each root occurring in the list. -/
theorem adjoin_universalRootProduct_eq_top
    {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (degree : (Fin t.rank → ℤ) →+ ℚ)
    (hdegree : ∀ γ ∈ l, 0 < degree ((t.simplyConnectedRootDatum ht).root γ)) :
    let u : Fin t.numRoots → MvPolynomial {γ // γ ∈ l} ℤ :=
      fun γ ↦ if hγ : γ ∈ l then MvPolynomial.X ⟨γ, hγ⟩ else 0
    let P := (l.map fun γ ↦
      ((D.rootSubgroupPoints γ _ (Multiplicative.ofAdd (u γ)) :
        Matrix.GeneralLinearGroup (Fin D.dim) (MvPolynomial {γ // γ ∈ l} ℤ)) :
          Matrix (Fin D.dim) (Fin D.dim) (MvPolynomial {γ // γ ∈ l} ℤ))).prod
    Algebra.adjoin ℤ (Set.range fun rs : Fin D.dim × Fin D.dim ↦ P rs.1 rs.2) = ⊤ := by
  classical
  let u : Fin t.numRoots → MvPolynomial {γ // γ ∈ l} ℤ :=
    fun γ ↦ if hγ : γ ∈ l then MvPolynomial.X ⟨γ, hγ⟩ else 0
  let P := (l.map fun γ ↦
    ((D.rootSubgroupPoints γ _ (Multiplicative.ofAdd (u γ)) :
      Matrix.GeneralLinearGroup (Fin D.dim) (MvPolynomial {γ // γ ∈ l} ℤ)) :
          Matrix (Fin D.dim) (Fin D.dim) (MvPolynomial {γ // γ ∈ l} ℤ))).prod
  have hmem := D.parameters_mem_of_list_prod_rootSubgroupPoints_mem hl degree hdegree
    (Algebra.adjoin ℤ (Set.range fun rs : Fin D.dim × Fin D.dim ↦ P rs.1 rs.2)) u
    (fun r s ↦ Algebra.subset_adjoin (Set.mem_range_self (r, s)))
  apply top_unique
  rw [← MvPolynomial.adjoin_range_X, Algebra.adjoin_le_iff]
  rintro _ ⟨γ, rfl⟩
  rcases γ with ⟨γ, hγ⟩
  simpa only [P, u, dite_eq_left hγ] using! hmem γ hγ

end TauCeti.DynkinType.ChevalleyDatum

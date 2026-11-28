/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Primitive
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Scheme
import TauCeti.Algebra.Group.Hom.Rational
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.OrderedProduct
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# Uniqueness and integral recovery of ordered root products for a Chevalley datum

Over every commutative ring and for **any** Chevalley datum `D`, a product of distinct root
elements in any fixed order determines all its parameters, provided all its roots have positive
degree for one rational degree map on integral weights. This covers lists of positive roots, with
the height degree, and lists of negative roots, with its negative, so also any enumeration of all
of them, regardless of the isogeny type of `D`.

This is the uniqueness half of positive-root factorization on `D.positivePoints A`, pairing with
positive-root collection in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.Collection.Basic` to
build the coordinate bijection `ChevalleyDatum.positiveRootEquiv` in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Coordinates`, and supplying the point-level
faithfulness needed for scheme-theoretic monomorphicity of `D.rootProduct` in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Scheme`.

The proof applies `list_prod_map_kostantRootSubgroupParam_inj` to the named all-root
Chevalley system, with a positive integral multiple of the degree. Thus no restriction on
characteristic or reducedness is needed.

With primitive root operators, every parameter belongs to any integral subalgebra containing
the entries of the product. This supplies polynomial coordinate recovery for closed root-product
charts without division or restrictions on the value ring.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.list_prod_map_rootSubgroupPoints_inj_of_degree`: ordered
  products of distinct roots of positive degree determine their parameters.
* `TauCeti.DynkinType.ChevalleyDatum.list_prod_map_rootSubgroupPoints_inj`: an ordered product of
  distinct positive root elements of `D` determines its parameters over every commutative ring.

* `TauCeti.DynkinType.ChevalleyDatum.parameters_mem_of_list_prod_rootSubgroupPoints_mem`:
  integral recovery of the parameters from the matrix entries of their ordered product.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

attribute [local instance high] Algebra.toModule

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- **Uniqueness of ordered root products for a degree.** In the point group of any Chevalley
datum, an ordered product of distinct root elements whose roots all have positive degree for one
rational degree map on integral weights determines exactly the parameters of the roots occurring
in the list. The order is arbitrary and the value ring may have nilpotents or positive
characteristic. -/
theorem list_prod_map_rootSubgroupPoints_inj_of_degree (A : Type v) [CommRing A]
    {l : List (Fin t.numRoots)} (hl : l.Nodup) (degree : (Fin t.rank → ℤ) →+ ℚ)
    (hdegree : ∀ γ ∈ l, 0 < degree ((t.simplyConnectedRootDatum ht).root γ))
    {u v : Fin t.numRoots → A} :
    (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ))).prod =
      (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (v γ))).prod ↔
      ∀ γ ∈ l, u γ = v γ := by
  -- A positive multiple of the degree is integral, and positive on the same roots.
  obtain ⟨n, degreeℤ, hn, hdegreeℤ'⟩ := degree.exists_pos_nat_mul_eq_intCast
  have hdegreeℤ (γ : Fin t.numRoots) (hγ : γ ∈ l) :
      0 < degreeℤ ((t.simplyConnectedRootDatum ht).root γ) := by
    have h := mul_pos (Nat.cast_pos.mpr hn : (0 : ℚ) < n) (hdegree γ hγ)
    rw [hdegreeℤ'] at h
    exact_mod_cast h
  let hAll := kostantForm_chevalleySystem_smul_mem D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator
  have hnative := list_prod_map_kostantRootSubgroupParam_inj
    (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice hAll
    (isNilpotent_apply_ι_chevalleySystem D.representation
      D.isNilpotent_representation_rootGenerator)
    (b := D.basis) (wt := D.weight) (α := (t.simplyConnectedRootDatum ht).root)
    (degree := degreeℤ) A D.isCartanWeightVector_basis
    (hl.map (t.simplyConnectedRootDatum ht).root.injective)
    (fun γ _ => t.lie_lieBasis_h_chevalleySystem ht γ)
    hdegreeℤ
    (fun γ _ c hc =>
      (D.smul_baseChange_kostantRootOperator_chevalleySystem_eq_zero_iff γ A c).mp hc)
    (u := u) (v := v)
  simp only [kostantRootSubgroupParam_chevalleySystem D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator] at hnative
  constructor
  · intro huv
    apply hnative.mp
    apply Units.map_injective (f := (LinearMap.toMatrixAlgEquiv
      (D.basis.baseChange A)).toMulEquiv.toMonoidHom)
      (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).injective
    have hmat := congrArg (D.points A).subtype huv
    simpa only [map_list_prod, List.map_map, Function.comp_def, Subgroup.subtype_apply,
      coe_rootSubgroupPoints, MulEquiv.toMonoidHom_eq_coe] using hmat
  · intro huv
    exact congrArg List.prod (List.map_congr_left fun γ hγ => by rw [huv γ hγ])

/-- In the point group of any Chevalley datum, an ordered product of distinct positive root
elements determines the parameters of all roots occurring in the list. The order is arbitrary and
the value ring may have nilpotents or arbitrary characteristic. -/
theorem list_prod_map_rootSubgroupPoints_inj (A : Type v) [CommRing A]
    {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (hpos : ∀ γ ∈ l, γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    {u v : Fin t.numRoots → A} :
    (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ))).prod =
      (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (v γ))).prod ↔
      ∀ γ ∈ l, u γ = v γ :=
  D.list_prod_map_rootSubgroupPoints_inj_of_degree A hl (t.weightDegree ht)
    fun _ hγ => t.weightDegree_root_pos ht (hpos _ hγ)

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

end TauCeti.DynkinType.ChevalleyDatum

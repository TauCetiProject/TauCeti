/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Injective
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.OrderedProduct
import TauCeti.Algebra.Group.Hom.Rational
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# Uniqueness of ordered positive-root and negative-root products in Chevalley groups

Over every commutative ring and for every Chevalley datum `D`, a product of distinct positive root
elements — or of distinct negative root elements — in any fixed order determines all its
parameters. The results apply to any duplicate-free list of positive (respectively negative) roots,
so also to any enumeration of all positive or all negative roots, in the point group of any
Chevalley datum. They supply uniqueness of root-subgroup coordinates on both unipotent factors;
existence of such coordinates is proved in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Collection` and
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Opposite`.

The proofs apply `list_prod_map_kostantRootSubgroupParam_inj` to the named all-root Chevalley
system with the positive and negated height functionals. Their operator-faithfulness hypothesis is
discharged integrally for every Chevalley datum by
`ChevalleyDatum.smul_baseChange_kostantRootOperator_eq_zero_iff`, so no restriction on
characteristic, reducedness, or the weight lattice is needed.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- In the point group of any Chevalley datum, an ordered product of distinct positive root
elements determines the parameters of all roots occurring in the list. The order is arbitrary and
the value ring may have nilpotents or bad characteristic. -/
theorem list_prod_map_rootSubgroupPoints_inj (A : Type*) [CommRing A]
    {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (hpos : ∀ γ ∈ l, γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    {u v : Fin t.numRoots → A} :
    (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ))).prod =
        (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (v γ))).prod ↔
      ∀ γ ∈ l, u γ = v γ := by
  obtain ⟨n, degree, hn, hdegree⟩ := (t.weightDegree ht).exists_pos_nat_mul_eq_intCast
  have hposdegree (γ : Fin t.numRoots) (hγ : γ ∈ l) :
      0 < degree ((t.simplyConnectedRootDatum ht).root γ) := by
    have h := mul_pos (Nat.cast_pos.mpr hn : (0 : ℚ) < n)
      (t.weightDegree_root_pos ht (hpos γ hγ))
    rw [hdegree] at h
    exact_mod_cast h
  let hAll := kostantForm_chevalleySystem_smul_mem D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator
  have hnative := list_prod_map_kostantRootSubgroupParam_inj
    (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice hAll
    (isNilpotent_apply_ι_chevalleySystem D.representation
      D.isNilpotent_representation_rootGenerator)
    (b := D.basis) (wt := D.weight) (α := (t.simplyConnectedRootDatum ht).root)
    (degree := degree) A D.isCartanWeightVector_basis
    (hl.map (t.simplyConnectedRootDatum ht).root.injective)
    (fun γ _ => t.lie_lieBasis_h_chevalleySystem ht γ)
    hposdegree
    (fun γ _ c hc => (D.smul_baseChange_kostantRootOperator_eq_zero_iff γ A c).mp hc)
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
      ChevalleyDatum.coe_rootSubgroupPoints, MulEquiv.toMonoidHom_eq_coe] using hmat
  · intro huv
    exact congrArg List.prod (List.map_congr_left fun γ hγ => by rw [huv γ hγ])

/-- In the point group of any Chevalley datum, an ordered product of distinct negative root
elements determines the parameters of all roots occurring in the list, over any commutative ring.
-/
theorem list_prod_map_rootSubgroupPoints_inj_of_negRoots (A : Type*) [CommRing A]
    {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (hneg : ∀ γ ∈ l, γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    {u v : Fin t.numRoots → A} :
    (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ))).prod =
        (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (v γ))).prod ↔
      ∀ γ ∈ l, u γ = v γ := by
  obtain ⟨n, degree, hn, hdegree⟩ := (t.weightDegree ht).exists_pos_nat_mul_eq_intCast
  have hnegdegree (γ : Fin t.numRoots) (hγ : γ ∈ l) :
      0 < (-degree) ((t.simplyConnectedRootDatum ht).root γ) := by
    have h := mul_neg_of_pos_of_neg (Nat.cast_pos.mpr hn : (0 : ℚ) < n)
      (t.weightDegree_root_neg ht (hneg γ hγ))
    rw [hdegree] at h
    have h' : (0 : ℚ) < -((degree ((t.simplyConnectedRootDatum ht).root γ) : ℤ) : ℚ) :=
      neg_pos.mpr h
    exact_mod_cast h'
  let hAll := kostantForm_chevalleySystem_smul_mem D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator
  have hnative := list_prod_map_kostantRootSubgroupParam_inj
    (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice hAll
    (isNilpotent_apply_ι_chevalleySystem D.representation
      D.isNilpotent_representation_rootGenerator)
    (b := D.basis) (wt := D.weight) (α := (t.simplyConnectedRootDatum ht).root)
    (degree := -degree) A D.isCartanWeightVector_basis
    (hl.map (t.simplyConnectedRootDatum ht).root.injective)
    (fun γ _ => t.lie_lieBasis_h_chevalleySystem ht γ)
    hnegdegree
    (fun γ _ c hc => (D.smul_baseChange_kostantRootOperator_eq_zero_iff γ A c).mp hc)
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
      ChevalleyDatum.coe_rootSubgroupPoints, MulEquiv.toMonoidHom_eq_coe] using hmat
  · intro huv
    exact congrArg List.prod (List.map_congr_left fun γ hγ => by rw [huv γ hγ])

end TauCeti.DynkinType.ChevalleyDatum

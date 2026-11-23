/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Faithful
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.OrderedProduct
import TauCeti.Algebra.Group.Hom.Rational
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# Uniqueness of ordered root products in Chevalley groups

Over every commutative ring and for every Chevalley datum `D`, an ordered product of distinct roots
lying in any open half-space `{γ | 0 < degree (root γ)}` determines all its parameters. Specializing
to the positive and negated height functionals gives parameter uniqueness for ordered positive-root
and negative-root products, supplying the uniqueness half of root-subgroup coordinates in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Coordinates` and
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Opposite.Coordinates`, as well as scheme monomorphicity in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Product`.

The proof applies `list_prod_map_kostantRootSubgroupParam_inj` to the named all-root Chevalley
system and discharges its operator-faithfulness hypothesis integrally via
`ChevalleyDatum.smul_baseChange_kostantRootOperator_eq_zero_iff`, so no restriction on
characteristic, reducedness, or the weight lattice is needed.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.list_prod_map_rootSubgroupPoints_inj_of_degree_pos`: parameter
  uniqueness for ordered root products in any open half-space `{γ | 0 < degree (root γ)}`.
* `TauCeti.DynkinType.ChevalleyDatum.list_prod_map_rootSubgroupPoints_inj_of_posRoots` and
  `TauCeti.DynkinType.ChevalleyDatum.list_prod_map_rootSubgroupPoints_inj_of_negRoots`:
  specializations to positive and negative root lists.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- In the point group of any Chevalley datum, an ordered product of distinct roots on which an
additive rational weight functional `degree` is strictly positive determines the parameters of all
roots occurring in the list, over any commutative ring. -/
theorem list_prod_map_rootSubgroupPoints_inj_of_degree_pos (A : Type*) [CommRing A]
    (degree : (Fin t.rank → ℤ) →+ ℚ) {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (hdeg : ∀ γ ∈ l, 0 < degree ((t.simplyConnectedRootDatum ht).root γ))
    {u v : Fin t.numRoots → A} :
    (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ))).prod =
        (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (v γ))).prod ↔
      ∀ γ ∈ l, u γ = v γ := by
  obtain ⟨n, degreeZ, hn, hdegreeZ⟩ := degree.exists_pos_nat_mul_eq_intCast
  have hposZ (γ : Fin t.numRoots) (hγ : γ ∈ l) :
      0 < degreeZ ((t.simplyConnectedRootDatum ht).root γ) := by
    have h := mul_pos (Nat.cast_pos.mpr hn : (0 : ℚ) < n) (hdeg γ hγ)
    rw [hdegreeZ] at h
    exact_mod_cast h
  let hAll := kostantForm_chevalleySystem_smul_mem D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator
  have hnative := list_prod_map_kostantRootSubgroupParam_inj
    (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice hAll
    (isNilpotent_apply_ι_chevalleySystem D.representation
      D.isNilpotent_representation_rootGenerator)
    (b := D.basis) (wt := D.weight) (α := (t.simplyConnectedRootDatum ht).root)
    (degree := degreeZ) A D.isCartanWeightVector_basis
    (hl.map (t.simplyConnectedRootDatum ht).root.injective)
    (fun γ _ => t.lie_lieBasis_h_chevalleySystem ht γ)
    hposZ
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

/-- In the point group of any Chevalley datum, an ordered product of distinct positive root
elements determines the parameters of all roots occurring in the list. The order is arbitrary and
the value ring may have nilpotents or bad characteristic. -/
theorem list_prod_map_rootSubgroupPoints_inj_of_posRoots (A : Type*) [CommRing A]
    {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (hpos : ∀ γ ∈ l, γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    {u v : Fin t.numRoots → A} :
    (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ))).prod =
        (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (v γ))).prod ↔
      ∀ γ ∈ l, u γ = v γ :=
  D.list_prod_map_rootSubgroupPoints_inj_of_degree_pos A (t.weightDegree ht) hl
    (fun γ hγ => t.weightDegree_root_pos ht (hpos γ hγ))

/-- In the point group of any Chevalley datum, an ordered product of distinct negative root
elements determines the parameters of all roots occurring in the list, over any commutative ring.
-/
theorem list_prod_map_rootSubgroupPoints_inj_of_negRoots (A : Type*) [CommRing A]
    {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (hneg : ∀ γ ∈ l, γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    {u v : Fin t.numRoots → A} :
    (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ))).prod =
        (l.map fun γ => D.rootSubgroupPoints γ A (Multiplicative.ofAdd (v γ))).prod ↔
      ∀ γ ∈ l, u γ = v γ :=
  D.list_prod_map_rootSubgroupPoints_inj_of_degree_pos A (-t.weightDegree ht) hl
    (fun γ hγ => neg_pos.mpr (t.weightDegree_root_neg ht (hneg γ hγ)))

end TauCeti.DynkinType.ChevalleyDatum

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.SimplyConnected
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.OrderedProduct
import TauCeti.Algebra.Group.Hom.Rational
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.SimplyConnectedModule.RootSubgroup
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# Uniqueness of ordered positive-root products in the full-weight Chevalley model

Over every commutative ring, a product of distinct positive root elements in any fixed
order determines all its parameters. The result applies to any list of positive roots,
so also to any enumeration of all positive roots, in the existing full-weight Chevalley
point group. It supplies uniqueness of positive-root coordinates; existence of such
coordinates for every element of the positive subgroup is a separate collection theorem.

The proof applies `list_prod_map_kostantRootSubgroupParam_inj` to the named all-root
Chevalley system. Its operator-faithfulness hypothesis is discharged integrally: the
fundamental modules supply primitive simple-root steps, transported to every root by
Weyl automorphisms. Thus no restriction on characteristic or reducedness is needed.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3.
-/

public section

namespace TauCeti.DynkinType

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

/-- In the full-weight Chevalley point group, an ordered product of distinct positive
root elements determines exactly the parameters of the roots occurring in the list.
The order is arbitrary and the value ring may have nilpotents or positive characteristic. -/
theorem list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj (A : Type*) [CommRing A]
    {l : List (Fin t.numRoots)} (hl : l.Nodup)
    (hpos : ∀ γ ∈ l, γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    {u v : Fin t.numRoots → A} :
    (l.map fun γ => (t.scChevalleyDatum ht).rootSubgroupPoints γ A
      (Multiplicative.ofAdd (u γ))).prod =
        (l.map fun γ => (t.scChevalleyDatum ht).rootSubgroupPoints γ A
          (Multiplicative.ofAdd (v γ))).prod ↔ ∀ γ ∈ l, u γ = v γ := by
  obtain ⟨n, degree, hn, hdegree⟩ := (t.weightDegree ht).exists_pos_nat_mul_eq_intCast
  have hposdegree (γ : Fin t.numRoots) (hγ : γ ∈ l) :
      0 < degree ((t.simplyConnectedRootDatum ht).root γ) := by
    have h := mul_pos (Nat.cast_pos.mpr hn : (0 : ℚ) < n)
      (t.weightDegree_root_pos ht (hpos γ hγ))
    rw [hdegree] at h
    exact_mod_cast h
  let D := t.scChevalleyDatum ht
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
    (fun γ _ c hc =>
      (t.smul_baseChange_kostantRootOperator_chevalleySystem_scLattice_eq_zero_iff ht γ A c).mp hc)
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
      ChevalleyDatum.coe_rootSubgroupPoints, MulEquiv.toMonoidHom_eq_coe, D] using hmat
  · intro huv
    exact congrArg List.prod (List.map_congr_left fun γ hγ => by rw [huv γ hγ])

end TauCeti.DynkinType

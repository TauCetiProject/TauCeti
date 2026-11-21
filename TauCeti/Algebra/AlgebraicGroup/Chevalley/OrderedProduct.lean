/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Primitive
import TauCeti.Algebra.Group.Hom.Rational
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.OrderedProduct
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# Uniqueness of ordered positive-root products for a Chevalley datum

Over every commutative ring and for **any** Chevalley datum `D`, a product of distinct positive
root elements in any fixed order determines all its parameters. The result applies to any
duplicate-free list of positive roots, and in particular to any enumeration of all positive roots,
regardless of the isogeny type of `D`. As a special case on singleton lists together with Weyl
conjugation, every root subgroup of `D` is injective on `A`-points.

This is the uniqueness half of positive-root factorization on `D.positivePoints A`, pairing with
positive-root collection in `TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Collection` to build
the coordinate bijection `ChevalleyDatum.positivePointsEquiv` in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Coordinates`, and supplying the point-level
faithfulness needed for scheme-theoretic monomorphicity of `D.rootProduct` in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Scheme`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.list_prod_map_rootSubgroupPoints_inj`: an ordered product of
  distinct positive root elements of `D` determines its parameters over every commutative ring.
* `TauCeti.DynkinType.ChevalleyDatum.rootSubgroupPoints_injective`: every root subgroup of `D` is
  injective on `A`-points over every commutative ring.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.3.3.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open TensorProduct TauCeti.UniversalEnvelopingAlgebra

attribute [local instance high] Algebra.toModule

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- In the point group of any Chevalley datum, an ordered product of distinct positive root
elements determines the parameters of all roots occurring in the list. The order is arbitrary and
the value ring may have nilpotents or arbitrary characteristic. -/
theorem list_prod_map_rootSubgroupPoints_inj (A : Type v) [CommRing A]
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

/-- Every root subgroup of a Chevalley datum is injective over every commutative ring, including
nonreduced rings and rings of small characteristic. -/
theorem rootSubgroupPoints_injective (γ : Fin t.numRoots) (A : Type v) [CommRing A] :
    Function.Injective (D.rootSubgroupPoints γ A) := by
  refine D.rootSubgroupPoints_injective_of_simple A (fun i u v huv => ?_) γ
  have h := (D.list_prod_map_rootSubgroupPoints_inj A (List.nodup_singleton (t.simpleIndex ht i))
    (fun _ hγ => List.mem_singleton.mp hγ ▸ simpleIndex_mem_posRoots i)
    (u := Function.const _ u.toAdd) (v := Function.const _ v.toAdd)).mp
    (by simpa using huv) (t.simpleIndex ht i) (List.mem_singleton_self _)
  exact Multiplicative.toAdd.injective h

end TauCeti.DynkinType.ChevalleyDatum

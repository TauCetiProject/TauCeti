/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Collection
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.SimplyConnected
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.OrderedProduct
import TauCeti.Algebra.Group.Hom.Rational
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.SimplyConnectedModule.RootSubgroup
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# Existence and uniqueness of ordered positive-root products in the full-weight Chevalley model

Over every commutative ring, a product of distinct positive root elements in any fixed
order in the full-weight Chevalley point group determines all its parameters uniquely, and every
element of the positive subgroup `(t.scChevalleyDatum ht).positivePoints A` arises from a unique
tuple of positive-root parameters. The result holds for any duplicate-free enumeration of the
positive roots and any commutative ring, including rings with nilpotents or bad characteristic.

Uniqueness applies `list_prod_map_kostantRootSubgroupParam_inj` to the named all-root Chevalley
system, using the fundamental modules and Weyl automorphisms to supply primitive root steps
integrally. Existence comes from `ChevalleyDatum.mem_positivePoints_iff_exists_prod`, yielding the
ordered-product coordinate equivalence `scPositivePointsProdEquiv`.

## Main declarations

* `TauCeti.DynkinType.list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj`: distinct positive
  root factors in any order determine their parameters uniquely.
* `TauCeti.DynkinType.scPositivePointsProdEquiv`: Steinberg's bijection between positive-root
  parameter tuples and `(t.scChevalleyDatum ht).positivePoints A`.

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

private noncomputable def scPositivePointsProdMap (A : Type*) [CommRing A]
    (l : List (Fin t.numRoots))
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (u : posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A) :
    (t.scChevalleyDatum ht).positivePoints A :=
  ⟨(l.attach.map fun x => (t.scChevalleyDatum ht).rootSubgroupPoints x.1 A
      (Multiplicative.ofAdd (u ⟨x.1, (hcover x.1).mp x.2⟩))).prod,
    Subgroup.list_prod_mem _ fun _ hx => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hx
      exact (t.scChevalleyDatum ht).rootSubgroupPoints_mem_positivePoints A
        ((hcover x.1).mp x.2) _⟩

private theorem scPositivePointsProdMap_bijective (A : Type*) [CommRing A]
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    Function.Bijective (t.scPositivePointsProdMap ht A l hcover) := by
  classical
  let extParam (u : posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A)
      (γ : Fin t.numRoots) : A :=
    if h : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) then u ⟨γ, h⟩ else 0
  have hval (u : posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A) :
      (t.scPositivePointsProdMap ht A l hcover u : (t.scChevalleyDatum ht).points A) =
        (l.map fun γ => (t.scChevalleyDatum ht).rootSubgroupPoints γ A
          (Multiplicative.ofAdd (extParam u γ))).prod := by
    dsimp only [scPositivePointsProdMap]
    rw [← List.attach_map_val (l := l)]
    exact congrArg List.prod (List.map_congr_left fun x _ => by
      simp only [extParam, (hcover x.1).mp x.2, ↓reduceDIte])
  refine ⟨?_, ?_⟩
  · intro u v huv
    have hprod : (l.map fun γ => (t.scChevalleyDatum ht).rootSubgroupPoints γ A
        (Multiplicative.ofAdd (extParam u γ))).prod =
        (l.map fun γ => (t.scChevalleyDatum ht).rootSubgroupPoints γ A
          (Multiplicative.ofAdd (extParam v γ))).prod := by
      rw [← hval u, ← hval v, huv]
    have heq := (t.list_prod_map_scChevalleyDatum_rootSubgroupPoints_inj ht A hl
      (fun γ hγ => (hcover γ).mp hγ)).mp hprod
    ext ⟨γ, hγ⟩
    simpa only [extParam, hγ, ↓reduceDIte] using heq γ ((hcover γ).mpr hγ)
  · rintro ⟨g, hg⟩
    obtain ⟨w, rfl⟩ :=
      ((t.scChevalleyDatum ht).mem_positivePoints_iff_exists_prod A l hl hcover g).mp hg
    refine ⟨fun γ => (w γ.1).toAdd, Subtype.ext ?_⟩
    dsimp only [scPositivePointsProdMap]
    rw [← List.attach_map_val (f := fun γ => (t.scChevalleyDatum ht).rootSubgroupPoints γ A (w γ))]
    exact congrArg List.prod (List.map_congr_left fun _ _ => by simp only [ofAdd_toAdd])

/-- Steinberg's ordered positive-root product equivalence for the full-weight Chevalley datum:
for any duplicate-free enumeration `l` of the positive roots and any commutative ring `A`,
forming the ordered product `∏_{γ ∈ l} x_γ(u_γ)` is a bijection from positive-root parameter
tuples onto `(t.scChevalleyDatum ht).positivePoints A`. -/
noncomputable def scPositivePointsProdEquiv (A : Type*) [CommRing A]
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) :
    (posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A) ≃
      (t.scChevalleyDatum ht).positivePoints A :=
  Equiv.ofBijective (t.scPositivePointsProdMap ht A l hcover)
    (t.scPositivePointsProdMap_bijective ht A l hl hcover)

/-- Evaluating `scPositivePointsProdEquiv` computes the ordered positive-root product along `l`. -/
@[simp]
theorem coe_scPositivePointsProdEquiv_apply (A : Type*) [CommRing A]
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (u : posRoots (t.rationalRootSystem ht) (t.rationalBase ht) → A) :
    (t.scPositivePointsProdEquiv ht A l hl hcover u : (t.scChevalleyDatum ht).points A) =
      (l.attach.map fun x => (t.scChevalleyDatum ht).rootSubgroupPoints x.1 A
        (Multiplicative.ofAdd (u ⟨x.1, (hcover x.1).mp x.2⟩))).prod :=
  (rfl)

/-- On restricted all-root parameter functions, `scPositivePointsProdEquiv` is the plain list
product along `l`. -/
theorem coe_scPositivePointsProdEquiv_comp_subtype (A : Type*) [CommRing A]
    (l : List (Fin t.numRoots)) (hl : l.Nodup)
    (hcover : ∀ γ, γ ∈ l ↔ γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (u : Fin t.numRoots → A) :
    (t.scPositivePointsProdEquiv ht A l hl hcover (fun γ => u γ.1) :
        (t.scChevalleyDatum ht).points A) =
      (l.map fun γ => (t.scChevalleyDatum ht).rootSubgroupPoints γ A
        (Multiplicative.ofAdd (u γ))).prod := by
  rw [coe_scPositivePointsProdEquiv_apply,
    List.attach_map_val (f := fun γ =>
      (t.scChevalleyDatum ht).rootSubgroupPoints γ A (Multiplicative.ofAdd (u γ)))]

end TauCeti.DynkinType

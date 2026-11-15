/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.Transitivity.Discrete
public import TauCeti.RepresentationTheory.Tensor.Induction.TrivialF2.Basic

/-!
# Trivial F₂ coefficients and tensor-induction transitivity

For an open finite-index tower `V ≤ U ≤ G`, the canonical identification of tensor-induced
trivial `𝔽₂` coefficients with ambient trivial coefficients commutes with transitivity.
Multiplying all factors at once agrees with first multiplying the factors over `U / V` and
then those over `G / U`. The theorem is an equality of morphisms on arbitrary tensors, not just
on diagonal tensors. It supplies the coefficient normalization for transitivity of the Evens norm.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), §6, Proposition 1.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U V : Subgroup G} (hVU : V ≤ U) (s : U.LeftTransversal)
  (t : (V.subgroupOf U).LeftTransversal) (hU : IsOpen (U : Set G)) (hV : IsOpen (V : Set G))
  [U.FiniteIndex] [(V.subgroupOf U).FiniteIndex]

omit [U.FiniteIndex] in
private theorem innerTrivialF2Iso_apply_tprod
    (m : U ⧸ V.subgroupOf U → (DiscreteRep.trivialF2 V).V) :
    letI : Fintype (U ⧸ V.subgroupOf U) := (V.subgroupOf U).fintypeQuotientOfFiniteIndex
    letI : Module ℤ (DiscreteRep.trivialF2 V).V := (DiscreteRep.trivialF2 V).module
    let z := PiTensorProduct.tprod ℤ m
    trivialF2Equiv U
      (((smoothTensorInductionFunctor ℤ U (V.subgroupOf U) (U.subgroupOf_isOpen V hV) t).map
          (eqToHom (smoothResFunctor_trivialF2 V
            (Subgroup.subgroupOfEquivOfLe hVU : V.subgroupOf U →* V)
            (Subgroup.continuous_subgroupOfEquivOfLe hVU))) ≫
        (smoothTensorInducedTrivialF2Iso U (V.subgroupOf U)
          (U.subgroupOf_isOpen V hV) t).hom).hom.hom z) =
      ∏ b, trivialF2Equiv V (m b) := by
  let : Fintype (U ⧸ V.subgroupOf U) := (V.subgroupOf U).fintypeQuotientOfFiniteIndex
  let : Module ℤ (DiscreteRep.trivialF2 V).V := (DiscreteRep.trivialF2 V).module
  let : Module ℤ (trivialF2 (V.subgroupOf U)).V := (trivialF2 (V.subgroupOf U)).hV2
  let A := (smoothResFunctor ℤ
    (Subgroup.subgroupOfEquivOfLe hVU : V.subgroupOf U →* V)
    (Subgroup.continuous_subgroupOfEquivOfLe hVU)).obj
      ⟨trivialF2 V, isSmoothDiscrete_trivialF2 V⟩
  let : Module ℤ A.obj.V := A.obj.hV2
  let e := eqToHom (smoothResFunctor_trivialF2 V
    (Subgroup.subgroupOfEquivOfLe hVU : V.subgroupOf U →* V)
    (Subgroup.continuous_subgroupOfEquivOfLe hVU))
  let z := PiTensorProduct.tprod ℤ m
  -- Expand only composition on carriers; the restriction transport is not an identity
  -- morphism between definitionally equal objects in importing modules.
  change trivialF2Equiv U
    ((smoothTensorInducedTrivialF2Iso U (V.subgroupOf U)
      (U.subgroupOf_isOpen V hV) t).hom.hom.hom
        (((smoothTensorInductionFunctor ℤ U (V.subgroupOf U)
          (U.subgroupOf_isOpen V hV) t).map e).hom.hom z)) = _
  have he := smoothTensorInductionFunctor_map_hom_hom_apply ℤ U (V.subgroupOf U)
    (U.subgroupOf_isOpen V hV) t e z
  refine (congrArg (fun w ↦ trivialF2Equiv U
    ((smoothTensorInducedTrivialF2Iso U (V.subgroupOf U)
      (U.subgroupOf_isOpen V hV) t).hom.hom.hom w)) he).trans ?_
  have hep := PiTensorProduct.map_tprod
    (fun _ : U ⧸ V.subgroupOf U ↦ e.hom.hom.toLinearMap) m
  refine (congrArg (fun w ↦ trivialF2Equiv U
    ((smoothTensorInducedTrivialF2Iso U (V.subgroupOf U)
      (U.subgroupOf_isOpen V hV) t).hom.hom.hom w)) hep).trans ?_
  refine (smoothTensorInducedTrivialF2Iso_hom_apply_piTensorProduct_tprod U
    (V.subgroupOf U) (U.subgroupOf_isOpen V hV) t _).trans ?_
  exact Finset.prod_congr rfl fun b _ ↦
    eqToHom_smoothResFunctor_trivialF2_apply V _ _ (m b)

/-- The transitivity square for tensor-induced trivial `𝔽₂` coefficients, evaluated on a pure
tensor of pure tensors: both routes multiply the same factors of the tower. -/
private theorem smoothTensorInducedTrivialF2Iso_transitivity_hom_apply_tprod
    (m : G ⧸ U → U ⧸ V.subgroupOf U → (DiscreteRep.trivialF2 V).V) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    letI : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
    letI : Fintype (U ⧸ V.subgroupOf U) := (V.subgroupOf U).fintypeQuotientOfFiniteIndex
    letI : Fintype (G ⧸ V) := V.fintypeQuotientOfFiniteIndex
    letI : Module ℤ (DiscreteRep.trivialF2 V).V := (DiscreteRep.trivialF2 V).module
    letI : Module ℤ (trivialF2 U).V := (trivialF2 U).hV2
    letI : Module ℤ (trivialF2 G).V := (trivialF2 G).hV2
    let x := fun a ↦ PiTensorProduct.tprod ℤ (m a)
    let z := PiTensorProduct.tprod ℤ x
    let f := (smoothTensorInductionFunctor ℤ U (V.subgroupOf U)
        (U.subgroupOf_isOpen V hV) t).map
          (eqToHom (smoothResFunctor_trivialF2 V
            (Subgroup.subgroupOfEquivOfLe hVU : V.subgroupOf U →* V)
            (Subgroup.continuous_subgroupOfEquivOfLe hVU))) ≫
        (smoothTensorInducedTrivialF2Iso U (V.subgroupOf U)
          (U.subgroupOf_isOpen V hV) t).hom
    trivialF2Equiv G
        ((smoothTensorInducedTrivialF2Iso G V hV
          (Subgroup.compositeLeftTransversal hVU s t)).hom.hom.hom
            ((smoothTensorInducedTransitivityIso hVU s t hU hV
              ⟨trivialF2 V, isSmoothDiscrete_trivialF2 V⟩).hom.hom.hom z)) =
      trivialF2Equiv G ((smoothTensorInducedTrivialF2Iso G U hU s).hom.hom.hom
        (((smoothTensorInductionFunctor ℤ G U hU s).map f).hom.hom z)) := by
  let : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  let : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  let : Fintype (U ⧸ V.subgroupOf U) := (V.subgroupOf U).fintypeQuotientOfFiniteIndex
  let : Fintype (G ⧸ V) := V.fintypeQuotientOfFiniteIndex
  let : Module ℤ (DiscreteRep.trivialF2 V).V := (DiscreteRep.trivialF2 V).module
  let : Module ℤ (trivialF2 U).V := (trivialF2 U).hV2
  let : Module ℤ (trivialF2 G).V := (trivialF2 G).hV2
  intro x z f
  have ht := smoothTensorInducedTransitivityIso_hom_apply_tprod hVU s t hU hV
    ⟨trivialF2 V, isSmoothDiscrete_trivialF2 V⟩ m
  refine (congrArg (fun w ↦ trivialF2Equiv G
    ((smoothTensorInducedTrivialF2Iso G V hV
      (Subgroup.compositeLeftTransversal hVU s t)).hom.hom.hom w)) ht).trans ?_
  refine (smoothTensorInducedTrivialF2Iso_hom_apply_piTensorProduct_tprod G V hV
    (Subgroup.compositeLeftTransversal hVU s t) _).trans ?_
  -- Compute the iterated route by mapping the inner normalization in each outer factor.
  have ho := smoothTensorInductionFunctor_map_hom_hom_apply ℤ G U hU s f z
  refine Eq.trans ?_ (congrArg (fun w ↦ trivialF2Equiv G
    ((smoothTensorInducedTrivialF2Iso G U hU s).hom.hom.hom w)) ho.symm)
  have hp := PiTensorProduct.map_tprod
    (fun _ : G ⧸ U ↦ f.hom.hom.toLinearMap) x
  refine Eq.trans ?_ (congrArg (fun w ↦ trivialF2Equiv G
    ((smoothTensorInducedTrivialF2Iso G U hU s).hom.hom.hom w)) hp.symm)
  refine Eq.trans ?_
    (smoothTensorInducedTrivialF2Iso_hom_apply_piTensorProduct_tprod G U hU s _).symm
  -- The direct product becomes an iterated product in the tower's coset coordinates.
  have hi (a : G ⧸ U) :
      trivialF2Equiv U (f.hom.hom (x a)) = ∏ b, trivialF2Equiv V (m a b) :=
    innerTrivialF2Iso_apply_tprod hVU t hV (m a)
  let e := Subgroup.quotientEquivProdOfLE' hVU (Subgroup.leftTransversalRep U s)
    (Subgroup.leftTransversalRep_mk U s)
  refine (Fintype.prod_equiv e _ (fun q ↦ trivialF2Equiv V (m q.1 q.2))
    (fun _ ↦ rfl)).trans ?_
  refine (Fintype.prod_prod_type _).trans ?_
  exact Finset.prod_congr rfl fun a _ ↦ (hi a).symm

/-- The canonical identification of tensor-induced trivial `𝔽₂` coefficients commutes with
transitivity: direct multiplication of the tensor factors agrees with multiplication in stages.
The inner restriction is identified with trivial coefficients by `smoothResFunctor_trivialF2`. -/
@[reassoc]
theorem smoothTensorInducedTrivialF2Iso_transitivity_hom :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (smoothTensorInducedTransitivityIso hVU s t hU hV
        ⟨trivialF2 V, isSmoothDiscrete_trivialF2 V⟩).hom ≫
        (smoothTensorInducedTrivialF2Iso G V hV
          (Subgroup.compositeLeftTransversal hVU s t)).hom =
      (smoothTensorInductionFunctor ℤ G U hU s).map
          ((smoothTensorInductionFunctor ℤ U (V.subgroupOf U) (U.subgroupOf_isOpen V hV) t).map
              (eqToHom (smoothResFunctor_trivialF2 V
                (Subgroup.subgroupOfEquivOfLe hVU : V.subgroupOf U →* V)
                (Subgroup.continuous_subgroupOfEquivOfLe hVU))) ≫
            (smoothTensorInducedTrivialF2Iso U (V.subgroupOf U)
              (U.subgroupOf_isOpen V hV) t).hom) ≫
        (smoothTensorInducedTrivialF2Iso G U hU s).hom := by
  let : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  let : Fintype (G ⧸ U) := U.fintypeQuotientOfFiniteIndex
  let : Fintype (U ⧸ V.subgroupOf U) := (V.subgroupOf U).fintypeQuotientOfFiniteIndex
  let : Fintype (G ⧸ V) := V.fintypeQuotientOfFiniteIndex
  let : Module ℤ (DiscreteRep.trivialF2 V).V := (DiscreteRep.trivialF2 V).module
  let : Module ℤ (trivialF2 U).V := (trivialF2 U).hV2
  let : Module ℤ (trivialF2 G).V := (trivialF2 G).hV2
  -- Finite tensor extensionality reduces the square to multiplying pure-tensor factors.
  apply ObjectProperty.hom_ext
  apply TopRep.hom_ext
  apply ContIntertwiningMap.toIntertwiningMap_injective
  apply Representation.IntertwiningMap.ext
  apply PiTensorProduct.ext_sigma_tprod (R := ℤ)
    (M := fun (_ : G ⧸ U) (_ : U ⧸ V.subgroupOf U) ↦ (DiscreteRep.trivialF2 V).V)
  intro m
  apply (trivialF2Equiv G).injective
  exact smoothTensorInducedTrivialF2Iso_transitivity_hom_apply_tprod hVU s t hU hV m

end TauCeti

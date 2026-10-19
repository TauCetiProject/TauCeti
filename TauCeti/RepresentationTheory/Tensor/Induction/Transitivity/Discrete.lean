/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Restriction
public import TauCeti.RepresentationTheory.Tensor.Induction.Smooth
public import TauCeti.RepresentationTheory.Tensor.Induction.Transitivity.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup

/-!
# Transitivity of discrete tensor induction

For a subgroup tower `V ≤ U ≤ G`, this file lifts the algebraic comparison
`Subgroup.tensorInducedTransitivity` to discrete continuous representations and to smooth discrete
representations. Iterated tensor induction from `V` to `U` to `G` is isomorphic to direct tensor
induction from `V` to `G` along the composite transversal, naturally in the coefficient
representation.

The inner tensor induction is along `V.subgroupOf U ≤ U`, so the coefficients are first restricted
along the canonical continuous isomorphism `Subgroup.subgroupOfEquivOfLe : V.subgroupOf U ≃* V`.
The lifts assume that both subgroup inclusions have finite index and that the subgroups are open,
exactly as required by the tensor-induction functors.

## Main definitions

* `TauCeti.DiscreteRep.tensorInducedTransitivityIso`: the comparison for discrete continuous
  representations.
* `TauCeti.smoothTensorInducedTransitivityIso`: the comparison for smooth discrete
  representations.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  *Transactions of the American Mathematical Society* 108 (1963), §§2–5.
-/

public section

open CategoryTheory

universe u v w

/-- The canonical isomorphism `V.subgroupOf U ≃* V` is continuous, read as the monoid
homomorphism along which discrete coefficients are restricted. This is the continuity part of
Mathlib's `Subgroup.subgroupOfContinuousMulEquivOfLe`, stated for the coercion that
`Subgroup.tensorInducedTransitivity` uses. -/
theorem Subgroup.continuous_subgroupOfEquivOfLe {G : Type v} [Group G] [TopologicalSpace G]
    {U V : Subgroup G} (hVU : V ≤ U) :
    Continuous (Subgroup.subgroupOfEquivOfLe hVU : V.subgroupOf U →* V) :=
  (Subgroup.subgroupOfContinuousMulEquivOfLe hVU).continuous

namespace TauCeti

namespace DiscreteRep

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U V : Subgroup G} (hVU : V ≤ U) (s : U.LeftTransversal)
  (t : (V.subgroupOf U).LeftTransversal) (hU : IsOpen (U : Set G)) (hV : IsOpen (V : Set G))
  [U.FiniteIndex] [(V.subgroupOf U).FiniteIndex]

/-- Iterated tensor induction of a discrete continuous representation is isomorphic to direct
tensor induction along the composite transversal. -/
noncomputable def tensorInducedTransitivityIso (A : DiscreteRep.{u, v, w} R V) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    tensorInduced U hU s
        (tensorInduced (V.subgroupOf U) (U.subgroupOf_isOpen V hV) t
          (res (Subgroup.subgroupOfEquivOfLe hVU : V.subgroupOf U →* V)
            (Subgroup.continuous_subgroupOfEquivOfLe hVU) A)) ≅
      tensorInduced V hV (Subgroup.compositeLeftTransversal hVU s t) A := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  exact
    { hom := (Subgroup.tensorInducedTransitivity hVU s t A.ρ).toIntertwiningMap
      inv := (Subgroup.tensorInducedTransitivity hVU s t A.ρ).symm.toIntertwiningMap
      hom_inv_id := Representation.IntertwiningMap.ext <| LinearMap.ext <|
        (Subgroup.tensorInducedTransitivity hVU s t A.ρ).symm_apply_apply
      inv_hom_id := Representation.IntertwiningMap.ext <| LinearMap.ext <|
        (Subgroup.tensorInducedTransitivity hVU s t A.ρ).apply_symm_apply }

/-- The forward map of discrete transitivity is the algebraic tensor-regrouping equivalence. -/
theorem tensorInducedTransitivityIso_hom_toLinearMap (A : DiscreteRep.{u, v, w} R V) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (tensorInducedTransitivityIso hVU s t hU hV A).hom.toLinearMap =
      (Subgroup.tensorInducedTransitivity hVU s t A.ρ).toLinearEquiv.toLinearMap := (rfl)

/-- The inverse map of discrete transitivity is the inverse algebraic regrouping equivalence. -/
theorem tensorInducedTransitivityIso_inv_toLinearMap (A : DiscreteRep.{u, v, w} R V) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (tensorInducedTransitivityIso hVU s t hU hV A).inv.toLinearMap =
      (Subgroup.tensorInducedTransitivity hVU s t A.ρ).symm.toLinearEquiv.toLinearMap := (rfl)

/-- On pure tensors, discrete transitivity flattens the two coset coordinates. -/
@[simp] theorem tensorInducedTransitivityIso_hom_apply_tprod
    (A : DiscreteRep.{u, v, w} R V)
    (m : (G ⧸ U) → (U ⧸ V.subgroupOf U) → A.V) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (tensorInducedTransitivityIso hVU s t hU hV A).hom.toLinearMap
        (PiTensorProduct.tprod R fun a ↦ PiTensorProduct.tprod R (m a)) =
      PiTensorProduct.tprod R (fun q : G ⧸ V ↦
        m (Subgroup.quotientEquivProdOfLE' hVU (Subgroup.leftTransversalRep U s)
          (Subgroup.leftTransversalRep_mk U s) q).1
          (Subgroup.quotientEquivProdOfLE' hVU (Subgroup.leftTransversalRep U s)
            (Subgroup.leftTransversalRep_mk U s) q).2) := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  exact Subgroup.tensorInducedTransitivity_tprod hVU s t A.ρ m

/-- On pure tensors, inverse discrete transitivity splits each coset into its two coordinates. -/
@[simp] theorem tensorInducedTransitivityIso_inv_apply_tprod
    (A : DiscreteRep.{u, v, w} R V) (m : G ⧸ V → A.V) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (tensorInducedTransitivityIso hVU s t hU hV A).inv.toLinearMap (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R (fun a ↦ PiTensorProduct.tprod R (fun b ↦
        m ((Subgroup.quotientEquivProdOfLE' hVU (Subgroup.leftTransversalRep U s)
          (Subgroup.leftTransversalRep_mk U s)).symm (a, b)))) := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  exact Subgroup.tensorInducedTransitivity_symm_tprod hVU s t A.ρ m

/-- The discrete tensor-induction transitivity comparison is natural in the coefficient
representation. -/
@[reassoc]
theorem tensorInducedTransitivityIso_hom_naturality
    {A B : DiscreteRep.{u, v, w} R V} (f : A ⟶ B) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (tensorInductionFunctor U hU s).map
          ((tensorInductionFunctor (V.subgroupOf U) (U.subgroupOf_isOpen V hV) t).map
            ((resFunctor (Subgroup.subgroupOfEquivOfLe hVU : V.subgroupOf U →* V)
              (Subgroup.continuous_subgroupOfEquivOfLe hVU)).map f)) ≫
        (tensorInducedTransitivityIso hVU s t hU hV B).hom =
      (tensorInducedTransitivityIso hVU s t hU hV A).hom ≫
        (tensorInductionFunctor V hV (Subgroup.compositeLeftTransversal hVU s t)).map f := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  apply Representation.IntertwiningMap.ext
  exact LinearMap.ext fun z ↦
    Subgroup.tensorInducedTransitivity_naturality hVU s t f z

end DiscreteRep

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U V : Subgroup G} (hVU : V ≤ U) (s : U.LeftTransversal)
  (t : (V.subgroupOf U).LeftTransversal) (hU : IsOpen (U : Set G)) (hV : IsOpen (V : Set G))
  [U.FiniteIndex] [(V.subgroupOf U).FiniteIndex]

/-- Iterated smooth tensor induction is isomorphic to direct smooth tensor induction along the
composite transversal.

The objects are written in the simp-normal form produced by `smoothTensorInductionFunctor_obj`
and `smoothResFunctor_obj`, so that the pure-tensor computation rules below can be simp
lemmas. -/
noncomputable def smoothTensorInducedTransitivityIso
    (A : SmoothDiscreteTopRep.{u, v, w} R V) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s
          ((ofSmoothDiscrete R U).obj
            ((toSmoothDiscrete R U).obj
              (DiscreteRep.tensorInduced (V.subgroupOf U) (U.subgroupOf_isOpen V hV) t
                ((ofSmoothDiscrete R (V.subgroupOf U)).obj
                  ((toSmoothDiscrete R (V.subgroupOf U)).obj
                    (DiscreteRep.res (Subgroup.subgroupOfEquivOfLe hVU : V.subgroupOf U →* V)
                      (Subgroup.continuous_subgroupOfEquivOfLe hVU)
                      ((ofSmoothDiscrete R V).obj A)))))))) ≅
      (toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced V hV (Subgroup.compositeLeftTransversal hVU s t)
          ((ofSmoothDiscrete R V).obj A)) := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  exact (toSmoothDiscrete R G).mapIso
    (DiscreteRep.tensorInducedTransitivityIso hVU s t hU hV
      ((ofSmoothDiscrete R V).obj A))

/-- On pure tensors, smooth transitivity flattens the two coset coordinates. -/
@[simp] theorem smoothTensorInducedTransitivityIso_hom_apply_tprod
    (A : SmoothDiscreteTopRep.{u, v, w} R V)
    (m : (G ⧸ U) → (U ⧸ V.subgroupOf U) → A.obj.V) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (smoothTensorInducedTransitivityIso hVU s t hU hV A).hom.hom.hom
        (PiTensorProduct.tprod R fun a ↦ PiTensorProduct.tprod R (m a)) =
      PiTensorProduct.tprod R (fun q : G ⧸ V ↦
        m (Subgroup.quotientEquivProdOfLE' hVU (Subgroup.leftTransversalRep U s)
          (Subgroup.leftTransversalRep_mk U s) q).1
          (Subgroup.quotientEquivProdOfLE' hVU (Subgroup.leftTransversalRep U s)
            (Subgroup.leftTransversalRep_mk U s) q).2) := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  -- The smooth comparison is `(toSmoothDiscrete R G).mapIso` of the discrete one, and
  -- `toSmoothDiscrete` keeps both underlying modules and maps (`toSmoothDiscrete_obj_obj`,
  -- `toSmoothDiscrete_map_hom_hom_apply`, `ofSmoothDiscrete_obj_V`, all `rfl`). So the smooth
  -- underlying map on `A.obj.V`-valued tensors is the discrete one, by definition.
  exact DiscreteRep.tensorInducedTransitivityIso_hom_apply_tprod hVU s t hU hV
    ((ofSmoothDiscrete R V).obj A) m

/-- On pure tensors, inverse smooth transitivity splits each coset into its two coordinates. -/
@[simp] theorem smoothTensorInducedTransitivityIso_inv_apply_tprod
    (A : SmoothDiscreteTopRep.{u, v, w} R V) (m : G ⧸ V → A.obj.V) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (smoothTensorInducedTransitivityIso hVU s t hU hV A).inv.hom.hom
        (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R (fun a ↦ PiTensorProduct.tprod R (fun b ↦
        m ((Subgroup.quotientEquivProdOfLE' hVU (Subgroup.leftTransversalRep U s)
          (Subgroup.leftTransversalRep_mk U s)).symm (a, b)))) := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  -- As for the forward map: the smooth inverse is `toSmoothDiscrete` applied to the discrete
  -- inverse, which keeps the underlying modules and map by definition.
  exact DiscreteRep.tensorInducedTransitivityIso_inv_apply_tprod hVU s t hU hV
    ((ofSmoothDiscrete R V).obj A) m

/-- The smooth tensor-induction transitivity comparison is natural in the coefficient
representation. -/
@[reassoc]
theorem smoothTensorInducedTransitivityIso_hom_naturality
    {A B : SmoothDiscreteTopRep.{u, v, w} R V} (f : A ⟶ B) :
    letI : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
    (smoothTensorInductionFunctor R G U hU s).map
          ((smoothTensorInductionFunctor R U (V.subgroupOf U)
            (U.subgroupOf_isOpen V hV) t).map
              ((smoothResFunctor R (Subgroup.subgroupOfEquivOfLe hVU : V.subgroupOf U →* V)
                (Subgroup.continuous_subgroupOfEquivOfLe hVU)).map f)) ≫
        (smoothTensorInducedTransitivityIso hVU s t hU hV B).hom =
      (smoothTensorInducedTransitivityIso hVU s t hU hV A).hom ≫
        (smoothTensorInductionFunctor R G V hV
          (Subgroup.compositeLeftTransversal hVU s t)).map f := by
  let _ : V.FiniteIndex := Subgroup.finiteIndex_of_finiteIndex_subgroupOf V U
  rw [smoothTensorInductionFunctor_map, smoothTensorInductionFunctor_map,
    smoothTensorInductionFunctor_map, smoothResFunctor_map]
  apply ObjectProperty.hom_ext
  apply TopRep.hom_ext
  apply ContIntertwiningMap.toIntertwiningMap_injective
  -- After the rewrites every functor is a discrete one sandwiched between `ofSmoothDiscrete` and
  -- `toSmoothDiscrete`, whose round trips on maps are the identity by definition
  -- (`discreteRepEquivSmoothTopRep` has identity unit and counit components). So the underlying
  -- intertwining maps are those of the discrete naturality square.
  exact DiscreteRep.tensorInducedTransitivityIso_hom_naturality hVU s t hU hV
    ((ofSmoothDiscrete R V).map f)

end TauCeti

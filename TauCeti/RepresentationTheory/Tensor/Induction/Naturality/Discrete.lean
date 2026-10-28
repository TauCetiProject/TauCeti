/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Index.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Restriction
public import TauCeti.RepresentationTheory.Tensor.Induction.Naturality.Basic
public import TauCeti.RepresentationTheory.Tensor.Induction.Smooth
public import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Naturality of discrete tensor induction in the group

Let `φ : G →* G'` be a continuous homomorphism carrying an open finite-index subgroup `U ≤ G`
into an open finite-index subgroup `U' ≤ G'`, with restriction `ψ : U →* U'`, and inducing an
equivalence `e : G ⧸ U ≃ G' ⧸ U'`. This file lifts the algebraic comparison
`Subgroup.tensorInducedMapEquiv` to discrete continuous representations and to smooth discrete
representations: for a discrete `U'`-module `A`,

```text
Ind⊗_U^G (Res_ψ A) ≅ Res_φ (Ind⊗_{U'}^{G'} A),
```

where the right-hand side induces along the image transversal `s.map φ e he`. On pure tensors
the comparison relabels the factors along `e`, and it is natural in `A`.

The main specialization is inflation. For a normal subgroup `N ≤ U`, tensor induction from
`U` to `G` of coefficients inflated from the image of `U` in `G ⧸ N` agrees with the inflation of
tensor induction in the quotient (`TauCeti.DiscreteRep.tensorInducedQuotientIso`,
`TauCeti.smoothTensorInducedQuotientIso`). This is the coefficient-level input for the
compatibility of Evens' norm with inflation.

## Main definitions

* `TauCeti.DiscreteRep.tensorInducedMapIso`: the comparison for discrete continuous
  representations.
* `TauCeti.DiscreteRep.tensorInducedQuotientIso`: its specialization to a quotient map.
* `TauCeti.smoothTensorInducedMapIso` and `TauCeti.smoothTensorInducedQuotientIso`: the same
  comparisons for smooth discrete representations.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  *Transactions of the American Mathematical Society* 108 (1963), §§2–3 and §6.
-/

public section

open CategoryTheory

universe u v w

namespace TauCeti

namespace DiscreteRep

section Map

-- `U'.FiniteIndex` follows from `U.FiniteIndex` through `e`. It is assumed as an instance so that
-- tensor induction from `U'` elaborates without a local instance in every statement.
variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G G' : Type v} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [Group G'] [TopologicalSpace G'] [SeparatelyContinuousMul G']
  {U : Subgroup G} {U' : Subgroup G'} (hU : IsOpen (U : Set G)) (hU' : IsOpen (U' : Set G'))
  [U.FiniteIndex] [U'.FiniteIndex]
  {φ : G →* G'} (hφ : Continuous φ) {ψ : U →* U'} (hψ : ∀ u, (ψ u : G') = φ u)
  {e : G ⧸ U ≃ G' ⧸ U'} (he : ∀ g : G, e g = (φ g : G' ⧸ U')) (s : U.LeftTransversal)

/-- Tensor induction of a discrete continuous representation restricted along `ψ` is the
restriction along `φ` of tensor induction along the image transversal. -/
noncomputable def tensorInducedMapIso (A : DiscreteRep.{u, v, w} R U') :
    tensorInduced U hU s (res ψ (hφ.subgroupHom hψ) A) ≅
      res φ hφ (tensorInduced U' hU' (s.map φ e he) A) where
  hom := (Subgroup.tensorInducedMapEquiv φ ψ hψ e he s A.ρ).toIntertwiningMap
  inv := (Subgroup.tensorInducedMapEquiv φ ψ hψ e he s A.ρ).symm.toIntertwiningMap
  hom_inv_id := Representation.IntertwiningMap.ext <| LinearMap.ext <|
    (Subgroup.tensorInducedMapEquiv φ ψ hψ e he s A.ρ).symm_apply_apply
  inv_hom_id := Representation.IntertwiningMap.ext <| LinearMap.ext <|
    (Subgroup.tensorInducedMapEquiv φ ψ hψ e he s A.ρ).apply_symm_apply

/-- The forward map of the discrete comparison is the algebraic reindexing equivalence. -/
theorem tensorInducedMapIso_hom_toLinearMap (A : DiscreteRep.{u, v, w} R U') :
    (tensorInducedMapIso hU hU' hφ hψ he s A).hom.toLinearMap =
      (Subgroup.tensorInducedMapEquiv φ ψ hψ e he s A.ρ).toLinearEquiv.toLinearMap := (rfl)

/-- The inverse map of the discrete comparison is the inverse algebraic reindexing
equivalence. -/
theorem tensorInducedMapIso_inv_toLinearMap (A : DiscreteRep.{u, v, w} R U') :
    (tensorInducedMapIso hU hU' hφ hψ he s A).inv.toLinearMap =
      (Subgroup.tensorInducedMapEquiv φ ψ hψ e he s A.ρ).symm.toLinearEquiv.toLinearMap :=
  (rfl)

/-- On pure tensors, the discrete comparison relabels the factors along `e`. -/
@[simp] theorem tensorInducedMapIso_hom_apply_tprod (A : DiscreteRep.{u, v, w} R U')
    (m : G ⧸ U → A.V) :
    (tensorInducedMapIso hU hU' hφ hψ he s A).hom.toLinearMap (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun y ↦ m (e.symm y) :=
  Subgroup.tensorInducedMapEquiv_apply_tprod φ ψ hψ e he s A.ρ m

/-- On pure tensors, the inverse discrete comparison relabels the factors along `e⁻¹`. -/
@[simp] theorem tensorInducedMapIso_inv_apply_tprod (A : DiscreteRep.{u, v, w} R U')
    (m : G' ⧸ U' → A.V) :
    (tensorInducedMapIso hU hU' hφ hψ he s A).inv.toLinearMap (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦ m (e x) :=
  Subgroup.tensorInducedMapEquiv_symm_apply_tprod φ ψ hψ e he s A.ρ m

/-- The discrete comparison is natural in the coefficient representation. -/
@[reassoc]
theorem tensorInducedMapIso_hom_naturality {A B : DiscreteRep.{u, v, w} R U'} (f : A ⟶ B) :
    (tensorInductionFunctor U hU s).map ((resFunctor ψ (hφ.subgroupHom hψ)).map f) ≫
        (tensorInducedMapIso hU hU' hφ hψ he s B).hom =
      (tensorInducedMapIso hU hU' hφ hψ he s A).hom ≫
        (resFunctor φ hφ).map ((tensorInductionFunctor U' hU' (s.map φ e he)).map f) := by
  apply Representation.IntertwiningMap.ext
  refine PiTensorProduct.ext (MultilinearMap.ext fun m : G ⧸ U → A.V ↦ ?_)
  -- The extensionality goal is wrapped in `MultilinearMap.compMultilinearMap` and in the
  -- categorical composition, so the pure-tensor lemmas cannot rewrite it. Unfold those wrappers
  -- to expose the algebraic maps on the pure tensor.
  change Subgroup.tensorInducedMapEquiv φ ψ hψ e he s B.ρ
      (((resFunctor ψ (hφ.subgroupHom hψ)).map f).tensorInduced s
        (PiTensorProduct.tprod R m)) =
    f.tensorInduced (s.map φ e he)
      (Subgroup.tensorInducedMapEquiv φ ψ hψ e he s A.ρ (PiTensorProduct.tprod R m))
  -- The restricted morphism lives on the restricted carrier, which is `A.V` only up to
  -- unfolding `res`, so its pure-tensor rule is applied through `congrArg` rather than `simp`.
  rw [congrArg (Subgroup.tensorInducedMapEquiv φ ψ hψ e he s B.ρ)
    (((resFunctor ψ (hφ.subgroupHom hψ)).map f).tensorInduced_apply_tprod s m)]
  simp only [Subgroup.tensorInducedMapEquiv_apply_tprod,
    Representation.IntertwiningMap.tensorInduced_apply_tprod]
  exact Subgroup.tensorInducedMapEquiv_apply_tprod φ ψ hψ e he s B.ρ _

end Map

section Quotient

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} (hU : IsOpen (U : Set G)) [U.FiniteIndex]
  {N : Subgroup G} [N.Normal] (hNU : N ≤ U) (s : U.LeftTransversal)

/-- **Discrete tensor induction commutes with inflation.** For a normal subgroup `N ≤ U`,
tensor induction from `U` to `G` of coefficients inflated from the image of `U` in `G ⧸ N` is
the inflation of tensor induction from that image to `G ⧸ N`. -/
noncomputable def tensorInducedQuotientIso
    (A : DiscreteRep.{u, v, w} R (U.map (QuotientGroup.mk' N))) :
    tensorInduced U hU s
        (res ((QuotientGroup.mk' N).subgroupMap U)
          (QuotientGroup.continuous_mk.subgroupHom (MonoidHom.subgroupMap_apply_coe _ U)) A) ≅
      res (QuotientGroup.mk' N) QuotientGroup.continuous_mk
        (tensorInduced (U.map (QuotientGroup.mk' N)) (QuotientGroup.isOpenMap_coe (N := N) U hU)
          (s.map (QuotientGroup.mk' N) (QuotientGroup.quotientEquivQuotientMapOfLE hNU)
            (QuotientGroup.quotientEquivQuotientMapOfLE_mk hNU)) A) :=
  tensorInducedMapIso hU (QuotientGroup.isOpenMap_coe (N := N) U hU) QuotientGroup.continuous_mk
    (MonoidHom.subgroupMap_apply_coe _ U) (QuotientGroup.quotientEquivQuotientMapOfLE_mk hNU) s A

/-- On pure tensors, the discrete inflation comparison relabels a coset of `U` by its image in
the quotient. -/
@[simp] theorem tensorInducedQuotientIso_hom_apply_tprod
    (A : DiscreteRep.{u, v, w} R (U.map (QuotientGroup.mk' N))) (m : G ⧸ U → A.V) :
    (tensorInducedQuotientIso hU hNU s A).hom.toLinearMap (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun y ↦
        m ((QuotientGroup.quotientEquivQuotientMapOfLE hNU).symm y) :=
  tensorInducedMapIso_hom_apply_tprod hU (QuotientGroup.isOpenMap_coe (N := N) U hU)
    QuotientGroup.continuous_mk (MonoidHom.subgroupMap_apply_coe _ U)
    (QuotientGroup.quotientEquivQuotientMapOfLE_mk hNU) s A m

/-- On pure tensors, the inverse discrete inflation comparison replaces a quotient coset by its
preimage coset in `G`. -/
@[simp] theorem tensorInducedQuotientIso_inv_apply_tprod
    (A : DiscreteRep.{u, v, w} R (U.map (QuotientGroup.mk' N)))
    (m : (G ⧸ N) ⧸ U.map (QuotientGroup.mk' N) → A.V) :
    (tensorInducedQuotientIso hU hNU s A).inv.toLinearMap (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦ m (QuotientGroup.quotientEquivQuotientMapOfLE hNU x) :=
  tensorInducedMapIso_inv_apply_tprod hU (QuotientGroup.isOpenMap_coe (N := N) U hU)
    QuotientGroup.continuous_mk (MonoidHom.subgroupMap_apply_coe _ U)
    (QuotientGroup.quotientEquivQuotientMapOfLE_mk hNU) s A m

/-- The discrete inflation comparison is natural in the coefficient representation. -/
@[reassoc]
theorem tensorInducedQuotientIso_hom_naturality
    {A B : DiscreteRep.{u, v, w} R (U.map (QuotientGroup.mk' N))} (f : A ⟶ B) :
    (tensorInductionFunctor U hU s).map
          ((resFunctor ((QuotientGroup.mk' N).subgroupMap U)
            (QuotientGroup.continuous_mk.subgroupHom (MonoidHom.subgroupMap_apply_coe _ U))).map
              f) ≫
        (tensorInducedQuotientIso hU hNU s B).hom =
      (tensorInducedQuotientIso hU hNU s A).hom ≫
        (resFunctor (QuotientGroup.mk' N) QuotientGroup.continuous_mk).map
          ((tensorInductionFunctor (U.map (QuotientGroup.mk' N))
            (QuotientGroup.isOpenMap_coe (N := N) U hU)
            (s.map (QuotientGroup.mk' N) (QuotientGroup.quotientEquivQuotientMapOfLE hNU)
              (QuotientGroup.quotientEquivQuotientMapOfLE_mk hNU))).map f) :=
  tensorInducedMapIso_hom_naturality hU (QuotientGroup.isOpenMap_coe (N := N) U hU)
    QuotientGroup.continuous_mk (MonoidHom.subgroupMap_apply_coe _ U)
    (QuotientGroup.quotientEquivQuotientMapOfLE_mk hNU) s f

end Quotient

end DiscreteRep

section Map

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G G' : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {U : Subgroup G} {U' : Subgroup G'} (hU : IsOpen (U : Set G)) (hU' : IsOpen (U' : Set G'))
  [U.FiniteIndex] [U'.FiniteIndex]
  {φ : G →* G'} (hφ : Continuous φ) {ψ : U →* U'} (hψ : ∀ u, (ψ u : G') = φ u)
  {e : G ⧸ U ≃ G' ⧸ U'} (he : ∀ g : G, e g = (φ g : G' ⧸ U')) (s : U.LeftTransversal)

/-- Smooth tensor induction of a representation restricted along `ψ` is the restriction along
`φ` of smooth tensor induction along the image transversal.

The objects are written in the simp-normal form produced by `smoothTensorInductionFunctor_obj`
and `smoothResFunctor_obj`, so that the pure-tensor computation rules below can be simp
lemmas. -/
noncomputable def smoothTensorInducedMapIso (A : SmoothDiscreteTopRep.{u, v, w} R U') :
    (toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s
          ((ofSmoothDiscrete R U).obj
            ((toSmoothDiscrete R U).obj
              (DiscreteRep.res ψ (hφ.subgroupHom hψ) ((ofSmoothDiscrete R U').obj A))))) ≅
      (toSmoothDiscrete R G).obj
        (DiscreteRep.res φ hφ
          ((ofSmoothDiscrete R G').obj
            ((toSmoothDiscrete R G').obj
              (DiscreteRep.tensorInduced U' hU' (s.map φ e he)
                ((ofSmoothDiscrete R U').obj A))))) :=
  (toSmoothDiscrete R G).mapIso
    (DiscreteRep.tensorInducedMapIso hU hU' hφ hψ he s ((ofSmoothDiscrete R U').obj A))

/-- On pure tensors, the smooth comparison relabels the factors along `e`. -/
@[simp] theorem smoothTensorInducedMapIso_hom_apply_tprod
    (A : SmoothDiscreteTopRep.{u, v, w} R U') (m : G ⧸ U → A.obj.V) :
    (smoothTensorInducedMapIso hU hU' hφ hψ he s A).hom.hom.hom (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun y ↦ m (e.symm y) :=
  -- `toSmoothDiscrete` keeps the underlying modules and maps, so the smooth underlying map is the
  -- discrete one by definition.
  DiscreteRep.tensorInducedMapIso_hom_apply_tprod hU hU' hφ hψ he s
    ((ofSmoothDiscrete R U').obj A) m

/-- On pure tensors, the inverse smooth comparison relabels the factors along `e⁻¹`. -/
@[simp] theorem smoothTensorInducedMapIso_inv_apply_tprod
    (A : SmoothDiscreteTopRep.{u, v, w} R U') (m : G' ⧸ U' → A.obj.V) :
    (smoothTensorInducedMapIso hU hU' hφ hψ he s A).inv.hom.hom (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦ m (e x) :=
  -- As for the forward map: `toSmoothDiscrete` keeps the underlying map by definition.
  DiscreteRep.tensorInducedMapIso_inv_apply_tprod hU hU' hφ hψ he s
    ((ofSmoothDiscrete R U').obj A) m

/-- The smooth comparison is natural in the coefficient representation. -/
@[reassoc]
theorem smoothTensorInducedMapIso_hom_naturality
    {A B : SmoothDiscreteTopRep.{u, v, w} R U'} (f : A ⟶ B) :
    (smoothTensorInductionFunctor R G U hU s).map
          ((smoothResFunctor R ψ (hφ.subgroupHom hψ)).map f) ≫
        (smoothTensorInducedMapIso hU hU' hφ hψ he s B).hom =
      (smoothTensorInducedMapIso hU hU' hφ hψ he s A).hom ≫
        (smoothResFunctor R φ hφ).map
          ((smoothTensorInductionFunctor R G' U' hU' (s.map φ e he)).map f) := by
  simp only [smoothTensorInductionFunctor_map, smoothResFunctor_map]
  apply ObjectProperty.hom_ext
  apply TopRep.hom_ext
  apply ContIntertwiningMap.toIntertwiningMap_injective
  -- After the rewrites every functor is a discrete one sandwiched between `ofSmoothDiscrete` and
  -- `toSmoothDiscrete`, whose round trips on maps are the identity by definition. So the
  -- underlying intertwining maps are those of the discrete naturality square.
  exact DiscreteRep.tensorInducedMapIso_hom_naturality hU hU' hφ hψ he s
    ((ofSmoothDiscrete R U').map f)

end Map

section Quotient

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} (hU : IsOpen (U : Set G)) [U.FiniteIndex]
  {N : Subgroup G} [N.Normal] (hNU : N ≤ U) (s : U.LeftTransversal)

/-- **Smooth tensor induction commutes with inflation.** For a normal subgroup `N ≤ U`, smooth
tensor induction from `U` to `G` of coefficients inflated from the image of `U` in `G ⧸ N` is
the inflation of smooth tensor induction from that image to `G ⧸ N`.

The objects are written in the simp-normal form produced by `smoothTensorInductionFunctor_obj`
and `smoothResFunctor_obj`. -/
noncomputable def smoothTensorInducedQuotientIso
    (A : SmoothDiscreteTopRep.{u, v, w} R (U.map (QuotientGroup.mk' N))) :
    (toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s
          ((ofSmoothDiscrete R U).obj
            ((toSmoothDiscrete R U).obj
              (DiscreteRep.res ((QuotientGroup.mk' N).subgroupMap U)
                (QuotientGroup.continuous_mk.subgroupHom (MonoidHom.subgroupMap_apply_coe _ U))
                ((ofSmoothDiscrete R (U.map (QuotientGroup.mk' N))).obj A))))) ≅
      (toSmoothDiscrete R G).obj
        (DiscreteRep.res (QuotientGroup.mk' N) QuotientGroup.continuous_mk
          ((ofSmoothDiscrete R (G ⧸ N)).obj
            ((toSmoothDiscrete R (G ⧸ N)).obj
              (DiscreteRep.tensorInduced (U.map (QuotientGroup.mk' N))
                (QuotientGroup.isOpenMap_coe (N := N) U hU)
                (s.map (QuotientGroup.mk' N) (QuotientGroup.quotientEquivQuotientMapOfLE hNU)
                  (QuotientGroup.quotientEquivQuotientMapOfLE_mk hNU))
                ((ofSmoothDiscrete R (U.map (QuotientGroup.mk' N))).obj A))))) :=
  (toSmoothDiscrete R G).mapIso
    (DiscreteRep.tensorInducedQuotientIso hU hNU s
      ((ofSmoothDiscrete R (U.map (QuotientGroup.mk' N))).obj A))

/-- On pure tensors, the smooth inflation comparison relabels a coset of `U` by its image in the
quotient. -/
@[simp] theorem smoothTensorInducedQuotientIso_hom_apply_tprod
    (A : SmoothDiscreteTopRep.{u, v, w} R (U.map (QuotientGroup.mk' N)))
    (m : G ⧸ U → A.obj.V) :
    (smoothTensorInducedQuotientIso hU hNU s A).hom.hom.hom (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun y ↦
        m ((QuotientGroup.quotientEquivQuotientMapOfLE hNU).symm y) :=
  -- `toSmoothDiscrete` keeps the underlying map by definition.
  DiscreteRep.tensorInducedQuotientIso_hom_apply_tprod hU hNU s
    ((ofSmoothDiscrete R (U.map (QuotientGroup.mk' N))).obj A) m

/-- On pure tensors, the inverse smooth inflation comparison replaces a quotient coset by its
preimage coset in `G`. -/
@[simp] theorem smoothTensorInducedQuotientIso_inv_apply_tprod
    (A : SmoothDiscreteTopRep.{u, v, w} R (U.map (QuotientGroup.mk' N)))
    (m : (G ⧸ N) ⧸ U.map (QuotientGroup.mk' N) → A.obj.V) :
    (smoothTensorInducedQuotientIso hU hNU s A).inv.hom.hom (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦ m (QuotientGroup.quotientEquivQuotientMapOfLE hNU x) :=
  -- `toSmoothDiscrete` keeps the underlying map by definition.
  DiscreteRep.tensorInducedQuotientIso_inv_apply_tprod hU hNU s
    ((ofSmoothDiscrete R (U.map (QuotientGroup.mk' N))).obj A) m

/-- The smooth inflation comparison is natural in the coefficient representation. -/
@[reassoc]
theorem smoothTensorInducedQuotientIso_hom_naturality
    {A B : SmoothDiscreteTopRep.{u, v, w} R (U.map (QuotientGroup.mk' N))} (f : A ⟶ B) :
    (smoothTensorInductionFunctor R G U hU s).map
          ((smoothResFunctor R ((QuotientGroup.mk' N).subgroupMap U)
            (QuotientGroup.continuous_mk.subgroupHom (MonoidHom.subgroupMap_apply_coe _ U))).map
              f) ≫
        (smoothTensorInducedQuotientIso hU hNU s B).hom =
      (smoothTensorInducedQuotientIso hU hNU s A).hom ≫
        (smoothResFunctor R (QuotientGroup.mk' N) QuotientGroup.continuous_mk).map
          ((smoothTensorInductionFunctor R (G ⧸ N) (U.map (QuotientGroup.mk' N))
            (QuotientGroup.isOpenMap_coe (N := N) U hU)
            (s.map (QuotientGroup.mk' N) (QuotientGroup.quotientEquivQuotientMapOfLE hNU)
              (QuotientGroup.quotientEquivQuotientMapOfLE_mk hNU))).map f) :=
  smoothTensorInducedMapIso_hom_naturality hU (QuotientGroup.isOpenMap_coe (N := N) U hU)
    QuotientGroup.continuous_mk (MonoidHom.subgroupMap_apply_coe _ U)
    (QuotientGroup.quotientEquivQuotientMapOfLE_mk hNU) s f

end Quotient

end TauCeti

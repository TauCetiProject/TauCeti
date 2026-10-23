/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Mackey.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Restriction
public import TauCeti.RepresentationTheory.Tensor.Induction.DoubleCoset.Basic
public import TauCeti.RepresentationTheory.Tensor.Induction.Smooth
public import TauCeti.RepresentationTheory.Tensor.Pi.Discrete
public import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# The Mackey formula for discrete tensor induction

Let `U` be an open subgroup of finite index of a topological group `G`, and let `V` be any
subgroup. This file lifts the Mackey formula for tensor induction,
`Subgroup.tensorInducedMackey`, to discrete continuous representations and to smooth discrete
representations: as discrete `V`-modules,

```text
Res_V (⨂Ind_U^G A)  ≅  ⨂_{VsU ∈ V\G/U} ⨂Ind_{V ∩ sUs⁻¹}^V (Res_{y ↦ s⁻¹ y s} A).
```

Each Mackey subgroup `V ⊓ sUs⁻¹` is open in `V` and of finite index there
(`Subgroup.isOpen_mackeySubgroup_subgroupOf`, `TauCeti.instIsFiniteRelIndexMackeySubgroup`), and
the conjugation `y ↦ s⁻¹ y s` into `U` is continuous (`Subgroup.continuous_mackeyToH`), so every
factor on the right is a discrete tensor induction of a discrete restriction, and the outer tensor
product is `TauCeti.DiscreteRep.piTensorProduct` over the finitely many double cosets. The
comparisons are natural in the coefficient representation.

The double-coset representatives `r` and the transversals `t D` of the Mackey subgroups are
data of the comparison, as in the algebraic statement; the transversal `s` of `U` is arbitrary.

## Main definitions

* `TauCeti.DiscreteRep.tensorInducedMackeyIso`: the Mackey comparison for discrete continuous
  representations.
* `TauCeti.smoothTensorInducedMackeyIso`: the Mackey comparison for smooth discrete
  representations.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  *Transactions of the American Mathematical Society* 108 (1963), §6.2.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace TauCeti

namespace DiscreteRep

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [ContinuousMul G]
  (U V : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
  (r : DoubleCoset.Quotient (V : Set G) (U : Set G) → G)
  (hr : ∀ D, DoubleCoset.mk V U (r D) = D)
  (t : ∀ D, ((mackeySubgroup (r D) U V).subgroupOf V).LeftTransversal)
  (s : U.LeftTransversal)

include hr in
/-- **The Mackey formula for discrete tensor induction.** Restricted to `V`, discrete tensor
induction from `U` to `G` is the tensor product, over the double cosets `V \ G / U`, of the
discrete tensor inductions from the Mackey subgroups `V ⊓ (r D) U (r D)⁻¹` to `V` of the
restrictions of `A` along `y ↦ (r D)⁻¹ y (r D)`. -/
noncomputable def tensorInducedMackeyIso (A : DiscreteRep.{u, v, w} R U) :
    piTensorProduct (fun D ↦
        tensorInduced _ (U.isOpen_mackeySubgroup_subgroupOf V hU (r D)) (t D)
          (res (mackeyToH (r D) U V) (U.continuous_mackeyToH V (r D)) A)) ≅
      res V.subtype continuous_subtype_val (tensorInduced U hU s A) where
  hom := (Subgroup.tensorInducedMackey U V r hr t A.ρ s).toIntertwiningMap
  inv := (Subgroup.tensorInducedMackey U V r hr t A.ρ s).symm.toIntertwiningMap
  hom_inv_id := Representation.IntertwiningMap.ext <| LinearMap.ext <|
    (Subgroup.tensorInducedMackey U V r hr t A.ρ s).symm_apply_apply
  inv_hom_id := Representation.IntertwiningMap.ext <| LinearMap.ext <|
    (Subgroup.tensorInducedMackey U V r hr t A.ρ s).apply_symm_apply

/-- The forward map of the discrete Mackey comparison is the algebraic Mackey comparison. -/
theorem tensorInducedMackeyIso_hom_toLinearMap (A : DiscreteRep.{u, v, w} R U) :
    (tensorInducedMackeyIso U V hU r hr t s A).hom.toLinearMap =
      (Subgroup.tensorInducedMackey U V r hr t A.ρ s).toLinearEquiv.toLinearMap := (rfl)

/-- The inverse map of the discrete Mackey comparison is the inverse algebraic Mackey
comparison. -/
theorem tensorInducedMackeyIso_inv_toLinearMap (A : DiscreteRep.{u, v, w} R U) :
    (tensorInducedMackeyIso U V hU r hr t s A).inv.toLinearMap =
      (Subgroup.tensorInducedMackey U V r hr t A.ρ s).symm.toLinearEquiv.toLinearMap := (rfl)

/-- On orbitwise pure tensors, the discrete Mackey comparison reads the Mackey coordinates of each
coset and corrects the factor by the difference between `s` and the Mackey-adapted transversal. -/
@[simp] theorem tensorInducedMackeyIso_hom_apply_tprod (A : DiscreteRep.{u, v, w} R U)
    (m : ∀ D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      V ⧸ (mackeySubgroup (r D) U V).subgroupOf V → A.V) :
    (tensorInducedMackeyIso U V hU r hr t s A).hom.toLinearMap
        (PiTensorProduct.tprod R fun D ↦ PiTensorProduct.tprod R (m D)) =
      PiTensorProduct.tprod R fun q : G ⧸ U ↦
        A.ρ ((U.monomialChangeTransversal s (U.mackeyLeftTransversal V r hr t)).left q)
          (m ((mackeyQuotientEquiv U V r hr).symm q).1 ((mackeyQuotientEquiv U V r hr).symm q).2) :=
  Subgroup.tensorInducedMackey_tprod U V r hr t A.ρ s m

/-- The discrete Mackey comparison is natural in the coefficient representation. -/
@[reassoc]
theorem tensorInducedMackeyIso_hom_naturality {A B : DiscreteRep.{u, v, w} R U} (f : A ⟶ B) :
    (piTensorProductFunctor R V _).map (fun D ↦
        (tensorInductionFunctor _ (U.isOpen_mackeySubgroup_subgroupOf V hU (r D)) (t D)).map
          ((resFunctor (mackeyToH (r D) U V) (U.continuous_mackeyToH V (r D))).map f)) ≫
        (tensorInducedMackeyIso U V hU r hr t s B).hom =
      (tensorInducedMackeyIso U V hU r hr t s A).hom ≫
        (resFunctor V.subtype continuous_subtype_val).map
          ((tensorInductionFunctor U hU s).map f) := by
  have e : ((piTensorProductFunctor R V _).map fun D ↦
      (tensorInductionFunctor _ (U.isOpen_mackeySubgroup_subgroupOf V hU (r D)) (t D)).map
        ((resFunctor (mackeyToH (r D) U V) (U.continuous_mackeyToH V (r D))).map f)).toLinearMap =
      PiTensorProduct.map fun _ ↦ PiTensorProduct.map fun _ ↦ f.toLinearMap :=
    (piTensorProductFunctor_map_toLinearMap _).trans (by
      simp only [tensorInductionFunctor_map,
        Representation.IntertwiningMap.tensorInduced_toLinearMap, resFunctor_map_toLinearMap]
      -- The two sides now differ only in how the factor modules are written: as the carriers of
      -- the tensor-induced restricted objects, or as `⨂[R] _, A.V`. These agree by definition
      -- (`tensorInduced_V`, `res_V`), which `simp` cannot rewrite inside the types.
      rfl)
  refine Representation.IntertwiningMap.ext <| LinearMap.ext fun z ↦ ?_
  -- Both composites unfold to the algebraic Mackey comparisons and factorwise maps; `e` rewrites
  -- the factorwise maps of the source into the form of the algebraic naturality theorem.
  exact (congrArg (fun z' ↦ Subgroup.tensorInducedMackey U V r hr t B.ρ s z')
    (LinearMap.congr_fun e z)).trans (Subgroup.tensorInducedMackey_naturality U V r hr t A.ρ f s z)

end DiscreteRep

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U V : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
  (r : DoubleCoset.Quotient (V : Set G) (U : Set G) → G)
  (hr : ∀ D, DoubleCoset.mk V U (r D) = D)
  (t : ∀ D, ((mackeySubgroup (r D) U V).subgroupOf V).LeftTransversal)
  (s : U.LeftTransversal)

include hr in
/-- **The Mackey formula for smooth tensor induction.** Restricted to `V`, smooth tensor induction
from `U` to `G` is the tensor product, over the double cosets `V \ G / U`, of the smooth tensor
inductions from the Mackey subgroups `V ⊓ (r D) U (r D)⁻¹` to `V` of the restrictions of `A`
along `y ↦ (r D)⁻¹ y (r D)`. The tensor product is taken in discrete representations.

The objects are written in the simp-normal form produced by `smoothTensorInductionFunctor_obj`
and `smoothResFunctor_obj`, so that the pure-tensor computation rule below can be a simp
lemma. -/
noncomputable def smoothTensorInducedMackeyIso (A : SmoothDiscreteTopRep.{u, v, w} R U) :
    (toSmoothDiscrete R V).obj (DiscreteRep.piTensorProduct fun D ↦
        (ofSmoothDiscrete R V).obj
          ((toSmoothDiscrete R V).obj
            (DiscreteRep.tensorInduced _ (U.isOpen_mackeySubgroup_subgroupOf V hU (r D)) (t D)
              ((ofSmoothDiscrete R _).obj
                ((toSmoothDiscrete R _).obj
                  (DiscreteRep.res (mackeyToH (r D) U V) (U.continuous_mackeyToH V (r D))
                    ((ofSmoothDiscrete R U).obj A))))))) ≅
      (toSmoothDiscrete R V).obj
        (DiscreteRep.res V.subtype continuous_subtype_val
          ((ofSmoothDiscrete R G).obj
            ((toSmoothDiscrete R G).obj
              (DiscreteRep.tensorInduced U hU s ((ofSmoothDiscrete R U).obj A))))) :=
  (toSmoothDiscrete R V).mapIso
    (DiscreteRep.tensorInducedMackeyIso U V hU r hr t s ((ofSmoothDiscrete R U).obj A))

/-- On orbitwise pure tensors, the smooth Mackey comparison reads the Mackey coordinates of each
coset and corrects the factor by the difference between `s` and the Mackey-adapted transversal. -/
@[simp] theorem smoothTensorInducedMackeyIso_hom_apply_tprod
    (A : SmoothDiscreteTopRep.{u, v, w} R U)
    (m : ∀ D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      V ⧸ (mackeySubgroup (r D) U V).subgroupOf V → A.obj.V) :
    (smoothTensorInducedMackeyIso U V hU r hr t s A).hom.hom.hom
        (PiTensorProduct.tprod R fun D ↦ PiTensorProduct.tprod R (m D)) =
      PiTensorProduct.tprod R fun q : G ⧸ U ↦
        A.obj.ρ ((U.monomialChangeTransversal s (U.mackeyLeftTransversal V r hr t)).left q)
          (m ((mackeyQuotientEquiv U V r hr).symm q).1 ((mackeyQuotientEquiv U V r hr).symm q).2) :=
  -- The smooth comparison is `toSmoothDiscrete` applied to the discrete one, which keeps the
  -- underlying modules and maps by definition.
  DiscreteRep.tensorInducedMackeyIso_hom_apply_tprod U V hU r hr t s
    ((ofSmoothDiscrete R U).obj A) m

/-- The smooth Mackey comparison is natural in the coefficient representation. -/
@[reassoc]
theorem smoothTensorInducedMackeyIso_hom_naturality
    {A B : SmoothDiscreteTopRep.{u, v, w} R U} (f : A ⟶ B) :
    (toSmoothDiscrete R V).map ((DiscreteRep.piTensorProductFunctor R V _).map fun D ↦
        (ofSmoothDiscrete R V).map
          ((smoothTensorInductionFunctor R V _ (U.isOpen_mackeySubgroup_subgroupOf V hU (r D))
            (t D)).map
              ((smoothResFunctor R (mackeyToH (r D) U V)
                (U.continuous_mackeyToH V (r D))).map f))) ≫
        (smoothTensorInducedMackeyIso U V hU r hr t s B).hom =
      (smoothTensorInducedMackeyIso U V hU r hr t s A).hom ≫
        (smoothResFunctor R V.subtype continuous_subtype_val).map
          ((smoothTensorInductionFunctor R G U hU s).map f) := by
  simp only [smoothTensorInductionFunctor_map, smoothResFunctor_map]
  apply ObjectProperty.hom_ext
  apply TopRep.hom_ext
  apply ContIntertwiningMap.toIntertwiningMap_injective
  -- After the rewrites every functor is a discrete one sandwiched between `ofSmoothDiscrete` and
  -- `toSmoothDiscrete`, whose round trips on maps are the identity by definition. So the
  -- underlying intertwining maps are those of the discrete naturality square.
  exact DiscreteRep.tensorInducedMackeyIso_hom_naturality U V hU r hr t s
    ((ofSmoothDiscrete R U).map f)

end TauCeti

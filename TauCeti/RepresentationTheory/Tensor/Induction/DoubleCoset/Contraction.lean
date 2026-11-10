/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.DoubleCoset.Complex
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Transport
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.ChangeOfGroup

/-!
# Contracting the Mackey-decomposed tensor resolution

The orbitwise tensor complex in the Mackey decomposition is a resolution of the restriction
of the tensor-induced coefficients. Restrict the contraction of the ambient tensor resolution
and pull it back along the Mackey chain isomorphism. Its augmentation is the orbitwise tensor
augmentation followed by the coefficient Mackey comparison.

Consequently an invariant cocycle in the orbitwise complex has a canonical continuous
cohomology class. The Mackey comparison preserves that class, and restriction of a class
computed in the ambient tensor resolution can be computed in the orbitwise complex. This is
the additive comparison needed before identifying the orbitwise class with a cup product.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), §6, Proposition 2.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U V : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex] [CompactSpace U]
  (r : DoubleCoset.Quotient (V : Set G) (U : Set G) → G)
  (hr : ∀ D, DoubleCoset.mk V U (r D) = D)
  (t : ∀ D, ((mackeySubgroup (r D) U V).subgroupOf V).LeftTransversal)
  (s : U.LeftTransversal) (A : SmoothDiscreteTopRep.{u, v, max v w} R U)
  [Fintype (DoubleCoset.Quotient (V : Set G) (U : Set G))]
  [∀ D, Fintype (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)] [Fintype (G ⧸ U)]
  [LinearOrder (G ⧸ U)]
  (hA : ∀ a : A.obj.V, a + a = 0)

omit [LinearOrder (G ⧸ U)] in
/-- The Mackey chain comparison with the categorical restriction of the ambient complex.
This includes the identity comparison between restricting homogeneous terms and taking the
homogeneous terms of the restricted representation. -/
noncomputable def smoothTensorInducedMackeyRestrictedResolutionIso :
    let J := ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.gradedCochainComplex
      (smoothTensorInducedGradedResolutionPiece U hU s A)
      (smoothTensorInducedGradedResolutionPiece_ρ_mem U hU s A)
      (smoothTensorInducedGradedResolutionDifferential U hU s A).hom
      (isHomogeneous_smoothTensorInducedGradedResolutionDifferential U hU s A)
      (smoothTensorInducedGradedResolutionDifferential_sq U hU s A hA)
    smoothTensorInducedMackeyResolution U V hU r hr t s A hA ≅
      ((TopRep.resFunctor V.subtype).mapHomologicalComplex _).obj J :=
  (smoothTensorInducedMackeyResolutionIso U V hU r hr t s A hA).trans
    (TopRep.resGradedCochainComplexIso V.subtype).symm

-- The two application lemmas are not simp lemmas: simplifying their indexed terms changes
-- the source or target through Functor.mapHomologicalComplex_obj_X.
omit [LinearOrder (G ⧸ U)] in
/-- The restricted chain comparison applies the original Mackey regrouping in each degree. -/
theorem smoothTensorInducedMackeyRestrictedResolutionIso_hom_f_apply (n : ℕ)
    (z : ((smoothTensorInducedMackeyResolution U V hU r hr t s A hA).X n).V) :
    (((smoothTensorInducedMackeyRestrictedResolutionIso U V hU r hr t s A hA).hom.f n).hom z).1 =
      (smoothTensorInducedMackeyIso U V hU r hr t s
        (smoothGradedResolutionFunctor.obj A)).hom.hom.hom z.1 := by
  unfold smoothTensorInducedMackeyRestrictedResolutionIso
  -- The restriction functor and the smooth dictionary have identical underlying carriers.
  erw [Iso.trans_hom, HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
    Iso.symm_hom, TopRep.resGradedCochainComplexIso_inv_f_apply,
    smoothTensorInducedMackeyResolutionIso_hom_f_apply]

omit [LinearOrder (G ⧸ U)] in
/-- The inverse restricted chain comparison applies the inverse Mackey regrouping. -/
theorem smoothTensorInducedMackeyRestrictedResolutionIso_inv_f_apply (n : ℕ) (z) :
    (((smoothTensorInducedMackeyRestrictedResolutionIso U V hU r hr t s A hA).inv.f n).hom z).1 =
      (smoothTensorInducedMackeyIso U V hU r hr t s
        (smoothGradedResolutionFunctor.obj A)).inv.hom.hom z.1 := by
  unfold smoothTensorInducedMackeyRestrictedResolutionIso
  -- The restriction functor and the smooth dictionary have identical underlying carriers.
  erw [Iso.trans_inv, HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
    smoothTensorInducedMackeyResolutionIso_inv_f_apply,
    Iso.symm_inv, TopRep.resGradedCochainComplexIso_hom_f_apply]

/-- The Mackey-decomposed tensor complex contracts onto the restriction to `V` of the
coefficients tensor induced from `U` to `G`. No compactness or openness of `V` is needed. -/
noncomputable def smoothTensorInducedMackeyResolutionContraction :
    TopRep.ResolutionContraction.{u, v, max u w}
      (TopRep.res V.subtype ((toSmoothDiscrete R G).obj
        (DiscreteRep.tensorInduced U hU s ((ofSmoothDiscrete R U).obj A))).obj)
      (smoothTensorInducedMackeyResolution U V hU r hr t s A hA) :=
  TopRep.ResolutionContraction.ofIso.{u, v, max u w}
    (TopRep.ResolutionContraction.res.{u, v, max u w}
      (ContinuousMonoidHom.subgroupSubtype V)
      (smoothTensorInducedGradedResolutionContraction U hU s A hA))
    (smoothTensorInducedMackeyRestrictedResolutionIso U V hU r hr t s A hA)

-- Keep this structural equation out of simp so the computed augmentation formula below can fire.
/-- The augmentation of the orbitwise contraction is the restricted ambient augmentation
followed by the inverse Mackey chain comparison. -/
theorem smoothTensorInducedMackeyResolutionContraction_ι :
    (smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA).ι =
      (TopRep.resFunctor V.subtype).map
        (smoothTensorInducedGradedResolutionContraction U hU s A hA).ι ≫
          (smoothTensorInducedMackeyRestrictedResolutionIso U V hU r hr t s A hA).inv.f 0 := by
  unfold smoothTensorInducedMackeyResolutionContraction
  exact (TopRep.ResolutionContraction.ofIso_ι
    (TopRep.ResolutionContraction.res.{u, v, max u w}
      (ContinuousMonoidHom.subgroupSubtype V)
      (smoothTensorInducedGradedResolutionContraction U hU s A hA))
    (smoothTensorInducedMackeyRestrictedResolutionIso U V hU r hr t s A hA)).trans
      (congrArg
        (· ≫ (smoothTensorInducedMackeyRestrictedResolutionIso U V hU r hr t s A hA).inv.f 0)
        (TopRep.ResolutionContraction.res_ι _ _))

/-- Applying the Mackey chain comparison to the orbitwise augmentation recovers the
restricted ambient augmentation. -/
@[reassoc]
theorem smoothTensorInducedMackeyResolutionContraction_ι_comp_hom :
    (smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA).ι ≫
        (smoothTensorInducedMackeyRestrictedResolutionIso U V hU r hr t s A hA).hom.f 0 =
      (TopRep.resFunctor V.subtype).map
        (smoothTensorInducedGradedResolutionContraction U hU s A hA).ι := by
  rw [smoothTensorInducedMackeyResolutionContraction_ι, Category.assoc,
    ← HomologicalComplex.comp_f, Iso.inv_hom_id]
  simp

/-- On orbitwise coefficient tensors the augmentation applies the original augmentation in
every factor. The coefficient Mackey comparison identifies its input with the restricted
tensor-induced coefficients. -/
@[simp] theorem smoothTensorInducedMackeyResolutionContraction_ι_apply
    (x : ⨂[R] D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      ⨂[R] _ : V ⧸ (mackeySubgroup (r D) U V).subgroupOf V, A.obj.V) :
    ((smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA).ι.hom
        ((smoothTensorInducedMackeyIso U V hU r hr t s A).hom.hom.hom x)).1 =
      PiTensorProduct.map (fun _ ↦ PiTensorProduct.map
        (fun _ ↦ A.obj.gradedResolutionAugmentation)) x := by
  let e := (smoothDiscreteι R V).mapIso
    (smoothTensorInducedMackeyIso U V hU r hr t s (smoothGradedResolutionFunctor.obj A))
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  have hc := congrArg Subtype.val (ConcreteCategory.congr_hom
    (smoothTensorInducedMackeyResolutionContraction_ι_comp_hom U V hU r hr t s A hA)
    ((smoothTensorInducedMackeyIso U V hU r hr t s A).hom.hom.hom x))
  -- The homogeneous subtype and its restriction carry the same vectors.
  erw [ConcreteCategory.comp_apply,
    smoothTensorInducedMackeyRestrictedResolutionIso_hom_f_apply] at hc
  have hres := congrArg
    (fun f ↦ (f ((smoothTensorInducedMackeyIso U V hU r hr t s A).hom.hom.hom x)).1)
    (TopRep.resFunctor_map_hom V.subtype
      (smoothTensorInducedGradedResolutionContraction U hU s A hA).ι)
  have haug := smoothTensorInducedGradedResolutionContraction_ι_apply U hU s A hA
    ((smoothTensorInducedMackeyIso U V hU r hr t s A).hom.hom.hom x)
  exact (hc.trans (hres.trans haug)).trans
    (smoothTensorInducedMackeyIso_resolutionAugmentation U V hU r hr t s A x).symm

/-- The retraction of the orbitwise resolution first regroups into the ambient resolution
and then applies its tensor projection. -/
@[simp] theorem smoothTensorInducedMackeyResolutionContraction_proj_apply
    (z : ((smoothTensorInducedMackeyResolution U V hU r hr t s A hA).X 0).V) :
    (smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA).proj z =
      (smoothTensorInducedGradedResolutionContraction U hU s A hA).proj
        (((smoothTensorInducedMackeyRestrictedResolutionIso U V hU r hr t s A hA).hom.f 0).hom
          z) := by
  unfold smoothTensorInducedMackeyResolutionContraction
  exact (TopRep.ResolutionContraction.ofIso_proj_apply _ _ z).trans
    (congrArg (fun f ↦ f
      (((smoothTensorInducedMackeyRestrictedResolutionIso U V hU r hr t s A hA).hom.f 0).hom z))
      (TopRep.ResolutionContraction.res_proj.{u, v, max u w}
        (ContinuousMonoidHom.subgroupSubtype V)
        (smoothTensorInducedGradedResolutionContraction U hU s A hA)))

/-- The orbitwise homotopy is the conjugate of the ambient tensor homotopy by the Mackey
comparison. -/
@[simp] theorem smoothTensorInducedMackeyResolutionContraction_hom_apply (n : ℕ)
    (z : ((smoothTensorInducedMackeyResolution U V hU r hr t s A hA).X (n + 1)).V) :
    (smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA).hom n z =
      ((smoothTensorInducedMackeyRestrictedResolutionIso U V hU r hr t s A hA).inv.f n).hom
        ((smoothTensorInducedGradedResolutionContraction U hU s A hA).hom n
          (((smoothTensorInducedMackeyRestrictedResolutionIso U V hU r hr t s A hA).hom.f
            (n + 1)).hom z)) := by
  unfold smoothTensorInducedMackeyResolutionContraction
  exact (TopRep.ResolutionContraction.ofIso_hom_apply _ _ n z).trans
    (congrArg (fun f ↦
      ((smoothTensorInducedMackeyRestrictedResolutionIso U V hU r hr t s A hA).inv.f n).hom
        (f (((smoothTensorInducedMackeyRestrictedResolutionIso U V hU r hr t s A hA).hom.f
          (n + 1)).hom z))) (TopRep.ResolutionContraction.res_hom.{u, v, max u w}
            (ContinuousMonoidHom.subgroupSubtype V)
            (smoothTensorInducedGradedResolutionContraction U hU s A hA) n))

/-- Restriction of a class computed on the ambient tensor resolution is computed on the
orbitwise tensor resolution by the inverse Mackey comparison. This holds in every degree
and for any number of double cosets. -/
theorem res_cohomologyClass_smoothTensorInducedMackeyResolution [LocallyCompactSpace V]
    {n : ℕ}
    (z : ((((smoothTensorInducedGradedResolutionFunctor U hU s).obj A).obj.gradedCochainComplex
      (smoothTensorInducedGradedResolutionPiece U hU s A)
      (smoothTensorInducedGradedResolutionPiece_ρ_mem U hU s A)
      (smoothTensorInducedGradedResolutionDifferential U hU s A).hom
      (isHomogeneous_smoothTensorInducedGradedResolutionDifferential U hU s A)
      (smoothTensorInducedGradedResolutionDifferential_sq U hU s A hA)).X n).ρ.invariants)
    (hz) :
    ContinuousCohomology.res V _ n
        ((smoothTensorInducedGradedResolutionContraction U hU s A hA).cohomologyClass z hz) =
      (smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA).cohomologyClass
        (((smoothTensorInducedMackeyRestrictedResolutionIso U V hU r hr t s A hA).inv.f n).hom
          |>.mapInvariants
            (Submodule.inclusion (ContRepresentation.invariants_le_invariants_restrict _
              V.subtype) z))
        (TopRep.d_mapInvariants_f_apply
          (smoothTensorInducedMackeyRestrictedResolutionIso U V hU r hr t s A hA).inv
          (Submodule.inclusion (ContRepresentation.invariants_le_invariants_restrict _
            V.subtype) z) hz) := by
  rw [TopRep.ResolutionContraction.res_cohomologyClass]
  symm
  exact TopRep.ResolutionContraction.cohomologyClass_map.{u, v, max u w}
    (TopRep.ResolutionContraction.res.{u, v, max u w}
      (ContinuousMonoidHom.subgroupSubtype V)
      (smoothTensorInducedGradedResolutionContraction U hU s A hA))
    (smoothTensorInducedMackeyResolutionContraction U V hU r hr t s A hA)
    (smoothTensorInducedMackeyRestrictedResolutionIso U V hU r hr t s A hA).inv
    (by
      rw [TopRep.ResolutionContraction.res_ι]
      exact (smoothTensorInducedMackeyResolutionContraction_ι U V hU r hr t s A hA).symm) _ _

end TauCeti

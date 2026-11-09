/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Norm.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeCast
public import TauCeti.RepresentationTheory.Tensor.Induction.Transitivity.Discrete
import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.ChangeOfGroup
import TauCeti.RepresentationTheory.Tensor.Induction.Naturality.Resolution
import TauCeti.RepresentationTheory.Tensor.Induction.Transitivity.Resolution
import TauCeti.RepresentationTheory.Tensor.Induction.Transitivity.TrivialF2

/-!
# Transitivity of the Evens norm

Let `V ≤ U` be compact open subgroups of finite index in a topological group `G`. The Evens norm
is transitive: for `x ∈ Hⁿ(V, 𝔽₂)`,
```
N_V^G x = N_U^G (N_V^U x)      in H^{[G : V] n}(G, 𝔽₂),
```
where `V` is regarded as the open subgroup `V.subgroupOf U` of `U`, the class `x` is carried
there along `V.subgroupOf U ≃ V`, and the degree `[G : U] ([U : V] n)` is transported to
`[G : V] n` (`OpenSubgroup.evensNorm_trans`).

The norm of the class of a cocycle `z` is the class of its diagonal tensor in the tensor-induced
resolution, with the tensor-induced coefficients identified with `𝔽₂` by multiplication. At the
level of cocycles, transitivity is `TauCeti.coeffMap_smoothTensorInducedDiagonalClass_transitivity`:
along `Ind⊗_U^G Ind⊗_V^U 𝔽₂ ≅ Ind⊗_V^G 𝔽₂`, the norm from `V` to `G` is the norm from `U` to `G` of
a cocycle `y` representing the norm from `V` to `U`, but with coefficients in the intermediate
tensor induction `Ind⊗_V^U 𝔽₂` rather than in `𝔽₂`. The identifications of the tensor-induced
coefficients with `𝔽₂` are compatible with transitivity
(`TauCeti.smoothTensorInducedTrivialF2Iso_transitivity_hom`), and the norm of a cocycle is natural
in the coefficients (`Subgroup.coeffMap_smoothTensorInducedDiagonalClass`). So the identification
`Ind⊗_V^U 𝔽₂ ≅ 𝔽₂` can be applied to `y` before taking the norm from `U` to `G`, and the class of
the result is the norm from `V` to `U`.

## Main results

* `OpenSubgroup.evensNorm_trans`: transitivity of the Evens norm, `N_V^G = N_U^G ∘ N_V^U`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), §6, Proposition 1.
-/

public section

namespace OpenSubgroup

open TauCeti CategoryTheory

universe u

-- Instance search would pick `AddCommGroup.toIntModule`, which is not the module structure that
-- tensor induction is formed with.
attribute [local instance 1100] DiscreteRep.module

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {U V : OpenSubgroup G}

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A morphism `res φ 𝔽₂ ⟶ 𝔽₂` that preserves the underlying values is the canonical
identification `res_trivialF2_hom`, pointwise. -/
private theorem hom_apply_eq_eqToHom_hom_apply {H : Type u} [Group H]
    (φ : H →* G) (f : TopRep.res φ (trivialF2 G) ⟶ trivialF2 H)
    (hf : ∀ x, trivialF2Equiv H (f.hom x) = trivialF2Equiv G x) (x : (trivialF2 G).V) :
    f.hom x = (eqToHom (res_trivialF2_hom φ)).hom x := by
  apply (trivialF2Equiv H).injective
  rw [hf, TopRep.eqToHom_hom_apply, trivialF2Equiv_cast]

section Normalization

variable (hVU : V.toSubgroup ≤ U.toSubgroup)
  (t : (V.toSubgroup.subgroupOf U.toSubgroup).LeftTransversal)
  [U.toSubgroup.FiniteIndex] [(V.toSubgroup.subgroupOf U.toSubgroup).FiniteIndex]

/-- The identification of the intermediate tensor-induced coefficients `Ind⊗_V^U 𝔽₂` with `𝔽₂`:
identify the restriction of `𝔽₂` to `V.subgroupOf U` with `𝔽₂` and multiply the tensor factors. -/
private noncomputable def normHom :
    smoothTensorInducedSubgroupOf hVU t V.isOpen'
        ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩ ⟶
      ⟨trivialF2 U.toSubgroup, isSmoothDiscrete_trivialF2 U.toSubgroup⟩ :=
  (smoothTensorInductionFunctor ℤ U.toSubgroup (V.toSubgroup.subgroupOf U.toSubgroup)
      (U.toSubgroup.subgroupOf_isOpen V.toSubgroup V.isOpen') t).map
      (eqToHom (smoothResFunctor_trivialF2 V.toSubgroup
        (Subgroup.subgroupOfEquivOfLe hVU : V.toSubgroup.subgroupOf U.toSubgroup →* V.toSubgroup)
        (Subgroup.continuous_subgroupOfEquivOfLe hVU))) ≫
    (smoothTensorInducedTrivialF2Iso U.toSubgroup (V.toSubgroup.subgroupOf U.toSubgroup)
      (U.toSubgroup.subgroupOf_isOpen V.toSubgroup V.isOpen') t).hom

/-- On cohomology, the identification of `Ind⊗_V^G 𝔽₂` with `𝔽₂` factors through the transitivity
isomorphism, the identification `Ind⊗_V^U 𝔽₂ ≅ 𝔽₂` induced to `G`, and that of `Ind⊗_U^G 𝔽₂`. -/
private theorem coeffMap_smoothTensorInducedTrivialF2Iso_transitivity
    (s : U.toSubgroup.LeftTransversal) (N : ℕ) :
    letI : V.toSubgroup.FiniteIndex :=
      Subgroup.finiteIndex_of_finiteIndex_subgroupOf V.toSubgroup U.toSubgroup
    ContinuousCohomology.coeffMap (smoothTensorInducedTrivialF2Iso G V.toSubgroup V.isOpen'
        (Subgroup.compositeLeftTransversal hVU s t)).hom.hom N =
      ContinuousCohomology.coeffMap (smoothTensorInducedTransitivityIso hVU s t U.isOpen'
          V.isOpen' ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩).inv.hom N ≫
        ContinuousCohomology.coeffMap
          ((smoothTensorInductionFunctor ℤ G U.toSubgroup U.isOpen' s).map (normHom hVU t)).hom N ≫
        ContinuousCohomology.coeffMap
          (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen' s).hom.hom N := by
  let : V.toSubgroup.FiniteIndex :=
    Subgroup.finiteIndex_of_finiteIndex_subgroupOf V.toSubgroup U.toSubgroup
  have h := congrArg (fun φ ↦ φ.hom) ((Iso.eq_inv_comp _).2
    (smoothTensorInducedTrivialF2Iso_transitivity_hom hVU s t U.isOpen' V.isOpen'))
  refine (congrArg (ContinuousCohomology.coeffMap · N) h).trans ?_
  exact (ContinuousCohomology.coeffMap_comp _ _ N).trans
    (congrArg _ (ContinuousCohomology.coeffMap_comp _ _ N))

variable [CompactSpace V.toSubgroup] [CompactSpace U.toSubgroup]
  [CompactSpace (V.toSubgroup.subgroupOf U.toSubgroup)]
  [Fintype (U.toSubgroup ⧸ V.toSubgroup.subgroupOf U.toSubgroup)]

omit [U.toSubgroup.FiniteIndex] [(V.toSubgroup.subgroupOf U.toSubgroup).FiniteIndex]
  [CompactSpace U.toSubgroup] [Fintype (U.toSubgroup ⧸ V.toSubgroup.subgroupOf U.toSubgroup)] in
/-- Restricting a cocycle `z` of the total resolution of `𝔽₂` from `V` to `V.subgroupOf U` and
identifying the restricted coefficients with `𝔽₂` represents the pullback of the class of `z`
along `V.subgroupOf U ≃ V`. -/
private theorem gradedCohomologyClass_eq_trivialF2Map {n : ℕ}
    (z : (TopRep.homogeneousCochains (trivialF2 V.toSubgroup)).X n)
    (hz : ((TopRep.homogeneousCochains (trivialF2 V.toSubgroup)).d n (n + 1)).hom z = 0)
    {w : (trivialF2 (V.toSubgroup.subgroupOf U.toSubgroup)).gradedResolutionModule}
    (hw : w ∈ (trivialF2 (V.toSubgroup.subgroupOf U.toSubgroup)).gradedResolutionPiece n)
    (hwinv : ∀ v, (trivialF2 (V.toSubgroup.subgroupOf U.toSubgroup)).gradedResolutionTopRep.ρ v w =
      w)
    (hdw : (trivialF2 (V.toSubgroup.subgroupOf U.toSubgroup)).gradedResolutionTopRepDifferential.hom
      w = 0)
    (hwz : w = TopRep.gradedResolutionMap (X := (smoothResSubgroupOf hVU
        ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj)
      (ContinuousMonoidHom.id _) (eqToHom (smoothResFunctor_trivialF2 V.toSubgroup
        (Subgroup.subgroupOfEquivOfLe hVU : V.toSubgroup.subgroupOf U.toSubgroup →* V.toSubgroup)
        (Subgroup.continuous_subgroupOfEquivOfLe hVU))).hom
      ((smoothGradedResolutionResMap
        (Subgroup.subgroupOfEquivOfLe hVU : V.toSubgroup.subgroupOf U.toSubgroup →* V.toSubgroup)
        (Subgroup.continuous_subgroupOfEquivOfLe hVU)
        ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩).hom.hom
          ((trivialF2 V.toSubgroup).cochainToGradedResolution n z))) :
    (TopRep.gradedResolutionContraction
        (isSmoothDiscrete_trivialF2 (V.toSubgroup.subgroupOf U.toSubgroup))).gradedCohomologyClass
        w hw hwinv hdw =
      trivialF2Map (Subgroup.subgroupOfContinuousMulEquivOfLe hVU : _ →ₜ* V.toSubgroup) n
        ((trivialF2 V.toSubgroup).cochainClass n z hz) := by
  subst hwz
  -- Read the class of `z` on the total resolution.
  have hzg := (trivialF2 V.toSubgroup).cochainToGradedResolution_mem n z
  have hzinv := (trivialF2 V.toSubgroup).cochainToGradedResolution_invariant n z
  have hdzg : (trivialF2 V.toSubgroup).gradedResolutionTopRepDifferential.hom
      ((trivialF2 V.toSubgroup).cochainToGradedResolution n z) = 0 :=
    (TopRep.gradedResolutionTopRepDifferential_apply _ _).trans
      ((TopRep.gradedResolutionDifferential_cochainToGradedResolution _ n z).trans
        ((congrArg _ hz).trans (map_zero _)))
  have hx : (trivialF2 V.toSubgroup).cochainClass n z hz =
      (TopRep.gradedResolutionContraction (isSmoothDiscrete_trivialF2 V.toSubgroup)
        ).gradedCohomologyClass _ hzg hzinv hdzg := by
    rw [TopRep.gradedCohomologyClass_eq_degreeCast_cochainClass _ rfl z hz _ rfl,
      ContinuousCohomology.degreeCast_rfl, Iso.refl_hom, ConcreteCategory.id_apply]
  rw [hx, trivialF2Map_def]
  -- The restriction followed by the identification of the coefficients is a single compatible
  -- pair along `ψ' = V.subgroupOf U ≃ V`.
  let ψ' : V.toSubgroup.subgroupOf U.toSubgroup →ₜ* V.toSubgroup :=
    ⟨Subgroup.subgroupOfEquivOfLe hVU, Subgroup.continuous_subgroupOfEquivOfLe hVU⟩
  let e := eqToHom (smoothResFunctor_trivialF2 V.toSubgroup
    (Subgroup.subgroupOfEquivOfLe hVU : V.toSubgroup.subgroupOf U.toSubgroup →* V.toSubgroup)
    (Subgroup.continuous_subgroupOfEquivOfLe hVU))
  have hcomp := DFunLike.congr_fun (TopRep.gradedResolutionMap_comp ψ'
    (Y := (smoothResSubgroupOf hVU
      ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj)
    (ContinuousMonoidHom.id (V.toSubgroup.subgroupOf U.toSubgroup)) (𝟙 _) e.hom)
    ((trivialF2 V.toSubgroup).cochainToGradedResolution n z)
  rw [LinearMap.comp_apply] at hcomp
  have hψ : ψ'.comp (ContinuousMonoidHom.id _) = Subgroup.subgroupOfContinuousMulEquivOfLe hVU :=
    ContinuousMonoidHom.ext fun _ ↦ rfl
  refine Eq.trans ?_ (ConcreteCategory.congr_hom (ContinuousCohomology.map_congr_of_hom_apply hψ
    ((TopRep.resFunctor _).map (𝟙 _) ≫ e.hom) (eqToHom _) ?_ n) _)
  · rw [TopRep.map_gradedResolutionContraction_gradedCohomologyClass _ _
      (isSmoothDiscrete_trivialF2 _)]
    congr 1
    exact (congrArg _ (smoothGradedResolutionResMap_hom_hom_apply _ _ _ _)).trans hcomp.symm
  · refine hom_apply_eq_eqToHom_hom_apply _ _ fun x ↦ ?_
    refine (congrArg _ (ConcreteCategory.comp_apply _ _ x)).trans <|
      (eqToHom_smoothResFunctor_trivialF2_apply V.toSubgroup
        (Subgroup.subgroupOfEquivOfLe hVU : V.toSubgroup.subgroupOf U.toSubgroup →* V.toSubgroup)
        (Subgroup.continuous_subgroupOfEquivOfLe hVU) _).trans (congrArg _ ?_)
    rw [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

omit [U.toSubgroup.FiniteIndex] [CompactSpace U.toSubgroup] in
/-- The norm from `V.subgroupOf U` to `U` of the restriction of a cocycle `z` of `V`, normalized to
trivial coefficients by `normHom`, is the Evens norm of the pullback of the class of `z` along
`V.subgroupOf U ≃ V`. -/
private theorem coeffMap_normHom_smoothTensorInducedDiagonalClass {n : ℕ}
    (z : (TopRep.homogeneousCochains (trivialF2 V.toSubgroup)).X n)
    (hz : ((TopRep.homogeneousCochains (trivialF2 V.toSubgroup)).d n (n + 1)).hom z = 0)
    {zr : (smoothResSubgroupOf hVU
      ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj.gradedResolutionModule}
    (hzr : zr ∈ (smoothResSubgroupOf hVU ⟨trivialF2 V.toSubgroup,
      isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj.gradedResolutionPiece n)
    (hzrinv : ∀ v, (smoothResSubgroupOf hVU ⟨trivialF2 V.toSubgroup,
      isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj.gradedResolutionTopRep.ρ v zr = zr)
    (hdzr : (smoothResSubgroupOf hVU ⟨trivialF2 V.toSubgroup,
      isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj.gradedResolutionDifferential zr = 0)
    (hzrz : zr = (smoothGradedResolutionResMap
      (Subgroup.subgroupOfEquivOfLe hVU : V.toSubgroup.subgroupOf U.toSubgroup →* V.toSubgroup)
      (Subgroup.continuous_subgroupOfEquivOfLe hVU)
      ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩).hom.hom
        ((trivialF2 V.toSubgroup).cochainToGradedResolution n z)) :
    ContinuousCohomology.coeffMap (normHom hVU t).hom
        (Fintype.card (U.toSubgroup ⧸ V.toSubgroup.subgroupOf U.toSubgroup) * n)
        (smoothTensorInducedDiagonalClass.{0, u, u} (V.toSubgroup.subgroupOf U.toSubgroup)
          (U.toSubgroup.subgroupOf_isOpen V.toSubgroup V.isOpen') t
          (smoothResSubgroupOf hVU
            ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩)
          (trivialF2_add_self V.toSubgroup) zr hzr hzrinv hdzr) =
      (⟨V.toSubgroup.subgroupOf U.toSubgroup,
        U.toSubgroup.subgroupOf_isOpen V.toSubgroup V.isOpen'⟩ :
          OpenSubgroup U.toSubgroup).evensNorm
        (trivialF2Map (Subgroup.subgroupOfContinuousMulEquivOfLe hVU : _ →ₜ* V.toSubgroup) n
          ((trivialF2 V.toSubgroup).cochainClass n z hz)) := by
  -- Identify the restricted coefficients with `𝔽₂`, then multiply the tensor factors.
  refine (ConcreteCategory.congr_hom (ContinuousCohomology.coeffMap_comp _ _ _) _).trans
    ((ConcreteCategory.comp_apply _ _ _).trans ?_)
  refine (congrArg _ (Subgroup.coeffMap_smoothTensorInducedDiagonalClass _ _ t _
    (trivialF2_add_self V.toSubgroup) (trivialF2_add_self (V.toSubgroup.subgroupOf U.toSubgroup))
    hzr hzrinv hdzr)).trans ?_
  refine (evensNorm_gradedCohomologyClass ⟨V.toSubgroup.subgroupOf U.toSubgroup,
    U.toSubgroup.subgroupOf_isOpen V.toSubgroup V.isOpen'⟩ t _ _ _).symm.trans (congrArg _ ?_)
  exact gradedCohomologyClass_eq_trivialF2Map hVU z hz _ _ _ (congrArg _ hzrz)

variable [Fintype (G ⧸ U.toSubgroup)]
  [LinearOrder (U.toSubgroup ⧸ V.toSubgroup.subgroupOf U.toSubgroup)]

/-- The outer half of transitivity: let `y` be the image under the comparison of the diagonal
tensor of the restriction `zr` of a cocycle `z` of `V`, a cocycle of the total resolution of the
intermediate coefficients `Ind⊗_V^U 𝔽₂`. Normalizing its coefficients by `normHom` and then
taking the norm from `U` to `G` gives `N_U^G (N_V^U x)` for the pullback `x` of the class of `z`. -/
private theorem coeffMap_smoothTensorInducedDiagonalClass_normHom
    (s : U.toSubgroup.LeftTransversal) {n : ℕ}
    (z : (TopRep.homogeneousCochains (trivialF2 V.toSubgroup)).X n)
    (hz : ((TopRep.homogeneousCochains (trivialF2 V.toSubgroup)).d n (n + 1)).hom z = 0)
    {zr : (smoothResSubgroupOf hVU
      ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj.gradedResolutionModule}
    (hzr : zr ∈ (smoothResSubgroupOf hVU ⟨trivialF2 V.toSubgroup,
      isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj.gradedResolutionPiece n)
    (hzrinv : ∀ v, (smoothResSubgroupOf hVU ⟨trivialF2 V.toSubgroup,
      isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj.gradedResolutionTopRep.ρ v zr = zr)
    (hdzr : (smoothResSubgroupOf hVU ⟨trivialF2 V.toSubgroup,
      isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj.gradedResolutionDifferential zr = 0)
    (hzrz : zr = (smoothGradedResolutionResMap
      (Subgroup.subgroupOfEquivOfLe hVU : V.toSubgroup.subgroupOf U.toSubgroup →* V.toSubgroup)
      (Subgroup.continuous_subgroupOfEquivOfLe hVU)
      ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩).hom.hom
        ((trivialF2 V.toSubgroup).cochainToGradedResolution n z))
    {y : (smoothTensorInducedSubgroupOf hVU t V.isOpen'
      ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj.gradedResolutionModule}
    (hy : y ∈ (smoothTensorInducedSubgroupOf hVU t V.isOpen' ⟨trivialF2 V.toSubgroup,
      isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj.gradedResolutionPiece
        (Fintype.card (U.toSubgroup ⧸ V.toSubgroup.subgroupOf U.toSubgroup) * n : ℕ))
    (hyinv : ∀ g, (smoothTensorInducedSubgroupOf hVU t V.isOpen' ⟨trivialF2 V.toSubgroup,
      isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj.gradedResolutionTopRep.ρ g y = y)
    (hdy : (smoothTensorInducedSubgroupOf hVU t V.isOpen' ⟨trivialF2 V.toSubgroup,
      isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj.gradedResolutionDifferential y = 0)
    (hyz : y = (smoothTensorInducedGradedResolutionComparison
      (V.toSubgroup.subgroupOf U.toSubgroup) (U.toSubgroup.subgroupOf_isOpen V.toSubgroup V.isOpen')
      t (smoothResSubgroupOf hVU ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩)
      (trivialF2_add_self V.toSubgroup)).hom.hom (PiTensorProduct.tprod ℤ fun _ ↦ zr)) :
    ContinuousCohomology.coeffMap
        (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen' s).hom.hom
        (Fintype.card (G ⧸ U.toSubgroup) *
          (Fintype.card (U.toSubgroup ⧸ V.toSubgroup.subgroupOf U.toSubgroup) * n))
        (ContinuousCohomology.coeffMap
          ((smoothTensorInductionFunctor ℤ G U.toSubgroup U.isOpen' s).map (normHom hVU t)).hom
          (Fintype.card (G ⧸ U.toSubgroup) *
            (Fintype.card (U.toSubgroup ⧸ V.toSubgroup.subgroupOf U.toSubgroup) * n))
          (smoothTensorInducedDiagonalClass.{0, u, u} U.toSubgroup U.isOpen' s
            (smoothTensorInducedSubgroupOf hVU t V.isOpen'
              ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩)
            (smoothTensorInducedSubgroupOf_add_self hVU t V.isOpen' _
              (trivialF2_add_self V.toSubgroup)) y hy hyinv hdy)) =
      U.evensNorm ((⟨V.toSubgroup.subgroupOf U.toSubgroup,
        U.toSubgroup.subgroupOf_isOpen V.toSubgroup V.isOpen'⟩ :
          OpenSubgroup U.toSubgroup).evensNorm
        (trivialF2Map (Subgroup.subgroupOfContinuousMulEquivOfLe hVU : _ →ₜ* V.toSubgroup) n
          ((trivialF2 V.toSubgroup).cochainClass n z hz))) := by
  have hdy' := (TopRep.gradedResolutionTopRepDifferential_apply _ _).trans hdy
  -- Normalize the intermediate coefficients inside the outer norm, which is then `N_U^G`.
  refine (congrArg _ (Subgroup.coeffMap_smoothTensorInducedDiagonalClass U.toSubgroup U.isOpen' s
    (normHom hVU t) _ (trivialF2_add_self U.toSubgroup) hy hyinv hdy)).trans ?_
  refine (evensNorm_gradedCohomologyClass U s _ _ _).symm.trans (congrArg U.evensNorm ?_)
  -- The class of the normalized cocycle is the norm from `V.subgroupOf U` of the restriction.
  refine (TopRep.map_gradedResolutionContraction_gradedCohomologyClass
    (X := (smoothTensorInducedSubgroupOf hVU t V.isOpen' _).obj) (Y := trivialF2 U.toSubgroup)
    (ContinuousMonoidHom.id _) (smoothTensorInducedSubgroupOf hVU t V.isOpen' _).property
    (isSmoothDiscrete_trivialF2 U.toSubgroup) (normHom hVU t).hom hy hyinv hdy').symm.trans ?_
  refine (congrArg _ (gradedCohomologyClass_smoothTensorInducedGradedResolutionComparison
    (V.toSubgroup.subgroupOf U.toSubgroup) (U.toSubgroup.subgroupOf_isOpen V.toSubgroup V.isOpen')
    t _ (trivialF2_add_self V.toSubgroup) hzr hzrinv hdzr hy hyinv _ hyz)).trans ?_
  rw [← ContinuousCohomology.coeffMap_def]
  exact coeffMap_normHom_smoothTensorInducedDiagonalClass hVU t z hz hzr hzrinv hdzr hzrz


/-- The inner half of transitivity: by transitivity of the norm of a cocycle and compatibility of
the identifications of tensor-induced coefficients with `𝔽₂`, the norm from `V` to `G` of the class
of `z` is the norm from `U` to `G` of `y`, normalized by `normHom` and by the identification of
`Ind⊗_U^G 𝔽₂`, after transporting the degree. -/
private theorem evensNorm_cochainClass_eq_degreeCast [V.toSubgroup.FiniteIndex]
    [Fintype (G ⧸ V.toSubgroup)] (s : U.toSubgroup.LeftTransversal) {n : ℕ}
    (z : (TopRep.homogeneousCochains (trivialF2 V.toSubgroup)).X n)
    (hz : ((TopRep.homogeneousCochains (trivialF2 V.toSubgroup)).d n (n + 1)).hom z = 0)
    {y : (smoothTensorInducedSubgroupOf hVU t V.isOpen'
      ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj.gradedResolutionModule}
    (hy : y ∈ (smoothTensorInducedSubgroupOf hVU t V.isOpen' ⟨trivialF2 V.toSubgroup,
      isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj.gradedResolutionPiece
        (Fintype.card (U.toSubgroup ⧸ V.toSubgroup.subgroupOf U.toSubgroup) * n : ℕ))
    (hyinv : ∀ g, (smoothTensorInducedSubgroupOf hVU t V.isOpen' ⟨trivialF2 V.toSubgroup,
      isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj.gradedResolutionTopRep.ρ g y = y)
    (hdy : (smoothTensorInducedSubgroupOf hVU t V.isOpen' ⟨trivialF2 V.toSubgroup,
      isSmoothDiscrete_trivialF2 V.toSubgroup⟩).obj.gradedResolutionDifferential y = 0)
    (hyz : y = (smoothTensorInducedGradedResolutionComparison
      (V.toSubgroup.subgroupOf U.toSubgroup) (U.toSubgroup.subgroupOf_isOpen V.toSubgroup V.isOpen')
      t (smoothResSubgroupOf hVU ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩)
      (trivialF2_add_self V.toSubgroup)).hom.hom (PiTensorProduct.tprod ℤ fun _ ↦
        (smoothGradedResolutionResMap
          (Subgroup.subgroupOfEquivOfLe hVU : V.toSubgroup.subgroupOf U.toSubgroup →* V.toSubgroup)
          (Subgroup.continuous_subgroupOfEquivOfLe hVU)
          ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩).hom.hom
            ((trivialF2 V.toSubgroup).cochainToGradedResolution n z))) :
    V.evensNorm ((trivialF2 V.toSubgroup).cochainClass n z hz) =
      (ContinuousCohomology.degreeCast (trivialF2 G) (by
        rw [Fintype.card_congr (Subgroup.quotientEquivProdOfLE hVU), Fintype.card_prod,
          mul_assoc])).hom
      (ContinuousCohomology.coeffMap
        (smoothTensorInducedTrivialF2Iso G U.toSubgroup U.isOpen' s).hom.hom
        (Fintype.card (G ⧸ U.toSubgroup) *
          (Fintype.card (U.toSubgroup ⧸ V.toSubgroup.subgroupOf U.toSubgroup) * n))
        (ContinuousCohomology.coeffMap
          ((smoothTensorInductionFunctor ℤ G U.toSubgroup U.isOpen' s).map (normHom hVU t)).hom
          (Fintype.card (G ⧸ U.toSubgroup) *
            (Fintype.card (U.toSubgroup ⧸ V.toSubgroup.subgroupOf U.toSubgroup) * n))
          (smoothTensorInducedDiagonalClass.{0, u, u} U.toSubgroup U.isOpen' s
            (smoothTensorInducedSubgroupOf hVU t V.isOpen'
              ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩)
            (smoothTensorInducedSubgroupOf_add_self hVU t V.isOpen' _
              (trivialF2_add_self V.toSubgroup)) y hy hyinv hdy))) := by
  have hdzg : (trivialF2 V.toSubgroup).gradedResolutionDifferential
      ((trivialF2 V.toSubgroup).cochainToGradedResolution n z) = 0 := by
    rw [TopRep.gradedResolutionDifferential_cochainToGradedResolution, hz, map_zero]
  rw [evensNorm_cochainClass V (Subgroup.compositeLeftTransversal hVU s t),
    tensorNormCocycleClass_def, coeffMap_smoothTensorInducedTrivialF2Iso_transitivity hVU t s]
  refine (ConcreteCategory.comp_apply _ _ _).trans ((ConcreteCategory.comp_apply _ _ _).trans ?_)
  -- Transitivity of the norm of a cocycle, along `Ind⊗_U^G Ind⊗_V^U 𝔽₂ ≅ Ind⊗_V^G 𝔽₂`.
  refine (congrArg _ (congrArg _ (coeffMap_smoothTensorInducedDiagonalClass_transitivity hVU s t
    U.isOpen' V.isOpen' ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩
    (trivialF2_add_self V.toSubgroup) ((trivialF2 V.toSubgroup).cochainToGradedResolution_mem n z)
    ((trivialF2 V.toSubgroup).cochainToGradedResolution_invariant n z) hdzg hy hyinv hdy
    hyz))).trans ?_
  -- Move the degree transport past the two coefficient maps.
  have hnat {X Y : TopRep.{u} ℤ G} (g : X ⟶ Y) {a b : ℕ} (h : a = b)
      (c : continuousCohomology a X) :
      ContinuousCohomology.coeffMap g b ((ContinuousCohomology.degreeCast X h).hom c) =
        (ContinuousCohomology.degreeCast Y h).hom (ContinuousCohomology.coeffMap g a c) := by
    rw [← ConcreteCategory.comp_apply, ← ContinuousCohomology.degreeCast_naturality,
      ConcreteCategory.comp_apply]
  exact (congrArg _ (hnat _ _ _)).trans (hnat _ _ _)

end Normalization

section Transitivity

variable (hVU : V ≤ U)
  [U.toSubgroup.FiniteIndex] [CompactSpace U.toSubgroup] [Fintype (G ⧸ U.toSubgroup)]
  [V.toSubgroup.FiniteIndex] [CompactSpace V.toSubgroup] [Fintype (G ⧸ V.toSubgroup)]
  [CompactSpace (V.toSubgroup.subgroupOf U.toSubgroup)]
  [Fintype (U.toSubgroup ⧸ V.toSubgroup.subgroupOf U.toSubgroup)]

/-- **Transitivity of the Evens norm.** Let `V ≤ U` be compact open subgroups of finite index in
`G`, and regard `V` as the open subgroup `V.subgroupOf U` of `U`. For `x ∈ Hⁿ(V, 𝔽₂)`, the norm
from `V` to `G` of `x` is the norm from `U` to `G` of the norm from `V.subgroupOf U` to `U` of the
pullback of `x` along `V.subgroupOf U ≃ V`: `N_V^G x = N_U^G (N_V^U x)`, after transporting the
degree `[G : U] ([U : V] n)` to `[G : V] n`. -/
theorem evensNorm_trans {n : ℕ} (x : continuousCohomology n (trivialF2 V.toSubgroup)) :
    V.evensNorm x =
      (ContinuousCohomology.degreeCast (trivialF2 G) (by
        rw [Fintype.card_congr (Subgroup.quotientEquivProdOfLE (OpenSubgroup.toSubgroup_le.2 hVU)),
          Fintype.card_prod, mul_assoc])).hom
        (U.evensNorm ((⟨V.toSubgroup.subgroupOf U.toSubgroup,
          U.toSubgroup.subgroupOf_isOpen V.toSubgroup V.isOpen'⟩ :
            OpenSubgroup U.toSubgroup).evensNorm
          (trivialF2Map (Subgroup.subgroupOfContinuousMulEquivOfLe
            (OpenSubgroup.toSubgroup_le.2 hVU) : _ →ₜ* V.toSubgroup) n x))) := by
  -- Represent `x` by a cocycle `z`, restrict it to `V.subgroupOf U` and take the norm `y` of the
  -- restriction on the total resolution of `Ind⊗_V^U 𝔽₂`. The two private lemmas above compute
  -- the two sides from `y`.
  have hVU' : V.toSubgroup ≤ U.toSubgroup := OpenSubgroup.toSubgroup_le.2 hVU
  obtain ⟨z, hz, rfl⟩ := TopRep.exists_cochainClass_eq x
  let s : U.toSubgroup.LeftTransversal := default
  let t : (V.toSubgroup.subgroupOf U.toSubgroup).LeftTransversal := default
  let : LinearOrder (U.toSubgroup ⧸ V.toSubgroup.subgroupOf U.toSubgroup) :=
    LinearOrder.lift' _ (Fintype.equivFin _).injective
  let A : SmoothDiscreteTopRep.{0, u, u} ℤ V.toSubgroup :=
    ⟨trivialF2 V.toSubgroup, isSmoothDiscrete_trivialF2 V.toSubgroup⟩
  let zg := (trivialF2 V.toSubgroup).cochainToGradedResolution n z
  have hzg : zg ∈ A.obj.gradedResolutionPiece n :=
    (trivialF2 V.toSubgroup).cochainToGradedResolution_mem n z
  have hzinv : ∀ v, A.obj.gradedResolutionTopRep.ρ v zg = zg :=
    (trivialF2 V.toSubgroup).cochainToGradedResolution_invariant n z
  have hdzg : A.obj.gradedResolutionDifferential zg = 0 := by
    rw [TopRep.gradedResolutionDifferential_cochainToGradedResolution, hz, map_zero]
  let ρ := smoothGradedResolutionResMap
    (Subgroup.subgroupOfEquivOfLe hVU' : V.toSubgroup.subgroupOf U.toSubgroup →* V.toSubgroup)
    (Subgroup.continuous_subgroupOfEquivOfLe hVU') A
  let A' := smoothResSubgroupOf hVU' A
  have hA' : ∀ a : A'.obj.V, a + a = 0 := trivialF2_add_self V.toSubgroup
  have hzr : ρ.hom.hom zg ∈ A'.obj.gradedResolutionPiece n :=
    (smoothGradedResolutionResMap_hom_hom_apply _
      (Subgroup.continuous_subgroupOfEquivOfLe hVU') A zg).symm ▸
      TopRep.gradedResolutionMap_mem_piece _ _ hzg
  have hzrinv : ∀ v, A'.obj.gradedResolutionTopRep.ρ v (ρ.hom.hom zg) = ρ.hom.hom zg :=
    fun v ↦ (congrArg _ (smoothGradedResolutionResMap_hom_hom_apply _
      (Subgroup.continuous_subgroupOfEquivOfLe hVU') A zg)).trans <|
      (TopRep.gradedResolutionTopRep_ρ_apply _ _ _).trans <|
        (TopRep.gradedResolutionMap_invariant _ _ (fun g ↦
          (TopRep.gradedResolutionTopRep_ρ_apply _ _ _).symm.trans (hzinv g)) v).trans
          (smoothGradedResolutionResMap_hom_hom_apply _
            (Subgroup.continuous_subgroupOfEquivOfLe hVU') A zg).symm
  have hdzr : A'.obj.gradedResolutionDifferential (ρ.hom.hom zg) = 0 :=
    (smoothGradedResolutionResMap_differential _
      (Subgroup.continuous_subgroupOfEquivOfLe hVU') A zg).symm.trans
      ((congrArg ρ.hom.hom hdzg).trans (map_zero _))
  let y := (smoothTensorInducedGradedResolutionComparison (V.toSubgroup.subgroupOf U.toSubgroup)
    (U.toSubgroup.subgroupOf_isOpen V.toSubgroup V.isOpen') t A' hA').hom.hom
      (PiTensorProduct.tprod ℤ fun _ ↦ ρ.hom.hom zg)
  have hy := smoothTensorInducedGradedResolutionComparison_tprod_const_mem_gradedResolutionPiece
    (V.toSubgroup.subgroupOf U.toSubgroup) (U.toSubgroup.subgroupOf_isOpen V.toSubgroup V.isOpen')
    t A' hA' hzr
  have hyinv := gradedResolutionTopRep_ρ_smoothTensorInducedGradedResolutionComparison_tprod_const
    (V.toSubgroup.subgroupOf U.toSubgroup) (U.toSubgroup.subgroupOf_isOpen V.toSubgroup V.isOpen')
    t A' hA' hzrinv
  have hdy :=
    gradedResolutionTopRepDifferential_smoothTensorInducedGradedResolutionComparison_eq_zero
    (V.toSubgroup.subgroupOf U.toSubgroup) (U.toSubgroup.subgroupOf_isOpen V.toSubgroup V.isOpen')
    t A' hA' hdzr
  -- Transitivity of the norm of a cocycle, then normalize the coefficients in stages.
  rw [evensNorm_cochainClass_eq_degreeCast hVU' t s z hz hy hyinv
    ((TopRep.gradedResolutionTopRepDifferential_apply _ _).symm.trans hdy) rfl]
  exact congrArg _ (coeffMap_smoothTensorInducedDiagonalClass_normHom hVU' t s z hz hzr hzrinv
    hdzr rfl hy hyinv _ rfl)

end Transitivity

end OpenSubgroup

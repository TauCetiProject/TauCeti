/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import TauCeti.GroupTheory.GroupExtension.Cohomology
public import TauCeti.RepresentationTheory.Rep.OfMulDistribMulAction
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Cohomological transport for relabelled group extensions

Given a group extension `S : GroupExtension M E G` with abelian kernel and action-intertwining
equivalences `eM : M' ≃* M` and `eG : G ≃* G'`, Mathlib's `groupCohomology.mapIso` applied to
`Rep.ofMulDistribMulActionLinearEquiv` produces an isomorphism
`TauCeti.GroupExtension.relabelCohomologyIso : Hⁿ(G, M) ≅ Hⁿ(G', M')`.

Its forward and inverse morphisms are given in terms of `groupCohomology.map` by
`TauCeti.GroupExtension.relabelCohomologyIso_hom` and
`TauCeti.GroupExtension.relabelCohomologyIso_inv`. In degree `2`, this isomorphism sends the
cohomology class of any normalized section of `S` to the cohomology class of any normalized section
of `S.relabel eM eG` (`TauCeti.GroupExtension.relabelCohomologyIso_cohomologyClass_factorSet`). In
particular, two extensions whose kernels and quotients are identified with a common pair `(M', G')`
inducing the same action can have their classes compared directly inside the single group
`H²(G', M')`.

## Main definitions

* `TauCeti.GroupExtension.relabelCohomologyIso`: the isomorphism `Hⁿ(G, M) ≅ Hⁿ(G', M')` induced
  by action-intertwining equivalences `eM : M' ≃* M` and `eG : G ≃* G'`.

## Main results

* `TauCeti.GroupExtension.relabelCohomologyIso_hom`,
  `TauCeti.GroupExtension.relabelCohomologyIso_inv`: the forward and inverse maps of
  `relabelCohomologyIso` in terms of `groupCohomology.map`.
* `TauCeti.GroupExtension.relabelCohomologyIso_cohomologyClass_factorSet`: `relabelCohomologyIso`
  in degree `2` transports the cohomology class of an extension to that of its relabelling.
-/

public section

namespace TauCeti.GroupExtension

open CategoryTheory _root_.groupCohomology

section Cohomology

variable {G M G' M' : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
  [Group G'] [CommGroup M'] [MulDistribMulAction G' M']

/-- **Isomorphism on group cohomology induced by relabelling kernel and quotient.** Equivalences
`eM : M' ≃* M` and `eG : G ≃* G'` intertwining the actions induce an isomorphism
`Hⁿ(G, M) ≅ Hⁿ(G', M')` in every degree `n`. -/
noncomputable def relabelCohomologyIso (eM : M' ≃* M) (eG : G ≃* G')
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m) (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction G M) n ≅
      groupCohomology (Rep.ofMulDistribMulAction G' M') n :=
  groupCohomology.mapIso eG (Rep.ofMulDistribMulActionLinearEquiv G G' eM)
    (Rep.ofMulDistribMulActionLinearEquiv_isIntertwining eM eG hsmul) n

/-- The forward map of `relabelCohomologyIso` is `groupCohomology.map` along `eG.symm` and
`Rep.ofMulDistribMulActionResHom`. -/
theorem relabelCohomologyIso_hom (eM : M' ≃* M) (eG : G ≃* G')
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m) (n : ℕ) :
    (relabelCohomologyIso eM eG hsmul n).hom =
      groupCohomology.map eG.symm.toMonoidHom
        (Rep.ofMulDistribMulActionResHom eM eG hsmul) n :=
  groupCohomology.mapIso_hom ..

/-- The inverse map of `relabelCohomologyIso` is `groupCohomology.map` along `eG` and
`Rep.ofMulDistribMulActionResHom` for the inverse equivalences. -/
theorem relabelCohomologyIso_inv (eM : M' ≃* M) (eG : G ≃* G')
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m) (n : ℕ) :
    (relabelCohomologyIso eM eG hsmul n).inv =
      groupCohomology.map eG.toMonoidHom
        (Rep.ofMulDistribMulActionResHom eM.symm eG.symm fun g' m ↦ by
          simpa using (eM.symm_apply_eq.2
            ((hsmul (eG.symm g') (eM.symm m)).trans (by simp))).symm) n := by
  rw [relabelCohomologyIso, groupCohomology.mapIso_inv]
  refine congrArg (fun φ ↦ groupCohomology.map eG.toMonoidHom φ n)
    (Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun a ↦ ?_)
  exact congrArg (fun f : _ ≃ₗ[ℤ] _ ↦ f a) (Rep.ofMulDistribMulActionLinearEquiv_symm eM)

/-- **Cohomology class transport under relabelling.** In degree `2`, `relabelCohomologyIso` sends
the cohomology class of any normalized section of `S` to the cohomology class of any normalized
section of `S.relabel eM eG`. -/
theorem relabelCohomologyIso_cohomologyClass_factorSet {E : Type*} [Group E]
    {S : GroupExtension M E G} (eM : M' ≃* M) (eG : G ≃* G')
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m)
    (σ : S.Section) (hσ : σ 1 = 1) (hact : InducesAction S)
    (σ' : (S.relabel eM eG).Section) (hσ' : σ' 1 = 1) :
    (relabelCohomologyIso eM eG hsmul 2).hom (factorSet σ hσ hact).cohomologyClass =
      (factorSet σ' hσ' (hact.relabel eM eG hsmul)).cohomologyClass := by
  have hσr : (σ.relabel eM eG) 1 = 1 := (σ.relabel_one_eq_one_iff eM eG).2 hσ
  rw [← cohomologyClass_factorSet_eq (σ.relabel eM eG) σ' hσr hσ' (hact.relabel eM eG hsmul),
    FactorSet.cohomologyClass_def, FactorSet.cohomologyClass_def, relabelCohomologyIso_hom,
    H2π_comp_map_apply]
  refine congrArg (H2π (Rep.ofMulDistribMulAction G' M')) (cocycles₂_ext fun g₁' g₂' ↦ ?_)
  rw [TauCeti.groupCohomology.mapCocycles₂_apply, FactorSet.coe_toCocycles₂,
    FactorSet.coe_toCocycles₂, coe_factorSet, coe_factorSet]
  refine (Rep.toAdditive (M := G') (G := M')).injective ?_
  refine (Rep.toAdditive_ofMulDistribMulActionResHom_hom eM eG hsmul _).trans ?_
  exact congrArg Additive.ofMul (σ.factorSetFun_relabel eM eG g₁' g₂').symm

end Cohomology

end TauCeti.GroupExtension

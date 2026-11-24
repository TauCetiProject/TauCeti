/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.Cohomology
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.OfMulDistribMulAction
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Cohomological transport for relabelled group extensions

Given a group extension `S : GroupExtension M E G` with abelian kernel and action-intertwining
equivalences `eM : M' ≃* M` and `eG : G ≃* G'`, `TauCeti.groupCohomology.relabelCohomologyIso`
gives an isomorphism `Hⁿ(G, M) ≅ Hⁿ(G', M')`.

In degree `2`, this isomorphism sends the cohomology class of any normalized section of `S` to the
cohomology class of any normalized section of any extension `S'` equal to `S.relabel eM eG`
(`TauCeti.GroupExtension.relabelCohomologyIso_cohomologyClass_factorSet`). In particular, two
extensions whose kernels and quotients are identified with a common pair `(M', G')` inducing the
same action can have their classes compared directly inside the single group `H²(G', M')`.

## Main results

* `TauCeti.GroupExtension.relabelCohomologyIso_cohomologyClass_factorSet`: `relabelCohomologyIso`
  in degree `2` transports the cohomology class of an extension to that of any extension equal to
  its relabelling.
-/

public section

namespace TauCeti.GroupExtension

open CategoryTheory _root_.groupCohomology TauCeti.groupCohomology

section Cohomology

variable {G M G' M' : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
  [Group G'] [CommGroup M'] [MulDistribMulAction G' M']

/-- **Cohomology class transport under relabelling.** In degree `2`, `relabelCohomologyIso` sends
the cohomology class of any normalized section of `S` to the cohomology class of any normalized
section of any extension `S'` equal to `S.relabel eM eG`. -/
theorem relabelCohomologyIso_cohomologyClass_factorSet {E : Type*} [Group E]
    {S : GroupExtension M E G} {S' : GroupExtension M' E G'}
    (eM : M' ≃* M) (eG : G ≃* G')
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m)
    (hS : S' = S.relabel eM eG)
    (σ : S.Section) (hσ : σ 1 = 1) (hact : S.InducesAction)
    (σ' : S'.Section) (hσ' : σ' 1 = 1) (hact' : S'.InducesAction) :
    (relabelCohomologyIso eM eG hsmul 2).hom (factorSet σ hσ hact).cohomologyClass =
      (factorSet σ' hσ' hact').cohomologyClass := by
  subst hS
  have hσr : (σ.relabel eM eG) 1 = 1 := (σ.relabel_one_eq_one_iff eM eG).2 hσ
  rw [← cohomologyClass_factorSet_eq (σ.relabel eM eG) σ' hσr hσ' hact',
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

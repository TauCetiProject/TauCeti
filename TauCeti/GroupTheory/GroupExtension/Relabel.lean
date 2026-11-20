/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import TauCeti.GroupTheory.GroupExtension.Cohomology
import Mathlib.Algebra.Module.Equiv.Basic
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Relabelling sections, splittings, and cohomology classes of group extensions

Given a group extension `S : GroupExtension N E G` and isomorphisms `eN : N' ≃* N` and
`eG : G ≃* G'`, `GroupExtension.relabel S eN eG` is the same middle group `E` viewed as an
extension of `G'` by `N'`. This file transports sections, splittings, factor sets, and cohomology
classes along such a relabelling.

For arbitrary groups, pulling back along `eG.symm` transports sections
(`GroupExtension.Section.relabel`) and splittings (`GroupExtension.Splitting.relabel`), so
splitting is invariant under relabelling (`GroupExtension.nonempty_splitting_relabel_iff`), and
the section's bare factor set transforms by precomposition with `eG.symm` and postcomposition
with `eN.symm` (`TauCeti.GroupExtension.factorSetFun_relabel`).

When the kernel is abelian and `eN`, `eG` intertwine ambient `MulDistribMulAction` instances on
`N` and `N'`, Mathlib's `groupCohomology.mapIso` produces an isomorphism
`TauCeti.GroupExtension.relabelCohomologyIso : Hⁿ(G, M) ≅ Hⁿ(G', M')`. In degree `2`, this
isomorphism sends the cohomology class of any normalized section of `S` to the cohomology class of
any normalized section of `S.relabel eM eG`
(`TauCeti.GroupExtension.relabelCohomologyIso_cohomologyClass_factorSet`). In particular, two
extensions whose kernels and quotients are identified with a common pair `(M', G')` inducing the
same action can have their classes compared directly inside the single group `H²(G', M')`.

## Main definitions

* `GroupExtension.Section.relabel`: transport a section along `GroupExtension.relabel`.
* `GroupExtension.Splitting.relabel`: transport a splitting along `GroupExtension.relabel`.
* `TauCeti.GroupExtension.relabelCohomologyIso`: the isomorphism `Hⁿ(G, M) ≅ Hⁿ(G', M')` induced
  by action-intertwining equivalences `eM : M' ≃* M` and `eG : G ≃* G'`.

## Main results

* `GroupExtension.nonempty_splitting_relabel_iff`: a relabelled extension splits if and only if
  the original extension splits.
* `TauCeti.GroupExtension.factorSetFun_relabel`: formula for the factor set of a relabelled
  section.
* `TauCeti.GroupExtension.relabelCohomologyIso_cohomologyClass_factorSet`: `relabelCohomologyIso`
  in degree `2` transports the cohomology class of an extension to that of its relabelling.
-/

public section

namespace GroupExtension

variable {N E G N' G' : Type*} [Group N] [Group E] [Group G] [Group N'] [Group G']
  {S : GroupExtension N E G}

/-- Transport a section of `S` to a section of `S.relabel eN eG` by precomposing with
`eG.symm`. -/
@[to_additive
  /-- Transport a section of an additive extension `S` to a section of `S.relabel eN eG` by
  precomposing with `eG.symm`. -/]
def Section.relabel (σ : S.Section) (eN : N' ≃* N) (eG : G ≃* G') :
    (S.relabel eN eG).Section where
  toFun g' := σ (eG.symm g')
  rightInverse_rightHom g' := by
    simp [GroupExtension.relabel_rightHom]

/-- Evaluating a relabelled section at `g'` evaluates the original section at `eG.symm g'`. -/
@[to_additive (attr := simp)
  /-- Evaluating a relabelled additive section at `g'` evaluates the original section at
  `eG.symm g'`. -/]
theorem Section.relabel_apply (σ : S.Section) (eN : N' ≃* N) (eG : G ≃* G') (g' : G') :
    σ.relabel eN eG g' = σ (eG.symm g') :=
  (rfl)

/-- A relabelled section is normalized if and only if the original section is normalized. -/
@[to_additive
  /-- A relabelled additive section is normalized if and only if the original section is
  normalized. -/]
theorem Section.relabel_one_eq_one_iff (σ : S.Section) (eN : N' ≃* N) (eG : G ≃* G') :
    σ.relabel eN eG 1 = 1 ↔ σ 1 = 1 := by
  simp [Section.relabel_apply]

/-- Transport a splitting of `S` to a splitting of `S.relabel eN eG` by precomposing with
`eG.symm`. -/
@[to_additive
  /-- Transport a splitting of an additive extension `S` to a splitting of `S.relabel eN eG` by
  precomposing with `eG.symm`. -/]
def Splitting.relabel (s : S.Splitting) (eN : N' ≃* N) (eG : G ≃* G') :
    (S.relabel eN eG).Splitting where
  toMonoidHom := s.toMonoidHom.comp eG.symm.toMonoidHom
  rightInverse_rightHom g' := by
    rw [GroupExtension.relabel_rightHom]
    exact (congrArg eG (s.rightInverse_rightHom (eG.symm g'))).trans (eG.apply_symm_apply g')

/-- Evaluating a relabelled splitting at `g'` evaluates the original splitting at `eG.symm g'`. -/
@[to_additive (attr := simp)
  /-- Evaluating a relabelled additive splitting at `g'` evaluates the original splitting at
  `eG.symm g'`. -/]
theorem Splitting.relabel_apply (s : S.Splitting) (eN : N' ≃* N) (eG : G ≃* G') (g' : G') :
    s.relabel eN eG g' = s (eG.symm g') :=
  (rfl)

/-- The underlying section of a relabelled splitting is the relabelled underlying section. -/
@[to_additive (attr := simp)
  /-- The underlying section of a relabelled additive splitting is the relabelled underlying
  section. -/]
theorem Splitting.relabel_toSection (s : S.Splitting) (eN : N' ≃* N) (eG : G ≃* G') :
    (s.relabel eN eG).toSection = s.toSection.relabel eN eG :=
  (rfl)

/-- A relabelled extension splits if and only if the original extension splits. -/
@[to_additive
  /-- A relabelled additive extension splits if and only if the original additive extension
  splits. -/]
theorem nonempty_splitting_relabel_iff (S : GroupExtension N E G) (eN : N' ≃* N) (eG : G ≃* G') :
    Nonempty (S.relabel eN eG).Splitting ↔ Nonempty S.Splitting := by
  refine ⟨fun ⟨s⟩ ↦ ⟨⟨s.toMonoidHom.comp eG.toMonoidHom, fun g ↦ ?_⟩⟩,
    fun ⟨s⟩ ↦ ⟨s.relabel eN eG⟩⟩
  have h := s.rightInverse_rightHom (eG g)
  rw [GroupExtension.relabel_rightHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
  exact eG.injective (by simpa using h)

end GroupExtension

namespace TauCeti.GroupExtension

open CategoryTheory _root_.groupCohomology

/-- Relabelling a section transforms its bare factor set by precomposing with `eG.symm` and
postcomposing with `eM.symm`. -/
theorem factorSetFun_relabel {M E G M' G' : Type*} [Group M] [Group E] [Group G]
    [Group M'] [Group G'] {S : GroupExtension M E G} (σ : S.Section)
    (eM : M' ≃* M) (eG : G ≃* G') (g' h' : G') :
    factorSetFun (σ.relabel eM eG) (g', h') =
      eM.symm (factorSetFun σ (eG.symm g', eG.symm h')) := by
  apply eM.injective
  rw [MulEquiv.apply_symm_apply]
  apply S.inl_injective
  have h := inl_factorSetFun (σ.relabel eM eG) g' h'
  rw [GroupExtension.relabel_inl, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
  rw [h, inl_factorSetFun]
  simp

section Cohomology

variable {G M G' M' : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
  [Group G'] [CommGroup M'] [MulDistribMulAction G' M']

/-- The `ℤ`-linear equivalence between the underlying modules of `Rep.ofMulDistribMulAction G M`
and `Rep.ofMulDistribMulAction G' M'` induced by `eM : M' ≃* M`. -/
private def relabelLinearEquiv (eM : M' ≃* M) :
    (Rep.ofMulDistribMulAction G M).V ≃ₗ[ℤ] (Rep.ofMulDistribMulAction G' M').V :=
  ((Rep.toAdditive (M := G) (G := M)).trans
    ((MulEquiv.toAdditive eM.symm).trans
      (Rep.toAdditive (M := G') (G := M')).symm)).toIntLinearEquiv

private theorem toAdditive_relabelLinearEquiv (eM : M' ≃* M)
    (a : Rep.ofMulDistribMulAction G M) :
    Rep.toAdditive (M := G') (G := M') (relabelLinearEquiv (G := G) (G' := G') eM a) =
      Additive.ofMul (eM.symm (Additive.toMul (Rep.toAdditive (M := G) (G := M) a))) :=
  (rfl)

/-- **Isomorphism on group cohomology induced by relabelling kernel and quotient.** Equivalences
`eM : M' ≃* M` and `eG : G ≃* G'` intertwining the actions induce an isomorphism
`Hⁿ(G, M) ≅ Hⁿ(G', M')` in every degree `n`. -/
noncomputable def relabelCohomologyIso (eM : M' ≃* M) (eG : G ≃* G')
    (hsmul : ∀ (g : G) (m : M'), eM (eG g • m) = g • eM m) (n : ℕ) :
    groupCohomology (Rep.ofMulDistribMulAction G M) n ≅
      groupCohomology (Rep.ofMulDistribMulAction G' M') n :=
  groupCohomology.mapIso eG (relabelLinearEquiv (G := G) (G' := G') eM) (fun g ↦
    LinearMap.ext fun a ↦ (Rep.toAdditive (M := G') (G := M')).injective <| by
      have hρ {H N : Type} [Group H] [CommGroup N] [MulDistribMulAction H N]
          (h : H) (x : Rep.ofMulDistribMulAction H N) :
          Rep.toAdditive (M := H) (G := N) ((Rep.ofMulDistribMulAction H N).ρ h x) =
            Additive.ofMul (h • Additive.toMul (Rep.toAdditive (M := H) (G := N) x)) :=
        Rep.ofMulDistribMulAction_ρ_apply_apply h (Rep.toAdditive x)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        toAdditive_relabelLinearEquiv, hρ, hρ, toAdditive_relabelLinearEquiv,
        toMul_ofMul, toMul_ofMul]
      exact congrArg Additive.ofMul (eM.injective (by simp [hsmul]))) n

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
    FactorSet.cohomologyClass_def, FactorSet.cohomologyClass_def, relabelCohomologyIso,
    groupCohomology.mapIso_hom, ← ConcreteCategory.comp_apply, H2π_comp_map,
    ConcreteCategory.comp_apply]
  refine congrArg (H2π (Rep.ofMulDistribMulAction G' M')) (cocycles₂_ext fun g₁' g₂' ↦ ?_)
  rw [TauCeti.groupCohomology.mapCocycles₂_apply, FactorSet.coe_toCocycles₂,
    FactorSet.coe_toCocycles₂, coe_factorSet, coe_factorSet]
  exact congrArg Additive.ofMul (factorSetFun_relabel σ eM eG g₁' g₂').symm

end Cohomology

end TauCeti.GroupExtension

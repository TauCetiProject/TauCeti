/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Spf
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections

/-!
# Sections of the completion of a finitely presented module on an affine scheme

Let `J` be an ideal of a commutative ring `R` and `M` a finitely presented module on `Spec R`. The
completion functor sends `M` to the coherent formal module `(M ⧸ J ^ (n + 1) M)ₙ` on the formal
completion of `Spec R` along `V(J)`, whose `n`-th level is the pullback of `M` to
`V(J ^ (n + 1))`. Transported along the identification `specIso J` of this formal completion with
the system `spf J` of the schemes `Spec (R ⧸ J ^ (n + 1))`, its tower of global sections
`CoherentFormalModule.sectionsTower J` is the reduction `(Γ(M) ⧸ J ^ (n + 1) Γ(M))ₙ` of the
`R`-module `Γ(M)` of global sections of `M` (`completionFunctorSectionsTowerIso`): restricting a
global section of `M` to `Spec (R ⧸ J ^ (n + 1))` is surjective with kernel `J ^ (n + 1) Γ(M)`, as
`Γ(Spec (R ⧸ J ^ (n + 1)), M) = (R ⧸ J ^ (n + 1)) ⊗_R Γ(M)` for the quasi-coherent module `M`.
Taking inverse limits, the sections of the completion of `M` are the `J`-adic completion of
`Γ(M)` (`completionFunctorSectionsLimEquiv`, Stacks, Section 30.23, Equation (30.23.3.1)); the
isomorphism sends the compatible family of restrictions of a global section `x` of `M` to the image
of `x` in the completion (`coe_completionFunctorSectionsLimEquiv_symm_of_apply`).

No noetherian hypothesis is needed: finite presentation of `M` is only used to form the
completion, and the computation of the sections holds for every ideal of every commutative ring.

## Main definitions

* `AlgebraicGeometry.Scheme.formalCompletion.completionFunctorSectionsTowerIso`: the tower of
  global sections of the completion of `M` is the reduction of `Γ(M)` along `J`.
* `AlgebraicGeometry.Scheme.formalCompletion.completionFunctorSectionsLimEquiv`: the inverse limit
  of the sections of the completion of `M` is the `J`-adic completion of `Γ(M)`.

## Main results

* `AlgebraicGeometry.Scheme.formalCompletion.completionFunctorSectionsTowerIso_hom_app_reductionπ`:
  the class of a global section of `M` modulo `J ^ (n + 1)` corresponds to its restriction to the
  `n`-th level.
* `AlgebraicGeometry.Scheme.formalCompletion.coe_completionFunctorSectionsLimEquiv_symm_of_apply`:
  the image of a global section of `M` in the completion corresponds to the family of its
  restrictions.

## References

* [Stacks Project, Section 30.23](https://stacks.math.columbia.edu/tag/0880).
-/

public section

open CategoryTheory Opposite AlgebraicGeometry Scheme.Modules
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

universe u

namespace AlgebraicGeometry.Scheme.formalCompletion

noncomputable section

variable {R : Type u} [CommRing R] (J : Ideal R)
  (M : FinitelyPresentedSheaf (Spec (CommRingCat.of R)))

/-! ### Pulling back global sections -/

/-- The reduction isomorphisms of the pullback of a completion carry the restriction of a global
section to the next level to its restriction to the given level. Here `t₀`, `t₁` are the closed
immersions of two consecutive levels `V₀ ⟶ V₁` of a formal completion into the scheme `S`, and
`g₀`, `g₁` the components at these levels of a morphism into it from an adic thickening system
with transition `ι : W₀ ⟶ W₁`. -/
private lemma transition_pullbackSections {S V₀ V₁ W₀ W₁ : Scheme.{u}} {t₀ : V₀ ⟶ S}
    {t₁ : V₁ ⟶ S} {ι' : V₀ ⟶ V₁} (hι' : ι' ≫ t₁ = t₀) {g₀ : W₀ ⟶ V₀} {g₁ : W₁ ⟶ V₁}
    {ι : W₀ ⟶ W₁} (w : ι ≫ g₁ = g₀ ≫ ι') (N : S.Modules) (x : Γ(N, ⊤)) :
    ((pullbackCompIsoOfCommSq ⟨w⟩).hom.app ((pullback t₁).obj N) ≫
        (pullback g₀).map ((pullbackComp ι' t₁).hom.app N ≫ (pullbackCongr hι').hom.app N)).app ⊤
      (ι.pullbackSections _ ⊤ (g₁.pullbackSections _ ⊤ (t₁.pullbackSections N ⊤ x))) =
      g₀.pullbackSections _ ⊤ (t₀.pullbackSections N ⊤ x) := by
  -- Work with sections pulled back to the whole source, where the comparisons of pullback are
  -- described by the `pullbackSectionsLE` API.
  rw [← Scheme.Hom.pullbackSectionsLE_top t₁, ← Scheme.Hom.pullbackSectionsLE_top g₁,
    ← Scheme.Hom.pullbackSectionsLE_top ι, ← Scheme.Hom.pullbackSectionsLE_top t₀,
    ← Scheme.Hom.pullbackSectionsLE_top g₀]
  simp only [Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    pullbackCompIsoOfCommSq_hom_app_pullbackSectionsLE (V' := ⊤) (hV' := ι'.preimage_top.ge)
      (hO' := g₀.preimage_top.ge)]
  rw [Scheme.Hom.pullbackSectionsLE_naturality, Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Hom.pullbackSectionsLE_comp_hom, Scheme.Hom.pullbackSectionsLE_congr]

/-! ### The sections of the completion of `M` on `spf J` -/

/-- The identification of the `n`-th level of the completion of `M` on `spf J` with the
pullback of `M` along `Spec (R ⧸ J ^ (n + 1)) ⟶ Spec R`. -/
private def levelIso (n : ℕ) :
    (pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1)))))).obj M.obj ≅
      (((CoherentFormalModule.pullback (specIso J).inv).obj
        ((completionFunctor _ _).obj M)).obj n) :=
  ((pullbackCongr ((specIso_inv_app_toScheme J n).trans (spfToSpec_app J n))).symm ≪≫
    (pullbackComp _ _).symm).app M.obj

/-- Pulling global sections of `M` back to the `n`-th level of its completion on `spf J`. -/
private def sectionsπ (n : ℕ) :
    moduleSpecΓFunctor.obj M.obj ⟶ ((CoherentFormalModule.sectionsTower J).obj
      ((CoherentFormalModule.pullback (specIso J).inv).obj
        ((completionFunctor _ _).obj M))).obj (op n) :=
  (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1)))).moduleSpecΓPullbackAdjoint
    (levelIso J M n).hom

/-- `sectionsπ J M n` restricts a global section of `M` along `V(J ^ (n + 1)) ⟶ Spec R` and then
along the level `n` component of `specIso J`. -/
private lemma sectionsπ_apply (n : ℕ) (x : moduleSpecΓFunctor.obj M.obj) :
    sectionsπ J M n x = ((specIso J).inv.app n).pullbackSections _ ⊤
      ((toScheme _ _ n).pullbackSections M.obj ⊤ x) := by
  refine (CommRingCat.Hom.moduleSpecΓPullbackAdjoint_apply _ _ x).trans ?_
  have h := Scheme.Hom.pullbackSections_comp_of_eq
    (h := (specIso_inv_app_toScheme J n).trans (spfToSpec_app J n)) (s := x)
  -- `x` is a section of `moduleSpecΓFunctor.obj M.obj`, whose carrier is only definitionally
  -- `Γ(M.obj, ⊤)`, so the unit of the adjunction is exposed with `erw`.
  erw [Scheme.Hom.pullbackSections_apply] at h
  exact h

/-- The restrictions of a global section of `M` to the levels of its completion on `spf J` are
compatible with the transitions of the tower of sections. -/
private lemma transition_sectionsπ (n : ℕ) (x : moduleSpecΓFunctor.obj M.obj) :
    ((CoherentFormalModule.sectionsTower J).obj
      ((CoherentFormalModule.pullback (specIso J).inv).obj
        ((completionFunctor _ _).obj M))).transition n (sectionsπ J M (n + 1) x) =
      sectionsπ J M n x := by
  have h := transition_pullbackSections (ι_toScheme _ _ n) ((specIso J).inv.naturality n) M.obj x
  rw [CoherentFormalModule.sectionsTower_obj_transition_apply, sectionsπ_apply, sectionsπ_apply]
  -- The levels `(spf J).X n` are the affine schemes `Spec (R ⧸ J ^ (n + 1))` only after unfolding
  -- `spf`, so global sections over them are matched with `erw`.
  erw [moduleSpecΓFunctor_map_apply,
    moduleSpecΓFunctor_map_apply ((pullbackPushforwardAdjunction ((spf J).ι n)).unit.app _)]
  erw [Scheme.Hom.pullbackSections_apply ((spf J).ι n)] at h
  exact h

/-- The restrictions of a global section of `M` are compatible with the composite transitions. -/
private lemma transitionOfLE_sectionsπ {k n : ℕ} (h : k ≤ n) (x : moduleSpecΓFunctor.obj M.obj) :
    ((CoherentFormalModule.sectionsTower J).obj
      ((CoherentFormalModule.pullback (specIso J).inv).obj
        ((completionFunctor _ _).obj M))).transitionOfLE h ((sectionsπ J M n).hom x) =
      (sectionsπ J M k).hom x := by
  induction n, h using Nat.le_induction with
  | base => rw [ModuleTower.transitionOfLE_refl, LinearMap.id_apply]
  | succ n h ih =>
    exact ((ModuleTower.transitionOfLE_transition _ h _).symm.trans
      (congrArg _ (transition_sectionsπ J M n x))).trans ih

/-- Every section of the `n`-th level is the restriction of a global section of `M`. -/
private lemma sectionsπ_surjective (n : ℕ) : Function.Surjective (sectionsπ J M n) := by
  intro y
  obtain ⟨z, rfl⟩ := (moduleSpecΓFunctor.mapIso (levelIso J M n)).toLinearEquiv.surjective y
  obtain ⟨x, rfl⟩ := CommRingCat.Hom.moduleSpecΓFunctor_map_unit_surjective
    (φ := CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1)))) Ideal.Quotient.mk_surjective M.obj z
  exact ⟨x, CommRingCat.Hom.moduleSpecΓPullbackAdjoint_apply _ _ x⟩

/-- A global section of `M` restricts to zero on the `n`-th level iff it lies in
`J ^ (n + 1) Γ(M)`. -/
private lemma ker_sectionsπ (n : ℕ) :
    LinearMap.ker (sectionsπ J M n).hom = J ^ (n + 1) • (⊤ : Submodule R _) := by
  have h := CommRingCat.Hom.ker_moduleSpecΓFunctor_map_unit
    (φ := CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1)))) Ideal.Quotient.mk_surjective M.obj
  rw [CommRingCat.hom_ofHom, Ideal.mk_ker] at h
  rw [← h]
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  refine (Eq.congr_left (CommRingCat.Hom.moduleSpecΓPullbackAdjoint_apply _ _ x)).trans ?_
  exact (moduleSpecΓFunctor.mapIso (levelIso J M n)).toLinearEquiv.injective.eq_iff' (map_zero _)

/-- **The sections of the completion of a module on an affine scheme are its reductions.** For
an ideal `J` of `R` and a finitely presented module `M` on `Spec R`, the tower of global sections
of the completion `(M ⧸ J ^ (n + 1) M)ₙ` of `M` along `V(J)`, transported to `spf J`, is the
reduction `(Γ(M) ⧸ J ^ (n + 1) Γ(M))ₙ` of the `R`-module of global sections of `M`. The class of
a global section modulo `J ^ (n + 1)` corresponds to its restriction to `V(J ^ (n + 1))`
(`completionFunctorSectionsTowerIso_hom_app_reductionπ`). -/
def completionFunctorSectionsTowerIso :
    ModuleTower.reduction J (moduleSpecΓFunctor.obj M.obj) ≅
      (CoherentFormalModule.sectionsTower J).obj
        ((CoherentFormalModule.pullback (specIso J).inv).obj ((completionFunctor _ _).obj M)) :=
  NatIso.ofComponents
    (fun n ↦ (ModuleTower.quotientsLiftEquiv _ _ n.unop (sectionsπ J M n.unop).hom
      (ker_sectionsπ J M n.unop) (sectionsπ_surjective J M n.unop)).toModuleIso) <| by
    rintro ⟨n⟩ ⟨k⟩ f
    ext x
    simp only [LinearEquiv.toModuleIso_hom, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom,
      ModuleTower.map_hom_eq_transitionOfLE, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, ModuleTower.transitionOfLE_quotientsπ,
      ModuleTower.quotientsLiftEquiv_quotientsπ]
    exact (transitionOfLE_sectionsπ J M _ x).symm

/-- Under `completionFunctorSectionsTowerIso`, the class of a global section `x` of `M` modulo
`J ^ (n + 1)` is the restriction of `x` to the `n`-th level `Spec (R ⧸ J ^ (n + 1))`, through
`V(J ^ (n + 1))`. -/
@[simp]
theorem completionFunctorSectionsTowerIso_hom_app_reductionπ (n : ℕ)
    (x : moduleSpecΓFunctor.obj M.obj) :
    ((completionFunctorSectionsTowerIso J M).hom.app (op n)).hom
        (ModuleTower.reductionπ J _ n x) =
      ((specIso J).inv.app n).pullbackSections _ ⊤
        ((toScheme _ _ n).pullbackSections M.obj ⊤ x) :=
  (ModuleTower.quotientsLiftEquiv_quotientsπ _ _ n _ _ _ x).trans (sectionsπ_apply J M n x)

/-- **The inverse limit of the sections of the completion of `M` is the `J`-adic completion of
`Γ(M)`** (Stacks, Section 30.23, Equation (30.23.3.1)): for an ideal `J` of `R` and a finitely
presented module `M` on `Spec R`, the limit of the tower of global sections of the completion of
`M` along `V(J)`, transported to `spf J`, is `AdicCompletion J Γ(M)`. It sends the family of
restrictions of a global section to its image in the completion
(`coe_completionFunctorSectionsLimEquiv_symm_of_apply`). -/
@[stacks 0880]
def completionFunctorSectionsLimEquiv :
    ((CoherentFormalModule.sectionsTower J).obj
        ((CoherentFormalModule.pullback (specIso J).inv).obj
          ((completionFunctor _ _).obj M))).lim ≃ₗ[R]
      AdicCompletion J (moduleSpecΓFunctor.obj M.obj) :=
  (ModuleTower.limEquivOfIso (completionFunctorSectionsTowerIso J M)).symm ≪≫ₗ
    ModuleTower.limReductionEquiv J _

/-- Under `completionFunctorSectionsLimEquiv`, the image of a global section `x` of `M` in the
`J`-adic completion corresponds to the compatible family of the restrictions of `x` to the levels
`Spec (R ⧸ J ^ (n + 1))`. -/
@[simp]
theorem coe_completionFunctorSectionsLimEquiv_symm_of_apply (x : moduleSpecΓFunctor.obj M.obj)
    (n : ℕ) :
    ((completionFunctorSectionsLimEquiv J M).symm (AdicCompletion.of J _ x) :
        ((CoherentFormalModule.sectionsTower J).obj
          ((CoherentFormalModule.pullback (specIso J).inv).obj
            ((completionFunctor _ _).obj M))).Product) n =
      ((specIso J).inv.app n).pullbackSections _ ⊤
        ((toScheme _ _ n).pullbackSections M.obj ⊤ x) := by
  rw [completionFunctorSectionsLimEquiv, LinearEquiv.symm_trans_apply,
    ← ModuleTower.limReductionEquiv_toLimReduction, LinearEquiv.symm_apply_apply]
  simpa using completionFunctorSectionsTowerIso_hom_app_reductionπ J M n x

end

end AlgebraicGeometry.Scheme.formalCompletion

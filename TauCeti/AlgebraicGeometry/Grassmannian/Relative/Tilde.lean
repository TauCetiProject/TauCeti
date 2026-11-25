/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Grassmannian.Relative.Basic

/-!
# The relative Grassmannian of the sheaf of a module

Let `R` be a commutative ring, `M` an `R`-module and `k` a natural number. The relative
Grassmannian `G(k, M~)` of the quasi-coherent sheaf `M~` on `Spec R` is Tau Ceti's Grassmannian
scheme `G(k, M)` of the module, over `Spec R`
(`AlgebraicGeometry.Scheme.Modules.grassmannianTildeIso`).

Over the affine open `⊤` of `Spec R` the relative Grassmannian is `G(k, Γ(M~, ⊤))` over
`Spec Γ(Spec R, ⊤)` (`AlgebraicGeometry.Scheme.Modules.isPullback_grassmannianι_fromSpec`), and
the inclusion of this part is an isomorphism because `Spec Γ(Spec R, ⊤) ⟶ Spec R` is one. The
change of base ring along `R ≅ Γ(Spec R, ⊤)` is a base change of modules: a linear map `M → N`
along a ring map `R → S`, both bijective, exhibits `N` as the base change of `M`
(`IsBaseChange.of_bijective`). Applied to `M ≅ Γ(M~, ⊤)` (`AlgebraicGeometry.tilde.isoTop`), the
base change morphism `IsBaseChange.grassmannianSchemeHom` gives `G(k, Γ(M~, ⊤)) ≅ G(k, M)`.

## Main declarations

* `IsBaseChange.of_bijective`: a bijective linear map along a bijective ring map is a base change.
* `AlgebraicGeometry.Scheme.Modules.grassmannianTildeIso`: `G(k, M~) ≅ G(k, M)`.
* `AlgebraicGeometry.Scheme.Modules.grassmannianTildeIso_hom_toSpec`: it lies over `Spec R`.
-/

public section

universe u v₁ v₂

open CategoryTheory Limits Opposite

namespace IsBaseChange

variable {R : Type*} {S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  {M : Type v₁} {N : Type v₂} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  [Module S N] [IsScalarTower R S N]

/-- **Base change along an isomorphism.** If `algebraMap R S` is bijective, every bijective
`R`-linear map `f : M → N` to an `S`-module exhibits `N` as the base change of `M` to `S`. -/
theorem of_bijective (hS : Function.Bijective (algebraMap R S)) {f : M →ₗ[R] N}
    (hf : Function.Bijective f) : IsBaseChange S f := by
  let e := LinearEquiv.ofBijective f hf
  refine of_lift_unique _ fun Q _ _ _ _ g ↦ ⟨?_, ?_, ?_⟩
  · -- `g ∘ f⁻¹` is `S`-linear: every scalar of `S` comes from `R`.
    refine
      { toFun := g ∘ e.symm
        map_add' := fun x y ↦ by simp only [Function.comp_apply, map_add]
        map_smul' := fun s x ↦ ?_ }
    obtain ⟨r, rfl⟩ := hS.surjective s
    simp only [Function.comp_apply, RingHom.id_apply, algebraMap_smul, map_smul]
  · ext m
    exact congrArg g (e.symm_apply_apply m)
  · intro g' hg'
    ext n
    obtain ⟨m, rfl⟩ := hf.surjective n
    change g' (f m) = g (e.symm (e m))
    rw [e.symm_apply_apply, ← hg']
    rfl

end IsBaseChange

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-- The structure map `R → Γ(Spec R, ⊤)` is bijective. -/
theorem bijective_algebraMap_Spec_top : Function.Bijective (algebraMap R Γ(Spec R, ⊤)) := by
  rw [IsAffineOpen.algebraMap_Spec_obj,
    show homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤) = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv

/-- `Spec Γ(Spec R, ⊤) ⟶ Spec R` induced by `R → Γ(Spec R, ⊤)` is the inclusion of the affine open
`⊤`. -/
theorem Spec_map_algebraMap_Spec_top :
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(Spec R, ⊤))) =
      (isAffineOpen_top (Spec R)).fromSpec := by
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, IsAffineOpen.algebraMap_Spec_obj,
    show homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤) = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id, Category.comp_id, CommRingCat.ofHom_hom]

/-- The global sections of `M~` as an `R`-linear map `M → Γ(M~, ⊤)`. -/
noncomputable abbrev tildeToTop (M : ModuleCat.{u} R) : M →ₗ[R] Γ(tilde M, ⊤) :=
  (tilde.toOpen M ⊤).hom

/-- `M → Γ(M~, ⊤)` exhibits `Γ(M~, ⊤)` as the base change of `M` along `R ≅ Γ(Spec R, ⊤)`. -/
theorem isBaseChange_tildeToTop (M : ModuleCat.{u} R) :
    IsBaseChange Γ(Spec R, ⊤) (tildeToTop M) :=
  IsBaseChange.of_bijective bijective_algebraMap_Spec_top
    (ConcreteCategory.bijective_of_isIso (tilde.toOpen M ⊤))

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (k : ℕ)

/-- The part of `G(k, M~)` over the affine open `⊤` of `Spec R` is all of it. -/
instance isIso_grassmannianι_tilde_top :
    IsIso (grassmannianι (tilde M) k ⟨⊤, isAffineOpen_top _⟩) := by
  have : IsIso (isAffineOpen_top (Spec R)).fromSpec := by
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  exact (isPullback_grassmannianι_fromSpec (tilde M) k ⟨⊤, isAffineOpen_top _⟩).isIso_snd_of_isIso

/-- Changing the base ring along `R ≅ Γ(Spec R, ⊤)` is an isomorphism of Grassmannians. -/
instance isIso_grassmannianSchemeHom_tildeToTop :
    IsIso ((isBaseChange_tildeToTop M).grassmannianSchemeHom k) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap R Γ(Spec R, ⊤)))) := by
    rw [Spec_map_algebraMap_Spec_top, IsAffineOpen.fromSpec_top]
    infer_instance
  exact ((isBaseChange_tildeToTop M).isPullback_grassmannianSchemeHom k).flip.isIso_snd_of_isIso

/-- **The relative Grassmannian of `M~` is the Grassmannian of `M`.** For a module `M` over a
commutative ring `R`, the relative Grassmannian `G(k, M~)` of the quasi-coherent sheaf `M~` on
`Spec R` is isomorphic to the Grassmannian scheme `G(k, M)`, over `Spec R`
(`AlgebraicGeometry.Scheme.Modules.grassmannianTildeIso_hom_toSpec`). -/
noncomputable def grassmannianTildeIso :
    grassmannian (tilde M) k ≅ Module.Grassmannian.scheme R M k :=
  (asIso (grassmannianι (tilde M) k ⟨⊤, isAffineOpen_top _⟩)).symm ≪≫
    asIso ((isBaseChange_tildeToTop M).grassmannianSchemeHom k)

/-- The isomorphism `G(k, M~) ≅ G(k, M)` lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem grassmannianTildeIso_hom_toSpec :
    (grassmannianTildeIso M k).hom ≫ Module.Grassmannian.toSpec R M k =
      grassmannianToBase (tilde M) k := by
  rw [grassmannianTildeIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc,
    IsIso.inv_comp_eq, IsBaseChange.grassmannianSchemeHom_toSpec, grassmannianι_toBase,
    Spec_map_algebraMap_Spec_top]
  rfl

end AlgebraicGeometry.Scheme.Modules

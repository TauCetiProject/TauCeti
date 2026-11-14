/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.RingTheory.Localization.Algebra
public import TauCeti.RingTheory.Almost.Algebra

import Mathlib.CategoryTheory.Adjunction.Unique
import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
import TauCeti.Algebra.Category.ModuleCat.Monoidal.ChangeOfRings
import TauCeti.Algebra.Module.LocalizedModule.Submodule
import TauCeti.RingTheory.Localization.Module

/-!
# Inverting an element of the setup ideal

Let `S = (V, m)` be a basic setup and `ϖ ∈ m`; `ϖ` need not be a nonzerodivisor (for instance,
`0 ∈ m` is always allowed). Because `ϖ` annihilates every almost zero `V`-module, localizing at
the powers of `ϖ` kills almost zero modules and turns almost isomorphisms into honest
isomorphisms. Since module localization is exact, the localization functor
`ModuleCat V ⥤ ModuleCat (Localization.Away ϖ)` factors uniquely up to unique isomorphism through
an exact functor `TauCeti.Almost.invert S hϖ : Almost.Module S ⥤ ModuleCat (Localization.Away ϖ)`.

Evaluating `invert` on an almostification `N^a` recovers `N[1/ϖ]`, and evaluating it on an
arbitrary almost module `M` recovers both `(M_*)[1/ϖ]` and `(M_!)[1/ϖ]`, because `M ≅ (M_*)^a`
and `M ≅ (M_!)^a`. Base-changing `S` to `V[1/ϖ]` makes the setup classical
(`TauCeti.Almost.BasicSetup.baseChange_away_eq_classical`), so almost modules over `V[1/ϖ]`
identify with honest `V[1/ϖ]`-modules (`TauCeti.Almost.Module.baseChangeAwayEquiv`). Moreover,
`invert` inherits a braided monoidal structure from extension of scalars `M ↦ V[1/ϖ] ⊗[V] M`, and
on almost algebras `A` localization of almost elements defines a functor
`TauCeti.Almost.Algebra.invert S ϖ : Algebra S ⥤ CommAlgCat V[1/ϖ]` sending `A` to `A_*[1/ϖ]`,
which for `ϖ ∈ m` is naturally isomorphic to the functor induced by `Almost.invert S hϖ` on
commutative monoid objects. Finally, any complex of `V`-modules with almost zero homology becomes
exact after inverting `ϖ`.

## Main definitions

* `TauCeti.Almost.invert`: the exact symmetric monoidal functor
  `Almost.Module S ⥤ ModuleCat (Localization.Away ϖ)` for `ϖ ∈ S.ideal`.
* `TauCeti.Almost.toAlmostCompInvertIso` and
  `TauCeti.Almost.toAlmostCompInvertIsoExtendScalars`: the natural isomorphisms identifying
  `toAlmost S ⋙ invert S hϖ` with `ModuleCat.localizedModuleFunctor (Submonoid.powers ϖ)` and
  with `ModuleCat.extendScalars (algebraMap V (Localization.Away ϖ))`.
* `TauCeti.Almost.invertElementsIso` and `TauCeti.Almost.invertShriekIso`: the canonical
  isomorphisms `(invert S hϖ).obj M ≅ LocalizedModule (Submonoid.powers ϖ) ((elements S).obj M)`
  and `(invert S hϖ).obj M ≅ LocalizedModule (Submonoid.powers ϖ) ((shriek S).obj M)`.
* `TauCeti.Almost.Module.baseChangeAwayEquiv` and
  `TauCeti.Almost.Algebra.baseChangeAwayEquiv`: the equivalences identifying almost modules and
  almost algebras over `S.baseChange W` with honest `W`-modules and `W`-algebras when `W` is a
  localization away from `ϖ ∈ S.ideal`.
* `TauCeti.Almost.invertMonoidal` and `TauCeti.Almost.invertBraided`: the braided monoidal
  structure on `invert S hϖ`.
* `TauCeti.Almost.Algebra.invert`: the functor `Algebra S ⥤ CommAlgCat (Localization.Away ϖ)`
  sending an almost algebra `A` to `A_*[1/ϖ]`, with comparison
  `TauCeti.Almost.Algebra.invertIsoMapCommMon` for `ϖ ∈ S.ideal`.

## Main results

* `TauCeti.Almost.BasicSetup.IsAlmostZero.subsingleton_localizedModule` and
  `TauCeti.Almost.BasicSetup.IsAlmostIso.bijective_localizedModule_map`: localizing at `ϖ ∈ m`
  annihilates almost zero modules and turns almost isomorphisms into bijections.
* `TauCeti.Almost.isZero_invert_toAlmost_obj_iff` and `TauCeti.Almost.isZero_invert_obj_iff`:
  vanishing after `invert S hϖ` means power-of-`ϖ` torsion.
* `TauCeti.Almost.invertCompRestrictScalarsIsoElements` and
  `TauCeti.Almost.isEquivalence_invert_of_isUnit`: when `ϖ ∈ m` is a unit of `V`, `invert S hϖ`
  identifies with `Almost.Module.elements S` along `V ≃+* V[1/ϖ]`, and is an equivalence.
* `TauCeti.Almost.BasicSetup.IsAlmostZero.exactAt_localizedModuleFunctor` and
  `TauCeti.Almost.BasicSetup.IsAlmostZero.exactAt_extendScalars`: a complex of `V`-modules whose
  homology at degree `i` is almost zero becomes exact at `i` after inverting `ϖ`.
* `TauCeti.Almost.Algebra.subsingleton_invert_obj_iff`,
  `TauCeti.Almost.Algebra.subsingleton_invert_toAlmost_obj_iff`, and
  `TauCeti.Almost.Algebra.invertObjEquivElementsOfIsUnit`: characterizations of vanishing and
  unit inversion for `Almost.Algebra.invert`.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §5.2, proof of
  Corollary 5.2.15.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Exercise 4.1.9.
* P. Scholze, J. Weinstein, *Berkeley lectures on p-adic geometry*, Lecture 8, proof of
  Proposition 8.2.8.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory TensorProduct
open scoped ChangeOfRings MonObj

namespace TauCeti.Almost

namespace BasicSetup

variable {V : Type*} [CommRing V] {S : BasicSetup V} {ϖ : V}

/-- Localizing an almost zero `V`-module at the powers of `ϖ ∈ m` produces the zero module. -/
theorem IsAlmostZero.subsingleton_of_isLocalizedModule {M M' : Type*} [AddCommGroup M]
    [_root_.Module V M] [AddCommMonoid M'] [_root_.Module V M'] (hM : S.IsAlmostZero M)
    (hϖ : ϖ ∈ S.ideal) (g : M →ₗ[V] M') [IsLocalizedModule (Submonoid.powers ϖ) g] :
    Subsingleton M' :=
  (IsLocalizedModule.subsingleton_iff (Submonoid.powers ϖ) g).mpr fun x ↦
    ⟨ϖ, Submonoid.mem_powers ϖ, hM.smul_eq_zero hϖ x⟩

/-- For `ϖ ∈ m`, `LocalizedModule (Submonoid.powers ϖ) M` is trivial whenever `M` is almost
zero. -/
theorem IsAlmostZero.subsingleton_localizedModule {M : Type*} [AddCommGroup M] [_root_.Module V M]
    (hM : S.IsAlmostZero M) (hϖ : ϖ ∈ S.ideal) :
    Subsingleton (LocalizedModule (Submonoid.powers ϖ) M) :=
  hM.subsingleton_of_isLocalizedModule hϖ (LocalizedModule.mkLinearMap (Submonoid.powers ϖ) M)

/-- Base-changing an almost zero `V`-module to a localization `W` of `V` away from `ϖ ∈ m` gives a
zero module. -/
theorem IsAlmostZero.subsingleton_tensorProduct {M : Type*} [AddCommGroup M] [_root_.Module V M]
    (hM : S.IsAlmostZero M) (hϖ : ϖ ∈ S.ideal) (W : Type*) [CommRing W] [_root_.Algebra V W]
    [IsLocalization.Away ϖ W] : Subsingleton (W ⊗[V] M) :=
  hM.subsingleton_of_isLocalizedModule hϖ (TensorProduct.mk V W M 1)

/-- Localizing at `ϖ ∈ m` makes a linear map with almost zero kernel injective. -/
theorem IsAlmostZero.injective_localizedModule_map {M N : Type*} [AddCommGroup M]
    [_root_.Module V M] [AddCommGroup N] [_root_.Module V N] {f : M →ₗ[V] N}
    (h : S.IsAlmostZero (LinearMap.ker f)) (hϖ : ϖ ∈ S.ideal) :
    Function.Injective (LocalizedModule.map (Submonoid.powers ϖ) f) :=
  (LinearMap.localizedMap_injective_iff_subsingleton_localized_ker (Submonoid.powers ϖ) f).mpr
    (h.subsingleton_localizedModule hϖ)

/-- Localizing at `ϖ ∈ m` makes a linear map with almost zero cokernel surjective. -/
theorem IsAlmostZero.surjective_localizedModule_map {M N : Type*} [AddCommGroup M]
    [_root_.Module V M] [AddCommGroup N] [_root_.Module V N] {f : M →ₗ[V] N}
    (h : S.IsAlmostZero (N ⧸ LinearMap.range f)) (hϖ : ϖ ∈ S.ideal) :
    Function.Surjective (LocalizedModule.map (Submonoid.powers ϖ) f) :=
  (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker (Submonoid.powers ϖ) f).mpr
    (h.subsingleton_localizedModule hϖ)

/-- Localizing at the powers of `ϖ ∈ m` turns an almost isomorphism into a bijection. -/
theorem IsAlmostIso.bijective_localizedModule_map {M N : Type*} [AddCommGroup M]
    [_root_.Module V M] [AddCommGroup N] [_root_.Module V N] {f : M →ₗ[V] N}
    (hf : S.IsAlmostIso f) (hϖ : ϖ ∈ S.ideal) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers ϖ) f) := by
  rcases S.isAlmostIso_iff.mp hf with ⟨hker, hcoker⟩
  exact ⟨hker.injective_localizedModule_map hϖ, hcoker.surjective_localizedModule_map hϖ⟩

/-- Any module localization at the powers of `ϖ ∈ m` turns an almost isomorphism into a
bijection. -/
theorem IsAlmostIso.bijective_isLocalizedModule_map {M N M' N' : Type*} [AddCommGroup M]
    [_root_.Module V M] [AddCommGroup N] [_root_.Module V N] [AddCommGroup M'] [_root_.Module V M']
    [AddCommGroup N'] [_root_.Module V N'] {f : M →ₗ[V] N} (hf : S.IsAlmostIso f)
    (hϖ : ϖ ∈ S.ideal) (g₁ : M →ₗ[V] M') (g₂ : N →ₗ[V] N')
    [IsLocalizedModule (Submonoid.powers ϖ) g₁] [IsLocalizedModule (Submonoid.powers ϖ) g₂] :
    Function.Bijective (IsLocalizedModule.map (Submonoid.powers ϖ) g₁ g₂ f) :=
  (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective g₁ g₂).mpr
    (hf.bijective_localizedModule_map hϖ)

/-- Base-changing along a localization `W` of `V` away from `ϖ ∈ m` turns an almost isomorphism
into a bijection. -/
theorem IsAlmostIso.bijective_lTensor {M N : Type*} [AddCommGroup M] [_root_.Module V M]
    [AddCommGroup N] [_root_.Module V N] {f : M →ₗ[V] N} (hf : S.IsAlmostIso f)
    (hϖ : ϖ ∈ S.ideal) (W : Type*) [CommRing W] [_root_.Algebra V W] [IsLocalization.Away ϖ W] :
    Function.Bijective (f.lTensor W) := by
  have hmap : f.lTensor W = IsLocalizedModule.map (Submonoid.powers ϖ)
      (TensorProduct.mk V W M 1) (TensorProduct.mk V W N 1) f := by
    refine IsLocalizedModule.ext (Submonoid.powers ϖ) (TensorProduct.mk V W M 1)
      (IsLocalizedModule.map_units (TensorProduct.mk V W N 1)) ?_
    ext x
    exact (IsLocalizedModule.map_apply (Submonoid.powers ϖ) (TensorProduct.mk V W M 1)
      (TensorProduct.mk V W N 1) f x).symm
  rw [hmap]
  exact hf.bijective_isLocalizedModule_map hϖ _ _

end BasicSetup

/-! ### The exact functor `Almost.invert` -/

section InvertFunctor

variable {V : Type u} [CommRing V]

/-- `ModuleCat.localizedModuleFunctor` kills almost zero `V`-modules when localizing at `ϖ ∈ m`. -/
private theorem isZero_localizedModuleFunctor_obj (S : BasicSetup V) {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (M : ModuleCat.{u} V) (hM : S.IsAlmostZero M) :
    IsZero ((ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).obj M) := by
  have : Subsingleton (LocalizedModule (Submonoid.powers ϖ) M) :=
    hM.subsingleton_localizedModule hϖ
  have : Subsingleton (Shrink.{u} (LocalizedModule (Submonoid.powers ϖ) M)) :=
    (equivShrink _).symm.subsingleton
  rw [ModuleCat.localizedModuleFunctor_obj, ModuleCat.localizedModule]
  exact ModuleCat.isZero_of_subsingleton _

/-- **Inverting an element `ϖ ∈ m` on almost modules**: the exact functor
`Almost.Module S ⥤ ModuleCat (Localization.Away ϖ)` obtained by factoring module localization at
the powers of `ϖ` through almostification (Gabber–Ramero, §5.2, Corollary 5.2.15; Bhatt,
Exercise 4.1.9). -/
noncomputable def invert (S : BasicSetup V) {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    Module S ⥤ ModuleCat.{u} (Localization.Away ϖ) :=
  Module.lift S (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ))
    (isZero_localizedModuleFunctor_obj S hϖ)

variable (S : BasicSetup V) {ϖ : V} (hϖ : ϖ ∈ S.ideal)

/-- Composing almostification with `invert S hϖ` recovers `ModuleCat.localizedModuleFunctor` at the
powers of `ϖ`. -/
noncomputable def toAlmostCompInvertIso :
    Module.toAlmost S ⋙ invert S hϖ ≅
      ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ) :=
  Module.fac S (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ))
    (isZero_localizedModuleFunctor_obj S hϖ)

/-- `invert S hϖ` is a localization lifting of `ModuleCat.localizedModuleFunctor` along
almostification. -/
noncomputable instance :
    Localization.Lifting (Module.toAlmost S) S.almostZero.isoModSerre
      (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)) (invert S hϖ) :=
  ⟨toAlmostCompInvertIso S hϖ⟩

/-- `invert S hϖ` preserves finite limits. -/
instance : PreservesFiniteLimits (invert S hϖ) :=
  inferInstanceAs (PreservesFiniteLimits (Module.lift S _ _))

/-- `invert S hϖ` preserves finite colimits. -/
instance : PreservesFiniteColimits (invert S hϖ) :=
  inferInstanceAs (PreservesFiniteColimits (Module.lift S _ _))

/-- `invert S hϖ` is an additive functor. -/
instance : (invert S hϖ).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Uniqueness of `invert S hϖ`: any functor `G : Module S ⥤ ModuleCat (Localization.Away ϖ)`
whose composition with `toAlmost S` is isomorphic to `ModuleCat.localizedModuleFunctor` at the
powers of `ϖ` is canonically isomorphic to `invert S hϖ`. -/
noncomputable def invertUniq (G : Module S ⥤ ModuleCat.{u} (Localization.Away ϖ))
    (e : Module.toAlmost S ⋙ G ≅ ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)) :
    G ≅ invert S hϖ :=
  Module.liftUniq S (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ))
    (isZero_localizedModuleFunctor_obj S hϖ) G e

/-- Removing `Shrink.{u}` from `(ModuleCat.localizedModuleFunctor.{u} p).obj N` when `V` and `N`
live in universe `u`. -/
private noncomputable def localizedModuleObjIso {p : Submonoid V} (N : ModuleCat.{u} V) :
    (ModuleCat.localizedModuleFunctor.{u} p).obj N ≅
      ModuleCat.of (Localization p) (LocalizedModule p N) :=
  (Shrink.linearEquiv.{u} (Localization p) (LocalizedModule p N)).toModuleIso

private theorem localizedModuleObjIso_hom_mkLinearMap {p : Submonoid V} (N : ModuleCat.{u} V)
    (x : N) :
    (localizedModuleObjIso N).hom (N.localizedModuleMkLinearMap p x) =
      LocalizedModule.mk x 1 := by
  -- Both `Shrink.linearEquiv` maps come from the same underlying `equivShrink`.
  change Shrink.linearEquiv.{u} (Localization p) (LocalizedModule p N)
    ((Shrink.linearEquiv.{u} V (LocalizedModule p N)).symm (LocalizedModule.mk x 1)) = _
  simp

private theorem localizedModuleObjIso_naturality {p : Submonoid V} {N₁ N₂ : ModuleCat.{u} V}
    (f : N₁ ⟶ N₂) :
    (ModuleCat.localizedModuleFunctor.{u} p).map f ≫ (localizedModuleObjIso N₂).hom =
      (localizedModuleObjIso N₁).hom ≫ ModuleCat.ofHom (LocalizedModule.map p f.hom) := by
  rw [ModuleCat.localizedModuleFunctor_map]
  -- Express the domain as `N₁.localizedModule p` so `Module V` and `IsScalarTower V` are found.
  change ModuleCat.localizedModuleMap p f ≫ (localizedModuleObjIso N₂).hom =
    (localizedModuleObjIso N₁).hom ≫ ModuleCat.ofHom (LocalizedModule.map p f.hom)
  apply ModuleCat.hom_ext
  apply LinearMap.restrictScalars_injective V
  apply IsLocalizedModule.linearMap_ext p (N₁.localizedModuleMkLinearMap p)
    (LocalizedModule.mkLinearMap p N₂)
  ext x
  -- Evaluate both `ModuleCat` composites directly on `N₁.localizedModuleMkLinearMap p x`.
  change (localizedModuleObjIso N₂).hom
      ((IsLocalizedModule.mapExtendScalars p (N₁.localizedModuleMkLinearMap p)
        (N₂.localizedModuleMkLinearMap p) (Localization p) f.hom)
        (N₁.localizedModuleMkLinearMap p x)) =
    LocalizedModule.map p f.hom
      ((localizedModuleObjIso N₁).hom (N₁.localizedModuleMkLinearMap p x))
  calc (localizedModuleObjIso N₂).hom
        ((IsLocalizedModule.mapExtendScalars p (N₁.localizedModuleMkLinearMap p)
          (N₂.localizedModuleMkLinearMap p) (Localization p) f.hom)
          (N₁.localizedModuleMkLinearMap p x))
      = (localizedModuleObjIso N₂).hom (N₂.localizedModuleMkLinearMap p (f.hom x)) :=
        congrArg (localizedModuleObjIso N₂).hom
          (IsLocalizedModule.map_apply p (N₁.localizedModuleMkLinearMap p)
            (N₂.localizedModuleMkLinearMap p) f.hom x)
    _ = LocalizedModule.mk (f.hom x) 1 :=
        localizedModuleObjIso_hom_mkLinearMap N₂ (f.hom x)
    _ = LocalizedModule.map p f.hom (LocalizedModule.mk x 1) :=
        (LocalizedModule.map_mk p f.hom x 1).symm
    _ = LocalizedModule.map p f.hom
          ((localizedModuleObjIso N₁).hom (N₁.localizedModuleMkLinearMap p x)) :=
        congrArg (LocalizedModule.map p f.hom)
          (localizedModuleObjIso_hom_mkLinearMap N₁ x).symm

/-- Extension of scalars to `Localization p` is naturally isomorphic to
`ModuleCat.localizedModuleFunctor p`. -/
private noncomputable def extendScalarsIsoLocalizedModuleFunctor (p : Submonoid V) :
    ModuleCat.extendScalars.{u, u, u} (algebraMap V (Localization p)) ≅
      ModuleCat.localizedModuleFunctor.{u} p :=
  NatIso.ofComponents
    (fun N ↦ N.extendScalarsLocalizationIso p ≪≫ (localizedModuleObjIso N).symm)
    fun {N₁ N₂} f ↦ by
      rw [← cancel_mono (localizedModuleObjIso N₂).hom]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        localizedModuleObjIso_naturality, Iso.inv_hom_id_assoc]
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      -- Express `1 ⊗ₜ x` with the `ChangeOfRings` tensor notation and evaluate both composites.
      change (N₂.extendScalarsLocalizationIso p).hom
          ((ModuleCat.extendScalars (algebraMap V (Localization p))).map f
            ((1 : Localization p) ⊗ₜ[V, algebraMap V (Localization p)] x)) =
        (ModuleCat.ofHom (LocalizedModule.map p f.hom))
          ((N₁.extendScalarsLocalizationIso p).hom
            ((1 : Localization p) ⊗ₜ[V, algebraMap V (Localization p)] x))
      calc (N₂.extendScalarsLocalizationIso p).hom
            ((ModuleCat.extendScalars (algebraMap V (Localization p))).map f
              ((1 : Localization p) ⊗ₜ[V, algebraMap V (Localization p)] x))
          = (N₂.extendScalarsLocalizationIso p).hom
              ((1 : Localization p) ⊗ₜ[V, algebraMap V (Localization p)] f x) :=
            congrArg (N₂.extendScalarsLocalizationIso p).hom
              (ModuleCat.ExtendScalars.map_tmul (algebraMap V (Localization p)) f 1 x)
        _ = LocalizedModule.mk (f x) 1 :=
            N₂.extendScalarsLocalizationIso_hom_one_tmul p (f x)
        _ = (ModuleCat.ofHom (LocalizedModule.map p f.hom)) (LocalizedModule.mk x 1) :=
            (LocalizedModule.map_mk p f.hom x 1).symm
        _ = (ModuleCat.ofHom (LocalizedModule.map p f.hom))
              ((N₁.extendScalarsLocalizationIso p).hom
                ((1 : Localization p) ⊗ₜ[V, algebraMap V (Localization p)] x)) :=
            congrArg (ModuleCat.ofHom (LocalizedModule.map p f.hom))
              (N₁.extendScalarsLocalizationIso_hom_one_tmul p x).symm

/-- `ModuleCat.localizedModuleFunctor` is naturally isomorphic to extension of scalars to the
localized ring. -/
private noncomputable def localizedModuleFunctorIsoExtendScalars (p : Submonoid V) :
    ModuleCat.localizedModuleFunctor.{u} p ≅
      ModuleCat.extendScalars.{u, u, u} (algebraMap V (Localization p)) :=
  (extendScalarsIsoLocalizedModuleFunctor p).symm

/-- Composing almostification with `invert S hϖ` is naturally isomorphic to extension of scalars
`M ↦ Localization.Away ϖ ⊗[V] M`. -/
noncomputable def toAlmostCompInvertIsoExtendScalars :
    Module.toAlmost S ⋙ invert S hϖ ≅
      ModuleCat.extendScalars.{u, u, u} (algebraMap V (Localization.Away ϖ)) :=
  toAlmostCompInvertIso S hϖ ≪≫ localizedModuleFunctorIsoExtendScalars (Submonoid.powers ϖ)

/-- Evaluating `invert S hϖ` on an almostification `N^a` recovers
`LocalizedModule (Submonoid.powers ϖ) N`. -/
noncomputable def invertToAlmostObjIso (N : ModuleCat.{u} V) :
    (invert S hϖ).obj ((Module.toAlmost S).obj N) ≅
      ModuleCat.of (Localization.Away ϖ) (LocalizedModule (Submonoid.powers ϖ) N) :=
  (toAlmostCompInvertIso S hϖ).app N ≪≫ localizedModuleObjIso N

/-- Naturality of `invertToAlmostObjIso`: `(invert S hϖ).map (f^a)` acts as
`LocalizedModule.map` on `LocalizedModule (Submonoid.powers ϖ)`. -/
@[reassoc]
theorem invert_map_toAlmost_comp_invertToAlmostObjIso_hom {N₁ N₂ : ModuleCat.{u} V}
    (f : N₁ ⟶ N₂) :
    (invert S hϖ).map ((Module.toAlmost S).map f) ≫ (invertToAlmostObjIso S hϖ N₂).hom =
      (invertToAlmostObjIso S hϖ N₁).hom ≫
        ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers ϖ) f.hom) := by
  simp only [invertToAlmostObjIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, ← Functor.comp_map (Module.toAlmost S) (invert S hϖ),
    (toAlmostCompInvertIso S hϖ).hom.naturality, Category.assoc, localizedModuleObjIso_naturality,
    Category.assoc]

/-- Inverting `ϖ ∈ m` sends `V^a` to the free rank-one module `Localization.Away ϖ`. -/
noncomputable def invertToAlmostRingIso :
    (invert S hϖ).obj ((Module.toAlmost S).obj (ModuleCat.of V V)) ≅
      ModuleCat.of (Localization.Away ϖ) (Localization.Away ϖ) :=
  invertToAlmostObjIso S hϖ (ModuleCat.of V V) ≪≫
    (LocalizedModule.equivLocalization (Submonoid.powers ϖ)).toModuleIso

/-- **Evaluating `invert S hϖ` through almost elements**: `(invert S hϖ).obj M` is canonically
isomorphic to `LocalizedModule (Submonoid.powers ϖ) ((Module.elements S).obj M)`. -/
noncomputable def invertElementsIso (M : Module S) :
    (invert S hϖ).obj M ≅
      ModuleCat.of (Localization.Away ϖ)
        (LocalizedModule (Submonoid.powers ϖ) ((Module.elements S).obj M)) :=
  (invert S hϖ).mapIso (asIso ((Module.adjElements S).counit.app M)).symm ≪≫
    invertToAlmostObjIso S hϖ ((Module.elements S).obj M)

/-- Naturality of `invertElementsIso`: `(invert S hϖ).map f` corresponds to localizing
`(Module.elements S).map f` at the powers of `ϖ`. -/
@[reassoc]
theorem invert_map_comp_invertElementsIso_hom {M₁ M₂ : Module S} (f : M₁ ⟶ M₂) :
    (invert S hϖ).map f ≫ (invertElementsIso S hϖ M₂).hom =
      (invertElementsIso S hϖ M₁).hom ≫
        ModuleCat.ofHom
          (LocalizedModule.map (Submonoid.powers ϖ) ((Module.elements S).map f).hom) := by
  simp only [invertElementsIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_inv]
  have hnat : f ≫ inv ((Module.adjElements S).counit.app M₂) =
      inv ((Module.adjElements S).counit.app M₁) ≫
        (Module.toAlmost S).map ((Module.elements S).map f) := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact ((Module.adjElements S).counit_naturality f).symm
  rw [← Category.assoc, ← Functor.map_comp, hnat, Functor.map_comp, Category.assoc,
    invert_map_toAlmost_comp_invertToAlmostObjIso_hom, Category.assoc]

/-- **Evaluating `invert S hϖ` through `M_!`**: `(invert S hϖ).obj M` is canonically isomorphic to
`LocalizedModule (Submonoid.powers ϖ) ((Module.shriek S).obj M)`. -/
noncomputable def invertShriekIso (M : Module S) :
    (invert S hϖ).obj M ≅
      ModuleCat.of (Localization.Away ϖ)
        (LocalizedModule (Submonoid.powers ϖ) ((Module.shriek S).obj M)) :=
  (invert S hϖ).mapIso (asIso ((Module.adjShriek S).unit.app M)) ≪≫
    invertToAlmostObjIso S hϖ ((Module.shriek S).obj M)

/-- Naturality of `invertShriekIso`: `(invert S hϖ).map f` corresponds to localizing
`(Module.shriek S).map f` at the powers of `ϖ`. -/
@[reassoc]
theorem invert_map_comp_invertShriekIso_hom {M₁ M₂ : Module S} (f : M₁ ⟶ M₂) :
    (invert S hϖ).map f ≫ (invertShriekIso S hϖ M₂).hom =
      (invertShriekIso S hϖ M₁).hom ≫
        ModuleCat.ofHom
          (LocalizedModule.map (Submonoid.powers ϖ) ((Module.shriek S).map f).hom) := by
  simp only [invertShriekIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, ← (Module.adjShriek S).unit_naturality f,
    Functor.map_comp, Category.assoc, invert_map_toAlmost_comp_invertToAlmostObjIso_hom,
    Category.assoc]

/-- `(invert S hϖ).obj (N^a)` is zero iff every element of `N` is annihilated by a power of `ϖ`. -/
theorem isZero_invert_toAlmost_obj_iff (N : ModuleCat.{u} V) :
    IsZero ((invert S hϖ).obj ((Module.toAlmost S).obj N)) ↔
      ∀ x : N, ∃ n : ℕ, (ϖ ^ n) • x = 0 := by
  rw [(invertToAlmostObjIso S hϖ N).isZero_iff, ModuleCat.isZero_of_iff_subsingleton,
    LocalizedModule.subsingleton_iff]
  simp [Submonoid.mem_powers_iff]

/-- `(invert S hϖ).obj M` is zero iff every almost element of `M` is annihilated by a power of
`ϖ`. -/
theorem isZero_invert_obj_iff (M : Module S) :
    IsZero ((invert S hϖ).obj M) ↔
      ∀ x : (Module.elements S).obj M, ∃ n : ℕ, (ϖ ^ n) • x = 0 := by
  rw [(invertElementsIso S hϖ M).isZero_iff, ModuleCat.isZero_of_iff_subsingleton,
    LocalizedModule.subsingleton_iff]
  simp [Submonoid.mem_powers_iff]

/-- Inverting `0 ∈ m` sends every almost module to zero, since `V[1/0] = 0`. -/
theorem isZero_invert_zero_obj (h0 : (0 : V) ∈ S.ideal) (M : Module S) :
    IsZero ((invert S h0).obj M) :=
  (isZero_invert_obj_iff S h0 M).mpr fun _ ↦ ⟨1, by simp⟩

/-- After base-changing `S` to a localization `W` away from `ϖ ∈ m`, the setup becomes classical,
so almostification `ModuleCat W ⥤ Module (S.baseChange W)` is an equivalence of categories. -/
theorem Module.isEquivalence_toAlmost_baseChange_away (W : Type u) [CommRing W]
    [_root_.Algebra V W] [IsLocalization.Away ϖ W] (hϖ : ϖ ∈ S.ideal) :
    (Module.toAlmost (S.baseChange W)).IsEquivalence := by
  rw [S.baseChange_away_eq_classical W hϖ]
  infer_instance

/-- Base-changing `S` to a localization `W` away from `ϖ ∈ m` identifies almost `W`-modules with
honest `W`-modules via `Module.toAlmost (S.baseChange W)`. -/
noncomputable def Module.baseChangeAwayEquiv (W : Type u) [CommRing W] [_root_.Algebra V W]
    [IsLocalization.Away ϖ W] (hϖ : ϖ ∈ S.ideal) :
    ModuleCat.{u} W ≌ Module (S.baseChange W) :=
  have := Module.isEquivalence_toAlmost_baseChange_away S W hϖ
  (Module.toAlmost (S.baseChange W)).asEquivalence

section IsUnit

/-- When `ϖ ∈ m` is a unit of `V` (so `S` is classical and `V ≃+* V[1/ϖ]`), `invert S hϖ`
followed by restriction of scalars along `V → V[1/ϖ]` is naturally isomorphic to
`Almost.Module.elements S`. -/
noncomputable def invertCompRestrictScalarsIsoElements (hu : IsUnit ϖ) :
    invert S hϖ ⋙ ModuleCat.restrictScalars (algebraMap V (Localization.Away ϖ)) ≅
      Module.elements S := by
  have hS : S = BasicSetup.classical V := by
    ext1; simp [Ideal.eq_top_of_isUnit_mem S.ideal hϖ hu]
  have : (Module.toAlmost S).IsEquivalence := by rw [hS]; infer_instance
  let Q := (Module.toAlmost S).asEquivalence
  let eElem : Module.elements S ≅ Q.inverse :=
    (Module.adjElements S).rightAdjointUniq Q.toAdjunction
  let eRing : V ≃+* Localization.Away ϖ :=
    (IsLocalization.atUnits V (Submonoid.powers ϖ) (Submonoid.powers_le.mpr hu)).toRingEquiv
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv eRing
  let eExt : ModuleCat.extendScalars.{u, u, u} (algebraMap V (Localization.Away ϖ)) ≅ E.inverse :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap V (Localization.Away ϖ))).leftAdjointUniq
      E.symm.toAdjunction
  let F := invert S hϖ ⋙ ModuleCat.restrictScalars (algebraMap V (Localization.Away ϖ))
  let eComp : Q.functor ⋙ F ≅ 𝟭 (ModuleCat.{u} V) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (toAlmostCompInvertIsoExtendScalars S hϖ ≪≫ eExt) E.functor ≪≫
      E.counitIso
  exact (Functor.leftUnitor F).symm ≪≫
    Functor.isoWhiskerRight Q.counitIso.symm F ≪≫
    Functor.associator Q.inverse Q.functor F ≪≫
    Functor.isoWhiskerLeft Q.inverse eComp ≪≫
    Functor.rightUnitor Q.inverse ≪≫
    eElem.symm

/-- When `ϖ ∈ m` is a unit of `V`, `invert S hϖ` is an equivalence of categories. -/
theorem isEquivalence_invert_of_isUnit (hu : IsUnit ϖ) : (invert S hϖ).IsEquivalence := by
  have hS : S = BasicSetup.classical V := by
    ext1; simp [Ideal.eq_top_of_isUnit_mem S.ideal hϖ hu]
  have : (Module.toAlmost S).IsEquivalence := by rw [hS]; infer_instance
  have : (Module.elements S).IsEquivalence :=
    Functor.isEquivalence_of_iso
      ((Module.adjElements S).rightAdjointUniq (Module.toAlmost S).asEquivalence.toAdjunction).symm
  let eRing : V ≃+* Localization.Away ϖ :=
    (IsLocalization.atUnits V (Submonoid.powers ϖ) (Submonoid.powers_le.mpr hu)).toRingEquiv
  have : (ModuleCat.restrictScalars (algebraMap V (Localization.Away ϖ))).IsEquivalence :=
    inferInstanceAs (ModuleCat.restrictScalars eRing.toRingHom).IsEquivalence
  have : (invert S hϖ ⋙
      ModuleCat.restrictScalars (algebraMap V (Localization.Away ϖ))).IsEquivalence :=
    Functor.isEquivalence_of_iso (invertCompRestrictScalarsIsoElements S hϖ hu).symm
  exact Functor.isEquivalence_of_comp_right (invert S hϖ)
    (ModuleCat.restrictScalars (algebraMap V (Localization.Away ϖ)))

end IsUnit

end InvertFunctor

/-! ### The symmetric monoidal structure on `Almost.invert` -/

private noncomputable instance extendScalarsBraided {V W : Type u} [CommRing V] [CommRing W]
    (f : V →+* W) : (ModuleCat.extendScalars.{u, u, u} f).Braided :=
  (ModuleCat.extendRestrictScalarsAdj f).leftAdjointBraided

section Monoidal

variable {V : Type u} [CommRing V] (S : BasicSetup V) {ϖ : V} (hϖ : ϖ ∈ S.ideal)

/-- `invert S hϖ` is a localization lifting of extension of scalars along almostification. -/
noncomputable instance :
    Localization.Lifting (Module.toAlmost S) S.almostZero.isoModSerre
      (ModuleCat.extendScalars.{u, u, u} (algebraMap V (Localization.Away ϖ)))
      (invert S hϖ) :=
  ⟨toAlmostCompInvertIsoExtendScalars S hϖ⟩

/-- **Inverting `ϖ ∈ m` is a monoidal functor**: `invert S hϖ` inherits a strong monoidal
structure from extension of scalars `M ↦ Localization.Away ϖ ⊗[V] M` along almostification. -/
noncomputable instance invertMonoidal : (invert S hϖ).Monoidal :=
  Localization.Monoidal.functorMonoidalOfComp (Module.toAlmost S) S.almostZero.isoModSerre
    (invert S hϖ) (ModuleCat.extendScalars.{u, u, u} (algebraMap V (Localization.Away ϖ)))

/-- The comparison `toAlmost S ⋙ invert S hϖ ≅ extendScalars (algebraMap V (Localization.Away ϖ))`
is a monoidal natural isomorphism. -/
instance isMonoidal_toAlmostCompInvertIsoExtendScalars_hom :
    (toAlmostCompInvertIsoExtendScalars S hϖ).hom.IsMonoidal :=
  Localization.Monoidal.lifting_isMonoidal (Module.toAlmost S) S.almostZero.isoModSerre
    (invert S hϖ) (ModuleCat.extendScalars.{u, u, u} (algebraMap V (Localization.Away ϖ)))

/-- Braiding compatibility of `invert S hϖ` on objects in the image of `Module.toAlmost S`. -/
private theorem invert_braided_toAlmost_obj (X₀ Y₀ : ModuleCat.{u} V) :
    Functor.LaxMonoidal.μ (invert S hϖ) ((Module.toAlmost S).obj X₀)
        ((Module.toAlmost S).obj Y₀) ≫
      (invert S hϖ).map (β_ ((Module.toAlmost S).obj X₀) ((Module.toAlmost S).obj Y₀)).hom =
    (β_ ((invert S hϖ).obj ((Module.toAlmost S).obj X₀))
        ((invert S hϖ).obj ((Module.toAlmost S).obj Y₀))).hom ≫
      Functor.LaxMonoidal.μ (invert S hϖ) ((Module.toAlmost S).obj Y₀)
        ((Module.toAlmost S).obj X₀) := by
  let F := invert S hϖ
  let Q := Module.toAlmost S
  let G := ModuleCat.extendScalars.{u, u, u} (algebraMap V (Localization.Away ϖ))
  let α := toAlmostCompInvertIsoExtendScalars S hϖ
  let X := Q.obj X₀
  let Y := Q.obj Y₀
  have hμ (A₀ B₀ : ModuleCat.{u} V) :
      Functor.LaxMonoidal.μ F (Q.obj A₀) (Q.obj B₀) ≫
        F.map (Functor.LaxMonoidal.μ Q A₀ B₀) ≫ α.hom.app (A₀ ⊗ B₀) =
      (α.hom.app A₀ ⊗ₘ α.hom.app B₀) ≫ Functor.LaxMonoidal.μ G A₀ B₀ := by
    simpa only [Functor.comp_obj, Functor.LaxMonoidal.comp_μ, Category.assoc] using
      NatTrans.IsMonoidal.tensor (τ := α.hom) A₀ B₀
  rw [← cancel_mono (F.map (Functor.LaxMonoidal.μ Q Y₀ X₀)), ← cancel_mono (α.hom.app (Y₀ ⊗ X₀))]
  simp only [Category.assoc]
  calc Functor.LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom ≫
        F.map (Functor.LaxMonoidal.μ Q Y₀ X₀) ≫ α.hom.app (Y₀ ⊗ X₀)
      = Functor.LaxMonoidal.μ F X Y ≫ F.map (Functor.LaxMonoidal.μ Q X₀ Y₀) ≫
          ((Q ⋙ F).map (β_ X₀ Y₀).hom ≫ α.hom.app (Y₀ ⊗ X₀)) := by
        rw [← Functor.map_comp_assoc, ← Functor.LaxBraided.braided X₀ Y₀, Functor.map_comp,
          Functor.comp_map, Category.assoc]
    _ = (Functor.LaxMonoidal.μ F X Y ≫ F.map (Functor.LaxMonoidal.μ Q X₀ Y₀) ≫
          α.hom.app (X₀ ⊗ Y₀)) ≫ G.map (β_ X₀ Y₀).hom := by
        rw [α.hom.naturality (β_ X₀ Y₀).hom, Category.assoc, Category.assoc]
    _ = (α.hom.app X₀ ⊗ₘ α.hom.app Y₀) ≫
          (Functor.LaxMonoidal.μ G X₀ Y₀ ≫ G.map (β_ X₀ Y₀).hom) := by
        rw [hμ X₀ Y₀, Category.assoc]
    _ = ((α.hom.app X₀ ⊗ₘ α.hom.app Y₀) ≫ (β_ (G.obj X₀) (G.obj Y₀)).hom) ≫
          Functor.LaxMonoidal.μ G Y₀ X₀ := by
        rw [Functor.LaxBraided.braided X₀ Y₀, Category.assoc]
    _ = (β_ (F.obj X) (F.obj Y)).hom ≫
          ((α.hom.app Y₀ ⊗ₘ α.hom.app X₀) ≫ Functor.LaxMonoidal.μ G Y₀ X₀) := by
        rw [BraidedCategory.braiding_naturality, Category.assoc]; rfl
    _ = (β_ (F.obj X) (F.obj Y)).hom ≫ Functor.LaxMonoidal.μ F Y X ≫
          F.map (Functor.LaxMonoidal.μ Q Y₀ X₀) ≫ α.hom.app (Y₀ ⊗ X₀) := by
        rw [← hμ Y₀ X₀]

/-- **Inverting `ϖ ∈ m` is a braided (symmetric) monoidal functor.** -/
noncomputable instance invertBraided : (invert S hϖ).Braided where
  braided X Y := by
    let eX := (Module.toAlmost S).objObjPreimageIso X
    let eY := (Module.toAlmost S).objObjPreimageIso Y
    rw [← cancel_epi ((invert S hϖ).map eX.hom ⊗ₘ (invert S hϖ).map eY.hom),
      Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp,
      BraidedCategory.braiding_naturality, Functor.map_comp,
      BraidedCategory.braiding_naturality_assoc, Functor.LaxMonoidal.μ_natural,
      ← Category.assoc, ← Category.assoc, invert_braided_toAlmost_obj]

end Monoidal

/-! ### Exactness of complexes after inverting `ϖ` -/

section Complexes

variable {V : Type u} [CommRing V]
variable {I : Type*} {c : ComplexShape I}

/-- A complex `K` of `V`-modules becomes exact at degree `i` after almostification iff its
homology `K.homology i` is almost zero. -/
theorem Module.exactAt_mapHomologicalComplex_toAlmost_iff (S : BasicSetup V)
    (K : HomologicalComplex (ModuleCat.{u} V) c) (i : I) :
    (((Module.toAlmost S).mapHomologicalComplex c).obj K).ExactAt i ↔
      S.IsAlmostZero (K.homology i) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (((K.sc i).mapHomologyIso (Module.toAlmost S))).isZero_iff.trans
    (Module.isZero_toAlmost_obj_iff S _)

/-- A complex `K` of `V`-modules becomes acyclic after almostification iff all of its homology
modules are almost zero. -/
theorem Module.acyclic_mapHomologicalComplex_toAlmost_iff (S : BasicSetup V)
    (K : HomologicalComplex (ModuleCat.{u} V) c) :
    (((Module.toAlmost S).mapHomologicalComplex c).obj K).Acyclic ↔
      ∀ i : I, S.IsAlmostZero (K.homology i) := by
  simp_rw [HomologicalComplex.acyclic_iff, Module.exactAt_mapHomologicalComplex_toAlmost_iff]

/-- `invert S hϖ` preserves exactness of complexes of almost modules at each degree. -/
theorem exactAt_mapHomologicalComplex_invert (S : BasicSetup V) {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (C : HomologicalComplex (Module S) c) {i : I} (hC : C.ExactAt i) :
    (((invert S hϖ).mapHomologicalComplex c).obj C).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff] at hC ⊢
  exact hC.map (invert S hϖ)

/-- `invert S hϖ` sends acyclic complexes of almost modules to acyclic complexes of
`V[1/ϖ]`-modules. -/
theorem acyclic_mapHomologicalComplex_invert (S : BasicSetup V) {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (C : HomologicalComplex (Module S) c) (hC : C.Acyclic) :
    (((invert S hϖ).mapHomologicalComplex c).obj C).Acyclic :=
  fun i ↦ exactAt_mapHomologicalComplex_invert S hϖ C (hC i)

/-- **A complex of `V`-modules with almost zero homology at degree `i` becomes exact at `i` after
inverting `ϖ ∈ m`** via `ModuleCat.localizedModuleFunctor`. -/
theorem BasicSetup.IsAlmostZero.exactAt_localizedModuleFunctor {S : BasicSetup V} {ϖ : V}
    {K : HomologicalComplex (ModuleCat.{u} V) c} {i : I} (hK : S.IsAlmostZero (K.homology i))
    (hϖ : ϖ ∈ S.ideal) :
    (((ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).mapHomologicalComplex c).obj
      K).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (((K.sc i).mapHomologyIso
    (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)))).isZero_iff.mpr
      (isZero_localizedModuleFunctor_obj S hϖ (K.homology i) hK)

/-- A complex of `V`-modules whose homology is almost zero in every degree becomes acyclic after
inverting `ϖ ∈ m`. -/
theorem BasicSetup.IsAlmostZero.acyclic_localizedModuleFunctor {S : BasicSetup V} {ϖ : V}
    {K : HomologicalComplex (ModuleCat.{u} V) c} (hK : ∀ i : I, S.IsAlmostZero (K.homology i))
    (hϖ : ϖ ∈ S.ideal) :
    (((ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers ϖ)).mapHomologicalComplex c).obj
      K).Acyclic :=
  fun i ↦ (hK i).exactAt_localizedModuleFunctor hϖ

/-- **A complex of `V`-modules with almost zero homology at degree `i` becomes exact at `i` after
base-changing to `Localization.Away ϖ`** for `ϖ ∈ m`. -/
theorem BasicSetup.IsAlmostZero.exactAt_extendScalars {S : BasicSetup V} {ϖ : V}
    {K : HomologicalComplex (ModuleCat.{u} V) c} {i : I} (hK : S.IsAlmostZero (K.homology i))
    (hϖ : ϖ ∈ S.ideal) :
    (((ModuleCat.extendScalars.{u, u, u}
      (algebraMap V (Localization.Away ϖ))).mapHomologicalComplex c).obj K).ExactAt i :=
  (hK.exactAt_localizedModuleFunctor hϖ).of_iso
    ((NatIso.mapHomologicalComplex
      (localizedModuleFunctorIsoExtendScalars (Submonoid.powers ϖ)) c).app K)

/-- A complex of `V`-modules whose homology is almost zero in every degree becomes acyclic after
base-changing to `Localization.Away ϖ` for `ϖ ∈ m`. -/
theorem BasicSetup.IsAlmostZero.acyclic_extendScalars {S : BasicSetup V} {ϖ : V}
    {K : HomologicalComplex (ModuleCat.{u} V) c} (hK : ∀ i : I, S.IsAlmostZero (K.homology i))
    (hϖ : ϖ ∈ S.ideal) :
    (((ModuleCat.extendScalars.{u, u, u}
      (algebraMap V (Localization.Away ϖ))).mapHomologicalComplex c).obj K).Acyclic :=
  fun i ↦ (hK i).exactAt_extendScalars hϖ

end Complexes

/-! ### Inverting scalars on almost algebras -/

namespace Algebra

open scoped ModuleCat.MonModuleEquivalenceAlgebra

attribute [local instance] ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toCommRing

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-- **Inverting a scalar `ϖ : V` on almost algebras**: sends an almost algebra `A` to `A_*[1/ϖ]`,
the localization of its algebra of almost elements at the powers of `ϖ`, viewed as a commutative
`Localization.Away ϖ`-algebra. On canonical numerators its action on morphisms is induced by
`(Algebra.elements S).map` (`invert_map_algebraMap`). When `ϖ ∈ S.ideal`, it agrees with the
functor induced on commutative monoid objects by `Almost.invert S hϖ`
(`invertIsoMapCommMon`). -/
noncomputable def invert (ϖ : V) : Algebra S ⥤ CommAlgCat.{u} (Localization.Away ϖ) where
  obj A :=
    CommAlgCat.of (Localization.Away ϖ)
      (Localization (_root_.Algebra.algebraMapSubmonoid ((elements S).obj A) (Submonoid.powers ϖ)))
  map {A B} f :=
    CommAlgCat.ofHom (IsLocalization.mapₐ (Submonoid.powers ϖ) (Localization.Away ϖ)
      (Localization (_root_.Algebra.algebraMapSubmonoid ((elements S).obj A) (Submonoid.powers ϖ)))
      (Localization (_root_.Algebra.algebraMapSubmonoid ((elements S).obj B) (Submonoid.powers ϖ)))
      ((elements S).map f).hom)
  map_id A := by
    ext z
    simp
  map_comp {A B C} f g := by
    ext z
    simp [Functor.map_comp, IsLocalization.map_map, AlgHom.comp_toRingHom]

/-- `(Algebra.invert S ϖ).obj A` is an algebra over `(Algebra.elements S).obj A` via the
localization map `A_* → A_*[1/ϖ]`. -/
noncomputable instance (ϖ : V) (A : Algebra S) :
    _root_.Algebra ((elements S).obj A) ((invert S ϖ).obj A) :=
  inferInstanceAs (_root_.Algebra ((elements S).obj A)
    (Localization (_root_.Algebra.algebraMapSubmonoid ((elements S).obj A) (Submonoid.powers ϖ))))

/-- `(Algebra.invert S ϖ).obj A` is a `V`-algebra. -/
noncomputable instance (ϖ : V) (A : Algebra S) :
    _root_.Algebra V ((invert S ϖ).obj A) :=
  inferInstanceAs (_root_.Algebra V
    (Localization (_root_.Algebra.algebraMapSubmonoid ((elements S).obj A) (Submonoid.powers ϖ))))

instance (ϖ : V) (A : Algebra S) :
    IsScalarTower V ((elements S).obj A) ((invert S ϖ).obj A) :=
  inferInstanceAs (IsScalarTower V ((elements S).obj A)
    (Localization (_root_.Algebra.algebraMapSubmonoid ((elements S).obj A) (Submonoid.powers ϖ))))

instance (ϖ : V) (A : Algebra S) :
    IsScalarTower V (Localization.Away ϖ) ((invert S ϖ).obj A) :=
  inferInstanceAs (IsScalarTower V (Localization.Away ϖ)
    (Localization (_root_.Algebra.algebraMapSubmonoid ((elements S).obj A) (Submonoid.powers ϖ))))

/-- `(Algebra.invert S ϖ).obj A` is a localization of `(Algebra.elements S).obj A` at the image of
the powers of `ϖ`. -/
instance isLocalization_invert_obj (ϖ : V) (A : Algebra S) :
    IsLocalization (_root_.Algebra.algebraMapSubmonoid ((elements S).obj A) (Submonoid.powers ϖ))
      ((invert S ϖ).obj A) :=
  inferInstanceAs (IsLocalization
    (_root_.Algebra.algebraMapSubmonoid ((elements S).obj A) (Submonoid.powers ϖ))
    (Localization (_root_.Algebra.algebraMapSubmonoid ((elements S).obj A) (Submonoid.powers ϖ))))

/-- `(Algebra.invert S ϖ).obj A` is a localization of `(Algebra.elements S).obj A` away from
`algebraMap V A_* ϖ`. -/
instance isLocalizationAway_invert_obj (ϖ : V) (A : Algebra S) :
    IsLocalization.Away (algebraMap V ((elements S).obj A) ϖ) ((invert S ϖ).obj A) := by
  -- Unfold `IsLocalization.Away` to rewrite `Submonoid.powers` via `algebraMapSubmonoid_powers`.
  change IsLocalization (Submonoid.powers (algebraMap V ((elements S).obj A) ϖ))
    ((invert S ϖ).obj A)
  rw [← _root_.Algebra.algebraMapSubmonoid_powers]
  infer_instance

/-- On canonical numerators from `A_*`, `(Algebra.invert S ϖ).map f` acts via
`(Algebra.elements S).map f`. -/
@[simp]
theorem invert_map_algebraMap (ϖ : V) {A B : Algebra S} (f : A ⟶ B) (x : (elements S).obj A) :
    (invert S ϖ).map f (algebraMap ((elements S).obj A) ((invert S ϖ).obj A) x) =
      algebraMap ((elements S).obj B) ((invert S ϖ).obj B) ((elements S).map f x) :=
  IsLocalization.map_eq (S := (invert S ϖ).obj A) (Q := (invert S ϖ).obj B)
    (_root_.Algebra.algebraMapSubmonoid_le_comap (Submonoid.powers ϖ) ((elements S).map f).hom) x

/-- `(Algebra.invert S ϖ).obj A` is the zero ring iff a power of `ϖ` maps to `0` in `A_*`. -/
theorem subsingleton_invert_obj_iff (ϖ : V) (A : Algebra S) :
    Subsingleton ((invert S ϖ).obj A) ↔
      ∃ n : ℕ, algebraMap V ((elements S).obj A) (ϖ ^ n) = 0 := by
  rw [IsLocalization.subsingleton_iff (M := Submonoid.powers (algebraMap V ((elements S).obj A) ϖ))
    (S := (invert S ϖ).obj A)]
  simp [Submonoid.mem_powers_iff, map_pow]

/-- Inverting `0` sends every almost algebra to the zero algebra. -/
instance subsingleton_invert_zero_obj (A : Algebra S) :
    Subsingleton ((invert S (0 : V)).obj A) :=
  (subsingleton_invert_obj_iff S 0 A).mpr ⟨1, by simp⟩

/-- Inverting a unit `ϖ : V` preserves the algebra `A_*` of almost elements: the canonical map
`A_* → (Algebra.invert S ϖ).obj A` is an `A_*`-algebra (hence `V`-algebra) isomorphism. -/
noncomputable def invertObjEquivElementsOfIsUnit {ϖ : V} (hu : IsUnit ϖ) (A : Algebra S) :
    ((invert S ϖ).obj A) ≃ₐ[(elements S).obj A] (elements S).obj A :=
  (IsLocalization.atUnits ((elements S).obj A)
    (Submonoid.powers (algebraMap V ((elements S).obj A) ϖ)) (S := (invert S ϖ).obj A)
    (Submonoid.powers_le.mpr (hu.map (algebraMap V ((elements S).obj A))))).symm

/-- Under `invertObjEquivElementsOfIsUnit`, a canonical numerator `algebraMap A_* _ x` maps back
to `x`. -/
theorem invertObjEquivElementsOfIsUnit_algebraMap {ϖ : V} (hu : IsUnit ϖ) (A : Algebra S)
    (x : (elements S).obj A) :
    invertObjEquivElementsOfIsUnit S hu A
      (algebraMap ((elements S).obj A) ((invert S ϖ).obj A) x) = x :=
  (invertObjEquivElementsOfIsUnit S hu A).commutes x

/-- After base-changing `S` to a localization `W` away from `ϖ ∈ m`, the setup becomes classical,
so almostification `CommAlgCat W ⥤ Algebra (S.baseChange W)` is an equivalence of categories. -/
theorem isEquivalence_toAlmost_baseChange_away (W : Type u) [CommRing W] [_root_.Algebra V W]
    {ϖ : V} [IsLocalization.Away ϖ W] (hϖ : ϖ ∈ S.ideal) :
    (toAlmost (S.baseChange W)).IsEquivalence := by
  rw [S.baseChange_away_eq_classical W hϖ]
  infer_instance

/-- Base-changing `S` to a localization `W` away from `ϖ ∈ m` identifies almost `W`-algebras with
honest commutative `W`-algebras via `Algebra.toAlmost (S.baseChange W)`. -/
noncomputable def baseChangeAwayEquiv (W : Type u) [CommRing W] [_root_.Algebra V W] {ϖ : V}
    [IsLocalization.Away ϖ W] (hϖ : ϖ ∈ S.ideal) :
    CommAlgCat.{u} W ≌ Algebra (S.baseChange W) :=
  have := isEquivalence_toAlmost_baseChange_away S W hϖ
  (toAlmost (S.baseChange W)).asEquivalence

/-- Extension of scalars of a commutative `V`-algebra `R` via `ModuleCat.extendScalars` on
commutative monoid objects agrees with `Localization.Away ϖ ⊗[V] R`. -/
private noncomputable def extendScalarsCommAlgIso (ϖ : V) (R : CommAlgCat.{u} V) :
    CommAlgCat.of (Localization.Away ϖ) (Localization.Away ϖ ⊗[V] R) ≅
      ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.obj
        ((ModuleCat.extendScalars.{u, u, u}
          (algebraMap V (Localization.Away ϖ))).mapCommMon.obj
          (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.obj R)) := by
  let S₀ := Localization.Away ϖ
  let φ := algebraMap V S₀
  let G := ModuleCat.extendScalars.{u, u, u} φ
  let R₀ := ModuleCat.of V R
  let M := G.mapCommMon.obj (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.obj R)
  let eLin : (S₀ ⊗[V] R) ≃ₗ[S₀] M.X :=
    (ModuleCat.extendScalarsAlgebraMapIso (S := S₀) R₀).symm.toLinearEquiv
  have heLin (s : S₀) (r : R) : eLin (s ⊗ₜ[V] r) = show M.X from s ⊗ₜ[V, φ] (r : R₀) :=
    ModuleCat.extendScalarsAlgebraMapIso_inv_tmul R₀ s r
  have hμ (r₁ r₂ : R) :
      (Functor.LaxMonoidal.μ G R₀ R₀)
          (((1 : S₀) ⊗ₜ[V, φ] (r₁ : R₀)) ⊗ₜ[S₀] ((1 : S₀) ⊗ₜ[V, φ] (r₂ : R₀))) =
        (1 : S₀) ⊗ₜ[V, φ] ((r₁ : R₀) ⊗ₜ[V] (r₂ : R₀) : ↑(R₀ ⊗ R₀)) :=
    (congrArg (Functor.LaxMonoidal.μ G R₀ R₀)
      (ModuleCat.extendScalars_δ_tmul φ R₀ R₀ r₁ r₂).symm).trans
      (ConcreteCategory.congr_hom (Functor.Monoidal.δ_μ G R₀ R₀) _)
  have h1 (r₁ r₂ : R) : eLin (1 ⊗ₜ[V] r₁) * eLin (1 ⊗ₜ[V] r₂) = eLin (1 ⊗ₜ[V] (r₁ * r₂)) :=
    (congrArg₂ (· * ·) (heLin 1 r₁) (heLin 1 r₂)).trans <|
      ((congrArg (G.map (ModuleCat.ofHom (LinearMap.mul' V R))) (hμ r₁ r₂)).trans
        (ModuleCat.ExtendScalars.map_tmul φ (ModuleCat.ofHom (LinearMap.mul' V R)) 1
          ((r₁ : R₀) ⊗ₜ[V] (r₂ : R₀) : ↑(R₀ ⊗ R₀)))).trans
        (heLin 1 (r₁ * r₂)).symm
  have hsmul (s : S₀) (r : R) : eLin (s ⊗ₜ[V] r) = s • eLin (1 ⊗ₜ[V] r) := by
    rw [← eLin.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hMul (x y : S₀ ⊗[V] R) : eLin (x * y) = eLin x * eLin y := by
    refine TensorProduct.inductionOn x (fun s₁ r₁ ↦ ?_) fun a b ha hb ↦ by
      simp only [add_mul, map_add] at ha hb ⊢; exact congrArg₂ (· + ·) ha hb
    refine TensorProduct.inductionOn y (fun s₂ r₂ ↦ ?_) fun a b ha hb ↦ by
      simp only [mul_add, map_add] at ha hb ⊢; exact congrArg₂ (· + ·) ha hb
    rw [_root_.Algebra.TensorProduct.tmul_mul_tmul, hsmul (s₁ * s₂), hsmul s₁, hsmul s₂,
      smul_mul_smul_comm, h1]
  have hOne : eLin 1 = 1 :=
    calc eLin 1 = eLin 1 * 1 := (mul_one _).symm
      _ = eLin 1 * eLin (eLin.symm 1) := by rw [eLin.apply_symm_apply]
      _ = eLin (1 * eLin.symm 1) := (hMul 1 (eLin.symm 1)).symm
      _ = eLin (eLin.symm 1) := by rw [one_mul]
      _ = 1 := eLin.apply_symm_apply 1
  exact CommAlgCat.isoMk (AlgEquiv.ofLinearEquiv eLin hOne hMul)

private theorem extendScalarsCommAlgIso_hom_tmul (ϖ : V) (R : CommAlgCat.{u} V)
    (s : Localization.Away ϖ) (r : R) :
    (extendScalarsCommAlgIso ϖ R).hom (s ⊗ₜ[V] r) =
      s ⊗ₜ[V, algebraMap V (Localization.Away ϖ)] r :=
  ModuleCat.extendScalarsAlgebraMapIso_inv_tmul (ModuleCat.of V R) s r

/-- Component comparison morphism `(Localization.Away ϖ ⊗[V] A_*) → (Almost.invert S hϖ).obj A` of
commutative monoid objects. -/
private noncomputable def extendScalarsElementsToInvertCommMon {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (A : Algebra S) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap V (Localization.Away ϖ))).mapCommMon.obj
        (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.obj ((elements S).obj A)) ⟶
      (Almost.invert S hϖ).mapCommMon.obj A :=
  (Functor.mapCommMonCompIso.symm ≪≫
      Functor.mapCommMonNatIso (toAlmostCompInvertIsoExtendScalars S hϖ)).inv.app
    (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.obj ((elements S).obj A)) ≫
    (Almost.invert S hϖ).mapCommMon.map ((counitIso S).app A).hom

/-- Component isomorphism identifying `(Algebra.invert S ϖ).obj A` with the commutative algebra
corresponding to `(Almost.invert S hϖ).mapCommMon.obj A`. -/
private noncomputable def invertObjIsoMapCommMonObj {ϖ : V} (hϖ : ϖ ∈ S.ideal) (A : Algebra S) :
    (invert S ϖ).obj A ≅
      ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.obj
        ((Almost.invert S hϖ).mapCommMon.obj A) :=
  CommAlgCat.isoMk
      (Localization.tensorRightAlgEquiv (Submonoid.powers ϖ) ((elements S).obj A)).symm ≪≫
    extendScalarsCommAlgIso ϖ ((elements S).obj A) ≪≫
    ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.mapIso
      (((Functor.mapCommMonCompIso.symm ≪≫
          Functor.mapCommMonNatIso (toAlmostCompInvertIsoExtendScalars S hϖ)).app
        (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.obj ((elements S).obj A))).symm ≪≫
        (Almost.invert S hϖ).mapCommMon.mapIso ((counitIso S).app A))

private theorem invertObjIsoMapCommMonObj_hom_algebraMap {ϖ : V} (hϖ : ϖ ∈ S.ideal)
    (A : Algebra S) (x : (elements S).obj A) :
    (invertObjIsoMapCommMonObj S hϖ A).hom
        (algebraMap ((elements S).obj A) ((invert S ϖ).obj A) x) =
      (extendScalarsElementsToInvertCommMon S hϖ A).hom.hom
        ((1 : Localization.Away ϖ) ⊗ₜ[V, algebraMap V (Localization.Away ϖ)] x) := by
  have hx : algebraMap ((elements S).obj A) ((invert S ϖ).obj A) x =
      Localization.tensorRightAlgEquiv (Submonoid.powers ϖ) ((elements S).obj A)
        ((1 : Localization.Away ϖ) ⊗ₜ[V] x) :=
    (Localization.tensorRightAlgEquiv_apply_one_tmul (Submonoid.powers ϖ) x).symm
  rw [hx]
  -- Unfold `invertObjIsoMapCommMonObj` as `tensorRightAlgEquiv.symm` followed by
  -- `extendScalarsCommAlgIso` and `extendScalarsElementsToInvertCommMon`.
  change (ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.map
      (extendScalarsElementsToInvertCommMon S hϖ A))
    ((extendScalarsCommAlgIso ϖ ((elements S).obj A)).hom
      ((Localization.tensorRightAlgEquiv (Submonoid.powers ϖ) ((elements S).obj A)).symm
        (Localization.tensorRightAlgEquiv (Submonoid.powers ϖ) ((elements S).obj A)
          ((1 : Localization.Away ϖ) ⊗ₜ[V] x)))) = _
  rw [AlgEquiv.symm_apply_apply, extendScalarsCommAlgIso_hom_tmul]
  rfl

/-- For `ϖ ∈ m`, `Algebra.invert S ϖ` is naturally isomorphic to the functor induced on
commutative monoid objects by the braided monoidal functor `Almost.invert S hϖ`. -/
noncomputable def invertIsoMapCommMon {ϖ : V} (hϖ : ϖ ∈ S.ideal) :
    invert S ϖ ≅
      (Almost.invert S hϖ).mapCommMon ⋙
        ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor := by
  refine NatIso.ofComponents (invertObjIsoMapCommMonObj S hϖ) fun {A B} f ↦ ?_
  apply CommAlgCat.hom_ext
  apply AlgHom.toRingHom_injective
  refine IsLocalization.ringHom_ext (_root_.Algebra.algebraMapSubmonoid ((elements S).obj A)
    (Submonoid.powers ϖ)) ?_
  ext x
  let G := ModuleCat.extendScalars.{u, u, u} (algebraMap V (Localization.Away ϖ))
  have hcounit :
      (Almost.invert S hϖ).mapCommMon.map ((toAlmost S).map ((elements S).map f)) ≫
        (Almost.invert S hϖ).mapCommMon.map ((counitIso S).app B).hom =
      (Almost.invert S hϖ).mapCommMon.map ((counitIso S).app A).hom ≫
        (Almost.invert S hϖ).mapCommMon.map f := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (Almost.invert S hϖ).mapCommMon.map ((counitIso S).hom.naturality f)
  have hk :
      G.mapCommMon.map
          (ModuleCat.CommMonModuleEquivalenceCommAlgebra.inverse.map ((elements S).map f)) ≫
        extendScalarsElementsToInvertCommMon S hϖ B =
      extendScalarsElementsToInvertCommMon S hϖ A ≫ (Almost.invert S hϖ).mapCommMon.map f :=
    ((Functor.mapCommMonCompIso.symm ≪≫
        Functor.mapCommMonNatIso (toAlmostCompInvertIsoExtendScalars S hϖ)).inv.naturality_assoc
      _ _).trans ((congrArg (_ ≫ ·) hcounit).trans (Category.assoc _ _ _).symm)
  -- Evaluate both sides of the naturality square at `algebraMap A_* A_*[1/ϖ] x`.
  change (invertObjIsoMapCommMonObj S hϖ B).hom ((invert S ϖ).map f
      (algebraMap ((elements S).obj A) ((invert S ϖ).obj A) x)) =
    (ModuleCat.CommMonModuleEquivalenceCommAlgebra.functor.map
      ((Almost.invert S hϖ).mapCommMon.map f))
      ((invertObjIsoMapCommMonObj S hϖ A).hom
        (algebraMap ((elements S).obj A) ((invert S ϖ).obj A) x))
  rw [invert_map_algebraMap, invertObjIsoMapCommMonObj_hom_algebraMap,
    invertObjIsoMapCommMonObj_hom_algebraMap]
  exact congrArg
    (fun m ↦ m.hom.hom ((1 : Localization.Away ϖ) ⊗ₜ[V, algebraMap V (Localization.Away ϖ)] x)) hk

/-- For `ϖ ∈ m` and an honest commutative `V`-algebra `R`, `(Algebra.invert S ϖ).obj (R^a)` is
canonically isomorphic as a `Localization.Away ϖ`-algebra to `R[1/ϖ]`. -/
noncomputable def invertToAlmostObjEquiv {ϖ : V} (hϖ : ϖ ∈ S.ideal) (R : CommAlgCat.{u} V) :
    ((invert S ϖ).obj ((toAlmost S).obj R)) ≃ₐ[Localization.Away ϖ]
      Localization (_root_.Algebra.algebraMapSubmonoid R (Submonoid.powers ϖ)) := by
  let u : R ⟶ (elements S).obj ((toAlmost S).obj R) := (adj S).unit.app R
  let Rₚ := Localization (_root_.Algebra.algebraMapSubmonoid R (Submonoid.powers ϖ))
  let Aₚ := (invert S ϖ).obj ((toAlmost S).obj R)
  let φ := IsLocalization.mapₐ (Submonoid.powers ϖ) (Localization.Away ϖ) Rₚ Aₚ u.hom
  have : IsLocalizedModule (Submonoid.powers ϖ)
      (IsScalarTower.toAlgHom V R Rₚ).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  have : IsLocalizedModule (Submonoid.powers ϖ)
      (IsScalarTower.toAlgHom V ((elements S).obj ((toAlmost S).obj R)) Aₚ).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  have hcoe : (φ : Rₚ → Aₚ) =
      IsLocalizedModule.map (Submonoid.powers ϖ)
        (IsScalarTower.toAlgHom V R Rₚ).toLinearMap
        (IsScalarTower.toAlgHom V ((elements S).obj ((toAlmost S).obj R)) Aₚ).toLinearMap
        u.hom.toLinearMap := by
    ext z
    exact (congrFun (congrArg DFunLike.coe (IsLocalization.map_eq_toLinearMap_mapₐ
      (Submonoid.powers ϖ) (Localization.Away ϖ) Rₚ Aₚ u.hom)) z).symm
  have hbij : Function.Bijective φ := by
    rw [hcoe]
    exact (isAlmostIso_adj_unit_app S R).bijective_isLocalizedModule_map hϖ _ _
  exact (AlgEquiv.ofBijective φ hbij).symm

/-- For `ϖ ∈ m`, `(Algebra.invert S ϖ).obj (R^a)` is the zero ring iff a power of `ϖ` maps to `0`
in `R`. -/
theorem subsingleton_invert_toAlmost_obj_iff {ϖ : V} (hϖ : ϖ ∈ S.ideal) (R : CommAlgCat.{u} V) :
    Subsingleton ((invert S ϖ).obj ((toAlmost S).obj R)) ↔
      ∃ n : ℕ, algebraMap V R (ϖ ^ n) = 0 := by
  rw [(invertToAlmostObjEquiv S hϖ R).toEquiv.subsingleton_congr,
    IsLocalization.subsingleton_iff
      (M := _root_.Algebra.algebraMapSubmonoid R (Submonoid.powers ϖ))]
  simp [_root_.Algebra.algebraMapSubmonoid_powers, Submonoid.mem_powers_iff, map_pow]

end Algebra

end TauCeti.Almost

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.AlgebraicGeometry.Sites.Big.Sheaf

/-!
# Restricting a big-site module along a morphism of schemes

Let `g : S' ⟶ S` be a morphism of schemes and `F` an `𝒪_S`-module. Regarding an `S'`-scheme
`(T, h)` as the `S`-scheme `(T, h ≫ g)` is the functor `Over.map g` between the big sites, and the
big structure sheaf of `S` restricts along it to the big structure sheaf of `S'`
(`AlgebraicGeometry.Scheme.bigRingCatSheafPullback`). This file shows that the restriction of the
big-site module `F^a : (T, h) ↦ Γ(T, h^* F)` of `S` along `Over.map g` is the big-site module
`(g^* F)^a` of `S'` (SchemeAndStackFoundations §2.9, *bigSheaf_pullback*): over `(T, h)` the two
are `Γ(T, (h ≫ g)^* F)` and `Γ(T, h^* g^* F)`, identified by the composition isomorphism of
pullbacks of modules (`AlgebraicGeometry.Scheme.Modules.bigSectionsPullbackEquiv`), and these
identifications commute with the restriction maps of the two big sites
(`AlgebraicGeometry.Scheme.Modules.bigSectionsRestrict_bigSectionsPullbackEquiv`), by the
associativity of the pullback pseudofunctor.

## Main declarations

* `AlgebraicGeometry.Scheme.bigRingCatSheafPullback g`: the big structure sheaf of `S'` is the
  restriction of that of `S` along `Over.map g`.
* `AlgebraicGeometry.Scheme.Modules.bigPresheafPullbackIso g F`: the restriction of
  `bigPresheaf F` along `Over.map g` is `bigPresheaf (g^* F)`.
* `AlgebraicGeometry.Scheme.Modules.bigSheafPullbackIso g F`: the same for the big fpqc sheaves,
  `bigSheaf F` restricted along `Over.map g` is `bigSheaf (g^* F)` for quasi-coherent `F`.
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {S S' : Scheme.{u}} (g : S' ⟶ S)

/-- The big structure sheaf `T ↦ Γ(T, 𝒪_T)` of `S'` is the restriction of the big structure sheaf
of `S` along `Over.map g : Over S' ⥤ Over S`: both take the value `Γ(T, 𝒪_T)` on an
`S'`-scheme `T`. -/
noncomputable def bigRingCatSheafPullback :
    bigRingCatSheaf S' ⟶ ((Over.map g).sheafPushforwardContinuous RingCat.{u}
      (fpqcTopology.over S') (fpqcTopology.over S)).obj (bigRingCatSheaf S) :=
  ⟨𝟙 _⟩

@[simp]
lemma bigRingCatSheafPullback_hom_app (T : (Over S')ᵒᵖ) :
    (bigRingCatSheafPullback g).hom.app T = 𝟙 _ :=
  (rfl)

namespace Modules

variable (F : S.Modules)

/-- The sections over an `S'`-scheme `(T, h)` of the big-site module of `F`, with `T` regarded as
the `S`-scheme `(T, h ≫ g)`, are the sections of the big-site module of `g^* F`: the composition
isomorphism `(h ≫ g)^* F ≅ h^* g^* F` of pullbacks gives a `Γ(T, 𝒪_T)`-linear equivalence. -/
noncomputable def bigSectionsPullbackEquiv (T : Over S') :
    Γ((pullback ((Over.map g).obj T).hom).obj F, ⊤) ≃ₗ[Γ(T.left, ⊤)]
      Γ((pullback T.hom).obj ((pullback g).obj F), ⊤) :=
  sectionsLinearEquiv ((pullbackComp T.hom g).app F).symm ⊤

lemma bigSectionsPullbackEquiv_apply (T : Over S')
    (s : Γ((pullback ((Over.map g).obj T).hom).obj F, ⊤)) :
    bigSectionsPullbackEquiv g F T s = ((pullbackComp T.hom g).inv.app F).app ⊤ s :=
  sectionsLinearEquiv_apply _ _ _

/-- The two composites `f^* (h' ≫ g)^* F ⟶ h^* g^* F` around the restriction along `f` and the
composition isomorphisms of pullbacks agree, for `f ≫ h' = h`. This is the associativity of the
pullback pseudofunctor, with `h` a free variable so that the equation `f ≫ h' = h` can be
substituted. -/
private lemma pullbackComp_coherence {T T' : Scheme.{u}} (f : T ⟶ T') (h' : T' ⟶ S')
    {h : T ⟶ S'} (w : f ≫ h' = h) :
    (pullbackComp f (h' ≫ g)).hom.app F ≫
        (pullbackCongr (by rw [← w, Category.assoc] : f ≫ h' ≫ g = h ≫ g)).hom.app F ≫
          (pullbackComp h g).inv.app F =
      (pullback f).map ((pullbackComp h' g).inv.app F) ≫
        (pullbackComp f h').hom.app ((pullback g).obj F) ≫
          (pullbackCongr w).hom.app ((pullback g).obj F) := by
  subst w
  rw [← cancel_epi ((pullback f).map ((pullbackComp h' g).hom.app F)),
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app_assoc]
  simp [pullbackCongr]

/-- The identifications `bigSectionsPullbackEquiv` commute with the restriction maps of the big
sites of `S` and `S'`: restricting along `f : T ⟶ T'` over `S'`, regarded as a morphism over `S`
through `Over.map g`, corresponds to restricting along `f` itself. -/
lemma bigSectionsRestrict_bigSectionsPullbackEquiv {T T' : Over S'} (f : T ⟶ T')
    (s : Γ((pullback ((Over.map g).obj T').hom).obj F, ⊤)) :
    bigSectionsPullbackEquiv g F T (bigSectionsRestrict F ((Over.map g).map f) s) =
      bigSectionsRestrict ((pullback g).obj F) f (bigSectionsPullbackEquiv g F T' s) := by
  rw [bigSectionsPullbackEquiv_apply, bigSectionsPullbackEquiv_apply, bigSectionsRestrict_apply,
    bigSectionsRestrict_apply, ← Hom.pullbackSections_naturality]
  exact congr($(pullbackComp_coherence g F f.left T'.hom (Over.w f)).app ⊤
    (f.left.pullbackSections _ ⊤ s))

/-- **Restriction of the big-site presheaf along a morphism of schemes.** The restriction of the
presheaf of modules `F^a : (T, h) ↦ Γ(T, h^* F)` on the big site of `S` along
`Over.map g : Over S' ⥤ Over S` is the presheaf of modules `(g^* F)^a` on the big site of `S'`. -/
noncomputable def bigPresheafPullbackIso :
    (PresheafOfModules.pushforward (bigRingCatSheafPullback g).hom).obj F.bigPresheaf ≅
      ((pullback g).obj F).bigPresheaf :=
  PresheafOfModules.isoMk
    (fun T ↦ ModuleCat.restrictScalarsId'App _ rfl _ ≪≫
      (bigSectionsPullbackEquiv g F T.unop).toModuleIso)
    (fun _ _ f ↦ by
      ext s
      exact bigSectionsRestrict_bigSectionsPullbackEquiv g F f.unop s)

@[simp]
lemma bigPresheafPullbackIso_hom_app_apply (T : Over S')
    (s : Γ((pullback ((Over.map g).obj T).hom).obj F, ⊤)) :
    (bigPresheafPullbackIso g F).hom.app (op T) s = ((pullbackComp T.hom g).inv.app F).app ⊤ s :=
  bigSectionsPullbackEquiv_apply g F T s

variable [F.IsQuasicoherent]

/-- **`bigSheaf_pullback`.** For a quasi-coherent `𝒪_S`-module `F`, the restriction of the
big-site module `F^a` of `S` along `Over.map g : Over S' ⥤ Over S` is the big-site module
`(g^* F)^a` of `S'` (SchemeAndStackFoundations §2.9). -/
noncomputable def bigSheafPullbackIso :
    (SheafOfModules.pushforward (bigRingCatSheafPullback g)).obj (bigSheaf F) ≅
      bigSheaf ((pullback g).obj F) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso (bigPresheafPullbackIso g F)

@[simp]
lemma bigSheafPullbackIso_hom_val :
    (bigSheafPullbackIso g F).hom.val = (bigPresheafPullbackIso g F).hom :=
  (rfl)

end Modules

end AlgebraicGeometry.Scheme

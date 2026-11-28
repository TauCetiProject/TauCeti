/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.AlgebraicGeometry.Sites.Big.Sheaf.Basic

/-!
# Restricting a big-site module along a morphism of schemes

Let `g : S' ⟶ S` be a morphism of schemes and `F` an `𝒪_S`-module. Regarding an `S'`-scheme
`(T, h)` as the `S`-scheme `(T, h ≫ g)` is the functor `Over.map g` between the big sites, and the
big structure sheaf of `S` restricts along it to the big structure sheaf of `S'`
(`AlgebraicGeometry.Scheme.bigRingCatSheafPullback`). This file shows that the restriction of the
big-site module `F^a : (T, h) ↦ Γ(T, h^* F)` of `S` along `Over.map g` is the big-site module
`(g^* F)^a` of `S'`: over `(T, h)` the two are `Γ(T, (h ≫ g)^* F)` and `Γ(T, h^* g^* F)`,
identified by the composition isomorphism of pullbacks of modules
(`AlgebraicGeometry.Scheme.Modules.bigSectionsPullbackEquiv`), and these identifications commute
with the restriction maps of the two big sites
(`AlgebraicGeometry.Scheme.Modules.bigSectionsPullbackEquiv_bigSectionsRestrict`), by the
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
    Γ((pullback (T.hom ≫ g)).obj F, ⊤) ≃ₗ[Γ(T.left, ⊤)]
      Γ((pullback T.hom).obj ((pullback g).obj F), ⊤) :=
  sectionsLinearEquiv ((pullbackComp T.hom g).app F).symm ⊤

@[simp]
lemma bigSectionsPullbackEquiv_apply (T : Over S') (s : Γ((pullback (T.hom ≫ g)).obj F, ⊤)) :
    bigSectionsPullbackEquiv g F T s = ((pullbackComp T.hom g).inv.app F).app ⊤ s :=
  sectionsLinearEquiv_apply _ _ _

@[simp]
lemma bigSectionsPullbackEquiv_symm_apply (T : Over S')
    (s : Γ((pullback T.hom).obj ((pullback g).obj F), ⊤)) :
    (bigSectionsPullbackEquiv g F T).symm s = ((pullbackComp T.hom g).hom.app F).app ⊤ s :=
  sectionsLinearEquiv_symm_apply _ _ _

/-- The identifications `bigSectionsPullbackEquiv` commute with the restriction maps of the big
sites of `S` and `S'`: restricting along `f : T ⟶ T'` over `S'`, regarded as a morphism over `S`
through `Over.map g`, corresponds to restricting along `f` itself. -/
lemma bigSectionsPullbackEquiv_bigSectionsRestrict {T T' : Over S'} (f : T ⟶ T')
    (s : Γ((pullback ((Over.map g).obj T').hom).obj F, ⊤)) :
    bigSectionsPullbackEquiv g F T (bigSectionsRestrict F ((Over.map g).map f) s) =
      bigSectionsRestrict ((pullback g).obj F) f (bigSectionsPullbackEquiv g F T' s) := by
  rw [bigSectionsPullbackEquiv_apply, bigSectionsPullbackEquiv_apply, bigSectionsRestrict_apply,
    bigSectionsRestrict_apply, ← Hom.pullbackSections_naturality]
  exact congr($(pullbackComp_hom_app_comp_pullbackCongr_hom_app_comp_pullbackComp_inv_app
    f.left T'.hom g (Over.w f) F).app ⊤ (f.left.pullbackSections _ ⊤ s))

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
      -- `pushforward (bigRingCatSheafPullback g).hom` only typechecks after unfolding
      -- `sheafPushforwardContinuous` to `(Over.map g).op ⋙ _`, so `simp` and `rw` cannot match in
      -- this goal. It is closed up to the `rfl` lemmas `restrictScalarsId'App_hom_apply`,
      -- `pushforward_obj_map_apply` and `bigPresheaf_map_apply`.
      ext s
      exact bigSectionsPullbackEquiv_bigSectionsRestrict g F f.unop s)

@[simp]
lemma bigPresheafPullbackIso_hom_app_apply (T : Over S')
    (s : Γ((pullback ((Over.map g).obj T).hom).obj F, ⊤)) :
    (bigPresheafPullbackIso g F).hom.app (op T) s = ((pullbackComp T.hom g).inv.app F).app ⊤ s :=
  bigSectionsPullbackEquiv_apply g F T s

@[simp]
lemma bigPresheafPullbackIso_inv_app_apply (T : Over S')
    (s : Γ((pullback T.hom).obj ((pullback g).obj F), ⊤)) :
    (bigPresheafPullbackIso g F).inv.app (op T) s = ((pullbackComp T.hom g).hom.app F).app ⊤ s :=
  bigSectionsPullbackEquiv_symm_apply g F T s

/-- The isomorphisms `bigPresheafPullbackIso g F` are natural in the `𝒪_S`-module `F`: they
intertwine the restriction of `(bigPresheafFunctor S).map φ` along `Over.map g` with
`(bigPresheafFunctor S').map (g^* φ)`. -/
@[reassoc]
lemma bigPresheafPullbackIso_hom_naturality {F G : S.Modules} (φ : F ⟶ G) :
    (PresheafOfModules.pushforward (bigRingCatSheafPullback g).hom).map
        ((bigPresheafFunctor S).map φ) ≫ (bigPresheafPullbackIso g G).hom =
      (bigPresheafPullbackIso g F).hom ≫ (bigPresheafFunctor S').map ((pullback g).map φ) := by
  -- As in `bigPresheafPullbackIso`, `simp` and `rw` cannot match in this goal, so the
  -- components are rewritten by `Eq.trans`. The composites and the pushforward of
  -- `(bigPresheafFunctor S).map φ` are then unfolded by the `rfl` lemmas
  -- `PresheafOfModules.comp_app` and `pushforward_map_app_apply`.
  ext T s
  refine (bigPresheafPullbackIso_hom_app_apply g G T.unop _).trans ?_
  refine Eq.trans ?_ (congrArg (((pullback T.unop.hom).map ((pullback g).map φ)).app ⊤)
    (bigPresheafPullbackIso_hom_app_apply g F T.unop s)).symm
  exact congr($((pullbackComp T.unop.hom g).inv.naturality φ).app ⊤ s)

variable [F.IsQuasicoherent]

/-- **Restriction of the big-site module along a morphism of schemes.** For a quasi-coherent
`𝒪_S`-module `F`, the restriction of the big-site module `F^a` of `S` along
`Over.map g : Over S' ⥤ Over S` is the big-site module `(g^* F)^a` of `S'`. -/
noncomputable def bigSheafPullbackIso :
    (SheafOfModules.pushforward (bigRingCatSheafPullback g)).obj (bigSheaf F) ≅
      bigSheaf ((pullback g).obj F) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso (bigPresheafPullbackIso g F)

@[simp]
lemma bigSheafPullbackIso_hom_val :
    (bigSheafPullbackIso g F).hom.val = (bigPresheafPullbackIso g F).hom :=
  (rfl)

@[simp]
lemma bigSheafPullbackIso_inv_val :
    (bigSheafPullbackIso g F).inv.val = (bigPresheafPullbackIso g F).inv :=
  (rfl)

open TauCeti.AlgebraicGeometry in
/-- The isomorphisms `bigSheafPullbackIso g F` are natural in the quasi-coherent module `F`: they
intertwine the restriction of `(bigSheafFunctor S).map φ` along `Over.map g` with
`(bigSheafFunctor S').map (g^* φ)`. -/
-- `g^* φ` is the morphism between the quasi-coherent modules `g^* F` and `g^* G` themselves:
-- `QuasicoherentSheaf.pullback g` is not exposed, so its values are not `g^* F` by definition.
@[reassoc]
lemma bigSheafPullbackIso_hom_naturality {F G : QuasicoherentSheaf S} (φ : F ⟶ G) :
    (SheafOfModules.pushforward (bigRingCatSheafPullback g)).map ((bigSheafFunctor S).map φ) ≫
        (bigSheafPullbackIso g G.obj).hom =
      (bigSheafPullbackIso g F.obj).hom ≫
        (bigSheafFunctor S').map (ObjectProperty.homMk
          (X := ⟨_, isQuasicoherent_pullback g F.obj⟩) (Y := ⟨_, isQuasicoherent_pullback g G.obj⟩)
          ((pullback g).map φ.hom)) :=
  SheafOfModules.Hom.ext (bigPresheafPullbackIso_hom_naturality g φ.hom)

end Modules

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Big.Sheaf

/-!
# The functor `F ↦ F^a` to big-site modules is fully faithful

Let `S` be a scheme. The functor `AlgebraicGeometry.Scheme.bigPresheafFunctor S` sends an
`𝒪_S`-module `F` to the presheaf of modules `F^a : (T, h) ↦ Γ(T, h^* F)` over the big structure
sheaf `T ↦ Γ(T, 𝒪_T)` on `Over S`. This file proves that it is fully faithful
(`AlgebraicGeometry.Scheme.bigPresheafFunctorFullyFaithful`): every `𝒪`-linear morphism
`ψ : F^a ⟶ G^a` is `φ^a` for a unique `φ : F ⟶ G`. Consequently the functor
`AlgebraicGeometry.Scheme.bigSheafFunctor S` from quasi-coherent `𝒪_S`-modules to modules on the
big fpqc site is fully faithful (`AlgebraicGeometry.Scheme.bigSheafFunctorFullyFaithful`; Stacks,
Lemma 35.8.8 (0GN7)).

The morphism `φ` is read off on the open subschemes `U` of `S`, whose big-site sections
`Γ(U, ι_U^* F)` are the sections `Γ(F, U)` (`AlgebraicGeometry.Scheme.Modules.bigOfHom`). To see
that `ψ` is `φ^a` over an arbitrary `S`-scheme `(T, h)`, `ψ` is first restricted to a morphism of
`𝒪_T`-modules `h^* F ⟶ h^* G` (`AlgebraicGeometry.Scheme.Modules.bigRestrictHom`), acting on the
sections over an open `W` of `T` through the `S`-scheme `W`. A morphism out of `h^* F` is
determined by its values on the pullbacks of sections of `F` (`Scheme.Modules.pullback_hom_ext`),
and on those both morphisms are computed by `ψ` on the open subschemes of `S`. No quasi-coherence
is needed for this argument.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.bigRestrictHom`: the morphism `h^* F ⟶ h^* G` of
  `𝒪_T`-modules induced by `ψ : F^a ⟶ G^a` over an `S`-scheme `(T, h)`.
* `AlgebraicGeometry.Scheme.Modules.bigOfHom`: the morphism `F ⟶ G` induced by `ψ`.
* `AlgebraicGeometry.Scheme.Modules.bigPresheafFunctor_map_bigOfHom`: `(bigOfHom ψ)^a = ψ`.
* `AlgebraicGeometry.Scheme.bigPresheafFunctorFullyFaithful`: `F ↦ F^a` is fully faithful on
  `𝒪_S`-modules.
* `AlgebraicGeometry.Scheme.bigSheafFunctorFullyFaithful`: `F ↦ F^a` is fully faithful on
  quasi-coherent `𝒪_S`-modules.

## References

* The Stacks Project, Section 35.8, *Quasi-coherent sheaves and topologies*,
  [Lemma 35.8.8 (0GN7)](https://stacks.math.columbia.edu/tag/0GN7).
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme

namespace Modules

variable {S : Scheme.{u}}

section Equivs

variable (F : S.Modules)

/-- For an `S`-scheme `(T, h)` and an open `W` of `T`, the sections of `h^* F` over `W` are the
global sections of the pullback of `F` to the `S`-scheme `W`. -/
-- Exposed so that its values are by definition the local restriction maps.
@[expose]
noncomputable def bigOpenEquiv (T : Over S) (W : T.left.Opens) :
    Γ((pullback T.hom).obj F, W) ≃ Γ((pullback (W.ι ≫ T.hom)).obj F, ⊤) :=
  Equiv.ofBijective _ (bijective_bigSectionsRestrictLE_ι F T.hom W rfl)

lemma bigOpenEquiv_apply (T : Over S) (W : T.left.Opens) (s : Γ((pullback T.hom).obj F, W)) :
    bigOpenEquiv F T W s = bigSectionsRestrictLE F W.ι rfl W ⊤ (by simp) s :=
  rfl

lemma bigOpenEquiv_add (T : Over S) (W : T.left.Opens) (s s' : Γ((pullback T.hom).obj F, W)) :
    bigOpenEquiv F T W (s + s') = bigOpenEquiv F T W s + bigOpenEquiv F T W s' := by
  simp only [bigOpenEquiv_apply, bigSectionsRestrictLE_apply, map_add]

lemma bigOpenEquiv_smul (T : Over S) (W : T.left.Opens) (r : Γ(T.left, W))
    (s : Γ((pullback T.hom).obj F, W)) :
    bigOpenEquiv F T W (r • s) =
      (W.ι.appLE W ⊤ (by simp)).hom r • bigOpenEquiv F T W s := by
  simp only [bigOpenEquiv_apply, bigSectionsRestrictLE_apply, map_smulₛₗ, Hom.app_smul]

/-- The sections of `F` over an open `U` of `S` are the global sections of its pullback to the
`S`-scheme `U`. -/
-- Exposed so that its values are by definition pulled-back sections.
@[expose]
noncomputable def bigOpensSectionsEquiv (U : S.Opens) :
    Γ(F, U) ≃ Γ((pullback U.ι).obj F, ⊤) :=
  Equiv.ofBijective _ (bijective_pullbackSectionsLE_ι F U ⊤ rfl)

lemma bigOpensSectionsEquiv_apply (U : S.Opens) (s : Γ(F, U)) :
    bigOpensSectionsEquiv F U s = U.ι.pullbackSectionsLE F U ⊤ (by simp) s :=
  rfl

lemma bigOpensSectionsEquiv_add (U : S.Opens) (s s' : Γ(F, U)) :
    bigOpensSectionsEquiv F U (s + s') =
      bigOpensSectionsEquiv F U s + bigOpensSectionsEquiv F U s' :=
  map_add (U.ι.pullbackSectionsLE F U ⊤ (by simp)) s s'

lemma bigOpensSectionsEquiv_smul (U : S.Opens) (r : Γ(S, U)) (s : Γ(F, U)) :
    bigOpensSectionsEquiv F U (r • s) =
      (U.ι.appLE U ⊤ (by simp)).hom r • bigOpensSectionsEquiv F U s :=
  map_smulₛₗ (U.ι.pullbackSectionsLE F U ⊤ (by simp)) r s

/-- Restriction from the `S`-scheme `U` to the `S`-scheme `U' ≤ U` is restriction of sections. -/
lemma bigSectionsRestrict_bigOpensSectionsEquiv {U U' : S.Opens} (i : U' ⟶ U) (s : Γ(F, U)) :
    bigSectionsRestrict F (Over.homMk (S.homOfLE i.le) (by simp) :
        Over.mk U'.ι ⟶ Over.mk U.ι) (bigOpensSectionsEquiv F U s) =
      bigOpensSectionsEquiv F U' (F.presheaf.map i.op s) := by
  rw [bigOpensSectionsEquiv_apply, bigOpensSectionsEquiv_apply, Hom.pullbackSectionsLE_map]
  · exact bigSectionsRestrict_pullbackSectionsLE F _ U _ _ s
  · exact fun x _ ↦ i.le x.property

/-- For an `S`-scheme `(T, h)` and an open `U` of `S`, the `S`-morphism from the open
subscheme `h⁻¹ U` of `T` to the open subscheme `U` of `S`. -/
noncomputable abbrev bigPreimageHom (T : Over S) (U : S.Opens) :
    Over.mk ((T.hom ⁻¹ᵁ U).ι ≫ T.hom) ⟶ Over.mk U.ι :=
  Over.homMk (T.hom.resLE U (T.hom ⁻¹ᵁ U) le_rfl) (Scheme.Hom.resLE_comp_ι _ _)

/-- The pullback to `h⁻¹ U` of a section of `F` over `U`, read on the `S`-scheme `h⁻¹ U`, is the
restriction of that section from the `S`-scheme `U`. -/
lemma bigOpenEquiv_pullbackSections (T : Over S) (U : S.Opens) (s : Γ(F, U)) :
    bigOpenEquiv F T (T.hom ⁻¹ᵁ U) (T.hom.pullbackSections F U s) =
      bigSectionsRestrict F (bigPreimageHom T U) (bigOpensSectionsEquiv F U s) := by
  have hV : ⊤ ≤ ((T.hom ⁻¹ᵁ U).ι ≫ T.hom) ⁻¹ᵁ U := by simp
  rw [bigOpenEquiv_apply, ← Hom.pullbackSectionsLE_self,
    bigSectionsRestrictLE_pullbackSectionsLE F _ rfl U _ ⊤ le_rfl _ hV, bigOpensSectionsEquiv_apply]
  exact (bigSectionsRestrict_pullbackSectionsLE F (bigPreimageHom T U) U (by simp) hV s).symm

end Equivs

variable {F G : S.Modules} (ψ : F.bigPresheaf ⟶ G.bigPresheaf)

section App

/-- The value of `ψ : F^a ⟶ G^a` on the global sections of the pullbacks to an `S`-scheme. -/
-- Exposed so that its values are by definition the components of `ψ`.
@[expose]
noncomputable def bigApp (T : Over S) (x : Γ((pullback T.hom).obj F, ⊤)) :
    Γ((pullback T.hom).obj G, ⊤) :=
  ψ.app (op T) x

lemma bigApp_add (T : Over S) (x y : Γ((pullback T.hom).obj F, ⊤)) :
    bigApp ψ T (x + y) = bigApp ψ T x + bigApp ψ T y :=
  (ψ.app (op T)).hom.map_add x y

lemma bigApp_smul (T : Over S) (r : Γ(T.left, ⊤)) (x : Γ((pullback T.hom).obj F, ⊤)) :
    bigApp ψ T (r • x) = r • bigApp ψ T x :=
  (ψ.app (op T)).hom.map_smul r x

lemma bigApp_bigSectionsRestrict {T T' : Over S} (f : T ⟶ T')
    (x : Γ((pullback T'.hom).obj F, ⊤)) :
    bigApp ψ T (bigSectionsRestrict F f x) = bigSectionsRestrict G f (bigApp ψ T' x) :=
  PresheafOfModules.naturality_apply ψ f.op x

end App

section Restrict

variable (T : Over S)

/-- The map on sections over an open `W` of `T` of the morphism `h^* F ⟶ h^* G` induced by `ψ`:
apply `ψ` on the `S`-scheme `W`. -/
-- Exposed so that `bigRestrictHom_app` holds by definition.
@[expose]
noncomputable def bigRestrictMap (W : T.left.Opens) (s : Γ((pullback T.hom).obj F, W)) :
    Γ((pullback T.hom).obj G, W) :=
  (bigOpenEquiv G T W).symm (bigApp ψ (Over.mk (W.ι ≫ T.hom)) (bigOpenEquiv F T W s))

lemma bigOpenEquiv_bigRestrictMap (W : T.left.Opens) (s : Γ((pullback T.hom).obj F, W)) :
    bigOpenEquiv G T W (bigRestrictMap ψ T W s) =
      bigApp ψ (Over.mk (W.ι ≫ T.hom)) (bigOpenEquiv F T W s) :=
  Equiv.apply_symm_apply _ _

lemma bigRestrictMap_add (W : T.left.Opens) (s s' : Γ((pullback T.hom).obj F, W)) :
    bigRestrictMap ψ T W (s + s') = bigRestrictMap ψ T W s + bigRestrictMap ψ T W s' :=
  (bigOpenEquiv G T W).injective (by
    rw [bigOpenEquiv_add, bigOpenEquiv_bigRestrictMap, bigOpenEquiv_bigRestrictMap,
      bigOpenEquiv_bigRestrictMap, bigOpenEquiv_add, bigApp_add])

lemma bigRestrictMap_smul (W : T.left.Opens) (r : Γ(T.left, W))
    (s : Γ((pullback T.hom).obj F, W)) :
    bigRestrictMap ψ T W (r • s) = r • bigRestrictMap ψ T W s :=
  (bigOpenEquiv G T W).injective (by
    rw [bigOpenEquiv_smul, bigOpenEquiv_bigRestrictMap, bigOpenEquiv_bigRestrictMap,
      bigOpenEquiv_smul, bigApp_smul])

lemma bigRestrictMap_map {W W' : T.left.Opens} (i : W' ⟶ W) (s : Γ((pullback T.hom).obj F, W)) :
    bigRestrictMap ψ T W' (((pullback T.hom).obj F).presheaf.map i.op s) =
      ((pullback T.hom).obj G).presheaf.map i.op (bigRestrictMap ψ T W s) :=
  (bigOpenEquiv G T W').injective (by
    let f : Over.mk (W'.ι ≫ T.hom) ⟶ Over.mk (W.ι ≫ T.hom) :=
      Over.homMk (T.left.homOfLE i.le) (by simp)
    have e (M : S.Modules) (x : Γ((pullback T.hom).obj M, W)) :
        bigSectionsRestrict M f (bigOpenEquiv M T W x) =
          bigOpenEquiv M T W' (((pullback T.hom).obj M).presheaf.map i.op x) :=
      bigSectionsRestrict_homMk_homOfLE M T i.le rfl rfl x
    rw [bigOpenEquiv_bigRestrictMap, ← e, ← e, bigApp_bigSectionsRestrict,
      bigOpenEquiv_bigRestrictMap])

/-- The morphism of `𝒪_T`-modules `h^* F ⟶ h^* G` induced by `ψ : F^a ⟶ G^a` over an `S`-scheme
`(T, h)`: on sections over an open `W` of `T` it is `ψ` on the `S`-scheme `W`. -/
-- Exposed so that `bigRestrictHom_app` holds by definition.
@[expose]
noncomputable def bigRestrictHom : (pullback T.hom).obj F ⟶ (pullback T.hom).obj G :=
  ⟨PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom (AddMonoidHom.mk' (bigRestrictMap ψ T W.unop)
        (bigRestrictMap_add ψ T W.unop))
      naturality _ _ i := by
        ext s
        exact bigRestrictMap_map ψ T i.unop s }
    fun W r s ↦ bigRestrictMap_smul ψ T W.unop r s⟩

lemma bigRestrictHom_app (W : T.left.Opens) (s : Γ((pullback T.hom).obj F, W)) :
    (bigRestrictHom ψ T).app W s = bigRestrictMap ψ T W s :=
  rfl

/-- On global sections, the restriction of `ψ` to `(T, h)` is `ψ` on `(T, h)`. -/
lemma bigRestrictHom_app_top (s : Γ((pullback T.hom).obj F, ⊤)) :
    (bigRestrictHom ψ T).app ⊤ s = bigApp ψ T s := by
  apply (bigOpenEquiv G T ⊤).injective
  let ι : Over.mk ((⊤ : T.left.Opens).ι ≫ T.hom) ⟶ T := Over.homMk (⊤ : T.left.Opens).ι
  have e (M : S.Modules) (x : Γ((pullback T.hom).obj M, ⊤)) :
      bigSectionsRestrict M ι x = bigOpenEquiv M T ⊤ x := by
    rw [bigSectionsRestrict_homMk_ι, bigOpenEquiv_apply]
    congr 1
    exact congr($(((pullback T.hom).obj M).presheaf.map_id (op ⊤)) x)
  rw [bigRestrictHom_app, bigOpenEquiv_bigRestrictMap, ← e, ← e, bigApp_bigSectionsRestrict]

/-- The restriction of `ψ` to `(T, h)` on the pullback of a section `s` of `F` over `U`: it is
`ψ` applied to `s` on the `S`-scheme `U`, restricted to `h⁻¹ U`. -/
lemma bigOpenEquiv_bigRestrictHom_pullbackSections (U : S.Opens) (s : Γ(F, U)) :
    bigOpenEquiv G T (T.hom ⁻¹ᵁ U)
        ((bigRestrictHom ψ T).app (T.hom ⁻¹ᵁ U) (T.hom.pullbackSections F U s)) =
      bigSectionsRestrict G (bigPreimageHom T U)
        (bigApp ψ (Over.mk U.ι) (bigOpensSectionsEquiv F U s)) := by
  rw [bigRestrictHom_app, bigOpenEquiv_bigRestrictMap, bigOpenEquiv_pullbackSections,
    bigApp_bigSectionsRestrict]

end Restrict

/-- If `ψ : F^a ⟶ G^a` agrees with `φ : F ⟶ G` on the open subschemes of `S`, then `ψ = φ^a`. -/
theorem bigPresheafFunctor_map_eq (φ : F ⟶ G)
    (h : ∀ (U : S.Opens) (s : Γ(F, U)),
      bigApp ψ (Over.mk U.ι) (bigOpensSectionsEquiv F U s) =
        bigOpensSectionsEquiv G U (φ.app U s)) :
    (bigPresheafFunctor S).map φ = ψ := by
  have key (T : Over S) : bigRestrictHom ψ T = (pullback T.hom).map φ := by
    refine pullback_hom_ext fun U s ↦ (bigOpenEquiv G T (T.hom ⁻¹ᵁ U)).injective ?_
    rw [bigOpenEquiv_bigRestrictHom_pullbackSections, h, Hom.pullbackSections_naturality,
      bigOpenEquiv_pullbackSections]
  ext T s
  have e := bigRestrictHom_app_top ψ T.unop s
  rw [key] at e
  exact e.trans rfl

/-- `φ^a` on the open subscheme `U` of `S` is `φ` on sections over `U`. -/
lemma bigApp_bigPresheafFunctor_map (φ : F ⟶ G) (U : S.Opens) (s : Γ(F, U)) :
    bigApp ((bigPresheafFunctor S).map φ) (Over.mk U.ι) (bigOpensSectionsEquiv F U s) =
      bigOpensSectionsEquiv G U (φ.app U s) :=
  Hom.pullbackSectionsLE_naturality U.ι F U ⊤ _ φ s

section OfHom

/-- The map on sections over an open `U` of `S` of the morphism `F ⟶ G` induced by `ψ`. -/
-- Exposed so that `bigOfHom_app` holds by definition.
@[expose]
noncomputable def bigOfHomMap (U : S.Opens) (s : Γ(F, U)) : Γ(G, U) :=
  (bigOpensSectionsEquiv G U).symm (bigApp ψ (Over.mk U.ι) (bigOpensSectionsEquiv F U s))

lemma bigOpensSectionsEquiv_bigOfHomMap (U : S.Opens) (s : Γ(F, U)) :
    bigOpensSectionsEquiv G U (bigOfHomMap ψ U s) =
      bigApp ψ (Over.mk U.ι) (bigOpensSectionsEquiv F U s) :=
  Equiv.apply_symm_apply _ _

lemma bigOfHomMap_add (U : S.Opens) (s s' : Γ(F, U)) :
    bigOfHomMap ψ U (s + s') = bigOfHomMap ψ U s + bigOfHomMap ψ U s' :=
  (bigOpensSectionsEquiv G U).injective (by
    rw [bigOpensSectionsEquiv_add, bigOpensSectionsEquiv_bigOfHomMap,
      bigOpensSectionsEquiv_bigOfHomMap, bigOpensSectionsEquiv_bigOfHomMap,
      bigOpensSectionsEquiv_add, bigApp_add])

lemma bigOfHomMap_smul (U : S.Opens) (r : Γ(S, U)) (s : Γ(F, U)) :
    bigOfHomMap ψ U (r • s) = r • bigOfHomMap ψ U s :=
  (bigOpensSectionsEquiv G U).injective (by
    rw [bigOpensSectionsEquiv_smul, bigOpensSectionsEquiv_bigOfHomMap,
      bigOpensSectionsEquiv_bigOfHomMap, bigOpensSectionsEquiv_smul, bigApp_smul])

lemma bigOfHomMap_map {U U' : S.Opens} (i : U' ⟶ U) (s : Γ(F, U)) :
    bigOfHomMap ψ U' (F.presheaf.map i.op s) = G.presheaf.map i.op (bigOfHomMap ψ U s) :=
  (bigOpensSectionsEquiv G U').injective (by
    rw [bigOpensSectionsEquiv_bigOfHomMap, ← bigSectionsRestrict_bigOpensSectionsEquiv,
      ← bigSectionsRestrict_bigOpensSectionsEquiv, bigOpensSectionsEquiv_bigOfHomMap,
      bigApp_bigSectionsRestrict])

/-- The morphism `F ⟶ G` induced by `ψ : F^a ⟶ G^a`: on sections over an open `U` of `S` it is
`ψ` on the `S`-scheme `U`. -/
-- Exposed so that `bigOfHom_app` holds by definition.
@[expose]
noncomputable def bigOfHom : F ⟶ G :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk' (bigOfHomMap ψ U.unop)
        (bigOfHomMap_add ψ U.unop))
      naturality _ _ i := by
        ext s
        exact bigOfHomMap_map ψ i.unop s }
    fun U r s ↦ bigOfHomMap_smul ψ U.unop r s⟩

lemma bigOfHom_app (U : S.Opens) (s : Γ(F, U)) : (bigOfHom ψ).app U s = bigOfHomMap ψ U s :=
  rfl

/-- **`(bigOfHom ψ)^a = ψ`.** Every `𝒪`-linear morphism `F^a ⟶ G^a` comes from a morphism of
`𝒪_S`-modules. -/
theorem bigPresheafFunctor_map_bigOfHom : (bigPresheafFunctor S).map (bigOfHom ψ) = ψ :=
  bigPresheafFunctor_map_eq ψ _ fun U s ↦ (bigOpensSectionsEquiv_bigOfHomMap ψ U s).symm

/-- The morphism induced by `φ^a` is `φ`. -/
theorem bigOfHom_bigPresheafFunctor_map (φ : F ⟶ G) :
    bigOfHom ((bigPresheafFunctor S).map φ) = φ :=
  Scheme.Modules.hom_ext _ _ fun U ↦ by
    ext s
    exact (bigOpensSectionsEquiv G U).injective
      ((bigOpensSectionsEquiv_bigOfHomMap _ U s).trans (bigApp_bigPresheafFunctor_map φ U s))

end OfHom

end Modules

/-- **`F ↦ F^a` is fully faithful.** Morphisms of `𝒪_S`-modules `F ⟶ G` correspond to
`𝒪`-linear morphisms `F^a ⟶ G^a` of presheaves of modules over the big structure sheaf. -/
noncomputable def bigPresheafFunctorFullyFaithful (S : Scheme.{u}) :
    (bigPresheafFunctor S).FullyFaithful where
  preimage := Modules.bigOfHom
  map_preimage := Modules.bigPresheafFunctor_map_bigOfHom
  preimage_map := Modules.bigOfHom_bigPresheafFunctor_map

instance full_bigPresheafFunctor (S : Scheme.{u}) : (bigPresheafFunctor S).Full :=
  (bigPresheafFunctorFullyFaithful S).full

instance faithful_bigPresheafFunctor (S : Scheme.{u}) : (bigPresheafFunctor S).Faithful :=
  (bigPresheafFunctorFullyFaithful S).faithful

open TauCeti.AlgebraicGeometry in
/-- **`F ↦ F^a` is fully faithful on quasi-coherent modules** (Stacks, Lemma 35.8.8 (0GN7)):
morphisms of quasi-coherent `𝒪_S`-modules correspond to morphisms of the big-site modules. -/
@[stacks 0GN7 "Stated for the big fpqc site, whose modules are sheaves for every coarser topology
(`AlgebraicGeometry.Scheme.Modules.isSheaf_bigPresheaf_of_le`)."]
noncomputable def bigSheafFunctorFullyFaithful (S : Scheme.{u}) :
    (bigSheafFunctor S).FullyFaithful where
  preimage ψ := ObjectProperty.homMk (Modules.bigOfHom ψ.val)
  map_preimage ψ := SheafOfModules.Hom.ext (Modules.bigPresheafFunctor_map_bigOfHom ψ.val)
  preimage_map φ := by
    ext : 1
    exact Modules.bigOfHom_bigPresheafFunctor_map φ.hom

instance full_bigSheafFunctor (S : Scheme.{u}) : (bigSheafFunctor S).Full :=
  (bigSheafFunctorFullyFaithful S).full

instance faithful_bigSheafFunctor (S : Scheme.{u}) : (bigSheafFunctor S).Faithful :=
  (bigSheafFunctorFullyFaithful S).faithful

end AlgebraicGeometry.Scheme

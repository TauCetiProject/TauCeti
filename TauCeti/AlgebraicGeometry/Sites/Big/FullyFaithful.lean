/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Big.Sheaf
public import TauCeti.AlgebraicGeometry.Sites.Big.SmallZariski

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
`Γ(U, ι_U^* F)` are the sections `Γ(F, U)` (`AlgebraicGeometry.Scheme.Modules.bigOfHom`, through
`AlgebraicGeometry.Scheme.Modules.bigPresheafOpensAddEquiv`). To see that `ψ` is `φ^a` over an
arbitrary `S`-scheme `(T, h)`, `ψ` is first restricted to a morphism of `𝒪_T`-modules
`h^* F ⟶ h^* G` (`AlgebraicGeometry.Scheme.Modules.bigRestrictHom`), acting on the sections over
an open `W` of `T` through the `S`-scheme `W` (`AlgebraicGeometry.Scheme.Modules.bigOpenEquiv`).
A morphism out of `h^* F` is determined by its values on the pullbacks of sections of `F`
(`Scheme.Modules.pullback_hom_ext`), and on those both morphisms are computed by `ψ` on the open
subschemes of `S`. No quasi-coherence is needed for this argument.

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

variable {S : Scheme.{u}} {F G : S.Modules} (ψ : F.bigPresheaf ⟶ G.bigPresheaf)

section Restrict

variable (T : Over S)

/-- The map on sections over an open `W` of `T` of the morphism `h^* F ⟶ h^* G` induced by `ψ`:
apply `ψ` on the `S`-scheme `W`. -/
private noncomputable def bigRestrictMap (W : T.left.Opens) (s : Γ((pullback T.hom).obj F, W)) :
    Γ((pullback T.hom).obj G, W) :=
  (bigOpenEquiv G T W).symm (ψ.app (op (Over.mk (W.ι ≫ T.hom))) (bigOpenEquiv F T W s))

private lemma bigOpenEquiv_bigRestrictMap (W : T.left.Opens)
    (s : Γ((pullback T.hom).obj F, W)) :
    bigOpenEquiv G T W (bigRestrictMap ψ T W s) =
      ψ.app (op (Over.mk (W.ι ≫ T.hom))) (bigOpenEquiv F T W s) :=
  Equiv.apply_symm_apply _ _

private lemma bigRestrictMap_add (W : T.left.Opens) (s s' : Γ((pullback T.hom).obj F, W)) :
    bigRestrictMap ψ T W (s + s') = bigRestrictMap ψ T W s + bigRestrictMap ψ T W s' :=
  (bigOpenEquiv G T W).injective (by
    rw [bigOpenEquiv_add, bigOpenEquiv_bigRestrictMap, bigOpenEquiv_bigRestrictMap,
      bigOpenEquiv_bigRestrictMap, bigOpenEquiv_add]
    exact (ψ.app _).hom.map_add _ _)

private lemma bigRestrictMap_smul (W : T.left.Opens) (r : Γ(T.left, W))
    (s : Γ((pullback T.hom).obj F, W)) :
    bigRestrictMap ψ T W (r • s) = r • bigRestrictMap ψ T W s :=
  (bigOpenEquiv G T W).injective (by
    rw [bigOpenEquiv_smul, bigOpenEquiv_bigRestrictMap, bigOpenEquiv_bigRestrictMap,
      bigOpenEquiv_smul]
    exact (ψ.app _).hom.map_smul _ _)

private lemma bigRestrictMap_map {W W' : T.left.Opens} (hW : W' ≤ W)
    (s : Γ((pullback T.hom).obj F, W)) :
    bigRestrictMap ψ T W' (((pullback T.hom).obj F).presheaf.map (homOfLE hW).op s) =
      ((pullback T.hom).obj G).presheaf.map (homOfLE hW).op (bigRestrictMap ψ T W s) :=
  (bigOpenEquiv G T W').injective (by
    let f : Over.mk (W'.ι ≫ T.hom) ⟶ Over.mk (W.ι ≫ T.hom) :=
      Over.homMk (T.left.homOfLE hW) (by simp)
    have e (M : S.Modules) (x : Γ((pullback T.hom).obj M, W)) :
        M.bigPresheaf.map f.op (bigOpenEquiv M T W x) =
          bigOpenEquiv M T W' (((pullback T.hom).obj M).presheaf.map (homOfLE hW).op x) := by
      rw [bigPresheaf_map_apply, bigOpenEquiv_apply, bigOpenEquiv_apply]
      exact bigSectionsRestrict_homMk_homOfLE M T hW rfl rfl x
    rw [bigOpenEquiv_bigRestrictMap, ← e, ← e, bigOpenEquiv_bigRestrictMap]
    exact PresheafOfModules.naturality_apply ψ f.op _)

/-- The morphism of `𝒪_T`-modules `h^* F ⟶ h^* G` induced by `ψ : F^a ⟶ G^a` over an `S`-scheme
`(T, h)`: on sections over an open `W` of `T` it is `ψ` on the `S`-scheme `W`
(`bigOpenEquiv_bigRestrictHom_app`). -/
noncomputable def bigRestrictHom : (pullback T.hom).obj F ⟶ (pullback T.hom).obj G :=
  ⟨PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom (AddMonoidHom.mk' (bigRestrictMap ψ T W.unop)
        (bigRestrictMap_add ψ T W.unop))
      naturality _ _ i := by
        ext s
        exact bigRestrictMap_map ψ T i.unop.le s }
    fun W r s ↦ bigRestrictMap_smul ψ T W.unop r s⟩

/-- On sections over an open `W` of `T`, the restriction of `ψ` to `(T, h)` is `ψ` on the
`S`-scheme `W`. -/
@[simp]
lemma bigOpenEquiv_bigRestrictHom_app (W : T.left.Opens) (s : Γ((pullback T.hom).obj F, W)) :
    bigOpenEquiv G T W ((bigRestrictHom ψ T).app W s) =
      ψ.app (op (Over.mk (W.ι ≫ T.hom))) (bigOpenEquiv F T W s) :=
  bigOpenEquiv_bigRestrictMap ψ T W s

/-- On global sections, the restriction of `ψ` to `(T, h)` is `ψ` on `(T, h)`. -/
@[simp]
lemma bigRestrictHom_app_top (s : Γ((pullback T.hom).obj F, ⊤)) :
    (bigRestrictHom ψ T).app ⊤ s = ψ.app (op T) s := by
  apply (bigOpenEquiv G T ⊤).injective
  let ι : Over.mk ((⊤ : T.left.Opens).ι ≫ T.hom) ⟶ T := Over.homMk (⊤ : T.left.Opens).ι
  have e (M : S.Modules) (x : Γ((pullback T.hom).obj M, ⊤)) :
      M.bigPresheaf.map ι.op x = bigOpenEquiv M T ⊤ x := by
    rw [bigPresheaf_map_apply, bigSectionsRestrict_homMk_ι, bigOpenEquiv_apply]
    congr 1
    exact congr($(((pullback T.hom).obj M).presheaf.map_id (op ⊤)) x)
  rw [bigOpenEquiv_bigRestrictHom_app, ← e F s]
  exact (PresheafOfModules.naturality_apply ψ ι.op s).trans (e G _)

/-- The restriction of `ψ` to `(T, h)` on the pullback of a section `s` of `F` over `U`: it is
`ψ` applied to `s` on the `S`-scheme `U`, restricted to `h⁻¹ U`. -/
lemma bigOpenEquiv_bigRestrictHom_pullbackSections (U : S.Opens) (s : Γ(F, U)) :
    bigOpenEquiv G T (T.hom ⁻¹ᵁ U)
        ((bigRestrictHom ψ T).app (T.hom ⁻¹ᵁ U) (T.hom.pullbackSections F U s)) =
      G.bigPresheaf.map (bigPreimageHom T U).op
        (ψ.app (op (Over.mk U.ι)) (F.bigPresheafOpensAddEquiv U s)) := by
  rw [bigOpenEquiv_bigRestrictHom_app, bigOpenEquiv_pullbackSections, ← bigPresheaf_map_apply]
  exact PresheafOfModules.naturality_apply ψ _ _

end Restrict

/-- If `ψ : F^a ⟶ G^a` agrees with `φ : F ⟶ G` on the open subschemes of `S`, then `ψ = φ^a`. -/
theorem bigPresheafFunctor_map_eq (φ : F ⟶ G)
    (h : ∀ (U : S.Opens) (s : Γ(F, U)),
      ψ.app (op (Over.mk U.ι)) (F.bigPresheafOpensAddEquiv U s) =
        G.bigPresheafOpensAddEquiv U (φ.app U s)) :
    (bigPresheafFunctor S).map φ = ψ := by
  have key (T : Over S) : bigRestrictHom ψ T = (pullback T.hom).map φ := by
    refine pullback_hom_ext fun U s ↦ (bigOpenEquiv G T (T.hom ⁻¹ᵁ U)).injective ?_
    rw [bigOpenEquiv_bigRestrictHom_pullbackSections, h, Hom.pullbackSections_naturality,
      bigOpenEquiv_pullbackSections, bigPresheaf_map_apply]
  ext ⟨T⟩ s
  exact (bigPresheafFunctor_map_app_apply φ T s).trans
    ((congr($(key T).app ⊤ s)).symm.trans (bigRestrictHom_app_top ψ T s))

section OfHom

/-- The map on sections over an open `U` of `S` of the morphism `F ⟶ G` induced by `ψ`. -/
private noncomputable def bigOfHomMap (U : S.Opens) (s : Γ(F, U)) : Γ(G, U) :=
  (G.bigPresheafOpensAddEquiv U).symm (ψ.app (op (Over.mk U.ι)) (F.bigPresheafOpensAddEquiv U s))

private lemma bigPresheafOpensAddEquiv_bigOfHomMap (U : S.Opens) (s : Γ(F, U)) :
    G.bigPresheafOpensAddEquiv U (bigOfHomMap ψ U s) =
      ψ.app (op (Over.mk U.ι)) (F.bigPresheafOpensAddEquiv U s) :=
  AddEquiv.apply_symm_apply _ _

private lemma bigOfHomMap_add (U : S.Opens) (s s' : Γ(F, U)) :
    bigOfHomMap ψ U (s + s') = bigOfHomMap ψ U s + bigOfHomMap ψ U s' :=
  (G.bigPresheafOpensAddEquiv U).injective (by
    simp only [map_add, bigPresheafOpensAddEquiv_bigOfHomMap]
    exact (ψ.app _).hom.map_add _ _)

private lemma bigOfHomMap_smul (U : S.Opens) (r : Γ(S, U)) (s : Γ(F, U)) :
    bigOfHomMap ψ U (r • s) = r • bigOfHomMap ψ U s :=
  (G.bigPresheafOpensAddEquiv U).injective (by
    rw [bigPresheafOpensAddEquiv_smul, bigPresheafOpensAddEquiv_bigOfHomMap,
      bigPresheafOpensAddEquiv_bigOfHomMap, bigPresheafOpensAddEquiv_smul]
    exact (ψ.app _).hom.map_smul _ _)

private lemma bigOfHomMap_map {U U' : S.Opens} (hU : U' ≤ U) (s : Γ(F, U)) :
    bigOfHomMap ψ U' (F.presheaf.map (homOfLE hU).op s) =
      G.presheaf.map (homOfLE hU).op (bigOfHomMap ψ U s) :=
  (G.bigPresheafOpensAddEquiv U').injective (by
    rw [bigPresheafOpensAddEquiv_bigOfHomMap, ← bigPresheaf_map_bigPresheafOpensAddEquiv,
      ← bigPresheaf_map_bigPresheafOpensAddEquiv, bigPresheafOpensAddEquiv_bigOfHomMap]
    exact PresheafOfModules.naturality_apply ψ _ _)

/-- The morphism `F ⟶ G` induced by `ψ : F^a ⟶ G^a`: on sections over an open `U` of `S` it is
`ψ` on the `S`-scheme `U` (`bigPresheafOpensAddEquiv_bigOfHom_app`). -/
noncomputable def bigOfHom : F ⟶ G :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk' (bigOfHomMap ψ U.unop)
        (bigOfHomMap_add ψ U.unop))
      naturality _ _ i := by
        ext s
        exact bigOfHomMap_map ψ i.unop.le s }
    fun U r s ↦ bigOfHomMap_smul ψ U.unop r s⟩

/-- On sections over an open `U` of `S`, the morphism induced by `ψ` is `ψ` on the `S`-scheme
`U`. -/
@[simp]
lemma bigPresheafOpensAddEquiv_bigOfHom_app (U : S.Opens) (s : Γ(F, U)) :
    G.bigPresheafOpensAddEquiv U ((bigOfHom ψ).app U s) =
      ψ.app (op (Over.mk U.ι)) (F.bigPresheafOpensAddEquiv U s) :=
  bigPresheafOpensAddEquiv_bigOfHomMap ψ U s

/-- **`(bigOfHom ψ)^a = ψ`.** Every `𝒪`-linear morphism `F^a ⟶ G^a` comes from a morphism of
`𝒪_S`-modules. -/
@[simp]
theorem bigPresheafFunctor_map_bigOfHom : (bigPresheafFunctor S).map (bigOfHom ψ) = ψ :=
  bigPresheafFunctor_map_eq ψ _ fun U s ↦ (bigPresheafOpensAddEquiv_bigOfHom_app ψ U s).symm

/-- The morphism induced by `φ^a` is `φ`. -/
@[simp]
theorem bigOfHom_bigPresheafFunctor_map (φ : F ⟶ G) :
    bigOfHom ((bigPresheafFunctor S).map φ) = φ :=
  Scheme.Modules.hom_ext _ _ fun U ↦ by
    ext s
    apply (G.bigPresheafOpensAddEquiv U).injective
    refine (bigPresheafOpensAddEquiv_bigOfHom_app _ U s).trans ?_
    exact (bigPresheafFunctor_map_app_apply φ _ _).trans (bigPresheafOpensAddEquiv_naturality φ U s)

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

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
an open `W` of `T` through the `S`-scheme `W` (`AlgebraicGeometry.Scheme.Modules.bigOpenAddEquiv`).
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

section Transport

/-! Both morphisms induced by `ψ` are built the same way: the sections over each open `W` of a
scheme `X` are additively identified, by `e`, with the big-site sections over an `S`-scheme `O W`,
compatibly with scalars and restriction, and `ψ` on `O W` is transported along `e`. -/

variable {X : Scheme.{u}} (P : S.Modules → X.Modules) (O : X.Opens → Over S)
  (e : ∀ (M : S.Modules) (W : X.Opens), Γ(P M, W) ≃+ Γ((pullback (O W).hom).obj M, ⊤))

/-- The map on sections over an open `W` of `X` obtained by conjugating `ψ` on `O W` with `e`. -/
private noncomputable def transportMap (W : X.Opens) : Γ(P F, W) →+ Γ(P G, W) :=
  (e G W).symm.toAddMonoidHom.comp
    ((ψ.app (op (O W))).hom.toAddMonoidHom.comp (e F W).toAddMonoidHom)

private lemma apply_transportMap (W : X.Opens) (s : Γ(P F, W)) :
    e G W (transportMap ψ P O e W s) = ψ.app (op (O W)) (e F W s) :=
  AddEquiv.apply_symm_apply _ _

variable (ρ : ∀ {W' W : X.Opens}, W' ≤ W → (O W' ⟶ O W))
  (σ : ∀ W : X.Opens, Γ(X, W) → Γ((O W).left, ⊤))
  (he_smul : ∀ (M : S.Modules) (W : X.Opens) (r : Γ(X, W)) (s : Γ(P M, W)),
    e M W (r • s) = σ W r • e M W s)
  (he_map : ∀ (M : S.Modules) {W' W : X.Opens} (h : W' ≤ W) (s : Γ(P M, W)),
    M.bigPresheaf.map (ρ h).op (e M W s) = e M W' ((P M).presheaf.map (homOfLE h).op s))

include he_smul in
private lemma transportMap_smul (W : X.Opens) (r : Γ(X, W)) (s : Γ(P F, W)) :
    transportMap ψ P O e W (r • s) = r • transportMap ψ P O e W s :=
  (e G W).injective (by
    rw [apply_transportMap, he_smul, he_smul, apply_transportMap]
    exact (ψ.app _).hom.map_smul _ _)

include he_map in
private lemma transportMap_map {W W' : X.Opens} (h : W' ≤ W) (s : Γ(P F, W)) :
    transportMap ψ P O e W' ((P F).presheaf.map (homOfLE h).op s) =
      (P G).presheaf.map (homOfLE h).op (transportMap ψ P O e W s) :=
  (e G W').injective (by
    rw [apply_transportMap, ← he_map F h, ← he_map G h, apply_transportMap]
    exact PresheafOfModules.naturality_apply ψ (ρ h).op _)

/-- The morphism `P F ⟶ P G` of `𝒪_X`-modules obtained by transporting `ψ` along identifications
`e` that are compatible with scalars (through `σ`) and with restriction (through `ρ`). -/
private noncomputable def transportHom : P F ⟶ P G :=
  ⟨PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom (transportMap ψ P O e W.unop)
      naturality _ _ i := by
        ext s
        exact transportMap_map ψ P O e ρ he_map i.unop.le s }
    fun W r s ↦ transportMap_smul ψ P O e σ he_smul W.unop r s⟩

end Transport

section Restrict

variable (T : Over S)

/-- The morphism of `𝒪_T`-modules `h^* F ⟶ h^* G` induced by `ψ : F^a ⟶ G^a` over an `S`-scheme
`(T, h)`: on sections over an open `W` of `T` it is `ψ` on the `S`-scheme `W`
(`bigOpenAddEquiv_bigRestrictHom_app`). -/
noncomputable def bigRestrictHom : (pullback T.hom).obj F ⟶ (pullback T.hom).obj G :=
  transportHom ψ (fun M ↦ (pullback T.hom).obj M) (fun W ↦ Over.mk (W.ι ≫ T.hom))
    (fun M W ↦ bigOpenAddEquiv M T W) (fun hW ↦ Over.homMk (T.left.homOfLE hW) (by simp))
    (fun W ↦ (W.ι.appLE W ⊤ (by simp)).hom) (fun M W ↦ bigOpenAddEquiv_smul M T W)
    fun M _ _ hW s ↦ by
      rw [bigPresheaf_map_apply, bigOpenAddEquiv_apply, bigOpenAddEquiv_apply]
      exact bigSectionsRestrict_homMk_homOfLE M T hW rfl rfl s

/-- On sections over an open `W` of `T`, the restriction of `ψ` to `(T, h)` is `ψ` on the
`S`-scheme `W`. -/
@[simp]
lemma bigOpenAddEquiv_bigRestrictHom_app (W : T.left.Opens) (s : Γ((pullback T.hom).obj F, W)) :
    bigOpenAddEquiv G T W ((bigRestrictHom ψ T).app W s) =
      ψ.app (op (Over.mk (W.ι ≫ T.hom))) (bigOpenAddEquiv F T W s) :=
  apply_transportMap ψ (fun M ↦ (pullback T.hom).obj M) (fun W ↦ Over.mk (W.ι ≫ T.hom))
    (fun M W ↦ bigOpenAddEquiv M T W) W s

/-- On global sections, the restriction of `ψ` to `(T, h)` is `ψ` on `(T, h)`. -/
@[simp]
lemma bigRestrictHom_app_top (s : Γ((pullback T.hom).obj F, ⊤)) :
    (bigRestrictHom ψ T).app ⊤ s = ψ.app (op T) s := by
  apply (bigOpenAddEquiv G T ⊤).injective
  let ι : Over.mk ((⊤ : T.left.Opens).ι ≫ T.hom) ⟶ T := Over.homMk (⊤ : T.left.Opens).ι
  have e (M : S.Modules) (x : Γ((pullback T.hom).obj M, ⊤)) :
      M.bigPresheaf.map ι.op x = bigOpenAddEquiv M T ⊤ x := by
    rw [bigPresheaf_map_apply, bigSectionsRestrict_homMk_ι, bigOpenAddEquiv_apply]
    congr 1
    rw [Subsingleton.elim (homOfLE le_top) (𝟙 (⊤ : T.left.Opens)), op_id,
      CategoryTheory.Functor.map_id, AddCommGrpCat.id_apply]
  rw [bigOpenAddEquiv_bigRestrictHom_app, ← e F s]
  exact (PresheafOfModules.naturality_apply ψ ι.op s).trans (e G _)

/-- The restriction of `ψ` to `(T, h)` on the pullback of a section `s` of `F` over `U`: it is
`ψ` applied to `s` on the `S`-scheme `U`, restricted to `h⁻¹ U`. -/
lemma bigOpenAddEquiv_bigRestrictHom_pullbackSections (U : S.Opens) (s : Γ(F, U)) :
    bigOpenAddEquiv G T (T.hom ⁻¹ᵁ U)
        ((bigRestrictHom ψ T).app (T.hom ⁻¹ᵁ U) (T.hom.pullbackSections F U s)) =
      G.bigPresheaf.map (bigPreimageHom T U).op
        (ψ.app (op (Over.mk U.ι)) (F.bigPresheafOpensAddEquiv U s)) := by
  rw [bigOpenAddEquiv_bigRestrictHom_app, bigOpenAddEquiv_pullbackSections, ← bigPresheaf_map_apply]
  exact PresheafOfModules.naturality_apply ψ _ _

end Restrict

/-- If `ψ : F^a ⟶ G^a` agrees with `φ : F ⟶ G` on the open subschemes of `S`, then `ψ = φ^a`. -/
theorem bigPresheafFunctor_map_eq (φ : F ⟶ G)
    (h : ∀ (U : S.Opens) (s : Γ(F, U)),
      ψ.app (op (Over.mk U.ι)) (F.bigPresheafOpensAddEquiv U s) =
        G.bigPresheafOpensAddEquiv U (φ.app U s)) :
    (bigPresheafFunctor S).map φ = ψ := by
  have key (T : Over S) : bigRestrictHom ψ T = (pullback T.hom).map φ := by
    refine pullback_hom_ext fun U s ↦ (bigOpenAddEquiv G T (T.hom ⁻¹ᵁ U)).injective ?_
    rw [bigOpenAddEquiv_bigRestrictHom_pullbackSections, h, Hom.pullbackSections_naturality,
      bigOpenAddEquiv_pullbackSections, bigPresheaf_map_apply]
  ext ⟨T⟩ s
  exact (bigPresheafFunctor_map_app_apply φ T s).trans
    ((congr($(key T).app ⊤ s)).symm.trans (bigRestrictHom_app_top ψ T s))

section OfHom

/-- The morphism `F ⟶ G` induced by `ψ : F^a ⟶ G^a`: on sections over an open `U` of `S` it is
`ψ` on the `S`-scheme `U` (`bigPresheafOpensAddEquiv_bigOfHom_app`). -/
noncomputable def bigOfHom : F ⟶ G :=
  transportHom ψ (fun M ↦ M) (fun U ↦ Over.mk U.ι) bigPresheafOpensAddEquiv
    (fun hU ↦ Over.homMk (S.homOfLE hU) (by simp)) (fun U ↦ (U.ι.appLE U ⊤ (by simp)).hom)
    bigPresheafOpensAddEquiv_smul fun M _ _ hU s ↦ bigPresheaf_map_bigPresheafOpensAddEquiv M hU s

/-- On sections over an open `U` of `S`, the morphism induced by `ψ` is `ψ` on the `S`-scheme
`U`. -/
@[simp]
lemma bigPresheafOpensAddEquiv_bigOfHom_app (U : S.Opens) (s : Γ(F, U)) :
    G.bigPresheafOpensAddEquiv U ((bigOfHom ψ).app U s) =
      ψ.app (op (Over.mk U.ι)) (F.bigPresheafOpensAddEquiv U s) :=
  apply_transportMap ψ (fun M ↦ M) (fun U ↦ Over.mk U.ι) bigPresheafOpensAddEquiv U s

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

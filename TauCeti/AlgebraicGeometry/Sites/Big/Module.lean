/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.Modules.Sections
public import TauCeti.AlgebraicGeometry.Sites.Big.StructureSheaf

/-!
# The presheaf of modules of a module on the big site

Let `S` be a scheme and `F` an `𝒪_S`-module. On the big site `Over S`, the assignment
`(T, h) ↦ Γ(T, h^* F)` is a presheaf of modules over the big structure sheaf
`T ↦ Γ(T, 𝒪_T)` (`AlgebraicGeometry.Scheme.bigRingCatSheaf`): a morphism `f : T ⟶ T'` of
`S`-schemes pulls a section of `h'^* F` back to a section of `f^* h'^* F ≅ h^* F`, and this is
semilinear along `f^♯ : Γ(T', 𝒪) ⟶ Γ(T, 𝒪)`. For quasi-coherent `F` this is the presheaf of
modules underlying the big-site module `F^a` (Stacks, Section 35.8), whose sheaf property for the
fpqc topology is Stacks, Lemma 35.8.1; that sheaf property is not proved in this file.

The restriction maps are compatible with identities and composition because global sections of
`h^* F` are morphisms `h^* 𝒪_S ⟶ h^* F` (`AlgebraicGeometry.Scheme.Modules.bigSectionsEquiv`),
and under this identification restriction is the pullback of morphisms that Mathlib's
`CategoryTheory.Pseudofunctor.presheafHom` performs for the pullback pseudofunctor of modules
(`AlgebraicGeometry.Scheme.Modules.bigSectionsEquiv_bigSectionsRestrict`). The underlying
presheaf of sets is therefore Mathlib's presheaf of morphisms from `𝒪_S` to `F`
(`AlgebraicGeometry.Scheme.Modules.bigPresheafCompForgetIso`). So for a topology for which the
pseudofunctor is a prestack, this presheaf of sets is a sheaf.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.bigSectionsRestrict`: the semilinear restriction map
  `Γ(T', h'^* F) ⟶ Γ(T, h^* F)` along a morphism of `S`-schemes.
* `AlgebraicGeometry.Scheme.Modules.bigPresheaf`: the presheaf of modules
  `(T, h) ↦ Γ(T, h^* F)` over `bigRingCatSheaf S`.
* `AlgebraicGeometry.Scheme.bigPresheafFunctor`: `F ↦ bigPresheaf F` as a functor on `𝒪_S`-modules.
* `AlgebraicGeometry.Scheme.Modules.bigPresheafCompForgetIso`: the underlying presheaf of sets
  is `Pseudofunctor.presheafHom` of the pullback pseudofunctor, from `𝒪_S` to `F`.

## References

* The Stacks Project, Section 35.8, *Quasi-coherent sheaves and topologies*, in particular
  [Lemma 35.8.8 (03DR)](https://stacks.math.columbia.edu/tag/03DR).
-/

public section

open CategoryTheory Limits Opposite MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme

open TauCeti.AlgebraicGeometry.Descent Pseudofunctor.LocallyDiscreteOpToCat

namespace Modules

variable {S : Scheme.{u}} (F : S.Modules)

/-- Global sections of the pullback `h^* F` to an `S`-scheme `(T, h)` are the morphisms
`h^* 𝒪_S ⟶ h^* F`, through `h^* 𝒪_S ≅ 𝒪_T` and `Hom(𝒪_T, h^* F) ≃ Γ(T, h^* F)`. -/
noncomputable def bigSectionsEquiv (T : Over S) :
    Γ((pullback T.hom).obj F, ⊤) ≃
      ((pullback T.hom).obj (𝟙_ S.Modules) ⟶ (pullback T.hom).obj F) :=
  ((pullback T.hom).obj F).unitHomEquivTop.symm.trans
    ((pullbackObjUnitIso T.hom).homFromEquiv).symm

/-- A morphism `h^* 𝒪_S ⟶ h^* F` corresponds to its value on the section `1`. -/
lemma bigSectionsEquiv_symm_apply (T : Over S)
    (φ : (pullback T.hom).obj (𝟙_ S.Modules) ⟶ (pullback T.hom).obj F) :
    (bigSectionsEquiv F T).symm φ =
      φ.app ⊤ ((pullbackObjUnitIso T.hom).inv.app ⊤ (1 : Γ(T.left, ⊤))) :=
  unitHomEquivTop_apply _ ((pullbackObjUnitIso T.hom).inv ≫ φ)

/-- The restriction map `Γ(T', h'^* F) ⟶ Γ(T, h^* F)` of the big site along a morphism
`f : T ⟶ T'` of `S`-schemes: pull a section back along `f` and identify
`f^* h'^* F ≅ (f ≫ h')^* F = h^* F`. It is semilinear along `f^♯ : Γ(T', 𝒪) ⟶ Γ(T, 𝒪)`. -/
noncomputable def bigSectionsRestrict {T T' : Over S} (f : T ⟶ T') :
    Γ((pullback T'.hom).obj F, ⊤) →ₛₗ[f.left.appTop.hom] Γ((pullback T.hom).obj F, ⊤) where
  toFun s := ((pullbackComp f.left T'.hom).hom.app F ≫ (pullbackCongr (Over.w f)).hom.app F).app ⊤
    (f.left.pullbackSections ((pullback T'.hom).obj F) ⊤ s)
  -- Pulled-back sections live over `f ⁻¹ᵁ ⊤`, which is `⊤` only by definition, so the two laws
  -- are assembled from those of `pullbackSections` and of the module map as terms.
  map_add' s s' := (congrArg (fun x ↦ ((pullbackComp f.left T'.hom).hom.app F ≫
      (pullbackCongr (Over.w f)).hom.app F).app ⊤ x) (map_add _ s s')).trans (map_add _ _ _)
  map_smul' r s := (congrArg (fun x ↦ ((pullbackComp f.left T'.hom).hom.app F ≫
      (pullbackCongr (Over.w f)).hom.app F).app ⊤ x) (map_smulₛₗ _ r s)).trans
        (Hom.app_smul _ _ _)

lemma bigSectionsRestrict_apply {T T' : Over S} (f : T ⟶ T')
    (s : Γ((pullback T'.hom).obj F, ⊤)) :
    bigSectionsRestrict F f s =
      ((pullbackComp f.left T'.hom).hom.app F ≫ (pullbackCongr (Over.w f)).hom.app F).app ⊤
        (f.left.pullbackSections ((pullback T'.hom).obj F) ⊤ s) :=
  (rfl)

/-- Under `bigSectionsEquiv`, restriction along `f` is the pullback of morphisms along `f.left`
performed by Mathlib's `Pseudofunctor.presheafHom` of the pullback pseudofunctor of modules. -/
lemma bigSectionsEquiv_bigSectionsRestrict {T T' : Over S} (f : T ⟶ T')
    (s : Γ((pullback T'.hom).obj F, ⊤)) :
    bigSectionsEquiv F T (bigSectionsRestrict F f s) =
      pullHom (F := modulesPseudofunctor) (bigSectionsEquiv F T' s) f.left T.hom T.hom := by
  refine (Equiv.eq_symm_apply _).mp ?_
  -- Both sides are values of `g^*` of the morphism `bigSectionsEquiv F T' s` on the unit section:
  -- on the right after identifying `pullHom` (`modulesPseudofunctor_pullHom`), on the left
  -- after writing `s` as the value of that morphism (`bigSectionsEquiv_symm_apply`).
  have hs := bigSectionsEquiv_symm_apply F T' (bigSectionsEquiv F T' s)
  rw [Equiv.symm_apply_apply] at hs
  have hu := (Hom.pullbackSections_comp_of_eq T'.hom (𝟙_ S.Modules) f.left (Over.w f)
    (1 : Γ(S, ⊤))).trans
    (congrArg (f.left.pullbackSections _ ⊤) (Hom.pullbackObjUnitIso_inv_app_one T'.hom).symm)
  rw [← Hom.pullbackObjUnitIso_inv_app_one] at hu
  have hn := Hom.pullbackSections_naturality f.left _ ⊤ (bigSectionsEquiv F T' s)
    ((pullbackObjUnitIso T'.hom).inv.app ⊤ (1 : Γ(T'.left, ⊤)))
  let C := (pullbackComp f.left T'.hom).hom.app F ≫ (pullbackCongr (Over.w f)).hom.app F
  refine (congrArg (fun x ↦ C.app ⊤ (f.left.pullbackSections _ ⊤ x)) hs).trans ?_
  refine (congrArg (fun x ↦ C.app ⊤ x) hn.symm).trans ?_
  refine (congrArg (fun x ↦ C.app ⊤ (((pullback f.left).map (bigSectionsEquiv F T' s)).app ⊤ x))
    hu.symm).trans ?_
  refine (bigSectionsEquiv_symm_apply F T ((pullbackCongr (Over.w f)).inv.app _ ≫
    (pullbackComp f.left T'.hom).inv.app _ ≫ (pullback f.left).map (bigSectionsEquiv F T' s) ≫
      C)).symm.trans ?_
  exact congrArg _ (modulesPseudofunctor_pullHom _ _ _ _ _ _).symm

@[simp]
lemma bigSectionsRestrict_id (T : Over S) (s : Γ((pullback T.hom).obj F, ⊤)) :
    bigSectionsRestrict F (𝟙 T) s = s :=
  (bigSectionsEquiv F T).injective ((bigSectionsEquiv_bigSectionsRestrict F (𝟙 T) s).trans
    (pullHom_id (F := modulesPseudofunctor) _))

lemma bigSectionsRestrict_comp {T T' T'' : Over S} (f : T ⟶ T') (g : T' ⟶ T'')
    (s : Γ((pullback T''.hom).obj F, ⊤)) :
    bigSectionsRestrict F (f ≫ g) s = bigSectionsRestrict F f (bigSectionsRestrict F g s) :=
  (bigSectionsEquiv F T).injective ((bigSectionsEquiv_bigSectionsRestrict F (f ≫ g) s).trans
    ((pullHom_pullHom (F := modulesPseudofunctor) _ g.left T'.hom T'.hom f.left T.hom
      T.hom).symm.trans
        (by rw [← bigSectionsEquiv_bigSectionsRestrict, ← bigSectionsEquiv_bigSectionsRestrict])))

variable {F} in
/-- Restriction on the big site commutes with the maps induced by a morphism of modules. -/
lemma bigSectionsRestrict_naturality {G : S.Modules} (φ : F ⟶ G) {T T' : Over S} (f : T ⟶ T')
    (s : Γ((pullback T'.hom).obj F, ⊤)) :
    bigSectionsRestrict G f (((pullback T'.hom).map φ).app ⊤ s) =
      ((pullback T.hom).map φ).app ⊤ (bigSectionsRestrict F f s) := by
  have h₁ := (pullbackComp f.left T'.hom).hom.naturality φ
  have h₂ := (pullbackCongr (Over.w f)).hom.naturality φ
  dsimp only [Functor.comp_map] at h₁ h₂
  have h : (pullback f.left).map ((pullback T'.hom).map φ) ≫
      (pullbackComp f.left T'.hom).hom.app G ≫ (pullbackCongr (Over.w f)).hom.app G =
      ((pullbackComp f.left T'.hom).hom.app F ≫ (pullbackCongr (Over.w f)).hom.app F) ≫
        (pullback T.hom).map φ := by
    rw [reassoc_of% h₁, h₂, Category.assoc]
  rw [bigSectionsRestrict_apply, bigSectionsRestrict_apply, ← Hom.pullbackSections_naturality]
  exact congr($(h).app ⊤ (f.left.pullbackSections _ ⊤ s))

/-- The presheaf of modules `(T, h) ↦ Γ(T, h^* F)` over the big structure sheaf of `S`, with
restriction maps `bigSectionsRestrict`. For quasi-coherent `F` it is the module `F^a` on the big
site of `S`. -/
-- Exposed so that the sections of `bigPresheaf F` over `(T, h)` are by definition `Γ(T, h^* F)`,
-- the module in which consumers state facts about them.
@[expose]
noncomputable def bigPresheaf : _root_.PresheafOfModules.{u} (bigRingCatSheaf S).obj where
  obj T := ((pullback T.unop.hom).obj F).val.obj (op ⊤)
  map f := ModuleCat.semilinearMapAddEquiv _ _ _ (bigSectionsRestrict F f.unop)
  map_id T := by
    ext s
    exact bigSectionsRestrict_id F T.unop s
  map_comp f g := by
    ext s
    exact bigSectionsRestrict_comp F g.unop f.unop s

lemma bigPresheaf_obj (T : Over S) :
    F.bigPresheaf.obj (op T) = ((pullback T.hom).obj F).val.obj (op ⊤) :=
  (rfl)

@[simp]
lemma bigPresheaf_map_apply {T T' : Over S} (f : T ⟶ T') (s : Γ((pullback T'.hom).obj F, ⊤)) :
    F.bigPresheaf.map f.op s = bigSectionsRestrict F f s :=
  (rfl)

/-- The underlying presheaf of sets of `bigPresheaf F` is Mathlib's presheaf of morphisms from
`𝒪_S` to `F` for the pullback pseudofunctor of modules, `T ↦ Hom(h^* 𝒪_S, h^* F)`. A topology for
which the pseudofunctor is a prestack therefore makes it a sheaf. -/
noncomputable def bigPresheafCompForgetIso :
    F.bigPresheaf.presheaf ⋙ CategoryTheory.forget AddCommGrpCat ≅
      modulesPseudofunctor.presheafHom (𝟙_ S.Modules) F :=
  NatIso.ofComponents (fun T ↦ (bigSectionsEquiv F T.unop).toIso) fun f ↦ by
    ext s
    exact bigSectionsEquiv_bigSectionsRestrict F f.unop s

lemma bigPresheafCompForgetIso_hom_app (T : Over S) (s : Γ((pullback T.hom).obj F, ⊤)) :
    (bigPresheafCompForgetIso F).hom.app (op T) s = bigSectionsEquiv F T s :=
  (rfl)

end Modules

/-- The functor `F ↦ bigPresheaf F` from `𝒪_S`-modules to presheaves of modules over the big
structure sheaf of `S`. A morphism `φ : F ⟶ G` acts on `Γ(T, h^* F)` through `h^* φ`. -/
-- Exposed, like `Modules.bigPresheaf`, so that its values are by definition `bigPresheaf F`.
@[expose]
noncomputable def bigPresheafFunctor (S : Scheme.{u}) :
    S.Modules ⥤ _root_.PresheafOfModules.{u} (bigRingCatSheaf S).obj where
  obj F := F.bigPresheaf
  map {F G} φ :=
    { app T := ((Modules.pullback T.unop.hom).map φ).val.app (op ⊤)
      naturality f := by
        ext s
        exact (Modules.bigSectionsRestrict_naturality φ f.unop s).symm }
  map_id F := by
    ext T s
    exact congr($((Modules.pullback T.unop.hom).map_id F).app ⊤ s)
  map_comp φ ψ := by
    ext T s
    exact congr($((Modules.pullback T.unop.hom).map_comp φ ψ).app ⊤ s)

@[simp]
lemma bigPresheafFunctor_obj (S : Scheme.{u}) (F : S.Modules) :
    (bigPresheafFunctor S).obj F = F.bigPresheaf :=
  (rfl)

@[simp]
lemma bigPresheafFunctor_map_app_apply {S : Scheme.{u}} {F G : S.Modules} (φ : F ⟶ G)
    (T : Over S) (s : Γ((Modules.pullback T.hom).obj F, ⊤)) :
    ((bigPresheafFunctor S).map φ).app (op T) s = ((Modules.pullback T.hom).map φ).app ⊤ s :=
  (rfl)

end AlgebraicGeometry.Scheme

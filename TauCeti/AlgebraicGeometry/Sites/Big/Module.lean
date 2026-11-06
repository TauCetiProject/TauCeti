/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Descent.QuasicoherentSheaf.Basic
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
fpqc topology is Stacks, Lemma 35.8.1; that sheaf property is not proved in this file (see
`TauCeti.AlgebraicGeometry.Sites.Big.Zariski` for the Zariski topology).

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
* `AlgebraicGeometry.Scheme.Modules.bigSectionsRestrictLE`: the restriction map of local sections
  `Γ(h^* F, U) ⟶ Γ(h'^* F, U')` along a morphism of `S`-schemes, which along the inclusion of an
  open `V` identifies sections over `V` with the global sections of the `S`-scheme `V`.
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

/-- The restriction map of local sections along a morphism `b : X' ⟶ X` of `S`-schemes, with
structure morphisms `h` and `h' = b ≫ h`: a section of `h^* F` over `U ⊆ X` is pulled back along
`b` to a section of `b^* h^* F` over `U' ⊆ b⁻¹ U` and then read in `h'^* F ≅ b^* h^* F`. On global
sections it is `bigSectionsRestrict` (`bigSectionsRestrict_eq_bigSectionsRestrictLE`), and along
the inclusion of an open `V` it identifies sections over `V` with the global sections of the
`S`-scheme `V` (`bijective_bigSectionsRestrictLE_ι`). -/
noncomputable def bigSectionsRestrictLE {X X' : Scheme.{u}} {h : X ⟶ S} {h' : X' ⟶ S}
    (b : X' ⟶ X) (w : b ≫ h = h') (U : X.Opens) (U' : X'.Opens) (hU : U' ≤ b ⁻¹ᵁ U)
    (s : Γ((pullback h).obj F, U)) : Γ((pullback h').obj F, U') :=
  ((pullbackComp b h).hom.app F ≫ (pullbackCongr w).hom.app F).app U'
    (b.pullbackSectionsLE ((pullback h).obj F) U U' hU s)

lemma bigSectionsRestrictLE_apply {X X' : Scheme.{u}} {h : X ⟶ S} {h' : X' ⟶ S}
    (b : X' ⟶ X) (w : b ≫ h = h') (U : X.Opens) (U' : X'.Opens) (hU : U' ≤ b ⁻¹ᵁ U)
    (s : Γ((pullback h).obj F, U)) :
    bigSectionsRestrictLE F b w U U' hU s =
      ((pullbackComp b h).hom.app F ≫ (pullbackCongr w).hom.app F).app U'
        (b.pullbackSectionsLE ((pullback h).obj F) U U' hU s) :=
  (rfl)

/-- On global sections, the local restriction map is the restriction map of the big site. -/
lemma bigSectionsRestrict_eq_bigSectionsRestrictLE {T T' : Over S} (f : T ⟶ T')
    (s : Γ((pullback T'.hom).obj F, ⊤)) :
    bigSectionsRestrict F f s = bigSectionsRestrictLE F f.left (Over.w f) ⊤ ⊤ (by simp) s := by
  rw [bigSectionsRestrict_apply, bigSectionsRestrictLE_apply]
  exact congrArg _ (Hom.pullbackSectionsLE_self _ _ _ s).symm

/-- Restricting a section to a smaller open before restricting it along `b` changes nothing. -/
lemma bigSectionsRestrictLE_map {X X' : Scheme.{u}} {h : X ⟶ S} {h' : X' ⟶ S}
    (b : X' ⟶ X) (w : b ≫ h = h') {U₀ U : X.Opens} (i : U₀ ⟶ U) (U' : X'.Opens)
    (hU₀ : U' ≤ b ⁻¹ᵁ U₀) (s : Γ((pullback h).obj F, U)) :
    bigSectionsRestrictLE F b w U₀ U' hU₀ (((pullback h).obj F).presheaf.map i.op s) =
      bigSectionsRestrictLE F b w U U' (hU₀.trans (b.preimage_mono i.le)) s :=
  congrArg (((pullbackComp b h).hom.app F ≫ (pullbackCongr w).hom.app F).app U')
    (Hom.pullbackSectionsLE_map b _ U U' _ i hU₀ s)

/-- Local restriction along a composite is the composite of the local restrictions. -/
lemma bigSectionsRestrictLE_comp {X X' X'' : Scheme.{u}} {h : X ⟶ S} {h' : X' ⟶ S}
    {h'' : X'' ⟶ S} (b : X' ⟶ X) (w : b ≫ h = h') (a : X'' ⟶ X') (w' : a ≫ h' = h'')
    (U : X.Opens) (U' : X'.Opens) (U'' : X''.Opens) (hU : U' ≤ b ⁻¹ᵁ U) (hU' : U'' ≤ a ⁻¹ᵁ U')
    (s : Γ((pullback h).obj F, U)) :
    bigSectionsRestrictLE F a w' U' U'' hU' (bigSectionsRestrictLE F b w U U' hU s) =
      bigSectionsRestrictLE F (a ≫ b) (by rw [Category.assoc, w, w']) U U''
        (by rw [Hom.comp_preimage]; exact hU'.trans (a.preimage_mono hU)) s := by
  subst w w'
  -- The identifications `a^* b^* h^* F ≅ (a ≫ b)^* h^* F ≅ ((a ≫ b) ≫ h)^* F` and
  -- `a^* b^* h^* F ≅ a^* (b ≫ h)^* F ≅ (a ≫ (b ≫ h))^* F` agree by associativity of pullback.
  have key : (pullbackComp a b).inv.app ((pullback h).obj F) ≫
      (pullback a).map ((pullbackComp b h).hom.app F ≫ (pullbackCongr rfl).hom.app F) ≫
        (pullbackComp a (b ≫ h)).hom.app F ≫ (pullbackCongr rfl).hom.app F =
      (pullbackComp (a ≫ b) h).hom.app F ≫
        (pullbackCongr (by rw [Category.assoc])).hom.app F := by
    simp [pullbackCongr, pullbackComp_inv_app_comp_pullback_map_pullbackComp_hom_app_assoc]
  have h₁ := Hom.pullbackSectionsLE_naturality a _ U' U'' hU'
    ((pullbackComp b h).hom.app F ≫ (pullbackCongr rfl).hom.app F)
    (b.pullbackSectionsLE ((pullback h).obj F) U U' hU s)
  have h₂ := Hom.pullbackSectionsLE_comp b ((pullback h).obj F) U a U' hU hU' s
  refine (congrArg (((pullbackComp a (b ≫ h)).hom.app F ≫
    (pullbackCongr rfl).hom.app F).app U'') (h₁.symm.trans (congrArg _ h₂.symm))).trans ?_
  exact congr($(key).app U'' _)

/-- Local restriction along equal morphisms agrees. -/
lemma bigSectionsRestrictLE_congr {X X' : Scheme.{u}} {h : X ⟶ S} {h' : X' ⟶ S}
    {b b' : X' ⟶ X} (hb : b = b') (w : b ≫ h = h') (U : X.Opens) (U' : X'.Opens)
    (hU : U' ≤ b ⁻¹ᵁ U) (s : Γ((pullback h).obj F, U)) :
    bigSectionsRestrictLE F b w U U' hU s =
      bigSectionsRestrictLE F b' (hb ▸ w) U U' (hb ▸ hU) s := by
  subst hb
  rfl

/-- Local restriction along the inclusion of an open `V` of `X` is a bijection from the sections
of `h^* F` over `V` to the global sections of the pullback of `F` to the `S`-scheme `V`. -/
lemma bijective_bigSectionsRestrictLE_ι {X : Scheme.{u}} (h : X ⟶ S) (V : X.Opens) :
    Function.Bijective (bigSectionsRestrictLE F V.ι rfl V ⊤ (by simp) :
      Γ((pullback h).obj F, V) → Γ((pullback (V.ι ≫ h)).obj F, ⊤)) :=
  (ConcreteCategory.bijective_of_isIso
    (((pullbackComp V.ι h).hom.app F ≫ (pullbackCongr rfl).hom.app F).app ⊤)).comp
      (bijective_pullbackSectionsLE_ι _ V ⊤ rfl)

/-- Restricting a global section to the `S`-scheme given by an open `V` is restricting it to `V`
and then identifying sections over `V` with global sections of `V`. -/
lemma bigSectionsRestrict_homMk_ι (T : Over S) (V : T.left.Opens)
    (y : Γ((pullback T.hom).obj F, ⊤)) :
    bigSectionsRestrict F (Over.homMk V.ι : Over.mk (V.ι ≫ T.hom) ⟶ T) y =
      bigSectionsRestrictLE F V.ι rfl V ⊤ (by simp)
        (((pullback T.hom).obj F).presheaf.map (homOfLE le_top).op y) := by
  rw [bigSectionsRestrict_eq_bigSectionsRestrictLE, bigSectionsRestrictLE_map]
  exact bigSectionsRestrictLE_congr F (Over.homMk_left _ _) _ _ _ _ _

/-- For opens `W ≤ V` of `T`, restriction from the `S`-scheme `V` to the `S`-scheme `W` is, under
the identifications of `bijective_bigSectionsRestrictLE_ι`, restriction of sections from `V` to
`W`. -/
lemma bigSectionsRestrict_homMk_homOfLE (T : Over S) {V W : T.left.Opens} (hWV : W ≤ V)
    (s : Γ((pullback T.hom).obj F, V)) :
    bigSectionsRestrict F (Over.homMk (T.left.homOfLE hWV) (by simp) :
        Over.mk (W.ι ≫ T.hom) ⟶ Over.mk (V.ι ≫ T.hom))
      (bigSectionsRestrictLE F V.ι rfl V ⊤ (by simp) s) =
      bigSectionsRestrictLE F W.ι rfl W ⊤ (by simp)
        (((pullback T.hom).obj F).presheaf.map (homOfLE hWV).op s) := by
  rw [bigSectionsRestrict_eq_bigSectionsRestrictLE, bigSectionsRestrictLE_comp]
  refine (bigSectionsRestrictLE_congr F (b' := W.ι) (by simp) _ _ _ _ _).trans ?_
  rw [bigSectionsRestrictLE_map]

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

/-- The restriction maps of the underlying presheaf of sets of `bigPresheaf F` are
`bigSectionsRestrict`. -/
lemma bigPresheaf_presheaf_comp_forget_map_apply {T T' : Over S} (f : T ⟶ T')
    (s : (F.bigPresheaf.presheaf ⋙ CategoryTheory.forget AddCommGrpCat).obj (op T')) :
    (F.bigPresheaf.presheaf ⋙ CategoryTheory.forget AddCommGrpCat).map f.op s =
      bigSectionsRestrict F f s :=
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

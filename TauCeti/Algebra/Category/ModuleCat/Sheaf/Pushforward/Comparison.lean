/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pushforward.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Sheafifying a sectionwise pushforward comparison

Let `F : C ⥤ D` be a continuous functor between sites, `S` and `R` sheaves of commutative
rings on `C` and `D`, and `φ : S ⟶ F_* R` a morphism of the underlying sheaves of rings. Many
endofunctors `T` of sheaves of modules, such as exterior and symmetric powers, are the
sheafification of a sectionwise endofunctor `P` of presheaves of modules. Given such
presentations `T_S` of `P_S` over `S` and `T_R` of `P_R` over `R`, a sectionwise comparison
`c : φ_* ⋙ P_S ⟶ P_R ⋙ φ_*` induces a natural comparison `T_S ∘ φ_* ⟶ φ_* ∘ T_R`: the transpose
along sheafification of `c` followed by the pushforward of the sheafification unit of `P_R M`.

The presentations are passed as identifications `T.obj M ≅ (P M)^#` together with the induced
formula for `T.map`, which is how `SheafOfModules.exteriorPower` and
`SheafOfModules.symmetricPower` are presented (`SheafOfModules.exteriorPowerIso`,
`SheafOfModules.exteriorPower_map`, and their symmetric-power counterparts).

## Main declarations

* `TauCeti.SheafOfModules.sheafifyPushforwardComparison`: the comparison
  `T_S ∘ φ_* ⟶ φ_* ∘ T_R`, determined on underlying presheaves by
  `unit_comp_forget_map_sheafifyPushforwardComparison_app`;
* `TauCeti.SheafOfModules.sheafifyPushforwardComparison_app_comp_pushforward_map`: the comparison
  is compatible with sheafified maps out of `T_S` and `T_R` whose sectionwise maps are compatible
  with `c`, as for the identifications of first exterior and symmetric powers with the module;
* `TauCeti.SheafOfModules.isIso_sheafifyPushforwardComparison`: the comparison is invertible
  when the sectionwise comparison is invertible and the functor of sites is cocontinuous.
-/

public section

open CategoryTheory

namespace TauCeti.SheafOfModules

universe u v₁ v₂ u₁ u₂

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : C ⥤ D} [F.IsContinuous J K] {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R))
  {TS : _root_.SheafOfModules.{u} (ringCatSheaf S) ⥤ _root_.SheafOfModules.{u} (ringCatSheaf S)}
  {PS : PresheafOfModulesOfCommRing.{u} S.obj ⥤ PresheafOfModulesOfCommRing.{u} S.obj}
  (eS : ∀ M, TS.obj M ≅
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf S).obj)).obj (PS.obj M.val))
  (hS : ∀ {M N} (f : M ⟶ N), TS.map f = (eS M).hom ≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf S).obj)).map (PS.map f.val) ≫ (eS N).inv)
  {TR : _root_.SheafOfModules.{u} (ringCatSheaf R) ⥤ _root_.SheafOfModules.{u} (ringCatSheaf R)}
  {PR : PresheafOfModulesOfCommRing.{u} R.obj ⥤ PresheafOfModulesOfCommRing.{u} R.obj}
  (eR : ∀ M, TR.obj M ≅
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj (PR.obj M.val))
  (hR : ∀ {M N} (f : M ⟶ N), TR.map f = (eR M).hom ≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map (PR.map f.val) ≫ (eR N).inv)
  (c : PresheafOfModulesOfCommRing.pushforward (commRingCatHom φ) ⋙ PS ⟶
    PR ⋙ PresheafOfModulesOfCommRing.pushforward (commRingCatHom φ))

/-- The presheaf map transposed to the sheafified comparison: the sectionwise comparison followed
by the pushforward of the sheafification unit of `P_R M`. -/
private def sheafifyPushforwardPresheafMap (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    PS.obj ((_root_.SheafOfModules.pushforward φ).obj M).val ⟶
      (_root_.SheafOfModules.forget _).obj ((_root_.SheafOfModules.pushforward φ).obj
        (TR.obj M)) :=
  c.app M.val ≫ (presheafPushforward φ).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
      (PR.obj M.val) ≫ (_root_.SheafOfModules.forget _).map (eR M).inv)

include hR in
omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private lemma sheafifyPushforwardPresheafMap_naturality
    {M N : _root_.SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ N) :
    PS.map ((_root_.SheafOfModules.pushforward φ).map f).val ≫
      sheafifyPushforwardPresheafMap φ eR c N =
    sheafifyPushforwardPresheafMap φ eR c M ≫
      (_root_.SheafOfModules.forget _).map ((_root_.SheafOfModules.pushforward φ).map
        (TR.map f)) := by
  -- Naturality of the sectionwise comparison moves `P f` past it; naturality of the
  -- sheafification unit (`hk`) then moves it past the unit of `P_R M`.
  have h := c.naturality f.val
  have hu := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.naturality
    (PR.map f.val)
  have hk : PR.map f.val ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
        (PR.obj N.val) ≫ (_root_.SheafOfModules.forget _).map (eR N).inv =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
        (PR.obj M.val) ≫ (_root_.SheafOfModules.forget _).map (eR M).inv) ≫
        (_root_.SheafOfModules.forget _).map (TR.map f) := by
    have e : (_root_.SheafOfModules.forget _).map (eR M).inv ≫
        (_root_.SheafOfModules.forget _).map (TR.map f) =
        (_root_.SheafOfModules.forget _).map ((PresheafOfModules.sheafification (𝟙 _)).map
          (PR.map f.val)) ≫ (_root_.SheafOfModules.forget _).map (eR N).inv := by
      rw [← Functor.map_comp, ← Functor.map_comp, hR, Iso.inv_hom_id_assoc]
    -- Reassociate by hand: the categories of presheaves of modules over `R.obj` and
    -- `(ringCatSheaf R).obj` agree only up to unfolding `sheafCompose`, which defeats `rw`.
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hu)).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e.symm).trans (Category.assoc _ _ _).symm))
  rw [sheafifyPushforwardPresheafMap, sheafifyPushforwardPresheafMap,
    forget_map_pushforward_map]
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h)).trans ?_
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    ((presheafPushforward φ).map_comp _ _).symm).trans ?_)
  refine (congrArg (fun g ↦ _ ≫ (presheafPushforward φ).map g) hk).trans ?_
  exact (congrArg (_ ≫ ·) ((presheafPushforward φ).map_comp _ _)).trans
    (Category.assoc _ _ _).symm

/-- The natural comparison `T_S (φ_* M) ⟶ φ_* (T_R M)` induced by a sectionwise comparison
`c : φ_* ⋙ P_S ⟶ P_R ⋙ φ_*`, for sheafified presentations `eS` of `T_S` and `eR` of `T_R`: the
transpose along sheafification of `c` followed by the pushforward of the sheafification unit. -/
def sheafifyPushforwardComparison :
    _root_.SheafOfModules.pushforward φ ⋙ TS ⟶ TR ⋙ _root_.SheafOfModules.pushforward φ where
  app M := (eS _).hom ≫
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).homEquiv _ _).symm
      (sheafifyPushforwardPresheafMap φ eR c M)
  naturality M N f := by
    rw [Functor.comp_map, Functor.comp_map, hS, Category.assoc, Category.assoc,
      Iso.inv_hom_id_assoc]
    -- Both sides are transposes along sheafification; compare the presheaf maps.
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)
    exact (congrArg (_ ≫ ·) ((adj.homEquiv_naturality_left_symm _ _).symm.trans
        ((congrArg _ (sheafifyPushforwardPresheafMap_naturality φ eR hR c f)).trans
          (adj.homEquiv_naturality_right_symm _ _)))).trans
      (Category.assoc _ _ _).symm

/-- On underlying presheaves, the sheafified comparison restricted along the sheafification unit
is the sectionwise comparison followed by the pushforward of the sheafification unit of `P_R M`.
This determines the comparison, by the universal property of sheafification. -/
@[reassoc]
theorem unit_comp_forget_map_sheafifyPushforwardComparison_app
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).unit.app
        (PS.obj ((_root_.SheafOfModules.pushforward φ).obj M).val) ≫
      (_root_.SheafOfModules.forget _).map
        ((eS ((_root_.SheafOfModules.pushforward φ).obj M)).inv ≫
          (sheafifyPushforwardComparison φ eS hS eR hR c).app M) =
    c.app M.val ≫ (presheafPushforward φ).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
        (PR.obj M.val) ≫ (_root_.SheafOfModules.forget _).map (eR M).inv) := by
  rw [sheafifyPushforwardComparison, Iso.inv_hom_id_assoc]
  exact ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).homEquiv_unit
    _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- The sheafified comparison is compatible with maps `fS : T_S (φ_* M) ⟶ φ_* M` and
`fR : T_R M ⟶ M` that are sheafifications of sectionwise maps `oS` and `oR` compatible with the
sectionwise comparison `c`. For instance, this identifies the comparison in degree one with the
identity, through the identifications of first exterior or symmetric powers with the module. -/
theorem sheafifyPushforwardComparison_app_comp_pushforward_map
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R))
    {fS : TS.obj ((_root_.SheafOfModules.pushforward φ).obj M) ⟶
      (_root_.SheafOfModules.pushforward φ).obj M} {fR : TR.obj M ⟶ M}
    {oS : PS.obj ((_root_.SheafOfModules.pushforward φ).obj M).val ⟶
      ((_root_.SheafOfModules.pushforward φ).obj M).val} {oR : PR.obj M.val ⟶ M.val}
    (hfS : (eS _).inv ≫ fS = (PresheafOfModules.sheafification (𝟙 (ringCatSheaf S).obj)).map oS ≫
      (sheafificationIso _ _).hom)
    (hfR : (eR M).inv ≫ fR = (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map oR ≫
      (sheafificationIso _ _).hom)
    (h : c.app M.val ≫ (PresheafOfModulesOfCommRing.pushforward (commRingCatHom φ)).map oR = oS) :
    (sheafifyPushforwardComparison φ eS hS eR hR c).app M ≫
      (_root_.SheafOfModules.pushforward φ).map fR = fS := by
  rw [← cancel_epi (eS ((_root_.SheafOfModules.pushforward φ).obj M)).inv]
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringCatSheaf S).obj)).homEquiv _ _).injective
  -- Compare the transposes along the sheafification map of `P_S (φ_* M)`: both are `oS`.
  have key : (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).unit.app
        (PS.obj ((_root_.SheafOfModules.pushforward φ).obj M).val) ≫
      ((eS _).inv ≫ (sheafifyPushforwardComparison φ eS hS eR hR c).app M).val ≫
        ((_root_.SheafOfModules.pushforward φ).map fR).val = oS := by
    let P := presheafPushforward φ
    -- The sectionwise comparison, typed as a morphism of presheaves of modules over
    -- `(ringCatSheaf S).obj` so that every composite below lives in one category.
    let c' : PS.obj ((_root_.SheafOfModules.pushforward φ).obj M).val ⟶ P.obj (PR.obj M.val) :=
      c.app M.val
    let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
      (PR.obj M.val)
    refine Eq.trans ?_ h
    calc
      _ = c' ≫ P.map (η ≫ (eR M).inv.val) ≫ P.map fR.val :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ P.map fR.val)
          (unit_comp_forget_map_sheafifyPushforwardComparison_app φ eS hS eR hR c M)).trans
            (Category.assoc _ _ _))
      _ = c' ≫ P.map (η ≫ ((eR M).inv ≫ fR).val) :=
        congrArg (c' ≫ ·) ((P.map_comp _ _).symm.trans (congrArg P.map (Category.assoc _ _ _)))
      _ = c' ≫ P.map oR :=
        (congrArg (fun g : (PresheafOfModules.sheafification
            (𝟙 (ringCatSheaf R).obj)).obj (PR.obj M.val) ⟶ M ↦ c' ≫ P.map (η ≫ g.val))
          hfR).trans (congrArg (fun g ↦ c' ≫ P.map g)
            (unit_comp_val_sheafification_map_comp_sheafificationIso_hom
              (R := ringCatSheaf R) oR))
  -- Transport both sides through the adjunction using their unit characterizations.
  refine (Adjunction.homEquiv_unit _ _ _ _).trans ?_
  refine key.trans ?_
  refine (unit_comp_val_sheafification_map_comp_sheafificationIso_hom
    (R := ringCatSheaf S) oS).symm.trans ?_
  rw [← hfS]
  exact (Adjunction.homEquiv_unit
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)) _ _
    ((eS ((_root_.SheafOfModules.pushforward φ).obj M)).inv ≫ fS)).symm

/-- Along a continuous and cocontinuous functor, sheafification carries an invertible
sectionwise pushforward comparison to an invertible comparison of sheaves of modules. -/
instance isIso_sheafifyPushforwardComparison [F.IsCocontinuous J K] [IsIso c] :
    IsIso (sheafifyPushforwardComparison φ eS hS eR hR c) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  let P := PR.obj M.val
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app P
  let L := PresheafOfModules.sheafification (𝟙 (ringCatSheaf S).obj)
  have hη : IsIso (L.map ((presheafPushforward φ).map η)) := by
    -- Sheafification inverts exactly the maps that are locally bijective on additive presheaves.
    change ((MorphismProperty.isomorphisms _).inverseImage L)
      ((presheafPushforward φ).map η)
    rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
    have eq : (PresheafOfModules.toPresheaf _).map ((presheafPushforward φ).map η) =
        Functor.whiskerLeft F.op (CategoryTheory.toSheafify K P.presheaf) := by
      have he := PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
        (𝟙 (ringCatSheaf R).obj) P
      exact congrArg (Functor.whiskerLeft F.op) he
    -- Evaluate the inverse-image morphism property before applying its section equation.
    change J.W ((PresheafOfModules.toPresheaf _).map ((presheafPushforward φ).map η))
    rw [eq]
    exact (J.W_iff_isLocallyBijective _).mpr
      ⟨Presheaf.isLocallyInjective_whisker J K F _,
        Presheaf.isLocallySurjective_whisker J K F _⟩
  have hc : IsIso (L.map (c.app M.val)) :=
    (L.mapIso ((asIso c).app M.val)).isIso_hom
  have he : IsIso (L.map ((presheafPushforward φ).map
      ((_root_.SheafOfModules.forget _).map (eR M).inv))) := by infer_instance
  dsimp only [η, P] at hη
  have hmap : IsIso (L.map (sheafifyPushforwardPresheafMap φ eR c M)) := by
    dsimp only [sheafifyPushforwardPresheafMap]
    erw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
    exact IsIso.comp_isIso' hc (IsIso.comp_isIso' hη he)
  dsimp only [L] at hmap
  -- The transpose is sheafification of the presheaf map followed by the counit.
  change IsIso ((eS _).hom ≫
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).homEquiv _ _).symm
      (sheafifyPushforwardPresheafMap φ eR c M))
  erw [Adjunction.homEquiv_counit]
  have hi : IsIso ((eS ((_root_.SheafOfModules.pushforward φ).obj M)).hom) := by infer_instance
  have hj : IsIso ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringCatSheaf S).obj)).counit.app
      ((_root_.SheafOfModules.pushforward φ).obj (TR.obj M))) := by infer_instance
  exact IsIso.comp_isIso' hi (IsIso.comp_isIso' hmap hj)

end

end TauCeti.SheafOfModules

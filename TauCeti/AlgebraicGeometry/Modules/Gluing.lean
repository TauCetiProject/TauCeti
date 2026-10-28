/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import TauCeti.AlgebraicGeometry.Scheme.LocallyDirected
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Gluing sheaves of modules along a locally directed diagram of open immersions

Let `F : J ⥤ Scheme` be a locally directed diagram of open immersions indexed by a small thin
category, so that its colimit is the scheme glued from the `F j` along the images of the
transition maps (`AlgebraicGeometry.Scheme.IsLocallyDirected.openCover`). Relative spectra and
relative `Proj` are glued in this way over the affine opens of the base.

A *gluing datum of modules* on `F` (`TauCeti.ModulesGlueData F`) is a sheaf of modules `Mⱼ` on
every `F j`, together with transition morphisms `Mⱼ ⟶ (F f)_* Mᵢ` for `f : i ⟶ j`, compatible with
identities and composition. Its *glued module* (`TauCeti.ModulesGlueData.glued`) is the module on
the colimit whose sections over an open `U` are the families of sections of the `Mⱼ` over the
preimages of `U` that are compatible under the transition morphisms: the limit of the
pushforwards `(ιⱼ)_* Mⱼ` along the inclusions `ιⱼ : F j ⟶ colimit F`.

When every transition morphism is bijective on the sections over opens inside the image of the
transition map, that is, when it identifies `Mᵢ` with the restriction of `Mⱼ` to `F i`, the glued
module restricts on each `F i` to `Mᵢ` (`TauCeti.ModulesGlueData.restrictGluedIso`). The proof
reconstructs a compatible family from one section of `Mᵢ`, gluing on each `F j` along the cover by
the images of the `F k` mapping to both `F i` and `F j`.

## Main definitions

* `TauCeti.ModulesGlueData F`: sheaves of modules on the `F j` with compatible transition maps.
* `TauCeti.ModulesGlueData.glued`: the glued module on `colimit F`.
* `TauCeti.ModulesGlueData.restrictGluedIso`: the restriction of the glued module to `F i` is
  `Mᵢ`.

## Main results

* `TauCeti.ModulesGlueData.bijective_π_app`: over an open inside the image of `F i`, the
  projection from the sections of the glued module to the sections of `Mᵢ` is bijective.

## References

* The Stacks Project, Section 6.33, Glueing sheaves.
* R. Hartshorne, *Algebraic Geometry*, Exercise II.1.22.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace TauCeti

universe u

/-- A **gluing datum of modules** on a diagram of schemes `F : J ⥤ Scheme`: a sheaf of modules
`Mⱼ` on each `F j`, with transition morphisms `Mⱼ ⟶ (F f)_* Mᵢ` for `f : i ⟶ j`, compatible with
identities and composition on sections. -/
structure ModulesGlueData {J : Type u} [SmallCategory J] (F : J ⥤ Scheme.{u}) where
  /-- The sheaf of modules on `F j`. -/
  obj (j : J) : (F.obj j).Modules
  /-- The transition morphism `Mⱼ ⟶ (F f)_* Mᵢ` along `f : i ⟶ j`. -/
  map {i j : J} (f : i ⟶ j) : obj j ⟶ (Scheme.Modules.pushforward (F.map f)).obj (obj i)
  /-- The transition morphism along an identity is the identity on sections, up to the
  restriction along `(F (𝟙 j))⁻¹ V = V`. -/
  map_id (j : J) (V : (F.obj j).Opens) (s : Γ(obj j, V)) :
    (obj j).presheaf.map (eqToHom (show V = F.map (𝟙 j) ⁻¹ᵁ V by rw [F.map_id]; rfl)).op
      ((map (𝟙 j)).app V s) = s
  /-- The transition morphisms are compatible with composition on sections, up to the restriction
  along `(F f)⁻¹ (F g)⁻¹ V = (F (f ≫ g))⁻¹ V`. -/
  map_comp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (V : (F.obj k).Opens) (s : Γ(obj k, V)) :
    (obj i).presheaf.map
        (eqToHom (show F.map f ⁻¹ᵁ F.map g ⁻¹ᵁ V = F.map (f ≫ g) ⁻¹ᵁ V by rw [F.map_comp]; rfl)).op
        ((map (f ≫ g)).app V s) =
      (map f).app (F.map g ⁻¹ᵁ V) ((map g).app V s)

namespace ModulesGlueData

noncomputable section

variable {J : Type u} [SmallCategory J] {F : J ⥤ Scheme.{u}} (D : ModulesGlueData F)
  [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)] [(F ⋙ Scheme.forget).IsLocallyDirected]
  [Quiver.IsThin J]

/-- The morphism `(ιⱼ)_* Mⱼ ⟶ (ιᵢ)_* Mᵢ` induced by the transition morphism of a gluing datum
along `f : i ⟶ j`, using `F f ≫ ιⱼ = ιᵢ`. -/
def transition {i j : J} (f : i ⟶ j) :
    (Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j) ⟶
      (Scheme.Modules.pushforward (colimit.ι F i)).obj (D.obj i) :=
  (Scheme.Modules.pushforward (colimit.ι F j)).map (D.map f) ≫
    (Scheme.Modules.pushforwardComp (F.map f) (colimit.ι F j)).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (colimit.w F f)).hom.app _

/-- On sections over `U`, the morphism induced by a transition morphism is the transition
morphism over `ιⱼ⁻¹ U` followed by the restriction along `(F f)⁻¹ ιⱼ⁻¹ U = ιᵢ⁻¹ U`. -/
theorem transition_app_apply {i j : J} (f : i ⟶ j) (U : (colimit F).Opens)
    (s : Γ((Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j), U)) :
    (D.transition f).app U s = (D.obj i).presheaf.map
      (eqToHom (show colimit.ι F i ⁻¹ᵁ U = F.map f ⁻¹ᵁ colimit.ι F j ⁻¹ᵁ U by
        rw [← colimit.w F f]; rfl)).op ((D.map f).app (colimit.ι F j ⁻¹ᵁ U) s) :=
  (rfl)

/-- The diagram of the pushforwards `(ιⱼ)_* Mⱼ` to `colimit F` of the modules of a gluing
datum, with the transition morphisms induced by those of the datum. -/
def diagram : Jᵒᵖ ⥤ (colimit F).Modules where
  obj j := (Scheme.Modules.pushforward (colimit.ι F j.unop)).obj (D.obj j.unop)
  map f := D.transition f.unop
  map_id j := by
    refine Scheme.Modules.hom_ext _ _ fun U ↦ ConcreteCategory.hom_ext _ _ fun s ↦ ?_
    rw [unop_id, transition_app_apply, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]
    conv_rhs => rw [← D.map_id j.unop _ s]
  map_comp {k j i} f g := by
    refine Scheme.Modules.hom_ext _ _ fun U ↦ ConcreteCategory.hom_ext _ _ fun s ↦ ?_
    have hnat := NatTrans.naturality_apply (D.map g.unop).mapPresheaf
      (X := op (F.map f.unop ⁻¹ᵁ colimit.ι F k.unop ⁻¹ᵁ U)) (Y := op (colimit.ι F j.unop ⁻¹ᵁ U))
      (eqToHom (show colimit.ι F j.unop ⁻¹ᵁ U = F.map f.unop ⁻¹ᵁ colimit.ι F k.unop ⁻¹ᵁ U by
        rw [← colimit.w F f.unop]; rfl)).op ((D.map f.unop).app (colimit.ι F k.unop ⁻¹ᵁ U) s)
    simp only [Scheme.Modules.mapPresheaf_app, unop_op] at hnat
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, unop_comp, transition_app_apply,
      transition_app_apply, transition_app_apply, hnat, Scheme.Modules.pushforward_obj_presheaf_map,
      ← D.map_comp g.unop f.unop (colimit.ι F k.unop ⁻¹ᵁ U) s]
    -- the restrictions are along equalities of opens, displayed in different forms
    erw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    rfl

/-- The composite of the morphisms induced by transition morphisms along `f : i ⟶ j` and
`g : j ⟶ k` is the morphism induced along `f ≫ g`. -/
theorem transition_comp_apply {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (U : (colimit F).Opens)
    (s : Γ((Scheme.Modules.pushforward (colimit.ι F k)).obj (D.obj k), U)) :
    (D.transition f).app U ((D.transition g).app U s) = (D.transition (f ≫ g)).app U s := by
  have := congr(Scheme.Modules.Hom.app $(D.diagram.map_comp g.op f.op) U)
  exact (ConcreteCategory.congr_hom this s).symm

/-- Over an open of `colimit F`, the morphisms induced by transition morphisms commute with the
restriction of sections. -/
theorem transition_app_map_apply {i j : J} (f : i ⟶ j) {U V : (colimit F).Opens} (h : V ≤ U)
    (s : Γ((Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j), U)) :
    (D.transition f).app V
        (((Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j)).presheaf.map (homOfLE h).op
          s) =
      ((Scheme.Modules.pushforward (colimit.ι F i)).obj (D.obj i)).presheaf.map (homOfLE h).op
        ((D.transition f).app U s) :=
  NatTrans.naturality_apply (D.transition f).mapPresheaf (homOfLE h).op s

/-- The **glued module** of a gluing datum of modules on `F`: the module on `colimit F` whose
sections over `U` are the compatible families of sections of the `Mⱼ` over the preimages
`ιⱼ⁻¹ U`, the limit of the pushforwards `(ιⱼ)_* Mⱼ`. -/
def glued : (colimit F).Modules :=
  limit D.diagram

/-- The projection from the glued module to the pushforward `(ιⱼ)_* Mⱼ`. -/
def π (j : J) : D.glued ⟶ (Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j) :=
  limit.π D.diagram (op j)

/-- The projections from the glued module are compatible with the transition morphisms. -/
@[reassoc (attr := simp)]
theorem π_transition {i j : J} (f : i ⟶ j) : D.π j ≫ D.transition f = D.π i :=
  limit.w D.diagram f.op

/-- The projections from the glued module are compatible with the transition morphisms, on
sections. -/
theorem transition_app_π_app {i j : J} (f : i ⟶ j) (U : (colimit F).Opens)
    (s : Γ(D.glued, U)) :
    (D.transition f).app U ((D.π j).app U s) = (D.π i).app U s :=
  ConcreteCategory.congr_hom congr(Scheme.Modules.Hom.app $(D.π_transition f) U) s

/-- The sections over `U` of the glued module are the limit of the sections over `U` of the
pushforwards `(ιⱼ)_* Mⱼ`. -/
private def isLimitSections (U : (colimit F).Opens) :=
  isLimitOfPreserves ((evaluation (colimit F).Opensᵒᵖ Ab.{u}).obj (op U))
    (isLimitOfPreserves (Scheme.Modules.toPresheaf _) (limit.isLimit D.diagram))

/-- Two sections of the glued module are equal if all their projections are. -/
theorem π_ext {U : (colimit F).Opens} {s t : Γ(D.glued, U)}
    (h : ∀ j, (D.π j).app U s = (D.π j).app U t) : s = t :=
  Concrete.isLimit_ext _ (D.isLimitSections U) s t fun j ↦ h j.unop

/-- A family of sections of the pushforwards `(ιⱼ)_* Mⱼ` over `U` compatible with the transition
morphisms is the family of projections of a section of the glued module. -/
theorem exists_π_app {U : (colimit F).Opens}
    (t : ∀ j, Γ((Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j), U))
    (ht : ∀ {i j : J} (f : i ⟶ j), (D.transition f).app U (t j) = t i) :
    ∃ s : Γ(D.glued, U), ∀ j, (D.π j).app U s = t j :=
  ⟨(Types.isLimitEquivSections (isLimitOfPreserves (forget _) (D.isLimitSections U))).symm
    ⟨fun j ↦ t j.unop, fun f ↦ ht f.unop⟩, fun j ↦
    Types.isLimitEquivSections_symm_apply (isLimitOfPreserves (forget _) (D.isLimitSections U)) _
      (op j)⟩

/-- Sections of `(ιⱼ)_* Mⱼ` over an open `U` contained in the image of `F i` agree if they agree
over the opens `U ⊓ ιₖ(F k)`, for `k` mapping to both `i` and `j`. -/
private theorem eq_of_restrict_eq {i j : J} {U : (colimit F).Opens}
    (hU : U ≤ (colimit.ι F i).opensRange)
    {x y : Γ((Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j), U)}
    (h : ∀ k : Σ k : J, (k ⟶ j) × (k ⟶ i),
      ((Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j)).presheaf.map
          (homOfLE (inf_le_left : U ⊓ (colimit.ι F k.1).opensRange ≤ U)).op x =
        ((Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j)).presheaf.map
          (homOfLE (inf_le_left : U ⊓ (colimit.ι F k.1).opensRange ≤ U)).op y) : x = y :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨(D.obj j).presheaf, (D.obj j).isSheaf⟩ : TopCat.Sheaf Ab _)
    (fun k : Σ k : J, (k ⟶ j) × (k ⟶ i) ↦
      colimit.ι F j ⁻¹ᵁ (U ⊓ (colimit.ι F k.1).opensRange))
    (colimit.ι F j ⁻¹ᵁ U) (fun _ ↦ homOfLE (Scheme.Hom.preimage_mono _ inf_le_left))
    (Scheme.IsLocallyDirected.preimage_le_iSup_preimage_inf_opensRange F hU) x y h

/-- The morphism from the restriction of the glued module to `F i` to `Mᵢ`, adjoint to the
projection `glued ⟶ (ιᵢ)_* Mᵢ` under the restriction–pushforward adjunction of `ιᵢ`. It is an
isomorphism when the transition morphisms are bijective over opens inside the images of the
transition maps (`TauCeti.ModulesGlueData.isIso_restrictGluedHom`). -/
def restrictGluedHom (i : J) : D.glued.restrict (colimit.ι F i) ⟶ D.obj i :=
  ((Scheme.Modules.restrictAdjunction (colimit.ι F i)).homEquiv _ _).symm (D.π i)

/-- On sections over `W`, the morphism from the restriction of the glued module to `Mᵢ` is the
projection over the image `ιᵢ(W)`, followed by the restriction along `ιᵢ⁻¹ ιᵢ(W) = W`. -/
theorem restrictGluedHom_app_apply (i : J) (W : (F.obj i).Opens)
    (s : Γ(D.glued.restrict (colimit.ι F i), W)) :
    (D.restrictGluedHom i).app W s = (D.obj i).presheaf.map
      (eqToHom ((colimit.ι F i).preimage_image_eq W).symm).op
        ((D.π i).app (colimit.ι F i ''ᵁ W) s) := by
  rw [restrictGluedHom, Adjunction.homEquiv_counit, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictAdjunction_counit_app_app]
  -- sections of the restriction along `ιᵢ` over `W` are sections over the image `ιᵢ(W)`
  rfl

section Bijective

variable (hD : ∀ {i j : J} (f : i ⟶ j) (V : (F.obj j).Opens), V ≤ (F.map f).opensRange →
  Function.Bijective ((D.map f).app V))
include hD

/-- If the transition morphisms of a gluing datum are bijective over opens inside the images of the
transition maps, so are the induced morphisms of pushforwards over opens inside the image of
`F i`. -/
theorem bijective_transition_app {i j : J} (f : i ⟶ j) {U : (colimit F).Opens}
    (hU : U ≤ (colimit.ι F i).opensRange) : Function.Bijective ((D.transition f).app U) := by
  have h := hD f (colimit.ι F j ⁻¹ᵁ U)
    ((Scheme.Hom.preimage_mono _ hU).trans (Scheme.IsLocallyDirected.preimage_opensRange_ι_le F f))
  rw [show ⇑((D.transition f).app U) = _ from funext (D.transition_app_apply f U)]
  exact (ConcreteCategory.bijective_of_isIso _).comp h

/-- Sections of `(ιⱼ)_* Mⱼ` over an open contained in the image of `F i` are determined by their
images under the transition morphisms along the `k ⟶ j` with `k` mapping to `i`. -/
private theorem eq_of_transition_app_eq {i j : J} {U : (colimit F).Opens}
    (hU : U ≤ (colimit.ι F i).opensRange)
    {x y : Γ((Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j), U)}
    (h : ∀ (k : J) (a : k ⟶ j), (k ⟶ i) → (D.transition a).app U x = (D.transition a).app U y) :
    x = y :=
  D.eq_of_restrict_eq hU fun k ↦ (D.bijective_transition_app hD k.2.1 inf_le_right).1 <| by
    rw [D.transition_app_map_apply, D.transition_app_map_apply, h k.1 k.2.1 k.2.2]

/-- A section `t` of `(ιᵢ)_* Mᵢ` over an open contained in the image of `F i` extends to a section
of `(ιⱼ)_* Mⱼ` with the same images under the transition morphisms to every `k` mapping to both
`i` and `j`. -/
private theorem exists_transition_app_eq {i j : J} {U : (colimit F).Opens}
    (hU : U ≤ (colimit.ι F i).opensRange)
    (t : Γ((Scheme.Modules.pushforward (colimit.ι F i)).obj (D.obj i), U)) :
    ∃ x : Γ((Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j), U),
      ∀ (k : J) (a : k ⟶ j) (b : k ⟶ i), (D.transition a).app U x = (D.transition b).app U t := by
  let V (k : Σ k : J, (k ⟶ j) × (k ⟶ i)) : (colimit F).Opens := U ⊓ (colimit.ι F k.1).opensRange
  let res {l : J} {W W' : (colimit F).Opens} (h : W' ≤ W) :=
    ((Scheme.Modules.pushforward (colimit.ι F l)).obj (D.obj l)).presheaf.map (homOfLE h).op
  -- over `V k`, the section is the preimage of `t` under the transition morphism along `k ⟶ j`
  let σ (k : Σ k : J, (k ⟶ j) × (k ⟶ i)) :=
    Function.surjInv (D.bijective_transition_app hD k.2.1 (U := V k) inf_le_right).2
      ((D.transition k.2.2).app (V k) (res inf_le_left t))
  have hσ₀ (k : Σ k : J, (k ⟶ j) × (k ⟶ i)) :
      (D.transition k.2.1).app (V k) (σ k) = (D.transition k.2.2).app (V k) (res inf_le_left t) :=
    Function.surjInv_eq _ _
  have hσ (k : Σ k : J, (k ⟶ j) × (k ⟶ i)) (l : J) (a : l ⟶ j) (b : l ⟶ i) :
      (D.transition a).app (V k) (σ k) = (D.transition b).app (V k) (res inf_le_left t) := by
    refine D.eq_of_transition_app_eq hD (i := k.1) inf_le_right fun l' c d ↦ ?_
    rw [transition_comp_apply, transition_comp_apply, Subsingleton.elim (c ≫ a) (d ≫ k.2.1),
      ← transition_comp_apply, hσ₀, transition_comp_apply, Subsingleton.elim (d ≫ k.2.2) (c ≫ b)]
  -- the local sections agree on overlaps
  have hcompat (k k' : Σ k : J, (k ⟶ j) × (k ⟶ i)) :
      res (inf_le_left : V k ⊓ V k' ≤ V k) (σ k) = res (inf_le_right : V k ⊓ V k' ≤ V k') (σ k') :=
    D.eq_of_transition_app_eq hD (inf_le_left.trans (inf_le_left.trans hU)) fun l a b ↦ by
      simp only [res, D.transition_app_map_apply, hσ _ l a b, ← Functor.map_comp_apply]
      rfl
  -- so they glue
  obtain ⟨x, hx, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨(D.obj j).presheaf, (D.obj j).isSheaf⟩ : TopCat.Sheaf Ab _)
    (fun k ↦ colimit.ι F j ⁻¹ᵁ V k) (colimit.ι F j ⁻¹ᵁ U)
    (fun _ ↦ homOfLE (Scheme.Hom.preimage_mono _ inf_le_left))
    (Scheme.IsLocallyDirected.preimage_le_iSup_preimage_inf_opensRange F hU) σ hcompat
  -- `x` is a section of `(ιⱼ)_* Mⱼ` over `U`, presented as a section of `Mⱼ` over `ιⱼ⁻¹ U`
  let x' : Γ((Scheme.Modules.pushforward (colimit.ι F j)).obj (D.obj j), U) := x
  have hx' (k : Σ k : J, (k ⟶ j) × (k ⟶ i)) : res (inf_le_left : V k ≤ U) x' = σ k := hx k
  refine ⟨x', fun l a b ↦ D.eq_of_restrict_eq hU fun k ↦ ?_⟩
  rw [← D.transition_app_map_apply, ← D.transition_app_map_apply]
  exact (congrArg ((D.transition a).app _) (hx' ⟨k.1, k.2.1 ≫ a, k.2.2⟩)).trans
    (hσ ⟨k.1, k.2.1 ≫ a, k.2.2⟩ l a b)

/-- **The sections of the glued module over an open inside the image of `F i` are the sections
of `Mᵢ`**: if the transition morphisms of a gluing datum are bijective over opens inside the images
of the transition maps, the projection to `(ιᵢ)_* Mᵢ` is bijective on sections over every open
contained in the image of `F i`. -/
theorem bijective_π_app {i : J} {U : (colimit F).Opens}
    (hU : U ≤ (colimit.ι F i).opensRange) : Function.Bijective ((D.π i).app U) := by
  refine ⟨fun s s' h ↦ D.π_ext fun j ↦ D.eq_of_transition_app_eq hD hU fun k a b ↦ ?_,
    fun t ↦ ?_⟩
  · rw [transition_app_π_app, transition_app_π_app, ← D.transition_app_π_app b,
      h, transition_app_π_app]
  choose x hx using fun j ↦ D.exists_transition_app_eq hD (j := j) hU t
  obtain ⟨s, hs⟩ := D.exists_π_app x fun {j' j} f ↦
    D.eq_of_transition_app_eq hD hU fun k a b ↦ by
      rw [transition_comp_apply, hx _ _ _ b, hx _ _ _ b]
  refine ⟨s, (hs i).trans (D.eq_of_transition_app_eq hD hU fun k a b ↦ ?_)⟩
  rw [hx, Subsingleton.elim a b]

/-- If the transition morphisms of a gluing datum are bijective over opens inside the images of the
transition maps, the morphism from the restriction of the glued module to `F i` to `Mᵢ` is an
isomorphism. -/
theorem isIso_restrictGluedHom (i : J) : IsIso (D.restrictGluedHom i) := by
  refine Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun W ↦ ?_
  rw [ConcreteCategory.isIso_iff_bijective,
    show ⇑((D.restrictGluedHom i).app W) = _ from funext (D.restrictGluedHom_app_apply i W)]
  exact (ConcreteCategory.bijective_of_isIso _).comp
    (D.bijective_π_app hD ((colimit.ι F i).image_le_opensRange W))

/-- **The glued module restricts to `Mᵢ` on `F i`**, if the transition morphisms of the gluing
datum are bijective over opens inside the images of the transition maps. -/
def restrictGluedIso (i : J) : D.glued.restrict (colimit.ι F i) ≅ D.obj i :=
  have := D.isIso_restrictGluedHom hD i
  asIso (D.restrictGluedHom i)

/-- The isomorphism from the restriction of the glued module to `Mᵢ` is the morphism adjoint to the
projection to `(ιᵢ)_* Mᵢ`. -/
@[simp]
theorem restrictGluedIso_hom (i : J) : (D.restrictGluedIso hD i).hom = D.restrictGluedHom i :=
  (rfl)

end Bijective

end

end ModulesGlueData

end TauCeti

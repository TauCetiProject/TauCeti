/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Grothendieck.TransportSection
public import Mathlib.CategoryTheory.SingleObj

/-!
# Group diagrams as one-object label systems

A diagram of groups gives a diagram of one-object groupoids. Its distinguished
section uses identity transport. Automorphisms of this section are exactly
compatible group elements, with their multiplication and their components.

The construction uses Mathlib's `MonCat.toCat`, `Units.toAut` and `toUnits`,
and `TransportSection.autEquivSections` for compatible automorphisms.
The representation specializes the formula of Mathlib's `Grothendieck.functorFrom`.
Its restriction recovers the original coefficient diagram, and the induced section
label action is the unique action on its limit with the given levelwise formula.

## Attribution

Adapted from `Mei/CategoryTheory/Grothendieck/SingleObj.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
Original author credit is retained; the file uses the required Tau Ceti copyright header.
-/

public section

open CategoryTheory CategoryTheory.Limits TauCeti Opposite

universe u v w u₂ v₂

namespace CategoryTheory.Functor

variable {D : Type u} [Category.{v} D] (F : D ⥤ GrpCat.{w})

/-- The identity-transport section of the associated one-object groupoids. This is an
abbreviation so its fiber objects retain their original single-object types. -/
abbrev singleObjSection :
    TransportSection (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat) where
  obj d := SingleObj.star (F.obj d)
  map {d e} _ := (1 : F.obj e)
  map_id d := by
    rw [eqToHom_refl]
    exact (SingleObj.id_as_one (F.obj d) _).symm
  map_comp {d e b} _ _ := by
    simp only [MonCat.toCat, comp_obj, comp_map, eqToHom_refl, Category.id_comp,
      toCatHom_toFunctor, SingleObj.mapHom_apply_map, map_one]
    exact (mul_one (1 : F.obj b)).symm

@[simp]
theorem singleObjSection_obj (d : D) :
    F.singleObjSection.obj d = SingleObj.star (F.obj d) := (rfl)

@[simp]
theorem singleObjSection_map {d e : D} (f : d ⟶ e) :
    F.singleObjSection.map f = (1 : F.obj e) := (rfl)

/-- The fibers of a group diagram are groupoids. -/
instance singleObjDiagramIsGroupoid (d : D) :
    IsGroupoid ((F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat).obj d) :=
  inferInstanceAs (IsGroupoid (SingleObj (F.obj d)))

/-- Identity transport sends the automorphism given by a group element to its image. The
equation is stated in the target group, the arrow type of its one-object category. -/
theorem singleObjSection_automorphismDiagram_map_toAut {d e : D} (f : d ⟶ e) (x : F.obj d) :
    Eq (α := F.obj e) ((F.singleObjSection.automorphismDiagram.map f)
      (Units.toAut (F.obj d) (toUnits x))).asIso.hom (F.map f x) := by
  rw [TransportSection.automorphismDiagram_map_apply_hom]
  simp [MonCat.toCat, SingleObj.inv_as_inv (F.obj e), SingleObj.comp_as_mul (F.obj e),
    SingleObj.toEnd, End.homEquiv, GrpCat.forget₂_map, @one_mul (F.obj e) _,
    @mul_one (F.obj e) _]

/-- Compatible group elements are precisely automorphisms of the identity-transport section. -/
noncomputable def singleObjSectionAutEquiv :
    GrpCat.sectionsSubgroup F ≃* Aut F.singleObjSection where
  toFun g := F.singleObjSection.autEquivSections.symm
    ⟨fun d => Units.toAut (F.obj d) (toUnits (g.val d)), by
      intro d e f
      apply Aut.ext
      apply Iso.ext
      -- Expose the forgotten group homomorphism so the transport formula can rewrite it.
      change ((F.singleObjSection.automorphismDiagram.map f)
        (Units.toAut (F.obj d) (toUnits (g.val d)))).asIso.hom = _
      rw [singleObjSection_automorphismDiagram_map_toAut]
      rw [Units.toAut_apply_asIso_hom]
      exact g.property f⟩
  invFun a := ⟨fun d => a.asIso.hom.app d, by
    intro d e f
    -- Name the underlying family to keep group operations independent of fiber wrappers.
    let b : ∀ d, F.obj d := fun d => a.asIso.hom.app d
    have ht : (1 : F.obj e) * (F.map f) (b d) = b e * 1 := a.asIso.hom.naturality f
    simp only [one_mul, mul_one] at ht
    exact ht⟩
  left_inv g := by
    apply Subtype.ext
    funext d
    dsimp only
    rw [TransportSection.autEquivSections_symm_apply_hom]
    simp [SingleObj.toEnd_def]
  right_inv a := by
    apply Aut.ext
    apply Iso.ext
    apply TransportSection.Hom.ext
    funext d
    dsimp only
    rw [TransportSection.autEquivSections_symm_apply_hom]
    rw [Units.toAut_apply_asIso_hom]
    rfl
  map_mul' g h := by
    apply F.singleObjSection.autEquivSections.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    funext d
    apply Aut.ext
    apply Iso.ext
    simp

/-- Recover the original group element from each component of its section label. -/
@[simp]
theorem singleObjSectionAutEquiv_hom_app (g : GrpCat.sectionsSubgroup F) (d : D) :
    (F.singleObjSectionAutEquiv g).asIso.hom.app d = g.val d := by
  rw [singleObjSectionAutEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    TransportSection.autEquivSections_symm_apply_hom]
  rw [Units.toAut_apply_asIso_hom]
  rfl

/-- The inverse identification reads off the fiber arrows. -/
@[simp]
theorem singleObjSectionAutEquiv_symm_apply (a : Aut F.singleObjSection) (d : D) :
    (F.singleObjSectionAutEquiv.symm a).val d = a.asIso.hom.app d := (rfl)

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {D : Type u} [Category.{v} D] (F : D ⥤ GrpCat.{w})
  {V : Type*} [Category V] (X : D ⥤ V)
  (ρ : ∀ d, F.obj d →* Aut (X.obj d))
  (hρ : ∀ {d e : D} (f : d ⟶ e) (g : F.obj d),
    (ρ d g).asIso.hom ≫ X.map f = X.map f ≫ (ρ e (F.map f g)).asIso.hom)

/-- The group element carried by the fiber of a total arrow. -/
def singleObjFiber
    {a b : Grothendieck (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat)}
    (f : a ⟶ b) : F.obj b.base := f.fiber

/-- The group label of a total arrow is its fiber component. -/
theorem singleObjFiber_def
    {a b : Grothendieck (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat)}
    (f : a ⟶ b) : F.singleObjFiber f = f.fiber := (rfl)

/-- Constructing a total arrow with a specified group element recovers that element. -/
@[simp]
theorem singleObjFiber_mk
    {a b : Grothendieck (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat)}
    (f : a.base ⟶ b.base) (g : F.obj b.base) :
    F.singleObjFiber (⟨f, g⟩ : a ⟶ b) = g := (rfl)

/-- The identity total arrow carries the identity group element. -/
@[simp]
theorem singleObjFiber_id
    (a : Grothendieck (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat)) :
    F.singleObjFiber (𝟙 a) = 1 := by
  simp [singleObjFiber, Grothendieck.id_fiber, MonCat.toCat,
    SingleObj.id_as_one (F.obj a.base)]

/-- Composition transports the first group element and then multiplies on the left. -/
@[simp]
theorem singleObjFiber_comp
    {a b c : Grothendieck (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat)}
    (f : a ⟶ b) (g : b ⟶ c) :
    F.singleObjFiber (f ≫ g) = F.singleObjFiber g * (F.map g.base) (F.singleObjFiber f) := by
  simp [singleObjFiber, Grothendieck.comp_fiber, MonCat.toCat,
    SingleObj.comp_as_mul (F.obj c.base), SingleObj.mapHom,
    SingleObj.id_as_one (F.obj c.base), @mul_one (F.obj c.base) _]
  -- The fiber transport applies the same homomorphism after forgetting to monoids.
  rfl

section LabelTransport

variable {F} {E : Type u₂} [Category.{v₂} E] {F' : E ⥤ GrpCat.{w}}
  (G : E ⥤ D) (φ : G ⋙ F ⟶ F')

/-- The map of total categories carries the target-fiber label through the group map. -/
@[simp]
theorem singleObjFiber_map_whiskerRight
    {a b : Grothendieck (G ⋙ (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat))}
    (f : a ⟶ b) :
    F'.singleObjFiber ((Grothendieck.map
      (whiskerRight φ (forget₂ GrpCat MonCat ⋙ MonCat.toCat))).map f) =
      φ.app b.base ((G ⋙ F).singleObjFiber f) := by
  simp only [singleObjFiber_def, Grothendieck.map_map,
    whiskerRight_app, comp_map, MonCat.toCat, toCatHom_toFunctor,
    Cat.eqToHom_app, SingleObj.mapHom]
  -- The Cat morphism wrappers must reduce to the target SingleObj composition.
  erw [SingleObj.comp_as_mul]
  exact mul_one _

/-- Pullback changes the base of a total arrow and retains its group label. -/
@[simp]
theorem singleObjFiber_pre
    {a b : Grothendieck (G ⋙ (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat))}
    (f : a ⟶ b) :
    F.singleObjFiber ((Grothendieck.pre
      (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat) G).map f) =
      (G ⋙ F).singleObjFiber f := by
  -- `pre` retains exactly the fiber arrow, viewed in the same one-object category.
  exact Grothendieck.pre_map_fiber _ G f

end LabelTransport

/-- Compatible actions on a coefficient diagram give a representation of the total
one-object label system. A total arrow first restricts coefficients, then acts.
The abbreviation retains the coefficient objects in dependent morphism types. -/
-- At these pins functorFrom's coherence types contain unexported private proofs;
-- its hom_id and hom_comp cannot be simplified through the public module interface.
abbrev singleObjRepresentation :
    Grothendieck (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat) ⥤ V where
  obj a := X.obj a.base
  map {a b} f := X.map f.base ≫ (ρ b.base (F.singleObjFiber f)).asIso.hom
  map_id a := by simp
  map_comp {a b c} f g := by
    simp only [singleObjFiber_comp, map_mul, Aut.mul_asIso, Iso.trans_hom,
      Grothendieck.comp_base, X.map_comp, Category.assoc]
    rw [← Category.assoc ((ρ b.base) (F.singleObjFiber f)).asIso.hom,
      hρ g.base (F.singleObjFiber f), Category.assoc]

/-- The represented coefficient object at `a` is the original one over `a.base`. -/
@[simp]
theorem singleObjRepresentation_obj
    (a : Grothendieck (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat)) :
    (F.singleObjRepresentation X ρ hρ).obj a = X.obj a.base := (rfl)

/-- A represented total arrow is restriction followed by its target group action. -/
@[simp]
theorem singleObjRepresentation_map
    {a b : Grothendieck (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat)} (f : a ⟶ b) :
    (F.singleObjRepresentation X ρ hρ).map f =
      X.map f.base ≫ (ρ b.base (F.singleObjFiber f)).asIso.hom := (rfl)

/-- The representation acts on a vertical label by the specified group action. -/
theorem singleObjRepresentation_map_ι (d : D) (g : F.obj d) :
    (F.singleObjRepresentation X ρ hρ).map
      ((Grothendieck.ι (F ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat) d).map
        (X := SingleObj.star (F.obj d)) (Y := SingleObj.star (F.obj d)) g) =
      (ρ d g).asIso.hom := by
  rw [singleObjRepresentation_map]
  simp [singleObjFiber, Grothendieck.ι, SingleObj.comp_as_mul (F.obj d),
    SingleObj.id_as_one (F.obj d)]
  -- The fiber-inclusion object has the same base d, so its action has these endpoints.
  rfl

/-- Restriction of the representation to identity transport recovers the coefficient diagram. -/
def singleObjRepresentationIso :
    F.singleObjSection.toFunctor ⋙ F.singleObjRepresentation X ρ hρ ≅ X :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro d e f; simp [singleObjFiber])

/-- The coefficient comparison is the identity at every object. -/
@[simp]
theorem singleObjRepresentationIso_hom_app (d : D) :
    (F.singleObjRepresentationIso X ρ hρ).hom.app d = 𝟙 (X.obj d) := (rfl)

/-- The inverse coefficient comparison is also the identity at every object. -/
@[simp]
theorem singleObjRepresentationIso_inv_app (d : D) :
    (F.singleObjRepresentationIso X ρ hρ).inv.app d = 𝟙 (X.obj d) := (rfl)

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {D : Type u} [Category.{v} D] (F : D ⥤ GrpCat.{w})
  {V : Type*} [Category V] (X : D ⥤ V)
  (ρ : ∀ d, F.obj d →* Aut (X.obj d))
  (hρ : ∀ {d e : D} (f : d ⟶ e) (g : F.obj d),
    (ρ d g).asIso.hom ≫ X.map f = X.map f ≫ (ρ e (F.map f g)).asIso.hom)
  [HasLimit X]

/-- The coefficient limit along identity transport exists whenever the original limit does. -/
instance singleObjRepresentation_hasLimit :
    HasLimit (F.singleObjSection.toFunctor ⋙ F.singleObjRepresentation X ρ hρ) :=
  hasLimit_of_iso (F.singleObjRepresentationIso X ρ hρ).symm

/-- The comparison of limits followed by the projection to a level is that projection. -/
@[reassoc]
theorem isoOfNatIso_singleObjRepresentationIso_hom_π (d : D) :
    (HasLimit.isoOfNatIso (F.singleObjRepresentationIso X ρ hρ)).hom ≫ limit.π X d =
      limit.π (F.singleObjSection.toFunctor ⋙ F.singleObjRepresentation X ρ hρ) d := by
  rw [HasLimit.isoOfNatIso_hom_π, singleObjRepresentationIso_hom_app]
  -- The comparison component is the identity of the original coefficient object.
  exact Category.comp_id _

/-- The inverse comparison of limits followed by the projection to a level is that projection. -/
@[reassoc]
theorem isoOfNatIso_singleObjRepresentationIso_inv_π (d : D) :
    (HasLimit.isoOfNatIso (F.singleObjRepresentationIso X ρ hρ)).inv ≫
      limit.π (F.singleObjSection.toFunctor ⋙ F.singleObjRepresentation X ρ hρ) d =
        limit.π X d := by
  rw [HasLimit.isoOfNatIso_inv_π, singleObjRepresentationIso_inv_app]
  -- The comparison component is the identity of the original coefficient object.
  exact Category.comp_id _

/-- The section-label action, transported to the original coefficient limit. -/
noncomputable def singleObjLimitAction : GrpCat.sectionsSubgroup F →* Aut (limit X) :=
  (Aut.autMulEquivOfIso
    (HasLimit.isoOfNatIso (F.singleObjRepresentationIso X ρ hρ))).toMonoidHom.comp
    ((TransportSection.completedAut (F.singleObjRepresentation X ρ hρ)
      F.singleObjSection).comp F.singleObjSectionAutEquiv.toMonoidHom)

/-- The represented section action recovers the original action at every projection. -/
@[reassoc (attr := simp)]
theorem singleObjLimitAction_hom_π (g : GrpCat.sectionsSubgroup F) (d : D) :
    (F.singleObjLimitAction X ρ hρ g).asIso.hom ≫ limit.π X d =
      limit.π X d ≫ (ρ d (g.val d)).asIso.hom := by
  have h : (TransportSection.completedAut (F.singleObjRepresentation X ρ hρ)
      F.singleObjSection (F.singleObjSectionAutEquiv g)).asIso.hom ≫
        limit.π (F.singleObjSection.toFunctor ⋙ F.singleObjRepresentation X ρ hρ) d =
      limit.π (F.singleObjSection.toFunctor ⋙ F.singleObjRepresentation X ρ hρ) d ≫
        (ρ d (g.val d)).asIso.hom := by
    rw [TransportSection.completedAut_hom_π, singleObjSectionAutEquiv_hom_app]
    -- The section object is the unique object, so the vertical-action formula applies.
    exact congrArg _ (F.singleObjRepresentation_map_ι X ρ hρ d (g.val d))
  -- Expand the transported action separately from its effect on projections.
  simp only [singleObjLimitAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Aut.autMulEquivOfIso_apply_asIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, isoOfNatIso_singleObjRepresentationIso_hom_π, h,
    isoOfNatIso_singleObjRepresentationIso_inv_π_assoc]

/-- A levelwise action on the coefficient limit agrees with the represented section action. -/
theorem singleObjLimitAction_unique (σ : GrpCat.sectionsSubgroup F →* Aut (limit X))
    (hσ : ∀ g d, (σ g).asIso.hom ≫ limit.π X d =
      limit.π X d ≫ (ρ d (g.val d)).asIso.hom) :
    σ = F.singleObjLimitAction X ρ hρ := by
  apply MonoidHom.ext
  intro g
  apply Aut.ext
  apply Iso.ext
  apply limit.hom_ext
  intro d
  rw [hσ, singleObjLimitAction_hom_π]

end CategoryTheory.Functor

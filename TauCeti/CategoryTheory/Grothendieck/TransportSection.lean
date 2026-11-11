/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Grothendieck.Basic
public import TauCeti.CategoryTheory.Grothendieck.Section
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Fiberwise transport data and compatible section automorphisms

`TransportSection` is a presentation of a section by objects and arrows in the
actual fibers. `sectionFunctor` sends these transport data to the section category
in `CategoryTheory.Grothendieck.Section`; the underlying total functor factors
through that existing category. This presentation retains the original fiber
carriers, so its automorphisms can be identified with compatible families of
fiber automorphisms, with transitions given by transport and conjugation.

The completed-label isomorphisms below require only invertibility of the chosen
label and limits at its specified endpoints. They use the existing section
coefficient diagrams, rather than a second construction of coefficient maps.
Their projections are the represented fiber arrows; identity, composition and
inversion agree with those of labels.

The constructions use Mathlib's `Grothendieck.ι`, `Aut.autMulEquivOfIso`,
`Functor.mapAut`, `GrpCat.sectionsSubgroup` and `HasLimit.isoOfNatIso`.

Adapted from `Mei/CategoryTheory/Grothendieck/TransportSection.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bac6f02d25746bc1c2ec808601d4e9284911c475` (Apache 2.0).
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u w z v' u'

namespace TauCeti

/-- An object in each fiber of a category-valued diagram, with functorial transport. -/
@[ext]
structure TransportSection {D : Type u} [Category.{v} D] (L : D ⥤ Cat.{w, z}) where
  /-- The chosen object in each fiber. -/
  obj (d : D) : L.obj d
  /-- Transport of the chosen object along a base arrow. -/
  map {d e : D} (f : d ⟶ e) : (L.map f).toFunctor.obj (obj d) ⟶ obj e
  /-- Transport along an identity is the canonical identification. -/
  map_id (d : D) : map (𝟙 d) = eqToHom (by simp)
  /-- Transport respects composition. -/
  map_comp {d e b : D} (f : d ⟶ e) (g : e ⟶ b) :
    map (f ≫ g) = eqToHom (by simp) ≫ (L.map g).toFunctor.map (map f) ≫ map g

namespace TransportSection

variable {D : Type u} [Category.{v} D] {L : D ⥤ Cat.{w, z}}

attribute [simp] map_id map_comp

/-- A vertical morphism between sections, commuting with the transport arrows. -/
@[ext]
structure Hom (s t : TransportSection L) where
  /-- The arrow in each fiber. -/
  app (d : D) : s.obj d ⟶ t.obj d
  /-- Fiber arrows commute with transport. -/
  naturality {d e : D} (f : d ⟶ e) :
    (L.map f).toFunctor.map (app d) ≫ t.map f = s.map f ≫ app e

attribute [reassoc] Hom.naturality

/-- Sections and vertical morphisms form a category. -/
instance : Category (TransportSection L) where
  Hom := Hom
  id s := ⟨fun d => 𝟙 (s.obj d), by simp⟩
  comp α β := ⟨fun d => α.app d ≫ β.app d, by
    intro d e f
    simp only [Functor.map_comp, Category.assoc]
    rw [β.naturality, α.naturality_assoc]⟩

@[simp]
theorem id_app (s : TransportSection L) (d : D) : (𝟙 s : s ⟶ s).app d = 𝟙 _ := (rfl)

@[simp]
theorem comp_app {s t r : TransportSection L} (α : s ⟶ t) (β : t ⟶ r) (d : D) :
    (α ≫ β).app d = α.app d ≫ β.app d := (rfl)

/-- Evaluation at a base object is a functor to that fiber. -/
abbrev evaluation (d : D) : TransportSection L ⥤ L.obj d where
  obj s := s.obj d
  map α := α.app d

/-- The total functor associated to a section. -/
abbrev toFunctor (s : TransportSection L) : D ⥤ Grothendieck L where
  obj d := ⟨d, s.obj d⟩
  map f := ⟨f, s.map f⟩
  map_id d := by
    refine Grothendieck.ext _ _ ?_ ?_
    · rfl
    · simp only [Grothendieck.id_fiber, map_id]
      -- The fiber lives in the category stored in `L.obj d`.
      erw [eqToHom_trans (C := L.obj d)]
  map_comp f g := by
    refine Grothendieck.ext _ _ ?_ ?_
    · rfl
    · simp only [Grothendieck.comp_fiber, map_comp]
      erw [eqToHom_trans_assoc (C := L.obj _)]

/-- The total functor determines the objects and transport arrows of its section presentation. -/
theorem toFunctor_injective :
    Function.Injective (toFunctor (L := L)) := by
  intro s t h
  rcases s with ⟨so, sm, _, _⟩
  rcases t with ⟨tobj, tm, _, _⟩
  have ho : so = tobj := by
    funext d
    exact eq_of_heq (Grothendieck.mk.inj
      (_root_.CategoryTheory.Functor.congr_obj h d)).2
  subst tobj
  refine TransportSection.ext ?_ ?_
  · rfl
  · apply heq_of_eq
    funext d e f
    have hf := _root_.CategoryTheory.Functor.congr_hom h f
    have hm := (by
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hf :
        (⟨f, sm f⟩ : (⟨d, so d⟩ : Grothendieck L) ⟶ ⟨e, so e⟩) = ⟨f, tm f⟩)
    exact eq_of_heq (Grothendieck.Hom.mk.inj hm).2

/-- The total functor of a section lies over the identity. -/
@[simp]
theorem toFunctor_comp_forget (s : TransportSection L) :
    s.toFunctor ⋙ Grothendieck.forget _ = 𝟭 D := (rfl)

/-- A morphism of sections as a natural transformation of total functors. -/
def toNatTrans {s t : TransportSection L} (α : s ⟶ t) : s.toFunctor ⟶ t.toFunctor where
  app d := (Grothendieck.ι _ d).map (α.app d)
  naturality d e f := by
    rw [← Grothendieck.ιNatTrans_app_comp_ι_map (s.toFunctor.map f),
      ← Grothendieck.ιNatTrans_app_comp_ι_map (t.toFunctor.map f)]
    -- Retype the factorizations through the fiber inclusions: the total functor's object
    -- wrappers prevent `simp` from recognizing the common endpoints for reassociation.
    change ((Grothendieck.ιNatTrans f).app (s.obj d) ≫
      (Grothendieck.ι L e).map (s.map f)) ≫ (Grothendieck.ι L e).map (α.app e) =
        (Grothendieck.ι L d).map (α.app d) ≫ (Grothendieck.ιNatTrans f).app (t.obj d) ≫
          (Grothendieck.ι L e).map (t.map f)
    simp only [Category.assoc]
    rw [(Grothendieck.ιNatTrans f).naturality_assoc (α.app d)]
    simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
      congrArg (fun k => (Grothendieck.ιNatTrans f).app (s.obj d) ≫
        (Grothendieck.ι L e).map k) (α.naturality f).symm

@[simp]
theorem toNatTrans_app {s t : TransportSection L} (α : s ⟶ t) (d : D) :
    (toNatTrans α).app d = (Grothendieck.ι _ d).map (α.app d) := (rfl)

/-- Fiberwise transport data give a section of the Grothendieck projection. -/
abbrev toSection (s : TransportSection L) : CategoryTheory.Grothendieck.Section L :=
  CategoryTheory.Functor.Fiber.mk s.toFunctor_comp_forget

/-- The actual section constructed from transport data has the specified total functor. -/
@[simp]
theorem toSection_toFunctor (s : TransportSection L) :
    s.toSection.toFunctor = s.toFunctor := (rfl)

/-- A transformation between transport sections has identity base components. -/
@[simp]
theorem sectionHom_base {s t : TransportSection L} (α : s.toSection ⟶ t.toSection) (d : D) :
    ((CategoryTheory.Grothendieck.Section.hom α).app d).base = 𝟙 d := by
  have h := CategoryTheory.Grothendieck.Section.whiskerRight_hom_forget α
  erw [eqToHom_refl (C := D ⥤ D), Category.id_comp] at h
  exact NatTrans.congr_app h d

/-- Fiberwise morphisms give morphisms in the existing category of sections. -/
def toSectionHom {s t : TransportSection L} (α : s ⟶ t) : s.toSection ⟶ t.toSection :=
  CategoryTheory.Grothendieck.Section.homMk (toNatTrans α) (by
    erw [eqToHom_refl (C := D ⥤ D), Category.id_comp]
    apply NatTrans.ext
    funext d
    erw [Functor.whiskerRight_app, toNatTrans_app])

/-- The underlying transformation of the section morphism is its total transformation. -/
@[simp]
theorem hom_toSectionHom {s t : TransportSection L} (α : s ⟶ t) :
    CategoryTheory.Grothendieck.Section.hom (toSectionHom α) = toNatTrans α := by
  exact CategoryTheory.Grothendieck.Section.hom_homMk _ _

/-- The transport presentation maps to the existing category of sections. -/
abbrev sectionFunctor : TransportSection L ⥤ CategoryTheory.Grothendieck.Section L where
  obj := toSection
  map := toSectionHom
  map_id s := by
    apply CategoryTheory.Grothendieck.Section.hom_ext
    intro d
    rw [hom_toSectionHom]
    exact (Grothendieck.ι L d).map_id _
  map_comp α β := by
    apply CategoryTheory.Grothendieck.Section.hom_ext
    intro d
    -- `Functor.map_comp` does not match through `Section.hom`'s fiber wrapper.
    -- Expose its componentwise composition so `hom_toSectionHom` can rewrite each factor.
    change (CategoryTheory.Grothendieck.Section.hom (toSectionHom (α ≫ β))).app d =
      (CategoryTheory.Grothendieck.Section.hom (toSectionHom α)).app d ≫
        (CategoryTheory.Grothendieck.Section.hom (toSectionHom β)).app d
    simp only [hom_toSectionHom, toNatTrans_app, comp_app]
    exact (Grothendieck.ι L d).map_comp _ _

@[simp]
theorem sectionFunctor_obj (s : TransportSection L) :
    sectionFunctor.obj s = s.toSection := (rfl)

@[simp]
theorem sectionFunctor_map {s t : TransportSection L} (α : s ⟶ t) :
    sectionFunctor.map α = toSectionHom α := (rfl)

instance : (sectionFunctor (L := L)).Faithful where
  map_injective {s t} α β h := by
    apply Hom.ext
    funext d
    apply (Grothendieck.ι L d).map_injective
    have hd := congrArg (fun γ => (CategoryTheory.Grothendieck.Section.hom γ).app d) h
    rw [sectionFunctor_map, sectionFunctor_map, hom_toSectionHom, hom_toSectionHom,
      toNatTrans_app, toNatTrans_app] at hd
    exact hd

/-- The total functor factors through the existing section category and its inclusion. -/
def totalFunctor : TransportSection L ⥤ (D ⥤ Grothendieck L) :=
  sectionFunctor ⋙ CategoryTheory.Functor.Fiber.fiberInclusion

/-- The object map is the section's total functor. -/
@[simp]
theorem totalFunctor_obj (s : TransportSection L) :
    totalFunctor.obj s = s.toFunctor := (rfl)

/-- The morphism map is the total natural transformation, after identifying its endpoints. -/
@[simp]
theorem totalFunctor_map {s t : TransportSection L} (α : s ⟶ t) :
    totalFunctor.map α =
      eqToHom (totalFunctor_obj s) ≫ toNatTrans α ≫ eqToHom (totalFunctor_obj t).symm := by
  simp only [totalFunctor]
  erw [eqToHom_refl (C := D ⥤ Grothendieck L),
    eqToHom_refl (C := D ⥤ Grothendieck L), Category.id_comp, Category.comp_id]
  exact hom_toSectionHom α

/-- The components of an invertible section morphism are invertible in their fibers. -/
instance app_isIso {s t : TransportSection L} (α : s ⟶ t) [IsIso α] (d : D) :
    IsIso (α.app d) :=
  Functor.map_isIso (evaluation d) α

@[simp]
theorem inv_app {s t : TransportSection L} (α : s ⟶ t) [IsIso α] (d : D) :
    (inv α).app d = inv (α.app d) :=
  (evaluation d).map_inv α

section GroupoidFibers

variable [∀ d, IsGroupoid (L.obj d)]

/-- A vertical morphism is inverted in every fiber. -/
noncomputable instance : Groupoid (TransportSection L) where
  inv α := ⟨fun d => inv (α.app d), by
    intro d e f
    apply (cancel_mono (α.app e)).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← α.naturality, ← Category.assoc, ← Functor.map_comp]
    simp⟩
  inv_comp α := by apply Hom.ext; funext d; simp
  comp_inv α := by apply Hom.ext; funext d; simp

end GroupoidFibers

section TransportAutomorphisms

variable (s : TransportSection L) [∀ {d e : D} (f : d ⟶ e), IsIso (s.map f)]

/-- Fiber automorphisms transported along a section by conjugation. This is reducible
on objects, retaining the actual automorphism groups as carriers. -/
noncomputable abbrev automorphismDiagram : D ⥤ GrpCat.{w} where
  obj d := GrpCat.of (Aut (s.obj d))
  map f := GrpCat.ofHom
    ((Aut.autMulEquivOfIso (asIso (s.map f))).toMonoidHom.comp ((L.map f).toFunctor.mapAut _))
  map_id d := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    apply Aut.ext
    apply Iso.ext
    have h := Functor.congr_hom congr($(L.map_id d).toFunctor) a.asIso.hom
    simpa [Aut.autMulEquivOfIso, Functor.mapAut] using
      congrArg (fun k => inv (s.map (𝟙 d)) ≫ k ≫ s.map (𝟙 d)) h
  map_comp f g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    apply Aut.ext
    apply Iso.ext
    have h := Functor.congr_hom congr($(L.map_comp f g).toFunctor) a.asIso.hom
    simpa [Aut.autMulEquivOfIso, Functor.mapAut] using
      congrArg (fun k => inv (s.map (f ≫ g)) ≫ k ≫ s.map (f ≫ g)) h

/-- Transport acts on the underlying arrow by fiber transport followed by conjugation. -/
@[simp↓]
theorem automorphismDiagram_map_apply_hom
    {d e : D} (f : d ⟶ e) (a : Aut (s.obj d)) :
    ((s.automorphismDiagram.map f) a).asIso.hom =
      inv (s.map f) ≫ (L.map f).toFunctor.map a.asIso.hom ≫ s.map f := (rfl)

/-- Automorphisms of a section are compatible families of fiber automorphisms. -/
noncomputable def autEquivSections :
    Aut s ≃* GrpCat.sectionsSubgroup s.automorphismDiagram where
  toFun a := ⟨fun d => (evaluation d).mapAut s a, by
    intro d e f
    apply Aut.ext
    apply Iso.ext
    dsimp [Functor.mapAut, automorphismDiagram, Aut.autMulEquivOfIso]
    rw [a.asIso.hom.naturality, IsIso.inv_hom_id_assoc]⟩
  invFun a := Aut.of
    { hom := ⟨fun d => (a.val d).asIso.hom, by
        intro d e f
        have h := congrArg (fun a => s.map f ≫ a.asIso.hom) (a.property f)
        simpa using h⟩
      inv := ⟨fun d => (a.val d).asIso.inv, by
        intro d e f
        have h := congrArg (fun a => s.map f ≫ a.asIso.hom) ((a⁻¹).property f)
        simpa using h⟩
      hom_inv_id := by apply Hom.ext; funext d; simp
      inv_hom_id := by apply Hom.ext; funext d; simp }
  left_inv a := by
    apply Aut.ext
    apply Iso.ext
    apply Hom.ext
    rfl
  right_inv a := by apply Subtype.ext; funext d; rfl
  map_mul' a b := by apply Subtype.ext; funext d; exact ((evaluation d).mapAut s).map_mul a b

@[simp]
theorem autEquivSections_apply (a : Aut s) (d : D) :
    (s.autEquivSections a).val d = (evaluation d).mapAut s a := (rfl)

/-- Reconstruction from compatible automorphisms retains their fiberwise arrows. -/
@[simp]
theorem autEquivSections_symm_apply_hom
    (a : GrpCat.sectionsSubgroup s.automorphismDiagram) (d : D) :
    (s.autEquivSections.symm a).asIso.hom.app d = (a.val d).asIso.hom := (rfl)

end TransportAutomorphisms

section Coefficients

variable {V : Type u'} [Category.{v'} V] (A : Grothendieck L ⥤ V)
  {s t r : TransportSection L}

/-- A completed label acts between the coefficient limits along its source and target sections. -/
noncomputable def completedLabelIso (α : s ⟶ t) [IsIso α]
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit (t.toFunctor ⋙ A)] :
    limit (s.toFunctor ⋙ A) ≅ limit (t.toFunctor ⋙ A) :=
  HasLimit.isoOfNatIso
    (((sectionFunctor ⋙ CategoryTheory.Grothendieck.Section.coefficientDiagram A)).mapIso
      (asIso α))

/-- Each projection computes the completed action using the represented fiber label. -/
@[reassoc (attr := simp)]
theorem completedLabelIso_hom_π (α : s ⟶ t) [IsIso α]
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit (t.toFunctor ⋙ A)] (d : D) :
    (completedLabelIso A α).hom ≫ limit.π (t.toFunctor ⋙ A) d =
      limit.π (s.toFunctor ⋙ A) d ≫ A.map ((Grothendieck.ι L d).map (α.app d)) := by
  unfold completedLabelIso
  erw [HasLimit.isoOfNatIso_hom_π]
  -- `hom_toSectionHom` cannot match inside the composite functor's `mapIso` projection.
  -- Its component reduces to the whiskering of `toSectionHom α` by `A`, identifying
  -- the total functors of `s.toSection` and `t.toSection`
  -- with `s.toFunctor` and `t.toFunctor`, respectively.
  change limit.π (s.toFunctor ⋙ A) d ≫
    A.map ((CategoryTheory.Grothendieck.Section.hom (toSectionHom α)).app d) = _
  rw [hom_toSectionHom, toNatTrans_app]
  rfl

/-- The inverse completed action is computed using the inverse fiber label. -/
@[reassoc (attr := simp)]
theorem completedLabelIso_inv_π (α : s ⟶ t) [IsIso α]
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit (t.toFunctor ⋙ A)] (d : D) :
    (completedLabelIso A α).inv ≫ limit.π (s.toFunctor ⋙ A) d =
      limit.π (t.toFunctor ⋙ A) d ≫ A.map ((Grothendieck.ι L d).map (inv (α.app d))) := by
  unfold completedLabelIso
  erw [HasLimit.isoOfNatIso_inv_π]
  -- `hom_toSectionHom` cannot match inside the composite functor's inverse `mapIso` projection.
  -- Its component reduces to the whiskering of `toSectionHom (inv α)` by `A`, identifying
  -- the total functors of `t.toSection` and `s.toSection`
  -- with `t.toFunctor` and `s.toFunctor`, respectively.
  change limit.π (t.toFunctor ⋙ A) d ≫
    A.map ((CategoryTheory.Grothendieck.Section.hom (toSectionHom (inv α))).app d) = _
  rw [hom_toSectionHom, toNatTrans_app, inv_app]
  rfl

/-- The identity label acts as the identity on the completed coefficient object. -/
@[simp]
theorem completedLabelIso_id (s : TransportSection L) [HasLimit (s.toFunctor ⋙ A)] :
    completedLabelIso A (𝟙 s) = Iso.refl _ := by
  apply Iso.ext
  apply limit.hom_ext
  intro d
  rw [completedLabelIso_hom_π]
  erw [(Grothendieck.ι L d).map_id, A.map_id, Category.comp_id (obj := V)]
  simp

/-- Completed labels act functorially. -/
@[simp]
theorem completedLabelIso_comp (α : s ⟶ t) (β : t ⟶ r) [IsIso α] [IsIso β]
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit (t.toFunctor ⋙ A)]
    [HasLimit (r.toFunctor ⋙ A)] :
    completedLabelIso A (α ≫ β) = completedLabelIso A α ≪≫ completedLabelIso A β := by
  apply Iso.ext
  apply limit.hom_ext
  intro d
  simp only [Iso.trans_hom, Category.assoc, completedLabelIso_hom_π,
    comp_app, Functor.map_comp]
  -- The fiber inclusion and total functor present the same objects through different wrappers.
  erw [A.map_comp, completedLabelIso_hom_π_assoc]
  exact (Category.assoc _ _ _).symm

/-- Inverting a label inverts its completed action. -/
@[simp]
theorem completedLabelIso_inv (α : s ⟶ t) [IsIso α]
    [HasLimit (s.toFunctor ⋙ A)] [HasLimit (t.toFunctor ⋙ A)] :
    completedLabelIso A (inv α) = (completedLabelIso A α).symm := by
  apply Iso.ext
  apply limit.hom_ext
  intro d
  rw [completedLabelIso_hom_π, Iso.symm_hom, completedLabelIso_inv_π, inv_app]

/-- The group of completed labels at a section acts on its completed coefficient object. -/
noncomputable def completedAut (s : TransportSection L) [HasLimit (s.toFunctor ⋙ A)] :
    Aut s →* Aut (limit (s.toFunctor ⋙ A)) where
  toFun a := Aut.of (completedLabelIso A a.asIso.hom)
  map_one' := by apply Aut.ext; simp
  map_mul' a b := by apply Aut.ext; simp

/-- The action of a completed automorphism has its prescribed fiberwise projections. -/
@[reassoc (attr := simp)]
theorem completedAut_hom_π (s : TransportSection L) [HasLimit (s.toFunctor ⋙ A)]
    (a : Aut s) (d : D) :
    (completedAut A s a).asIso.hom ≫ limit.π (s.toFunctor ⋙ A) d =
      limit.π (s.toFunctor ⋙ A) d ≫ A.map ((Grothendieck.ι L d).map (a.asIso.hom.app d)) :=
  completedLabelIso_hom_π A a.asIso.hom d

end Coefficients

end TransportSection
end TauCeti

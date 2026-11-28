/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DoubleCategory.Implicit.Functor

/-!
# Double functors preserving representations

A represented implicit double functor preserves the chosen identity and binary composite
of generators, together with their globular comparison isomorphisms. Preservation of the
comparisons for arbitrary paths follows recursively; it is not additional structure.

The horizontal preservation condition makes sense on its own, so it can also be used when
only one direction has a representation. Applying it to the transposed functor supplies the
vertical condition with independent universes for the two generating quivers.

The comparison laws are equalities of cells after named boundary transports. Requiring the
hom of each comparison to be preserved also determines its inverse, since the comparisons
are isomorphisms in the globular categories.

The represented implicit presentation follows A. D. Fairbanks and M. Shulman,
*Doubly weak double categories*, Applied Categorical Structures **34** (2026), article 26,
Definitions 3.1–3.3.
-/

public section

universe s₁ s₂ s₃ s₄ u₁ u₂ u₃ u₄ h₁ h₂ h₃ h₄ v₁ v₂ v₃ v₄

namespace TauCeti

open CategoryTheory StrictDoubleCategory DoubleCategoryStruct

variable {O₁ : Type u₁} {H₁ : Quiver.{h₁} O₁} {V₁ : Quiver.{v₁} O₁}
  {O₂ : Type u₂} {H₂ : Quiver.{h₂} O₂} {V₂ : Quiver.{v₂} O₂}
  {O₃ : Type u₃} {H₃ : Quiver.{h₃} O₃} {V₃ : Quiver.{v₃} O₃}
  {D₁ : ImplicitDoubleCategory.{s₁} O₁ H₁ V₁}
  {D₂ : ImplicitDoubleCategory.{s₂} O₂ H₂ V₂}
  {D₃ : ImplicitDoubleCategory.{s₃} O₃ H₃ V₃}

namespace ImplicitDoubleFunctor

/-- Preservation of chosen horizontal composites and their comparison cells. Only the homs
of the comparisons are required: their inverses are determined by the isomorphism laws. -/
structure PreservesHorizontalRepresentation (F : ImplicitDoubleFunctor D₁ D₂)
    (R₁ : D₁.HorizontalRepresentation) (R₂ : D₂.HorizontalRepresentation) : Prop where
  /-- Preserve the chosen identity generator. -/
  map_unit (a : O₁) : F.hGenerator (R₁.unit a) = R₂.unit (F.obj a)
  /-- Preserve the chosen binary composite of generators. -/
  map_mul {a b c : O₁} (f : @Quiver.Hom O₁ H₁ a b) (g : @Quiver.Hom O₁ H₁ b c) :
    F.hGenerator (R₁.mul f g) = R₂.mul (F.hGenerator f) (F.hGenerator g)
  /-- Preserve the nullary comparison after identifying all four boundaries. -/
  map_unitIso_hom (a : O₁) :
    F.map (R₁.unitIso a).hom.cell = ((R₂.unitIso (F.obj a)).hom.cell).cast
      (F.hMap_id a).symm (by simp [map_unit]) (F.vMap_id a).symm (F.vMap_id a).symm
  /-- Preserve the binary comparison after identifying all four boundaries. -/
  map_mulIso_hom {a b c : O₁} (f : @Quiver.Hom O₁ H₁ a b) (g : @Quiver.Hom O₁ H₁ b c) :
    F.map (R₁.mulIso f g).hom.cell =
      ((R₂.mulIso (F.hGenerator f) (F.hGenerator g)).hom.cell).cast
        (by simp) (by simp [map_mul]) (F.vMap_id a).symm (F.vMap_id c).symm

namespace PreservesHorizontalRepresentation

variable {F : ImplicitDoubleFunctor D₁ D₂}
  {R₁ : D₁.HorizontalRepresentation} {R₂ : D₂.HorizontalRepresentation}
  (hF : F.PreservesHorizontalRepresentation R₁ R₂)

include hF in
/-- The generator representing a mapped path is the image of its representing generator. -/
theorem map_rep {a b : O₁} (p : @Quiver.Path O₁ H₁ a b) :
    F.hGenerator (R₁.rep p) = R₂.rep (F.hMap p) := by
  rw [F.hMap_eq_mapPath]
  induction p with
  | nil => simpa using hF.map_unit _
  | @cons b c p f ih =>
    cases p with
    | nil => simp
    | cons p g => simpa [hF.map_mul] using congrArg (fun x ↦ R₂.mul x (F.hGenerator f)) ih

include hF in
/-- A functor preserving the chosen nullary and binary comparisons preserves the recursively
constructed comparison of every path. -/
theorem map_repIso_hom {a b : O₁} (p : @Quiver.Path O₁ H₁ a b) :
    F.map (R₁.repIso p).hom.cell = ((R₂.repIso (F.hMap p)).hom.cell).cast
      rfl (by rw [F.hMap_toPath, hF.map_rep]) (F.vMap_id a).symm (F.vMap_id b).symm := by
  rw [eq_comm, Cell.cast_eq_iff_heq, heq_comm]
  suffices h : F.map (R₁.repIso p).hom.cell ≍
      (R₂.repIso (@Prefunctor.mapPath O₁ H₁ O₂ H₂ F.hPrefunctor a b p)).hom.cell by
    have hc : ∀ (q r : @Quiver.Path O₂ H₂ (F.obj a) (F.obj b)), q = r →
        (R₂.repIso q).hom.cell ≍ (R₂.repIso r).hom.cell := by
      rintro q r rfl
      rfl
    exact h.trans (hc _ _ (F.hMap_eq_mapPath p).symm)
  induction p with
  | nil =>
    dsimp only [Prefunctor.mapPath_nil]
    rw [R₁.repIso_nil a, R₂.repIso_nil (F.obj a)]
    exact (heq_of_eq (hF.map_unitIso_hom a)).trans (Cell.cast_heq _ _ _ _ _)
  | @cons b c p f ih =>
    cases p with
    | nil =>
      dsimp only [Prefunctor.mapPath_cons, Prefunctor.mapPath_nil]
      rw [HorizontalRepresentation.repIso_cons_nil, HorizontalRepresentation.repIso_cons_nil]
      dsimp only [Iso.refl_hom]
      rw [HorizontalGlobular.id_cell, HorizontalGlobular.id_cell]
      have hc : ∀ (q r : @Quiver.Path O₂ H₂ (F.obj a) (F.obj c)), q = r →
          D₂.vId q ≍ D₂.vId r := by
        rintro q r rfl
        rfl
      exact (heq_of_eq (F.map_vId _)).trans
        ((Cell.cast_heq _ _ _ _ _).trans (hc _ _ (F.hMap_toPath f)))
    | cons p g =>
      dsimp only [Prefunctor.mapPath_cons, Prefunctor.mapPath_nil]
      dsimp only [Prefunctor.mapPath_cons] at ih
      rw [HorizontalRepresentation.repIso_cons_cons, HorizontalRepresentation.repIso_cons_cons]
      -- Whisker the induction hypothesis, then identify the binary comparison's generator.
      have hw := F.toStrictDoubleFunctor.map_hWhiskerRight_cell_heq
        (@Quiver.Hom.toPath O₁ H₁ _ _ f) (R₁.repIso (@Quiver.Path.cons O₁ H₁ _ _ _ p g)).hom
        (R₂.repIso (@Prefunctor.mapPath O₁ H₁ O₂ H₂ F.hPrefunctor a b
          (@Quiver.Path.cons O₁ H₁ _ _ _ p g))).hom (F.hMap_toPath f)
        (F.hMap_eq_mapPath _) (by simp only [F.hMap_toPath, hF.map_rep, F.hMap_eq_mapPath]) ih
      dsimp only [Prefunctor.mapPath_cons] at hw
      have hm := ((heq_of_eq
        (hF.map_mulIso_hom (R₁.rep (@Quiver.Path.cons O₁ H₁ _ _ _ p g)) f)).trans
          (Cell.cast_heq _ _ _ _ _)).trans
            (congr_arg_heq (fun x ↦ (R₂.mulIso x (F.hGenerator f)).hom.cell)
              ((hF.map_rep _).trans (congrArg R₂.rep (F.hMap_eq_mapPath _))))
      dsimp only [Prefunctor.mapPath_cons] at hm
      -- Compose the preserved cells, transporting their vertical identity boundaries in the lemma.
      erw [Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom]
      refine F.toStrictDoubleFunctor.map_horizontalGlobular_comp_cell_heq _ _ _ _ ?_ ?_ ?_ hw hm
      all_goals
        simp [hWhiskerRight_obj, hF.map_rep, hF.map_mul]

include hF in
/-- Preservation of a path comparison as an isomorphism of globular paths. The final
isomorphism transports its representing singleton along preservation of its generator. -/
theorem map_repIso {a b : O₁} (p : @Quiver.Path O₁ H₁ a b) :
    (F.toStrictDoubleFunctor.horizontalGlobularFunctor a b).mapIso (R₁.repIso p) =
      R₂.repIso (F.hMap p) ≪≫ eqToIso (congrArg HorizontalGlobular.mk
        ((F.hMap_toPath (R₁.rep p)).trans
          (congrArg (@Quiver.Hom.toPath O₂ H₂ _ _) (hF.map_rep p))).symm) := by
  apply Iso.ext
  apply HorizontalGlobular.hom_ext
  rw [Functor.mapIso_hom, StrictDoubleFunctor.horizontalGlobularFunctor_map_cell,
    hF.map_repIso_hom, Cell.cast_cast]
  have hp : (@Quiver.Hom.toPath O₂ H₂ _ _ (R₂.rep (F.hMap p))) =
      F.hMap (@Quiver.Hom.toPath O₁ H₁ _ _ (R₁.rep p)) := by
    rw [F.hMap_toPath, hF.map_rep]
  have hc := HorizontalGlobular.eqToHom_comp_eqToHom_cell (D := D₂)
    rfl (R₂.repIso (F.hMap p)).hom (congrArg HorizontalGlobular.mk hp)
  dsimp only [StrictDoubleFunctor.horizontalGlobularFunctor]
  simpa only [eqToHom_refl, Category.id_comp, Iso.trans_hom, eqToIso.hom] using hc.symm

include hF in
/-- Preservation of the inverse of the recursive path comparison. -/
theorem map_repIso_inv {a b : O₁} (p : @Quiver.Path O₁ H₁ a b) :
    (F.toStrictDoubleFunctor.horizontalGlobularFunctor a b).map (R₁.repIso p).inv =
      eqToHom (congrArg HorizontalGlobular.mk
        ((F.hMap_toPath (R₁.rep p)).trans
          (congrArg (@Quiver.Hom.toPath O₂ H₂ _ _) (hF.map_rep p)))) ≫
        (R₂.repIso (F.hMap p)).inv := by
  have h := congrArg Iso.inv (hF.map_repIso p)
  simpa only [Functor.mapIso_inv, Iso.trans_inv, eqToIso.inv] using h

/-- The identity implicit double functor preserves every horizontal representation. -/
protected theorem id (R : D₁.HorizontalRepresentation) :
    (ImplicitDoubleFunctor.id D₁).PreservesHorizontalRepresentation R R where
  map_unit _ := rfl
  map_mul _ _ := rfl
  map_unitIso_hom _ := rfl
  map_mulIso_hom _ _ := rfl

include hF in
/-- Preservation of horizontal representations is closed under composition. -/
protected theorem comp {G : ImplicitDoubleFunctor D₂ D₃}
    {R₃ : D₃.HorizontalRepresentation} (hG : G.PreservesHorizontalRepresentation R₂ R₃) :
    (F.comp G).PreservesHorizontalRepresentation R₁ R₃ where
  map_unit a := by simp [hF.map_unit, hG.map_unit]
  map_mul f g := by simp [hF.map_mul, hG.map_mul]
  map_unitIso_hom a := by
    simp [hF.map_unitIso_hom, hG.map_unitIso_hom]
  map_mulIso_hom f g := by
    dsimp only [ImplicitDoubleFunctor.comp_toStrictDoubleFunctor, StrictDoubleFunctor.comp_map]
    rw [hF.map_mulIso_hom]
    rw [StrictDoubleFunctor.map_cast, hG.map_mulIso_hom, Cell.cast_cast]
    rfl

end PreservesHorizontalRepresentation

end ImplicitDoubleFunctor

/-- A generator-preserving double functor preserving both chosen representations, including
all four nullary and binary comparison families. -/
structure RepresentedImplicitDoubleFunctor (R₁ : D₁.Representation) (R₂ : D₂.Representation)
    extends ImplicitDoubleFunctor D₁ D₂ where
  /-- Preservation in the horizontal direction. -/
  horizontal : toImplicitDoubleFunctor.PreservesHorizontalRepresentation R₁.horizontal R₂.horizontal
  /-- Preservation in the vertical direction, expressed horizontally in the transpose. -/
  vertical : toImplicitDoubleFunctor.transpose.PreservesHorizontalRepresentation
    R₁.vertical R₂.vertical

namespace RepresentedImplicitDoubleFunctor

variable {R₁ : D₁.Representation} {R₂ : D₂.Representation} {R₃ : D₃.Representation}

/-- Equality of the underlying implicit functors determines equality of represented functors;
preservation of a representation is a property, with no additional choice of data. -/
@[ext]
theorem ext {F G : RepresentedImplicitDoubleFunctor R₁ R₂}
    (h : F.toImplicitDoubleFunctor = G.toImplicitDoubleFunctor) : F = G := by
  cases F
  cases G
  cases h
  rfl

variable (R₁) in
/-- The identity represented implicit double functor. Its body is exposed so the endpoints
of its cell map compute. -/
@[expose]
def id : RepresentedImplicitDoubleFunctor R₁ R₁ where
  toImplicitDoubleFunctor := ImplicitDoubleFunctor.id D₁
  horizontal := .id R₁.horizontal
  vertical := .id R₁.vertical

@[simp]
theorem id_toImplicitDoubleFunctor :
    (id R₁).toImplicitDoubleFunctor = ImplicitDoubleFunctor.id D₁ := rfl

/-- Compose represented implicit double functors in diagrammatic order. The body is exposed
so the endpoints of its cell map compute. -/
@[expose]
def comp (F : RepresentedImplicitDoubleFunctor R₁ R₂)
    (G : RepresentedImplicitDoubleFunctor R₂ R₃) : RepresentedImplicitDoubleFunctor R₁ R₃ where
  toImplicitDoubleFunctor := F.toImplicitDoubleFunctor.comp G.toImplicitDoubleFunctor
  horizontal := F.horizontal.comp G.horizontal
  vertical := F.vertical.comp G.vertical

@[simp]
theorem comp_toImplicitDoubleFunctor (F : RepresentedImplicitDoubleFunctor R₁ R₂)
    (G : RepresentedImplicitDoubleFunctor R₂ R₃) :
    (F.comp G).toImplicitDoubleFunctor = F.toImplicitDoubleFunctor.comp G.toImplicitDoubleFunctor :=
  rfl

@[simp]
theorem id_comp (F : RepresentedImplicitDoubleFunctor R₁ R₂) : (id R₁).comp F = F :=
  ext (ImplicitDoubleFunctor.id_comp _)

@[simp]
theorem comp_id (F : RepresentedImplicitDoubleFunctor R₁ R₂) : F.comp (id R₂) = F :=
  ext (ImplicitDoubleFunctor.comp_id _)

/-- Composition of represented implicit double functors is associative. -/
theorem comp_assoc {O₄ : Type u₄} {H₄ : Quiver.{h₄} O₄} {V₄ : Quiver.{v₄} O₄}
    {D₄ : ImplicitDoubleCategory.{s₄} O₄ H₄ V₄} {R₄ : D₄.Representation}
    (F : RepresentedImplicitDoubleFunctor R₁ R₂) (G : RepresentedImplicitDoubleFunctor R₂ R₃)
    (K : RepresentedImplicitDoubleFunctor R₃ R₄) :
    (F.comp G).comp K = F.comp (G.comp K) := ext (ImplicitDoubleFunctor.comp_assoc _ _ _)

/-- The chosen representing generator of any horizontal path is preserved. -/
@[simp]
theorem hGenerator_rep (F : RepresentedImplicitDoubleFunctor R₁ R₂) {a b : O₁}
    (p : @Quiver.Path O₁ H₁ a b) :
    F.hGenerator (R₁.horizontal.rep p) = R₂.horizontal.rep (F.hMap p) := F.horizontal.map_rep p

/-- The chosen representing generator of any vertical path is preserved. -/
@[simp]
theorem vGenerator_rep (F : RepresentedImplicitDoubleFunctor R₁ R₂) {a b : O₁}
    (p : @Quiver.Path O₁ V₁ a b) :
    F.vGenerator (R₁.vertical.rep p) = R₂.vertical.rep (F.vMap p) := F.vertical.map_rep p

/-- The horizontal comparison of an arbitrary path is preserved. -/
@[simp]
theorem map_horizontal_repIso_hom (F : RepresentedImplicitDoubleFunctor R₁ R₂) {a b : O₁}
    (p : @Quiver.Path O₁ H₁ a b) :
    F.map (R₁.horizontal.repIso p).hom.cell =
      ((R₂.horizontal.repIso (F.hMap p)).hom.cell).cast rfl
        (by rw [F.hMap_toPath, F.hGenerator_rep]) (F.vMap_id a).symm (F.vMap_id b).symm :=
  F.horizontal.map_repIso_hom p

/-- The vertical comparison of an arbitrary path is preserved. -/
@[simp]
theorem map_vertical_repIso_hom (F : RepresentedImplicitDoubleFunctor R₁ R₂) {a b : O₁}
    (p : @Quiver.Path O₁ V₁ a b) :
    F.map (R₁.vertical.repIso p).hom.cell =
      ((R₂.vertical.repIso (F.vMap p)).hom.cell).cast
        (F.hMap_id a).symm (F.hMap_id b).symm rfl
        (by rw [F.vMap_toPath, F.vGenerator_rep]) := by
  have h := F.vertical.map_repIso_hom p
  dsimp only [ImplicitDoubleFunctor.transpose, StrictDoubleFunctor.transpose] at h
  erw [DoubleCategoryStruct.transpose_cast] at h
  exact h

end RepresentedImplicitDoubleFunctor

/-- An isomorphism of represented implicit double categories, with strict two-sided inverse
laws on the full generator-preserving double functors. -/
structure RepresentedImplicitDoubleIso (R₁ : D₁.Representation) (R₂ : D₂.Representation) where
  /-- The forward represented functor. -/
  hom : RepresentedImplicitDoubleFunctor R₁ R₂
  /-- The inverse represented functor. -/
  inv : RepresentedImplicitDoubleFunctor R₂ R₁
  /-- The forward functor followed by its inverse is the identity. -/
  hom_inv_id : hom.comp inv = RepresentedImplicitDoubleFunctor.id R₁
  /-- The inverse followed by the forward functor is the identity. -/
  inv_hom_id : inv.comp hom = RepresentedImplicitDoubleFunctor.id R₂

namespace RepresentedImplicitDoubleIso

attribute [simp] hom_inv_id inv_hom_id

variable {R₁ : D₁.Representation} {R₂ : D₂.Representation} {R₃ : D₃.Representation}

/-- Forget the representation and generator conditions, retaining a strict double
isomorphism. Its body is reducible so the boundary maps compute when applying the
existing inverse laws to arbitrary cells. -/
abbrev toStrictDoubleIso (e : RepresentedImplicitDoubleIso R₁ R₂) : StrictDoubleIso D₁ D₂ where
  hom := e.hom.toStrictDoubleFunctor
  inv := e.inv.toStrictDoubleFunctor
  hom_inv_id := congrArg
    (fun F : RepresentedImplicitDoubleFunctor R₁ R₁ ↦ F.toStrictDoubleFunctor) e.hom_inv_id
  inv_hom_id := congrArg
    (fun F : RepresentedImplicitDoubleFunctor R₂ R₂ ↦ F.toStrictDoubleFunctor) e.inv_hom_id

@[simp]
theorem toStrictDoubleIso_hom (e : RepresentedImplicitDoubleIso R₁ R₂) :
    e.toStrictDoubleIso.hom = e.hom.toStrictDoubleFunctor := (rfl)

@[simp]
theorem toStrictDoubleIso_inv (e : RepresentedImplicitDoubleIso R₁ R₂) :
    e.toStrictDoubleIso.inv = e.inv.toStrictDoubleFunctor := (rfl)

/-- A represented double isomorphism is determined by its forward functor. -/
@[ext]
theorem ext {e e' : RepresentedImplicitDoubleIso R₁ R₂} (h : e.hom = e'.hom) : e = e' := by
  have hi : e.inv = e'.inv := by
    apply RepresentedImplicitDoubleFunctor.ext
    apply ImplicitDoubleFunctor.ext
    have he : e.toStrictDoubleIso = e'.toStrictDoubleIso := by
      apply StrictDoubleIso.ext
      simpa only [toStrictDoubleIso_hom] using
        congrArg (fun F : RepresentedImplicitDoubleFunctor R₁ R₂ ↦ F.toStrictDoubleFunctor) h
    exact congrArg StrictDoubleIso.inv he
  cases e
  cases e'
  cases h
  cases hi
  rfl

variable (R₁) in
/-- The identity represented double isomorphism. -/
def refl : RepresentedImplicitDoubleIso R₁ R₁ where
  hom := RepresentedImplicitDoubleFunctor.id R₁
  inv := RepresentedImplicitDoubleFunctor.id R₁
  hom_inv_id := RepresentedImplicitDoubleFunctor.id_comp _
  inv_hom_id := RepresentedImplicitDoubleFunctor.id_comp _

/-- Reverse a represented double isomorphism. -/
def symm (e : RepresentedImplicitDoubleIso R₁ R₂) : RepresentedImplicitDoubleIso R₂ R₁ where
  hom := e.inv
  inv := e.hom
  hom_inv_id := e.inv_hom_id
  inv_hom_id := e.hom_inv_id

/-- Compose represented double isomorphisms in diagrammatic order. -/
def trans (e : RepresentedImplicitDoubleIso R₁ R₂) (e' : RepresentedImplicitDoubleIso R₂ R₃) :
    RepresentedImplicitDoubleIso R₁ R₃ where
  hom := e.hom.comp e'.hom
  inv := e'.inv.comp e.inv
  hom_inv_id := by
    rw [RepresentedImplicitDoubleFunctor.comp_assoc,
      ← RepresentedImplicitDoubleFunctor.comp_assoc e'.hom, e'.hom_inv_id,
      RepresentedImplicitDoubleFunctor.id_comp, e.hom_inv_id]
  inv_hom_id := by
    rw [RepresentedImplicitDoubleFunctor.comp_assoc,
      ← RepresentedImplicitDoubleFunctor.comp_assoc e.inv, e.inv_hom_id,
      RepresentedImplicitDoubleFunctor.id_comp, e'.inv_hom_id]

@[simp]
theorem refl_hom : (refl R₁).hom = RepresentedImplicitDoubleFunctor.id R₁ := (rfl)

@[simp]
theorem refl_inv : (refl R₁).inv = RepresentedImplicitDoubleFunctor.id R₁ := (rfl)

@[simp]
theorem symm_hom (e : RepresentedImplicitDoubleIso R₁ R₂) : e.symm.hom = e.inv := (rfl)

@[simp]
theorem symm_inv (e : RepresentedImplicitDoubleIso R₁ R₂) : e.symm.inv = e.hom := (rfl)

@[simp]
theorem trans_hom (e : RepresentedImplicitDoubleIso R₁ R₂)
    (e' : RepresentedImplicitDoubleIso R₂ R₃) : (e.trans e').hom = e.hom.comp e'.hom := (rfl)

@[simp]
theorem trans_inv (e : RepresentedImplicitDoubleIso R₁ R₂)
    (e' : RepresentedImplicitDoubleIso R₂ R₃) : (e.trans e').inv = e'.inv.comp e.inv := (rfl)

@[simp]
theorem symm_symm (e : RepresentedImplicitDoubleIso R₁ R₂) : e.symm.symm = e := (rfl)

@[simp]
theorem refl_trans (e : RepresentedImplicitDoubleIso R₁ R₂) : (refl R₁).trans e = e :=
  ext (RepresentedImplicitDoubleFunctor.id_comp _)

@[simp]
theorem trans_refl (e : RepresentedImplicitDoubleIso R₁ R₂) : e.trans (refl R₂) = e :=
  ext (RepresentedImplicitDoubleFunctor.comp_id _)

@[simp]
theorem self_trans_symm (e : RepresentedImplicitDoubleIso R₁ R₂) : e.trans e.symm = refl R₁ :=
  ext e.hom_inv_id

@[simp]
theorem symm_trans_self (e : RepresentedImplicitDoubleIso R₁ R₂) : e.symm.trans e = refl R₂ :=
  ext e.inv_hom_id

/-- Composition of represented double isomorphisms is associative. -/
theorem trans_assoc {O₄ : Type u₄} {H₄ : Quiver.{h₄} O₄} {V₄ : Quiver.{v₄} O₄}
    {D₄ : ImplicitDoubleCategory.{s₄} O₄ H₄ V₄} {R₄ : D₄.Representation}
    (e : RepresentedImplicitDoubleIso R₁ R₂) (e' : RepresentedImplicitDoubleIso R₂ R₃)
    (e'' : RepresentedImplicitDoubleIso R₃ R₄) :
    (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  ext (RepresentedImplicitDoubleFunctor.comp_assoc _ _ _)

end RepresentedImplicitDoubleIso

end TauCeti

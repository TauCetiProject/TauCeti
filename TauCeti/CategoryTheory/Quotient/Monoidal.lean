/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import TauCeti.CategoryTheory.Quotient.Iterated

/-!
# The monoidal structure on a quotient category

Let `C` be a monoidal category and `r : HomRel C` a relation on its morphisms. When `r` is
*monoidal*, that is stable under whiskering by arbitrary objects on either side
(`HomRel.IsMonoidal`), the monoidal structure of `C` descends to Mathlib's quotient category
`CategoryTheory.Quotient r`: the tensor product of objects is that of `C`, whiskering by an object
is induced by whiskering in `C`, and the associator and unitors are the classes of those of `C`.
No additivity is needed, and `r` need not be an equivalence relation or stable under composition:
the quotient category is formed by the congruence that `r` generates.

With this structure the quotient functor `C ⥤ Quotient r` is strong monoidal with identity
structure morphisms, the factorization `CategoryTheory.Quotient.lift` of a lax, oplax or strong
monoidal functor is lax, oplax or strong monoidal with the structure morphisms of that functor,
and monoidal natural
transformations descend along the quotient functor.

An arbitrary relation `r` generates a least monoidal relation, `HomRel.MonoidalClosure r`, and a
strong monoidal functor identifies the morphisms related by `r` exactly when it identifies those
related by `HomRel.MonoidalClosure r`. The quotient by `HomRel.MonoidalClosure r` is therefore
the monoidal category obtained from `C` by imposing the equations `r`; this is how monoidal
categories presented by generators and relations are built from free ones, and the quotient of a
monoidal preadditive category by a tensor ideal (`TauCeti.MonoidalQuotient`) is a special case.
Quotienting successively by two families of equations agrees with quotienting once by their union,
as a monoidal equivalence (`CategoryTheory.Quotient.iteratedEquiv` for monoidal relations, and
`CategoryTheory.Quotient.iteratedMonoidalEquiv` for arbitrary relations via `MonoidalClosure`).

## Main definitions and results

* `HomRel.IsMonoidal r`: the relation `r` is stable under whiskering on both sides. Strong
  monoidal functors induce monoidal relations (`HomRel.isMonoidal_homRel`), and `IsMonoidal` is
  preserved by `HomRel.sup` and `HomRel.mapQuotient`.
* `HomRel.MonoidalClosure r`: the least monoidal relation containing `r`, with
  `HomRel.MonoidalClosure.imp`, `HomRel.monoidalClosure_iff_self`,
  `HomRel.monoidalClosure_sup_iff`, and `HomRel.monoidalClosure_mapQuotient_iff`.
* the instance `MonoidalCategory (CategoryTheory.Quotient r)` for monoidal `r`, characterized by
  `CategoryTheory.Quotient.whiskerLeft_map`, `CategoryTheory.Quotient.map_whiskerRight`,
  `CategoryTheory.Quotient.map_tensorHom_map` and the corresponding lemmas for the associator and
  unitors;
* the instance `(CategoryTheory.Quotient.functor r).Monoidal`, with identity structure morphisms
  (`CategoryTheory.Quotient.functor_μ` and its companions);
* the instances `(CategoryTheory.Quotient.lift r F H).LaxMonoidal`, `.OplaxMonoidal` and
  `.Monoidal` for a lax, oplax or strong monoidal functor `F`, whose structure morphisms are those
  of `F` (`CategoryTheory.Quotient.lift_μ` and its companions), together with the instance saying
  that `CategoryTheory.Quotient.lift.isLift` is a monoidal natural isomorphism for lax monoidal
  `F`;
* the instance saying that `CategoryTheory.Quotient.natTransLift r τ` is monoidal when `τ` is;
* the monoidal equivalence instances on `CategoryTheory.Quotient.iteratedEquiv` (for monoidal
  relations) and `CategoryTheory.Quotient.iteratedMonoidalEquiv` (for arbitrary relations closed
  under whiskering).
-/

public section

universe v u v' u'

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace HomRel

/-- A relation on the morphisms of a monoidal category is **monoidal** when it is stable under
whiskering by arbitrary objects on either side. -/
class IsMonoidal (r : HomRel C) : Prop where
  /-- Left whiskering preserves the relation. -/
  whiskerLeft (X : C) {Y Z : C} {f g : Y ⟶ Z} : r f g → r (X ◁ f) (X ◁ g)
  /-- Right whiskering preserves the relation. -/
  whiskerRight {X Y : C} {f g : X ⟶ Y} (Z : C) : r f g → r (f ▷ Z) (g ▷ Z)

/-- Two morphisms identified by a strong monoidal functor stay identified after whiskering. -/
instance isMonoidal_homRel {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (F : C ⥤ D)
    [F.Monoidal] : F.homRel.IsMonoidal where
  whiskerLeft X _ _ _ _ h := by
    simp only [Functor.homRel_iff, Functor.Monoidal.map_whiskerLeft] at h ⊢
    rw [h]
  whiskerRight Z h := by
    simp only [Functor.homRel_iff, Functor.Monoidal.map_whiskerRight] at h ⊢
    rw [h]

/-- The **monoidal closure** of a relation: the least relation containing `r` which is stable
under whiskering on both sides. -/
inductive MonoidalClosure (r : HomRel C) : HomRel C
  | of {X Y : C} {f g : X ⟶ Y} : r f g → MonoidalClosure r f g
  | whiskerLeft (X : C) {Y Z : C} {f g : Y ⟶ Z} :
      MonoidalClosure r f g → MonoidalClosure r (X ◁ f) (X ◁ g)
  | whiskerRight {X Y : C} {f g : X ⟶ Y} (Z : C) :
      MonoidalClosure r f g → MonoidalClosure r (f ▷ Z) (g ▷ Z)

variable {r : HomRel C}

instance (r : HomRel C) : (MonoidalClosure r).IsMonoidal where
  whiskerLeft X _ _ _ _ := .whiskerLeft X
  whiskerRight Z := .whiskerRight Z

/-- The monoidal closure of `r` is contained in every monoidal relation containing `r`. -/
theorem MonoidalClosure.imp {s : HomRel C} [s.IsMonoidal]
    (h : ∀ ⦃X Y : C⦄ ⦃f g : X ⟶ Y⦄, r f g → s f g) {X Y : C} {f g : X ⟶ Y}
    (hfg : MonoidalClosure r f g) : s f g := by
  induction hfg with
  | of hfg => exact h hfg
  | whiskerLeft X _ ih => exact IsMonoidal.whiskerLeft X ih
  | whiskerRight Z _ ih => exact IsMonoidal.whiskerRight Z ih

/-- A monoidal relation is its own monoidal closure. -/
theorem monoidalClosure_iff_self [r.IsMonoidal] {X Y : C} (f g : X ⟶ Y) :
    MonoidalClosure r f g ↔ r f g :=
  ⟨MonoidalClosure.imp fun _ _ _ _ h ↦ h, MonoidalClosure.of⟩

/-- A strong monoidal functor identifies the morphisms related by the monoidal closure of `r` as
soon as it identifies those related by `r`. -/
theorem MonoidalClosure.map_eq {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {F : C ⥤ D}
    [F.Monoidal] (h : ∀ ⦃X Y : C⦄ ⦃f g : X ⟶ Y⦄, r f g → F.map f = F.map g) {X Y : C}
    {f g : X ⟶ Y} (hfg : MonoidalClosure r f g) : F.map f = F.map g :=
  MonoidalClosure.imp (s := F.homRel) h hfg

/-- The union of two monoidal relations is monoidal. -/
instance IsMonoidal.sup (r₁ r₂ : HomRel C) [r₁.IsMonoidal] [r₂.IsMonoidal] :
    (r₁.sup r₂).IsMonoidal where
  whiskerLeft X _ _ _ _ h := h.imp (IsMonoidal.whiskerLeft X) (IsMonoidal.whiskerLeft X)
  whiskerRight Z h := h.imp (IsMonoidal.whiskerRight Z) (IsMonoidal.whiskerRight Z)

/-- The monoidal closure of a union of two relations is the union of their monoidal closures. -/
theorem monoidalClosure_sup_iff (r₁ r₂ : HomRel C) {X Y : C} (f g : X ⟶ Y) :
    MonoidalClosure (r₁.sup r₂) f g ↔ (MonoidalClosure r₁).sup (MonoidalClosure r₂) f g := by
  constructor
  · exact MonoidalClosure.imp (s := (MonoidalClosure r₁).sup (MonoidalClosure r₂))
      fun _ _ _ _ h ↦ h.imp MonoidalClosure.of MonoidalClosure.of
  · rintro (h₁ | h₂)
    · exact MonoidalClosure.imp (s := MonoidalClosure (r₁.sup r₂))
        (fun _ _ _ _ h ↦ MonoidalClosure.of (.inl h)) h₁
    · exact MonoidalClosure.imp (s := MonoidalClosure (r₁.sup r₂))
        (fun _ _ _ _ h ↦ MonoidalClosure.of (.inr h)) h₂

end HomRel

namespace CategoryTheory.Quotient

variable (r : HomRel C) [r.IsMonoidal]

/-- The monoidal data descended to the quotient by a monoidal relation: tensor products,
associator and unitors are the classes of those of `C`, and whiskering by the class of `W` is the
factorization `CategoryTheory.Quotient.lift` of `tensorLeft W` or `tensorRight W` followed by the
quotient functor. -/
instance monoidalCategoryStruct : MonoidalCategoryStruct (Quotient r) where
  tensorObj X Y := (functor r).obj (X.as ⊗ Y.as)
  whiskerLeft X _ _ f :=
    (lift r (tensorLeft X.as ⋙ functor r) fun _ _ _ _ h ↦
      Quotient.sound r (HomRel.IsMonoidal.whiskerLeft X.as h)).map f
  whiskerRight f Y :=
    (lift r (tensorRight Y.as ⋙ functor r) fun _ _ _ _ h ↦
      Quotient.sound r (HomRel.IsMonoidal.whiskerRight Y.as h)).map f
  tensorUnit := (functor r).obj (𝟙_ C)
  associator X Y Z := (functor r).mapIso (α_ X.as Y.as Z.as)
  leftUnitor X := (functor r).mapIso (λ_ X.as)
  rightUnitor X := (functor r).mapIso (ρ_ X.as)

/-- The monoidal category structure on the quotient by a monoidal relation, descended from that
of `C`. -/
-- Each structure morphism of the quotient is, by construction, the class of the corresponding
-- morphism of `C`, and composition of classes is the class of the composite; so once the objects
-- and morphisms are written as classes, each axiom is definitionally the image of the axiom of `C`
-- (with `tensorHom_def` unfolding the tensor product of morphisms into whiskerings).
instance monoidalCategory : MonoidalCategory (Quotient r) where
  id_tensorHom_id := by
    rintro ⟨X⟩ ⟨Y⟩
    exact congrArg (functor r).map ((tensorHom_def _ _).symm.trans (id_tensorHom_id X Y))
  tensorHom_comp_tensorHom := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ f₁ f₂ g₁ g₂
    obtain ⟨f₁, rfl⟩ := (functor r).map_surjective f₁
    obtain ⟨f₂, rfl⟩ := (functor r).map_surjective f₂
    obtain ⟨g₁, rfl⟩ := (functor r).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (functor r).map_surjective g₂
    have h := tensorHom_comp_tensorHom f₁ f₂ g₁ g₂
    simp only [tensorHom_def] at h
    exact congrArg (functor r).map h
  whiskerLeft_id := by
    rintro ⟨X⟩ ⟨Y⟩
    exact congrArg (functor r).map (MonoidalCategory.whiskerLeft_id X Y)
  id_whiskerRight := by
    rintro ⟨X⟩ ⟨Y⟩
    exact congrArg (functor r).map (MonoidalCategory.id_whiskerRight X Y)
  associator_naturality := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ f₁ f₂ f₃
    obtain ⟨f₁, rfl⟩ := (functor r).map_surjective f₁
    obtain ⟨f₂, rfl⟩ := (functor r).map_surjective f₂
    obtain ⟨f₃, rfl⟩ := (functor r).map_surjective f₃
    have h := associator_naturality f₁ f₂ f₃
    simp only [tensorHom_def] at h
    exact congrArg (functor r).map h
  leftUnitor_naturality := by
    rintro ⟨⟩ ⟨⟩ f
    obtain ⟨f, rfl⟩ := (functor r).map_surjective f
    exact congrArg (functor r).map (leftUnitor_naturality f)
  rightUnitor_naturality := by
    rintro ⟨⟩ ⟨⟩ f
    obtain ⟨f, rfl⟩ := (functor r).map_surjective f
    exact congrArg (functor r).map (rightUnitor_naturality f)
  pentagon := by
    rintro ⟨W⟩ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
    exact congrArg (functor r).map (MonoidalCategory.pentagon W X Y Z)
  triangle := by
    rintro ⟨X⟩ ⟨Y⟩
    exact congrArg (functor r).map (MonoidalCategory.triangle X Y)

variable {r}

/-! ### The descended structure on classes -/

/-- The tensor product of the classes of two objects is the class of their tensor product. -/
theorem obj_tensorObj_obj (X Y : C) :
    (functor r).obj X ⊗ (functor r).obj Y = (functor r).obj (X ⊗ Y) :=
  (rfl)

/-- The tensor unit of the quotient is the class of the tensor unit. -/
theorem tensorUnit_eq : 𝟙_ (Quotient r) = (functor r).obj (𝟙_ C) :=
  (rfl)

/-- Left whiskering of a class is the class of the left whiskering. -/
@[simp]
theorem whiskerLeft_map (X : C) {Y Z : C} (f : Y ⟶ Z) :
    (functor r).obj X ◁ (functor r).map f = (functor r).map (X ◁ f) :=
  (rfl)

/-- Right whiskering of a class is the class of the right whiskering. -/
@[simp]
theorem map_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) :
    (functor r).map f ▷ (functor r).obj Z = (functor r).map (f ▷ Z) :=
  (rfl)

/-- The tensor product of the classes of two morphisms is the class of their tensor product. -/
@[simp]
theorem map_tensorHom_map {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (functor r).map f ⊗ₘ (functor r).map g = (functor r).map (f ⊗ₘ g) := by
  rw [tensorHom_def, map_whiskerRight, whiskerLeft_map, ← Functor.map_comp, ← tensorHom_def]

/-- The associator of classes is the class of the associator. -/
@[simp]
theorem associator_hom_obj (X Y Z : C) :
    (α_ ((functor r).obj X) ((functor r).obj Y) ((functor r).obj Z)).hom =
      (functor r).map (α_ X Y Z).hom :=
  (rfl)

/-- The inverse associator of classes is the class of the inverse associator. -/
@[simp]
theorem associator_inv_obj (X Y Z : C) :
    (α_ ((functor r).obj X) ((functor r).obj Y) ((functor r).obj Z)).inv =
      (functor r).map (α_ X Y Z).inv :=
  (rfl)

/- The unitor lemmas are not `@[simp]`: the Mathlib simp lemmas
`Functor.LaxMonoidal.left_unitality` and `right_unitality` rewrite their right-hand sides back
into unitors of the quotient. -/

/-- The left unitor of a class is the class of the left unitor. -/
theorem leftUnitor_hom_obj (X : C) :
    (λ_ ((functor r).obj X)).hom = (functor r).map (λ_ X).hom :=
  (rfl)

/-- The inverse left unitor of a class is the class of the inverse left unitor. -/
theorem leftUnitor_inv_obj (X : C) :
    (λ_ ((functor r).obj X)).inv = (functor r).map (λ_ X).inv :=
  (rfl)

/-- The right unitor of a class is the class of the right unitor. -/
theorem rightUnitor_hom_obj (X : C) :
    (ρ_ ((functor r).obj X)).hom = (functor r).map (ρ_ X).hom :=
  (rfl)

/-- The inverse right unitor of a class is the class of the inverse right unitor. -/
theorem rightUnitor_inv_obj (X : C) :
    (ρ_ ((functor r).obj X)).inv = (functor r).map (ρ_ X).inv :=
  (rfl)

/-! ### The quotient functor is strict monoidal -/

variable (r) in
/-- The quotient functor onto the quotient by a monoidal relation is strong monoidal, with
identity structure isomorphisms. -/
instance functorMonoidal : (functor r).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _
      μIso_hom_natural_left _ _ := by
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, map_whiskerRight]
      μIso_hom_natural_right _ _ := by
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, whiskerLeft_map]
      associativity _ _ _ := by
        simp only [Iso.refl_hom, Category.id_comp, associator_hom_obj, id_whiskerRight,
          MonoidalCategory.whiskerLeft_id, Category.comp_id]
      left_unitality _ := by
        simp only [Iso.refl_hom, leftUnitor_hom_obj, id_whiskerRight, Category.id_comp]
      right_unitality _ := by
        simp only [Iso.refl_hom, rightUnitor_hom_obj, MonoidalCategory.whiskerLeft_id,
          Category.id_comp] }

/-- The unit morphism of the quotient functor is the identity. -/
@[simp]
theorem functor_ε : Functor.LaxMonoidal.ε (functor r) = 𝟙 _ :=
  (rfl)

/-- The counit morphism of the quotient functor is the identity. -/
@[simp]
theorem functor_η : Functor.OplaxMonoidal.η (functor r) = 𝟙 _ :=
  (rfl)

/-- The tensorator of the quotient functor is the identity. -/
@[simp]
theorem functor_μ (X Y : C) : Functor.LaxMonoidal.μ (functor r) X Y = 𝟙 _ :=
  (rfl)

/-- The inverse tensorator of the quotient functor is the identity. -/
@[simp]
theorem functor_δ (X Y : C) : Functor.OplaxMonoidal.δ (functor r) X Y = 𝟙 _ :=
  (rfl)

/-! ### Monoidal factorization through the quotient -/

section lift

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] (F : C ⥤ D)
  (H : ∀ (X Y : C) (f₁ f₂ : X ⟶ Y), r f₁ f₂ → F.map f₁ = F.map f₂)

/-- The factorization `CategoryTheory.Quotient.lift` through the quotient by a monoidal relation
of a lax monoidal functor is lax monoidal, with the unit morphism and tensorator of that
functor. -/
instance liftLaxMonoidal [F.LaxMonoidal] : (lift r F H).LaxMonoidal where
  ε := Functor.LaxMonoidal.ε F
  μ X Y := Functor.LaxMonoidal.μ F X.as Y.as
  μ_natural_left f Z := by
    obtain ⟨f, rfl⟩ := (functor r).map_surjective f
    exact Functor.LaxMonoidal.μ_natural_left F f Z.as
  μ_natural_right Z f := by
    obtain ⟨f, rfl⟩ := (functor r).map_surjective f
    exact Functor.LaxMonoidal.μ_natural_right F Z.as f
  associativity X Y Z := Functor.LaxMonoidal.associativity F X.as Y.as Z.as
  left_unitality X := Functor.LaxMonoidal.left_unitality F X.as
  right_unitality X := Functor.LaxMonoidal.right_unitality F X.as

/-- The factorization `CategoryTheory.Quotient.lift` through the quotient by a monoidal relation
of an oplax monoidal functor is oplax monoidal, with the counit morphism and inverse tensorator
of that functor. -/
instance liftOplaxMonoidal [F.OplaxMonoidal] : (lift r F H).OplaxMonoidal where
  η := Functor.OplaxMonoidal.η F
  δ X Y := Functor.OplaxMonoidal.δ F X.as Y.as
  δ_natural_left f Z := by
    obtain ⟨f, rfl⟩ := (functor r).map_surjective f
    exact Functor.OplaxMonoidal.δ_natural_left F f Z.as
  δ_natural_right Z f := by
    obtain ⟨f, rfl⟩ := (functor r).map_surjective f
    exact Functor.OplaxMonoidal.δ_natural_right F Z.as f
  oplax_associativity X Y Z := Functor.OplaxMonoidal.associativity F X.as Y.as Z.as
  oplax_left_unitality X := Functor.OplaxMonoidal.left_unitality F X.as
  oplax_right_unitality X := Functor.OplaxMonoidal.right_unitality F X.as

/-- The factorization `CategoryTheory.Quotient.lift` through the quotient by a monoidal relation
of a strong monoidal functor is strong monoidal, with the structure isomorphisms of that
functor. -/
instance liftMonoidal [F.Monoidal] : (lift r F H).Monoidal where
  toLaxMonoidal := liftLaxMonoidal F H
  toOplaxMonoidal := liftOplaxMonoidal F H
  ε_η := Functor.Monoidal.ε_η F
  η_ε := Functor.Monoidal.η_ε F
  μ_δ X Y := Functor.Monoidal.μ_δ F X.as Y.as
  δ_μ X Y := Functor.Monoidal.δ_μ F X.as Y.as

/-- The unit morphism of the factorization of `F` is that of `F`. -/
@[simp]
theorem lift_ε [F.LaxMonoidal] : Functor.LaxMonoidal.ε (lift r F H) = Functor.LaxMonoidal.ε F :=
  (rfl)

/-- The counit morphism of the factorization of `F` is that of `F`. -/
@[simp]
theorem lift_η [F.OplaxMonoidal] :
    Functor.OplaxMonoidal.η (lift r F H) = Functor.OplaxMonoidal.η F :=
  (rfl)

/-- On classes, the tensorator of the factorization of `F` is that of `F`. -/
@[simp]
theorem lift_μ [F.LaxMonoidal] (X Y : C) :
    Functor.LaxMonoidal.μ (lift r F H) ((functor r).obj X) ((functor r).obj Y) =
      Functor.LaxMonoidal.μ F X Y :=
  (rfl)

/-- On classes, the inverse tensorator of the factorization of `F` is that of `F`. -/
@[simp]
theorem lift_δ [F.OplaxMonoidal] (X Y : C) :
    Functor.OplaxMonoidal.δ (lift r F H) ((functor r).obj X) ((functor r).obj Y) =
      Functor.OplaxMonoidal.δ F X Y :=
  (rfl)

/-- The identification `CategoryTheory.Quotient.lift.isLift` of the quotient functor followed by
the factorization of `F` with `F` is a monoidal natural isomorphism. -/
instance [F.LaxMonoidal] : (lift.isLift r F H).hom.IsMonoidal where
  unit := by
    simp only [Functor.comp_obj, Functor.LaxMonoidal.comp_ε, lift_ε, functor_ε,
      CategoryTheory.Functor.map_id, Category.comp_id, lift.isLift_hom]
    exact Category.comp_id _
  tensor X Y := by
    simp only [Functor.comp_obj, Functor.LaxMonoidal.comp_μ, lift_μ, functor_μ,
      CategoryTheory.Functor.map_id, Category.comp_id, lift.isLift_hom]
    exact (Category.comp_id _).trans
      ((congrArg (· ≫ _) (id_tensorHom_id _ _)).trans (Category.id_comp _)).symm

end lift

/-! ### Descent of monoidal natural transformations -/

section natTransLift

variable {D : Type u'} [Category.{v'} D] [MonoidalCategory D] {F G : Quotient r ⥤ D}
  [F.LaxMonoidal] [G.LaxMonoidal]

/-- A natural transformation between lax monoidal functors out of the quotient by a monoidal
relation is monoidal as soon as its restriction along the quotient functor is. -/
instance (τ : functor r ⋙ F ⟶ functor r ⋙ G) [τ.IsMonoidal] : (natTransLift r τ).IsMonoidal where
  unit := by
    have h := NatTrans.IsMonoidal.unit (τ := τ)
    simp only [Functor.comp_obj, Functor.LaxMonoidal.comp_ε, functor_ε,
      CategoryTheory.Functor.map_id, Category.comp_id] at h
    exact h
  tensor X Y := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    have h := NatTrans.IsMonoidal.tensor (τ := τ) X Y
    simp only [Functor.comp_obj, Functor.LaxMonoidal.comp_μ, functor_μ,
      CategoryTheory.Functor.map_id, Category.comp_id] at h
    exact h

end natTransLift

end CategoryTheory.Quotient

namespace HomRel

/-- The image in `Quotient r₁` of a monoidal relation `r₂` is monoidal when `r₁` is monoidal. -/
instance IsMonoidal.mapQuotient (r₁ r₂ : HomRel C) [r₁.IsMonoidal] [r₂.IsMonoidal] :
    (r₁.mapQuotient r₂).IsMonoidal where
  whiskerLeft X _ _ _ _ := by
    rintro ⟨f', g', rfl, rfl, h⟩
    exact ⟨X.as ◁ f', X.as ◁ g', rfl, rfl, IsMonoidal.whiskerLeft X.as h⟩
  whiskerRight Z := by
    rintro ⟨f', g', rfl, rfl, h⟩
    exact ⟨f' ▷ Z.as, g' ▷ Z.as, rfl, rfl, IsMonoidal.whiskerRight Z.as h⟩

/-- The monoidal closure of the image of `r₂` in `Quotient r₁` agrees with the image of the
monoidal closure of `r₂`. -/
theorem monoidalClosure_mapQuotient_iff (r₁ r₂ : HomRel C) [r₁.IsMonoidal]
    {X Y : CategoryTheory.Quotient r₁} (f g : X ⟶ Y) :
    MonoidalClosure (r₁.mapQuotient r₂) f g ↔ r₁.mapQuotient (MonoidalClosure r₂) f g := by
  constructor
  · exact MonoidalClosure.imp (s := r₁.mapQuotient (MonoidalClosure r₂))
      fun _ _ _ _ ⟨f', g', hf, hg, h⟩ ↦ ⟨f', g', hf, hg, MonoidalClosure.of h⟩
  · rintro ⟨f', g', rfl, rfl, h⟩
    have key : ∀ {A B : C} {u v : A ⟶ B}, MonoidalClosure r₂ u v →
        MonoidalClosure (r₁.mapQuotient r₂)
          ((CategoryTheory.Quotient.functor r₁).map u)
          ((CategoryTheory.Quotient.functor r₁).map v) := by
      intro A B u v huv
      induction huv with
      | of h => exact MonoidalClosure.of ⟨_, _, rfl, rfl, h⟩
      | whiskerLeft W _ ih =>
          exact MonoidalClosure.whiskerLeft ((CategoryTheory.Quotient.functor r₁).obj W) ih
      | whiskerRight W _ ih =>
          exact MonoidalClosure.whiskerRight ((CategoryTheory.Quotient.functor r₁).obj W) ih
    exact key h

end HomRel

namespace CategoryTheory.Quotient

/-! ### Iterated monoidal quotients -/

section IteratedMonoidalRelations

variable (r₁ r₂ : HomRel C) [r₁.IsMonoidal] [r₂.IsMonoidal]

/-- The equivalence `iteratedToSup` between an iterated quotient by two monoidal relations and the
combined quotient is strong monoidal, with identity structure morphisms. -/
instance instMonoidalIteratedToSup : (iteratedToSup r₁ r₂).Monoidal :=
  liftMonoidal (r := r₁.mapQuotient r₂)
    (lift r₁ (functor (r₁.sup r₂)) fun _ _ _ _ h ↦ Quotient.sound _ (.inl h)) _

/-- The inverse equivalence `supToIterated` is strong monoidal, with identity structure
morphisms. -/
instance instMonoidalSupToIterated : (supToIterated r₁ r₂).Monoidal :=
  liftMonoidal (r := r₁.sup r₂) (functor r₁ ⋙ functor (r₁.mapQuotient r₂)) _

instance instMonoidalIteratedEquivFunctor : (iteratedEquiv r₁ r₂).functor.Monoidal :=
  instMonoidalIteratedToSup r₁ r₂

instance instMonoidalIteratedEquivInverse : (iteratedEquiv r₁ r₂).inverse.Monoidal :=
  instMonoidalSupToIterated r₁ r₂

@[simp]
theorem iteratedToSup_ε : Functor.LaxMonoidal.ε (iteratedToSup r₁ r₂) = 𝟙 _ := rfl

@[simp]
theorem iteratedToSup_η : Functor.OplaxMonoidal.η (iteratedToSup r₁ r₂) = 𝟙 _ := rfl

@[simp]
theorem iteratedToSup_μ (X Y : Quotient (r₁.mapQuotient r₂)) :
    Functor.LaxMonoidal.μ (iteratedToSup r₁ r₂) X Y = 𝟙 _ := rfl

@[simp]
theorem iteratedToSup_δ (X Y : Quotient (r₁.mapQuotient r₂)) :
    Functor.OplaxMonoidal.δ (iteratedToSup r₁ r₂) X Y = 𝟙 _ := rfl

@[simp]
theorem supToIterated_ε : Functor.LaxMonoidal.ε (supToIterated r₁ r₂) = 𝟙 _ := by
  refine (lift_ε _ _).trans ?_
  simp only [Functor.LaxMonoidal.comp_ε, functor_ε, Category.id_comp]
  exact (functor (r₁.mapQuotient r₂)).map_id _

@[simp]
theorem supToIterated_η : Functor.OplaxMonoidal.η (supToIterated r₁ r₂) = 𝟙 _ := by
  refine (lift_η _ _).trans ?_
  simp only [Functor.OplaxMonoidal.comp_η, functor_η, Category.comp_id]
  exact (functor (r₁.mapQuotient r₂)).map_id _

@[simp]
theorem supToIterated_μ (X Y : Quotient (r₁.sup r₂)) :
    Functor.LaxMonoidal.μ (supToIterated r₁ r₂) X Y = 𝟙 _ := by
  refine (lift_μ _ _ X.as Y.as).trans ?_
  simp only [Functor.LaxMonoidal.comp_μ, functor_μ]
  exact (Category.id_comp _).trans ((functor (r₁.mapQuotient r₂)).map_id _)

@[simp]
theorem supToIterated_δ (X Y : Quotient (r₁.sup r₂)) :
    Functor.OplaxMonoidal.δ (supToIterated r₁ r₂) X Y = 𝟙 _ := by
  refine (lift_δ _ _ X.as Y.as).trans ?_
  simp only [Functor.OplaxMonoidal.comp_δ, functor_δ, Category.comp_id]
  exact (functor (r₁.mapQuotient r₂)).map_id _

/-- The equivalence between an iterated quotient by two monoidal relations and the quotient by
their union is monoidal. -/
instance iteratedEquivIsMonoidal : (iteratedEquiv r₁ r₂).IsMonoidal where
  leftAdjoint_ε :=
    (supToIterated_ε r₁ r₂).trans
      ((Category.id_comp _).symm.trans
        (congrArg (𝟙 _ ≫ ·) (CategoryTheory.Functor.map_id (supToIterated r₁ r₂) _).symm))
  leftAdjoint_μ X Y :=
    (supToIterated_μ r₁ r₂ X Y).trans
      ((Category.id_comp _).symm.trans (congrArg (𝟙 _ ≫ ·)
        ((CategoryTheory.Functor.map_id (supToIterated r₁ r₂) _).symm.trans
          (congrArg (supToIterated r₁ r₂).map
            ((Category.id_comp _).symm.trans
              (congrArg (𝟙 _ ≫ ·) (id_tensorHom_id _ _).symm))))))

end IteratedMonoidalRelations

section IteratedMonoidalClosure

variable (r₁ r₂ : HomRel C)

/-- The canonical functor from the iterated monoidal quotient (first closing `r₁` under whiskering,
then closing the image of `r₂` under whiskering) to the single monoidal quotient by `r₁.sup r₂`. -/
@[expose] def iteratedMonoidalToSup :
    Quotient (HomRel.MonoidalClosure ((HomRel.MonoidalClosure r₁).mapQuotient r₂)) ⥤
      Quotient (HomRel.MonoidalClosure (r₁.sup r₂)) :=
  lift (HomRel.MonoidalClosure ((HomRel.MonoidalClosure r₁).mapQuotient r₂))
    (lift (HomRel.MonoidalClosure r₁) (functor (HomRel.MonoidalClosure (r₁.sup r₂)))
      fun _ _ _ _ h ↦ HomRel.MonoidalClosure.map_eq
        (fun _ _ _ _ h₁ ↦ Quotient.sound _ (.of (.inl h₁))) h)
    fun _ _ _ _ h ↦ HomRel.MonoidalClosure.map_eq
      (fun _ _ _ _ ⟨_, _, hf, hg, h₂⟩ ↦ by
        rw [← hf, ← hg]
        exact Quotient.sound _ (.of (.inr h₂))) h

/-- The canonical functor from the single monoidal quotient by `r₁.sup r₂` to the iterated
monoidal quotient. -/
@[expose] def supToIteratedMonoidal :
    Quotient (HomRel.MonoidalClosure (r₁.sup r₂)) ⥤
      Quotient (HomRel.MonoidalClosure ((HomRel.MonoidalClosure r₁).mapQuotient r₂)) :=
  lift (HomRel.MonoidalClosure (r₁.sup r₂))
    (functor (HomRel.MonoidalClosure r₁) ⋙
      functor (HomRel.MonoidalClosure ((HomRel.MonoidalClosure r₁).mapQuotient r₂)))
    fun _ _ _ _ h ↦ HomRel.MonoidalClosure.map_eq (fun _ _ _ _ h₁₂ ↦ by
      rcases h₁₂ with h₁ | h₂
      · exact congrArg
          (functor (HomRel.MonoidalClosure ((HomRel.MonoidalClosure r₁).mapQuotient r₂))).map
          (Quotient.sound _ (.of h₁))
      · exact Quotient.sound _ (.of (HomRel.mapQuotient_of _ h₂))) h

instance instMonoidalIteratedMonoidalToSup : (iteratedMonoidalToSup r₁ r₂).Monoidal :=
  liftMonoidal (r := HomRel.MonoidalClosure ((HomRel.MonoidalClosure r₁).mapQuotient r₂))
    (lift (HomRel.MonoidalClosure r₁) (functor (HomRel.MonoidalClosure (r₁.sup r₂))) _) _

instance instMonoidalSupToIteratedMonoidal : (supToIteratedMonoidal r₁ r₂).Monoidal :=
  liftMonoidal (r := HomRel.MonoidalClosure (r₁.sup r₂))
    (functor (HomRel.MonoidalClosure r₁) ⋙
      functor (HomRel.MonoidalClosure ((HomRel.MonoidalClosure r₁).mapQuotient r₂))) _

theorem functor_comp_iteratedMonoidalToSup :
    functor (HomRel.MonoidalClosure r₁) ⋙
        functor (HomRel.MonoidalClosure ((HomRel.MonoidalClosure r₁).mapQuotient r₂)) ⋙
        iteratedMonoidalToSup r₁ r₂ =
      functor (HomRel.MonoidalClosure (r₁.sup r₂)) :=
  rfl

theorem functor_comp_supToIteratedMonoidal :
    functor (HomRel.MonoidalClosure (r₁.sup r₂)) ⋙ supToIteratedMonoidal r₁ r₂ =
      functor (HomRel.MonoidalClosure r₁) ⋙
        functor (HomRel.MonoidalClosure ((HomRel.MonoidalClosure r₁).mapQuotient r₂)) :=
  rfl

@[simp]
theorem iteratedMonoidalToSup_ε :
    Functor.LaxMonoidal.ε (iteratedMonoidalToSup r₁ r₂) = 𝟙 _ := rfl

@[simp]
theorem iteratedMonoidalToSup_η :
    Functor.OplaxMonoidal.η (iteratedMonoidalToSup r₁ r₂) = 𝟙 _ := rfl

@[simp]
theorem iteratedMonoidalToSup_μ
    (X Y : Quotient (HomRel.MonoidalClosure ((HomRel.MonoidalClosure r₁).mapQuotient r₂))) :
    Functor.LaxMonoidal.μ (iteratedMonoidalToSup r₁ r₂) X Y = 𝟙 _ := rfl

@[simp]
theorem iteratedMonoidalToSup_δ
    (X Y : Quotient (HomRel.MonoidalClosure ((HomRel.MonoidalClosure r₁).mapQuotient r₂))) :
    Functor.OplaxMonoidal.δ (iteratedMonoidalToSup r₁ r₂) X Y = 𝟙 _ := rfl

@[simp]
theorem supToIteratedMonoidal_ε :
    Functor.LaxMonoidal.ε (supToIteratedMonoidal r₁ r₂) = 𝟙 _ := by
  refine (lift_ε _ _).trans ?_
  simp only [Functor.LaxMonoidal.comp_ε, functor_ε, Category.id_comp]
  exact (functor _).map_id _

@[simp]
theorem supToIteratedMonoidal_η :
    Functor.OplaxMonoidal.η (supToIteratedMonoidal r₁ r₂) = 𝟙 _ := by
  refine (lift_η _ _).trans ?_
  simp only [Functor.OplaxMonoidal.comp_η, functor_η, Category.comp_id]
  exact (functor _).map_id _

@[simp]
theorem supToIteratedMonoidal_μ (X Y : Quotient (HomRel.MonoidalClosure (r₁.sup r₂))) :
    Functor.LaxMonoidal.μ (supToIteratedMonoidal r₁ r₂) X Y = 𝟙 _ := by
  refine (lift_μ _ _ X.as Y.as).trans ?_
  simp only [Functor.LaxMonoidal.comp_μ, functor_μ]
  exact (Category.id_comp _).trans ((functor _).map_id _)

@[simp]
theorem supToIteratedMonoidal_δ (X Y : Quotient (HomRel.MonoidalClosure (r₁.sup r₂))) :
    Functor.OplaxMonoidal.δ (supToIteratedMonoidal r₁ r₂) X Y = 𝟙 _ := by
  refine (lift_δ _ _ X.as Y.as).trans ?_
  simp only [Functor.OplaxMonoidal.comp_δ, functor_δ, Category.comp_id]
  exact (functor _).map_id _

theorem iteratedMonoidalToSup_comp_supToIteratedMonoidal :
    iteratedMonoidalToSup r₁ r₂ ⋙ supToIteratedMonoidal r₁ r₂ = 𝟭 _ := by
  apply lift_unique' (HomRel.MonoidalClosure ((HomRel.MonoidalClosure r₁).mapQuotient r₂))
  apply lift_unique' (HomRel.MonoidalClosure r₁)
  rfl

theorem supToIteratedMonoidal_comp_iteratedMonoidalToSup :
    supToIteratedMonoidal r₁ r₂ ⋙ iteratedMonoidalToSup r₁ r₂ = 𝟭 _ := by
  apply lift_unique' (HomRel.MonoidalClosure (r₁.sup r₂))
  rfl

/-- Quotienting a monoidal category first by the monoidal closure of `r₁` and then by the monoidal
closure of the image of `r₂` is monoidally equivalent to quotienting once by the monoidal closure
of `r₁.sup r₂`. -/
@[expose] def iteratedMonoidalEquiv :
    Quotient (HomRel.MonoidalClosure ((HomRel.MonoidalClosure r₁).mapQuotient r₂)) ≌
      Quotient (HomRel.MonoidalClosure (r₁.sup r₂)) where
  functor := iteratedMonoidalToSup r₁ r₂
  inverse := supToIteratedMonoidal r₁ r₂
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) fun {X Y} f ↦ by
    obtain ⟨f, rfl⟩ :=
      (functor (HomRel.MonoidalClosure ((HomRel.MonoidalClosure r₁).mapQuotient r₂))).map_surjective
        f
    obtain ⟨f, rfl⟩ := (functor (HomRel.MonoidalClosure r₁)).map_surjective f
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) fun {X Y} f ↦ by
    obtain ⟨f, rfl⟩ := (functor (HomRel.MonoidalClosure (r₁.sup r₂))).map_surjective f
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  functor_unitIso_comp _ := Category.comp_id _

instance instMonoidalIteratedMonoidalEquivFunctor :
    (iteratedMonoidalEquiv r₁ r₂).functor.Monoidal :=
  instMonoidalIteratedMonoidalToSup r₁ r₂

instance instMonoidalIteratedMonoidalEquivInverse :
    (iteratedMonoidalEquiv r₁ r₂).inverse.Monoidal :=
  instMonoidalSupToIteratedMonoidal r₁ r₂

instance iteratedMonoidalEquivIsMonoidal : (iteratedMonoidalEquiv r₁ r₂).IsMonoidal where
  leftAdjoint_ε :=
    (supToIteratedMonoidal_ε r₁ r₂).trans
      ((Category.id_comp _).symm.trans
        (congrArg (𝟙 _ ≫ ·) (CategoryTheory.Functor.map_id (supToIteratedMonoidal r₁ r₂) _).symm))
  leftAdjoint_μ X Y :=
    (supToIteratedMonoidal_μ r₁ r₂ X Y).trans
      ((Category.id_comp _).symm.trans (congrArg (𝟙 _ ≫ ·)
        ((CategoryTheory.Functor.map_id (supToIteratedMonoidal r₁ r₂) _).symm.trans
          (congrArg (supToIteratedMonoidal r₁ r₂).map
            ((Category.id_comp _).symm.trans
              (congrArg (𝟙 _ ≫ ·) (id_tensorHom_id _ _).symm))))))

end IteratedMonoidalClosure

end CategoryTheory.Quotient

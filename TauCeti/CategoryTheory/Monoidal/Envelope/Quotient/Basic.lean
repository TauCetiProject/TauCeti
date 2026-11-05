/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Basic
public import TauCeti.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Quotients of monoidal preadditive categories by tensor ideals

A **tensor ideal** of a monoidal preadditive category `C` is a two-sided morphism ideal
(`TauCeti.MorphismIdeal`) that is in addition closed under whiskering by arbitrary objects on
either side, hence under tensoring with arbitrary morphisms. Since the whiskerings of a monoidal
preadditive category are additive, `W ◁ f - W ◁ g = W ◁ (f - g)`, so whiskering respects
congruence modulo such an ideal and the monoidal structure of `C` descends to the quotient
category `C/I`: the tensor product of the classes of two objects is the class of their tensor
product, the tensor product of the classes of two morphisms is the class of their tensor product,
and the associator and unitors are the classes of those of `C`. With this structure the quotient
functor `C ⥤ C/I` is strict monoidal, the quotient is again monoidal preadditive, and it is
monoidal `S`-linear whenever `C` is.

The additivity of the whiskerings is used here, not just closure of the ideal under whiskering:
descent asks for `W ◁ f - W ◁ g ∈ I` whenever `f - g ∈ I`, while closure only provides
`W ◁ (f - g) ∈ I`.

Quotients of this kind are the classical route from diagram categories to semisimple and fusion
categories: in a spherical category the negligible morphisms (those `f` with `tr (f ≫ g) = 0` for
every `g`) form a tensor ideal, and one passes to the quotient by it.

The preadditive and linear structures of the quotient, its zero detection
`TauCeti.MorphismIdeal.quotientFunctor_map_eq_zero_iff` and its additive factorizations are those
of `TauCeti.MorphismIdeal.Quotient`, which `TauCeti.MonoidalQuotient` abbreviates.

## Main definitions

* `TauCeti.MonoidalIdeal C`: a tensor ideal of the monoidal preadditive category `C`.
* `TauCeti.MonoidalQuotient I` and `TauCeti.toMonoidalQuotient I`: the quotient category `C/I`
  and the quotient functor `C ⥤ C/I`.

## Main results

* the instance `MonoidalCategory (TauCeti.MonoidalQuotient I)`, the descended monoidal structure,
  characterized by `TauCeti.MonoidalQuotient.whiskerLeft_map`,
  `TauCeti.MonoidalQuotient.map_whiskerRight`, `TauCeti.MonoidalQuotient.map_tensorHom_map` and
  the corresponding lemmas for the associator and unitors;
* the instance `(TauCeti.toMonoidalQuotient I).Monoidal`: the quotient functor is strong
  monoidal, with identity structure morphisms (`TauCeti.MonoidalQuotient.μ_eq` and its
  companions);
* the universal property: for a strong monoidal additive functor `F` killing `I`, the instance
  `(I.toMorphismIdeal.lift F hF).Monoidal`, whose structure morphisms are those of `F`
  (`TauCeti.MonoidalQuotient.lift_μ` and its companions), and the instance saying that
  `CategoryTheory.Quotient.lift.isLift`, identifying the composite with the quotient functor
  with `F`, is a monoidal natural isomorphism;
* the instances `MonoidalPreadditive (TauCeti.MonoidalQuotient I)` and
  `MonoidalLinear S (TauCeti.MonoidalQuotient I)`.

## References

* J. W. Barrett and B. W. Westbury, *Spherical categories*, Adv. Math. 143 (1999), 357–375
  (the quotient of a spherical category by its negligible morphisms).
* F. M. Goodman and H. Wenzl, *Ideals in the Temperley–Lieb category*, appendix to
  M. H. Freedman, *A magnetic model with a possible Chern–Simons phase*, Comm. Math. Phys. 234
  (2003), 129–183.
-/

public section

universe v u v' u'

namespace TauCeti

open CategoryTheory MonoidalCategory

/-- A **tensor ideal** of a monoidal preadditive category `C`: a two-sided morphism ideal which
is closed under whiskering by arbitrary objects on either side. -/
structure MonoidalIdeal (C : Type u) [Category.{v} C] [Preadditive C] [MonoidalCategory C]
    extends MorphismIdeal C where
  /-- Left whiskering a member of the ideal stays in the ideal. -/
  whiskerLeft_mem (W : C) {X Y : C} {f : X ⟶ Y} : f ∈ hom X Y → W ◁ f ∈ hom (W ⊗ X) (W ⊗ Y)
  /-- Right whiskering a member of the ideal stays in the ideal. -/
  whiskerRight_mem {X Y : C} {f : X ⟶ Y} (W : C) : f ∈ hom X Y → f ▷ W ∈ hom (X ⊗ W) (Y ⊗ W)

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

namespace MonoidalIdeal

theorem toMorphismIdeal_injective :
    Function.Injective (toMorphismIdeal : MonoidalIdeal C → MorphismIdeal C)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

/-- Two tensor ideals with the same members are equal. -/
@[ext]
theorem ext {I J : MonoidalIdeal C}
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), f ∈ I.hom X Y ↔ f ∈ J.hom X Y) : I = J :=
  toMorphismIdeal_injective (MorphismIdeal.ext h)

variable (I : MonoidalIdeal C)

/-- A tensor product of morphisms lies in a tensor ideal as soon as its second factor does. -/
theorem tensorHom_mem_left {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) {g : X₂ ⟶ Y₂}
    (hg : g ∈ I.hom X₂ Y₂) : f ⊗ₘ g ∈ I.hom (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) := by
  rw [tensorHom_def]
  exact I.comp_mem_left _ (I.whiskerLeft_mem Y₁ hg)

/-- A tensor product of morphisms lies in a tensor ideal as soon as its first factor does. -/
theorem tensorHom_mem_right {X₁ Y₁ X₂ Y₂ : C} {f : X₁ ⟶ Y₁} (g : X₂ ⟶ Y₂)
    (hf : f ∈ I.hom X₁ Y₁) : f ⊗ₘ g ∈ I.hom (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) := by
  rw [tensorHom_def]
  exact I.comp_mem_right _ (I.whiskerRight_mem X₂ hf)

variable [MonoidalPreadditive C]

/-- In a monoidal preadditive category, left whiskering respects congruence modulo a tensor
ideal. -/
theorem rel_whiskerLeft (W : C) {X Y : C} {f g : X ⟶ Y} (h : I.rel f g) :
    I.rel (W ◁ f) (W ◁ g) := by
  rw [MorphismIdeal.rel_iff, ← whiskerLeft_sub]
  exact I.whiskerLeft_mem W (I.rel_iff.1 h)

/-- In a monoidal preadditive category, right whiskering respects congruence modulo a tensor
ideal. -/
theorem rel_whiskerRight {X Y : C} {f g : X ⟶ Y} (h : I.rel f g) (W : C) :
    I.rel (f ▷ W) (g ▷ W) := by
  rw [MorphismIdeal.rel_iff, ← sub_whiskerRight]
  exact I.whiskerRight_mem W (I.rel_iff.1 h)

end MonoidalIdeal

/-- The **quotient** `C/I` of a monoidal preadditive category by a tensor ideal: the quotient
category `TauCeti.MorphismIdeal.Quotient` of the underlying ideal, which carries the descended
monoidal structure. -/
abbrev MonoidalQuotient (I : MonoidalIdeal C) : Type u :=
  I.toMorphismIdeal.Quotient

/-- The quotient functor `C ⥤ C/I` onto the quotient by a tensor ideal. It is strict monoidal
for the descended monoidal structure. -/
abbrev toMonoidalQuotient (I : MonoidalIdeal C) : C ⥤ MonoidalQuotient I :=
  I.toMorphismIdeal.quotientFunctor

namespace MonoidalQuotient

variable [MonoidalPreadditive C] (I : MonoidalIdeal C)

/-- The monoidal data descended to the quotient by a tensor ideal: tensor products, whiskerings,
associator and unitors are the classes of those of `C`. Whiskering by the class of `W` is the
factorization `TauCeti.MorphismIdeal.lift` of `tensorLeft W` or `tensorRight W` followed by the
quotient functor, which kill the ideal. -/
noncomputable instance : MonoidalCategoryStruct (MonoidalQuotient I) where
  tensorObj X Y := (toMonoidalQuotient I).obj (X.as ⊗ Y.as)
  whiskerLeft X _ _ f :=
    (I.toMorphismIdeal.lift (tensorLeft X.as ⋙ toMonoidalQuotient I) fun _ _ _ hf ↦
      (Functor.mem_kerIdeal_hom _).2
        ((MorphismIdeal.quotientFunctor_map_eq_zero_iff _).2 (I.whiskerLeft_mem X.as hf))).map f
  whiskerRight f Y :=
    (I.toMorphismIdeal.lift (tensorRight Y.as ⋙ toMonoidalQuotient I) fun _ _ _ hf ↦
      (Functor.mem_kerIdeal_hom _).2
        ((MorphismIdeal.quotientFunctor_map_eq_zero_iff _).2 (I.whiskerRight_mem Y.as hf))).map f
  tensorUnit := (toMonoidalQuotient I).obj (𝟙_ C)
  associator X Y Z := (toMonoidalQuotient I).mapIso (α_ X.as Y.as Z.as)
  leftUnitor X := (toMonoidalQuotient I).mapIso (λ_ X.as)
  rightUnitor X := (toMonoidalQuotient I).mapIso (ρ_ X.as)

/-- The monoidal category structure on the quotient by a tensor ideal, descended from that of
`C`. -/
-- Each structure morphism of the quotient is, by construction, the class of the corresponding
-- morphism of `C`, and composition of classes is the class of the composite; so once the objects
-- and morphisms are written as classes, each axiom is definitionally the image of the axiom of `C`
-- (with `tensorHom_def` unfolding the tensor product of morphisms into whiskerings).
noncomputable instance : MonoidalCategory (MonoidalQuotient I) where
  id_tensorHom_id := by
    rintro ⟨X⟩ ⟨Y⟩
    exact congrArg (toMonoidalQuotient I).map ((tensorHom_def _ _).symm.trans (id_tensorHom_id X Y))
  tensorHom_comp_tensorHom := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ f₁ f₂ g₁ g₂
    obtain ⟨f₁, rfl⟩ := (toMonoidalQuotient I).map_surjective f₁
    obtain ⟨f₂, rfl⟩ := (toMonoidalQuotient I).map_surjective f₂
    obtain ⟨g₁, rfl⟩ := (toMonoidalQuotient I).map_surjective g₁
    obtain ⟨g₂, rfl⟩ := (toMonoidalQuotient I).map_surjective g₂
    have h := tensorHom_comp_tensorHom f₁ f₂ g₁ g₂
    simp only [tensorHom_def] at h
    exact congrArg (toMonoidalQuotient I).map h
  whiskerLeft_id := by
    rintro ⟨X⟩ ⟨Y⟩
    exact congrArg (toMonoidalQuotient I).map (MonoidalCategory.whiskerLeft_id X Y)
  id_whiskerRight := by
    rintro ⟨X⟩ ⟨Y⟩
    exact congrArg (toMonoidalQuotient I).map (MonoidalCategory.id_whiskerRight X Y)
  associator_naturality := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ f₁ f₂ f₃
    obtain ⟨f₁, rfl⟩ := (toMonoidalQuotient I).map_surjective f₁
    obtain ⟨f₂, rfl⟩ := (toMonoidalQuotient I).map_surjective f₂
    obtain ⟨f₃, rfl⟩ := (toMonoidalQuotient I).map_surjective f₃
    have h := associator_naturality f₁ f₂ f₃
    simp only [tensorHom_def] at h
    exact congrArg (toMonoidalQuotient I).map h
  leftUnitor_naturality := by
    rintro ⟨⟩ ⟨⟩ f
    obtain ⟨f, rfl⟩ := (toMonoidalQuotient I).map_surjective f
    exact congrArg (toMonoidalQuotient I).map (leftUnitor_naturality f)
  rightUnitor_naturality := by
    rintro ⟨⟩ ⟨⟩ f
    obtain ⟨f, rfl⟩ := (toMonoidalQuotient I).map_surjective f
    exact congrArg (toMonoidalQuotient I).map (rightUnitor_naturality f)
  pentagon := by
    rintro ⟨W⟩ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
    exact congrArg (toMonoidalQuotient I).map (MonoidalCategory.pentagon W X Y Z)
  triangle := by
    rintro ⟨X⟩ ⟨Y⟩
    exact congrArg (toMonoidalQuotient I).map (MonoidalCategory.triangle X Y)

variable {I}

/-! ### The descended structure on classes -/

/-- The tensor product of the classes of two objects is the class of their tensor product. -/
theorem obj_tensorObj_obj (X Y : C) :
    (toMonoidalQuotient I).obj X ⊗ (toMonoidalQuotient I).obj Y =
      (toMonoidalQuotient I).obj (X ⊗ Y) :=
  (rfl)

/-- The tensor unit of the quotient is the class of the tensor unit. -/
theorem tensorUnit_eq : 𝟙_ (MonoidalQuotient I) = (toMonoidalQuotient I).obj (𝟙_ C) :=
  (rfl)

/-- Left whiskering of a class is the class of the left whiskering. -/
@[simp]
theorem whiskerLeft_map (X : C) {Y Z : C} (f : Y ⟶ Z) :
    (toMonoidalQuotient I).obj X ◁ (toMonoidalQuotient I).map f =
      (toMonoidalQuotient I).map (X ◁ f) :=
  (rfl)

/-- Right whiskering of a class is the class of the right whiskering. -/
@[simp]
theorem map_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) :
    (toMonoidalQuotient I).map f ▷ (toMonoidalQuotient I).obj Z =
      (toMonoidalQuotient I).map (f ▷ Z) :=
  (rfl)

/-- The tensor product of the classes of two morphisms is the class of their tensor product. -/
@[simp]
theorem map_tensorHom_map {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (toMonoidalQuotient I).map f ⊗ₘ (toMonoidalQuotient I).map g =
      (toMonoidalQuotient I).map (f ⊗ₘ g) := by
  rw [tensorHom_def, map_whiskerRight, whiskerLeft_map, ← Functor.map_comp, ← tensorHom_def]

/-- The associator of classes is the class of the associator. -/
@[simp]
theorem associator_hom_obj (X Y Z : C) :
    (α_ ((toMonoidalQuotient I).obj X) ((toMonoidalQuotient I).obj Y)
      ((toMonoidalQuotient I).obj Z)).hom = (toMonoidalQuotient I).map (α_ X Y Z).hom :=
  (rfl)

/-- The inverse associator of classes is the class of the inverse associator. -/
@[simp]
theorem associator_inv_obj (X Y Z : C) :
    (α_ ((toMonoidalQuotient I).obj X) ((toMonoidalQuotient I).obj Y)
      ((toMonoidalQuotient I).obj Z)).inv = (toMonoidalQuotient I).map (α_ X Y Z).inv :=
  (rfl)

/-- The left unitor of a class is the class of the left unitor. -/
theorem leftUnitor_hom_obj (X : C) :
    (λ_ ((toMonoidalQuotient I).obj X)).hom = (toMonoidalQuotient I).map (λ_ X).hom :=
  (rfl)

/-- The inverse left unitor of a class is the class of the inverse left unitor. -/
theorem leftUnitor_inv_obj (X : C) :
    (λ_ ((toMonoidalQuotient I).obj X)).inv = (toMonoidalQuotient I).map (λ_ X).inv :=
  (rfl)

/-- The right unitor of a class is the class of the right unitor. -/
theorem rightUnitor_hom_obj (X : C) :
    (ρ_ ((toMonoidalQuotient I).obj X)).hom = (toMonoidalQuotient I).map (ρ_ X).hom :=
  (rfl)

/-- The inverse right unitor of a class is the class of the inverse right unitor. -/
theorem rightUnitor_inv_obj (X : C) :
    (ρ_ ((toMonoidalQuotient I).obj X)).inv = (toMonoidalQuotient I).map (ρ_ X).inv :=
  (rfl)

/-! ### The quotient functor is strict monoidal -/

variable (I) in
/-- The quotient functor onto the quotient by a tensor ideal is strong monoidal, with identity
structure isomorphisms. -/
noncomputable instance : (toMonoidalQuotient I).Monoidal :=
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
theorem ε_eq : Functor.LaxMonoidal.ε (toMonoidalQuotient I) = 𝟙 _ :=
  (rfl)

/-- The counit morphism of the quotient functor is the identity. -/
@[simp]
theorem η_eq : Functor.OplaxMonoidal.η (toMonoidalQuotient I) = 𝟙 _ :=
  (rfl)

/-- The tensorator of the quotient functor is the identity. -/
@[simp]
theorem μ_eq (X Y : C) : Functor.LaxMonoidal.μ (toMonoidalQuotient I) X Y = 𝟙 _ :=
  (rfl)

/-- The inverse tensorator of the quotient functor is the identity. -/
@[simp]
theorem δ_eq (X Y : C) : Functor.OplaxMonoidal.δ (toMonoidalQuotient I) X Y = 𝟙 _ :=
  (rfl)

/-! ### Monoidal factorization through the quotient -/

section lift

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [MonoidalCategory D] (F : C ⥤ D)
  [F.Additive] [F.Monoidal] (hF : I.toMorphismIdeal ≤ F.kerIdeal)

/-- The factorization `TauCeti.MorphismIdeal.lift` through the quotient by a tensor ideal of a
strong monoidal additive functor killing the ideal is strong monoidal, with the structure
isomorphisms of `F`. -/
noncomputable instance : (I.toMorphismIdeal.lift F hF).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Functor.Monoidal.εIso F
      μIso X Y := Functor.Monoidal.μIso F X.as Y.as
      μIso_hom_natural_left f Z := by
        obtain ⟨f, rfl⟩ := (toMonoidalQuotient I).map_surjective f
        exact Functor.LaxMonoidal.μ_natural_left F f Z.as
      μIso_hom_natural_right Z f := by
        obtain ⟨f, rfl⟩ := (toMonoidalQuotient I).map_surjective f
        exact Functor.LaxMonoidal.μ_natural_right F Z.as f
      associativity X Y Z := Functor.LaxMonoidal.associativity F X.as Y.as Z.as
      left_unitality X := Functor.LaxMonoidal.left_unitality F X.as
      right_unitality X := Functor.LaxMonoidal.right_unitality F X.as }

/-- The unit morphism of the factorization of `F` is that of `F`. -/
@[simp]
theorem lift_ε :
    Functor.LaxMonoidal.ε (I.toMorphismIdeal.lift F hF) = Functor.LaxMonoidal.ε F :=
  (rfl)

/-- The counit morphism of the factorization of `F` is that of `F`. -/
@[simp]
theorem lift_η :
    Functor.OplaxMonoidal.η (I.toMorphismIdeal.lift F hF) = Functor.OplaxMonoidal.η F :=
  (rfl)

/-- On classes, the tensorator of the factorization of `F` is that of `F`. -/
@[simp]
theorem lift_μ (X Y : C) :
    Functor.LaxMonoidal.μ (I.toMorphismIdeal.lift F hF) ((toMonoidalQuotient I).obj X)
      ((toMonoidalQuotient I).obj Y) = Functor.LaxMonoidal.μ F X Y :=
  (rfl)

/-- On classes, the inverse tensorator of the factorization of `F` is that of `F`. -/
@[simp]
theorem lift_δ (X Y : C) :
    Functor.OplaxMonoidal.δ (I.toMorphismIdeal.lift F hF) ((toMonoidalQuotient I).obj X)
      ((toMonoidalQuotient I).obj Y) = Functor.OplaxMonoidal.δ F X Y :=
  (rfl)

/-- The identification `CategoryTheory.Quotient.lift.isLift` of the quotient functor followed by
the factorization of `F` with `F` is a monoidal natural isomorphism. -/
instance : (Iso.hom (X := toMonoidalQuotient I ⋙ I.toMorphismIdeal.lift F hF) (Y := F)
    (CategoryTheory.Quotient.lift.isLift I.rel F _)).IsMonoidal where
  unit := by
    simp only [Functor.comp_obj, Functor.LaxMonoidal.comp_ε, lift_ε, ε_eq,
      CategoryTheory.Functor.map_id, Category.comp_id, CategoryTheory.Quotient.lift.isLift_hom]
    exact Category.comp_id _
  tensor X Y := by
    simp only [Functor.comp_obj, Functor.LaxMonoidal.comp_μ, lift_μ, μ_eq,
      CategoryTheory.Functor.map_id, Category.comp_id, CategoryTheory.Quotient.lift.isLift_hom]
    exact (Category.comp_id _).trans
      ((congrArg (· ≫ _) (id_tensorHom_id _ _)).trans (Category.id_comp _)).symm

end lift

/-! ### Additive and linear structure -/

-- The whiskerings of the quotient are factorizations `TauCeti.MorphismIdeal.lift` of additive
-- (and, for `C` linear, linear) functors, so they inherit additivity and linearity.

/-- The quotient of a monoidal preadditive category by a tensor ideal is monoidal preadditive. -/
instance : MonoidalPreadditive (MonoidalQuotient I) where
  whiskerLeft_zero := Functor.map_zero _ _ _
  zero_whiskerRight := Functor.map_zero _ _ _
  whiskerLeft_add _ _ := Functor.map_add _
  add_whiskerRight _ _ := Functor.map_add _

/-- The quotient of a monoidal `S`-linear category by a tensor ideal is monoidal `S`-linear. -/
instance (S : Type*) [Semiring S] [Linear S C] [MonoidalLinear S C] :
    MonoidalLinear S (MonoidalQuotient I) where
  whiskerLeft_smul _ _ _ _ _ := Functor.map_smul _ _ _
  smul_whiskerRight _ _ _ _ _ := Functor.map_smul _ _ _

end MonoidalQuotient

end TauCeti

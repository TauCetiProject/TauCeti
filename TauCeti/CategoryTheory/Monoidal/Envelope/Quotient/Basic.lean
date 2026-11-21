/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Basic
public import TauCeti.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.CategoryTheory.Quotient.Monoidal

/-!
# Quotients of monoidal preadditive categories by tensor ideals

A **tensor ideal** of a monoidal preadditive category `C` is a two-sided morphism ideal
(`TauCeti.MorphismIdeal`) that is in addition closed under whiskering by arbitrary objects on
either side, hence under tensoring with arbitrary morphisms. Since the whiskerings of a monoidal
preadditive category are additive, `W ◁ f - W ◁ g = W ◁ (f - g)`, so whiskering respects
congruence modulo such an ideal: it is a monoidal relation (`HomRel.IsMonoidal`). The monoidal
structure of `C` therefore descends to the quotient category `C/I` by the general construction
`CategoryTheory.Quotient.monoidalCategory`: the tensor product of the classes of two objects or
morphisms is the class of their tensor product, the associator and unitors are the classes of
those of `C`, the quotient functor `C ⥤ C/I` is strict monoidal, and a strong monoidal functor
killing `I` factors through a strong monoidal functor (`CategoryTheory.Quotient.liftMonoidal`).
This file adds that the quotient is again monoidal preadditive, and monoidal `S`-linear whenever
`C` is.

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

* the instance `TauCeti.MonoidalIdeal.isMonoidal_rel`: congruence modulo a tensor ideal is a
  monoidal relation, so `C/I` carries the descended monoidal structure, the quotient functor is
  strong monoidal and monoidal functors killing `I` factor monoidally through it;
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

/-- In a monoidal preadditive category, congruence modulo a tensor ideal is a monoidal relation, so
the quotient by a tensor ideal carries the descended monoidal structure
`CategoryTheory.Quotient.monoidalCategory`. -/
instance isMonoidal_rel : I.rel.IsMonoidal where
  whiskerLeft W _ _ _ _ h := I.rel_whiskerLeft W h
  whiskerRight W h := I.rel_whiskerRight h W

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

/-! ### Additive and linear structure -/

-- Every morphism of the quotient is a class, the whiskering of a class is the class of the
-- whiskering, and the quotient functor is additive (and, for `C` linear, linear); so each axiom
-- is the image under the quotient functor of the corresponding axiom of `C`.

/-- The quotient of a monoidal preadditive category by a tensor ideal is monoidal preadditive. -/
instance : MonoidalPreadditive (MonoidalQuotient I) where
  whiskerLeft_zero := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩
    exact (congrArg (toMonoidalQuotient I).map MonoidalPreadditive.whiskerLeft_zero).trans
      (Functor.map_zero _ _ _)
  zero_whiskerRight := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩
    exact (congrArg (toMonoidalQuotient I).map MonoidalPreadditive.zero_whiskerRight).trans
      (Functor.map_zero _ _ _)
  whiskerLeft_add := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f g
    obtain ⟨f, rfl⟩ := (toMonoidalQuotient I).map_surjective f
    obtain ⟨g, rfl⟩ := (toMonoidalQuotient I).map_surjective g
    rw [← Functor.map_add]
    exact (congrArg (toMonoidalQuotient I).map (MonoidalPreadditive.whiskerLeft_add f g)).trans
      (Functor.map_add _)
  add_whiskerRight := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f g
    obtain ⟨f, rfl⟩ := (toMonoidalQuotient I).map_surjective f
    obtain ⟨g, rfl⟩ := (toMonoidalQuotient I).map_surjective g
    rw [← Functor.map_add]
    exact (congrArg (toMonoidalQuotient I).map (MonoidalPreadditive.add_whiskerRight f g)).trans
      (Functor.map_add _)

/-- The quotient of a monoidal `S`-linear category by a tensor ideal is monoidal `S`-linear. -/
instance (S : Type*) [Semiring S] [Linear S C] [MonoidalLinear S C] :
    MonoidalLinear S (MonoidalQuotient I) where
  whiskerLeft_smul := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ a f
    obtain ⟨f, rfl⟩ := (toMonoidalQuotient I).map_surjective f
    rw [← Functor.map_smul]
    exact (congrArg (toMonoidalQuotient I).map (MonoidalLinear.whiskerLeft_smul X a f)).trans
      (Functor.map_smul _ _ _)
  smul_whiskerRight := by
    rintro a ⟨Y⟩ ⟨Z⟩ f ⟨X⟩
    obtain ⟨f, rfl⟩ := (toMonoidalQuotient I).map_surjective f
    rw [← Functor.map_smul]
    exact (congrArg (toMonoidalQuotient I).map (MonoidalLinear.smul_whiskerRight a f X)).trans
      (Functor.map_smul _ _ _)

end MonoidalQuotient

end TauCeti

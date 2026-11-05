/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Envelope.Quotient.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Braiding on quotients by tensor ideals

The braiding of a monoidal preadditive category descends to its quotient by any tensor ideal:
the braiding of two quotient objects is the image of their original braiding. Naturality follows
by lifting the morphisms to the original category, and the hexagons are the images of the
original hexagons. No faithfulness of the quotient functor is required.

The quotient functor is braided. An additive braided functor killing the ideal factors as a
braided functor through the quotient, using the existing monoidal structure on
`TauCeti.MorphismIdeal.lift`. Symmetry also descends when the original braiding is symmetric.

These constructions allow braided diagram categories to retain their braiding after passing
to the quotient by negligible morphisms, as in the semisimplification of Temperley–Lieb
categories.

## References

* J. W. Barrett and B. W. Westbury, *Spherical categories*, Adv. Math. 143 (1999), 357–375.
* F. M. Goodman and H. Wenzl, *Ideals in the Temperley–Lieb category*, appendix to
  M. H. Freedman, *A magnetic model with a possible Chern–Simons phase*, Comm. Math. Phys. 234
  (2003), 129–183.
-/

public section

universe v u v' u'

namespace TauCeti.MonoidalQuotient

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] (I : MonoidalIdeal C)

section Braided

variable [BraidedCategory C]

/-- The braiding on a quotient by a tensor ideal is the image of the original braiding. -/
noncomputable instance : BraidedCategory (MonoidalQuotient I) where
  braiding X Y := (toMonoidalQuotient I).mapIso (β_ X.as Y.as)
  braiding_naturality_right X Y Z f := by
    obtain ⟨f, rfl⟩ := (toMonoidalQuotient I).map_surjective f
    exact congrArg (toMonoidalQuotient I).map
      (BraidedCategory.braiding_naturality_right X.as f)
  braiding_naturality_left f Z := by
    obtain ⟨f, rfl⟩ := (toMonoidalQuotient I).map_surjective f
    exact congrArg (toMonoidalQuotient I).map
      (BraidedCategory.braiding_naturality_left f Z.as)
  hexagon_forward X Y Z :=
    congrArg (toMonoidalQuotient I).map (BraidedCategory.hexagon_forward X.as Y.as Z.as)
  hexagon_reverse X Y Z :=
    congrArg (toMonoidalQuotient I).map (BraidedCategory.hexagon_reverse X.as Y.as Z.as)

-- These projection equations are not simp rules: `Functor.map_braiding` normalizes in the
-- opposite direction after simplifying the identity tensorators of the quotient functor.

/-- The braiding morphism in the quotient is the class of the original braiding. -/
theorem braiding_hom (X Y : MonoidalQuotient I) :
    (β_ X Y).hom = (toMonoidalQuotient I).map (β_ X.as Y.as).hom := (rfl)

/-- The inverse braiding in the quotient is the class of the original inverse braiding. -/
theorem braiding_inv (X Y : MonoidalQuotient I) :
    (β_ X Y).inv = (toMonoidalQuotient I).map (β_ X.as Y.as).inv := (rfl)

/-- The quotient functor preserves the braiding, with its existing monoidal structure. -/
noncomputable instance : (toMonoidalQuotient I).Braided where
  braided X Y := by
    simp only [μ_eq, Category.id_comp, Category.comp_id, braiding_hom]
    rfl

end Braided

/-- A symmetric braiding remains symmetric after quotienting by a tensor ideal. -/
noncomputable instance [SymmetricCategory C] : SymmetricCategory (MonoidalQuotient I) where
  symmetry X Y :=
    congrArg (toMonoidalQuotient I).map (SymmetricCategory.symmetry X.as Y.as)

section lift

variable [BraidedCategory C] {I} {D : Type u'} [Category.{v'} D] [Preadditive D]
  [MonoidalCategory D] [BraidedCategory D] (F : C ⥤ D) [F.Additive] [F.Braided]
  (hF : I.toMorphismIdeal ≤ F.kerIdeal)

/-- The factorization of an additive braided functor killing the ideal is braided for the
descended braiding and the existing monoidal factorization. -/
noncomputable instance : (I.toMorphismIdeal.lift F hF).Braided where
  braided X Y := Functor.LaxBraided.braided (F := F) X.as Y.as

end lift

end TauCeti.MonoidalQuotient

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Quotient.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Braiding on quotients by monoidal relations

The braiding of a monoidal category descends to its quotient by any monoidal relation:
the braiding of two quotient objects is the image of their original braiding. Naturality follows
by lifting the morphisms to the original category, and the hexagons are the images of the
original hexagons. No faithfulness of the quotient functor is required.

The quotient functor is braided. A braided functor identifying related morphisms factors as a
braided functor through the quotient, using the existing monoidal structure on
`CategoryTheory.Quotient.lift`. Symmetry also descends when the original braiding is symmetric.

In particular, these constructions give the descended braiding for quotients by tensor ideals,
including quotients of braided diagram categories by negligible morphisms.

## Main results

* `CategoryTheory.Quotient.braidedCategory` and `CategoryTheory.Quotient.symmetricCategory`:
  braided and symmetric structures descend through monoidal relations.
* `CategoryTheory.Quotient.braiding_hom` and `CategoryTheory.Quotient.braiding_inv`:
  the braiding and its inverse on classes are the images of the original morphisms.
* `CategoryTheory.Quotient.functorBraided`: the quotient functor is braided.
* `CategoryTheory.Quotient.liftBraided`: a braided functor identifying related morphisms
  factors through a braided functor.

## References

For the application to tensor ideals:

* J. W. Barrett and B. W. Westbury, *Spherical categories*, Adv. Math. 143 (1999), 357–375.
* F. M. Goodman and H. Wenzl, *Ideals in the Temperley–Lieb category*, appendix to
  M. H. Freedman, *A magnetic model with a possible Chern–Simons phase*, Comm. Math. Phys. 234
  (2003), 129–183.
-/

public section

universe v u v' u'

namespace CategoryTheory.Quotient

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (r : HomRel C) [r.IsMonoidal]

section Braided

variable [BraidedCategory C]

/-- The braiding on a quotient by a monoidal relation is the image of the original braiding. -/
noncomputable instance braidedCategory : BraidedCategory (Quotient r) where
  braiding X Y := (functor r).mapIso (β_ X.as Y.as)
  braiding_naturality_right X Y Z f := by
    obtain ⟨f, rfl⟩ := (functor r).map_surjective f
    exact congrArg (functor r).map
      (BraidedCategory.braiding_naturality_right X.as f)
  braiding_naturality_left f Z := by
    obtain ⟨f, rfl⟩ := (functor r).map_surjective f
    exact congrArg (functor r).map
      (BraidedCategory.braiding_naturality_left f Z.as)
  hexagon_forward X Y Z :=
    congrArg (functor r).map (BraidedCategory.hexagon_forward X.as Y.as Z.as)
  hexagon_reverse X Y Z :=
    congrArg (functor r).map (BraidedCategory.hexagon_reverse X.as Y.as Z.as)

-- These projection equations are not simp rules: `Functor.map_braiding` normalizes in the
-- opposite direction after simplifying the identity tensorators of the quotient functor.

/-- The braiding morphism in the quotient is the class of the original braiding. -/
theorem braiding_hom (X Y : Quotient r) :
    (β_ X Y).hom = (functor r).map (β_ X.as Y.as).hom := (rfl)

/-- The inverse braiding in the quotient is the class of the original inverse braiding. -/
theorem braiding_inv (X Y : Quotient r) :
    (β_ X Y).inv = (functor r).map (β_ X.as Y.as).inv := (rfl)

/-- The quotient functor preserves the braiding, with its existing monoidal structure. -/
noncomputable instance functorBraided : (functor r).Braided where
  braided X Y := by
    simp only [Quotient.functor_μ, Category.id_comp, Category.comp_id, braiding_hom]
    rfl

end Braided

/-- A symmetric braiding remains symmetric after quotienting by a monoidal relation. -/
noncomputable instance symmetricCategory [SymmetricCategory C] :
    SymmetricCategory (Quotient r) where
  symmetry X Y :=
    congrArg (functor r).map (SymmetricCategory.symmetry X.as Y.as)

section lift

variable [BraidedCategory C] {D : Type u'} [Category.{v'} D]
  [MonoidalCategory D] [BraidedCategory D] (F : C ⥤ D) [F.Braided]
  (H : ∀ (X Y : C) (f₁ f₂ : X ⟶ Y), r f₁ f₂ → F.map f₁ = F.map f₂)

/-- The factorization of a braided functor identifying related morphisms is braided for the
descended braiding and the existing monoidal factorization. -/
noncomputable instance liftBraided : (lift r F H).Braided where
  braided X Y := Functor.LaxBraided.braided (F := F) X.as Y.as

end lift

end CategoryTheory.Quotient

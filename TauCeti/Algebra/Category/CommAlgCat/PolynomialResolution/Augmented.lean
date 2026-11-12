/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.PolynomialResolution.Simplicial
public import TauCeti.CategoryTheory.Monad.SimplicialResolution.Augmented

/-!
# The augmented standard polynomial resolution

The standard simplicial polynomial algebra is augmented to its original algebra
by evaluating all layers of polynomial variables. After forgetting to sets, the
map sending an element to its indexed variable is an extra degeneracy. Thus the
augmentation has a section and a simplicial contraction supplied by Mathlib's
`SimplicialObject.Augmented.ExtraDegeneracy.section_` and
`SimplicialObject.Augmented.ExtraDegeneracy.homotopy`.

The extra degeneracy is a map of sets: it need not preserve addition or scalars.
This file does not assert a contraction of the underlying module complex.

## References

* The Stacks Project, Definition 92.3.1 (Tag 08PM).
* Joël Riou's extra-degeneracy and simplicial-homotopy API in Mathlib.
-/

public noncomputable section

open CategoryTheory Opposite

universe u v

namespace CommAlgCat

variable (R : Type u) [CommRing R]

/-- The standard polynomial resolution with its evaluation augmentation.
The body is exposed so its dependent polynomial term carriers compute. -/
@[expose] def polynomialAugmentedResolution :
    CommAlgCat.{max u v} R ⥤ SimplicialObject.Augmented (CommAlgCat.{max u v} R) :=
  (polynomialComonad R).augmentedSimplicialResolution

/-- Dropping the augmentation recovers the standard simplicial polynomial algebra. -/
@[simp] lemma polynomialAugmentedResolution_obj_left (B : CommAlgCat.{max u v} R) :
    ((polynomialAugmentedResolution R).obj B).left =
      (polynomialSimplicialResolution R).obj B := (rfl)

@[simp] lemma polynomialAugmentedResolution_obj_right (B : CommAlgCat.{max u v} R) :
    ((polynomialAugmentedResolution R).obj B).right = B := (rfl)

/-- In every degree, the augmentation evaluates all polynomial layers. -/
lemma polynomialAugmentedResolution_hom_app (B : CommAlgCat.{max u v} R) (n : ℕ) :
    ((polynomialAugmentedResolution R).obj B).hom.app (op (SimplexCategory.mk n)) =
      ((polynomialComonad R).resolutionCounit (n + 1)).app B := by
  exact Comonad.simplicialResolutionAugmentation_app _ B n

-- The dependent categorical source and target prevent reliable ordinary simp matching;
-- keep the evaluation equation as a named rewrite.

/-- The degree-zero augmentation evaluates each variable at the element indexing it. -/
lemma polynomialAugmentedResolution_hom_app_zero_hom
    (B : CommAlgCat.{max u v} R) :
    (((polynomialAugmentedResolution R).obj B).hom.app
      (op (SimplexCategory.mk 0))).hom = MvPolynomial.aeval (id : B → B) := by
  exact (congrArg Hom.hom
    ((polynomialComonad R).simplicialResolutionAugmentation_app_zero B)).trans
      (polynomialComonad_ε_app_hom R B)

/-- The map on the simplicial algebra is the usual polynomial resolution map. -/
lemma polynomialAugmentedResolution_map_left {B B' : CommAlgCat.{max u v} R}
    (f : B ⟶ B') :
    ((polynomialAugmentedResolution R).map f).left =
      (polynomialSimplicialResolution R).map f := (rfl)

lemma polynomialAugmentedResolution_map_right {B B' : CommAlgCat.{max u v} R}
    (f : B ⟶ B') : ((polynomialAugmentedResolution R).map f).right = f := (rfl)

/-- Sending an element to the variable indexed by it is an extra degeneracy of
the augmented polynomial resolution after forgetting to sets. -/
def polynomialResolutionExtraDegeneracy (B : CommAlgCat.{max u v} R) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (((SimplicialObject.Augmented.whiskering (CommAlgCat.{max u v} R)
        (Type (max u v))).obj (forget (CommAlgCat.{max u v} R))).obj
          ((polynomialAugmentedResolution R).obj B)) :=
  (adj R).resolutionExtraDegeneracy B

/-- The section of the augmentation sends an algebra element to its indexed variable. -/
lemma polynomialResolutionExtraDegeneracy_s' (B : CommAlgCat.{max u v} R) :
    (polynomialResolutionExtraDegeneracy R B).s' =
      ↾(MvPolynomial.X : B → MvPolynomial B R) := by
  unfold polynomialResolutionExtraDegeneracy
  rw [Adjunction.resolutionExtraDegeneracy_s', adj_unit_app]

/-- The extra degeneracy in any degree inserts an outer variable. -/
lemma polynomialResolutionExtraDegeneracy_s (B : CommAlgCat.{max u v} R) (n : ℕ) :
    (polynomialResolutionExtraDegeneracy R B).s n =
      ↾(MvPolynomial.X :
        ((polynomialSimplicialResolution R).obj B).obj (op (SimplexCategory.mk n)) →
          MvPolynomial _ R) := by
  unfold polynomialResolutionExtraDegeneracy
  rw [Adjunction.resolutionExtraDegeneracy_s, adj_unit_app]
  rfl

-- Keep these characteristic equations named. Rewriting the bundled maps breaks
-- Mathlib's generic extra-degeneracy laws, while application simp rules leave the
-- dependent forgotten term carrier opaque and do not reliably close caller goals.

/-- Applying the augmentation section produces the indexed variable. -/
lemma polynomialResolutionExtraDegeneracy_s'_apply
    (B : CommAlgCat.{max u v} R) (b : B) :
    (polynomialResolutionExtraDegeneracy R B).s' b = MvPolynomial.X b := by
  rw [polynomialResolutionExtraDegeneracy_s']
  rfl

/-- Applying the extra degeneracy in any degree produces the indexed variable. -/
lemma polynomialResolutionExtraDegeneracy_s_apply
    (B : CommAlgCat.{max u v} R) (n : ℕ)
    (p : ((polynomialSimplicialResolution R).obj B).obj (op (SimplexCategory.mk n))) :
    (polynomialResolutionExtraDegeneracy R B).s n p = MvPolynomial.X p := by
  rw [polynomialResolutionExtraDegeneracy_s]
  rfl

end CommAlgCat

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Braided.Ribbon
public import TauCeti.CategoryTheory.Monoidal.Pivotal.OfBalanced

/-!
# Ribbon categories are spherical

The pivotal structure associated to a ribbon twist is spherical. We first express its two
traces using the twist and the braiding. Naturality of the twist at coevaluation and the
balancing axiom change the inverse crossing in the left trace to the crossing in the right
trace. Compatibility with duality then cancels the two extra twists.

This implication requires neither additivity nor semisimplicity. The converse is not asserted:
a spherical pivotal structure need not induce a ribbon twist without further hypotheses.
The canonical pivotal structure on a symmetric rigid category does induce a ribbon twist,
since that twist is the identity.

## References

* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937),
  Appendix A.2, Proposition A.4
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §8.10
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory ExactPairing

universe v u

namespace TauCeti

section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RigidCategory C]

section Balanced

variable [BalancedCategory C]

-- The trace formulas in this section use the pivotal structure induced by the chosen twist.
attribute [local instance] pivotalOfBalanced

/-- For the pivotal structure induced by a twist, the right trace is a braided loop
with a twist on its object strand. -/
theorem rightTrace_pivotalOfBalanced {X : C} (f : X ⟶ X) :
    rightTrace f = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ BalancedCategory.twist.hom.app X ▷ Xᘁ ≫
      (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
  rw [rightTrace_eq_pivotalIsoApp, pivotalOfBalanced_pivotalIsoApp_hom,
    comp_whiskerRight]
  simp only [Functor.id_obj, Category.assoc, drinfeldIso_hom_comp_evaluation]

/-- For the pivotal structure induced by a twist, the left trace is an inversely braided
loop with an inverse twist on its object strand. -/
theorem leftTrace_pivotalOfBalanced {X : C} (f : X ⟶ X) :
    leftTrace f = η_ X Xᘁ ≫ (β_ Xᘁ X).inv ≫ Xᘁ ◁ BalancedCategory.twist.inv.app X ≫
      Xᘁ ◁ f ≫ ε_ X Xᘁ := by
  rw [leftTrace_eq_pivotalIsoApp, pivotalOfBalanced_pivotalIsoApp_inv, whiskerLeft_comp]
  simp only [Functor.id_obj, Category.assoc, coevaluation_comp_drinfeldIso_inv_assoc]

/-- The pivotal structure of a ribbon category has equal left and right traces. -/
theorem leftTrace_eq_rightTrace_pivotalOfBalanced [RibbonCategory C] {X : C} (f : X ⟶ X) :
    leftTrace f = rightTrace f := by
  -- Balancing changes the crossing at the cup. Slide the dual twist onto the object
  -- strand, then move the inverse twist backwards through the crossing to cancel it.
  rw [leftTrace_pivotalOfBalanced, rightTrace_pivotalOfBalanced,
    BalancedCategory.comp_inv_braiding_assoc, tensorHom_def', Category.assoc,
    RibbonCategory.coevaluation_comp_twist_assoc,
    ← braiding_naturality_left_assoc, ← comp_whiskerRight_assoc]
  simp only [Functor.id_obj]
  rw [← braiding_naturality_left_assoc, ← comp_whiskerRight_assoc,
    ← comp_whiskerRight_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  -- Naturality commutes the remaining twist with the endomorphism inside the loop.
  simpa only [Functor.id_map, comp_whiskerRight, Category.assoc] using
    congrArg (fun g => η_ X Xᘁ ≫ g ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ)
      (BalancedCategory.twist.hom.naturality f).symm

/-- The pivotal structure induced by a ribbon twist is spherical. This is not a global
instance: it applies specifically to `pivotalOfBalanced C`, not an arbitrary pivotal structure. -/
theorem sphericalCategory_pivotalOfBalanced [RibbonCategory C] : SphericalCategory C where
  leftTrace_eq_rightTrace := leftTrace_eq_rightTrace_pivotalOfBalanced

end Balanced

/-- A pivotal structure is spherical if its associated twist is ribbon. -/
theorem sphericalCategory_of_ribbonCategory [PivotalCategory C]
    (h : letI := balancedOfBraidedPivotal C; RibbonCategory C) : SphericalCategory C := by
  have hs : @SphericalCategory C _ _ _
      (@pivotalOfBalanced C _ _ _ _ (balancedOfBraidedPivotal C)) :=
    @sphericalCategory_pivotalOfBalanced C _ _ _ _ (balancedOfBraidedPivotal C) h
  rwa [pivotalOfBalanced_balancedOfBraidedPivotal] at hs

end

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [RigidCategory C]

/-- In a symmetric rigid category, the twist associated to the canonical pivotal structure
is ribbon: its components are identities. -/
theorem ribbonCategory_balancedOfBraidedPivotal :
    letI := balancedOfBraidedPivotal C
    RibbonCategory C := by
  let := balancedOfBraidedPivotal C
  constructor
  intro X
  simp only [balancedOfBraidedPivotal_twist_eq_refl, Iso.refl_hom, NatTrans.id_app,
    rightAdjointMate_id, Functor.id_obj]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Spherical
public import TauCeti.CategoryTheory.Monoidal.Rigid.Drinfeld

/-!
# The canonical pivotal structure on a symmetric rigid category

In a symmetric rigid category the Drinfeld isomorphisms `drinfeldIso X : X ≅ Xᘁᘁ` form a
monoidal natural isomorphism `drinfeldNatIso : 𝟭 C ≅ doubleRightDualFunctor C`
(`TauCeti.drinfeldNatIso_isMonoidal`). Hence every symmetric rigid category carries a canonical
pivotal structure, registered as the instance `TauCeti.symmetricPivotalCategory`.

Through the Drinfeld isomorphism, the pivotal pairing of `X` becomes the braided swap of the
pairing `(X, Xᘁ)`, so both traces are computed by the braiding:
`rightTrace f = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ` and
`leftTrace f = η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ`. Naturality of the braiding then
shows that the left and right traces of every endomorphism agree: the canonical pivotal
structure is spherical, registered as the instance `TauCeti.symmetricSphericalCategory`.

## Main declarations

* `TauCeti.symmetricPivotalCategory`: the canonical pivotal structure on a symmetric rigid
  category, whose components are the Drinfeld isomorphisms (`TauCeti.pivotalIsoApp_eq_drinfeldIso`);
* `TauCeti.rightTrace_eq_braiding` and `TauCeti.leftTrace_eq_braiding`: the traces as braided
  loops, and `TauCeti.leftTrace_eq_rightTrace_of_symmetric`: the two traces agree;
* `TauCeti.symmetricSphericalCategory`: the canonical pivotal structure is spherical, and
  `TauCeti.trace_eq_braiding`: its trace as a braided loop;
* `TauCeti.trace_associator_inv_braiding_whiskerRight_associator_hom_comp_whiskerLeft`: contracting
  a symmetric braiding in a categorical trace.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§8.9–8.10
* [leanprover-community/mathlib4#42192](https://github.com/leanprover-community/mathlib4/pull/42192),
  for the names `symmetricPivotalCategory` and `symmetricSphericalCategory` and the construction
  of the pivotal structure from the Drinfeld isomorphism
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory ExactPairing

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Pivotal

variable [SymmetricCategory C] [RigidCategory C]

/-- The canonical pivotal structure on a symmetric rigid category, given by the Drinfeld
isomorphisms. -/
noncomputable instance symmetricPivotalCategory : PivotalCategory C where
  pivotalIso := drinfeldNatIso

/-- The components of the canonical pivotal structure on a symmetric rigid category are the
Drinfeld isomorphisms. -/
@[simp]
theorem pivotalIsoApp_eq_drinfeldIso (X : C) : pivotalIsoApp X = drinfeldIso X :=
  Iso.ext ((pivotalIso_hom_app X).symm.trans (drinfeldNatIso_hom_app X))

/-- In a symmetric rigid category, the coevaluation of `pivotalExactPairing X` is the coevaluation
of `(X, Xᘁ)` followed by the braiding. -/
theorem pivotalExactPairing_coevaluation_eq_braiding (X : C) :
    @coevaluation C _ _ Xᘁ X (pivotalExactPairing X) = η_ X Xᘁ ≫ (β_ X Xᘁ).hom := by
  rw [pivotalExactPairing_coevaluation, pivotalIsoApp_eq_drinfeldIso,
    coevaluation_comp_drinfeldIso_inv, SymmetricCategory.braiding_swap_eq_inv_braiding]

/-- In a symmetric rigid category, the evaluation of `pivotalExactPairing X` is the braiding
followed by the evaluation of `(X, Xᘁ)`. -/
theorem pivotalExactPairing_evaluation_eq_braiding (X : C) :
    @evaluation C _ _ Xᘁ X (pivotalExactPairing X) = (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
  rw [pivotalExactPairing_evaluation, pivotalIsoApp_eq_drinfeldIso, drinfeldIso_hom_comp_evaluation]

/-- In a symmetric rigid category with its canonical pivotal structure, the right trace of `f`
closes up `f` with the coevaluation of `(X, Xᘁ)` and the braided evaluation. -/
theorem rightTrace_eq_braiding {X : C} (f : X ⟶ X) :
    rightTrace f = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
  rw [rightTrace_eq_pivotalIsoApp, pivotalIsoApp_eq_drinfeldIso, drinfeldIso_hom_comp_evaluation]

/-- In a symmetric rigid category with its canonical pivotal structure, the left trace of `f`
closes up `f` with the braided coevaluation and the evaluation of `(X, Xᘁ)`. -/
theorem leftTrace_eq_braiding {X : C} (f : X ⟶ X) :
    leftTrace f = η_ X Xᘁ ≫ (β_ X Xᘁ).hom ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ := by
  rw [leftTrace_eq_pivotalIsoApp, pivotalIsoApp_eq_drinfeldIso,
    coevaluation_comp_drinfeldIso_inv_assoc, ← SymmetricCategory.braiding_swap_eq_inv_braiding]

/-- In a symmetric rigid category with its canonical pivotal structure, the left and right traces
of every endomorphism agree. -/
theorem leftTrace_eq_rightTrace_of_symmetric {X : C} (f : X ⟶ X) :
    leftTrace f = rightTrace f := by
  rw [leftTrace_eq_braiding, rightTrace_eq_braiding, braiding_naturality_left_assoc]

/-- The canonical pivotal structure on a symmetric rigid category is spherical. -/
instance symmetricSphericalCategory : SphericalCategory C where
  leftTrace_eq_rightTrace := leftTrace_eq_rightTrace_of_symmetric

/-- In a symmetric rigid category with its canonical spherical structure, the trace of `f`
closes up `f` with the coevaluation of `(X, Xᘁ)` and the braided evaluation. -/
theorem trace_eq_braiding {X : C} (f : X ⟶ X) :
    trace f = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
  rw [trace_eq_rightTrace, rightTrace_eq_braiding]

/-- Left partial trace over the first factor of `(β_ X X).hom` is the identity on `X`. -/
private theorem coevaluation_braiding_comp_braiding_comp_evaluation (X : C) :
    (λ_ X).inv ≫ (η_ X Xᘁ ≫ (β_ X Xᘁ).hom) ▷ X ≫ (α_ Xᘁ X X).hom ≫
      Xᘁ ◁ (β_ X X).hom ≫ (α_ Xᘁ X X).inv ≫ ε_ X Xᘁ ▷ X ≫ (λ_ X).hom = 𝟙 X := by
  have h : (β_ X Xᘁ).hom ▷ X ≫ (α_ Xᘁ X X).hom ≫ Xᘁ ◁ (β_ X X).hom ≫ (α_ Xᘁ X X).inv =
      (α_ X Xᘁ X).hom ≫ (β_ X (Xᘁ ⊗ X)).hom := by
    rw [braiding_tensor_right_hom, Iso.hom_inv_id_assoc]
  rw [comp_whiskerRight, Category.assoc, reassoc_of% h,
    ← braiding_naturality_right_assoc, braiding_tensorUnit_right]
  calc _ = (λ_ X).inv ≫ (η_ X Xᘁ ▷ X ≫ (α_ X Xᘁ X).hom ≫ X ◁ ε_ X Xᘁ) ≫ (ρ_ X).hom := by
        monoidal
    _ = 𝟙 X := by
        rw [evaluation_coevaluation]
        monoidal

/-- Contracting the first two factors of `(α_ X X Z)⁻¹ ≫ β_{X,X} ▷ Z ≫ α_ X X Z ≫ X ◁ h` in the
categorical trace leaves the trace of `h : X ⊗ Z ⟶ X ⊗ Z`. -/
theorem trace_associator_inv_braiding_whiskerRight_associator_hom_comp_whiskerLeft {X Z : C}
    (h : X ⊗ Z ⟶ X ⊗ Z) :
    trace ((α_ X X Z).inv ≫ (β_ X X).hom ▷ Z ≫ (α_ X X Z).hom ≫ X ◁ h) = trace h := by
  have key : (λ_ (X ⊗ Z)).inv ≫ (η_ X Xᘁ ≫ (β_ X Xᘁ).hom) ▷ (X ⊗ Z) ≫
      (α_ Xᘁ X (X ⊗ Z)).hom ≫
        Xᘁ ◁ ((α_ X X Z).inv ≫ (β_ X X).hom ▷ Z ≫ (α_ X X Z).hom ≫ X ◁ h) ≫
        (α_ Xᘁ X (X ⊗ Z)).inv ≫ ε_ X Xᘁ ▷ (X ⊗ Z) ≫ (λ_ (X ⊗ Z)).hom = h := by
    calc _ = ((λ_ X).inv ≫ (η_ X Xᘁ ≫ (β_ X Xᘁ).hom) ▷ X ≫ (α_ Xᘁ X X).hom ≫
          Xᘁ ◁ (β_ X X).hom ≫ (α_ Xᘁ X X).inv) ▷ Z ≫
          (α_ (Xᘁ ⊗ X) X Z).hom ≫ ((Xᘁ ⊗ X) ◁ h ≫ ε_ X Xᘁ ▷ (X ⊗ Z)) ≫ (λ_ (X ⊗ Z)).hom := by
          monoidal
      _ = ((λ_ X).inv ≫ (η_ X Xᘁ ≫ (β_ X Xᘁ).hom) ▷ X ≫ (α_ Xᘁ X X).hom ≫
          Xᘁ ◁ (β_ X X).hom ≫ (α_ Xᘁ X X).inv ≫ ε_ X Xᘁ ▷ X ≫ (λ_ X).hom) ▷ Z ≫ h := by
          rw [whisker_exchange]
          monoidal
      _ = h := by
          rw [coevaluation_braiding_comp_braiding_comp_evaluation, id_whiskerRight,
            Category.id_comp]
  rw [trace_eq_leftTrace, trace_eq_leftTrace, leftTrace_tensorObj,
    pivotalExactPairing_coevaluation_eq_braiding, key]

end Pivotal

end TauCeti

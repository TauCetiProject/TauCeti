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
  `TauCeti.trace_eq_braiding`: its trace as a braided loop.

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

end Pivotal

end TauCeti

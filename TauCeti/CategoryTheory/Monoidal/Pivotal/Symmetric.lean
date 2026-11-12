/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Braided.TensorPow
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

Contracting the cyclic shift `TauCeti.tensorPowShiftIso X n` against the tensor power
`TauCeti.tensorPowMap f (n + 1)` of an endomorphism `f : X ⟶ X` inside the categorical trace
yields the categorical trace of the `(n + 1)`-st iterate `(End.of f ^ (n + 1)).asHom`
(`TauCeti.trace_tensorPowMap_comp_tensorPowShiftIso_hom`), and in particular the trace of the
cyclic shift itself is `quantumDim X` (`TauCeti.trace_tensorPowShiftIso_hom`).

## Main declarations

* `TauCeti.symmetricPivotalCategory`: the canonical pivotal structure on a symmetric rigid
  category, whose components are the Drinfeld isomorphisms (`TauCeti.pivotalIsoApp_eq_drinfeldIso`);
* `TauCeti.rightTrace_eq_braiding` and `TauCeti.leftTrace_eq_braiding`: the traces as braided
  loops, and `TauCeti.leftTrace_eq_rightTrace_of_symmetric`: the two traces agree;
* `TauCeti.symmetricSphericalCategory`: the canonical pivotal structure is spherical, and
  `TauCeti.trace_eq_braiding`: its trace as a braided loop;
* `TauCeti.trace_associator_inv_braiding_whiskerRight_associator_hom_comp_whiskerLeft`: contracting
  a symmetric braiding in a categorical trace;
* `TauCeti.trace_tensorHom_tensorPowMap_comp_tensorPowShiftIso_hom`,
  `TauCeti.trace_tensorPowMap_comp_tensorPowShiftIso_hom`, and
  `TauCeti.trace_tensorPowShiftIso_hom`: the categorical trace of a tensor power composed with the
  cyclic shift.

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
          rw [coevaluation_braiding_comp_braiding_comp_evaluation_assoc, Iso.inv_hom_id,
            id_whiskerRight, Category.id_comp]
  rw [trace_eq_leftTrace, trace_eq_leftTrace, leftTrace_tensorObj,
    pivotalExactPairing_coevaluation_eq_braiding, key]

section CyclicTrace

/-- **Cyclic power-trace induction**: in a symmetric rigid category, the categorical trace of
`(a ⊗ₘ tensorPowMap f n) ≫ (tensorPowShiftIso X n).hom` on `tensorPow X (n + 1)` equals the
categorical trace of `(End.of f ^ n).asHom ≫ a` on `X`. -/
theorem trace_tensorHom_tensorPowMap_comp_tensorPowShiftIso_hom {X : C} (a f : X ⟶ X) (n : ℕ) :
    trace ((a ⊗ₘ tensorPowMap f n) ≫ (tensorPowShiftIso X n).hom) =
      trace ((End.of f ^ n).asHom ≫ a) := by
  induction n generalizing a with
  | zero =>
    simpa [tensorPowMap_zero] using trace_conj (ρ_ X).symm a
  | succ n ih =>
    have h1 : (a ⊗ₘ (f ⊗ₘ tensorPowMap f n)) ≫
        (α_ X X (tensorPow X n)).inv ≫ (β_ X X).hom ▷ tensorPow X n ≫
          (α_ X X (tensorPow X n)).hom ≫ X ◁ (tensorPowShiftIso X n).hom =
        ((α_ X X (tensorPow X n)).inv ≫ (β_ X X).hom ▷ tensorPow X n ≫
          (α_ X X (tensorPow X n)).hom ≫
            X ◁ (a ▷ tensorPow X n ≫ X ◁ tensorPowMap f n ≫ (tensorPowShiftIso X n).hom)) ≫
          f ▷ (X ⊗ tensorPow X n) := by
      rw [tensorHom_def a, Category.assoc,
        whiskerLeft_tensorHom_comp_associator_inv_braiding_associator_hom_assoc,
        whiskerRight_comp_associator_inv_braiding_associator_hom_assoc]
      simp only [← MonoidalCategory.whiskerLeft_comp, Category.assoc]
      rw [← whisker_exchange, ← MonoidalCategory.whiskerLeft_comp_assoc]
    have h2 : f ▷ (X ⊗ tensorPow X n) ≫
        ((α_ X X (tensorPow X n)).inv ≫ (β_ X X).hom ▷ tensorPow X n ≫
          (α_ X X (tensorPow X n)).hom ≫
            X ◁ (a ▷ tensorPow X n ≫ X ◁ tensorPowMap f n ≫ (tensorPowShiftIso X n).hom)) =
        (α_ X X (tensorPow X n)).inv ≫ (β_ X X).hom ▷ tensorPow X n ≫
          (α_ X X (tensorPow X n)).hom ≫
            X ◁ (((f ≫ a) ⊗ₘ tensorPowMap f n) ≫ (tensorPowShiftIso X n).hom) := by
      rw [whiskerRight_comp_associator_inv_braiding_associator_hom_assoc]
      simp only [← MonoidalCategory.whiskerLeft_comp, ← comp_whiskerRight_assoc,
        tensorHom_def, Category.assoc]
    rw [tensorPowMap_succ, tensorPowShiftIso_succ_hom, h1, trace_comm, h2,
      trace_associator_inv_braiding_whiskerRight_associator_hom_comp_whiskerLeft, ih (f ≫ a),
      pow_succ', End.mul_asHom, Category.assoc]

/-- **Categorical trace of a tensor power with cyclic shift**: in a symmetric rigid category, the
categorical trace of `tensorPowMap f (n + 1) ≫ (tensorPowShiftIso X n).hom` is the categorical
trace of the `(n + 1)`-st iterate `(End.of f ^ (n + 1)).asHom`. -/
theorem trace_tensorPowMap_comp_tensorPowShiftIso_hom {X : C} (f : X ⟶ X) (n : ℕ) :
    trace (tensorPowMap f (n + 1) ≫ (tensorPowShiftIso X n).hom) =
      trace (End.of f ^ (n + 1)).asHom := by
  rw [tensorPowMap_succ, trace_tensorHom_tensorPowMap_comp_tensorPowShiftIso_hom, pow_succ',
    End.mul_asHom]

/-- The categorical trace of the cyclic shift `(tensorPowShiftIso X n).hom` on `tensorPow X (n + 1)`
equals the quantum dimension of `X`. -/
@[simp]
theorem trace_tensorPowShiftIso_hom (X : C) (n : ℕ) :
    trace (tensorPowShiftIso X n).hom = quantumDim X := by
  simpa using trace_tensorPowMap_comp_tensorPowShiftIso_hom (𝟙 X) n

end CyclicTrace

end Pivotal

end TauCeti

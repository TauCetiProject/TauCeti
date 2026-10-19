/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Basic
public import TauCeti.CategoryTheory.Monoidal.Scalar

/-!
# Left and right traces in a pivotal category

In a pivotal category `C`, every object `X` is both a right dual of `Xᘁ`, through the pairing
`TauCeti.pivotalExactPairing X : ExactPairing Xᘁ X`, and a left dual of `Xᘁ`, through the rigid
structure. So an endomorphism `f : X ⟶ X` can be closed up into a loop in two ways, giving two
scalars `𝟙_ C ⟶ 𝟙_ C`:

* the *left trace* `leftTrace f = η_ Xᘁ X ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ`, whose coevaluation is that of
  `pivotalExactPairing X`;
* the *right trace* `rightTrace f = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ ε_ Xᘁ X`, whose evaluation is that of
  `pivotalExactPairing X`.

Unfolding the pivotal pairing writes the pivotal isomorphism `φ_X : X ≅ Xᘁᘁ` out explicitly:
`leftTrace f = η_ Xᘁ Xᘁᘁ ≫ Xᘁ ◁ φ_X⁻¹ ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ` and
`rightTrace f = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ φ_X ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ`. The *left* and *right dimensions* of `X`
are the traces of its identity.

We prove the basic properties of the two traces: both are cyclic, so in particular invariant
under conjugation by an isomorphism; the right adjoint mate exchanges them, by the Freyd–Yetter
identity `φ_{Xᘁ} = (φ_X⁻¹)ᘁ`, so that the left dimension of `Xᘁ` is the right dimension of `X`;
both are the identity on scalars `𝟙_ C ⟶ 𝟙_ C`, so that the unit has dimension `𝟙`; and both are
compatible with extracting scalar actions from the outside of a loop; and both are additive, and
`R`-linear in an `R`-linear monoidal category. The zero object has both dimensions zero in a
preadditive monoidal category.

## Main declarations

* `TauCeti.leftTrace` and `TauCeti.rightTrace`: the two traces of an endomorphism, with their
  defining formulas `TauCeti.leftTrace_def` and `TauCeti.rightTrace_def` and their unfolded
  forms `TauCeti.leftTrace_eq_pivotalIsoApp` and `TauCeti.rightTrace_eq_pivotalIsoApp`;
* `TauCeti.leftDim` and `TauCeti.rightDim`: the two dimensions of an object, the traces of its
  identity, and invariant under isomorphism by `TauCeti.leftDim_congr` and
  `TauCeti.rightDim_congr`;
* `TauCeti.leftTrace_comm` and `TauCeti.rightTrace_comm`: cyclicity;
* `TauCeti.leftTrace_comp_whiskerLeft_scalar` and
  `TauCeti.rightTrace_scalar_whiskerRight_comp`: a scalar acting on the outer side of a loop
  factors out of the trace;
* `TauCeti.leftTrace_rightAdjointMate` and `TauCeti.rightTrace_rightAdjointMate`: the mate
  exchanges the two traces, and `TauCeti.leftDim_rightDual` and `TauCeti.rightDim_rightDual`
  exchange the two dimensions;
* `TauCeti.leftTrace_unit` and `TauCeti.rightTrace_unit`: the trace of a scalar is itself, and
  `TauCeti.leftDim_unit`, `TauCeti.rightDim_unit`;
* `TauCeti.leftTrace_add`, `TauCeti.leftTrace_smul` and their right-handed versions: additivity
  in a preadditive monoidal category, and `R`-linearity in an `R`-linear one.

## References

* A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*, [arXiv:1509.02937](https://arxiv.org/abs/1509.02937), §2.1
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.7
* [leanprover-community/mathlib4#42191](https://github.com/leanprover-community/mathlib4/pull/42191),
  for the names `leftTrace` and `rightTrace` and their packaging through `pivotalExactPairing`
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory ExactPairing
open scoped ZeroObject

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C] [PivotalCategory C]

/-- The *left trace* `η_ Xᘁ X ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ` of an endomorphism `f : X ⟶ X` in a pivotal
category, where the coevaluation is that of the pivotal pairing `pivotalExactPairing X`. -/
noncomputable def leftTrace {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  @coevaluation C _ _ Xᘁ X (pivotalExactPairing X) ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ

/-- The *right trace* `η_ X Xᘁ ≫ f ▷ Xᘁ ≫ ε_ Xᘁ X` of an endomorphism `f : X ⟶ X` in a pivotal
category, where the evaluation is that of the pivotal pairing `pivotalExactPairing X`. -/
noncomputable def rightTrace {X : C} (f : X ⟶ X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X Xᘁ ≫ f ▷ Xᘁ ≫ @evaluation C _ _ Xᘁ X (pivotalExactPairing X)

/-- The *left dimension* of an object of a pivotal category: the left trace of its identity. -/
noncomputable def leftDim (X : C) : 𝟙_ C ⟶ 𝟙_ C :=
  leftTrace (𝟙 X)

/-- The *right dimension* of an object of a pivotal category: the right trace of its identity. -/
noncomputable def rightDim (X : C) : 𝟙_ C ⟶ 𝟙_ C :=
  rightTrace (𝟙 X)

/-- The defining formula of the left trace, with the coevaluation of `pivotalExactPairing X`. -/
theorem leftTrace_def {X : C} (f : X ⟶ X) :
    leftTrace f = @coevaluation C _ _ Xᘁ X (pivotalExactPairing X) ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ :=
  (rfl)

/-- The defining formula of the right trace, with the evaluation of `pivotalExactPairing X`. -/
theorem rightTrace_def {X : C} (f : X ⟶ X) :
    rightTrace f = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ @evaluation C _ _ Xᘁ X (pivotalExactPairing X) :=
  (rfl)

/-- The left trace of an identity is the left dimension. -/
@[simp]
theorem leftTrace_id (X : C) : leftTrace (𝟙 X) = leftDim X :=
  (rfl)

/-- The right trace of an identity is the right dimension. -/
@[simp]
theorem rightTrace_id (X : C) : rightTrace (𝟙 X) = rightDim X :=
  (rfl)

/-- The left trace with the pivotal isomorphism written out:
`leftTrace f = η_ Xᘁ Xᘁᘁ ≫ Xᘁ ◁ φ_X⁻¹ ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ`. -/
theorem leftTrace_eq_pivotalIsoApp {X : C} (f : X ⟶ X) :
    leftTrace f =
      η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ Xᘁ ◁ (pivotalIsoApp X).inv ≫ Xᘁ ◁ f ≫ ε_ X Xᘁ := by
  rw [leftTrace_def, pivotalExactPairing_coevaluation, Category.assoc]

/-- The right trace with the pivotal isomorphism written out:
`rightTrace f = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ φ_X ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ`. -/
theorem rightTrace_eq_pivotalIsoApp {X : C} (f : X ⟶ X) :
    rightTrace f =
      η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (pivotalIsoApp X).hom ▷ Xᘁ ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) := by
  rw [rightTrace_def, pivotalExactPairing_evaluation]

/-- **Cyclicity of the left trace**: `leftTrace (f ≫ g) = leftTrace (g ≫ f)`. -/
theorem leftTrace_comm {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    leftTrace (f ≫ g) = leftTrace (g ≫ f) := by
  rw [leftTrace_eq_pivotalIsoApp, leftTrace_eq_pivotalIsoApp, MonoidalCategory.whiskerLeft_comp,
    Category.assoc]
  -- Slide `g` around the loop: at the evaluation `Xᘁ ◁ g` becomes its mate `gᘁ ▷ Y`, which
  -- passes the whiskerings by `Xᘁ` and reaches the coevaluation as `Yᘁ ◁ gᘁᘁ`.
  rw [← rightAdjointMate_comp_evaluation g, whisker_exchange_assoc, whisker_exchange_assoc,
    ← coevaluation_comp_rightAdjointMate_assoc (gᘁ)]
  -- Naturality of `φ⁻¹` turns `gᘁᘁ ≫ φ_X⁻¹` into `φ_Y⁻¹ ≫ g`.
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, pivotalIsoApp_inv_naturality,
    MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- **The mate exchanges the two traces**: the left trace of `fᘁ` is the right trace of `f`. -/
@[simp]
theorem leftTrace_rightAdjointMate {X : C} (f : X ⟶ X) : leftTrace (fᘁ) = rightTrace f := by
  rw [leftTrace_eq_pivotalIsoApp, rightTrace_eq_pivotalIsoApp, pivotalIsoApp_rightDual_inv,
    coevaluation_comp_rightAdjointMate_assoc, ← whisker_exchange_assoc,
    coevaluation_comp_rightAdjointMate_assoc]

/-- **The mate exchanges the two traces**: the right trace of `fᘁ` is the left trace of `f`. -/
@[simp]
theorem rightTrace_rightAdjointMate {X : C} (f : X ⟶ X) : rightTrace (fᘁ) = leftTrace f := by
  rw [leftTrace_eq_pivotalIsoApp, rightTrace_eq_pivotalIsoApp, pivotalIsoApp_rightDual,
    rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc, rightAdjointMate_comp_evaluation]

/-- **Cyclicity of the right trace**: `rightTrace (f ≫ g) = rightTrace (g ≫ f)`. -/
theorem rightTrace_comm {X Y : C} (f : X ⟶ Y) (g : Y ⟶ X) :
    rightTrace (f ≫ g) = rightTrace (g ≫ f) := by
  rw [← leftTrace_rightAdjointMate, ← leftTrace_rightAdjointMate, comp_rightAdjointMate,
    comp_rightAdjointMate, leftTrace_comm]

/-- A scalar acting on `Y` from the right factors out of the left trace. -/
theorem leftTrace_comp_whiskerLeft_scalar {Y : C} (g : Y ⟶ Y) (a : 𝟙_ C ⟶ 𝟙_ C) :
    leftTrace (g ≫ (ρ_ Y).inv ≫ Y ◁ a ≫ (ρ_ Y).hom) = leftTrace g ≫ a := by
  have h : (Yᘁ : C) ◁ ((ρ_ Y).inv ≫ Y ◁ a ≫ (ρ_ Y).hom) ≫ ε_ Y Yᘁ = ε_ Y Yᘁ ≫ a := by
    calc _ = (ρ_ ((Yᘁ : C) ⊗ Y)).inv ≫ ((Yᘁ : C) ⊗ Y) ◁ a ≫
          ((ρ_ ((Yᘁ : C) ⊗ Y)).hom ≫ ε_ Y Yᘁ) := by monoidal
      _ = _ := by rw [whiskerLeft_scalar_comp]; simp
  rw [leftTrace_def, leftTrace_def, MonoidalCategory.whiskerLeft_comp, Category.assoc, h]
  simp only [Category.assoc]

/-- A scalar acting on `X` from the left factors out of the right trace. -/
theorem rightTrace_scalar_whiskerRight_comp {X : C} (a : 𝟙_ C ⟶ 𝟙_ C) (f : X ⟶ X) :
    rightTrace ((λ_ X).inv ≫ a ▷ X ≫ (λ_ X).hom ≫ f) = a ≫ rightTrace f := by
  have h : η_ X Xᘁ ≫ ((λ_ X).inv ≫ a ▷ X ≫ (λ_ X).hom ≫ f) ▷ (Xᘁ : C) =
      a ≫ η_ X Xᘁ ≫ f ▷ (Xᘁ : C) := by
    calc _ = (η_ X Xᘁ ≫ (λ_ (X ⊗ (Xᘁ : C))).inv) ≫ a ▷ (X ⊗ (Xᘁ : C)) ≫
          (λ_ (X ⊗ (Xᘁ : C))).hom ≫ f ▷ (Xᘁ : C) := by monoidal
      _ = _ := by rw [comp_scalar_whiskerRight_assoc]; simp
  rw [rightTrace_def, rightTrace_def, reassoc_of% h]

/-- The left trace is invariant under conjugation by an isomorphism. -/
theorem leftTrace_conj {X Y : C} (i : X ≅ Y) (f : X ⟶ X) :
    leftTrace (i.inv ≫ f ≫ i.hom) = leftTrace f := by
  rw [leftTrace_comm, Category.assoc, i.hom_inv_id, Category.comp_id]

/-- The right trace is invariant under conjugation by an isomorphism. -/
theorem rightTrace_conj {X Y : C} (i : X ≅ Y) (f : X ⟶ X) :
    rightTrace (i.inv ≫ f ≫ i.hom) = rightTrace f := by
  rw [rightTrace_comm, Category.assoc, i.hom_inv_id, Category.comp_id]

/-- Isomorphic objects have the same left dimension. -/
theorem leftDim_congr {X Y : C} (i : X ≅ Y) : leftDim X = leftDim Y := by
  rw [leftDim, leftDim, ← i.hom_inv_id, leftTrace_comm, i.inv_hom_id]

/-- Isomorphic objects have the same right dimension. -/
theorem rightDim_congr {X Y : C} (i : X ≅ Y) : rightDim X = rightDim Y := by
  rw [rightDim, rightDim, ← i.hom_inv_id, rightTrace_comm, i.inv_hom_id]

/-- The left dimension of `Xᘁ` is the right dimension of `X`. -/
@[simp]
theorem leftDim_rightDual (X : C) : leftDim Xᘁ = rightDim X := by
  rw [leftDim, rightDim, ← rightAdjointMate_id, leftTrace_rightAdjointMate]

/-- The right dimension of `Xᘁ` is the left dimension of `X`. -/
@[simp]
theorem rightDim_rightDual (X : C) : rightDim Xᘁ = leftDim X := by
  rw [leftDim, rightDim, ← rightAdjointMate_id, rightTrace_rightAdjointMate]

section Unit

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The left dimension of the unit is `𝟙`. -/
@[simp]
theorem leftDim_unit : leftDim (𝟙_ C) = 𝟙 (𝟙_ C) := by
  -- `φ_𝟙⁻¹` is the inverse unit comparison of the double right dual functor.
  rw [leftDim, leftTrace_eq_pivotalIsoApp, pivotalIsoApp_unit_inv, doubleRightDualFunctor_η]
  simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, coevaluation_comp_rightMate_assoc]
  rw [← whisker_exchange_assoc, rightDualIso_hom, rightDualIso_inv,
    coevaluation_comp_rightMate_assoc, rightMate_comp_evaluation]
  simp

/-- The right dimension of the unit is `𝟙`. -/
@[simp]
theorem rightDim_unit : rightDim (𝟙_ C) = 𝟙 (𝟙_ C) := by
  rw [← leftDim_rightDual,
    leftDim_congr (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit),
    leftDim_unit]

/-- **The left trace of a scalar is itself**: for `a : 𝟙_ C ⟶ 𝟙_ C`, `leftTrace a = a`. -/
@[simp]
theorem leftTrace_unit (a : 𝟙_ C ⟶ 𝟙_ C) : leftTrace a = a := by
  calc leftTrace a = leftDim (𝟙_ C) ≫ a := by
        rw [leftDim, leftTrace_def, leftTrace_def, MonoidalCategory.whiskerLeft_id,
          Category.id_comp, whiskerLeft_scalar_comp, Category.assoc]
    _ = a := by rw [leftDim_unit, Category.id_comp]

/-- **The right trace of a scalar is itself**: for `a : 𝟙_ C ⟶ 𝟙_ C`, `rightTrace a = a`. -/
@[simp]
theorem rightTrace_unit (a : 𝟙_ C ⟶ 𝟙_ C) : rightTrace a = a := by
  calc rightTrace a = a ≫ rightDim (𝟙_ C) := by
        rw [rightDim, rightTrace_def, rightTrace_def, MonoidalCategory.id_whiskerRight,
          Category.id_comp, comp_scalar_whiskerRight_assoc]
    _ = a := by rw [rightDim_unit, Category.comp_id]

end Unit

section Linear

variable [Preadditive C] [MonoidalPreadditive C]

/-- The left trace is additive. -/
@[simp]
theorem leftTrace_add {X : C} (f g : X ⟶ X) : leftTrace (f + g) = leftTrace f + leftTrace g := by
  simp [leftTrace_def]

/-- The left trace of zero is zero. -/
@[simp]
theorem leftTrace_zero (X : C) : leftTrace (0 : X ⟶ X) = 0 := by
  simp [leftTrace_def]

/-- The zero object has left pivotal dimension zero. -/
@[simp]
theorem leftDim_zero [HasZeroObject C] : leftDim (0 : C) = 0 := by
  rw [← leftTrace_id, id_zero, leftTrace_zero]

/-- The left trace commutes with finite sums. -/
@[simp]
theorem leftTrace_sum {ι : Type*} {X : C} (s : Finset ι) (f : ι → (X ⟶ X)) :
    leftTrace (∑ i ∈ s, f i) = ∑ i ∈ s, leftTrace (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

/-- The left trace commutes with negation. -/
@[simp]
theorem leftTrace_neg {X : C} (f : X ⟶ X) : leftTrace (-f) = -leftTrace f :=
  eq_neg_of_add_eq_zero_left (by rw [← leftTrace_add, neg_add_cancel, leftTrace_zero])

/-- The left trace commutes with subtraction. -/
@[simp]
theorem leftTrace_sub {X : C} (f g : X ⟶ X) : leftTrace (f - g) = leftTrace f - leftTrace g := by
  rw [sub_eq_add_neg, leftTrace_add, leftTrace_neg, sub_eq_add_neg]

/-- The right trace is additive. -/
@[simp]
theorem rightTrace_add {X : C} (f g : X ⟶ X) :
    rightTrace (f + g) = rightTrace f + rightTrace g := by
  simp [rightTrace_def]

/-- The right trace of zero is zero. -/
@[simp]
theorem rightTrace_zero (X : C) : rightTrace (0 : X ⟶ X) = 0 := by
  simp [rightTrace_def]

/-- The zero object has right pivotal dimension zero. -/
@[simp]
theorem rightDim_zero [HasZeroObject C] : rightDim (0 : C) = 0 := by
  rw [← rightTrace_id, id_zero, rightTrace_zero]

/-- The right trace commutes with finite sums. -/
@[simp]
theorem rightTrace_sum {ι : Type*} {X : C} (s : Finset ι) (f : ι → (X ⟶ X)) :
    rightTrace (∑ i ∈ s, f i) = ∑ i ∈ s, rightTrace (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

/-- The right trace commutes with negation. -/
@[simp]
theorem rightTrace_neg {X : C} (f : X ⟶ X) : rightTrace (-f) = -rightTrace f :=
  eq_neg_of_add_eq_zero_left (by rw [← rightTrace_add, neg_add_cancel, rightTrace_zero])

/-- The right trace commutes with subtraction. -/
@[simp]
theorem rightTrace_sub {X : C} (f g : X ⟶ X) :
    rightTrace (f - g) = rightTrace f - rightTrace g := by
  rw [sub_eq_add_neg, rightTrace_add, rightTrace_neg, sub_eq_add_neg]

variable {R : Type*} [Semiring R] [Linear R C] [MonoidalLinear R C]

/-- The left trace is `R`-linear in an `R`-linear monoidal category. -/
@[simp]
theorem leftTrace_smul {X : C} (r : R) (f : X ⟶ X) : leftTrace (r • f) = r • leftTrace f := by
  simp [leftTrace_def]

/-- The right trace is `R`-linear in an `R`-linear monoidal category. -/
@[simp]
theorem rightTrace_smul {X : C} (r : R) (f : X ⟶ X) : rightTrace (r • f) = r • rightTrace f := by
  simp [rightTrace_def]

end Linear

end TauCeti

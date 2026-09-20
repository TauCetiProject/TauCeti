/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# The internal hom out of a dualizable object

Let `C` be a monoidal category in which an object `Y` is closed, so that `(Y ⟶[C] -)` is right
adjoint to `Y ⊗ -`. If `Y` also admits a left dual, that is, if `ExactPairing D Y` holds for some
object `D`, then `D ⊗ -` is a second right adjoint of `Y ⊗ -`, and the two agree:

```text
(Y ⟶[C] Z) ≅ D ⊗ Z,      in particular      (Y ⟶[C] 𝟙_ C) ≅ D.
```

So the internal hom into the unit computes the left dual, and the internal hom out of `Y` is
tensoring with that dual. The comparison is characterized by the evaluation of the internal hom:
under it, the evaluation becomes the composite
`Y ⊗ (D ⊗ Z) ⟶ (Y ⊗ D) ⊗ Z ⟶ 𝟙_ C ⊗ Z ⟶ Z` built from the pairing `ε_ D Y`, and over the unit
the evaluation becomes the pairing itself.

The dual `D` is an explicit argument rather than `CategoryTheory.HasLeftDual`, so that a caller
with a preferred model of the dual — for instance a finite free sheaf of modules, which is its
own dual — gets the comparison with that model. Taking `D = ᘁY` gives `(Y ⟶[C] 𝟙_ C) ≅ ᘁY`.

Mathlib builds the two adjunctions separately, as `CategoryTheory.ihom.adjunction` for the
closed structure and `CategoryTheory.tensorLeftAdjunction` for the pairing; the comparison here
is their uniqueness isomorphism `CategoryTheory.Adjunction.rightAdjointUniq`.

## Main declarations

* `TauCeti.tensorLeftAdjunction_unit_app` and `TauCeti.tensorLeftAdjunction_counit_app`: the unit
  and the counit of the adjunction attached to an exact pairing, as the coevaluation and the
  evaluation;
* `TauCeti.ihomIsoTensorLeft`: the natural isomorphism `ihom Y ≅ tensorLeft D`, together with the
  componentwise formulas `TauCeti.ihomIsoTensorLeft_hom_app`,
  `TauCeti.ihomIsoTensorLeft_inv_app` and
  `TauCeti.whiskerLeft_ihomIsoTensorLeft_inv_app_comp_ev`;
* `TauCeti.ihomUnitIso`: the isomorphism `(Y ⟶[C] 𝟙_ C) ≅ D` between the internal hom into the
  unit and the dual, whose inverse transposes the pairing
  (`TauCeti.ihomUnitIso_inv`);
* `TauCeti.exactPairingIhomUnit`: the internal hom into the unit is itself a left dual of `Y`,
  with evaluation and coevaluation exposed by `TauCeti.exactPairingIhomUnit_evaluation` and
  `TauCeti.exactPairingIhomUnit_coevaluation`.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (D Y : C) [ExactPairing D Y]

/-- The evaluation of an exact pairing transported across an isomorphism in its left argument.

This is not a `simp` lemma: `CategoryTheory.exactPairingCongrLeft` is how a transported pairing
is *built*, so rewriting with it would unfold the evaluation of every such pairing and rob the
transported instance of its own normal form. -/
@[reassoc]
theorem exactPairingCongrLeft_evaluation {X X' Y : C} [ExactPairing X' Y] (i : X ≅ X') :
    @ExactPairing.evaluation C _ _ X Y (exactPairingCongrLeft i) = Y ◁ i.hom ≫ ε_ X' Y :=
  rfl

/-- The coevaluation of an exact pairing transported across an isomorphism in its left
argument. Not a `simp` lemma, for the reason given on
`TauCeti.exactPairingCongrLeft_evaluation`. -/
@[reassoc]
theorem exactPairingCongrLeft_coevaluation {X X' Y : C} [ExactPairing X' Y] (i : X ≅ X') :
    @ExactPairing.coevaluation C _ _ X Y (exactPairingCongrLeft i) = η_ X' Y ≫ i.inv ▷ Y :=
  rfl

/-- The unit of the adjunction `tensorLeft Y ⊣ tensorLeft D` attached to an exact pairing
`ExactPairing D Y` inserts the coevaluation. -/
theorem tensorLeftAdjunction_unit_app (Z : C) :
    (tensorLeftAdjunction D Y).unit.app Z = (λ_ Z).inv ≫ η_ D Y ▷ Z ≫ (α_ D Y Z).hom := by
  simp [tensorLeftAdjunction, tensorLeftHomEquiv]

/-- The counit of the adjunction `tensorLeft Y ⊣ tensorLeft D` attached to an exact pairing
`ExactPairing D Y` contracts the evaluation. -/
theorem tensorLeftAdjunction_counit_app (Z : C) :
    (tensorLeftAdjunction D Y).counit.app Z = (α_ Y D Z).inv ≫ ε_ D Y ▷ Z ≫ (λ_ Z).hom := by
  simp [tensorLeftAdjunction, tensorLeftHomEquiv]

variable [Closed Y]

/-- The internal hom out of `Y` is left tensoring by a left dual `D` of `Y`: both functors are
right adjoint to `Y ⊗ -`. -/
def ihomIsoTensorLeft : ihom Y ≅ tensorLeft D :=
  (ihom.adjunction Y).rightAdjointUniq (tensorLeftAdjunction D Y)

variable {D Y}

/-- Under the comparison `D ⊗ Z ⟶ (Y ⟶[C] Z)`, the evaluation of the internal hom becomes the
evaluation of the pairing. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_ihomIsoTensorLeft_inv_app_comp_ev (Z : C) :
    Y ◁ (ihomIsoTensorLeft D Y).inv.app Z ≫ (ihom.ev Y).app Z =
      (α_ Y D Z).inv ≫ ε_ D Y ▷ Z ≫ (λ_ Z).hom := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit
    (tensorLeftAdjunction D Y) (ihom.adjunction Y) Z
  rw [tensorLeftAdjunction_counit_app] at h
  simpa [ihomIsoTensorLeft, Adjunction.rightAdjointUniq_inv_app] using h

/-- Under the comparison `(Y ⟶[C] Z) ⟶ D ⊗ Z`, the evaluation of the pairing becomes the
evaluation of the internal hom. -/
@[reassoc]
theorem whiskerLeft_ihomIsoTensorLeft_hom_app_comp_evaluation (Z : C) :
    Y ◁ (ihomIsoTensorLeft D Y).hom.app Z ≫ (α_ Y D Z).inv ≫ ε_ D Y ▷ Z ≫ (λ_ Z).hom =
      (ihom.ev Y).app Z := by
  rw [← whiskerLeft_ihomIsoTensorLeft_inv_app_comp_ev (D := D) (Y := Y) Z, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id_app]
  simp

/-- The comparison `(Y ⟶[C] Z) ⟶ D ⊗ Z` inserts the coevaluation and then evaluates. -/
theorem ihomIsoTensorLeft_hom_app (Z : C) :
    (ihomIsoTensorLeft D Y).hom.app Z =
      (λ_ _).inv ≫ η_ D Y ▷ _ ≫ (α_ D Y _).hom ≫ D ◁ (ihom.ev Y).app Z := by
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app
    (ihom.adjunction Y) (tensorLeftAdjunction D Y) Z
  rw [Equiv.symm_apply_eq] at h
  simpa [ihomIsoTensorLeft, tensorLeftAdjunction, tensorLeftHomEquiv] using h

/-- The comparison `D ⊗ Z ⟶ (Y ⟶[C] Z)` is the transpose of the evaluation of the pairing. -/
theorem ihomIsoTensorLeft_inv_app (Z : C) :
    (ihomIsoTensorLeft D Y).inv.app Z =
      curry ((α_ Y D Z).inv ≫ ε_ D Y ▷ Z ≫ (λ_ Z).hom) := by
  rw [← whiskerLeft_ihomIsoTensorLeft_inv_app_comp_ev, ← uncurry_eq, curry_uncurry]

/-- The comparison is natural in the source: precomposing the internal hom with `f : Y ⟶ Y'`
corresponds to tensoring with the left adjoint mate `ᘁf`. -/
theorem ihomIsoTensorLeft_hom_app_comp_whiskerRight_leftAdjointMate {Y Y' : C} [HasLeftDual Y]
    [HasLeftDual Y'] [Closed Y] [Closed Y'] (f : Y ⟶ Y') (Z : C) :
    (ihomIsoTensorLeft (ᘁY') Y').hom.app Z ≫ (ᘁf) ▷ Z =
      (pre f).app Z ≫ (ihomIsoTensorLeft (ᘁY) Y).hom.app Z := by
  apply (tensorLeftHomEquiv ((ihom Y').obj Z) (ᘁY) Y Z).symm.injective
  simp only [curriedTensor_obj_obj, tensorLeftHomEquiv, Equiv.coe_fn_symm_mk,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    whiskerLeft_ihomIsoTensorLeft_hom_app_comp_evaluation, id_tensor_pre_app_comp_ev]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    leftAdjointMate_comp_evaluation, comp_whiskerRight_assoc,
    ← associator_inv_naturality_left_assoc]
  -- This last exchange is a separate `rw` because its pattern only becomes visible once the
  -- rewrites above have fixed the objects around the comparison.
  rw [whisker_exchange_assoc, whiskerLeft_ihomIsoTensorLeft_hom_app_comp_evaluation]

variable (D Y)

/-- The internal hom of `Y` into the unit is a left dual of `Y`. -/
def ihomUnitIso : (Y ⟶[C] 𝟙_ C) ≅ D :=
  (ihomIsoTensorLeft D Y).app (𝟙_ C) ≪≫ ρ_ D

/-- The comparison `(Y ⟶[C] 𝟙_ C) ⟶ D` inserts the coevaluation and then evaluates. -/
theorem ihomUnitIso_hom :
    (ihomUnitIso D Y).hom =
      (λ_ _).inv ≫ η_ D Y ▷ _ ≫ (α_ D Y _).hom ≫ D ◁ (ihom.ev Y).app (𝟙_ C) ≫ (ρ_ D).hom := by
  simp [ihomUnitIso, ihomIsoTensorLeft_hom_app]

/-- Under the comparison `D ⟶ (Y ⟶[C] 𝟙_ C)`, the evaluation of the internal hom becomes the
evaluation of the pairing. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_ihomUnitIso_inv_comp_ev :
    Y ◁ (ihomUnitIso D Y).inv ≫ (ihom.ev Y).app (𝟙_ C) = ε_ D Y := by
  simp only [ihomUnitIso, Iso.trans_inv, Iso.app_inv, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, whiskerLeft_ihomIsoTensorLeft_inv_app_comp_ev]
  rw [unitors_equal, rightUnitor_naturality]
  monoidal

/-- The comparison `D ⟶ (Y ⟶[C] 𝟙_ C)` is the transpose of the evaluation of the pairing. -/
theorem ihomUnitIso_inv : (ihomUnitIso D Y).inv = curry (ε_ D Y) := by
  rw [← whiskerLeft_ihomUnitIso_inv_comp_ev, ← uncurry_eq, curry_uncurry]

/-- Pairing against the comparison `D ⟶ (Y ⟶[C] 𝟙_ C)` is pairing against the dual. -/
@[reassoc]
theorem tensorHom_ihomUnitIso_inv_comp_ev {M N : C} (f : M ⟶ Y) (g : N ⟶ D) :
    (f ⊗ₘ (g ≫ (ihomUnitIso D Y).inv)) ≫ (ihom.ev Y).app (𝟙_ C) = (f ⊗ₘ g) ≫ ε_ D Y := by
  have h : f ⊗ₘ (g ≫ (ihomUnitIso D Y).inv) = (f ⊗ₘ g) ≫ Y ◁ (ihomUnitIso D Y).inv := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id]
  rw [h, Category.assoc, whiskerLeft_ihomUnitIso_inv_comp_ev]

/-- Transporting the pairing along `TauCeti.ihomUnitIso` exhibits the internal hom of `Y` into
the unit as a left dual of `Y`: the categorical dual of `Y` is `Hom(Y, 𝟙_ C)`. -/
@[instance_reducible]
def exactPairingIhomUnit : ExactPairing (Y ⟶[C] 𝟙_ C) Y :=
  exactPairingCongrLeft (ihomUnitIso D Y)

/-- The evaluation of the pairing transported to the internal hom is the internal-hom
evaluation. -/
@[simp]
theorem exactPairingIhomUnit_evaluation :
    @ExactPairing.evaluation C _ _ (Y ⟶[C] 𝟙_ C) Y (exactPairingIhomUnit D Y) =
      (ihom.ev Y).app (𝟙_ C) := by
  rw [exactPairingIhomUnit, exactPairingCongrLeft_evaluation]
  rw [← whiskerLeft_ihomUnitIso_inv_comp_ev (D := D) (Y := Y),
    ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id]
  simp

/-- The coevaluation of the pairing transported to the internal hom is obtained by composing
the original coevaluation with the inverse comparison. -/
@[simp]
theorem exactPairingIhomUnit_coevaluation :
    @ExactPairing.coevaluation C _ _ (Y ⟶[C] 𝟙_ C) Y (exactPairingIhomUnit D Y) =
      η_ D Y ≫ (ihomUnitIso D Y).inv ▷ Y := by
  rw [exactPairingIhomUnit, exactPairingCongrLeft_coevaluation]

end TauCeti

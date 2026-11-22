/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.SquaredNorm
public import TauCeti.CategoryTheory.Monoidal.Rigid.Simple
public import TauCeti.CategoryTheory.Semisimple.Basic

/-!
# Opposite exact pairings of simple objects

In a finite semisimple rigid monoidal abelian category with simple tensor unit, every simple object
`X` has nonzero evaluation `ε_ X Xᘁ : Xᘁ ⊗ X ⟶ 𝟙_ C`, hence a split epimorphism. Transposing a
chosen section `𝟙_ C ⟶ Xᘁ ⊗ X` gives an isomorphism `TauCeti.simpleDoubleDualIso X : X ≅ Xᘁᘁ` and
a chosen opposite exact pairing `TauCeti.simpleOppositeExactPairing X : ExactPairing Xᘁ X` whose
coevaluation splits `ε_ X Xᘁ`, so `squaredNorm (simpleDoubleDualIso X)` equals `η_ X Xᘁ` followed
by the opposite evaluation (`TauCeti.squaredNorm_simpleDoubleDualIso`).

Neither a pivotal structure nor a field is needed for the construction, and when `u : X ≅ 𝟙_ C`
the pairing is already unique and agrees with the unit pairing transported along `u` and
`u.rightAdjointMate.symm`. Over an algebraically closed field `k` with
`FiniteDimensional k (X ⟶ X)`, Schur's lemma makes `𝟙_ C ⟶ Xᘁ ⊗ X` one-dimensional, so
`simpleDoubleDualIso X` and `simpleOppositeExactPairing X` are canonical, unique, and compatible
with isomorphisms of split simple objects; both algebraic-closedness and finite-dimensionality are
necessary (otherwise `End(X)` can be a larger division algebra and `ε_ X Xᘁ` admits an affine space
of sections).

## Main declarations

* `TauCeti.simpleDoubleDualIso` and
  `TauCeti.coevaluation_comp_whiskerLeft_simpleDoubleDualIso_inv_comp_evaluation`: a chosen
  isomorphism `X ≅ Xᘁᘁ` whose inverse carries `η_ Xᘁ Xᘁᘁ` to a section of `ε_ X Xᘁ`;
* `TauCeti.simpleOppositeExactPairing` with `_def`, `_evaluation`, `_coevaluation`,
  `_coevaluation_comp_evaluation`, and `TauCeti.squaredNorm_simpleDoubleDualIso`;
* `TauCeti.simpleOppositeExactPairing_coevaluation_of_iso_unit` and `_evaluation_of_iso_unit`:
  field-free formulas when `X ≅ 𝟙_ C`;
* `TauCeti.eq_simpleOppositeExactPairing_coevaluation_iff`,
  `TauCeti.eq_simpleDoubleDualIso_inv_iff`, `TauCeti.simpleDoubleDualIso_inv_conj`,
  `TauCeti.hom_comp_simpleDoubleDualIso_hom`,
  `TauCeti.simpleOppositeExactPairing_coevaluation_congr`, and `_evaluation_congr`: uniqueness and
  isomorphism compatibility for split simple objects over an algebraically closed field.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §2
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§4.8, 7.21
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace TauCeti

universe w v u

section Construction

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [RigidCategory C] [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]

private theorem isSplitEpi_evaluation (X : C) [Simple X] : IsSplitEpi (ε_ X Xᘁ) :=
  isSplitEpi_of_nonzero_to_simple (evaluation_ne_zero (Simple.not_isZero X))

private def simpleEvalSection (X : C) [Simple X] : 𝟙_ C ⟶ Xᘁ ⊗ X :=
  have := isSplitEpi_evaluation X; section_ (ε_ X Xᘁ)

@[reassoc]
private theorem simpleEvalSection_comp_evaluation (X : C) [Simple X] :
    simpleEvalSection X ≫ ε_ X Xᘁ = 𝟙 (𝟙_ C) :=
  have := isSplitEpi_evaluation X; IsSplitEpi.id (ε_ X Xᘁ)

private def simpleDoubleDualInvAux (X : C) [Simple X] : ((Xᘁ : C)ᘁ : C) ⟶ X :=
  (ρ_ ((Xᘁ : C)ᘁ : C)).inv ≫
    (tensorLeftHomEquiv (𝟙_ C) Xᘁ ((Xᘁ : C)ᘁ : C) X).symm (simpleEvalSection X)

@[reassoc]
private theorem coevaluation_comp_whiskerLeft_simpleDoubleDualInvAux (X : C) [Simple X] :
    η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ Xᘁ ◁ simpleDoubleDualInvAux X = simpleEvalSection X := by
  apply (tensorLeftHomEquiv (𝟙_ C) Xᘁ ((Xᘁ : C)ᘁ : C) X).symm.injective
  rw [tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft]
  simp [simpleDoubleDualInvAux]

variable [MonoidalPreadditive C]

/-- In a finite semisimple rigid category with simple tensor unit, every simple object `X` admits an
isomorphism `X ≅ Xᘁᘁ` whose inverse carries the coevaluation of `(Xᘁ, Xᘁᘁ)` to a section of
`ε_ X Xᘁ`. Over an algebraically closed field where `X` is split, this isomorphism is unique
(`TauCeti.eq_simpleDoubleDualIso_inv_iff`). -/
def simpleDoubleDualIso (X : C) [Simple X] : X ≅ ((Xᘁ : C)ᘁ : C) := by
  have hg : simpleDoubleDualInvAux X ≠ 0 := fun h ↦ by
    have hs := coevaluation_comp_whiskerLeft_simpleDoubleDualInvAux X
    rw [h, MonoidalPreadditive.whiskerLeft_zero, comp_zero] at hs
    have hid := simpleEvalSection_comp_evaluation X
    rw [← hs, zero_comp] at hid
    exact CategoryTheory.id_ne_zero (𝟙_ C) hid.symm
  have := isIso_of_hom_simple hg
  exact (asIso (simpleDoubleDualInvAux X)).symm

/-- `(simpleDoubleDualIso X).inv` carries `η_ Xᘁ Xᘁᘁ` to a section of `ε_ X Xᘁ`. -/
@[reassoc (attr := simp)]
theorem coevaluation_comp_whiskerLeft_simpleDoubleDualIso_inv_comp_evaluation (X : C) [Simple X] :
    η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ Xᘁ ◁ (simpleDoubleDualIso X).inv ≫ ε_ X Xᘁ = 𝟙 (𝟙_ C) :=
  (coevaluation_comp_whiskerLeft_simpleDoubleDualInvAux_assoc X _).trans
    (simpleEvalSection_comp_evaluation X)

/-- A chosen opposite exact pairing `ExactPairing Xᘁ X` of a simple object `X` in a finite
semisimple rigid category with simple tensor unit, obtained by transporting the pairing of `Xᘁ` and
`Xᘁᘁ` along `TauCeti.simpleDoubleDualIso X`. Over an algebraically closed field where `X` is split,
this pairing is canonical and unique (`TauCeti.eq_simpleOppositeExactPairing_coevaluation_iff`). -/
@[instance_reducible]
def simpleOppositeExactPairing (X : C) [Simple X] : ExactPairing Xᘁ X :=
  exactPairingCongrRight (simpleDoubleDualIso X)

/-- `TauCeti.simpleOppositeExactPairing` transports the right-dual pairing of `Xᘁ` along
`TauCeti.simpleDoubleDualIso`. -/
theorem simpleOppositeExactPairing_def (X : C) [Simple X] :
    simpleOppositeExactPairing X = exactPairingCongrRight (simpleDoubleDualIso X) := (rfl)

/-- The evaluation `X ⊗ Xᘁ ⟶ 𝟙_ C` of `TauCeti.simpleOppositeExactPairing X`. -/
theorem simpleOppositeExactPairing_evaluation (X : C) [Simple X] :
    @ExactPairing.evaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) =
      (simpleDoubleDualIso X).hom ▷ Xᘁ ≫ ε_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) :=
  exactPairingCongrRight_evaluation _

/-- The coevaluation `𝟙_ C ⟶ Xᘁ ⊗ X` of `TauCeti.simpleOppositeExactPairing X`. -/
theorem simpleOppositeExactPairing_coevaluation (X : C) [Simple X] :
    @ExactPairing.coevaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) =
      η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ Xᘁ ◁ (simpleDoubleDualIso X).inv :=
  exactPairingCongrRight_coevaluation _

/-- The coevaluation of `TauCeti.simpleOppositeExactPairing X` is a section of `ε_ X Xᘁ`. -/
@[reassoc (attr := simp)]
theorem simpleOppositeExactPairing_coevaluation_comp_evaluation (X : C) [Simple X] :
    @ExactPairing.coevaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) ≫ ε_ X Xᘁ = 𝟙 (𝟙_ C) := by
  rw [simpleOppositeExactPairing_coevaluation, Category.assoc,
    coevaluation_comp_whiskerLeft_simpleDoubleDualIso_inv_comp_evaluation]

/-- The squared norm of a simple object `X`, computed with `TauCeti.simpleDoubleDualIso X`, equals
`η_ X Xᘁ` followed by the evaluation of `TauCeti.simpleOppositeExactPairing X`. -/
theorem squaredNorm_simpleDoubleDualIso (X : C) [Simple X] :
    squaredNorm (simpleDoubleDualIso X) =
      η_ X Xᘁ ≫ @ExactPairing.evaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) := by
  rw [squaredNorm_def, doubleDualTrace_rightAdjointMate,
    coevaluation_comp_whiskerLeft_simpleDoubleDualIso_inv_comp_evaluation, Category.comp_id,
    doubleDualTrace_def, simpleOppositeExactPairing_evaluation]

/-- When a simple object `X` is equipped with an isomorphism `u : X ≅ 𝟙_ C`, the coevaluation of
`TauCeti.simpleOppositeExactPairing X` is `(λ_ (𝟙_ C)).inv` followed by `(u.hom)ᘁ ⊗ₘ u.inv`,
with no linearity or field hypotheses required. -/
theorem simpleOppositeExactPairing_coevaluation_of_iso_unit {X : C} [Simple X] (u : X ≅ 𝟙_ C) :
    @ExactPairing.coevaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) =
      (λ_ (𝟙_ C)).inv ≫ ((u.hom)ᘁ ⊗ₘ u.inv) := by
  let s : 𝟙_ C ⟶ Xᘁ ⊗ X := (λ_ (𝟙_ C)).inv ≫ ((u.hom)ᘁ ⊗ₘ u.inv)
  have : IsIso s := by dsimp only [s]; rw [← Iso.rightAdjointMate_hom u]; infer_instance
  have hs : s ≫ ε_ X Xᘁ = 𝟙 (𝟙_ C) := by
    rw [Category.assoc, tensorHom_def', Category.assoc,
      rightAdjointMate_whiskerRight_comp_evaluation_of_unit, ← Category.assoc,
      ← leftUnitor_inv_naturality, Category.assoc, Iso.inv_hom_id_assoc, u.inv_hom_id]
  have hεs : ε_ X Xᘁ ≫ s = 𝟙 (Xᘁ ⊗ X) := by rw [← cancel_epi s, reassoc_of% hs, Category.comp_id]
  rw [← Category.comp_id (@ExactPairing.coevaluation C _ _ Xᘁ X (simpleOppositeExactPairing X)),
    ← hεs, ← Category.assoc, simpleOppositeExactPairing_coevaluation_comp_evaluation,
    Category.id_comp]

/-- When a simple object `X` is equipped with an isomorphism `u : X ≅ 𝟙_ C`, the evaluation of
`TauCeti.simpleOppositeExactPairing X` is `u.hom ⊗ₘ (u.inv)ᘁ` followed by `(λ_ (𝟙_ C)).hom`,
with no linearity or field hypotheses required. -/
theorem simpleOppositeExactPairing_evaluation_of_iso_unit {X : C} [Simple X] (u : X ≅ 𝟙_ C) :
    @ExactPairing.evaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) =
      (u.hom ⊗ₘ (u.inv)ᘁ) ≫ (λ_ (𝟙_ C)).hom := by
  let v : Xᘁ ≅ 𝟙_ C := u.rightAdjointMate.symm
  let p₂ : ExactPairing Xᘁ X := exactPairingCongr v u
  have hcoev : @ExactPairing.coevaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) =
      @ExactPairing.coevaluation C _ _ Xᘁ X p₂ := by
    rw [simpleOppositeExactPairing_coevaluation_of_iso_unit u, exactPairingCongr_coevaluation,
      ExactPairing.unit_coevaluation, ← tensorHom_def', unitors_inv_equal]
    simp [v]
  rw [ExactPairing.evaluation_eq_of_coevaluation_eq (simpleOppositeExactPairing X) p₂ hcoev,
    exactPairingCongr_evaluation, ExactPairing.unit_evaluation, ← tensorHom_def'_assoc,
    ← unitors_equal]
  simp [v]

end Construction

section Uniqueness

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [Linear k C] [MonoidalLinear k C] [RigidCategory C] [IsFiniteSemisimpleCategory C]
  [Simple (𝟙_ C)]

include k in
/-- Over an algebraically closed field, the coevaluation of `TauCeti.simpleOppositeExactPairing X`
for a split simple object `X` is the unique section of `ε_ X Xᘁ`. -/
theorem eq_simpleOppositeExactPairing_coevaluation_iff
    {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)] {t : 𝟙_ C ⟶ Xᘁ ⊗ X} :
    t = @ExactPairing.coevaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) ↔
      t ≫ ε_ X Xᘁ = 𝟙 (𝟙_ C) := by
  refine ⟨by rintro rfl; exact simpleOppositeExactPairing_coevaluation_comp_evaluation X,
    fun ht ↦ ?_⟩
  let _ : ExactPairing Xᘁ X := simpleOppositeExactPairing X
  obtain ⟨c, rfl⟩ := hom_from_tensorUnit_eq_smul_coevaluation_of_simple_right k t
  rw [Linear.smul_comp, simpleOppositeExactPairing_coevaluation_comp_evaluation] at ht
  have hc : c = 1 := sub_eq_zero.1 <|
    (smul_eq_zero.1 (by rw [sub_smul, one_smul, ht, sub_self])).resolve_right
      (CategoryTheory.id_ne_zero (𝟙_ C))
  rw [hc, one_smul]

include k in
/-- Over an algebraically closed field, `(simpleDoubleDualIso X).inv` for a split simple object `X`
is uniquely characterized by carrying `η_ Xᘁ Xᘁᘁ` to a section of `ε_ X Xᘁ`. -/
theorem eq_simpleDoubleDualIso_inv_iff
    {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)] {g : ((Xᘁ : C)ᘁ : C) ⟶ X} :
    g = (simpleDoubleDualIso X).inv ↔
      η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ Xᘁ ◁ g ≫ ε_ X Xᘁ = 𝟙 (𝟙_ C) := by
  rw [← Category.assoc, ← eq_simpleOppositeExactPairing_coevaluation_iff k,
    simpleOppositeExactPairing_coevaluation]
  refine ⟨by rintro rfl; rfl, fun h ↦ ?_⟩
  simpa using congrArg (tensorLeftHomEquiv (𝟙_ C) Xᘁ ((Xᘁ : C)ᘁ : C) X).symm h

include k in
/-- An isomorphism `u : X ≅ Y` between split simple objects transports the coevaluation of
`TauCeti.simpleOppositeExactPairing X` to that of `TauCeti.simpleOppositeExactPairing Y`. -/
@[reassoc]
theorem simpleOppositeExactPairing_coevaluation_congr {X Y : C} [Simple X] [Simple Y]
    [FiniteDimensional k (X ⟶ X)] (u : X ≅ Y) :
    @ExactPairing.coevaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) ≫
        ((u.inv)ᘁ ⊗ₘ u.hom) =
      @ExactPairing.coevaluation C _ _ Yᘁ Y (simpleOppositeExactPairing Y) := by
  have : FiniteDimensional k (Y ⟶ Y) := Module.Finite.equiv (Linear.homCongr k u u)
  rw [eq_simpleOppositeExactPairing_coevaluation_iff k, Category.assoc, tensorHom_def',
    Category.assoc, rightAdjointMate_comp_evaluation, ← whiskerLeft_comp_assoc, u.hom_inv_id,
    whiskerLeft_id, Category.id_comp, simpleOppositeExactPairing_coevaluation_comp_evaluation]

include k in
/-- `TauCeti.simpleDoubleDualIso` commutes with any isomorphism `u : X ≅ Y` between split simple
objects, stated for the inverse morphisms. -/
@[reassoc]
theorem simpleDoubleDualIso_inv_conj {X Y : C} [Simple X] [Simple Y]
    [FiniteDimensional k (X ⟶ X)] (u : X ≅ Y) :
    ((u.inv)ᘁ)ᘁ ≫ (simpleDoubleDualIso X).inv ≫ u.hom = (simpleDoubleDualIso Y).inv := by
  have : FiniteDimensional k (Y ⟶ Y) := Module.Finite.equiv (Linear.homCongr k u u)
  rw [eq_simpleDoubleDualIso_inv_iff k, whiskerLeft_comp_assoc, ← Category.assoc,
    coevaluation_comp_rightAdjointMate (f := (u.inv)ᘁ), Category.assoc, ← whisker_exchange_assoc,
    whiskerLeft_comp_assoc, ← tensorHom_def'_assoc, ← Category.assoc,
    ← simpleOppositeExactPairing_coevaluation,
    simpleOppositeExactPairing_coevaluation_congr_assoc k u,
    simpleOppositeExactPairing_coevaluation_comp_evaluation]

include k in
/-- `TauCeti.simpleDoubleDualIso` commutes with any isomorphism `u : X ≅ Y` between split simple
objects, stated for the forward morphisms. -/
@[reassoc]
theorem hom_comp_simpleDoubleDualIso_hom {X Y : C} [Simple X] [Simple Y]
    [FiniteDimensional k (X ⟶ X)] (u : X ≅ Y) :
    u.hom ≫ (simpleDoubleDualIso Y).hom = (simpleDoubleDualIso X).hom ≫ ((u.hom)ᘁ)ᘁ := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv]
  have h := simpleDoubleDualIso_inv_conj k u
  rw [← Iso.rightAdjointMate_inv, ← Iso.rightAdjointMate_inv, Iso.inv_comp_eq] at h
  simpa [Iso.rightAdjointMate_hom] using h

include k in
/-- An isomorphism `u : X ≅ Y` between split simple objects transports the evaluation of
`TauCeti.simpleOppositeExactPairing Y` to that of `TauCeti.simpleOppositeExactPairing X`. -/
@[reassoc]
theorem simpleOppositeExactPairing_evaluation_congr {X Y : C} [Simple X] [Simple Y]
    [FiniteDimensional k (X ⟶ X)] (u : X ≅ Y) :
    (u.hom ⊗ₘ (u.inv)ᘁ) ≫
        @ExactPairing.evaluation C _ _ Yᘁ Y (simpleOppositeExactPairing Y) =
      @ExactPairing.evaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) := by
  let _ : ExactPairing Yᘁ Y := simpleOppositeExactPairing Y
  let p₂ : ExactPairing Xᘁ X := exactPairingCongr u.rightAdjointMate.symm u
  have hcoev : @ExactPairing.coevaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) =
      @ExactPairing.coevaluation C _ _ Xᘁ X p₂ := by
    rw [exactPairingCongr_coevaluation, ← simpleOppositeExactPairing_coevaluation_congr k u,
      Category.assoc, Iso.symm_inv, Iso.rightAdjointMate_hom, ← tensorHom_def',
      tensorHom_comp_tensorHom, ← comp_rightAdjointMate, u.hom_inv_id, rightAdjointMate_id,
      id_tensorHom_id, Category.comp_id]
  rw [ExactPairing.evaluation_eq_of_coevaluation_eq (simpleOppositeExactPairing X) p₂ hcoev,
    exactPairingCongr_evaluation, Iso.symm_hom, Iso.rightAdjointMate_inv, ← tensorHom_def'_assoc]

end Uniqueness

end TauCeti

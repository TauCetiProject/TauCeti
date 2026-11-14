/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.DualFunctor
public import TauCeti.CategoryTheory.Monoidal.Rigid.Simple
public import TauCeti.CategoryTheory.Semisimple.Basic

/-!
# The canonical opposite pairing of a simple object

In a rigid monoidal abelian category which is finite semisimple with simple tensor unit, every
simple object `X` has a nonzero evaluation morphism `ε_ X Xᘁ : Xᘁ ⊗ X ⟶ 𝟙_ C`. Because `𝟙_ C` is
simple, `ε_ X Xᘁ` is a split epimorphism; transposing a section `𝟙_ C ⟶ Xᘁ ⊗ X` along Frobenius
reciprocity yields a nonzero morphism `Xᘁᘁ ⟶ X` between simple objects, hence an isomorphism
`TauCeti.simpleDoubleDualIso X : X ≅ Xᘁᘁ`. Transporting the canonical exact pairing of `Xᘁ` and
`Xᘁᘁ` along this isomorphism equips `X` with an opposite exact pairing
`TauCeti.simpleOppositeExactPairing X : ExactPairing Xᘁ X` whose coevaluation `𝟙_ C ⟶ Xᘁ ⊗ X` is a
section of `ε_ X Xᘁ`.

Neither a pivotal structure nor a coefficient field is required to construct this pairing. Over an
algebraically closed field `k` over which `C` is `k`-linear with `X ⟶ X` finite-dimensional, Schur's
lemma makes `𝟙_ C ⟶ Xᘁ ⊗ X` one-dimensional, so the section `𝟙_ C ⟶ Xᘁ ⊗ X` of `ε_ X Xᘁ` — and
therefore `simpleDoubleDualIso X` and `simpleOppositeExactPairing X` — is unique. Both
algebraic-closedness and finite-dimensionality are necessary for uniqueness: when `End(X)` is a
division algebra strictly larger than `k`, `𝟙_ C ⟶ Xᘁ ⊗ X` has dimension greater than `1` and
`ε_ X Xᘁ` admits an affine space of sections. Under uniqueness, `simpleDoubleDualIso` commutes with
every isomorphism between simple objects, and for a simple object `X` isomorphic to `𝟙_ C` its
opposite pairing agrees with the unit pairing transported along `u : X ≅ 𝟙_ C` and its dual mate.

## Main declarations

* `TauCeti.simpleDoubleDualIso`: the isomorphism `X ≅ Xᘁᘁ` for a simple object `X`, normalized so
  that the transported coevaluation splits `ε_ X Xᘁ`;
* `TauCeti.simpleOppositeExactPairing`: the opposite exact pairing `ExactPairing Xᘁ X` of a simple
  object `X`, with evaluation and coevaluation formulas
  `TauCeti.simpleOppositeExactPairing_evaluation` and
  `TauCeti.simpleOppositeExactPairing_coevaluation`, normalized by
  `TauCeti.simpleOppositeExactPairing_coevaluation_comp_evaluation`;
* `TauCeti.eq_simpleOppositeExactPairing_coevaluation_iff` and
  `TauCeti.eq_simpleDoubleDualIso_inv_iff`: uniqueness of the normalized coevaluation and double
  dual isomorphism for a split simple object over an algebraically closed field;
* `TauCeti.simpleDoubleDualIso_inv_conj`, `TauCeti.simpleDoubleDualIso_hom_conj`,
  `TauCeti.simpleOppositeExactPairing_coevaluation_congr` and
  `TauCeti.simpleOppositeExactPairing_evaluation_congr`: compatibility with an isomorphism `X ≅ Y`
  of simple objects;
* `TauCeti.rightDualIsoUnitOfIso`,
  `TauCeti.simpleOppositeExactPairing_coevaluation_of_iso_unit` and
  `TauCeti.simpleOppositeExactPairing_evaluation_of_iso_unit`: explicit formulas when `X ≅ 𝟙_ C`.

## References

* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §2
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§4.8, 7.21
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace TauCeti

universe w v u

section RightDualUnit

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- Given an isomorphism `u : X ≅ 𝟙_ C` in a right rigid monoidal category, `Xᘁ` is canonically
isomorphic to `𝟙_ C` by composing the inverse right adjoint mate of `u` with
`TauCeti.rightDualUnitIso C`. -/
def rightDualIsoUnitOfIso {X : C} (u : X ≅ 𝟙_ C) : Xᘁ ≅ 𝟙_ C :=
  (@Iso.rightAdjointMate C _ _ X (𝟙_ C) _ (RightRigidCategory.rightDual (𝟙_ C)) u).symm ≪≫
    rightDualUnitIso C

/-- The forward morphism `Xᘁ ⟶ 𝟙_ C` of `TauCeti.rightDualIsoUnitOfIso u`. -/
theorem rightDualIsoUnitOfIso_hom {X : C} (u : X ≅ 𝟙_ C) :
    (rightDualIsoUnitOfIso u).hom =
      @rightAdjointMate C _ _ (𝟙_ C) X (RightRigidCategory.rightDual (𝟙_ C)) _ u.inv ≫
        (rightDualUnitIso C).hom := by
  let : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
  simp [rightDualIsoUnitOfIso]

/-- The inverse morphism `𝟙_ C ⟶ Xᘁ` of `TauCeti.rightDualIsoUnitOfIso u`. -/
theorem rightDualIsoUnitOfIso_inv {X : C} (u : X ≅ 𝟙_ C) :
    (rightDualIsoUnitOfIso u).inv =
      (rightDualUnitIso C).inv ≫
        @rightAdjointMate C _ _ X (𝟙_ C) _ (RightRigidCategory.rightDual (𝟙_ C)) u.hom := by
  let : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
  simp [rightDualIsoUnitOfIso]

/-- Evaluating `(rightDualIsoUnitOfIso u).inv : 𝟙_ C ⟶ Xᘁ` against `X` recovers `u.hom` after the
left unitor. -/
@[reassoc]
theorem rightDualIsoUnitOfIso_inv_whiskerRight_evaluation {X : C} (u : X ≅ 𝟙_ C) :
    (rightDualIsoUnitOfIso u).inv ▷ X ≫ ε_ X Xᘁ = (λ_ X).hom ≫ u.hom := by
  let p₁ : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
  rw [rightDualIsoUnitOfIso_inv, comp_whiskerRight_assoc,
    @rightAdjointMate_comp_evaluation C _ _ X (𝟙_ C) _ p₁ u.hom, ← whisker_exchange_assoc,
    rightDualUnitIso_inv, ExactPairing.rightDualIso_inv_whiskerRight_evaluation,
    TauCeti.ExactPairing.unit_evaluation, ← unitors_equal, leftUnitor_naturality]

end RightDualUnit

section Construction

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [RigidCategory C] [IsFiniteSemisimpleCategory C] [Simple (𝟙_ C)]

/-- Auxiliary section `𝟙_ C ⟶ Xᘁ ⊗ X` of `ε_ X Xᘁ` for a simple object `X`. -/
private def simpleEvalSection (X : C) [Simple X] : 𝟙_ C ⟶ Xᘁ ⊗ X :=
  have hε : ε_ X Xᘁ ≠ 0 := fun h ↦ by
    have hz := ExactPairing.evaluation_coevaluation X Xᘁ
    rw [h, MonoidalPreadditive.whiskerLeft_zero, comp_zero] at hz
    exact CategoryTheory.id_ne_zero X (by simpa using (λ_ X).inv ≫= hz.symm =≫ (ρ_ X).hom)
  have := isSplitEpi_of_nonzero_to_simple hε
  section_ (ε_ X Xᘁ)

@[reassoc]
private theorem simpleEvalSection_comp_evaluation (X : C) [Simple X] :
    simpleEvalSection X ≫ ε_ X Xᘁ = 𝟙 (𝟙_ C) := by
  have hε : ε_ X Xᘁ ≠ 0 := fun h ↦ by
    have hz := ExactPairing.evaluation_coevaluation X Xᘁ
    rw [h, MonoidalPreadditive.whiskerLeft_zero, comp_zero] at hz
    exact CategoryTheory.id_ne_zero X (by simpa using (λ_ X).inv ≫= hz.symm =≫ (ρ_ X).hom)
  have := isSplitEpi_of_nonzero_to_simple hε
  exact IsSplitEpi.id (ε_ X Xᘁ)

/-- Auxiliary morphism `Xᘁᘁ ⟶ X` obtained by transposing `simpleEvalSection X`. -/
private def simpleDoubleDualInvAux (X : C) [Simple X] : ((Xᘁ : C)ᘁ : C) ⟶ X :=
  (ρ_ ((Xᘁ : C)ᘁ : C)).inv ≫
    (tensorLeftHomEquiv (𝟙_ C) Xᘁ ((Xᘁ : C)ᘁ : C) X).symm (simpleEvalSection X)

@[reassoc]
private theorem coevaluation_comp_whiskerLeft_simpleDoubleDualInvAux (X : C) [Simple X] :
    η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ Xᘁ ◁ simpleDoubleDualInvAux X = simpleEvalSection X := by
  have h : η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ Xᘁ ◁ simpleDoubleDualInvAux X =
      tensorLeftHomEquiv (𝟙_ C) Xᘁ ((Xᘁ : C)ᘁ : C) X
        ((ρ_ ((Xᘁ : C)ᘁ : C)).hom ≫ simpleDoubleDualInvAux X) := by
    dsimp only [tensorLeftHomEquiv, Equiv.coe_fn_mk]
    simp only [whiskerLeft_comp]
    monoidal
  rw [h, simpleDoubleDualInvAux, Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]

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

private theorem simpleDoubleDualIso_inv (X : C) [Simple X] :
    (simpleDoubleDualIso X).inv = simpleDoubleDualInvAux X :=
  rfl

/-- The canonical opposite exact pairing `ExactPairing Xᘁ X` of a simple object `X` in a finite
semisimple rigid category with simple tensor unit, obtained by transporting the pairing of `Xᘁ` and
`Xᘁᘁ` along `TauCeti.simpleDoubleDualIso X`. -/
@[instance_reducible]
def simpleOppositeExactPairing (X : C) [Simple X] : ExactPairing Xᘁ X :=
  exactPairingCongrRight (simpleDoubleDualIso X)

/-- `TauCeti.simpleOppositeExactPairing` transports the right-dual pairing of `Xᘁ` along
`TauCeti.simpleDoubleDualIso`. -/
theorem simpleOppositeExactPairing_def (X : C) [Simple X] :
    simpleOppositeExactPairing X = exactPairingCongrRight (simpleDoubleDualIso X) :=
  (rfl)

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
  rw [simpleOppositeExactPairing_coevaluation, simpleDoubleDualIso_inv,
    coevaluation_comp_whiskerLeft_simpleDoubleDualInvAux, simpleEvalSection_comp_evaluation]

end Construction

section Uniqueness

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [Linear k C] [MonoidalLinear k C] [RigidCategory C] [IsFiniteSemisimpleCategory C]
  [Simple (𝟙_ C)]

include k in
/-- Over an algebraically closed field, any morphism `𝟙_ C ⟶ Xᘁ ⊗ X` for a split simple object `X`
is a scalar multiple of the coevaluation of `TauCeti.simpleOppositeExactPairing X`. -/
theorem hom_from_tensorUnit_eq_smul_simpleOppositeExactPairing_coevaluation
    {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)] (t : 𝟙_ C ⟶ Xᘁ ⊗ X) :
    ∃ c : k, t = c • @ExactPairing.coevaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) := by
  let _ : ExactPairing Xᘁ X := simpleOppositeExactPairing X
  let e : (𝟙_ C ⟶ Xᘁ ⊗ X) ≃ₗ[k] (X ⟶ X) :=
    (tensorLeftHomLinearEquiv k (𝟙_ C) Xᘁ X X).symm.trans (Linear.homCongr k (ρ_ X) (Iso.refl X))
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id k (e t)
  refine ⟨c, e.injective ?_⟩
  rw [map_smul, ← hc]
  congr 1
  -- Under Frobenius reciprocity for `simpleOppositeExactPairing X`, the coevaluation maps to `𝟙 X`.
  have hη : e (η_ Xᘁ X) = 𝟙 X := by
    simp only [e, LinearEquiv.trans_apply, Linear.homCongr_apply, Iso.refl_hom, Category.comp_id,
      tensorLeftHomLinearEquiv_symm_apply, tensorLeftHomEquiv, Equiv.coe_fn_symm_mk]
    calc _ = (ρ_ X).inv ≫ (X ◁ η_ Xᘁ X ≫ (α_ X Xᘁ X).inv ≫ ε_ Xᘁ X ▷ X) ≫ (λ_ X).hom := by monoidal
      _ = 𝟙 X := by rw [ExactPairing.coevaluation_evaluation]; monoidal
  exact hη.symm

include k in
/-- Over an algebraically closed field, the coevaluation of `TauCeti.simpleOppositeExactPairing X`
for a split simple object `X` is the unique section of `ε_ X Xᘁ`. -/
theorem eq_simpleOppositeExactPairing_coevaluation_iff
    {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)] {t : 𝟙_ C ⟶ Xᘁ ⊗ X} :
    t = @ExactPairing.coevaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) ↔
      t ≫ ε_ X Xᘁ = 𝟙 (𝟙_ C) := by
  refine ⟨by rintro rfl; exact simpleOppositeExactPairing_coevaluation_comp_evaluation X,
    fun ht ↦ ?_⟩
  obtain ⟨c, rfl⟩ := hom_from_tensorUnit_eq_smul_simpleOppositeExactPairing_coevaluation k t
  rw [Linear.smul_comp, simpleOppositeExactPairing_coevaluation_comp_evaluation] at ht
  have hc : c = 1 := by
    have hsub : (c - 1) • 𝟙 (𝟙_ C) = 0 := by rw [sub_smul, one_smul, ht, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 hsub).resolve_right (CategoryTheory.id_ne_zero (𝟙_ C)))
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
  -- Whiskering on the left by `Xᘁ` after `η_ Xᘁ Xᘁᘁ` is injective by Frobenius reciprocity.
  have key : ∀ f : ((Xᘁ : C)ᘁ : C) ⟶ X,
      (ρ_ ((Xᘁ : C)ᘁ : C)).inv ≫
        (tensorLeftHomEquiv (𝟙_ C) Xᘁ ((Xᘁ : C)ᘁ : C) X).symm
          (η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ Xᘁ ◁ f) = f := fun f ↦ by
    have hf : η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ Xᘁ ◁ f =
        tensorLeftHomEquiv (𝟙_ C) Xᘁ ((Xᘁ : C)ᘁ : C) X ((ρ_ ((Xᘁ : C)ᘁ : C)).hom ≫ f) := by
      dsimp only [tensorLeftHomEquiv, Equiv.coe_fn_mk]
      simp only [whiskerLeft_comp]
      monoidal
    rw [hf, Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]
  rw [← key g, ← key (simpleDoubleDualIso X).inv, h]

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
  rw [eq_simpleOppositeExactPairing_coevaluation_iff k]
  rw [Category.assoc, tensorHom_def', Category.assoc, rightAdjointMate_comp_evaluation,
    ← whiskerLeft_comp_assoc, u.hom_inv_id, whiskerLeft_id, Category.id_comp,
    simpleOppositeExactPairing_coevaluation_comp_evaluation]

include k in
/-- `TauCeti.simpleDoubleDualIso` commutes with any isomorphism `u : X ≅ Y` between split simple
objects, stated for the inverse morphisms. -/
@[reassoc]
theorem simpleDoubleDualIso_inv_conj {X Y : C} [Simple X] [Simple Y]
    [FiniteDimensional k (X ⟶ X)] (u : X ≅ Y) :
    ((u.inv)ᘁ)ᘁ ≫ (simpleDoubleDualIso X).inv ≫ u.hom = (simpleDoubleDualIso Y).inv := by
  have : FiniteDimensional k (Y ⟶ Y) := Module.Finite.equiv (Linear.homCongr k u u)
  rw [eq_simpleDoubleDualIso_inv_iff k]
  have hmate : η_ (Yᘁ : C) ((Yᘁ : C)ᘁ : C) ≫ Yᘁ ◁ ((u.inv)ᘁ)ᘁ =
      η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ (u.inv)ᘁ ▷ ((Xᘁ : C)ᘁ : C) :=
    coevaluation_comp_rightAdjointMate (f := (u.inv)ᘁ)
  rw [whiskerLeft_comp_assoc, ← Category.assoc, hmate, Category.assoc, ← whisker_exchange_assoc,
    whiskerLeft_comp_assoc, ← tensorHom_def'_assoc, ← Category.assoc,
    ← simpleOppositeExactPairing_coevaluation,
    simpleOppositeExactPairing_coevaluation_congr_assoc k u,
    simpleOppositeExactPairing_coevaluation_comp_evaluation]

include k in
/-- `TauCeti.simpleDoubleDualIso` commutes with any isomorphism `u : X ≅ Y` between split simple
objects, stated for the forward morphisms. -/
@[reassoc]
theorem simpleDoubleDualIso_hom_conj {X Y : C} [Simple X] [Simple Y]
    [FiniteDimensional k (X ⟶ X)] (u : X ≅ Y) :
    u.hom ≫ (simpleDoubleDualIso Y).hom = (simpleDoubleDualIso X).hom ≫ ((u.hom)ᘁ)ᘁ := by
  have h := simpleDoubleDualIso_inv_conj k u
  have hmate : ((u.hom)ᘁ)ᘁ ≫ ((u.inv)ᘁ)ᘁ = 𝟙 ((Xᘁ : C)ᘁ : C) := by
    rw [← comp_rightAdjointMate, ← comp_rightAdjointMate, u.hom_inv_id,
      rightAdjointMate_id, rightAdjointMate_id]
  have h1 : (simpleDoubleDualIso X).hom ≫ ((u.hom)ᘁ)ᘁ ≫
      (((u.inv)ᘁ)ᘁ ≫ (simpleDoubleDualIso X).inv ≫ u.hom) = u.hom := by
    rw [reassoc_of% hmate, Iso.hom_inv_id_assoc]
  rw [h] at h1
  conv_lhs => rw [← h1]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

include k in
/-- An isomorphism `u : X ≅ Y` between split simple objects transports the evaluation of
`TauCeti.simpleOppositeExactPairing Y` to that of `TauCeti.simpleOppositeExactPairing X`. -/
@[reassoc]
theorem simpleOppositeExactPairing_evaluation_congr {X Y : C} [Simple X] [Simple Y]
    [FiniteDimensional k (X ⟶ X)] (u : X ≅ Y) :
    (u.hom ⊗ₘ (u.inv)ᘁ) ≫
        @ExactPairing.evaluation C _ _ Yᘁ Y (simpleOppositeExactPairing Y) =
      @ExactPairing.evaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) := by
  rw [simpleOppositeExactPairing_evaluation, simpleOppositeExactPairing_evaluation,
    tensorHom_def_assoc, ← whisker_exchange_assoc, ← comp_whiskerRight_assoc,
    simpleDoubleDualIso_hom_conj k u, comp_whiskerRight_assoc,
    rightAdjointMate_comp_evaluation, whisker_exchange_assoc, ← whiskerLeft_comp_assoc,
    ← comp_rightAdjointMate, u.hom_inv_id, rightAdjointMate_id, whiskerLeft_id, Category.id_comp]

include k in
/-- When `X` is a split simple object equipped with an isomorphism `u : X ≅ 𝟙_ C`, the coevaluation
of `TauCeti.simpleOppositeExactPairing X` is `(λ_ (𝟙_ C)).inv` followed by
`(rightDualIsoUnitOfIso u).inv ⊗ₘ u.inv`. -/
theorem simpleOppositeExactPairing_coevaluation_of_iso_unit
    {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)] (u : X ≅ 𝟙_ C) :
    @ExactPairing.coevaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) =
      (λ_ (𝟙_ C)).inv ≫ ((rightDualIsoUnitOfIso u).inv ⊗ₘ u.inv) := by
  symm
  rw [eq_simpleOppositeExactPairing_coevaluation_iff k, Category.assoc, tensorHom_def',
    Category.assoc, rightDualIsoUnitOfIso_inv_whiskerRight_evaluation, ← Category.assoc,
    ← leftUnitor_inv_naturality, Category.assoc, Iso.inv_hom_id_assoc, u.inv_hom_id]

include k in
/-- When `X` is a split simple object equipped with an isomorphism `u : X ≅ 𝟙_ C`, the evaluation
of `TauCeti.simpleOppositeExactPairing X` is `u.hom ⊗ₘ (rightDualIsoUnitOfIso u).hom` followed by
`(λ_ (𝟙_ C)).hom`. -/
theorem simpleOppositeExactPairing_evaluation_of_iso_unit
    {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)] (u : X ≅ 𝟙_ C) :
    @ExactPairing.evaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) =
      (u.hom ⊗ₘ (rightDualIsoUnitOfIso u).hom) ≫ (λ_ (𝟙_ C)).hom := by
  let _ : ExactPairing Xᘁ X := simpleOppositeExactPairing X
  apply (tensorLeftHomEquiv Xᘁ Xᘁ X (𝟙_ C)).injective
  have hlhs : tensorLeftHomEquiv Xᘁ Xᘁ X (𝟙_ C) (ε_ Xᘁ X) = (ρ_ Xᘁ).inv := by
    dsimp only [tensorLeftHomEquiv, Equiv.coe_fn_mk]
    rw [ExactPairing.evaluation_coevaluation, Iso.inv_hom_id_assoc]
  rw [hlhs]
  symm
  dsimp only [tensorLeftHomEquiv, Equiv.coe_fn_mk]
  have hcoev : η_ Xᘁ X = (λ_ (𝟙_ C)).inv ≫ ((rightDualIsoUnitOfIso u).inv ⊗ₘ u.inv) :=
    simpleOppositeExactPairing_coevaluation_of_iso_unit k u
  rw [hcoev]
  simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp]
  calc _ = 𝟙 (Xᘁ : C) ⊗≫ (rightDualIsoUnitOfIso u).inv ▷ 𝟙_ C ▷ (Xᘁ : C) ⊗≫
            ((Xᘁ : C) ◁ (u.inv ▷ (Xᘁ : C)) ≫ (Xᘁ : C) ◁ (u.hom ▷ (Xᘁ : C))) ⊗≫
            (Xᘁ : C) ◁ 𝟙_ C ◁ (rightDualIsoUnitOfIso u).hom ⊗≫ 𝟙 ((Xᘁ : C) ⊗ 𝟙_ C) := by
          monoidal
    _ = 𝟙 (Xᘁ : C) ⊗≫ ((rightDualIsoUnitOfIso u).inv ▷ (Xᘁ : C) ≫
          (Xᘁ : C) ◁ (rightDualIsoUnitOfIso u).hom) ⊗≫ 𝟙 ((Xᘁ : C) ⊗ 𝟙_ C) := by
          rw [← whiskerLeft_comp, ← comp_whiskerRight, u.inv_hom_id, id_whiskerRight,
            whiskerLeft_id]
          monoidal
    _ = 𝟙 (Xᘁ : C) ⊗≫ (𝟙_ C ◁ (rightDualIsoUnitOfIso u).hom ≫
          (rightDualIsoUnitOfIso u).inv ▷ 𝟙_ C) ⊗≫ 𝟙 ((Xᘁ : C) ⊗ 𝟙_ C) := by
          rw [← whisker_exchange]
    _ = 𝟙 (Xᘁ : C) ⊗≫ (((rightDualIsoUnitOfIso u).hom ≫
          (rightDualIsoUnitOfIso u).inv) ▷ 𝟙_ C) ⊗≫ 𝟙 ((Xᘁ : C) ⊗ 𝟙_ C) := by monoidal
    _ = _ := by
          rw [Iso.hom_inv_id, id_whiskerRight]
          monoidal

end Uniqueness

end TauCeti

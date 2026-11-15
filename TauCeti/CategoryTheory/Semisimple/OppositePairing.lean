/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.Simple
public import TauCeti.CategoryTheory.Monoidal.Rigid.SquaredNorm
public import TauCeti.CategoryTheory.Semisimple.Basic

/-!
# Opposite exact pairings of simple objects

In a rigid monoidal abelian category which is finite semisimple with simple tensor unit, every
simple object `X` has a nonzero evaluation morphism `ε_ X Xᘁ : Xᘁ ⊗ X ⟶ 𝟙_ C`. Because `𝟙_ C` is
simple, `ε_ X Xᘁ` is a split epimorphism; transposing a chosen section `𝟙_ C ⟶ Xᘁ ⊗ X` along
Frobenius reciprocity yields a nonzero morphism `Xᘁᘁ ⟶ X` between simple objects, hence an
isomorphism `TauCeti.simpleDoubleDualIso X : X ≅ Xᘁᘁ`. Transporting the canonical exact pairing of
`Xᘁ` and `Xᘁᘁ` along this isomorphism equips `X` with a chosen opposite exact pairing
`TauCeti.simpleOppositeExactPairing X : ExactPairing Xᘁ X` whose coevaluation `𝟙_ C ⟶ Xᘁ ⊗ X` is
a section of `ε_ X Xᘁ`. Because the second factor of `TauCeti.squaredNorm (simpleDoubleDualIso X)`
is this normalized composite `𝟙 (𝟙_ C)`, the squared norm of `simpleDoubleDualIso X` equals
`η_ X Xᘁ` followed by the evaluation of `simpleOppositeExactPairing X`.

Neither a pivotal structure nor a coefficient field is required to construct this pairing, and when
`X` is equipped with an isomorphism `u : X ≅ 𝟙_ C` the evaluation `ε_ X Xᘁ` is itself an
isomorphism, so the opposite pairing is already unique and agrees with the unit pairing transported
along `u` and `u.rightAdjointMate.symm` without any linearity hypotheses. Over an algebraically
closed field `k` over which `C` is `k`-linear with `X ⟶ X` finite-dimensional, Schur's lemma makes
`𝟙_ C ⟶ Xᘁ ⊗ X` one-dimensional, so the section `𝟙_ C ⟶ Xᘁ ⊗ X` of `ε_ X Xᘁ` — and therefore
`simpleDoubleDualIso X` and `simpleOppositeExactPairing X` — is canonical and unique. Both
algebraic-closedness and finite-dimensionality are necessary for uniqueness: when `End(X)` is a
division algebra strictly larger than `k`, `𝟙_ C ⟶ Xᘁ ⊗ X` has dimension greater than `1` and
`ε_ X Xᘁ` admits an affine space of sections. Under uniqueness, `simpleDoubleDualIso` commutes with
every isomorphism between simple objects.

## Main declarations

* `TauCeti.simpleDoubleDualIso`: a chosen isomorphism `X ≅ Xᘁᘁ` for a simple object `X`, normalized
  by `TauCeti.coevaluation_comp_whiskerLeft_simpleDoubleDualIso_inv_comp_evaluation` so that the
  transported coevaluation splits `ε_ X Xᘁ`;
* `TauCeti.simpleOppositeExactPairing`: a chosen opposite exact pairing `ExactPairing Xᘁ X` of a
  simple object `X` (canonical and unique for split simples over an algebraically closed field),
  with evaluation and coevaluation formulas `TauCeti.simpleOppositeExactPairing_evaluation` and
  `TauCeti.simpleOppositeExactPairing_coevaluation`, normalized by
  `TauCeti.simpleOppositeExactPairing_coevaluation_comp_evaluation`;
* `TauCeti.squaredNorm_simpleDoubleDualIso`: the squared norm of `simpleDoubleDualIso X` equals
  `η_ X Xᘁ` followed by the evaluation of `simpleOppositeExactPairing X`;
* `TauCeti.simpleOppositeExactPairing_coevaluation_of_iso_unit` and
  `TauCeti.simpleOppositeExactPairing_evaluation_of_iso_unit`: explicit field-free formulas when
  `X ≅ 𝟙_ C`;
* `TauCeti.eq_simpleOppositeExactPairing_coevaluation_iff` and
  `TauCeti.eq_simpleDoubleDualIso_inv_iff`: uniqueness of the normalized coevaluation and double
  dual isomorphism for a split simple object over an algebraically closed field;
* `TauCeti.simpleDoubleDualIso_inv_conj`, `TauCeti.hom_comp_simpleDoubleDualIso_hom`,
  `TauCeti.simpleOppositeExactPairing_coevaluation_congr` and
  `TauCeti.simpleOppositeExactPairing_evaluation_congr`: compatibility with an isomorphism `X ≅ Y`
  of split simple objects.

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

/-- Auxiliary section `𝟙_ C ⟶ Xᘁ ⊗ X` of `ε_ X Xᘁ` for a simple object `X`. -/
private def simpleEvalSection (X : C) [Simple X] : 𝟙_ C ⟶ Xᘁ ⊗ X :=
  have := isSplitEpi_evaluation X
  section_ (ε_ X Xᘁ)

@[reassoc]
private theorem simpleEvalSection_comp_evaluation (X : C) [Simple X] :
    simpleEvalSection X ≫ ε_ X Xᘁ = 𝟙 (𝟙_ C) := by
  have := isSplitEpi_evaluation X
  exact IsSplitEpi.id (ε_ X Xᘁ)

/-- Auxiliary morphism `Xᘁᘁ ⟶ X` obtained by transposing `simpleEvalSection X`. -/
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

private theorem simpleDoubleDualIso_inv (X : C) [Simple X] :
    (simpleDoubleDualIso X).inv = simpleDoubleDualInvAux X :=
  rfl

/-- `(simpleDoubleDualIso X).inv` carries `η_ Xᘁ Xᘁᘁ` to a section of `ε_ X Xᘁ`. -/
@[reassoc (attr := simp)]
theorem coevaluation_comp_whiskerLeft_simpleDoubleDualIso_inv_comp_evaluation (X : C) [Simple X] :
    η_ (Xᘁ : C) ((Xᘁ : C)ᘁ : C) ≫ Xᘁ ◁ (simpleDoubleDualIso X).inv ≫ ε_ X Xᘁ = 𝟙 (𝟙_ C) := by
  rw [← Category.assoc, simpleDoubleDualIso_inv,
    coevaluation_comp_whiskerLeft_simpleDoubleDualInvAux, simpleEvalSection_comp_evaluation]

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
  have : IsIso s := by
    dsimp only [s]
    rw [← Iso.rightAdjointMate_hom u]
    infer_instance
  have hs : s ≫ ε_ X Xᘁ = 𝟙 (𝟙_ C) := by
    dsimp only [s]
    have hmate : (u.hom)ᘁ ▷ X ≫ ε_ X Xᘁ = (λ_ X).hom ≫ u.hom := by
      rw [rightAdjointMate_comp_evaluation]
      change 𝟙_ C ◁ u.hom ≫ ε_ (𝟙_ C) (𝟙_ C) = _
      rw [ExactPairing.unit_evaluation, ← unitors_equal, leftUnitor_naturality]
    rw [Category.assoc, tensorHom_def', Category.assoc, hmate, ← Category.assoc,
      ← leftUnitor_inv_naturality, Category.assoc, Iso.inv_hom_id_assoc, u.inv_hom_id]
  have hεs : ε_ X Xᘁ ≫ s = 𝟙 (Xᘁ ⊗ X) := by
    rw [← cancel_epi s, reassoc_of% hs, Category.comp_id]
  calc @ExactPairing.coevaluation C _ _ Xᘁ X (simpleOppositeExactPairing X)
      = @ExactPairing.coevaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) ≫ (ε_ X Xᘁ ≫ s) := by
        rw [hεs, Category.comp_id]
    _ = s := by
        rw [← Category.assoc, simpleOppositeExactPairing_coevaluation_comp_evaluation,
          Category.id_comp]

/-- When a simple object `X` is equipped with an isomorphism `u : X ≅ 𝟙_ C`, the evaluation of
`TauCeti.simpleOppositeExactPairing X` is `u.hom ⊗ₘ (u.inv)ᘁ` followed by `(λ_ (𝟙_ C)).hom`,
with no linearity or field hypotheses required. -/
theorem simpleOppositeExactPairing_evaluation_of_iso_unit {X : C} [Simple X] (u : X ≅ 𝟙_ C) :
    @ExactPairing.evaluation C _ _ Xᘁ X (simpleOppositeExactPairing X) =
      (u.hom ⊗ₘ (u.inv)ᘁ) ≫ (λ_ (𝟙_ C)).hom := by
  let v : Xᘁ ≅ 𝟙_ C := u.rightAdjointMate.symm
  let p₁ : ExactPairing Xᘁ X := simpleOppositeExactPairing X
  let p₂ : ExactPairing Xᘁ X := exactPairingCongr v u
  have hcoev : @ExactPairing.coevaluation C _ _ Xᘁ X p₁ =
      @ExactPairing.coevaluation C _ _ Xᘁ X p₂ := by
    rw [simpleOppositeExactPairing_coevaluation_of_iso_unit u, exactPairingCongr_coevaluation,
      ExactPairing.unit_coevaluation, ← tensorHom_def', unitors_inv_equal]
    simp [v]
  have hiso : (rightDualIso p₁ p₂).hom = 𝟙 X := by
    have h := ExactPairing.coevaluation_comp_rightMate p₂ p₁ (𝟙 (Xᘁ : C))
    rw [← ExactPairing.rightDualIso_hom, id_whiskerRight, Category.comp_id, ← hcoev] at h
    have h' : @ExactPairing.coevaluation C _ _ Xᘁ X p₁ ≫ Xᘁ ◁ (rightDualIso p₁ p₂).hom =
        @ExactPairing.coevaluation C _ _ Xᘁ X p₁ ≫ Xᘁ ◁ 𝟙 X := by
      simpa using h
    let _ : ExactPairing Xᘁ X := p₁
    have h1 := congrArg (tensorLeftHomEquiv (𝟙_ C) Xᘁ X X).symm h'
    rw [tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft,
      tensorLeftHomEquiv_symm_coevaluation_comp_whiskerLeft] at h1
    exact (cancel_epi (ρ_ X).hom).1 h1
  have hev := ExactPairing.rightDualIso_hom_whiskerRight_evaluation p₁ p₂
  rw [hiso, id_whiskerRight, Category.id_comp] at hev
  rw [← hev, exactPairingCongr_evaluation, ExactPairing.unit_evaluation, ← tensorHom_def'_assoc,
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
theorem hom_comp_simpleDoubleDualIso_hom {X Y : C} [Simple X] [Simple Y]
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
    hom_comp_simpleDoubleDualIso_hom k u, comp_whiskerRight_assoc,
    rightAdjointMate_comp_evaluation, whisker_exchange_assoc, ← whiskerLeft_comp_assoc,
    ← comp_rightAdjointMate, u.hom_inv_id, rightAdjointMate_id, whiskerLeft_id, Category.id_comp]

end Uniqueness

end TauCeti

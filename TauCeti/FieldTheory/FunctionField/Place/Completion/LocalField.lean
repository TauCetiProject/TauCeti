/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finiteness
public import TauCeti.FieldTheory.FunctionField.Place.Completion.Basic
public import TauCeti.NumberTheory.LocalField.Uniformizer
public import TauCeti.Topology.Algebra.Valued.WithVal
public import TauCeti.Topology.Algebra.ValuativeRel.Completion
import TauCeti.RingTheory.Valuation.Surjective
import TauCeti.Topology.Algebra.Valued.DiscreteValuationRing

/-!
# The completion at a place with finite residue field is a local field

Let `P` be a place of `F/k` whose residue field is finite, for instance any place of an algebraic
function field over a finite field. Its completion `F_P = P.Completion` carries Mathlib's valuative
relation, induced by the valuation of `F`, and its valuative topology. This file shows that `F_P` is
then a nonarchimedean local field, so the local theory stated for such fields (local class field
theory, the Artin-defined norm-residue symbol, unit filtrations) applies to every completion of a
global function field.

It also reads the invariants of the valuative relation on `F_P` back in terms of `P`. Its ring of
integers is the valuation ring of the completed place, its residue field is the residue field of
`P`, of cardinality `q ^ deg P` over a field with `q` elements, and its normalized valuation is the
order of the completed place. In particular a function of order one at `P` is a uniformizer of
`F_P`.

The valuative relation is the one Mathlib puts on every completion of a field at a valuation; the
completed valuation `Valued.v` is compatible with it by `Valuation.Completion.compatible_valued`.
Local compactness comes from `Valued.integer.locallyCompactSpace_of_finite_residueField`, which
also gives it for the adic completions of Dedekind domains in
`TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel`.

## Main results

* `TauCeti.Place.instIsNonarchimedeanLocalFieldCompletion`: the completion at a place with finite
  residue field is a nonarchimedean local field.
* `TauCeti.Place.integer_completion_eq`: the ring of integers of the valuative relation on `F_P`
  is the valuation ring of the completed place.
* `TauCeti.Place.valuativeResidueFieldEquiv`: the residue field of the valuative relation on `F_P`
  is the residue field of `P`, with its value on residues (`valuativeResidueFieldEquiv_residue`);
  `natCard_valuativeResidueField` computes its cardinality.
* `TauCeti.Place.normalizedValuation_completion`: the normalized valuation of `F_P` is the order of
  the completed place; `normalizedValuation_unitsMap_completionEmbedding` reads it on `Fˣ` as
  `ord_P`, and `isUniformizer_unitsMap_completionEmbedding_iff` characterizes uniformizers.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section I.7.
* J.-P. Serre, *Local Fields*, Chapter II, §1.
-/

public section

noncomputable section

open ValuativeRel
open scoped WithZero

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F)

/-- The valuative relation of `F` with the valuation of a place is nontrivial. Through
`UniformSpace.Completion.isNontrivial` this makes the valuative relation of the completion
`P.Completion` nontrivial. -/
instance instIsNontrivialWithVal : ValuativeRel.IsNontrivial (WithVal P.valuation) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial (WithVal.valuation P.valuation)).mpr <|
    Valuation.isNontrivial_of_surjective fun γ ↦ by
      obtain ⟨x, hx⟩ := P.valuation_surjective γ
      exact ⟨WithVal.toVal P.valuation x, (WithVal.valuation_toVal P.valuation x).trans hx⟩

/-- **The ring of integers of the completion.** The ring of integers of the valuative relation on
`P.Completion` is the valuation ring of the completed place. -/
theorem integer_completion_eq : 𝒪[P.Completion] = P.completionPlace.integers.toSubring := by
  ext x
  rw [ValuationSubring.mem_toSubring, mem_integers_iff, completionPlace_valuation,
    Valuation.mem_integer_iff]
  exact (Valuation.vle_one_iff (ValuativeRel.valuation P.Completion)).symm.trans
    (Valuation.vle_one_iff (Valued.v : Valuation P.Completion ℤᵐ⁰))

/-- The ring of integers of the valuative relation on `P.Completion` is the valuation ring of the
completed place, as a ring isomorphism. -/
def integerCompletionEquiv : 𝒪[P.Completion] ≃+* P.completionPlace.integers :=
  RingEquiv.subringCongr P.integer_completion_eq

@[simp]
theorem coe_integerCompletionEquiv (x : 𝒪[P.Completion]) :
    (P.integerCompletionEquiv x : P.Completion) = x := (rfl)

@[simp]
theorem coe_integerCompletionEquiv_symm (x : P.completionPlace.integers) :
    (P.integerCompletionEquiv.symm x : P.Completion) = x := (rfl)

/-- **The residue field of the completion.** The residue field of the valuative relation on
`P.Completion` is the residue field of `P`. -/
def valuativeResidueFieldEquiv : 𝓀[P.Completion] ≃+* P.ResidueField :=
  (IsLocalRing.ResidueField.mapEquiv P.integerCompletionEquiv).trans
    P.residueFieldEquivCompletion.symm.toRingEquiv

/-- The residue-field isomorphism on the residue of an integer `x` of `P.Completion`: it is the
residue of `x` in the valuation ring of the completed place, read in the residue field of `P`. -/
@[simp]
theorem valuativeResidueFieldEquiv_residue (x : 𝒪[P.Completion]) :
    P.valuativeResidueFieldEquiv (IsLocalRing.residue 𝒪[P.Completion] x) =
      P.residueFieldEquivCompletion.symm
        (IsLocalRing.residue P.completionPlace.integers (P.integerCompletionEquiv x)) := by
  simp [valuativeResidueFieldEquiv]

/-- The residue-field isomorphism sends the residue of the image of a function regular at `P` to
its value at `P`. -/
theorem valuativeResidueFieldEquiv_residue_completionIntegersEmbedding (x : P.integers) :
    P.valuativeResidueFieldEquiv (IsLocalRing.residue 𝒪[P.Completion]
        (P.integerCompletionEquiv.symm (P.completionIntegersEmbedding x))) =
      IsLocalRing.residue P.integers x := by
  rw [valuativeResidueFieldEquiv_residue, RingEquiv.apply_symm_apply,
    residueFieldEquivCompletion_symm_residue_completionIntegersEmbedding]

/-- **The completion at a place with finite residue field is a nonarchimedean local field.** -/
instance instIsNonarchimedeanLocalFieldCompletion [Finite P.ResidueField] :
    IsNonarchimedeanLocalField P.Completion := by
  -- The completed valuation is discrete of rank one.
  have : (Valued.v : Valuation P.Completion ℤᵐ⁰).IsRankOneDiscrete :=
    P.completionPlace_valuation_eq ▸ inferInstance
  -- The ring of integers of `Valued.v` is the valuation ring of the completed place, whose
  -- residue field is that of `P`.
  let e : Valued.integer P.Completion ≃+* P.completionPlace.integers :=
    RingEquiv.subringCongr <| by
      ext x
      simp [Valued.integer, Valuation.mem_integer_iff]
  have : Finite (IsLocalRing.ResidueField (Valued.integer P.Completion)) :=
    Finite.of_equiv _ (P.residueFieldEquivCompletion.toRingEquiv.trans
      (IsLocalRing.ResidueField.mapEquiv e.symm)).toEquiv
  have : LocallyCompactSpace P.Completion :=
    Valued.integer.locallyCompactSpace_of_finite_residueField
  exact ⟨⟩

/-- **The residue cardinality of the completion.** If the residue field of `P` is finite-dimensional
over the constants `k`, the residue field of `P.Completion` has `(Nat.card k) ^ deg P` elements; for
a finite field `k` with `q` elements this is `q ^ deg P`. -/
theorem natCard_valuativeResidueField [Module.Finite k P.ResidueField] :
    Nat.card 𝓀[P.Completion] = Nat.card k ^ P.degree := by
  rw [Nat.card_congr P.valuativeResidueFieldEquiv.toEquiv]
  rcases finite_or_infinite k with hk | hk
  · have := Module.finite_of_finite k (M := P.ResidueField)
    have := Fintype.ofFinite k
    have := Fintype.ofFinite P.ResidueField
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := k),
      degree_eq_finrank]
  · -- Over infinite constants both sides vanish, as `deg P ≥ 1`.
    have := Infinite.of_injective _ (algebraMap k P.ResidueField).injective
    rw [Nat.card_eq_zero_of_infinite, Nat.card_eq_zero_of_infinite,
      zero_pow (Nat.one_le_iff_ne_zero.mp (one_le_degree P))]

variable [Finite P.ResidueField]

/-- The zero-preserving normalized valuation of `P.Completion` is the inverse of its completed
valuation `Valued.v`. -/
@[simp]
theorem normalizedValuationWithZero_completion (x : P.Completion) :
    normalizedValuationWithZero P.Completion x = (Valued.v x)⁻¹ :=
  Valuation.normalizedValuationWithZero_eq_inv_of_surjective _
    (P.completionPlace_valuation_eq ▸ P.completionPlace.valuation_surjective) x

/-- **The normalized valuation of the completion is the order of the completed place.** -/
theorem normalizedValuation_completion (x : P.Completionˣ) :
    normalizedValuation P.Completion x = Multiplicative.ofAdd (P.completionPlace.ord x) := by
  rw [← WithZero.coe_inj, ← normalizedValuationWithZero_coe,
    normalizedValuationWithZero_completion, ← completionPlace_valuation,
    P.completionPlace.valuation_eq_exp_neg_ord x.ne_zero, ← WithZero.exp_neg, neg_neg,
    WithZero.exp_eq_coe_ofAdd]

/-- **The normalized valuation on functions.** The normalized valuation of the local field
`P.Completion` at the image of a nonzero function is its order at `P`. -/
@[simp]
theorem normalizedValuation_unitsMap_completionEmbedding (a : Fˣ) :
    normalizedValuation P.Completion (Units.map (P.completionEmbedding : F →* P.Completion) a) =
      Multiplicative.ofAdd (P.ord a) := by
  rw [normalizedValuation_completion, Units.coe_map, MonoidHom.coe_ofClass, ord_completionEmbedding]

/-- **Uniformizers from functions.** The image of a nonzero function is a uniformizer of the local
field `P.Completion` exactly when the function has order one at `P`. -/
theorem isUniformizer_unitsMap_completionEmbedding_iff (a : Fˣ) :
    IsUniformizer P.Completion (Units.map (P.completionEmbedding : F →* P.Completion) a) ↔
      P.ord a = 1 := by
  rw [isUniformizer_def, normalizedValuation_unitsMap_completionEmbedding,
    Multiplicative.ofAdd.injective.eq_iff]

end TauCeti.Place

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.DedekindZeta
public import TauCeti.NumberTheory.LFunctions.Data.Series
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Conductor
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Inverse
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
import TauCeti.NumberTheory.LFunctions.DedekindZeta.TrivialZeros

/-!
# The analytic card of a Grossencharacter and its completions

For a presentation `χ : Grossencharacter K 𝔪` of an algebraic Hecke character with unitary part
`χ_u` and ideal-side shift `σ` (`χ = χ_u N ^ σ` on ideals), the analytic card
`grossencharacterData χ` is the card of the **unitary part at the conductor**. Its fields are
pinned to the Hecke character:

* the coefficients are the norm-regrouped primitive unitary weight
  `HeckeCharacter.unitaryIdealWeight`, the ideal character of `χ_u` on the ideals prime to the
  finite conductor `𝔣₀`, extended by zero;
* the conductor is `|d_K| N(𝔣₀)`;
* there is one real gamma shift at each real place, the parity there of the archimedean
  restriction, and one complex gamma shift `|n_τ - n_τ'| / 2` at each complex place, for the
  algebraic infinity type `n`, an embedding `τ` of the place and its conjugate `τ'`;
* the polar divisor consists of simple poles at `0` and `1` exactly when `χ_u` is trivial.

The completed function and root number are those of `AnalyticLFunctionData.ofSeries`: the
canonical continuation of `N ^ (s / 2) γ(s) L(χ_u, s)` from `Re s > 1` and `Λ(2) / conj Λ(-1)`.
They define the unitary completion `Grossencharacter.unitaryCompletion` and the root number
`Grossencharacter.rootNumber`. The full completion `Grossencharacter.completed` recentres the
unitary completion at the shift, `Λ(χ, s) = Λ(χ_u, s - σ)`. When `σ ≠ 0` it is not the completed
function of an analytic card: its critical line is `Re s = 1 / 2 + σ`.

The card, the two completions and the root number depend on the presentation only through its
Hecke character. The card of the inverse presentation is the dual card, so the root number of the
inverse is the conjugate root number. When the unitary part is trivial (the trivial character,
the norm powers `N ^ m`), the card agrees with `dedekindZetaData K` off the coefficient at zero,
so it has Dirichlet agreement, meromorphic continuation and its functional equation, and the full
completion of `N ^ m` is `s ↦ Λ_K(s - m)`. In general, the continuation and the functional
equation come from the theta kernel of the presentation.

## Main definitions

* `TauCeti.LFunctions.grossencharacterData`: the analytic card of a presentation.
* `TauCeti.LFunctions.Grossencharacter.unitaryCompletion`,
  `TauCeti.LFunctions.Grossencharacter.rootNumber`: its completed function and root number.
* `TauCeti.LFunctions.Grossencharacter.completed`: the full completion `Λ(χ, s)`.

## Main results

* `TauCeti.LFunctions.grossencharacterData_conductor`: the conductor is `|d_K|` times the norm
  of the finite part of the presentation conductor.
* `TauCeti.LFunctions.grossencharacterData_congr` and its consequences for the completions: the
  card is a function of the Hecke character.
* `TauCeti.LFunctions.grossencharacterData_degree`: the card has degree `[K : ℚ]`.
* `TauCeti.LFunctions.grossencharacterData_hasAverageCoefficientGrowth`.
* `TauCeti.LFunctions.grossencharacterData_inverse`: the card of the inverse presentation is the
  dual card; `TauCeti.LFunctions.Grossencharacter.rootNumber_inverse`.
* `TauCeti.LFunctions.grossencharacterData_eqOffZero_dedekindZetaData`: a trivial unitary part
  gives the Dedekind zeta card; `TauCeti.LFunctions.Grossencharacter.completed_normPow`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §8.
* E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen
  (Zweite Mitteilung)*, Math. Z. 6 (1920), §6.
-/

public section
noncomputable section

open Complex NumberField NumberField.InfinitePlace
open scoped ComplexConjugate

namespace TauCeti.LFunctions

open GlobalNumberFields AnalyticLFunctionData

variable {K : Type*} [Field K] [NumberField K] {𝔪 𝔫 : Modulus K}

/-- The conductor `|d_K| N(𝔣₀)` of the card of a Hecke character with finite conductor `𝔣₀`. -/
private def cardConductor (φ : HeckeCharacter K) : ℕ+ :=
  ⟨(discr K).natAbs * Ideal.absNorm φ.finiteConductor,
    Nat.mul_pos (Int.natAbs_pos.mpr (discr_ne_zero K))
      (Nat.pos_of_ne_zero fun h ↦ φ.finiteConductor_ne_bot (Ideal.absNorm_eq_zero_iff.mp h))⟩

open scoped Classical in
/-- **The analytic card of a Grossencharacter**: the card of the unitary part `χ_u` of the
presented Hecke character at its conductor. Its coefficients are the norm-regrouped primitive
unitary weight, its conductor is `|d_K| N(𝔣₀)`, it has one real gamma shift at each real place,
the parity there of the archimedean restriction, and one complex gamma shift at each complex
place, half the absolute value of the angular frequency there; it records simple poles at `0` and
`1` exactly when `χ_u` is trivial. The completed function and the root number are those of
`AnalyticLFunctionData.ofSeries`. -/
def grossencharacterData (χ : Grossencharacter K 𝔪) : AnalyticLFunctionData :=
  ofSeries (normCoeff K χ.toHeckeCharacter.unitaryIdealWeight.toIdealArithmeticFunction)
    (cardConductor χ.toHeckeCharacter)
    (Finset.univ.val.map fun w ↦ ((χ.toHeckeCharacter.infinityType.realParity w).val : ℂ))
    (Finset.univ.val.map fun w ↦
      ((|χ.toHeckeCharacter.infinityType.complexAngularFrequency w| : ℤ) : ℂ) / 2)
    (if χ.toHeckeCharacter.unitaryPart = 1 then Finsupp.single 0 1 + Finsupp.single 1 1 else 0)

variable (χ : Grossencharacter K 𝔪)

/-- The coefficients of the card are the norm-regrouped primitive unitary weight. -/
@[simp]
theorem grossencharacterData_coeff :
    (grossencharacterData χ).coeff =
      normCoeff K χ.toHeckeCharacter.unitaryIdealWeight.toIdealArithmeticFunction := by
  rw [grossencharacterData, ofSeries_coeff]

/-- The coefficient at zero, which `LSeries` does not read, is `0`. -/
@[simp]
theorem grossencharacterData_coeff_zero : (grossencharacterData χ).coeff 0 = 0 := by
  simp

/-- The first coefficient is `1`, the weight of the unit ideal. -/
@[simp]
theorem grossencharacterData_coeff_one : (grossencharacterData χ).coeff 1 = 1 := by
  simp

/-- **The conductor of the card** is `|d_K|` times the norm of the finite part of the
presentation conductor `χ.conductor`, which is the finite conductor `𝔣₀` of the Hecke character
(`Grossencharacter.finitePart_conductor`). -/
@[simp]
theorem grossencharacterData_conductor :
    ((grossencharacterData χ).conductor : ℕ) =
      (discr K).natAbs * Ideal.absNorm χ.conductor.finitePart := by
  rw [grossencharacterData, ofSeries_conductor, Grossencharacter.finitePart_conductor]
  rfl

open scoped Classical in
/-- There is one real gamma shift at each real place: the parity there of the archimedean
restriction of the Hecke character, not the parity of its algebraic exponent. -/
theorem grossencharacterData_gammaR :
    (grossencharacterData χ).gammaR =
      Finset.univ.val.map fun w ↦ ((χ.toHeckeCharacter.infinityType.realParity w).val : ℂ) := by
  rw [grossencharacterData, ofSeries_gammaR]

open scoped Classical in
/-- There is one complex gamma shift at each complex place: half the absolute value of the
angular frequency there of the archimedean restriction. -/
theorem grossencharacterData_gammaC :
    (grossencharacterData χ).gammaC =
      Finset.univ.val.map fun w ↦
        ((|χ.toHeckeCharacter.infinityType.complexAngularFrequency w| : ℤ) : ℂ) / 2 := by
  rw [grossencharacterData, ofSeries_gammaC]

open scoped Classical in
/-- The complex gamma shift at a complex place `w`, read off the algebraic infinity type `n` of
the presentation: `|n_τ - n_τ'| / 2` for the embedding `τ` of `w` and its conjugate `τ'`. -/
theorem grossencharacterData_gammaC_eq_infinityType :
    (grossencharacterData χ).gammaC =
      Finset.univ.val.map fun w : {w : InfinitePlace K // w.IsComplex} ↦
        ((|χ.infinityType w.val.embedding -
          χ.infinityType (ComplexEmbedding.conjugate w.val.embedding)| : ℤ) : ℂ) / 2 := by
  obtain ⟨-, -, hk⟩ := (ContinuousInfinityType.agreesOnIdentityComponent_iff _ _).mp
    χ.agreesOnIdentityComponent
  simp [grossencharacterData_gammaC, hk]

open scoped Classical in
/-- The card records simple poles at `0` and `1` exactly when the unitary part is trivial. -/
theorem grossencharacterData_polarOrder :
    (grossencharacterData χ).polarOrder =
      if χ.toHeckeCharacter.unitaryPart = 1 then Finsupp.single 0 1 + Finsupp.single 1 1
      else 0 := by
  simp [grossencharacterData]

/-- A nontrivial unitary part leaves the card without poles. -/
theorem grossencharacterData_polarOrder_eq_zero (h : χ.toHeckeCharacter.unitaryPart ≠ 1) :
    (grossencharacterData χ).polarOrder = 0 := by
  classical
  rw [grossencharacterData_polarOrder, ite_eq_right h]

/-- The completed function of the card is the canonical continuation of the completed series. -/
theorem grossencharacterData_completed :
    (grossencharacterData χ).completed = TauCeti.meromorphicContinuation 1 fun s ↦
      (((grossencharacterData χ).conductor : ℕ) : ℂ) ^ (s / 2) *
        (grossencharacterData χ).gammaFactor s * LSeries (grossencharacterData χ).coeff s := by
  rw [grossencharacterData, ofSeries_completed]
  simp

/-- The root number of the card is extracted from its completed function as
`Λ(2) / conj Λ(-1)`. -/
theorem grossencharacterData_rootNumber :
    (grossencharacterData χ).rootNumber =
      (grossencharacterData χ).completed 2 / conj ((grossencharacterData χ).completed (-1)) := by
  rw [grossencharacterData, ofSeries_rootNumber]

/-- **The card has degree `[K : ℚ]`**, from its `r₁` real and `r₂` complex gamma factors. -/
@[simp]
theorem grossencharacterData_degree : (grossencharacterData χ).degree = Module.finrank ℚ K := by
  simpa [degree_def, grossencharacterData_gammaR, grossencharacterData_gammaC] using
    card_add_two_mul_card_eq_rank K

/-- The coefficients of the card are bounded by the ideal counts of the Dedekind zeta function,
so the card has average coefficient growth. -/
theorem grossencharacterData_hasAverageCoefficientGrowth :
    (grossencharacterData χ).HasAverageCoefficientGrowth :=
  (dedekindZetaData_hasAverageCoefficientGrowth K).of_norm_coeff_le_norm_coeff fun n hn ↦ by
    have h := UnitaryIdealWeight.norm_normCoeff_le_norm_normCoeff_one K
      χ.toHeckeCharacter.unitaryIdealWeight n
    rwa [normCoeff_one_apply, ite_eq_right hn, ← dedekindZetaData_coeff,
      ← grossencharacterData_coeff] at h

/-- **The card is a function of the Hecke character.** Two presentations of the same Hecke
character, even at different moduli, have the same card. -/
theorem grossencharacterData_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) :
    grossencharacterData χ = grossencharacterData ψ := by
  rw [grossencharacterData, grossencharacterData, h]

/-- **The card of the inverse presentation is the dual card.** The inverse character has the
conjugate primitive weight, the same finite conductor, the same parities and the same absolute
angular frequencies, and canonical continuation commutes with conjugation
(`AnalyticLFunctionData.ofSeries_dual`). -/
theorem grossencharacterData_inverse :
    grossencharacterData χ.inverse = (grossencharacterData χ).dual := by
  classical
  rw [grossencharacterData, grossencharacterData, ofSeries_dual]
  congr 1
  · funext n
    simp only [Grossencharacter.toHeckeCharacter_inverse, HeckeCharacter.unitaryIdealWeight_inv,
      UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, UnitaryIdealWeight.val_conj,
      MultiplicativeIdealWeight.toIdealArithmeticFunction_conj, normCoeff_star_apply,
      Complex.star_def]
  · exact PNat.eq (by simp [cardConductor, HeckeCharacter.finiteConductor_inv])
  · simp only [Multiset.map_map, Function.comp_def, Grossencharacter.toHeckeCharacter_inverse,
      HeckeCharacter.infinityType_inv, ContinuousInfinityType.neg_realParity, Pi.neg_apply,
      ZMod.neg_eq_self_mod_two, map_natCast]
  · simp only [Multiset.map_map, Function.comp_def, Grossencharacter.toHeckeCharacter_inverse,
      HeckeCharacter.infinityType_inv, ContinuousInfinityType.neg_complexAngularFrequency,
      Pi.neg_apply, abs_neg, map_div₀, map_intCast, map_ofNat]
  · simp only [Grossencharacter.toHeckeCharacter_inverse, HeckeCharacter.unitaryPart_inv,
      inv_eq_one]
    split_ifs
    · simp [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    · simp

/-! ### Trivial unitary part -/

/-- The completed Dedekind zeta function does not vanish at `2`. -/
private theorem completedDedekindZeta_two_ne_zero : completedDedekindZeta K 2 ≠ 0 := by
  have h := completedDedekindZeta_ne_zero_of_re_neg K (s := -1) (by norm_num)
  rwa [← completedDedekindZeta_one_sub, sub_neg_eq_add, one_add_one_eq_two] at h

/-- **A trivial unitary part gives the Dedekind zeta card.** If `χ_u = 1`, as for the trivial
character and the norm powers `N ^ m`, the card of `χ` agrees with `dedekindZetaData K` off the
coefficient at zero: conductor `|d_K|`, gamma shifts zero, simple poles at `0` and `1`, completed
function `completedDedekindZeta K` and root number `1`. -/
theorem grossencharacterData_eqOffZero_dedekindZetaData
    (h : χ.toHeckeCharacter.unitaryPart = 1) :
    (grossencharacterData χ).EqOffZero (dedekindZetaData K) := by
  classical
  -- The infinity type of the unitary part, hence its parities and frequencies, vanish.
  have hinf := χ.infinityType_unitaryPart
  rw [h, HeckeCharacter.infinityType_one] at hinf
  have hpar : χ.toHeckeCharacter.infinityType.realParity = 0 :=
    (congrArg ContinuousInfinityType.realParity hinf).symm
  obtain ⟨-, -, hk⟩ := (ContinuousInfinityType.agreesOnIdentityComponent_iff _ _).mp
    χ.agreesOnIdentityComponent
  have hfreq : χ.toHeckeCharacter.infinityType.complexAngularFrequency = 0 :=
    hk.trans (congrArg ContinuousInfinityType.complexAngularFrequency hinf).symm
  have hweight : χ.toHeckeCharacter.unitaryIdealWeight = 1 := by
    rw [← HeckeCharacter.unitaryIdealWeight_unitaryPart, h, HeckeCharacter.unitaryIdealWeight_one]
  have hcond : χ.toHeckeCharacter.finiteConductor = ⊤ := by
    rw [← HeckeCharacter.finiteConductor_unitaryPart, h, HeckeCharacter.finiteConductor_one]
  -- The card is the series card of the Dedekind zeta data, up to the coefficient at zero.
  have hcard : grossencharacterData χ =
      ofSeries (normCoeff K (1 : UnitaryIdealWeight K).toIdealArithmeticFunction)
        (dedekindZetaData K).conductor (dedekindZetaData K).gammaR (dedekindZetaData K).gammaC
        (dedekindZetaData K).polarOrder := by
    rw [grossencharacterData, hweight]
    congr 1
    · exact PNat.eq (by simp [cardConductor, hcond])
    · simp [hpar, Multiset.map_const', nrRealPlaces]
    · simp [hfreq, Multiset.map_const', nrComplexPlaces]
    · simp [h]
  have hd : ofSeries (dedekindZetaData K).coeff (dedekindZetaData K).conductor
      (dedekindZetaData K).gammaR (dedekindZetaData K).gammaC (dedekindZetaData K).polarOrder =
        dedekindZetaData K :=
    ofSeries_eq (dedekindZetaData_hasDirichletAgreement K)
      (dedekindZetaData_hasFunctionalEquation K)
      (by rw [dedekindZetaData_completed]; exact meromorphicNFOn_completedDedekindZeta K)
      (by norm_num [dedekindZetaData_polarOrder, Finsupp.single_apply])
      (by rw [dedekindZetaData_completed]; exact completedDedekindZeta_two_ne_zero)
  have heq := eqOffZero_ofSeries (normCoeff K (1 : UnitaryIdealWeight K).toIdealArithmeticFunction)
    (dedekindZetaData K).conductor (dedekindZetaData K).gammaR (dedekindZetaData K).gammaC
    (dedekindZetaData K).polarOrder (b := (dedekindZetaData K).coeff) fun n hn ↦ by
      rw [normCoeff_toIdealArithmeticFunction_one_apply, ite_eq_right hn, dedekindZetaData_coeff]
  rwa [hd, ← hcard] at heq

/-- A trivial unitary part gives the card Dirichlet agreement. -/
theorem grossencharacterData_hasDirichletAgreement_of_unitaryPart_eq_one
    (h : χ.toHeckeCharacter.unitaryPart = 1) :
    (grossencharacterData χ).HasDirichletAgreement :=
  (grossencharacterData_eqOffZero_dedekindZetaData χ h).symm.hasDirichletAgreement
    (dedekindZetaData_hasDirichletAgreement K)

/-- A trivial unitary part gives the card its meromorphic continuation, with simple poles at `0`
and `1`. -/
theorem grossencharacterData_hasMeromorphicContinuation_of_unitaryPart_eq_one
    (h : χ.toHeckeCharacter.unitaryPart = 1) :
    (grossencharacterData χ).HasMeromorphicContinuation :=
  (grossencharacterData_eqOffZero_dedekindZetaData χ h).symm.hasMeromorphicContinuation
    (dedekindZetaData_hasMeromorphicContinuation K)

/-- A trivial unitary part gives the card its functional equation, with root number `1`. -/
theorem grossencharacterData_hasFunctionalEquation_of_unitaryPart_eq_one
    (h : χ.toHeckeCharacter.unitaryPart = 1) :
    (grossencharacterData χ).HasFunctionalEquation :=
  (grossencharacterData_eqOffZero_dedekindZetaData χ h).symm.hasFunctionalEquation
    (dedekindZetaData_hasFunctionalEquation K)

namespace Grossencharacter

/-! ### The completions -/

/-- **The unitary completion** `Λ(χ_u, s)`: the completed function of `grossencharacterData χ`. -/
def unitaryCompletion : ℂ → ℂ :=
  (grossencharacterData χ).completed

/-- **The root number** `W(χ)`: the root number of `grossencharacterData χ`. -/
def rootNumber : ℂ :=
  (grossencharacterData χ).rootNumber

/-- **The full completion** `Λ(χ, s) = Λ(χ_u, s - σ)`: the unitary completion recentred at the
ideal-side shift `σ`. Its conductor power is `A ^ ((s - σ) / 2)` and its gamma factor is
evaluated at `s - σ`, for `A` the conductor of the card. -/
def completed (s : ℂ) : ℂ :=
  χ.unitaryCompletion (s - χ.idealShift)

/-- The defining equation of the unitary completion. -/
theorem unitaryCompletion_def : χ.unitaryCompletion = (grossencharacterData χ).completed :=
  (rfl)

/-- The defining equation of the root number. -/
theorem rootNumber_def : χ.rootNumber = (grossencharacterData χ).rootNumber :=
  (rfl)

/-- The defining equation of the full completion. -/
theorem completed_def (s : ℂ) : χ.completed s = χ.unitaryCompletion (s - χ.idealShift) :=
  (rfl)

/-- The unitary completion is a function of the Hecke character. -/
theorem unitaryCompletion_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) :
    χ.unitaryCompletion = ψ.unitaryCompletion := by
  rw [unitaryCompletion_def, unitaryCompletion_def, grossencharacterData_congr h]

/-- The root number is a function of the Hecke character. -/
theorem rootNumber_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) : χ.rootNumber = ψ.rootNumber := by
  rw [rootNumber_def, rootNumber_def, grossencharacterData_congr h]

/-- The full completion is a function of the Hecke character. -/
theorem completed_congr {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) : χ.completed = ψ.completed := by
  funext s
  rw [completed_def, completed_def, unitaryCompletion_congr h, idealShift_congr h]

/-- The unitary completion of the inverse presentation is the reflected unitary completion. -/
theorem unitaryCompletion_inverse :
    χ.inverse.unitaryCompletion = conj ∘ χ.unitaryCompletion ∘ conj := by
  rw [unitaryCompletion_def, unitaryCompletion_def, grossencharacterData_inverse, dual_completed]

/-- **The root number of the inverse presentation is the conjugate root number.** -/
theorem rootNumber_inverse : χ.inverse.rootNumber = conj χ.rootNumber := by
  rw [rootNumber_def, rootNumber_def, grossencharacterData_inverse, dual_rootNumber]

/-- A trivial unitary part gives the completed Dedekind zeta function as unitary completion. -/
theorem unitaryCompletion_eq_completedDedekindZeta (h : χ.toHeckeCharacter.unitaryPart = 1) :
    χ.unitaryCompletion = completedDedekindZeta K := by
  rw [unitaryCompletion_def, (grossencharacterData_eqOffZero_dedekindZetaData χ h).completed_eq,
    dedekindZetaData_completed]

/-- A trivial unitary part gives root number `1`. -/
theorem rootNumber_eq_one (h : χ.toHeckeCharacter.unitaryPart = 1) :
    χ.rootNumber = 1 := by
  rw [rootNumber_def, (grossencharacterData_eqOffZero_dedekindZetaData χ h).rootNumber_eq,
    dedekindZetaData_rootNumber]

/-- **The full completion of the norm power `N ^ m` is `s ↦ Λ_K(s - m)`**, with poles at `m`
and `1 + m`. -/
theorem completed_normPow (m : ℤ) (s : ℂ) :
    (normPow K m).completed s = completedDedekindZeta K (s - m) := by
  have h : (normPow K m).toHeckeCharacter.unitaryPart = 1 := by
    simpa using HeckeCharacter.unitaryPart_normPow_ofReal (K := K) (-m)
  rw [completed_def, unitaryCompletion_eq_completedDedekindZeta _ h, idealShift_normPow,
    Complex.ofReal_intCast]

end Grossencharacter

end TauCeti.LFunctions

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IntermediateField.Adjoin.BaseChange
public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
import TauCeti.Algebra.Algebra.Hom
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.FieldTheory.IntermediateField.ScalarTower
import TauCeti.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.RingTheory.DiscreteValuationRing.AbhyankarModel.Localization
import TauCeti.RingTheory.DiscreteValuationRing.Kummer
import TauCeti.RingTheory.Localization.Finiteness
import TauCeti.RingTheory.Localization.Integral
import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing

/-!
# Kummer case of Abhyankar's lemma for discrete valuation rings

This file establishes the Kummer case of Abhyankar's lemma for discrete valuation rings (Stacks,
Lemma 15.116.4 (0BRM)): if `L` is a finite extension of the fraction field `K` of a discrete
valuation ring `A` that is tamely ramified with respect to `A`, and `α` is an `n`-th root of a
uniformizer `π` of `A` whose exponent `n` is divisible by the ramification index over `A` of every
maximal ideal of `integralClosure A L`, then `integralClosure A K(α)` is a discrete valuation ring
with respect to which `L(α)` is unramified. Specializing to `L` unramified with respect to `A` shows
that adjoining any root of a uniformizer preserves unramifiedness.

These results supply the Kummer root-extraction input for the Kummer characterization of tamely
ramified extensions in `TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified.Kummer` (Stacks,
Lemma 15.116.7 (0EXW)), base-change stability of tamely ramified DVR extensions in
`TauCeti.RingTheory.DiscreteValuationRing.BaseChange.TamelyRamified` (Stacks, Lemma 15.116.9
(0EXY)), tameness of standard tame covers (Stacks, Lemma 58.31.4 (0EYF)), and Abhyankar's lemma for
a regular divisor (Stacks, Lemma 58.31.5 (0EYG)).

## Usage notes

* In `IsTamelyRamifiedWRT.isUnramifiedWRT_adjoin_root`,
  `IsTamelyRamifiedWRT.exists_isUnramifiedWRT_adjoin_root`, `IsUnramifiedWRT.adjoin_root`, and
  `IsUnramifiedWRT.exists_adjoin_root`, `L⟮α⟯` carries the `letI`-bound `K⟮α⟯`-algebra structure
  induced by `TauCeti.IntermediateField.adjoinBaseChange K L α`. Neither `[Algebra.IsSeparable K L]`
  nor invertibility of `n` in `A ⧸ maximalIdeal A` is required in
  `IsTamelyRamifiedWRT.isUnramifiedWRT_adjoin_root`, and neither `[Algebra.IsSeparable K L]` nor
  `n ≠ 0` is required in `IsUnramifiedWRT.adjoin_root` (the case `n = 0` is vacuous since a
  uniformizer is not a unit).

## Main results

* `TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_of_pow_eq_of_irreducible`,
  `TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_adjoin_root`, and
  `TauCeti.Algebra.IsTamelyRamifiedWRT.exists_isUnramifiedWRT_adjoin_root`: adjoining an `n`-th
  root of a uniformizer whose exponent is divisible by every maximal ideal's ramification index
  makes the extension unramified over the Kummer base.
* `TauCeti.Algebra.IsUnramifiedWRT.adjoin_root` and
  `TauCeti.Algebra.IsUnramifiedWRT.exists_adjoin_root`: adjoining any root of a uniformizer
  preserves unramifiedness.

## References

* [Stacks Project, Lemma 15.116.4](https://stacks.math.columbia.edu/tag/0BRM).
-/

public section

open IsLocalRing _root_.IntermediateField

namespace TauCeti.Algebra

section TamelyRamified

/-- Packaging the Dedekind-over-DVR localization facts with the tame-ramification conditions at a
maximal ideal `P` of `B` over `maximalIdeal A`. -/
private theorem exists_uniformizer_localizationAtPrime_of_tame
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [FaithfulSMul A B]
    {π : A} (hπ : Irreducible π) (P : Ideal B) [P.IsMaximal] [P.LiesOver (maximalIdeal A)]
    (hsep : Algebra.IsSeparable (A ⧸ maximalIdeal A) (B ⧸ P))
    (he_unit : IsUnit ((P.ramificationIdx A : ℕ) : A ⧸ maximalIdeal A)) :
    ∃ (_ : IsDiscreteValuationRing (Localization.AtPrime P))
      (_ : IsLocalHom (algebraMap A (Localization.AtPrime P))),
      IsUnit ((P.ramificationIdx A : ℕ) : Localization.AtPrime P) ∧
        Algebra.IsSeparable (ResidueField A) (ResidueField (Localization.AtPrime P)) ∧
        ∃ (ϖ u : Localization.AtPrime P), Irreducible ϖ ∧ IsUnit u ∧
          algebraMap A (Localization.AtPrime P) π = u * ϖ ^ P.ramificationIdx A := by
  have heA : IsUnit ((P.ramificationIdx A : ℕ) : A) :=
    (isUnit_map_iff (IsLocalRing.residue A) _).mp (by rw [map_natCast]; exact he_unit)
  let := Ideal.Quotient.field (maximalIdeal A)
  let := Ideal.Quotient.field P
  exact ⟨P.isDiscreteValuationRing_localizationAtPrime_of_liesOver
      (IsDiscreteValuationRing.not_a_field A),
    Localization.AtPrime.isLocalHom_algebraMap_of_liesOver (R := A) P,
    by simpa using heA.map (algebraMap A (Localization.AtPrime P)),
    (P.isSeparable_quotient_iff_residueField (R := A)).mp hsep,
    P.exists_eq_unit_mul_pow_ramificationIdx hπ⟩

/-- Applying the local Abhyankar model at primes `Q` over `P` in commuting towers `A → A₁ → B₁` and
`A → B → B₁` when `ϖ₁ ^ (e * d) = π` in `B₁` and `π = u * ϖ ^ e` in `Localization.AtPrime P`. -/
private theorem ramificationIdx_eq_one_and_isSeparable_of_tame_liesOver
    {A A₁ B B₁ : Type*} [CommRing A] [IsLocalRing A]
    [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁] [Algebra A A₁]
    [CommRing B] [IsDomain B] [Algebra A B]
    [CommRing B₁] [IsDomain B₁] [IsIntegrallyClosed B₁]
    [Algebra A B₁] [Algebra A₁ B₁] [Algebra B B₁] [FaithfulSMul B B₁]
    [IsScalarTower A A₁ B₁] [IsScalarTower A B B₁]
    {π : A} {ϖ₁ : A₁} (hϖ₁ : Irreducible ϖ₁)
    (P : Ideal B) [P.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime P)]
    [IsLocalHom (algebraMap A (Localization.AtPrime P))]
    (Q : Ideal B₁) [Q.IsMaximal] [Q.LiesOver (maximalIdeal A₁)] [Q.LiesOver P]
    {ϖ u : Localization.AtPrime P} {e d : ℕ} (hϖ : Irreducible ϖ) (hu : IsUnit u)
    (he : IsUnit (e : Localization.AtPrime P)) (hd : d ≠ 0)
    (hsepBP : Algebra.IsSeparable (ResidueField A) (ResidueField (Localization.AtPrime P)))
    (hπBP : algebraMap A (Localization.AtPrime P) π = u * ϖ ^ e)
    (hb_pow : (algebraMap A₁ B₁ ϖ₁) ^ (e * d) = algebraMap A B₁ π)
    (hgenS : letI := Localization.AtPrime.algebraOfLiesOver P Q
      ∀ c : Localization.AtPrime Q, ∃ s : Localization.AtPrime P, s ≠ 0 ∧
        algebraMap (Localization.AtPrime P) (Localization.AtPrime Q) s * c ∈
          Algebra.adjoin (Localization.AtPrime P)
            {algebraMap B₁ (Localization.AtPrime Q) (algebraMap A₁ B₁ ϖ₁)}) :
    Q.ramificationIdx A₁ = 1 ∧ Algebra.IsSeparable (A₁ ⧸ maximalIdeal A₁) (B₁ ⧸ Q) := by
  let := Localization.AtPrime.algebraOfLiesOver P Q
  have : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) := by
    rw [Localization.AtPrime.algebraMap_eq P Q]
    infer_instance
  have : IsLocalHom (algebraMap A (Localization.AtPrime Q)) := by
    rw [IsScalarTower.algebraMap_eq A (Localization.AtPrime P) (Localization.AtPrime Q)]
    infer_instance
  have : IsIntegrallyClosed (Localization.AtPrime Q) :=
    isIntegrallyClosed_of_isLocalization _ Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  have : FaithfulSMul (Localization.AtPrime P) (Localization.AtPrime Q) := by
    rw [faithfulSMul_iff_algebraMap_injective,
      ← IsLocalization.map_unique (T := Q.primeCompl)
        (Localization.le_comap_primeCompl_iff.mpr (Q.over_def P).ge) _
        fun b ↦ (IsScalarTower.algebraMap_apply B _ (Localization.AtPrime Q) b).symm]
    exact IsLocalization.map_injective_of_injective' P.primeCompl B₁ (Localization.AtPrime Q) _
      (fun h0 ↦ h0 Q.zero_mem) (FaithfulSMul.algebraMap_injective B B₁)
  have hbS : algebraMap B₁ (Localization.AtPrime Q) (algebraMap A₁ B₁ ϖ₁) ^ (e * d) =
      algebraMap (Localization.AtPrime P) (Localization.AtPrime Q) (u * ϖ ^ e) := by
    rw [← map_pow, hb_pow, ← IsScalarTower.algebraMap_apply A B₁ (Localization.AtPrime Q),
      ← hπBP, ← IsScalarTower.algebraMap_apply A (Localization.AtPrime P) (Localization.AtPrime Q)]
  have := isDiscreteValuationRing_of_pow_eq_unit_mul_pow hϖ hu he hd hbS hgenS
  have hirrS := irreducible_of_pow_eq_unit_mul_pow hϖ hu he hd hbS hgenS
  have := isSeparable_residueField_of_pow_eq_unit_mul_pow hϖ hu he hd hbS hgenS
  have hsepAS : Algebra.IsSeparable (ResidueField A) (ResidueField (Localization.AtPrime Q)) :=
    .trans _ (ResidueField (Localization.AtPrime P)) _
  exact Q.ramificationIdx_eq_one_and_isSeparable_of_irreducible_localizationAtPrime
    hϖ₁ hirrS hsepAS

/-- If `E` is generated over `L` by the image of an `n`-th root `α₁ ∈ K₁` of `π ∈ A` (`n ≠ 0`), then
`E` is generated as an `L`-algebra by the image of `⟨α₁, _⟩` through `integralClosure A E`. -/
private theorem adjoin_singleton_integralClosure_eq_top
    {A L K₁ E : Type*} [CommRing A] [Field L] [Algebra A L]
    [Field K₁] [Algebra A K₁] [Field E] [Algebra A E] [Algebra L E] [Algebra K₁ E]
    [IsScalarTower A L E] [IsScalarTower A K₁ E]
    {π : A} {n : ℕ} (hn : n ≠ 0) {α₁ : K₁} (hα₁ : α₁ ^ n = algebraMap A K₁ π)
    (hα₁A₁ : α₁ ∈ integralClosure A K₁) (hgenL : L⟮algebraMap K₁ E α₁⟯ = ⊤) :
    letI := TauCeti.integralClosureMapAlgebra A K₁ A E
    Algebra.adjoin L (algebraMap (integralClosure A E) E ''
      ({algebraMap (integralClosure A K₁) (integralClosure A E) ⟨α₁, hα₁A₁⟩} : Set _)) = ⊤ := by
  let := TauCeti.integralClosureMapAlgebra A K₁ A E
  have := TauCeti.isScalarTower_integralClosureMapAlgebra_right A K₁ A E
  have hbE : algebraMap (integralClosure A E) E
      (algebraMap (integralClosure A K₁) (integralClosure A E) ⟨α₁, hα₁A₁⟩) =
      algebraMap K₁ E α₁ :=
    (IsScalarTower.algebraMap_apply (integralClosure A K₁) (integralClosure A E) E ⟨α₁, hα₁A₁⟩).symm
  have hα₁E_int : IsIntegral A (algebraMap K₁ E α₁) :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) <| by
      rw [← map_pow, hα₁, ← IsScalarTower.algebraMap_apply A K₁ E]
      exact isIntegral_algebraMap
  rw [Set.image_singleton, hbE,
    ← adjoin_simple_toSubalgebra_of_isAlgebraic hα₁E_int.tower_top.isAlgebraic, hgenL,
    top_toSubalgebra]

/-- Local step of the Kummer-case Abhyankar theorem: at each maximal ideal `Q` of
`integralClosure A E` lying over `maximalIdeal (integralClosure A K₁)`, the ramification index over
`integralClosure A K₁` is `1` and the residue extension is separable. -/
private theorem ramificationIdx_eq_one_and_isSeparable_of_pow_eq
    {A K L K₁ E : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L]
    [Field K₁] [Algebra A K₁] [Algebra K K₁] [IsScalarTower A K K₁]
    [Field E] [Algebra A E] [Algebra K E] [Algebra L E] [Algebra K₁ E]
    [IsScalarTower A K E] [IsScalarTower A L E] [IsScalarTower A K₁ E] [FiniteDimensional K E]
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {n : ℕ} (hn : n ≠ 0)
    {α₁ : K₁} (hα₁ : α₁ ^ n = algebraMap A K₁ π) (hgenK : K⟮α₁⟯ = ⊤)
    (hgenL : L⟮algebraMap K₁ E α₁⟯ = ⊤)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal], P.ramificationIdx A ∣ n)
    [IsDiscreteValuationRing (integralClosure A K₁)] :
    letI := TauCeti.integralClosureMapAlgebra A K₁ A E
    ∀ (Q : Ideal (integralClosure A E)) [Q.IsMaximal]
      [Q.LiesOver (maximalIdeal (integralClosure A K₁))],
      Q.ramificationIdx (integralClosure A K₁) = 1 ∧
        Algebra.IsSeparable (integralClosure A K₁ ⧸ maximalIdeal (integralClosure A K₁))
          (integralClosure A E ⧸ Q) := by
  let := TauCeti.integralClosureMapAlgebra A K₁ A E
  have := TauCeti.isScalarTower_integralClosureMapAlgebra_left A K₁ A E
  have := TauCeti.isScalarTower_integralClosureMapAlgebra_right A K₁ A E
  let := TauCeti.integralClosureMapAlgebra A L A E
  have := TauCeti.isScalarTower_integralClosureMapAlgebra_left A L A E
  have := TauCeti.isScalarTower_integralClosureMapAlgebra_right A L A E
  have : IsDedekindDomain (integralClosure A L) := TauCeti.integralClosure.isDedekindDomain A K L
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L (integralClosure A L)
  have : IsIntegrallyClosed (integralClosure A E) :=
    _root_.integralClosure.isIntegrallyClosedOfFiniteExtension K
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K E (integralClosure A E)
  have := FaithfulSMul.trans A K L
  have : FaithfulSMul A (integralClosure A L) := .tower_bot A (integralClosure A L) L
  have := FaithfulSMul.trans (integralClosure A L) L E
  have : FaithfulSMul (integralClosure A L) (integralClosure A E) := .tower_bot _ _ E
  have hα₁A₁ : α₁ ∈ integralClosure A K₁ :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hα₁ ▸ isIntegral_algebraMap)
  have hϖ₁ : Irreducible (⟨α₁, hα₁A₁⟩ : integralClosure A K₁) :=
    IsDiscreteValuationRing.irreducible_mk_of_pow_eq_of_irreducible hπ hα₁ hgenK hα₁A₁
  let b : integralClosure A E := algebraMap (integralClosure A K₁) _ ⟨α₁, hα₁A₁⟩
  have hbE : algebraMap (integralClosure A E) E b = algebraMap K₁ E α₁ :=
    (IsScalarTower.algebraMap_apply (integralClosure A K₁) (integralClosure A E) E ⟨α₁, hα₁A₁⟩).symm
  have htopE := adjoin_singleton_integralClosure_eq_top hn hα₁ hα₁A₁ hgenL (L := L)
  intro Q _ _
  have : (maximalIdeal (integralClosure A K₁)).LiesOver (maximalIdeal A) :=
    ⟨(eq_maximalIdeal (Ideal.IsMaximal.under A _)).symm⟩
  have : Q.LiesOver (maximalIdeal A) := .trans Q (maximalIdeal (integralClosure A K₁)) _
  let P : Ideal (integralClosure A L) := Q.under (integralClosure A L)
  have : Q.LiesOver P := ⟨rfl⟩
  have : P.LiesOver (maximalIdeal A) := ⟨by rw [Ideal.under_under, Q.over_def (maximalIdeal A)]⟩
  have : P.IsMaximal := .of_liesOver_isMaximal P (maximalIdeal A)
  obtain ⟨hsepP, heP_unit⟩ := isTamelyRamifiedWRT_def.mp h P
  obtain ⟨_, _, heBP, hsepBP, ϖ, u, hϖ, hu, hπBP⟩ :=
    exists_uniformizer_localizationAtPrime_of_tame hπ P hsepP heP_unit
  obtain ⟨d, hd_eq⟩ := hdvd P
  have hd : d ≠ 0 := fun hd0 ↦ hn (by rw [hd_eq, hd0, mul_zero])
  have hb_pow : b ^ (P.ramificationIdx A * d) = algebraMap A (integralClosure A E) π :=
    Subtype.ext <| by
      rw [← hd_eq, Subalgebra.coe_pow, Subalgebra.coe_algebraMap,
        ← Subalgebra.algebraMap_apply (integralClosure A E) b, hbE, ← map_pow, hα₁,
        ← IsScalarTower.algebraMap_apply A K₁ E]
  refine ramificationIdx_eq_one_and_isSeparable_of_tame_liesOver hϖ₁ P Q hϖ hu heBP hd hsepBP hπBP
    hb_pow fun c ↦ ?_
  have hcE : algebraMap (Localization.AtPrime Q) E c ∈
      Algebra.adjoin L (algebraMap (integralClosure A E) E '' ({b} : Set _)) :=
    htopE ▸ Algebra.mem_top
  simpa only [Set.image_singleton] using
    TauCeti.Localization.AtPrime.exists_mul_mem_adjoin P Q hcE

/-- **Kummer case of Abhyankar's lemma for discrete valuation rings.** Let `A` be a discrete
valuation ring with fraction field `K` and uniformizer `π`, and let `L / K` be a finite extension
that is tamely ramified with respect to `A`. Let `K₁ = K(α₁)` be generated by an `n`-th root `α₁`
of `π`, where every maximal ideal of `integralClosure A L` has ramification index over `A` dividing
`n`, and let `E` be an extension of `L` and `K₁` generated over `L` by the image of `α₁`. Then the
integral closure of `A` in `K₁` is a discrete valuation ring with respect to which `E` is
unramified. Neither separability of `L / K` nor invertibility of `n` in the residue field of `A` is
required. -/
@[stacks 0BRM "Kummer case, unramifiedness over the Kummer ring"]
theorem IsTamelyRamifiedWRT.isUnramifiedWRT_of_pow_eq_of_irreducible
    {A K L K₁ E : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L]
    [Field K₁] [Algebra A K₁] [Algebra K K₁] [IsScalarTower A K K₁]
    [Field E] [Algebra K E] [Algebra L E] [Algebra K₁ E]
    [IsScalarTower K L E] [IsScalarTower K K₁ E]
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {n : ℕ}
    {α₁ : K₁} (hα₁ : α₁ ^ n = algebraMap A K₁ π) (hgenK : K⟮α₁⟯ = ⊤)
    (hgenL : L⟮algebraMap K₁ E α₁⟯ = ⊤)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal], P.ramificationIdx A ∣ n) :
    ∃ hDVR : IsDiscreteValuationRing (integralClosure A K₁),
      letI := hDVR
      IsUnramifiedWRT (integralClosure A K₁) E := by
  let : Algebra A E := ((algebraMap K E).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K E := .of_algebraMap_eq fun _ ↦ rfl
  have : FaithfulSMul A K₁ := .trans A K K₁
  have hn : n ≠ 0 := _root_.Algebra.ne_zero_of_pow_eq_algebraMap_of_injective
    (FaithfulSMul.algebraMap_injective A K₁) hπ.ne_one hα₁
  have hDVR :=
    IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
      hπ hα₁ hgenK
  have : IsScalarTower A L E := .to₁₃₄ A K L E
  have : IsScalarTower A K₁ E := .to₁₃₄ A K K₁ E
  have hintL : IsIntegral L (algebraMap K₁ E α₁) :=
    (IsIntegral.of_pow (Nat.pos_of_ne_zero hn)
      (by
        rw [← map_pow, hα₁, ← IsScalarTower.algebraMap_apply A K₁ E]
        exact isIntegral_algebraMap)).tower_top
  have : FiniteDimensional L E := by
    have := adjoin.finiteDimensional hintL
    exact Module.Finite.equiv (hgenL ▸ IntermediateField.topEquiv (F := L) (E := E)).toLinearEquiv
  have : FiniteDimensional K E := Module.Finite.trans L E
  let := TauCeti.integralClosureMapAlgebra A K₁ A E
  have := TauCeti.isScalarTower_integralClosureMapAlgebra_left A K₁ A E
  have := TauCeti.isScalarTower_integralClosureMapAlgebra_right A K₁ A E
  have : IsScalarTower (integralClosure A K₁) K₁ E := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsIntegral (integralClosure A K₁) (integralClosure A E) := .tower_top A
  have : FaithfulSMul (integralClosure A K₁) (integralClosure A E) := .tower_bot _ _ E
  have : IsIntegralClosure (integralClosure A E) (integralClosure A K₁) E :=
    IsIntegralClosure.tower_top (R := A)
  refine ⟨hDVR, (isUnramifiedWRT_iff_of_isIntegralClosure (integralClosure A E)).mpr ?_⟩
  exact ramificationIdx_eq_one_and_isSeparable_of_pow_eq h hπ hn hα₁ hgenK hgenL hdvd

/-- Let `A` be a discrete valuation ring with fraction field `K`, and let `L / K` be a finite
extension that is tamely ramified with respect to `A`. Adjoining an `n`-th root `α` of a
uniformizer `π` of `A` to both `K` and `L`, where every maximal ideal of `integralClosure A L` has
ramification index dividing `n`, makes `integralClosure A K(α)` a discrete valuation ring with
respect to which `L(α)` (equipped with the `K(α)`-algebra structure induced by `adjoinBaseChange`)
is unramified. Neither separability of `L / K` nor invertibility of `n` in the residue field of `A`
is required. -/
@[stacks 0BRM "Kummer case, adjoining a root in an ambient field"]
theorem IsTamelyRamifiedWRT.isUnramifiedWRT_adjoin_root
    {A K L Ω : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L]
    [Field Ω] [Algebra K Ω] [Algebra L Ω] [Algebra A Ω] [IsScalarTower K L Ω]
    [IsScalarTower A K Ω]
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {n : ℕ} {α : Ω}
    (hα : α ^ n = algebraMap A Ω π)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal], P.ramificationIdx A ∣ n) :
    letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
    ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮α⟯),
      letI := hDVR
      IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ := by
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
  have hgenL : L⟮algebraMap K⟮α⟯ L⟮α⟯ (AdjoinSimple.gen K α)⟯ = ⊤ := by
    rw [AlgHom.algebraMap_toAlgebra_apply, TauCeti.IntermediateField.adjoinBaseChange_gen]
    exact _root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α
  exact h.isUnramifiedWRT_of_pow_eq_of_irreducible hπ
    (AdjoinSimple.gen_pow_eq_algebraMap_iff.mpr hα)
    (_root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α) hgenL hdvd

/-- Let `A` be a discrete valuation ring with fraction field `K`, and let `L / K` be a finite
extension tamely ramified with respect to `A` inside an algebraically closed field `Ω`. For every
positive `n` divisible by the ramification indices of all maximal ideals of `integralClosure A L`,
there is an `n`-th root `α` of the uniformizer `π` in `Ω` such that `integralClosure A K(α)` is a
discrete valuation ring and `L(α)` (with its `K(α)`-algebra structure induced by `adjoinBaseChange`)
is unramified with respect to `integralClosure A K(α)`. -/
theorem IsTamelyRamifiedWRT.exists_isUnramifiedWRT_adjoin_root
    {A K L Ω : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L]
    [Field Ω] [Algebra K Ω] [Algebra L Ω] [Algebra A Ω] [IsScalarTower K L Ω]
    [IsScalarTower A K Ω] [IsAlgClosed Ω]
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {n : ℕ} (hn : 0 < n)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal], P.ramificationIdx A ∣ n) :
    ∃ α : Ω, α ^ n = algebraMap A Ω π ∧
      letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
      ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮α⟯),
        letI := hDVR
        IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A Ω π) hn
  exact ⟨α, hα, h.isUnramifiedWRT_adjoin_root hπ hα hdvd⟩

end TamelyRamified

section Unramified

variable {A K L Ω : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
  [IsScalarTower A K L] [FiniteDimensional K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω] [Algebra A Ω] [IsScalarTower K L Ω]
  [IsScalarTower A K Ω]

/-- For a finite extension `L` of the fraction field `K` of a discrete valuation ring `A` that is
unramified with respect to `A`, adjoining an `n`-th root `α` of a uniformizer `π` of `A` to both
fields preserves unramifiedness: `integralClosure A K(α)` is a discrete valuation ring, even for a
wild root extraction, and `L(α)` (with the `K(α)`-algebra structure induced by `adjoinBaseChange`)
is unramified with respect to it. Neither separability of `L / K` nor `n ≠ 0` is required. -/
theorem IsUnramifiedWRT.adjoin_root (h : IsUnramifiedWRT A L) {π : A}
    (hπ : Irreducible π) {n : ℕ} {α : Ω}
    (hα : α ^ n = algebraMap A Ω π) :
    letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
    ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮α⟯),
      letI := hDVR
      IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ :=
  h.isTamelyRamifiedWRT.isUnramifiedWRT_adjoin_root hπ hα fun P _ ↦ by
    have : P.LiesOver (maximalIdeal A) :=
      ⟨(eq_maximalIdeal (Ideal.IsMaximal.under A P)).symm⟩
    exact (isUnramifiedWRT_def.mp h P).1 ▸ one_dvd n

/-- For a finite extension `L` of the fraction field `K` of a discrete valuation ring `A` that is
unramified with respect to `A`, inside an algebraically closed ambient extension `Ω`, every positive
root degree `n` admits an `n`-th root `α` of a uniformizer `π` making `integralClosure A K(α)` a
discrete valuation ring and `L(α)` (with its `K(α)`-algebra structure via `adjoinBaseChange`)
unramified with respect to it. -/
theorem IsUnramifiedWRT.exists_adjoin_root [IsAlgClosed Ω] (h : IsUnramifiedWRT A L)
    {π : A} (hπ : Irreducible π) {n : ℕ} (hn : 0 < n) :
    ∃ α : Ω, α ^ n = algebraMap A Ω π ∧
      letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
      ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮α⟯),
        letI := hDVR
        IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A Ω π) hn
  exact ⟨α, hα, h.adjoin_root hπ hα⟩

end Unramified

end TauCeti.Algebra

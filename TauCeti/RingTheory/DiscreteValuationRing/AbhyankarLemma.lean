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
import TauCeti.RingTheory.DiscreteValuationRing.AbhyankarModel.Localization
import TauCeti.RingTheory.DiscreteValuationRing.Kummer
import TauCeti.RingTheory.Ideal.LiesOver
import TauCeti.RingTheory.Localization.AtPrime
import TauCeti.RingTheory.Localization.Integral

/-!
# Abhyankar's lemma and Kummer characterization of tame ramification

Let `A` be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let `L / K`
be a finite separable extension.

If `L` is tamely ramified with respect to `A`, and `β` is an `e`-th root of `π` in an ambient
extension `Ω` of `L` such that every ramification index of `integralClosure A L` over `A` divides
`e`, then `integralClosure A K(β)` is a discrete valuation ring and `L(β)` is unramified with
respect to it (`TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_adjoin_root`). No
invertibility hypothesis on `e` is needed here.

In an algebraically closed extension `Ω` of `L`, this gives the three equivalent characterizations
of tame ramification in Stacks, Lemma 15.116.7 (0EXW) (`TauCeti.Algebra.isTamelyRamifiedWRT_tfae`
and `TauCeti.Algebra.isTamelyRamifiedWRT_iff_exists_kummer`): `L` is tamely ramified with respect
to `A` iff there exist `e` invertible in `κ_A` and an `e`-th root `β` of `π` with `L(β)`
unramified over `integralClosure A K(β)`, iff there exists `e₀` invertible in `κ_A` such that for
every multiple `e` of `e₀` and every `e`-th root `β` of `π`, `L(β)` is unramified over
`integralClosure A K(β)`.

## Main results

* `TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_adjoin_root`: adjoining an `e`-th root `β`
  of a uniformizer `π` with every ramification index dividing `e` makes `L(β)` unramified over
  `integralClosure A K(β)` (SGA 1, Exposé X, Lemme 3.6; Stacks, Lemma 15.116.4 (0BRM)).
* `TauCeti.Algebra.isTamelyRamifiedWRT_tfae` and
  `TauCeti.Algebra.isTamelyRamifiedWRT_iff_exists_kummer`: the Kummer characterization of tame
  ramification (Stacks, Lemma 15.116.7 (0EXW)).

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé X, Lemme 3.6.
* [Stacks Project, Lemma 15.116.4](https://stacks.math.columbia.edu/tag/0BRM).
* [Stacks Project, Lemma 15.116.7](https://stacks.math.columbia.edu/tag/0EXW).
-/

public section

open IntermediateField IsLocalRing Polynomial

namespace TauCeti.Algebra

variable {A K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
  [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- Clear denominators over a domain `B_P` with fraction field `L` when an element `βS` of a
domain `S` (with fraction field `L₁`) generates `L₁` as an `L`-algebra. -/
private theorem exists_mul_mem_adjoin_of_adjoin_eq_top
    {B_P S L₁ : Type*} [CommRing B_P] [IsDomain B_P] [Algebra B_P L] [IsFractionRing B_P L]
    [CommRing S] [Algebra B_P S] [Field L₁] [Algebra L L₁] [Algebra S L₁]
    [IsFractionRing S L₁]
    (hcomp : (algebraMap S L₁).comp (algebraMap B_P S) =
      (algebraMap L L₁).comp (algebraMap B_P L))
    {βS : S} (hβgen : Algebra.adjoin L {algebraMap S L₁ βS} = ⊤) (c : S) :
    ∃ s : B_P, s ≠ 0 ∧ algebraMap B_P S s * c ∈ Algebra.adjoin B_P {βS} := by
  have hmem : algebraMap S L₁ c ∈ Algebra.adjoin L {algebraMap S L₁ βS} :=
    hβgen ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, hp⟩ := hmem
  obtain ⟨s, hs, hsp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors B_P) p
  refine ⟨s, nonZeroDivisors.ne_zero hs, ?_⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors B_P) p,
    IsFractionRing.injective S L₁ ?_⟩
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hp ⊢
  rw [aeval_def, map_mul, ← RingHom.comp_apply, hcomp, RingHom.comp_apply,
    Polynomial.hom_eval₂, hcomp, ← eval₂_map, hsp,
    ← IsScalarTower.algebraMap_smul L s p, eval₂_smul, ← aeval_def, hp]

-- At a maximal ideal `Q` of an integral closure `B₁` of `A₁` in `L₁ = L(β)`, localize at `Q` and
-- `P = Q ∩ B` to apply the local Abhyankar model (`TauCeti.irreducible_of_pow_eq_unit_mul_pow` and
-- `TauCeti.isSeparable_residueField_of_pow_eq_unit_mul_pow`). Abstracting `B, B₁, L₁` avoids
-- `Subalgebra.instSMul` instance loops.
private theorem ramificationIdx_eq_one_and_isSeparable_at_prime
    {A₁ L₁ B B₁ : Type*}
    [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁]
    [Algebra A A₁] [Algebra.IsIntegral A A₁]
    [Field L₁] [Algebra L L₁] [Algebra A₁ L₁]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [Algebra B L] [Algebra B L₁]
    [IsScalarTower A B L] [IsScalarTower B L L₁] [IsIntegralClosure B A L]
    [IsFractionRing B L] [FaithfulSMul A B]
    [CommRing B₁] [IsDedekindDomain B₁] [Algebra A B₁] [Algebra A₁ B₁] [Algebra B B₁]
    [Algebra B₁ L₁] [IsScalarTower A A₁ B₁] [IsScalarTower A B B₁]
    [IsScalarTower B B₁ L₁] [IsScalarTower A₁ B₁ L₁] [Algebra.IsIntegral A₁ B₁]
    [IsFractionRing B₁ L₁] [FaithfulSMul A₁ B₁]
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {e : ℕ} (he : e ≠ 0)
    (βA₁ : A₁) (hβA₁_irred : Irreducible βA₁)
    (hβA₁_pow : βA₁ ^ e = algebraMap A A₁ π)
    (hβgen : Algebra.adjoin L {algebraMap A₁ L₁ βA₁} = ⊤)
    (hdvd : ∀ (P : Ideal B) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ e)
    (Q : Ideal B₁) [Q.IsMaximal] [Q.LiesOver (maximalIdeal A₁)] :
    Q.ramificationIdx A₁ = 1 ∧
      Algebra.IsSeparable (A₁ ⧸ maximalIdeal A₁) (B₁ ⧸ Q) := by
  have : Algebra.IsIntegral A B₁ := Algebra.IsIntegral.trans A₁
  have : Algebra.IsIntegral B B₁ := .tower_top A
  have : (maximalIdeal A₁).LiesOver (maximalIdeal A) :=
    ⟨(eq_maximalIdeal (Ideal.IsMaximal.under A _)).symm⟩
  have : Q.LiesOver (maximalIdeal A) := .trans Q (maximalIdeal A₁) (maximalIdeal A)
  set P : Ideal B := Q.under B
  have : Q.LiesOver P := ⟨rfl⟩
  have : P.IsMaximal := Ideal.IsMaximal.under B Q
  have : P.LiesOver (maximalIdeal A) :=
    ⟨by simp only [P, Ideal.under_under, ← Ideal.over_def Q (maximalIdeal A)]⟩
  have hPne : P ≠ ⊥ := fun hP ↦ IsDiscreteValuationRing.not_a_field A <| by
    rw [Ideal.over_def P (maximalIdeal A), hP]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective A B)
  have hQne : Q ≠ ⊥ := fun hQ ↦ IsDiscreteValuationRing.not_a_field A₁ <| by
    rw [Ideal.over_def Q (maximalIdeal A₁), hQ]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective A₁ B₁)
  -- Localize at `P` and `Q`: `B_P` and `S` are DVRs with `B_P ⊆ S` inside `L ⊆ L₁`.
  let B_P := Localization.AtPrime P
  let S := Localization.AtPrime Q
  have : IsDiscreteValuationRing B_P :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hPne B_P
  have : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B₁ hQne S
  let := Localization.AtPrime.algebraOfLiesOver P Q
  have : IsLocalHom (algebraMap B_P S) := by
    rw [Localization.AtPrime.algebraMap_eq P Q]
    exact Localization.isLocalHom_localRingHom P Q (algebraMap B B₁) Ideal.LiesOver.over
  have hcomp : (algebraMap S L₁).comp (algebraMap B_P S) =
      (algebraMap L L₁).comp (algebraMap B_P L) :=
    IsLocalization.ringHom_ext P.primeCompl <| RingHom.ext fun b ↦ by
      simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B B_P S,
        ← IsScalarTower.algebraMap_apply B B_P L]
      rw [IsScalarTower.algebraMap_apply B B₁ S, ← IsScalarTower.algebraMap_apply B₁ S L₁,
        ← IsScalarTower.algebraMap_apply B B₁ L₁, ← IsScalarTower.algebraMap_apply B L L₁]
  have hBP_S_inj : Function.Injective (algebraMap B_P S) :=
    Function.Injective.of_comp (f := algebraMap S L₁) <| by
      rw [← RingHom.coe_comp, hcomp]
      exact (algebraMap L L₁).injective.comp (IsFractionRing.injective B_P L)
  have : FaithfulSMul B_P S := (faithfulSMul_iff_algebraMap_injective B_P S).mpr hBP_S_inj
  -- Express `π` in `B_P` as `u * ϖ ^ m`, with `m = P.ramificationIdx A` invertible and `m ∣ e`.
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B_P
  have hπBP_ne : algebraMap A B_P π ≠ 0 := by
    have : FaithfulSMul A B_P := .trans A B B_P
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B_P)).mpr hπ.ne_zero
  obtain ⟨m, u, hπBP⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπBP_ne hϖ
  have hm_eq : P.ramificationIdx A = m := by
    refine Ideal.IsDedekindDomain.ramificationIdx_eq_of_map_eq_pow (maximalIdeal A) P m ?_
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.map_span,
      Set.image_singleton, hπBP, Ideal.span_singleton_mul_left_unit u.isUnit,
      ← Ideal.span_singleton_pow,
      ← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
  have hunit_mA : IsUnit (m : A) := (isUnit_map_iff (IsLocalRing.residue A) _).mp (by
    rw [map_natCast]; exact hm_eq ▸ ((isTamelyRamifiedWRT_iff_of_isIntegralClosure B).mp h P).2)
  have hunit_mBP : IsUnit (m : B_P) := by simpa using hunit_mA.map (algebraMap A B_P)
  obtain ⟨d, hmd⟩ := hm_eq ▸ hdvd P
  have hd : d ≠ 0 := right_ne_zero_of_mul (hmd ▸ he)
  -- Apply the local Abhyankar model to `βS ∈ S`.
  let βS : S := algebraMap B₁ S (algebraMap A₁ B₁ βA₁)
  have hβS_pow : βS ^ (m * d) = algebraMap B_P S ((u : B_P) * ϖ ^ m) :=
    calc βS ^ (m * d) = algebraMap B₁ S (algebraMap A₁ B₁ (βA₁ ^ e)) := by
          rw [← hmd, map_pow, map_pow]
      _ = algebraMap A S π := by
          rw [hβA₁_pow, ← IsScalarTower.algebraMap_apply A A₁ B₁,
            ← IsScalarTower.algebraMap_apply A B₁ S]
      _ = algebraMap B_P S ((u : B_P) * ϖ ^ m) := by
          rw [← hπBP, ← IsScalarTower.algebraMap_apply A B_P S]
  have hβS_val : algebraMap S L₁ βS = algebraMap A₁ L₁ βA₁ := by
    rw [← IsScalarTower.algebraMap_apply B₁ S L₁, ← IsScalarTower.algebraMap_apply A₁ B₁ L₁]
  have hgen : ∀ c : S, ∃ s : B_P,
      s ≠ 0 ∧ algebraMap B_P S s * c ∈ Algebra.adjoin B_P {βS} :=
    exists_mul_mem_adjoin_of_adjoin_eq_top hcomp (hβS_val.symm ▸ hβgen)
  have hβS_irred : Irreducible βS :=
    TauCeti.irreducible_of_pow_eq_unit_mul_pow hϖ u.isUnit hunit_mBP hd hβS_pow hgen
  have : Algebra.IsSeparable (ResidueField B_P) (ResidueField S) :=
    TauCeti.isSeparable_residueField_of_pow_eq_unit_mul_pow hϖ u.isUnit hunit_mBP hd hβS_pow hgen
  refine ⟨?_, ?_⟩
  · refine Ideal.IsDedekindDomain.ramificationIdx_eq_of_map_eq_pow (maximalIdeal A₁) Q 1 ?_
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer βA₁).mp hβA₁_irred,
      Ideal.map_span, Set.image_singleton, pow_one, IsScalarTower.algebraMap_apply A₁ B₁ S,
      ← (IsDiscreteValuationRing.irreducible_iff_uniformizer βS).mp hβS_irred]
  · let := Ideal.Quotient.field (maximalIdeal A)
    let := Ideal.Quotient.field P
    let := Ideal.Quotient.field (maximalIdeal A₁)
    let := Ideal.Quotient.field Q
    have : Algebra.IsSeparable (A ⧸ maximalIdeal A) (B ⧸ P) :=
      ((isTamelyRamifiedWRT_iff_of_isIntegralClosure B).mp h P).1
    have : Algebra.IsSeparable (B ⧸ P) (B₁ ⧸ Q) :=
      (Algebra.isSeparable_residueField_iff (p := P) (q := Q)).mp ‹_›
    have := Ideal.Quotient.isScalarTower_quotient_of_liesOver (maximalIdeal A) P Q
    have : Algebra.IsSeparable (A ⧸ maximalIdeal A) (B₁ ⧸ Q) := .trans _ (B ⧸ P) _
    have := Ideal.Quotient.isScalarTower_quotient_of_liesOver (maximalIdeal A) (maximalIdeal A₁) Q
    exact Algebra.isSeparable_tower_top_of_isSeparable (A ⧸ maximalIdeal A) _ _

include K in
/-- Global Abhyankar's lemma for opaque `A₁ ⊆ K₁ ⊆ L₁`, avoiding nested `Subalgebra` reduction
when forming `integralClosure A₁ L₁`. -/
private theorem isUnramifiedWRT_of_dvr_adjoin_root
    {A₁ K₁ L₁ : Type*}
    [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁]
    [Algebra A A₁] [Algebra.IsIntegral A A₁]
    [Field K₁] [Algebra A₁ K₁] [IsFractionRing A₁ K₁]
    [Field L₁] [Algebra L L₁] [Algebra K₁ L₁] [Algebra A L₁] [Algebra A₁ L₁]
    [IsScalarTower A L L₁] [IsScalarTower A A₁ L₁] [IsScalarTower A₁ K₁ L₁]
    [FiniteDimensional K₁ L₁] [Algebra.IsSeparable K₁ L₁]
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {e : ℕ} (he : e ≠ 0)
    (βA₁ : A₁) (hβA₁_irred : Irreducible βA₁)
    (hβA₁_pow : βA₁ ^ e = algebraMap A A₁ π)
    (hβgen : Algebra.adjoin L {algebraMap A₁ L₁ βA₁} = ⊤)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ e) :
    IsUnramifiedWRT A₁ L₁ := by
  have : IsDedekindDomain (integralClosure A L) := integralClosure.isDedekindDomain A K L
  have : IsFractionRing (integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L _
  have : FaithfulSMul A L := .trans A K L
  have : FaithfulSMul A (integralClosure A L) := .tower_bot A _ L
  have : IsDedekindDomain (integralClosure A₁ L₁) :=
    integralClosure.isDedekindDomain A₁ K₁ L₁
  have : IsFractionRing (integralClosure A₁ L₁) L₁ :=
    IsIntegralClosure.isFractionRing_of_finite_extension A₁ K₁ L₁ _
  have : FaithfulSMul A₁ (integralClosure A₁ L₁) := by
    have : FaithfulSMul A₁ L₁ := .trans A₁ K₁ L₁
    exact .tower_bot A₁ (integralClosure A₁ L₁) L₁
  let := integralClosureMapAlgebra A L A₁ L₁
  have := isScalarTower_integralClosureMapAlgebra_left A L A₁ L₁
  have := isScalarTower_integralClosureMapAlgebra_right A L A₁ L₁
  have : IsScalarTower A A₁ (integralClosure A₁ L₁) :=
    .of_algebraMap_eq fun a ↦ Subtype.ext (by
      simp [Subalgebra.coe_algebraMap, ← IsScalarTower.algebraMap_apply A A₁ L₁])
  exact isUnramifiedWRT_def.mpr fun Q _ _ ↦
    ramificationIdx_eq_one_and_isSeparable_at_prime
      h hπ he βA₁ hβA₁_irred hβA₁_pow hβgen hdvd Q

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra L Ω] [Algebra A Ω]
  [IsScalarTower K L Ω] [IsScalarTower A K Ω]

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] in
/-- Shared scalar towers and generator-power equation for adjoining an `e`-th root `β ∈ Ω` of
`π ∈ A` to `K ⊆ L`. -/
private theorem adjoinBaseChange_towers_and_pow {π : A} {e : ℕ} {β : Ω}
    (hβ : β ^ e = algebraMap A Ω π) :
    letI := (TauCeti.IntermediateField.adjoinBaseChange K L β).toAlgebra
    ∃ h : IsScalarTower A L Ω, letI := h
      IsScalarTower A K L⟮β⟯ ∧ IsScalarTower A K⟮β⟯ L⟮β⟯ ∧
        AdjoinSimple.gen K β ^ e = algebraMap A K⟮β⟯ π := by
  let := (TauCeti.IntermediateField.adjoinBaseChange K L β).toAlgebra
  have hALΩ : IsScalarTower A L Ω := .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A K Ω, IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply K L Ω]
  have hAKLβ : IsScalarTower A K L⟮β⟯ := .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A L L⟮β⟯,
      IsScalarTower.algebraMap_apply K L L⟮β⟯, ← IsScalarTower.algebraMap_apply A K L]
  have hAKβLβ : IsScalarTower A K⟮β⟯ L⟮β⟯ :=
    IsScalarTower.of_algHom ((TauCeti.IntermediateField.adjoinBaseChange K L β).restrictScalars A)
  have hβK : AdjoinSimple.gen K β ^ e = algebraMap A K⟮β⟯ π :=
    Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A K K⟮β⟯,
      IsScalarTower.algebraMap_apply A K Ω] using hβ)
  exact ⟨hALΩ, hAKLβ, hAKβLβ, hβK⟩

/-- **Abhyankar's lemma for discrete valuation rings (global Kummer case).** Let `L / K` be a
finite separable extension tamely ramified with respect to a discrete valuation ring `A` with
uniformizer `π`. If `β` is an `e`-th root of `π` in an ambient extension `Ω` of `L` such that
every ramification index of `integralClosure A L` over `A` divides `e`, then `L(β)` is unramified
with respect to the discrete valuation ring `integralClosure A K(β)`. The exponent `e` need not be
invertible in the residue field of `A`. -/
@[stacks 0BRM "global Kummer case"]
theorem IsTamelyRamifiedWRT.isUnramifiedWRT_adjoin_root (h : IsTamelyRamifiedWRT A L)
    {π : A} (hπ : Irreducible π) {e : ℕ} {β : Ω} (hβ : β ^ e = algebraMap A Ω π)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ e) :
    letI := (TauCeti.IntermediateField.adjoinBaseChange K L β).toAlgebra
    ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮β⟯),
      letI := hDVR
      IsUnramifiedWRT (integralClosure A K⟮β⟯) L⟮β⟯ := by
  let := (TauCeti.IntermediateField.adjoinBaseChange K L β).toAlgebra
  have := FaithfulSMul.trans A K Ω
  have he : e ≠ 0 := Algebra.ne_zero_of_pow_eq_algebraMap_of_injective
    (FaithfulSMul.algebraMap_injective A Ω) hπ.ne_one hβ
  obtain ⟨_, _, _, hβK⟩ := adjoinBaseChange_towers_and_pow (A := A) (K := K) (L := L) hβ
  have hgenK : K⟮AdjoinSimple.gen K β⟯ = ⊤ := adjoin_adjoinSimple_gen_eq_top β
  let A₁ := integralClosure A K⟮β⟯
  have : IsDiscreteValuationRing A₁ :=
    IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
      hπ hβK hgenK
  have : IsFractionRing A₁ K⟮β⟯ :=
    IsDiscreteValuationRing.isFractionRing_integralClosure_of_pow_eq_of_irreducible hπ hβK hgenK
  have : FiniteDimensional K⟮β⟯ L⟮β⟯ :=
    TauCeti.IntermediateField.finiteDimensional_adjoinBaseChange K L β
  have : Algebra.IsSeparable K⟮β⟯ L⟮β⟯ :=
    TauCeti.IntermediateField.isSeparable_adjoinBaseChange K L β
  have : IsScalarTower A A₁ L⟮β⟯ := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A₁ K⟮β⟯ L⟮β⟯,
      ← IsScalarTower.algebraMap_apply A A₁ K⟮β⟯,
      ← IsScalarTower.algebraMap_apply A K⟮β⟯ L⟮β⟯]
  have hβA₁_mem : AdjoinSimple.gen K β ∈ A₁ := (mem_integralClosure_iff _ _).mpr
    (IsIntegral.of_pow (Nat.pos_of_ne_zero he) (hβK ▸ isIntegral_algebraMap))
  let βA₁ : A₁ := ⟨AdjoinSimple.gen K β, hβA₁_mem⟩
  have hβA₁_irred : Irreducible βA₁ :=
    IsDiscreteValuationRing.irreducible_mk_of_pow_eq_of_irreducible hπ hβK hgenK hβA₁_mem
  have hβA₁_pow : βA₁ ^ e = algebraMap A A₁ π := Subtype.ext (by
    simpa [βA₁, Subalgebra.coe_algebraMap] using hβK)
  have hβintL : IsIntegral L β :=
    (IsIntegral.of_pow (Nat.pos_of_ne_zero he) (hβ ▸ isIntegral_algebraMap (R := A))).tower_top
  have hβgen : Algebra.adjoin L {algebraMap A₁ L⟮β⟯ βA₁} = ⊤ := by
    have hval : algebraMap A₁ L⟮β⟯ βA₁ = AdjoinSimple.gen L β :=
      TauCeti.IntermediateField.adjoinBaseChange_gen K L β
    rw [hval, ← IntermediateField.adjoin.powerBasis_gen hβintL]
    exact (IntermediateField.adjoin.powerBasis hβintL).adjoin_gen_eq_top
  exact ⟨inferInstance,
    isUnramifiedWRT_of_dvr_adjoin_root (K := K) (K₁ := K⟮β⟯)
      h hπ he βA₁ hβA₁_irred hβA₁_pow hβgen hdvd⟩

/-- **Kummer characterization of tame ramification.** Let `A` be a discrete valuation ring with
fraction field `K` and uniformizer `π`, let `L / K` be a finite separable extension, and let `Ω`
be an algebraically closed field extending `L`. The following are equivalent:

1. `L` is tamely ramified with respect to `A`;
2. there exist `e` invertible in `κ_A` and an `e`-th root `β ∈ Ω` of `π` such that `L(β)` is
   unramified with respect to `integralClosure A K(β)`;
3. there exists `e₀` invertible in `κ_A` such that for every multiple `e` of `e₀` and every
   `e`-th root `β ∈ Ω` of `π`, `L(β)` is unramified with respect to `integralClosure A K(β)`. -/
@[stacks 0EXW]
theorem isTamelyRamifiedWRT_tfae [IsAlgClosed Ω] {π : A} (hπ : Irreducible π) :
    List.TFAE [
      IsTamelyRamifiedWRT A L,
      ∃ (e : ℕ) (β : Ω), IsUnit (e : A ⧸ maximalIdeal A) ∧ β ^ e = algebraMap A Ω π ∧
        letI := (TauCeti.IntermediateField.adjoinBaseChange K L β).toAlgebra
        ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮β⟯),
          letI := hDVR
          IsUnramifiedWRT (integralClosure A K⟮β⟯) L⟮β⟯,
      ∃ e₀ : ℕ, IsUnit (e₀ : A ⧸ maximalIdeal A) ∧
        ∀ (e : ℕ) (β : Ω), e₀ ∣ e → β ^ e = algebraMap A Ω π →
          letI := (TauCeti.IntermediateField.adjoinBaseChange K L β).toAlgebra
          ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮β⟯),
            letI := hDVR
            IsUnramifiedWRT (integralClosure A K⟮β⟯) L⟮β⟯
    ] := by
  tfae_have 1 → 3 := fun h ↦ by
    obtain ⟨e₀, he₀, hdvd⟩ := h.exists_isUnit_ramificationIdx_dvd K
    exact ⟨e₀, he₀, fun e β he hβ ↦
      h.isUnramifiedWRT_adjoin_root hπ hβ fun P _ _ ↦ (hdvd P).trans he⟩
  tfae_have 3 → 2 := by
    rintro ⟨e₀, he₀, h⟩
    have he₀_pos : 0 < e₀ := Nat.pos_of_ne_zero (by rintro rfl; simp at he₀)
    obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A Ω π) he₀_pos
    exact ⟨e₀, β, he₀, hβ, h e₀ β dvd_rfl hβ⟩
  tfae_have 2 → 1 := by
    rintro ⟨e, β, he, hβ, hDVR, hU⟩
    let := (TauCeti.IntermediateField.adjoinBaseChange K L β).toAlgebra
    obtain ⟨_, _, _, hβK⟩ := adjoinBaseChange_towers_and_pow (A := A) (K := K) (L := L) hβ
    exact IsDiscreteValuationRing.isTamelyRamifiedWRT_of_isUnramifiedWRT_of_pow_eq_of_irreducible
      hπ he hβK (adjoin_adjoinSimple_gen_eq_top β) hU
  tfae_finish

/-- A finite separable extension `L / K` is tamely ramified with respect to a discrete valuation
ring `A` with uniformizer `π` iff, in an algebraically closed extension `Ω` of `L`, there exist
`e` invertible in `κ_A` and an `e`-th root `β` of `π` with `L(β)` unramified over
`integralClosure A K(β)`. -/
@[stacks 0EXW "(1) ↔ (2)"]
theorem isTamelyRamifiedWRT_iff_exists_kummer [IsAlgClosed Ω] {π : A} (hπ : Irreducible π) :
    IsTamelyRamifiedWRT A L ↔
      ∃ (e : ℕ) (β : Ω), IsUnit (e : A ⧸ maximalIdeal A) ∧ β ^ e = algebraMap A Ω π ∧
        letI := (TauCeti.IntermediateField.adjoinBaseChange K L β).toAlgebra
        ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮β⟯),
          letI := hDVR
          IsUnramifiedWRT (integralClosure A K⟮β⟯) L⟮β⟯ :=
  (isTamelyRamifiedWRT_tfae (K := K) (Ω := Ω) hπ).out 1 2

end TauCeti.Algebra

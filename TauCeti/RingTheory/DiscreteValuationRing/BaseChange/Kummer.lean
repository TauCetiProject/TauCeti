/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.TFAE
public import TauCeti.FieldTheory.IntermediateField.Adjoin.BaseChange
public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Tactic.TFAE
import TauCeti.Algebra.Algebra.Hom
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.RingTheory.DiscreteValuationRing.AbhyankarModel.Localization
import TauCeti.RingTheory.DiscreteValuationRing.BaseChange.Unramified
import TauCeti.RingTheory.DiscreteValuationRing.Kummer
import TauCeti.RingTheory.Localization.Integral
import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing

/-!
# Adjoining a root of a uniformizer and the Kummer characterization of tame ramification

Let `A` be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let `L / K`
be a finite extension.

* If `L / K` is separable and unramified with respect to `A`, adjoining any `n`-th root `α` of `π`
  (`n ≠ 0`) to both fields gives an extension `L(α) / K(α)` unramified with respect to the
  integral closure of `A` in `K(α)`.
* More generally, if `L` is tamely ramified with respect to `A` and every maximal ideal of the
  integral closure of `A` in `L` has ramification index over `A` dividing `n`, then adjoining an
  `n`-th root `α` of `π` makes `L(α)` unramified with respect to the integral closure of `A` in
  `K(α)` (the Kummer case of Abhyankar's lemma for discrete valuation rings, Stacks, Lemma 15.116.4
  (0BRM)). Neither separability of `L / K` nor invertibility of `n` in the residue field of `A` is
  needed here.
* For `L / K` finite and separable, `L` is tamely ramified with respect to `A` if and only if there
  exist `e` invertible in the residue field of `A` and a finite separable extension of
  `K(π ^ (1 / e))` containing `L` that is unramified with respect to the integral closure of `A` in
  `K(π ^ (1 / e))`, if and only if there exists `e₀` invertible in the residue field of `A` such
  that this holds at exponent `e₀ * d` for every `d` invertible in the residue field of `A`
  (Stacks, Lemma 15.116.7 (0EXW)).

## Main results

* `TauCeti.Algebra.IsUnramifiedWRT.adjoin_root` and
  `TauCeti.Algebra.IsUnramifiedWRT.exists_adjoin_root`: adjoining a root of a uniformizer preserves
  unramifiedness.
* `TauCeti.Algebra.IsTamelyRamifiedWRT.exists_isUnit_forall_ramificationIdx_dvd`: when `L` is
  tamely ramified with respect to `A`, the ramification indices of the maximal ideals of the
  integral closure have a common multiple invertible in the residue field of `A`.
* `TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_of_pow_eq_of_irreducible`,
  `TauCeti.Algebra.IsTamelyRamifiedWRT.adjoin_root`, and
  `TauCeti.Algebra.IsTamelyRamifiedWRT.exists_adjoin_root`: adjoining an `n`-th root of a
  uniformizer whose exponent is divisible by every maximal ideal's ramification index kills
  ramification over the Kummer base.
* `TauCeti.Algebra.isTamelyRamifiedWRT_tfae` and
  `TauCeti.Algebra.isTamelyRamifiedWRT_iff_exists_kummer`: all three equivalent clauses of the
  Kummer characterization of tame ramification (Stacks, Lemma 15.116.7 (0EXW)).

## References

* [Stacks Project, Lemma 15.116.4](https://stacks.math.columbia.edu/tag/0BRM).
* [Stacks Project, Lemma 15.116.7](https://stacks.math.columbia.edu/tag/0EXW).
* [Stacks Project, Lemma 15.116.9](https://stacks.math.columbia.edu/tag/0EXY).
-/

public section

universe u

open scoped TensorProduct
open IsLocalRing _root_.IntermediateField

namespace TauCeti.Algebra

section Unramified

variable {A K L Ω : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
  [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω] [Algebra A Ω] [IsScalarTower K L Ω]
  [IsScalarTower A K Ω]

/-- Adjoining a root of a uniformizer to both fields preserves unramifiedness. The integral
closure in the new base field is a discrete valuation ring, even for a wild root extraction.
The algebra structure on `L(α)` is induced by the canonical inclusion `K(α) → L(α)`. -/
theorem IsUnramifiedWRT.adjoin_root (h : IsUnramifiedWRT A L) {π : A}
    (hπ : Irreducible π) {n : ℕ} (hn : n ≠ 0) {α : Ω}
    (hα : α ^ n = algebraMap A Ω π) :
    letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
    ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮α⟯),
      letI := hDVR
      IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ := by
  have : IsScalarTower A L Ω := .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A K Ω, IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply K L Ω]
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
  have hαK : AdjoinSimple.gen K α ^ n = algebraMap A K⟮α⟯ π :=
    Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A K K⟮α⟯,
      IsScalarTower.algebraMap_apply A K Ω] using hα)
  have hgen : K⟮AdjoinSimple.gen K α⟯ = ⊤ :=
    _root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α
  have := IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
    hπ hαK hgen
  have hdegree := IsDiscreteValuationRing.finrank_eq_of_pow_eq_of_irreducible hπ hαK hgen
  have : FiniteDimensional K K⟮α⟯ :=
    Module.finite_of_finrank_pos (hdegree ▸ Nat.pos_of_ne_zero hn)
  have : IsFractionRing (integralClosure A K⟮α⟯) K⟮α⟯ :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K K⟮α⟯ _
  have : IsScalarTower A K L⟮α⟯ := .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A L L⟮α⟯,
      IsScalarTower.algebraMap_apply K L L⟮α⟯, ← IsScalarTower.algebraMap_apply A K L]
  have : IsScalarTower A K⟮α⟯ L⟮α⟯ :=
    IsScalarTower.of_algHom ((TauCeti.IntermediateField.adjoinBaseChange K L α).restrictScalars A)
  have hint : IsIntegral K α :=
    (IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hα ▸ isIntegral_algebraMap (R := A))).tower_top
  refine ⟨inferInstance, ?_⟩
  exact h.baseChange (TauCeti.IntermediateField.adjoinBaseChangeTensorLift K L α)
    (TauCeti.IntermediateField.surjective_adjoinBaseChange_tensorProduct K L hint.tower_top)

/-- In an algebraically closed ambient extension, every positive root degree admits an
unramified extension after adjoining a root of the uniformizer to both fields. In particular,
one may enlarge a Kummer exponent by any positive multiple. -/
theorem IsUnramifiedWRT.exists_adjoin_root [IsAlgClosed Ω] (h : IsUnramifiedWRT A L)
    {π : A} (hπ : Irreducible π) {n : ℕ} (hn : 0 < n) :
    ∃ α : Ω, α ^ n = algebraMap A Ω π ∧
      letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
      ∃ hDVR : IsDiscreteValuationRing (integralClosure A K⟮α⟯),
        letI := hDVR
        IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A Ω π) hn
  exact ⟨α, hα, h.adjoin_root hπ hn.ne' hα⟩

end Unramified

section TamelyRamified

/-- For a finite extension `L` of the fraction field `K` of a discrete valuation ring `A` that is
tamely ramified with respect to `A`, there is a natural number invertible in the residue field of
`A` that is divisible by the ramification index over `A` of every maximal ideal of the integral
closure of `A` in `L`. -/
theorem IsTamelyRamifiedWRT.exists_isUnit_forall_ramificationIdx_dvd
    {A L : Type*} (K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L] [FiniteDimensional K L] (h : IsTamelyRamifiedWRT A L) :
    ∃ e : ℕ, IsUnit (e : A ⧸ maximalIdeal A) ∧
      ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal], P.ramificationIdx A ∣ e := by
  have : IsDedekindDomain (integralClosure A L) :=
    TauCeti.integralClosure.isDedekindDomain A K L
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  refine ⟨∏ Q : (maximalIdeal A).primesOver (integralClosure A L), Q.1.ramificationIdx A, ?_, ?_⟩
  · rw [Nat.cast_prod]
    refine Finset.prod_induction _ IsUnit (fun _ _ ↦ IsUnit.mul) isUnit_one fun Q _ ↦ ?_
    have := Q.2.1
    have := Q.2.2
    have : Q.1.IsMaximal := .of_liesOver_isMaximal Q.1 (maximalIdeal A)
    exact (isTamelyRamifiedWRT_def.mp h Q.1).2
  · intro P _
    have hP : P ∈ (maximalIdeal A).primesOver (integralClosure A L) :=
      ⟨inferInstance, ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A P)).symm⟩⟩
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨P, hP⟩ : (maximalIdeal A).primesOver _))

/-- If `E` is generated over the fraction field `L` of `B` by an element `β` integral over `L`, and
`S` is the localization of a domain `B₁` over `B` with fraction field `E`, then every element of `S`
becomes a polynomial in `β` over `Localization.AtPrime P` after multiplication by a nonzero element
of `Localization.AtPrime P`. -/
private theorem exists_mul_mem_adjoin_localizationAtPrime
    {B L B₁ E : Type*} [CommRing B] [Field L] [Algebra B L] [IsFractionRing B L]
    [CommRing B₁] [Algebra B B₁] [Field E] [Algebra B E] [Algebra L E]
    [Algebra B₁ E] [IsScalarTower B L E] [IsScalarTower B B₁ E] [IsFractionRing B₁ E]
    (P : Ideal B) [P.IsPrime] (Q : Ideal B₁) [Q.IsPrime] [Q.LiesOver P]
    {b : B₁} (hint : IsIntegral L (algebraMap B₁ E b)) (hgen : L⟮algebraMap B₁ E b⟯ = ⊤) :
    letI := Localization.AtPrime.algebraOfLiesOver P Q
    ∀ c : Localization.AtPrime Q, ∃ s : Localization.AtPrime P, s ≠ 0 ∧
      algebraMap (Localization.AtPrime P) (Localization.AtPrime Q) s * c ∈
        Algebra.adjoin (Localization.AtPrime P) {algebraMap B₁ (Localization.AtPrime Q) b} := by
  have : IsDomain B := (IsFractionRing.injective B L).isDomain
  have : IsDomain B₁ := (IsFractionRing.injective B₁ E).isDomain
  let := Localization.AtPrime.algebraOfLiesOver P Q
  let g : Localization.AtPrime Q →+* E :=
    IsLocalization.map E (M := Q.primeCompl) (T := nonZeroDivisors B₁) (RingHom.id B₁)
      Q.primeCompl_le_nonZeroDivisors
  let := g.toAlgebra
  have : IsScalarTower B₁ (Localization.AtPrime Q) E := .of_algebraMap_eq fun x ↦
    (IsLocalization.map_eq (M := Q.primeCompl) (T := nonZeroDivisors B₁)
      (S := Localization.AtPrime Q) (Q := E) (g := RingHom.id B₁)
      Q.primeCompl_le_nonZeroDivisors x).symm
  have : IsScalarTower B (Localization.AtPrime Q) E := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply B B₁ E,
      IsScalarTower.algebraMap_apply B B₁ (Localization.AtPrime Q),
      IsScalarTower.algebraMap_apply B₁ (Localization.AtPrime Q) E]
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    Q.primeCompl (Localization.AtPrime Q) E
  let j : Localization.AtPrime Q →ₐ[B] E := IsScalarTower.toAlgHom B (Localization.AtPrime Q) E
  have hj_inj : Function.Injective j := IsFractionRing.injective (Localization.AtPrime Q) E
  have hjb : j (algebraMap B₁ (Localization.AtPrime Q) b) = algebraMap B₁ E b :=
    (IsScalarTower.algebraMap_apply B₁ (Localization.AtPrime Q) E b).symm
  have htop : Algebra.adjoin L ({algebraMap B₁ E b} : Set E) = ⊤ := by
    rw [← adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hgen, top_toSubalgebra]
  intro c
  obtain ⟨t, ht⟩ := multiple_mem_adjoin_of_mem_localization_adjoin
    (nonZeroDivisors B) L ({algebraMap B₁ E b} : Set E) (j c) (htop ▸ Algebra.mem_top)
  have ht0 : (t : B) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp t.2
  refine ⟨algebraMap B (Localization.AtPrime P) t, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (IsLocalization.injective _ P.primeCompl_le_nonZeroDivisors)).mpr ht0
  · rw [← IsScalarTower.algebraMap_apply B (Localization.AtPrime P) (Localization.AtPrime Q)]
    -- Pull `t • j c ∈ B[β]` back from `E` to `Localization.AtPrime Q` along the injection `j`,
    -- then extend coefficients from `B` to `Localization.AtPrime P`.
    have hmem : algebraMap B (Localization.AtPrime Q) t * c ∈
        Algebra.adjoin B ({algebraMap B₁ (Localization.AtPrime Q) b} : Set _) := by
      rw [← hjb, ← Set.image_singleton, ← AlgHom.map_adjoin] at ht
      obtain ⟨z, hz, hzc⟩ := ht
      have hzc' : j z = j (algebraMap B (Localization.AtPrime Q) t * c) := by
        rw [map_mul, j.commutes, ← Algebra.smul_def, ← Submonoid.smul_def]
        exact hzc
      exact hj_inj hzc' ▸ hz
    exact Algebra.adjoin_le (R := B)
      (S := (Algebra.adjoin (Localization.AtPrime P)
        {algebraMap B₁ (Localization.AtPrime Q) b}).restrictScalars B)
      (Set.singleton_subset_iff.mpr (Algebra.self_mem_adjoin_singleton _ _)) hmem

/-- At a maximal ideal `P` of the Dedekind domain `B` over the discrete valuation ring `A`, the
localization `B_P` is a discrete valuation ring dominating `A` whose uniformizer `ϖ` satisfies
`π = u * ϖ ^ e` for a unit `u`, where `e = P.ramificationIdx A`; when `L` is tamely ramified at
`P`, `e` is invertible in `B_P` and `ResidueField B_P` is separable over `ResidueField A`. -/
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
  have hP_ne : P ≠ ⊥ := fun hP ↦ hπ.ne_zero <|
    (FaithfulSMul.algebraMap_injective A B).eq_iff.mp <| by
      simpa [hP] using (Ideal.mem_of_liesOver P (maximalIdeal A) π).mp
        ((mem_maximalIdeal π).mpr hπ.not_isUnit)
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP_ne
    (Localization.AtPrime P)
  have : FaithfulSMul A (Localization.AtPrime P) := by
    rw [faithfulSMul_iff_algebraMap_injective,
      IsScalarTower.algebraMap_eq A B (Localization.AtPrime P)]
    exact (IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors).comp
      (FaithfulSMul.algebraMap_injective A B)
  let : IsLocalHom (algebraMap A (Localization.AtPrime P)) := ⟨fun a ha ↦ by
    by_contra ha'
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P
      (algebraMap A B a)).mpr
      ((Ideal.mem_of_liesOver P (maximalIdeal A) a).mp ((mem_maximalIdeal a).mpr ha'))
      (by rwa [IsScalarTower.algebraMap_apply A B (Localization.AtPrime P)] at ha)⟩
  have heA : IsUnit ((P.ramificationIdx A : ℕ) : A) :=
    (isUnit_map_iff (IsLocalRing.residue A) _).mp (by rw [map_natCast]; exact he_unit)
  have heBP : IsUnit ((P.ramificationIdx A : ℕ) : Localization.AtPrime P) := by
    simpa using heA.map (algebraMap A (Localization.AtPrime P))
  -- `B ⧸ P ≃ ResidueField (Localization.AtPrime P)` over `A ⧸ maximalIdeal A = ResidueField A`.
  let τ :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)).restrictScalars A
  have hsepBP : Algebra.IsSeparable (ResidueField A) (ResidueField (Localization.AtPrime P)) :=
    (AlgEquiv.Algebra.isSeparable_iff
      (τ.extendScalarsOfSurjective (S := A ⧸ maximalIdeal A) Ideal.Quotient.mk_surjective)).mp hsep
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
  have hmap_ne : (maximalIdeal A).map (algebraMap A (Localization.AtPrime P)) ≠ ⊥ := by
    intro hbot
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A (Localization.AtPrime P))).mpr
      hπ.ne_zero (Ideal.mem_bot.mp
        (hbot ▸ Ideal.mem_map_of_mem _ ((mem_maximalIdeal π).mpr hπ.not_isUnit)))
  have hpow := IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx hmap_ne
  have he_eq : P.ramificationIdx A = (maximalIdeal (Localization.AtPrime P)).ramificationIdx A :=
    Ideal.IsDedekindDomain.ramificationIdx_eq_of_map_eq_pow (maximalIdeal A) P _ hpow
  rw [← he_eq, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hϖ.maximalIdeal_eq,
    Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at hpow
  obtain ⟨u, hu⟩ := hpow.symm
  exact ⟨inferInstance, inferInstance, heBP, hsepBP, ϖ, u, hϖ, u.isUnit, by rw [← hu, mul_comm]⟩

/-- If `A → A₁ → B₁` is a tower of commutative rings with `A` local, `A₁` a discrete valuation ring,
and `B₁` a domain, `Q` is a maximal ideal of `B₁` over `maximalIdeal A₁` whose localization
`Localization.AtPrime Q` is a discrete valuation ring dominating `A` in which a uniformizer `ϖ₁` of
`A₁` maps to a uniformizer, and `ResidueField (Localization.AtPrime Q)` is separable over
`ResidueField A`, then `Q` has ramification index `1` over `A₁` and `B₁ ⧸ Q` is separable over
`A₁ ⧸ maximalIdeal A₁`. -/
private theorem ramificationIdx_eq_one_and_isSeparable_of_irreducible_localizationAtPrime
    {A A₁ B₁ : Type*} [CommRing A] [IsLocalRing A]
    [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁] [Algebra A A₁]
    [CommRing B₁] [IsDomain B₁] [Algebra A B₁] [Algebra A₁ B₁] [IsScalarTower A A₁ B₁]
    {ϖ₁ : A₁} (hϖ₁ : Irreducible ϖ₁)
    (Q : Ideal B₁) [Q.IsMaximal] [Q.LiesOver (maximalIdeal A₁)]
    [IsDiscreteValuationRing (Localization.AtPrime Q)]
    [IsLocalHom (algebraMap A (Localization.AtPrime Q))]
    (hirr : Irreducible (algebraMap B₁ (Localization.AtPrime Q) (algebraMap A₁ B₁ ϖ₁)))
    (hsep : Algebra.IsSeparable (ResidueField A) (ResidueField (Localization.AtPrime Q))) :
    Q.ramificationIdx A₁ = 1 ∧
      Algebra.IsSeparable (A₁ ⧸ maximalIdeal A₁) (B₁ ⧸ Q) := by
  have hmap1 : (maximalIdeal A₁).map (algebraMap A₁ (Localization.AtPrime Q)) =
      maximalIdeal (Localization.AtPrime Q) ^ 1 := by
    rw [pow_one, hϖ₁.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      IsScalarTower.algebraMap_apply A₁ B₁ (Localization.AtPrime Q), hirr.maximalIdeal_eq]
  refine ⟨Ideal.IsDedekindDomain.ramificationIdx_eq_of_map_eq_pow (maximalIdeal A₁) Q 1 hmap1, ?_⟩
  have : IsLocalHom (algebraMap A₁ (Localization.AtPrime Q)) :=
    ((local_hom_tfae (algebraMap A₁ (Localization.AtPrime Q))).out 3 1).mp (by simpa using hmap1.le)
  have : IsScalarTower A A₁ (Localization.AtPrime Q) := .to₁₂₄ A A₁ B₁ (Localization.AtPrime Q)
  have : IsLocalHom ((algebraMap A₁ (Localization.AtPrime Q)).comp (algebraMap A A₁)) := by
    rw [← IsScalarTower.algebraMap_eq A A₁ (Localization.AtPrime Q)]
    infer_instance
  have : IsLocalHom (algebraMap A A₁) :=
    isLocalHom_of_comp (algebraMap A A₁) (algebraMap A₁ (Localization.AtPrime Q))
  have hsepA₁ : Algebra.IsSeparable (ResidueField A₁) (ResidueField (Localization.AtPrime Q)) :=
    Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A) (ResidueField A₁)
      (ResidueField (Localization.AtPrime Q))
  let σ :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal Q (Localization.AtPrime Q)).restrictScalars A₁
  exact (AlgEquiv.Algebra.isSeparable_iff
    (σ.extendScalarsOfSurjective
      (S := A₁ ⧸ maximalIdeal A₁) Ideal.Quotient.mk_surjective)).mpr hsepA₁

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
    rw [faithfulSMul_iff_algebraMap_injective, Localization.AtPrime.algebraMap_eq P Q]
    unfold Localization.localRingHom
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
  exact ramificationIdx_eq_one_and_isSeparable_of_irreducible_localizationAtPrime
    hϖ₁ Q hirrS hsepAS

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
  have : IsFractionRing (integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L _
  have : IsIntegrallyClosed (integralClosure A E) :=
    _root_.integralClosure.isIntegrallyClosedOfFiniteExtension K
  have : IsFractionRing (integralClosure A E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K E _
  have : FaithfulSMul A (integralClosure A L) :=
    have := FaithfulSMul.trans A K L
    .tower_bot A (integralClosure A L) L
  have : FaithfulSMul (integralClosure A L) (integralClosure A E) :=
    have := FaithfulSMul.trans (integralClosure A L) L E
    .tower_bot _ _ E
  have hα₁A₁ : α₁ ∈ integralClosure A K₁ :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hα₁ ▸ isIntegral_algebraMap)
  have hϖ₁ : Irreducible (⟨α₁, hα₁A₁⟩ : integralClosure A K₁) :=
    IsDiscreteValuationRing.irreducible_mk_of_pow_eq_of_irreducible hπ hα₁ hgenK hα₁A₁
  let b : integralClosure A E :=
    algebraMap (integralClosure A K₁) (integralClosure A E) ⟨α₁, hα₁A₁⟩
  have hbE : algebraMap (integralClosure A E) E b = algebraMap K₁ E α₁ :=
    IsScalarTower.algebraMap_apply (integralClosure A K₁) (integralClosure A E) E ⟨α₁, hα₁A₁⟩
  intro Q _ _
  have : (maximalIdeal (integralClosure A K₁)).LiesOver (maximalIdeal A) :=
    ⟨(eq_maximalIdeal (Ideal.IsMaximal.under A _)).symm⟩
  have : Q.LiesOver (maximalIdeal A) :=
    .trans Q (maximalIdeal (integralClosure A K₁)) (maximalIdeal A)
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
        show (b : E) = algebraMap K₁ E α₁ from hbE, ← map_pow, hα₁,
        ← IsScalarTower.algebraMap_apply A K₁ E]
  exact ramificationIdx_eq_one_and_isSeparable_of_tame_liesOver hϖ₁ P Q hϖ hu heBP hd hsepBP hπBP
    hb_pow (exists_mul_mem_adjoin_localizationAtPrime P Q b.2.tower_top (hbE.symm ▸ hgenL))

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
    [Field E] [Algebra A E] [Algebra K E] [Algebra L E] [Algebra K₁ E]
    [IsScalarTower A K E] [IsScalarTower K L E] [IsScalarTower K K₁ E]
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {n : ℕ}
    {α₁ : K₁} (hα₁ : α₁ ^ n = algebraMap A K₁ π) (hgenK : K⟮α₁⟯ = ⊤)
    (hgenL : L⟮algebraMap K₁ E α₁⟯ = ⊤)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal], P.ramificationIdx A ∣ n) :
    ∃ hDVR : IsDiscreteValuationRing (integralClosure A K₁),
      letI := hDVR
      IsUnramifiedWRT (integralClosure A K₁) E := by
  have : FaithfulSMul A K₁ := .trans A K K₁
  have hn : n ≠ 0 := _root_.Algebra.ne_zero_of_pow_eq_algebraMap_of_injective
    (FaithfulSMul.algebraMap_injective A K₁) hπ.ne_one hα₁
  have hDVR :=
    IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
      hπ hα₁ hgenK
  have : IsScalarTower A L E := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K E, IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply K L E]
  have : IsScalarTower A K₁ E := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K E, IsScalarTower.algebraMap_apply A K K₁,
      ← IsScalarTower.algebraMap_apply K K₁ E]
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

/-- Adjoining an `n`-th root `α` of a uniformizer `π` of `A` to both `K` and `L`, where every
maximal ideal of `integralClosure A L` has ramification index dividing `n`, produces an extension
`L(α)` unramified with respect to the integral closure of `A` in `K(α)`. Neither separability of
`L / K` nor invertibility of `n` in the residue field of `A` is needed. -/
@[stacks 0BRM "Kummer case, adjoining a root in an ambient field"]
theorem IsTamelyRamifiedWRT.adjoin_root
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
  have : IsScalarTower A L Ω := .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A K Ω, IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply K L Ω]
  have : IsScalarTower A K L⟮α⟯ := .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A L L⟮α⟯,
      IsScalarTower.algebraMap_apply K L L⟮α⟯, ← IsScalarTower.algebraMap_apply A K L]
  have hαK : AdjoinSimple.gen K α ^ n = algebraMap A K⟮α⟯ π :=
    Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A K K⟮α⟯,
      IsScalarTower.algebraMap_apply A K Ω] using hα)
  have hgenK : K⟮AdjoinSimple.gen K α⟯ = ⊤ :=
    _root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α
  have hgenL : L⟮algebraMap K⟮α⟯ L⟮α⟯ (AdjoinSimple.gen K α)⟯ = ⊤ := by
    rw [AlgHom.algebraMap_toAlgebra_apply, TauCeti.IntermediateField.adjoinBaseChange_gen]
    exact _root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α
  exact h.isUnramifiedWRT_of_pow_eq_of_irreducible hπ hαK hgenK hgenL hdvd

/-- In an algebraically closed ambient field `Ω`, for every positive `n` divisible by the
ramification indices of all maximal ideals of `integralClosure A L`, there is an `n`-th root `α` of
the uniformizer `π` making `L(α)` unramified with respect to `integralClosure A K(α)`. -/
theorem IsTamelyRamifiedWRT.exists_adjoin_root
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
  exact ⟨α, hα, h.adjoin_root hπ hα hdvd⟩

end TamelyRamified

section KummerCharacterization

/-- Constructing the finite separable unramified Kummer witness of exponent `n` from tame
ramification when `n > 0` is divisible by every maximal ideal's ramification index. -/
private theorem exists_unramified_kummer_of_forall_ramificationIdx_dvd
    {A K : Type*} {L : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {n : ℕ} (hn : 0 < n)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal], P.ramificationIdx A ∣ n) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E) (_ : Algebra L E)
      (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E)
      (_ : IsDiscreteValuationRing (integralClosure A K⟮β⟯)),
      β ^ n = algebraMap A E π ∧
        FiniteDimensional K⟮β⟯ E ∧ Algebra.IsSeparable K⟮β⟯ E ∧
        IsUnramifiedWRT (integralClosure A K⟮β⟯) E := by
  let Ω : Type u := AlgebraicClosure L
  have : IsScalarTower A K Ω := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A L Ω, IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply K L Ω]
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A Ω π) hn
  let β : L⟮α⟯ := AdjoinSimple.gen L α
  have : IsScalarTower A K L⟮α⟯ := .of_algebraMap_eq fun a ↦
    Subtype.ext (IsScalarTower.algebraMap_apply A K Ω a)
  have hβ : β ^ n = algebraMap A L⟮α⟯ π :=
    Subtype.ext (by simpa [β, IsScalarTower.algebraMap_apply A L L⟮α⟯,
      IsScalarTower.algebraMap_apply A L Ω] using hα)
  have hβK : AdjoinSimple.gen K β ^ n = algebraMap A K⟮β⟯ π :=
    Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A K K⟮β⟯,
      IsScalarTower.algebraMap_apply A K L⟮α⟯] using hβ)
  have hgenK : K⟮AdjoinSimple.gen K β⟯ = ⊤ :=
    _root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top β
  have hgenL : L⟮algebraMap K⟮β⟯ L⟮α⟯ (AdjoinSimple.gen K β)⟯ = ⊤ :=
    _root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α
  obtain ⟨hDVR, hunr⟩ := h.isUnramifiedWRT_of_pow_eq_of_irreducible hπ hβK hgenK hgenL hdvd
  have hintL : IsIntegral L β :=
    IsIntegral.of_pow hn (by rw [hβ, IsScalarTower.algebraMap_apply A K L⟮α⟯,
      IsScalarTower.algebraMap_apply K L L⟮α⟯]; exact isIntegral_algebraMap)
  -- `K(β) ⊗[K] L` maps onto `L(α)` since `L(α) = L(β)`, making `L(α)` finite separable over `K(β)`.
  let ψ : K⟮β⟯ ⊗[K] L →ₐ[K⟮β⟯] L⟮α⟯ :=
    Algebra.TensorProduct.lift (Algebra.ofId K⟮β⟯ L⟮α⟯) (IsScalarTower.toAlgHom K L L⟮α⟯)
      fun _ _ ↦ .all _ _
  have hψ : Function.Surjective ψ := by
    have htop : Algebra.adjoin L ({β} : Set L⟮α⟯) = ⊤ := by
      rw [← adjoin_simple_toSubalgebra_of_isAlgebraic hintL.isAlgebraic,
        _root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α, top_toSubalgebra]
    intro x
    let R : Subalgebra L L⟮α⟯ :=
      { ψ.range.toSubring with algebraMap_mem' := fun l ↦ ⟨1 ⊗ₜ[K] l, by simp [ψ]⟩ }
    have hβR : β ∈ R := ⟨AdjoinSimple.gen K β ⊗ₜ[K] 1, by simp [ψ]⟩
    exact (AlgHom.mem_range ψ).mp (Algebra.adjoin_le (Set.singleton_subset_iff.mpr hβR)
      (htop ▸ Algebra.mem_top : x ∈ Algebra.adjoin L {β}))
  have : FiniteDimensional K⟮β⟯ L⟮α⟯ := Module.Finite.of_surjective ψ.toLinearMap hψ
  have : Algebra.FormallyUnramified K L := .of_isSeparable K L
  have : Algebra.FormallyUnramified K⟮β⟯ L⟮α⟯ := .of_surjective ψ hψ
  have hsep : Algebra.IsSeparable K⟮β⟯ L⟮α⟯ :=
    (Algebra.FormallyUnramified.iff_isSeparable _ _).mp ‹_›
  exact ⟨L⟮α⟯, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, β, hDVR, hβ, inferInstance, hsep, hunr⟩

variable {A : Type*} (K : Type*) (L : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
  [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- **Kummer characterization of tamely ramified extensions of a discrete valuation ring.**
Let `A` be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let `L / K`
be a finite separable extension. The following are equivalent (Stacks, Lemma 15.116.7):
1. `L` is tamely ramified with respect to `A`;
2. there exist `e` invertible in the residue field of `A` and a finite separable extension `E` of
   `K(π ^ (1 / e))` containing `L` that is unramified with respect to the integral closure of `A`
   in `K(π ^ (1 / e))`;
3. there exists `e₀` invertible in the residue field of `A` such that for every `d` invertible in
   the residue field of `A`, there is a finite separable extension `E` of `K(π ^ (1 / (e₀ * d)))`
   containing `L` that is unramified with respect to the integral closure of `A` in
   `K(π ^ (1 / (e₀ * d)))`. -/
@[stacks 0EXW]
theorem isTamelyRamifiedWRT_tfae {π : A} (hπ : Irreducible π) :
    List.TFAE
      [IsTamelyRamifiedWRT A L,
        ∃ (e : ℕ) (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E)
          (_ : Algebra L E) (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E)
          (_ : IsDiscreteValuationRing (integralClosure A K⟮β⟯)),
          IsUnit (e : A ⧸ maximalIdeal A) ∧ β ^ e = algebraMap A E π ∧
            FiniteDimensional K⟮β⟯ E ∧ Algebra.IsSeparable K⟮β⟯ E ∧
            IsUnramifiedWRT (integralClosure A K⟮β⟯) E,
        ∃ e₀ : ℕ, IsUnit (e₀ : A ⧸ maximalIdeal A) ∧
          ∀ d : ℕ, IsUnit (d : A ⧸ maximalIdeal A) →
            ∃ (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E)
              (_ : Algebra L E) (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E)
              (_ : IsDiscreteValuationRing (integralClosure A K⟮β⟯)),
              β ^ (e₀ * d) = algebraMap A E π ∧
                FiniteDimensional K⟮β⟯ E ∧ Algebra.IsSeparable K⟮β⟯ E ∧
                IsUnramifiedWRT (integralClosure A K⟮β⟯) E] := by
  tfae_have 1 → 3 := fun h ↦ by
    obtain ⟨e₀, he₀, hdvd⟩ := h.exists_isUnit_forall_ramificationIdx_dvd K
    refine ⟨e₀, he₀, fun d hd ↦ ?_⟩
    have hed : IsUnit ((e₀ * d : ℕ) : A ⧸ maximalIdeal A) := by
      rw [Nat.cast_mul]
      exact he₀.mul hd
    let := Ideal.Quotient.field (maximalIdeal A)
    have hne : e₀ * d ≠ 0 := by
      rintro h0
      simp [h0] at hed
    exact exists_unramified_kummer_of_forall_ramificationIdx_dvd h hπ (Nat.pos_of_ne_zero hne)
      (fun P _ ↦ (hdvd P).trans (dvd_mul_right e₀ d))
  tfae_have 3 → 2 := by
    rintro ⟨e₀, he₀, h⟩
    obtain ⟨E, _, _, _, _, _, _, β, hDVR, hβ, hfin, hsep, hunr⟩ := h 1 (by simp)
    exact ⟨e₀, E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, β, hDVR, he₀, by simpa using hβ, hfin, hsep, hunr⟩
  tfae_have 2 → 1 := by
    rintro ⟨e, E, _, _, _, _, _, _, β, _, he, hβ, -, -, hunr⟩
    exact IsDiscreteValuationRing.isTamelyRamifiedWRT_of_isUnramifiedWRT_of_pow_eq_of_irreducible
      hπ he hβ hunr
  tfae_finish

/-- A finite separable extension `L` of the fraction field `K` of a discrete valuation ring `A`
with uniformizer `π` is tamely ramified with respect to `A` if and only if it embeds into a finite
separable extension `E` of some tame Kummer extension `K(π ^ (1 / e))` that is unramified with
respect to the integral closure of `A` in `K(π ^ (1 / e))`. -/
@[stacks 0EXW "(1) ↔ (2)"]
theorem isTamelyRamifiedWRT_iff_exists_kummer {π : A} (hπ : Irreducible π) :
    IsTamelyRamifiedWRT A L ↔
      ∃ (e : ℕ) (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E)
        (_ : Algebra L E) (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E)
        (_ : IsDiscreteValuationRing (integralClosure A K⟮β⟯)),
        IsUnit (e : A ⧸ maximalIdeal A) ∧ β ^ e = algebraMap A E π ∧
          FiniteDimensional K⟮β⟯ E ∧ Algebra.IsSeparable K⟮β⟯ E ∧
          IsUnramifiedWRT (integralClosure A K⟮β⟯) E :=
  (isTamelyRamifiedWRT_tfae K L hπ).out 1 2

end KummerCharacterization

end TauCeti.Algebra

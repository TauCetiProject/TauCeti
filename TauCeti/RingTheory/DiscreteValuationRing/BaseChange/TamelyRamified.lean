/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.FieldTheory.IntermediateField.Adjoin.BaseChange
public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Unramified.Field
import TauCeti.Algebra.Algebra.Hom
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic
import TauCeti.RingTheory.DiscreteValuationRing.AbhyankarModel.Localization
import TauCeti.RingTheory.DiscreteValuationRing.BaseChange.Unramified
import TauCeti.RingTheory.DiscreteValuationRing.Kummer
import TauCeti.RingTheory.IntegralClosure.TensorProduct
import TauCeti.RingTheory.Localization.AtPrime
import TauCeti.RingTheory.Localization.Integral

/-!
# Kummer characterization and base change of tamely ramified extensions

Let `A` be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let `L / K`
be a finite separable extension.

## Kummer characterization (Abhyankar's lemma for discrete valuation rings)

If `L` is tamely ramified with respect to `A`, and `β` is an `e`-th root of `π` in an ambient
extension `Ω` of `L` such that every ramification index `e_P` of `integralClosure A L` over `A`
divides `e`, then `L(β)` is unramified with respect to the discrete valuation ring
`A₁ = integralClosure A K(β)`
(`TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_adjoin_root`).
No invertibility hypothesis on `e` is needed here: at each maximal ideal `Q` of
`integralClosure A₁ L(β)` lying over `P` in `integralClosure A L`, the localization at `Q`
dominates the discrete valuation ring `B_P = (integralClosure A L)_P`, in which `π = u ϖ ^ e_P`
with `e_P` invertible and `e = e_P d` (`d ≠ 0`). Applying the local Abhyankar model
(`TauCeti.irreducible_of_pow_eq_unit_mul_pow` and
`TauCeti.isSeparable_residueField_of_pow_eq_unit_mul_pow`) shows that `β` is a uniformizer at `Q`
and the residue field extension at `Q` is separable over `κ(A₁)`.

In an algebraically closed extension `Ω` of `L`, this yields all three equivalent characterizations
of tame ramification in Stacks, Lemma 15.116.7 (0EXW)
(`TauCeti.Algebra.isTamelyRamifiedWRT_tfae` and
`TauCeti.Algebra.isTamelyRamifiedWRT_iff_exists_kummer`):
`L` is tamely ramified with respect to `A` iff there exist `e` invertible in `κ_A` and an `e`-th
root `β` of `π` with `L(β)` unramified over `integralClosure A K(β)`, iff there exists `e₀`
invertible in `κ_A` such that for every multiple `e` of `e₀` and every `e`-th root `β` of `π`,
`L(β)` is unramified over `integralClosure A K(β)`.

## Base change of tamely ramified extensions

Let `A → A'` be a ring map of discrete valuation rings with compatible fraction fields `K → K'`,
not necessarily local, and let `L'` be a field factor of `K' ⊗[K] L` given by a surjective
`K'`-algebra map `φ : K' ⊗[K] L → L'`. If `L` is tamely ramified with respect to `A`, then `L'`
is tamely ramified with respect to `A'` (`TauCeti.Algebra.IsTamelyRamifiedWRT.baseChange`,
Stacks, Lemma 15.116.9 (0EXY)).

Write `π = u' π' ^ r` in `A'` for a unit `u'` and uniformizer `π'` (allowing `r = 0` when
`A → A'` is non-local). Taking `e` divisible by every ramification index of `L / K` over `A` and
invertible in `κ_A` (hence in `A` and `A'`), we extract `e`-th roots `β` of `π'` and `γ` of `u'`
in an algebraic closure `Ω` of `L'`, and set `α = γ β ^ r`, an `e`-th root of `π`. Then
`B₁ = integralClosure A₁ L(α)` is finite étale over `A₁ = integralClosure A K(α)`, and the
standard tame cover `T = A'₁[y]/(y ^ e − u')` is finite étale over `A'₁ = integralClosure A' K'(β)`
and receives `A₁` via `α ↦ y β ^ r`, so `S = T ⊗[A₁] B₁` is finite étale over `A'₁`. The image
`E` of `K'(β) ⊗[A'₁] S → Ω` is a field containing `L'` and unramified over `A'₁`, hence tamely
ramified over `A'`; descending along `L' ⊆ E` gives tame ramification of `L'` over `A'`.

## Main results

* `TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_adjoin_root`: adjoining an `e`-th root `β`
  of a uniformizer `π` with every ramification index dividing `e` makes `L(β)` unramified over
  `integralClosure A K(β)`.
* `TauCeti.Algebra.isTamelyRamifiedWRT_tfae` and
  `TauCeti.Algebra.isTamelyRamifiedWRT_iff_exists_kummer`: the Kummer characterization of tame
  ramification (Stacks, Lemma 15.116.7 (0EXW)).
* `TauCeti.Algebra.IsTamelyRamifiedWRT.baseChange`: every factor of `K' ⊗[K] L` is tamely ramified
  with respect to `A'` when `L` is tamely ramified with respect to `A`
  (Stacks, Lemma 15.116.9 (0EXY)).

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé X, Lemme 3.6.
* [Stacks Project, Lemma 15.116.4](https://stacks.math.columbia.edu/tag/0BRM).
* [Stacks Project, Lemma 15.116.7](https://stacks.math.columbia.edu/tag/0EXW).
* [Stacks Project, Lemma 15.116.9](https://stacks.math.columbia.edu/tag/0EXY).
-/

public section

open IntermediateField IsLocalRing Polynomial
open scoped TensorProduct

namespace TauCeti.Algebra

section Kummer

variable {A K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L]
  [IsScalarTower A K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

include K in
/-- For a tamely ramified extension `L / K` over a discrete valuation ring `A`, the product of the
ramification indices at all maximal ideals of `integralClosure A L` over `maximalIdeal A` is
invertible in `κ_A` and divisible by every ramification index. -/
private theorem exists_ramificationIdx_dvd_of_isTamelyRamifiedWRT
    (h : IsTamelyRamifiedWRT A L) :
    ∃ e₀ : ℕ, IsUnit (e₀ : A ⧸ maximalIdeal A) ∧
      ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
        P.ramificationIdx A ∣ e₀ := by
  have : IsDedekindDomain (integralClosure A L) := integralClosure.isDedekindDomain A K L
  have : FaithfulSMul A L := .trans A K L
  have : FaithfulSMul A (integralClosure A L) := .tower_bot A _ L
  have : Module.IsTorsionFree A (integralClosure A L) := FaithfulSMul.to_isTorsionFree ..
  refine ⟨∏ P : (maximalIdeal A).primesOver (integralClosure A L), P.1.ramificationIdx A, ?_,
    fun P _ _ ↦ Finset.dvd_prod_of_mem _
      (Finset.mem_univ (⟨P, ⟨inferInstance, inferInstance⟩⟩ :
        (maximalIdeal A).primesOver (integralClosure A L)))⟩
  rw [Nat.cast_prod, IsUnit.prod_univ_iff]
  intro P
  have := P.2.1
  have := P.2.2
  have : P.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P.1 (maximalIdeal A)
  exact (isTamelyRamifiedWRT_def.mp h P.1).2

/-- At a maximal ideal `Q` of an integral closure `B₁` of `A₁` in `L₁ = L(β)`, apply the local
Abhyankar model to `B_P → (B₁)_Q` (for `P = Q ∩ B`) to prove `e(Q | A₁) = 1` and separability
of `κ(Q) / κ(A₁)`. Abstracting `B, B₁, L₁` avoids `Subalgebra.instSMul` instance loops. -/
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
  -- Clear denominators over `B_P` and apply the local Abhyankar model.
  let βS : S := algebraMap B₁ S (algebraMap A₁ B₁ βA₁)
  have hβS_pow : βS ^ (m * d) = algebraMap B_P S ((u : B_P) * ϖ ^ m) := by
    rw [← hmd, ← hπBP, ← IsScalarTower.algebraMap_apply A B_P S,
      IsScalarTower.algebraMap_apply A A₁ S, IsScalarTower.algebraMap_apply A₁ B₁ S,
      ← hβA₁_pow, map_pow, map_pow]
  have hgen : ∀ c : S, ∃ s : B_P,
      s ≠ 0 ∧ algebraMap B_P S s * c ∈ Algebra.adjoin B_P {βS} := by
    intro c
    have hmem : algebraMap S L₁ c ∈ Algebra.adjoin L {algebraMap A₁ L₁ βA₁} :=
      hβgen ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
    obtain ⟨p, hp⟩ := hmem
    obtain ⟨s, hs, hsp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors B_P) p
    refine ⟨s, nonZeroDivisors.ne_zero hs, ?_⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    refine ⟨IsLocalization.integerNormalization (nonZeroDivisors B_P) p,
      IsFractionRing.injective S L₁ ?_⟩
    have hβS_val : algebraMap S L₁ βS = algebraMap A₁ L₁ βA₁ := by
      rw [← IsScalarTower.algebraMap_apply B₁ S L₁,
        ← IsScalarTower.algebraMap_apply A₁ B₁ L₁]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hp ⊢
    rw [aeval_def, map_mul, ← RingHom.comp_apply, hcomp, RingHom.comp_apply,
      Polynomial.hom_eval₂, hcomp, hβS_val, ← eval₂_map, hsp,
      ← IsScalarTower.algebraMap_smul L s p, eval₂_smul, ← aeval_def, hp]
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
    have : IsScalarTower (A ⧸ maximalIdeal A) (B ⧸ P) (B₁ ⧸ Q) :=
      .of_algebraMap_eq fun x ↦ by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [← Ideal.Quotient.algebraMap_eq,
          ← IsScalarTower.algebraMap_apply A (A ⧸ maximalIdeal A) (B₁ ⧸ Q),
          ← IsScalarTower.algebraMap_apply A (A ⧸ maximalIdeal A) (B ⧸ P),
          IsScalarTower.algebraMap_apply A B (B ⧸ P),
          ← IsScalarTower.algebraMap_apply B (B ⧸ P) (B₁ ⧸ Q),
          IsScalarTower.algebraMap_apply B B₁ (B₁ ⧸ Q),
          ← IsScalarTower.algebraMap_apply A B B₁,
          ← IsScalarTower.algebraMap_apply A B₁ (B₁ ⧸ Q)]
    have : Algebra.IsSeparable (A ⧸ maximalIdeal A) (B₁ ⧸ Q) := .trans _ (B ⧸ P) _
    have : IsScalarTower (A ⧸ maximalIdeal A) (A₁ ⧸ maximalIdeal A₁) (B₁ ⧸ Q) :=
      .of_algebraMap_eq fun x ↦ by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [← Ideal.Quotient.algebraMap_eq,
          ← IsScalarTower.algebraMap_apply A (A ⧸ maximalIdeal A) (B₁ ⧸ Q),
          ← IsScalarTower.algebraMap_apply A (A ⧸ maximalIdeal A) (A₁ ⧸ maximalIdeal A₁),
          IsScalarTower.algebraMap_apply A A₁ (A₁ ⧸ maximalIdeal A₁),
          ← IsScalarTower.algebraMap_apply A₁ (A₁ ⧸ maximalIdeal A₁) (B₁ ⧸ Q),
          IsScalarTower.algebraMap_apply A₁ B₁ (B₁ ⧸ Q),
          ← IsScalarTower.algebraMap_apply A A₁ B₁,
          ← IsScalarTower.algebraMap_apply A B₁ (B₁ ⧸ Q)]
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
  have : IsScalarTower A L Ω := .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A K Ω, IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply K L Ω]
  have : IsScalarTower A K L⟮β⟯ := .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A L L⟮β⟯,
      IsScalarTower.algebraMap_apply K L L⟮β⟯, ← IsScalarTower.algebraMap_apply A K L]
  have : IsScalarTower A K⟮β⟯ L⟮β⟯ :=
    IsScalarTower.of_algHom ((TauCeti.IntermediateField.adjoinBaseChange K L β).restrictScalars A)
  have hβK : AdjoinSimple.gen K β ^ e = algebraMap A K⟮β⟯ π :=
    Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A K K⟮β⟯,
      IsScalarTower.algebraMap_apply A K Ω] using hβ)
  have hgenK : K⟮AdjoinSimple.gen K β⟯ = ⊤ := adjoin_adjoinSimple_gen_eq_top β
  let A₁ := integralClosure A K⟮β⟯
  have : IsDiscreteValuationRing A₁ :=
    IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
      hπ hβK hgenK
  have : IsScalarTower A A₁ L⟮β⟯ := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A₁ K⟮β⟯ L⟮β⟯,
      ← IsScalarTower.algebraMap_apply A A₁ K⟮β⟯,
      ← IsScalarTower.algebraMap_apply A K⟮β⟯ L⟮β⟯]
  have hβA₁_mem : AdjoinSimple.gen K β ∈ A₁ := (mem_integralClosure_iff _ _).mpr
    (IsIntegral.of_pow (Nat.pos_of_ne_zero he) (hβK ▸ isIntegral_algebraMap))
  let βA₁ : A₁ := ⟨AdjoinSimple.gen K β, hβA₁_mem⟩
  have hβA₁_irred : Irreducible βA₁ :=
    IsDiscreteValuationRing.irreducible_mk_of_pow_eq_of_irreducible hπ hβK hgenK hβA₁_mem
  have hdegK := IsDiscreteValuationRing.finrank_eq_of_pow_eq_of_irreducible hπ hβK hgenK
  have : FiniteDimensional K K⟮β⟯ :=
    Module.finite_of_finrank_pos (hdegK ▸ Nat.pos_of_ne_zero he)
  have : IsFractionRing A₁ K⟮β⟯ :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K K⟮β⟯ _
  have hβintL : IsIntegral L β :=
    (IsIntegral.of_pow (Nat.pos_of_ne_zero he) (hβ ▸ isIntegral_algebraMap (R := A))).tower_top
  have hsurj := TauCeti.IntermediateField.surjective_adjoinBaseChange_tensorProduct K L hβintL
  have : FiniteDimensional K⟮β⟯ L⟮β⟯ := Module.Finite.of_surjective
    (TauCeti.IntermediateField.adjoinBaseChangeTensorLift K L β).toLinearMap hsurj
  have : Algebra.FormallyUnramified K L :=
    (Algebra.FormallyUnramified.iff_isSeparable K L).mpr inferInstance
  have : Algebra.FormallyUnramified K⟮β⟯ L⟮β⟯ :=
    .of_surjective (A := K⟮β⟯ ⊗[K] L)
      (TauCeti.IntermediateField.adjoinBaseChangeTensorLift K L β) hsurj
  have : Algebra.IsSeparable K⟮β⟯ L⟮β⟯ :=
    (Algebra.FormallyUnramified.iff_isSeparable K⟮β⟯ L⟮β⟯).mp inferInstance
  have hβA₁_pow : βA₁ ^ e = algebraMap A A₁ π := Subtype.ext (by
    simpa [βA₁, Subalgebra.coe_algebraMap] using hβK)
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
    obtain ⟨e₀, he₀, hdvd⟩ := exists_ramificationIdx_dvd_of_isTamelyRamifiedWRT (K := K) h
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
    have : IsScalarTower A L Ω := .of_algebraMap_eq fun a ↦ by
      simp [IsScalarTower.algebraMap_apply A K Ω, IsScalarTower.algebraMap_apply A K L,
        IsScalarTower.algebraMap_apply K L Ω]
    have : IsScalarTower A K L⟮β⟯ := .of_algebraMap_eq fun a ↦ by
      simp [IsScalarTower.algebraMap_apply A L L⟮β⟯,
        IsScalarTower.algebraMap_apply K L L⟮β⟯, ← IsScalarTower.algebraMap_apply A K L]
    have : IsScalarTower A K⟮β⟯ L⟮β⟯ :=
      IsScalarTower.of_algHom
        ((TauCeti.IntermediateField.adjoinBaseChange K L β).restrictScalars A)
    have hβK : AdjoinSimple.gen K β ^ e = algebraMap A K⟮β⟯ π :=
      Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A K K⟮β⟯,
        IsScalarTower.algebraMap_apply A K Ω] using hβ)
    have hK₁ : IsTamelyRamifiedWRT A K⟮β⟯ :=
      (IsDiscreteValuationRing.isTamelyRamifiedWRT_iff_of_pow_eq_of_irreducible hπ hβK
        (adjoin_adjoinSimple_gen_eq_top β)).mpr he
    exact (hK₁.trans hU.isTamelyRamifiedWRT).tower_bot K
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

end Kummer

section BaseChange

/-- Map an `A`-algebra `A₁ ≃ A[x]/(x^e − π)` to the standard tame cover
`T = A'₁[y]/(y^e − u')` by `x ↦ y · β ^ r` when `π = u' π' ^ r` and `β ^ e = π'`, compatibly
with embeddings into `Ω`. -/
private theorem exists_algHom_standardTameCover
    {A A' A₁ A'₁ Ω : Type*}
    [CommRing A] [CommRing A'] [CommRing A₁] [CommRing A'₁] [CommRing Ω]
    [Algebra A A'] [Algebra A A₁] [Algebra A' A'₁] [Algebra A Ω] [Algebra A' Ω]
    [Algebra A₁ Ω] [Algebra A'₁ Ω]
    [IsScalarTower A A' Ω] [IsScalarTower A A₁ Ω] [IsScalarTower A' A'₁ Ω]
    {π : A} {π' : A'} {r : ℕ} {u' : A'ˣ} (hπA' : algebraMap A A' π = (u' : A') * π' ^ r)
    {e : ℕ} {βA'₁ : A'₁} (hβ : βA'₁ ^ e = algebraMap A' A'₁ π')
    {p : A[X]} (hp : p = X ^ e - C π) (eA₁ : A₁ ≃ₐ[A] AdjoinRoot p)
    {γ : Ω} (hγ : γ ^ e = algebraMap A' Ω u')
    (hroot : algebraMap A₁ Ω (eA₁.symm (AdjoinRoot.root p)) =
      γ * algebraMap A'₁ Ω βA'₁ ^ r) :
    let T := TauCeti.standardTameCover A'₁ (algebraMap A' A'₁ u') e
    letI : Algebra A T := ((algebraMap A'₁ T).comp ((algebraMap A' A'₁).comp
      (algebraMap A A'))).toAlgebra
    ∃ (f : A₁ →ₐ[A] T) (gT : T →ₐ[A'₁] Ω),
      ∀ x : A₁, gT (f x) = algebraMap A₁ Ω x := by
  subst hp
  let T := TauCeti.standardTameCover A'₁ (algebraMap A' A'₁ u') e
  let : Algebra A T := ((algebraMap A'₁ T).comp ((algebraMap A' A'₁).comp
    (algebraMap A A'))).toAlgebra
  let img : T := AdjoinRoot.root (X ^ e - C (algebraMap A' A'₁ u')) *
    algebraMap A'₁ T (βA'₁ ^ r)
  have hy : AdjoinRoot.root (X ^ e - C (algebraMap A' A'₁ u')) ^ e =
      algebraMap A'₁ T (algebraMap A' A'₁ u') := by
    have h0 := AdjoinRoot.eval₂_root (X ^ e - C (algebraMap A' A'₁ u'))
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h0
    exact h0
  have himg : eval₂ (Algebra.ofId A T) img (X ^ e - C π) = 0 := by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, AlgHom.coe_toRingHom, Algebra.ofId_apply,
      RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingHom.comp_apply, mul_pow, hy,
      ← map_pow (algebraMap A'₁ T), ← pow_mul, mul_comm r e, pow_mul, hβ,
      ← map_pow (algebraMap A' A'₁), ← map_mul (algebraMap A'₁ T),
      ← map_mul (algebraMap A' A'₁), ← hπA', sub_self]
  let liftF := AdjoinRoot.liftAlgHom (X ^ e - C π) (Algebra.ofId A T) img himg
  let f : A₁ →ₐ[A] T := liftF.comp eA₁.toAlgHom
  have hγ_root : eval₂ (Algebra.ofId A'₁ Ω) γ (X ^ e - C (algebraMap A' A'₁ u')) = 0 := by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, AlgHom.coe_toRingHom, Algebra.ofId_apply,
      ← IsScalarTower.algebraMap_apply A' A'₁ Ω, hγ, sub_self]
  let gT : T →ₐ[A'₁] Ω :=
    AdjoinRoot.liftAlgHom (X ^ e - C (algebraMap A' A'₁ u')) (Algebra.ofId A'₁ Ω) γ hγ_root
  refine ⟨f, gT, fun x ↦ ?_⟩
  have hgT_A (a : A) : gT (algebraMap A T a) = algebraMap A Ω a := by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, RingHom.comp_apply, gT.commutes,
      ← IsScalarTower.algebraMap_apply A' A'₁ Ω, ← IsScalarTower.algebraMap_apply A A' Ω]
  let lhs : TauCeti.standardTameCover A π e →ₐ[A] Ω :=
    { gT.toRingHom.comp liftF.toRingHom with
      commutes' := fun a ↦ by
        simp only [RingHom.toFun_eq_coe, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, liftF.commutes, hgT_A] }
  let rhs : TauCeti.standardTameCover A π e →ₐ[A] Ω :=
    (IsScalarTower.toAlgHom A A₁ Ω).comp eA₁.symm.toAlgHom
  have hagree : lhs = rhs := AdjoinRoot.algHom_ext <| by
    simp only [lhs, rhs, liftF, AlgHom.coe_mk, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, AdjoinRoot.liftAlgHom_root, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      IsScalarTower.coe_toAlgHom', img, map_mul, map_pow, gT, AlgHom.commutes]
    rw [AdjoinRoot.liftAlgHom_root, hroot]
  simpa only [f, lhs, rhs, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_mk,
    RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.symm_apply_apply,
    IsScalarTower.coe_toAlgHom'] using AlgHom.congr_fun hagree (eA₁ x)

/-- Specialize `exists_algHom_standardTameCover` to the Kummer DVRs `A₁ = integralClosure A K(α)`
and `A'₁ = integralClosure A' K'(β)` when `α = γ β ^ r`, `α ^ e = π`, `β ^ e = π'`, and
`γ ^ e = u'`. -/
private theorem exists_algHom_integralClosure_standardTameCover
    {A K A' K' Ω : Type*}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] [CommRing A'] [Field K'] [Algebra A' K'] [Algebra A A']
    [Field Ω] [Algebra A Ω] [Algebra K Ω] [Algebra A' Ω] [Algebra K' Ω]
    [IsScalarTower A K Ω] [IsScalarTower A' K' Ω] [IsScalarTower A A' Ω]
    {π : A} (hπ : Irreducible π) {π' : A'} {r : ℕ} {u' : A'ˣ}
    (hπA' : algebraMap A A' π = (u' : A') * π' ^ r)
    {e : ℕ} (he0 : e ≠ 0) {α β γ : Ω}
    (hαK : AdjoinSimple.gen K α ^ e = algebraMap A K⟮α⟯ π)
    (hβK' : AdjoinSimple.gen K' β ^ e = algebraMap A' K'⟮β⟯ π')
    (hγ : γ ^ e = algebraMap A' Ω u') (hα_eq : α = γ * β ^ r) :
    let A₁ := integralClosure A K⟮α⟯
    let A'₁ := integralClosure A' K'⟮β⟯
    let T := TauCeti.standardTameCover A'₁ (algebraMap A' A'₁ u') e
    letI : Algebra A T := ((algebraMap A'₁ T).comp ((algebraMap A' A'₁).comp
      (algebraMap A A'))).toAlgebra
    ∃ (f : A₁ →ₐ[A] T) (gT : T →ₐ[A'₁] Ω),
      ∀ x : A₁, gT (f x) = algebraMap A₁ Ω x := by
  let A₁ := integralClosure A K⟮α⟯
  let A'₁ := integralClosure A' K'⟮β⟯
  have : IsScalarTower A A₁ Ω := .of_algebraMap_eq fun a ↦ by
    rw [Subalgebra.algebraMap_def, Subalgebra.coe_algebraMap,
      IsScalarTower.algebraMap_apply A K K⟮α⟯,
      ← IsScalarTower.algebraMap_apply K K⟮α⟯ Ω,
      ← IsScalarTower.algebraMap_apply A K Ω]
  have : IsScalarTower A' A'₁ Ω := .of_algebraMap_eq fun a' ↦ by
    rw [Subalgebra.algebraMap_def, Subalgebra.coe_algebraMap,
      IsScalarTower.algebraMap_apply A' K' K'⟮β⟯,
      ← IsScalarTower.algebraMap_apply K' K'⟮β⟯ Ω,
      ← IsScalarTower.algebraMap_apply A' K' Ω]
  have hβA'₁_mem : AdjoinSimple.gen K' β ∈ A'₁ := (mem_integralClosure_iff _ _).mpr
    (IsIntegral.of_pow (Nat.pos_of_ne_zero he0) (hβK' ▸ isIntegral_algebraMap))
  let βA'₁ : A'₁ := ⟨AdjoinSimple.gen K' β, hβA'₁_mem⟩
  have hβA'₁_pow : βA'₁ ^ e = algebraMap A' A'₁ π' := Subtype.ext (by
    simpa [βA'₁, Subalgebra.coe_algebraMap] using hβK')
  have : FaithfulSMul A K⟮α⟯ := .trans A K K⟮α⟯
  have : Module.IsTorsionFree A K⟮α⟯ := FaithfulSMul.to_isTorsionFree ..
  have hαint : IsIntegral A (AdjoinSimple.gen K α) :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero he0) (hαK ▸ isIntegral_algebraMap)
  have hmin : minpoly A (AdjoinSimple.gen K α) = X ^ e - C π :=
    IsDiscreteValuationRing.minpoly_eq_of_pow_eq_of_irreducible hπ hαK
  have heqA₁ : A₁ = Algebra.adjoin A {AdjoinSimple.gen K α} :=
    IsDiscreteValuationRing.integralClosure_eq_adjoin_of_pow_eq_of_irreducible hπ hαK
      (adjoin_adjoinSimple_gen_eq_top α)
  let eA₁ : A₁ ≃ₐ[A] AdjoinRoot (minpoly A (AdjoinSimple.gen K α)) :=
    (Subalgebra.equivOfEq _ _ heqA₁).trans (minpoly.equivAdjoin hαint).symm
  have hroot : algebraMap A₁ Ω
      (eA₁.symm (AdjoinRoot.root (minpoly A (AdjoinSimple.gen K α)))) =
      γ * algebraMap A'₁ Ω βA'₁ ^ r := by
    have h2 : minpoly.equivAdjoin hαint (AdjoinRoot.root (minpoly A (AdjoinSimple.gen K α))) =
        ⟨AdjoinSimple.gen K α, Algebra.subset_adjoin rfl⟩ := by
      rw [minpoly.coe_equivAdjoin, AdjoinRoot.Minpoly.toAdjoin, AdjoinRoot.liftAlgHom_root]
    have h1 : (eA₁.symm (AdjoinRoot.root (minpoly A (AdjoinSimple.gen K α))) : K⟮α⟯) =
        AdjoinSimple.gen K α := by
      simp [eA₁, h2]
    exact (congrArg (IntermediateField.val K⟮α⟯) h1).trans hα_eq
  exact exists_algHom_standardTameCover hπA' hβA'₁_pow hmin eA₁ hγ hroot

/-- Given an unramified extension `L₁ / K₁` over a DVR `A₁` (receiving `A → A₁` and `L → L₁`),
a finite étale `A'₁`-algebra `T` receiving `A₁`, and compatible embeddings into `Ω`, let
`B₁ = integralClosure A₁ L₁` (finite étale over `A₁`). Then the image `E ⊆ Ω` of
`K'₁ ⊗[A'₁] (T ⊗[A₁] B₁)` is an intermediate field unramified over `A'₁` containing `L'`. -/
private theorem exists_unramified_overfield_of_etale_cover
    {A K L K' L' A₁ K₁ L₁ A'₁ K'₁ T Ω : Type*}
    [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [Algebra.IsAlgebraic K L]
    [Field K'] [Algebra K K'] [Field L'] [Algebra K' L']
    (φ : K' ⊗[K] L →ₐ[K'] L') (hφ : Function.Surjective φ)
    [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁] [Algebra A A₁]
    [Field K₁] [Algebra A₁ K₁] [IsFractionRing A₁ K₁]
    [Field L₁] [Algebra L L₁] [Algebra K₁ L₁] [Algebra A L₁] [Algebra A₁ L₁]
    [IsScalarTower A L L₁] [IsScalarTower A A₁ L₁] [IsScalarTower A₁ K₁ L₁]
    [FiniteDimensional K₁ L₁] [Algebra.IsSeparable K₁ L₁]
    (hU : IsUnramifiedWRT A₁ L₁)
    [CommRing A'₁] [IsDomain A'₁] [IsDiscreteValuationRing A'₁]
    [Field K'₁] [Algebra K' K'₁] [Algebra A'₁ K'₁] [IsFractionRing A'₁ K'₁]
    [CommRing T] [Algebra A'₁ T] [Algebra A T] [Algebra.Etale A'₁ T] [Module.Finite A'₁ T]
    [Field Ω] [Algebra L' Ω] [Algebra K' Ω] [Algebra K'₁ Ω] [Algebra A'₁ Ω]
    [Algebra A₁ Ω] [Algebra L₁ Ω] [IsScalarTower K' L' Ω] [IsScalarTower K' K'₁ Ω]
    [IsScalarTower A'₁ K'₁ Ω] [IsScalarTower A₁ L₁ Ω]
    (f : A₁ →ₐ[A] T) (gT : T →ₐ[A'₁] Ω)
    (hfg : ∀ x : A₁, gT (f x) = algebraMap A₁ Ω x)
    (hL : ∀ x : L, algebraMap L₁ Ω (algebraMap L L₁ x) =
      algebraMap L' Ω (φ ((1 : K') ⊗ₜ[K] x))) :
    ∃ E : IntermediateField K'₁ Ω,
      IsUnramifiedWRT A'₁ E ∧ ∀ z : L', algebraMap L' Ω z ∈ E := by
  let B₁ := integralClosure A₁ L₁
  have : Algebra.Etale A₁ B₁ := (isUnramifiedWRT_iff_etale A₁ K₁ L₁).mp hU
  have : Module.Finite A₁ B₁ := IsIntegralClosure.finite A₁ K₁ L₁ _
  let : Algebra A₁ T := f.toAlgebra
  let S := T ⊗[A₁] B₁
  have : Algebra.Etale T S := inferInstance
  have : Module.Finite T S := inferInstance
  have : Algebra.Etale A'₁ S := Algebra.Etale.comp A'₁ T S
  have : Module.Finite A'₁ S := .trans T S
  let gT_A₁ : T →ₐ[A₁] Ω := { gT.toRingHom with commutes' := fun x ↦ hfg x }
  let gB₁ : B₁ →ₐ[A₁] Ω := (IsScalarTower.toAlgHom A₁ L₁ Ω).comp B₁.val
  let ψ_A₁ : S →ₐ[A₁] Ω := Algebra.TensorProduct.lift gT_A₁ gB₁ fun _ _ ↦ .all _ _
  let ψ : S →ₐ[A'₁] Ω :=
    { ψ_A₁.toRingHom with
      commutes' := fun a' ↦ by
        simp only [S, RingHom.toFun_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.algebraMap_apply, ψ_A₁, Algebra.TensorProduct.lift_tmul,
          gT_A₁, AlgHom.coe_mk, gT.commutes, map_one, mul_one] }
  let χ₀ : K'₁ ⊗[A'₁] S →ₐ[K'₁] Ω :=
    Algebra.TensorProduct.lift (Algebra.ofId K'₁ Ω) ψ fun _ _ ↦ .all _ _
  have : Module.Finite K'₁ (K'₁ ⊗[A'₁] S) := inferInstance
  have : Module.Finite K'₁ χ₀.range :=
    Module.Finite.of_surjective χ₀.rangeRestrict.toLinearMap χ₀.rangeRestrict_surjective
  let E : IntermediateField K'₁ Ω :=
    χ₀.range.toIntermediateField' (isField_of_isIntegral_of_isField' (Field.toIsField K'₁))
  let χ : K'₁ ⊗[A'₁] S →ₐ[K'₁] E :=
    { toRingHom := χ₀.toRingHom.codRestrict E.toSubring fun x ↦ ⟨x, rfl⟩
      commutes' := fun k ↦ Subtype.ext (χ₀.commutes k) }
  have hχ : Function.Surjective χ := fun ⟨_, x, hx⟩ ↦ ⟨x, Subtype.ext hx⟩
  refine ⟨E, χ.isUnramifiedWRT_of_surjective hχ, ?_⟩
  -- `L'` is spanned over `K'` by `{φ (1 ⊗ₜ b) | b ∈ integralClosure A L}`, which land in `E`.
  have hspan : Submodule.span K'
      (Set.range fun b : integralClosure A L ↦ φ ((1 : K') ⊗ₜ[K] (b : L))) = ⊤ := by
    have h1 := congrArg (Submodule.map φ.toLinearMap)
      (TauCeti.span_one_tmul_integralClosure_eq_top (A := A) (K := K) (L := L) (K' := K'))
    rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr hφ] at h1
    rwa [← Set.range_comp] at h1
  have hsub : Submodule.map (IsScalarTower.toAlgHom K' L' Ω).toLinearMap ⊤ ≤
      E.toSubalgebra.toSubmodule.restrictScalars K' := by
    rw [← hspan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    have hbB₁ : algebraMap L L₁ b ∈ B₁ :=
      (b.2.map (IsScalarTower.toAlgHom A L L₁)).tower_top
    let b₁ : B₁ := ⟨algebraMap L L₁ b, hbB₁⟩
    refine ⟨1 ⊗ₜ[A'₁] (1 ⊗ₜ[A₁] b₁), ?_⟩
    dsimp only [χ₀, ψ, ψ_A₁, gB₁, S]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one,
      one_mul, AlgHom.coe_mk, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact hL b
  exact fun z ↦ hsub ⟨z, Submodule.mem_top, rfl⟩

variable {A K L A' K' L' : Type*}
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A'] [Field K'] [Algebra A' K']
  [IsFractionRing A' K'] [Algebra A A'] [Algebra A K'] [Algebra K K'] [IsScalarTower A A' K']
  [IsScalarTower A K K'] [Field L'] [Algebra K' L'] [Algebra A' L'] [IsScalarTower A' K' L']

/-- Tame base change carried out inside an opaque algebraically closed overfield `Ω` of `L'`,
avoiding `whnf` unfolding of `AlgebraicClosure L'` inside `IntermediateField` instances. -/
private theorem isTamelyRamifiedWRT_baseChange_of_isAlgClosed
    {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    [Algebra A Ω] [Algebra K Ω] [Algebra L Ω] [Algebra A' Ω] [Algebra K' Ω] [Algebra L' Ω]
    [IsScalarTower A K Ω] [IsScalarTower K L Ω] [IsScalarTower A L Ω]
    [IsScalarTower A' K' Ω] [IsScalarTower K' L' Ω] [IsScalarTower A' L' Ω]
    [IsScalarTower A A' Ω]
    (h : IsTamelyRamifiedWRT A L) (φ : K' ⊗[K] L →ₐ[K'] L') (hφ : Function.Surjective φ)
    (hL : ∀ x : L, algebraMap L Ω x = algebraMap L' Ω (φ ((1 : K') ⊗ₜ[K] x))) :
    IsTamelyRamifiedWRT A' L' := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨π', hπ'⟩ := IsDiscreteValuationRing.exists_irreducible A'
  have hπA'_ne : algebraMap A A' π ≠ 0 := fun h0 ↦ hπ.ne_zero <| by
    have hK' : algebraMap K K' (algebraMap A K π) = 0 := by
      rw [← IsScalarTower.algebraMap_apply A K K', IsScalarTower.algebraMap_apply A A' K', h0,
        map_zero]
    exact IsFractionRing.injective A K ((algebraMap K K').injective (by simpa using hK'))
  obtain ⟨r, u', hπA'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπA'_ne hπ'
  obtain ⟨e, he_κA, hdvd⟩ := exists_ramificationIdx_dvd_of_isTamelyRamifiedWRT (K := K) h
  have he_A : IsUnit (e : A) := (isUnit_map_iff (IsLocalRing.residue A) _).mp (by
    rw [map_natCast]; exact he_κA)
  have he_A' : IsUnit (e : A') := by simpa using he_A.map (algebraMap A A')
  have he_κA' : IsUnit (e : A' ⧸ maximalIdeal A') := by
    simpa using he_A'.map (Ideal.Quotient.mk (maximalIdeal A'))
  have he0 : e ≠ 0 := by rintro rfl; simp at he_κA
  -- Extract `e`-th roots `β` of `π'` and `γ` of `u'`, and set `α = γ β ^ r` (`α ^ e = π`).
  obtain ⟨β, hβ⟩ :=
    IsAlgClosed.exists_pow_nat_eq (algebraMap A' Ω π') (Nat.pos_of_ne_zero he0)
  obtain ⟨γ, hγ⟩ :=
    IsAlgClosed.exists_pow_nat_eq (algebraMap A' Ω u') (Nat.pos_of_ne_zero he0)
  let α : Ω := γ * β ^ r
  have hα : α ^ e = algebraMap A Ω π := by
    rw [mul_pow, ← pow_mul, mul_comm r e, pow_mul, hγ, hβ, ← map_pow, ← map_mul, ← hπA',
      ← IsScalarTower.algebraMap_apply A A' Ω]
  -- By global Abhyankar's lemma, `L(α)` is unramified over `A₁ = integralClosure A K(α)`.
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
  obtain ⟨_, hU_A₁⟩ := h.isUnramifiedWRT_adjoin_root (K := K) hπ hα hdvd
  let A₁ := integralClosure A K⟮α⟯
  have : IsScalarTower A K L⟮α⟯ := .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A L L⟮α⟯,
      IsScalarTower.algebraMap_apply K L L⟮α⟯, ← IsScalarTower.algebraMap_apply A K L]
  have : IsScalarTower A K⟮α⟯ L⟮α⟯ :=
    IsScalarTower.of_algHom ((TauCeti.IntermediateField.adjoinBaseChange K L α).restrictScalars A)
  have : IsScalarTower A A₁ L⟮α⟯ := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A₁ K⟮α⟯ L⟮α⟯,
      ← IsScalarTower.algebraMap_apply A A₁ K⟮α⟯,
      ← IsScalarTower.algebraMap_apply A K⟮α⟯ L⟮α⟯]
  have hαK : AdjoinSimple.gen K α ^ e = algebraMap A K⟮α⟯ π :=
    Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A K K⟮α⟯,
      IsScalarTower.algebraMap_apply A K Ω] using hα)
  have hdegα := IsDiscreteValuationRing.finrank_eq_of_pow_eq_of_irreducible hπ hαK
    (adjoin_adjoinSimple_gen_eq_top α)
  have : FiniteDimensional K K⟮α⟯ :=
    Module.finite_of_finrank_pos (hdegα ▸ Nat.pos_of_ne_zero he0)
  have : IsFractionRing A₁ K⟮α⟯ :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K K⟮α⟯ _
  have hαintL : IsIntegral L α :=
    (IsIntegral.of_pow (Nat.pos_of_ne_zero he0) (hα ▸ isIntegral_algebraMap (R := A))).tower_top
  have hsurjα := TauCeti.IntermediateField.surjective_adjoinBaseChange_tensorProduct K L hαintL
  have : FiniteDimensional K⟮α⟯ L⟮α⟯ := Module.Finite.of_surjective
    (TauCeti.IntermediateField.adjoinBaseChangeTensorLift K L α).toLinearMap hsurjα
  have : Algebra.FormallyUnramified K L :=
    (Algebra.FormallyUnramified.iff_isSeparable K L).mpr inferInstance
  have : Algebra.FormallyUnramified K⟮α⟯ L⟮α⟯ :=
    .of_surjective (A := K⟮α⟯ ⊗[K] L)
      (TauCeti.IntermediateField.adjoinBaseChangeTensorLift K L α) hsurjα
  have : Algebra.IsSeparable K⟮α⟯ L⟮α⟯ :=
    (Algebra.FormallyUnramified.iff_isSeparable K⟮α⟯ L⟮α⟯).mp inferInstance
  -- Build the Kummer DVR `A'₁ = integralClosure A' K'(β)` and the standard tame cover `T`.
  let A'₁ := integralClosure A' K'⟮β⟯
  have hβK' : AdjoinSimple.gen K' β ^ e = algebraMap A' K'⟮β⟯ π' :=
    Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A' K' K'⟮β⟯,
      IsScalarTower.algebraMap_apply A' K' Ω] using hβ)
  have hgenβ : K'⟮AdjoinSimple.gen K' β⟯ = ⊤ := adjoin_adjoinSimple_gen_eq_top β
  have : IsDiscreteValuationRing A'₁ :=
    IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
      hπ' hβK' hgenβ
  have hdegβ := IsDiscreteValuationRing.finrank_eq_of_pow_eq_of_irreducible hπ' hβK' hgenβ
  have : FiniteDimensional K' K'⟮β⟯ :=
    Module.finite_of_finrank_pos (hdegβ ▸ Nat.pos_of_ne_zero he0)
  have : IsFractionRing A'₁ K'⟮β⟯ :=
    IsIntegralClosure.isFractionRing_of_finite_extension A' K' K'⟮β⟯ _
  let T := TauCeti.standardTameCover A'₁ (algebraMap A' A'₁ u') e
  have : Algebra.Etale A'₁ T :=
    TauCeti.standardTameCover_etale (u'.isUnit.map _)
      (by simpa using he_A'.map (algebraMap A' A'₁))
  have : NeZero e := ⟨he0⟩
  have : Module.Finite A'₁ T := inferInstance
  let : Algebra A T := ((algebraMap A'₁ T).comp ((algebraMap A' A'₁).comp
    (algebraMap A A'))).toAlgebra
  -- Obtain `f : A₁ → T` compatible with `gT : T → Ω`, and apply finite étale base change.
  have : IsScalarTower A' K'⟮β⟯ Ω := .of_algebraMap_eq fun a' ↦ by
    rw [IsScalarTower.algebraMap_apply A' K' K'⟮β⟯,
      ← IsScalarTower.algebraMap_apply K' K'⟮β⟯ Ω,
      ← IsScalarTower.algebraMap_apply A' K' Ω]
  have : IsScalarTower A'₁ K'⟮β⟯ Ω := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A₁ L⟮α⟯ Ω := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply A₁ K⟮α⟯ L⟮α⟯]
    exact (TauCeti.IntermediateField.coe_adjoinBaseChange K L α (x : K⟮α⟯)).symm
  obtain ⟨f, gT, hfg⟩ :=
    exists_algHom_integralClosure_standardTameCover hπ hπA' he0 hαK hβK' hγ rfl
  -- Apply the finite étale base change construction to obtain an unramified overfield `E ⊇ L'`.
  obtain ⟨E, hUnramE, hL'_mem⟩ :=
    exists_unramified_overfield_of_etale_cover (A := A) (K := K) (L := L)
      (A₁ := A₁) (K₁ := K⟮α⟯) (L₁ := L⟮α⟯) (A'₁ := A'₁) (K'₁ := K'⟮β⟯) (T := T)
      (Ω := Ω) φ hφ hU_A₁ f gT hfg fun x ↦ hL x
  -- Descend tame ramification from `E` (tamely ramified over `A'` via `K'(β)`) to `L'`.
  let : Algebra L' E := RingHom.toAlgebra
    { toFun := fun z ↦ ⟨algebraMap L' Ω z, hL'_mem z⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ ↦ Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ ↦ Subtype.ext (map_add _ _ _) }
  have : IsScalarTower A' L' E := .of_algebraMap_eq fun a' ↦
    Subtype.ext (IsScalarTower.algebraMap_apply A' L' Ω a')
  have : FiniteDimensional K' L' := Module.Finite.of_surjective φ.toLinearMap hφ
  have : Algebra.FormallyUnramified K' L' := .of_surjective φ hφ
  have : Algebra.IsSeparable K' L' :=
    (Algebra.FormallyUnramified.iff_isSeparable K' L').mp inferInstance
  have hK'₁ : IsTamelyRamifiedWRT A' K'⟮β⟯ :=
    (IsDiscreteValuationRing.isTamelyRamifiedWRT_iff_of_pow_eq_of_irreducible hπ' hβK' hgenβ).mpr
      he_κA'
  exact (hK'₁.trans hUnramE.isTamelyRamifiedWRT).tower_bot K'

/-- Tamely ramified extensions of a discrete valuation ring are stable under base change: if `L` is
tamely ramified with respect to `A`, then every factor `L'` of `K' ⊗[K] L`, given by a surjective
`K'`-algebra map `φ : K' ⊗[K] L → L'`, is tamely ramified with respect to `A'`. -/
@[stacks 0EXY "tamely ramified case"]
theorem IsTamelyRamifiedWRT.baseChange (h : IsTamelyRamifiedWRT A L)
    (φ : K' ⊗[K] L →ₐ[K'] L') (hφ : Function.Surjective φ) : IsTamelyRamifiedWRT A' L' := by
  -- Install compatible algebra structures on `L'`, hence automatically on `AlgebraicClosure L'`.
  let : Algebra K L' := ((algebraMap K' L').comp (algebraMap K K')).toAlgebra
  have : IsScalarTower K K' L' := .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra A L' := ((algebraMap A' L').comp (algebraMap A A')).toAlgebra
  have : IsScalarTower A A' L' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A K' L' := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply A A' K',
      ← IsScalarTower.algebraMap_apply A' K' L']
  have : IsScalarTower A K L' := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply K K' L', ← IsScalarTower.algebraMap_apply A K K',
      ← IsScalarTower.algebraMap_apply A K' L']
  let : Algebra L L' :=
    (φ.toRingHom.comp
      (Algebra.TensorProduct.includeRight : L →ₐ[K] K' ⊗[K] L).toRingHom).toAlgebra
  have : IsScalarTower K L L' := .of_algebraMap_eq fun k ↦ by
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul, ← Algebra.TensorProduct.algebraMap_apply,
      IsScalarTower.algebraMap_apply K K' (K' ⊗[K] L), AlgHom.commutes]
  have : IsScalarTower A L L' := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply K L L',
      ← IsScalarTower.algebraMap_apply A K L']
  exact isTamelyRamifiedWRT_baseChange_of_isAlgClosed (Ω := AlgebraicClosure L') h φ hφ
    fun x ↦ by
      simp [IsScalarTower.algebraMap_apply L L' (AlgebraicClosure L'),
        RingHom.algebraMap_toAlgebra]

end BaseChange

end TauCeti.Algebra

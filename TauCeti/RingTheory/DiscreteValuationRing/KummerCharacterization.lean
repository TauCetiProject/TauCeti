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
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Unramified.Field
import Mathlib.Tactic.TFAE
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.RingTheory.DiscreteValuationRing.AbhyankarModel.Localization
import TauCeti.RingTheory.DiscreteValuationRing.Kummer
import TauCeti.RingTheory.Localization.AtPrime
import TauCeti.RingTheory.Localization.Integral
import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing

/-!
# Kummer elimination and characterization of tamely ramified extensions

Let `A` be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let `L / K`
be a finite separable extension. This file proves that adjoining an `n`-th root of `π`, where `n`
is a multiple of every ramification index of `L` over `A`, eliminates tame ramification (Stacks,
Lemma 15.116.4 (0BRM), finite separable case) and deduces the Kummer characterization of tame
ramification (Stacks, Lemma 15.116.7 (0EXW)).

The elimination step follows SGA 1, Exposé X, Lemme 3.6 via the local structure of the Abhyankar
model (`TauCeti.exists_algEquiv_localization_abhyankarModel`). If `L / K` is tamely ramified with
respect to `A` and `n` is a multiple of every ramification index over `A`, adjoining an `n`-th root
`β` of `π` produces an extension `L(β) / K(β)` that is unramified with respect to the integral
closure `A[β]` of `A` in `K(β)` (`TauCeti.Algebra.IsTamelyRamifiedWRT.adjoin_root`): each
localization of the integral closure of `A[β]` in `L(β)` at a maximal ideal is isomorphic to a
localization of the Abhyankar model over the corresponding discrete valuation ring of `L`, so `β`
remains a uniformizer there and the residue extension remains separable. Taking `e₀` to be the
product of the ramification indices over `A` gives an exponent invertible in `κ_A`, and any further
multiple `d * e₀` (including wild multiples when `d ≠ 0`) works the same way. Together with the
converse
`TauCeti.IsDiscreteValuationRing.isTamelyRamifiedWRT_of_isUnramifiedWRT_of_pow_eq_of_irreducible`,
this gives the three-way equivalence of Lemma 15.116.7 (`TauCeti.Algebra.isTamelyRamifiedWRT_tfae`).

## Main results

* `TauCeti.IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_adjoin`: for an `n`-th
  root `α` of a uniformizer of `A` in an extension of `K`, `integralClosure A K(α)` is a discrete
  valuation ring.
* `TauCeti.IsDiscreteValuationRing.isTamelyRamifiedWRT_adjoin_of_pow_eq_of_irreducible`: when `n`
  is invertible in `κ_A`, `K(α)` is tamely ramified with respect to `A`.
* `TauCeti.Algebra.IsTamelyRamifiedWRT.isUnramifiedWRT_of_pow_eq_of_irreducible` and
  `TauCeti.Algebra.IsTamelyRamifiedWRT.adjoin_root`: adjoining an `n`-th root of a uniformizer,
  where every ramification index of `L` over `A` divides `n`, eliminates tame ramification.
* `TauCeti.Algebra.IsTamelyRamifiedWRT.exists_ramificationIdx_dvd`: a tamely ramified extension
  admits a positive exponent `e₀` invertible in `κ_A` divisible by all ramification indices.
* `TauCeti.Algebra.isTamelyRamifiedWRT_tfae`,
  `TauCeti.Algebra.isTamelyRamifiedWRT_iff_exists_kummer`,
  `TauCeti.Algebra.isTamelyRamifiedWRT_iff_exists_forall_kummer`, and
  `TauCeti.Algebra.isTamelyRamifiedWRT_iff_exists_adjoin_root`: the Kummer characterizations of
  tame ramification (Stacks, Lemma 15.116.7).

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé X, Lemme 3.6.
* [Stacks Project, Lemma 15.116.2](https://stacks.math.columbia.edu/tag/09EV).
* [Stacks Project, Lemma 15.116.4](https://stacks.math.columbia.edu/tag/0BRM).
* [Stacks Project, Lemma 15.116.7](https://stacks.math.columbia.edu/tag/0EXW).
-/

public section

universe u

open scoped TensorProduct
open _root_.IntermediateField IsLocalRing

namespace TauCeti.IsDiscreteValuationRing

section AdjoinSubfield

variable {A K L : Type*} [CommRing A] [IsDomain A] [_root_.IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]

/-- **The integral closure in an adjoined Kummer subfield is a discrete valuation ring.** If `α` is
an `n`-th root of a uniformizer `π` of `A` in an extension `L` of the fraction field `K` of `A`,
then the integral closure of `A` in `K(α)` is a discrete valuation ring. -/
@[stacks 09EV "(3), adjoined subfield"]
theorem isDiscreteValuationRing_integralClosure_adjoin
    {π : A} (hπ : Irreducible π) {n : ℕ} {α : L} (hα : α ^ n = algebraMap A L π) :
    _root_.IsDiscreteValuationRing (integralClosure A K⟮α⟯) := by
  have hαK : AdjoinSimple.gen K α ^ n = algebraMap A K⟮α⟯ π :=
    Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A K K⟮α⟯,
      IsScalarTower.algebraMap_apply A K L] using hα)
  exact isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible hπ hαK
    (_root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α)

/-- **Adjoining a tame root of a uniformizer gives a tamely ramified subfield.** When `n` is
invertible in `κ_A`, the subfield `K(α)` generated by an `n`-th root `α` of a uniformizer `π` of
`A` is tamely ramified with respect to `A`. -/
@[stacks 09EV "(6), adjoined subfield"]
theorem isTamelyRamifiedWRT_adjoin_of_pow_eq_of_irreducible {π : A} (hπ : Irreducible π)
    {n : ℕ} (hn : IsUnit (n : A ⧸ maximalIdeal A)) {α : L} (hα : α ^ n = algebraMap A L π) :
    Algebra.IsTamelyRamifiedWRT A K⟮α⟯ := by
  have hαK : AdjoinSimple.gen K α ^ n = algebraMap A K⟮α⟯ π :=
    Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A K K⟮α⟯,
      IsScalarTower.algebraMap_apply A K L] using hα)
  exact (isTamelyRamifiedWRT_iff_of_pow_eq_of_irreducible hπ hαK
    (_root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α)).mpr hn

end AdjoinSubfield

end TauCeti.IsDiscreteValuationRing

namespace TauCeti.Algebra

section EliminateRamification

/-- In an extension of a fraction field `K` of `A`, an `n`-th root of an irreducible element `π`
of `A` can exist only for `n ≠ 0`. -/
private theorem ne_zero_of_pow_eq_irreducible {A : Type*} [CommRing A] {π : A} {n : ℕ}
    (K : Type*) {E : Type*} [Field K] [Algebra A K] [IsFractionRing A K] [Field E] [Algebra K E]
    [Algebra A E] [IsScalarTower A K E] {β : E} (hπ : Irreducible π)
    (hβ : β ^ n = algebraMap A E π) : n ≠ 0 := by
  rintro rfl
  rw [pow_zero, IsScalarTower.algebraMap_apply A K E, ← map_one (algebraMap K E),
    (algebraMap K E).injective.eq_iff, ← map_one (algebraMap A K),
    (IsFractionRing.injective A K).eq_iff] at hβ
  exact hπ.not_isUnit (hβ ▸ isUnit_one)

/-- At a maximal ideal `P` of a Dedekind domain `C` over a discrete valuation ring `A` with
uniformizer `π`, if `C` embeds into an extension `L` of the fraction field `K` of `A`, the image of
`π` in `Localization.AtPrime P` is a unit times the `e`-th power of a uniformizer `ϖ`, where `e` is
`P.ramificationIdx A`. -/
private theorem exists_unit_mul_pow_ramificationIdx_localization
    {A K L C : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [CommRing C] [IsDedekindDomain C] [Algebra A C] [Algebra C L]
    [IsScalarTower A C L] [IsFractionRing C L]
    {π : A} (hπ : Irreducible π) (P : Ideal C) [P.IsMaximal] [P.LiesOver (maximalIdeal A)]
    {ϖ : Localization.AtPrime P} (hϖ : Irreducible ϖ)
    [IsDiscreteValuationRing (Localization.AtPrime P)] :
    ∃ u : (Localization.AtPrime P)ˣ,
      algebraMap A (Localization.AtPrime P) π = ↑u * ϖ ^ P.ramificationIdx A := by
  let B := Localization.AtPrime P
  have : IsLocalHom (algebraMap A B) := by
    apply ((local_hom_tfae (algebraMap A B)).out 5 1).mp
    rw [IsScalarTower.algebraMap_eq A C B, ← Ideal.comap_comap, ← Ideal.under_def C,
      IsLocalization.AtPrime.under_maximalIdeal B P, ← Ideal.under_def,
      ← Ideal.over_def P (maximalIdeal A)]
  have hπB_ne : algebraMap A B π ≠ 0 := fun h0 ↦ by
    have hK : algebraMap A L π = 0 := by
      rw [IsScalarTower.algebraMap_apply A C L, IsScalarTower.algebraMap_apply C B L,
        ← IsScalarTower.algebraMap_apply A C B, h0, map_zero]
    rw [IsScalarTower.algebraMap_apply A K L, map_eq_zero,
      IsFractionRing.to_map_eq_zero_iff] at hK
    exact hπ.ne_zero hK
  have hmap_ne : (maximalIdeal A).map (algebraMap A B) ≠ ⊥ := fun hbot ↦
    hπB_ne (Ideal.mem_bot.mp
      (hbot ▸ Ideal.mem_map_of_mem _ ((mem_maximalIdeal π).mpr hπ.not_isUnit)))
  have hmap := TauCeti.IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx hmap_ne
  have he : P.ramificationIdx A = (maximalIdeal B).ramificationIdx A :=
    Ideal.IsDedekindDomain.ramificationIdx_eq_of_map_eq_pow (maximalIdeal A) P _ hmap
  rw [← he, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hϖ.maximalIdeal_eq,
    Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at hmap
  obtain ⟨u, hu⟩ := hmap.symm
  exact ⟨u, by rw [← hu, mul_comm]⟩

/-- If `E` is generated over `L` by the image of `α₀ ∈ K₁` integral over `L`, and `L / K` is finite
and separable, then `E` is a finite separable extension of `K₁`. -/
private theorem finiteDimensional_and_isSeparable_of_adjoin_eq_top
    {K K₁ L E : Type*} [Field K] [Field K₁] [Field L] [Field E]
    [Algebra K K₁] [Algebra K L] [Algebra K E] [Algebra K₁ E] [Algebra L E]
    [IsScalarTower K K₁ E] [IsScalarTower K L E]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {α₀ : K₁} (hβ : IsIntegral L (algebraMap K₁ E α₀))
    (hgen : L⟮algebraMap K₁ E α₀⟯ = ⊤) :
    FiniteDimensional K₁ E ∧ Algebra.IsSeparable K₁ E := by
  let ψ : K₁ ⊗[K] L →ₐ[K₁] E :=
    Algebra.TensorProduct.lift (Algebra.ofId K₁ E) (IsScalarTower.toAlgHom K L E)
      fun _ _ ↦ .all _ _
  have hψ : Function.Surjective ψ := by
    let S : Subalgebra L E :=
      { ψ.range.toSubring with
        algebraMap_mem' := fun l ↦ ⟨1 ⊗ₜ[K] l, by simp [ψ]⟩ }
    have hmem : algebraMap K₁ E α₀ ∈ S := ⟨α₀ ⊗ₜ[K] 1, by simp [ψ]⟩
    have hadj : Algebra.adjoin L ({algebraMap K₁ E α₀} : Set E) = ⊤ :=
      (adjoin_simple_eq_top_iff_of_isAlgebraic hβ.isAlgebraic).mp hgen
    have htop : S = ⊤ := top_unique (hadj ▸ Algebra.adjoin_le (Set.singleton_subset_iff.mpr hmem))
    intro x
    have hx : x ∈ S := htop ▸ Algebra.mem_top
    exact (AlgHom.mem_range ψ).mp hx
  have : FiniteDimensional K₁ E := Module.Finite.of_surjective ψ.toLinearMap hψ
  have : Algebra.FormallyUnramified K L := .of_isSeparable K L
  have : Algebra.FormallyUnramified K₁ E := .of_surjective ψ hψ
  exact ⟨‹_›, (Algebra.FormallyUnramified.iff_isSeparable K₁ E).mp ‹_›⟩

/-- If `E = L[β]` for the fraction field `L` of `B` and `S` is a `B`-algebra embedding into `E`
with fraction field `E`, every element of `S` becomes a polynomial in `β` over `B` after
multiplication by a nonzero element of `B`. -/
private theorem exists_multiple_mem_adjoin_of_adjoin_eq_top
    {B L S E : Type*} [CommRing B] [IsDomain B] [Field L] [Algebra B L] [IsFractionRing B L]
    [CommRing S] [Algebra B S] [Field E] [Algebra L E] [Algebra B E] [IsScalarTower B L E]
    [Algebra S E] [IsFractionRing S E] [IsScalarTower B S E]
    {β_S : S} (hadj : Algebra.adjoin L ({algebraMap S E β_S} : Set E) = ⊤) (c : S) :
    ∃ s : B, s ≠ 0 ∧ algebraMap B S s * c ∈ Algebra.adjoin B {β_S} := by
  have hc : algebraMap S E c ∈ Algebra.adjoin L ({algebraMap S E β_S} : Set E) :=
    hadj ▸ Algebra.mem_top
  obtain ⟨t, ht⟩ := _root_.multiple_mem_adjoin_of_mem_localization_adjoin
    (nonZeroDivisors B) L {algebraMap S E β_S} (algebraMap S E c) hc
  let ιS : S →ₐ[B] E := IsScalarTower.toAlgHom B S E
  have hmap : (Algebra.adjoin B ({β_S} : Set S)).map ιS =
      Algebra.adjoin B ({algebraMap S E β_S} : Set E) := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    rfl
  rw [← hmap] at ht
  obtain ⟨z, hz, hzeq⟩ := ht
  refine ⟨t, mem_nonZeroDivisors_iff_ne_zero.mp t.2, ?_⟩
  have hzeq' : algebraMap S E z = (t : B) • algebraMap S E c := hzeq
  have heq : algebraMap S E (algebraMap B S t * c) = algebraMap S E z := by
    rw [hzeq', Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply B S E]
  exact (IsFractionRing.injective S E heq) ▸ hz

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

/-- Any ideal lying over the maximal ideal of a faithfully embedded discrete valuation ring is
nonzero. -/
private theorem prime_ne_bot_of_liesOver_maximalIdeal
    {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [Algebra R S] [FaithfulSMul R S]
    (Q : Ideal S) [Q.LiesOver (maximalIdeal R)] : Q ≠ ⊥ := by
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible R
  refine fun hbot ↦ hπ.ne_zero <| (FaithfulSMul.algebraMap_injective R S) ?_
  rw [map_zero, ← Ideal.mem_bot, ← hbot, ← Ideal.mem_comap, ← Ideal.under_def,
    ← Ideal.over_def Q (maximalIdeal R)]
  exact (mem_maximalIdeal π).mpr hπ.not_isUnit

/-- Compatibility of `Localization.AtPrime P → Localization.AtPrime M'` with the fraction-field
embeddings `C → L → E` and `C' → E`. -/
private theorem isScalarTower_and_faithfulSMul_localizationAtPrime
    {C C' L E : Type*} [CommRing C] [IsDomain C] [CommRing C'] [IsDomain C']
    [Field L] [Field E] [Algebra C L] [IsFractionRing C L] [Algebra C' E] [IsFractionRing C' E]
    [Algebra C C'] [Algebra L E] [Algebra C E] [IsScalarTower C C' E] [IsScalarTower C L E]
    (P : Ideal C) [P.IsPrime] (M' : Ideal C') [M'.IsPrime] [M'.LiesOver P]
    [Algebra (Localization.AtPrime P) E] [IsScalarTower (Localization.AtPrime P) L E] :
    ((algebraMap (Localization.AtPrime M') E).comp
      (algebraMap (Localization.AtPrime P) (Localization.AtPrime M')) =
        (algebraMap L E).comp (algebraMap (Localization.AtPrime P) L)) ∧
      IsScalarTower (Localization.AtPrime P) (Localization.AtPrime M') E ∧
      FaithfulSMul (Localization.AtPrime P) (Localization.AtPrime M') := by
  let B_loc := Localization.AtPrime P
  let S_loc := Localization.AtPrime M'
  have hBS_E : (algebraMap S_loc E).comp (algebraMap B_loc S_loc) =
      (algebraMap L E).comp (algebraMap B_loc L) := by
    apply IsLocalization.ringHom_ext P.primeCompl
    ext c
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply C B_loc S_loc,
      ← IsScalarTower.algebraMap_apply C B_loc L]
    rw [IsScalarTower.algebraMap_apply C C' S_loc, ← IsScalarTower.algebraMap_apply C' S_loc E,
      ← IsScalarTower.algebraMap_apply C C' E, ← IsScalarTower.algebraMap_apply C L E]
  have hst : IsScalarTower B_loc S_loc E := .of_algebraMap_eq fun b ↦ by
    rw [← RingHom.comp_apply, hBS_E, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply B_loc L E]
  refine ⟨hBS_E, hst, (faithfulSMul_iff_algebraMap_injective B_loc S_loc).mpr <|
    Function.Injective.of_comp (f := algebraMap S_loc E) ?_⟩
  rw [← RingHom.coe_comp, hBS_E]
  exact (algebraMap L E).injective.comp (IsFractionRing.injective B_loc L)

/-- Local Abhyankar elimination step at a single maximal ideal `M'` of `C'` lying over the closed
point of `A₁`: localizing `C` at `M' ∩ C` and `C'` at `M'` puts `M'` in the setting of
`TauCeti.exists_algEquiv_localization_abhyankarModel`, yielding ramification index one and
separable residue extension over `A₁`. -/
private theorem ramificationIdx_eq_one_and_isSeparable_at_maximal
    {A K L A₁ C C' E : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁] [Algebra A A₁]
    [Algebra.IsIntegral A A₁]
    [CommRing C] [IsDedekindDomain C] [Algebra A C] [Algebra.IsIntegral A C] [Algebra C L]
    [IsScalarTower A C L] [IsFractionRing C L]
    [CommRing C'] [IsDedekindDomain C'] [Algebra A₁ C'] [Algebra A C'] [Algebra C C']
    [IsScalarTower A A₁ C'] [IsScalarTower A C C'] [Algebra.IsIntegral C C']
    [Field E] [Algebra A E] [Algebra L E] [Algebra A₁ E] [Algebra C E] [Algebra C' E]
    [IsScalarTower A L E] [IsScalarTower A₁ C' E] [IsScalarTower C C' E] [IsScalarTower C L E]
    [FaithfulSMul A₁ E] [IsFractionRing C' E]
    {π : A} (hπ : Irreducible π) {α₁ : A₁} (hα₁ : Irreducible α₁)
    {n : ℕ} (hn : n ≠ 0) (hβ : (algebraMap A₁ E α₁) ^ n = algebraMap A E π)
    (hadjE : Algebra.adjoin L ({algebraMap A₁ E α₁} : Set E) = ⊤)
    (htame : ∀ (P : Ideal C) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      Algebra.IsSeparable (A ⧸ maximalIdeal A) (C ⧸ P) ∧
        IsUnit ((P.ramificationIdx A : ℕ) : A ⧸ maximalIdeal A))
    (hdvd : ∀ (P : Ideal C) [P.IsMaximal] [P.LiesOver (maximalIdeal A)], P.ramificationIdx A ∣ n)
    (M' : Ideal C') [M'.IsMaximal] [M'.LiesOver (maximalIdeal A₁)] :
    M'.ramificationIdx A₁ = 1 ∧ Algebra.IsSeparable (A₁ ⧸ maximalIdeal A₁) (C' ⧸ M') := by
  let P : Ideal C := M'.under C
  have : M'.LiesOver P := ⟨rfl⟩
  have : P.IsMaximal := Ideal.IsMaximal.under C M'
  have : P.LiesOver (maximalIdeal A) := ⟨(eq_maximalIdeal (Ideal.IsMaximal.under A P)).symm⟩
  have : (maximalIdeal A₁).LiesOver (maximalIdeal A) :=
    ⟨(eq_maximalIdeal (Ideal.IsMaximal.under A _)).symm⟩
  have : M'.LiesOver (maximalIdeal A) := .trans M' (maximalIdeal A₁) (maximalIdeal A)
  have : FaithfulSMul A C := have : FaithfulSMul A L := .trans A K L; .tower_bot A C L
  have : FaithfulSMul A₁ C' := .tower_bot A₁ C' E
  let B_loc := Localization.AtPrime P
  let S_loc := Localization.AtPrime M'
  have : IsDiscreteValuationRing B_loc :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C
      (prime_ne_bot_of_liesOver_maximalIdeal (R := A) P) B_loc
  have : IsDiscreteValuationRing S_loc :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C'
      (prime_ne_bot_of_liesOver_maximalIdeal (R := A₁) M') S_loc
  let : Algebra B_loc E := ((algebraMap L E).comp (algebraMap B_loc L)).toAlgebra
  have : IsScalarTower B_loc L E := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A₁ S_loc E := .to₁₃₄ A₁ C' S_loc E
  obtain ⟨hBS_E, _, _⟩ := isScalarTower_and_faithfulSMul_localizationAtPrime (L := L) (E := E) P M'
  obtain ⟨ϖ, hϖ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible B_loc
  obtain ⟨u, hu_eq⟩ := exists_unit_mul_pow_ramificationIdx_localization (K := K) (L := L) hπ P hϖ
  have he_A : IsUnit (P.ramificationIdx A : A) :=
    (isUnit_map_iff (residue A) _).mp (by rw [map_natCast]; exact (htame P).2)
  have he_B : IsUnit (P.ramificationIdx A : B_loc) := by simpa using he_A.map (algebraMap A B_loc)
  obtain ⟨d, hd_eq⟩ := hdvd P
  have hd : d ≠ 0 := right_ne_zero_of_mul (hd_eq ▸ hn)
  have hβ_SE : algebraMap S_loc E (algebraMap A₁ S_loc α₁) = algebraMap A₁ E α₁ :=
    (IsScalarTower.algebraMap_apply A₁ S_loc E α₁).symm
  have hβ_pow : (algebraMap A₁ S_loc α₁) ^ (P.ramificationIdx A * d) =
      algebraMap B_loc S_loc (↑u * ϖ ^ P.ramificationIdx A) :=
    IsFractionRing.injective S_loc E (by
      rw [map_pow, hβ_SE, ← hd_eq, hβ, ← hu_eq, IsScalarTower.algebraMap_apply A C B_loc,
        ← RingHom.comp_apply (algebraMap S_loc E) (algebraMap B_loc S_loc), hBS_E,
        RingHom.comp_apply, ← IsScalarTower.algebraMap_apply C B_loc L,
        ← IsScalarTower.algebraMap_apply A C L, ← IsScalarTower.algebraMap_apply A L E])
  have hgenS := exists_multiple_mem_adjoin_of_adjoin_eq_top (B := B_loc) (L := L) (hβ_SE ▸ hadjE)
  have hβ_irr : Irreducible (algebraMap A₁ S_loc α₁) :=
    irreducible_of_pow_eq_unit_mul_pow hϖ u.isUnit he_B hd hβ_pow hgenS
  have hmapA₁ : (maximalIdeal A₁).map (algebraMap A₁ S_loc) = maximalIdeal S_loc ^ 1 := by
    rw [pow_one, hα₁.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hβ_irr.maximalIdeal_eq]
  refine ⟨Ideal.IsDedekindDomain.ramificationIdx_eq_of_map_eq_pow (maximalIdeal A₁) M' 1 hmapA₁, ?_⟩
  have := (htame P).1
  have := isSeparable_residueField_of_pow_eq_unit_mul_pow hϖ u.isUnit he_B hd hβ_pow hgenS
  have : Algebra.IsSeparable (maximalIdeal A).ResidueField M'.ResidueField :=
    .trans _ P.ResidueField _
  have := Algebra.isSeparable_tower_top_of_isSeparable (maximalIdeal A).ResidueField
    (maximalIdeal A₁).ResidueField M'.ResidueField
  exact inferInstance

variable {A K L : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- Core Kummer elimination step for an abstract Kummer extension `K₁ = K(α₀)` inside `E = L(α₀)`.
Separating `K₁` from `K⟮β⟯` lets both `isUnramifiedWRT_of_pow_eq_of_irreducible` and `adjoin_root`
follow without transporting integral closures across subfield equivalences. -/
private theorem isUnramifiedWRT_of_pow_eq_of_irreducible_aux
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {n : ℕ}
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ n)
    {K₁ E : Type*} [Field K₁] [Algebra A K₁] [Algebra K K₁] [IsScalarTower A K K₁]
    [Field E] [Algebra A E] [Algebra K E] [Algebra L E] [Algebra K₁ E]
    [IsScalarTower A K E] [IsScalarTower K L E] [IsScalarTower K K₁ E]
    [IsLocalRing (integralClosure A K₁)]
    {α₀ : K₁} (hα₀ : α₀ ^ n = algebraMap A K₁ π) (hgenK₁ : K⟮α₀⟯ = ⊤)
    (hgenE : L⟮algebraMap K₁ E α₀⟯ = ⊤) :
    IsUnramifiedWRT (integralClosure A K₁) E ∧
      FiniteDimensional K₁ E ∧ Algebra.IsSeparable K₁ E := by
  have hn : n ≠ 0 := ne_zero_of_pow_eq_irreducible K hπ hα₀
  have : IsScalarTower A L E := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply K L E,
      ← IsScalarTower.algebraMap_apply A K E]
  have : IsScalarTower A K₁ E := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K K₁, ← IsScalarTower.algebraMap_apply K K₁ E,
      ← IsScalarTower.algebraMap_apply A K E]
  let A₁ := integralClosure A K₁
  have : IsScalarTower A A₁ E := ⟨fun a y z ↦ smul_assoc a (y : K₁) z⟩
  have : IsScalarTower A₁ K₁ E := ⟨fun y k z ↦ smul_assoc (y : K₁) k z⟩
  have : IsDiscreteValuationRing A₁ :=
    TauCeti.IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_of_pow_eq_of_irreducible
      hπ hα₀ hgenK₁
  have hdegK₁ := TauCeti.IsDiscreteValuationRing.finrank_eq_of_pow_eq_of_irreducible hπ hα₀ hgenK₁
  have : FiniteDimensional K K₁ :=
    Module.finite_of_finrank_pos (hdegK₁ ▸ Nat.pos_of_ne_zero hn)
  have : IsFractionRing A₁ K₁ := IsIntegralClosure.isFractionRing_of_finite_extension A K K₁ _
  have : FaithfulSMul A₁ E := .trans A₁ K₁ E
  have hα₀_mem : α₀ ∈ A₁ :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hα₀ ▸ isIntegral_algebraMap)
  let α₁ : A₁ := ⟨α₀, hα₀_mem⟩
  have hα₁ : Irreducible α₁ :=
    TauCeti.IsDiscreteValuationRing.irreducible_mk_of_pow_eq_of_irreducible hπ hα₀ hgenK₁ hα₀_mem
  have hα₁_K₁ : algebraMap A₁ K₁ α₁ = α₀ := rfl
  have hβ : (algebraMap A₁ E α₁) ^ n = algebraMap A E π := by
    rw [IsScalarTower.algebraMap_apply A₁ K₁ E, hα₁_K₁, ← map_pow, hα₀,
      ← IsScalarTower.algebraMap_apply A K₁ E]
  have hβ_intL : IsIntegral L (algebraMap K₁ E α₀) :=
    (IsIntegral.of_pow (Nat.pos_of_ne_zero hn)
      ((IsScalarTower.algebraMap_apply A₁ K₁ E α₁ ▸ hβ) ▸ isIntegral_algebraMap (R := A))).tower_top
  obtain ⟨hfinE, hsepE⟩ :=
    finiteDimensional_and_isSeparable_of_adjoin_eq_top (K := K) hβ_intL hgenE
  have hadjE : Algebra.adjoin L ({algebraMap A₁ E α₁} : Set E) = ⊤ :=
    (adjoin_simple_eq_top_iff_of_isAlgebraic hβ_intL.isAlgebraic).mp hgenE
  let C := integralClosure A L
  let C' := integralClosure A₁ E
  have : IsScalarTower C L E := ⟨fun c l z ↦ smul_assoc (c : L) l z⟩
  have : IsDedekindDomain C := integralClosure.isDedekindDomain A K L
  have : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L _
  have : IsDedekindDomain C' := integralClosure.isDedekindDomain A₁ K₁ E
  have : IsFractionRing C' E := IsIntegralClosure.isFractionRing_of_finite_extension A₁ K₁ E _
  let := integralClosureMapAlgebra A L A₁ E
  have := isScalarTower_integralClosureMapAlgebra_left A L A₁ E
  have := isScalarTower_integralClosureMapAlgebra_right A L A₁ E
  have : Algebra.IsIntegral A C' := Algebra.IsIntegral.trans A₁
  have : Algebra.IsIntegral C C' := .tower_top A
  refine ⟨isUnramifiedWRT_def.mpr fun M' _ _ ↦
    ramificationIdx_eq_one_and_isSeparable_at_maximal (K := K) (L := L) (C := C) (C' := C')
      hπ hα₁ hn hβ hadjE (isTamelyRamifiedWRT_def.mp h) hdvd M', hfinE, hsepE⟩

/-- **Eliminating tame ramification over a Kummer extension.** Let `L` be a finite separable
extension of the fraction field `K` of a discrete valuation ring `A` that is tamely ramified with
respect to `A`. Let `π` be a uniformizer of `A`, and let `n` be a multiple of every ramification
index of `L` over `A`. If `E` is generated over `L` by an `n`-th root `β` of `π`, then `E` is
unramified with respect to the integral closure `A[β]` of `A` in `K(β)`.

No invertibility assumption on `n` itself is needed: `n` may be a wild multiple of the tame
ramification indices. This is the finite separable case of Abhyankar's lemma for discrete valuation
rings (SGA 1, Exposé X, Lemme 3.6; Stacks, Lemma 15.116.4 (0BRM)), supplying the implication
(1) ⇒ (2), (3) of Stacks, Lemma 15.116.7 (0EXW). -/
@[stacks 0BRM "finite separable case over a Kummer extension"]
theorem IsTamelyRamifiedWRT.isUnramifiedWRT_of_pow_eq_of_irreducible
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {n : ℕ}
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ n)
    {E : Type*} [Field E] [Algebra A E] [Algebra K E] [Algebra L E]
    [IsScalarTower A K E] [IsScalarTower K L E] {β : E}
    [IsLocalRing (integralClosure A K⟮β⟯)]
    (hβ : β ^ n = algebraMap A E π) (hgen : L⟮β⟯ = ⊤) :
    IsUnramifiedWRT (integralClosure A K⟮β⟯) E := by
  have : IsScalarTower A K⟮β⟯ E := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K K⟮β⟯, ← IsScalarTower.algebraMap_apply K K⟮β⟯ E,
      ← IsScalarTower.algebraMap_apply A K E]
  have hα₀ : AdjoinSimple.gen K β ^ n = algebraMap A K⟮β⟯ π := (algebraMap K⟮β⟯ E).injective (by
    rw [map_pow, AdjoinSimple.algebraMap_gen, hβ, ← IsScalarTower.algebraMap_apply])
  exact (isUnramifiedWRT_of_pow_eq_of_irreducible_aux h hπ hdvd hα₀
    (_root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top β) hgen).1

/-- **Adjoining a root of a uniformizer to eliminate tame ramification.** In an ambient extension
field `Ω` of `L`, adjoining an `n`-th root `α` of a uniformizer `π` of `A` to both `K` and `L`,
where every ramification index of `L` over `A` divides `n`, makes `L(α)` unramified with respect to
the discrete valuation ring `integralClosure A K(α)`. -/
theorem IsTamelyRamifiedWRT.adjoin_root {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra L Ω]
    [Algebra A Ω] [IsScalarTower K L Ω] [IsScalarTower A K Ω]
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {n : ℕ}
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ n)
    {α : Ω} [IsLocalRing (integralClosure A K⟮α⟯)] (hα : α ^ n = algebraMap A Ω π) :
    letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
    IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ := by
  have : IsScalarTower A L Ω := .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A K Ω, IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply K L Ω]
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
  have : IsScalarTower A K L⟮α⟯ := .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A L L⟮α⟯,
      IsScalarTower.algebraMap_apply K L L⟮α⟯, ← IsScalarTower.algebraMap_apply A K L]
  have hαK : AdjoinSimple.gen K α ^ n = algebraMap A K⟮α⟯ π :=
    Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A K K⟮α⟯,
      IsScalarTower.algebraMap_apply A K Ω] using hα)
  have hgenL : L⟮algebraMap K⟮α⟯ L⟮α⟯ (AdjoinSimple.gen K α)⟯ = ⊤ := by
    have hgen_eq : algebraMap K⟮α⟯ L⟮α⟯ (AdjoinSimple.gen K α) = AdjoinSimple.gen L α :=
      TauCeti.IntermediateField.adjoinBaseChange_gen K L α
    rw [hgen_eq]
    exact _root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α
  exact (isUnramifiedWRT_of_pow_eq_of_irreducible_aux h hπ hdvd hαK
    (_root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α) hgenL).1

end EliminateRamification

section KummerCharacterization

variable {A K : Type*} {L : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

include K in
/-- **Common tame exponent.** For a finite separable extension `L / K` tamely ramified with respect
to `A`, there exists a positive integer `e₀`, invertible in the residue field of `A`, that is a
multiple of the ramification index of every maximal ideal of the integral closure of `A` in `L`. -/
theorem IsTamelyRamifiedWRT.exists_ramificationIdx_dvd (h : IsTamelyRamifiedWRT A L) :
    ∃ e₀ : ℕ, 1 ≤ e₀ ∧ IsUnit (e₀ : A ⧸ maximalIdeal A) ∧
      ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
        P.ramificationIdx A ∣ e₀ := by
  let C := integralClosure A L
  have : IsDedekindDomain C := integralClosure.isDedekindDomain A K L
  have : Module.Finite A C := IsIntegralClosure.finite A K L _
  have : FaithfulSMul A L := .trans A K L
  have : FaithfulSMul A C := .tower_bot A C L
  have : Module.IsTorsionFree A C := FaithfulSMul.to_isTorsionFree ..
  let e₀ : ℕ := ∏ Q : (maximalIdeal A).primesOver C, Q.1.ramificationIdx A
  have hpos : 0 < e₀ := Finset.prod_pos fun Q _ ↦ Ideal.ramificationIdx_pos A Q.1
  have hunit : IsUnit (e₀ : A ⧸ maximalIdeal A) := by
    rw [Nat.cast_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ ↦ IsUnit.mul) isUnit_one
      fun Q _ ↦ (isTamelyRamifiedWRT_def.mp h Q.1).2
  refine ⟨e₀, hpos, hunit, fun P _ _ ↦ ?_⟩
  simpa [e₀] using Finset.dvd_prod_of_mem
    (fun Q : (maximalIdeal A).primesOver C ↦ Q.1.ramificationIdx A)
    (Finset.mem_univ ⟨P, inferInstance, inferInstance⟩)

/-- Helper packaging `L(α)` inside an abstract algebraically closed overfield `Ω : Type u` as an
existential witness for `isTamelyRamifiedWRT_tfae`, avoiding unfolding `AlgebraicClosure L`. -/
private theorem exists_kummer_witness_of_dvd {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    [Algebra L Ω] [Algebra K Ω] [Algebra A Ω]
    [IsScalarTower K L Ω] [IsScalarTower A L Ω]
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {n : ℕ} (hn : 0 < n)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ n) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E) (_ : Algebra L E)
      (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E)
      (_ : FiniteDimensional K⟮β⟯ E) (_ : Algebra.IsSeparable K⟮β⟯ E)
      (_ : IsLocalRing (integralClosure A K⟮β⟯)),
      β ^ n = algebraMap A E π ∧ IsUnramifiedWRT (integralClosure A K⟮β⟯) E := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A Ω π) hn
  have hK : IsScalarTower A K L⟮α⟯ := .of_algebraMap_eq fun a ↦ by
    simp [IsScalarTower.algebraMap_apply A L L⟮α⟯,
      IsScalarTower.algebraMap_apply K L L⟮α⟯, ← IsScalarTower.algebraMap_apply A K L]
  let β : L⟮α⟯ := AdjoinSimple.gen L α
  have hβ : β ^ n = algebraMap A L⟮α⟯ π :=
    Subtype.ext (by simpa [β, IsScalarTower.algebraMap_apply A L L⟮α⟯,
      ← IsScalarTower.algebraMap_apply A L Ω] using hα)
  have hgenE : L⟮β⟯ = ⊤ := _root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α
  have : IsDiscreteValuationRing (integralClosure A K⟮β⟯) :=
    TauCeti.IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_adjoin hπ hβ
  have : IsScalarTower A K⟮β⟯ L⟮α⟯ := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K K⟮β⟯, ← IsScalarTower.algebraMap_apply K K⟮β⟯ L⟮α⟯,
      ← IsScalarTower.algebraMap_apply A K L⟮α⟯]
  have hβK : AdjoinSimple.gen K β ^ n = algebraMap A K⟮β⟯ π :=
    (algebraMap K⟮β⟯ L⟮α⟯).injective (by
      rw [map_pow, AdjoinSimple.algebraMap_gen, hβ, ← IsScalarTower.algebraMap_apply])
  obtain ⟨hunr, hfin, hsep⟩ := isUnramifiedWRT_of_pow_eq_of_irreducible_aux h hπ hdvd hβK
    (_root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top β) hgenE
  exact ⟨L⟮α⟯, inferInstance, inferInstance, inferInstance, inferInstance, hK, inferInstance,
    β, hfin, hsep, inferInstance, hβ, hunr⟩

/-- **Kummer characterization of tame ramification** (Stacks, Lemma 15.116.7). Let `A` be a
discrete valuation ring with fraction field `K` and uniformizer `π`, and let `L / K` be a finite
separable extension. The following are equivalent:

1. `L` is tamely ramified with respect to `A`;
2. there exist `e ≥ 1` invertible in `κ_A` and an extension `E` of `L` containing an `e`-th root
   `β` of `π` such that `E / K(β)` is finite separable and unramified with respect to the discrete
   valuation ring `integralClosure A K(β)`;
3. there exists `e₀ ≥ 1` invertible in `κ_A` such that for every `d` invertible in `κ_A`, clause
   (2) holds at exponent `d * e₀`. -/
@[stacks 0EXW]
theorem isTamelyRamifiedWRT_tfae {π : A} (hπ : Irreducible π) :
    List.TFAE
      [IsTamelyRamifiedWRT A L,
        ∃ e : ℕ, 1 ≤ e ∧ IsUnit (e : A ⧸ maximalIdeal A) ∧
          ∃ (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E) (_ : Algebra L E)
            (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E)
            (_ : FiniteDimensional K⟮β⟯ E) (_ : Algebra.IsSeparable K⟮β⟯ E)
            (_ : IsLocalRing (integralClosure A K⟮β⟯)),
            β ^ e = algebraMap A E π ∧ IsUnramifiedWRT (integralClosure A K⟮β⟯) E,
        ∃ e₀ : ℕ, 1 ≤ e₀ ∧ IsUnit (e₀ : A ⧸ maximalIdeal A) ∧
          ∀ d : ℕ, IsUnit (d : A ⧸ maximalIdeal A) →
            ∃ (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E) (_ : Algebra L E)
              (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E)
              (_ : FiniteDimensional K⟮β⟯ E) (_ : Algebra.IsSeparable K⟮β⟯ E)
              (_ : IsLocalRing (integralClosure A K⟮β⟯)),
              β ^ (d * e₀) = algebraMap A E π ∧ IsUnramifiedWRT (integralClosure A K⟮β⟯) E] := by
  tfae_have 1 → 3 := fun h ↦ by
    obtain ⟨e₀, he₀_pos, he₀_unit, hdvd⟩ := h.exists_ramificationIdx_dvd (K := K)
    refine ⟨e₀, he₀_pos, he₀_unit, fun d hd_unit ↦ ?_⟩
    let := Ideal.Quotient.field (maximalIdeal A)
    have hd_ne : d ≠ 0 := by rintro rfl; simp at hd_unit
    exact exists_kummer_witness_of_dvd (Ω := AlgebraicClosure L) h hπ
      (Nat.mul_pos (Nat.pos_of_ne_zero hd_ne) he₀_pos)
      (fun P _ _ ↦ dvd_mul_of_dvd_right (hdvd P) d)
  tfae_have 3 → 2 := fun h3 ↦
    h3.elim fun e₀ h3 ↦ by
      refine ⟨e₀, h3.1, h3.2.1, ?_⟩
      have h1 := h3.2.2 1 (by simp)
      rwa [one_mul] at h1
  tfae_have 2 → 1 := fun h2 ↦
    h2.elim fun _ he ↦ he.2.2.elim fun E hE ↦ hE.elim fun _ hE ↦ hE.elim fun _ hE ↦
    hE.elim fun _ hE ↦ hE.elim fun _ hE ↦ hE.elim fun _ hE ↦ hE.elim fun _ hE ↦
    hE.elim fun β hβ ↦ hβ.elim fun _ hβ ↦ hβ.elim fun _ hβ ↦ hβ.elim fun _ hβ ↦
    TauCeti.IsDiscreteValuationRing.isTamelyRamifiedWRT_of_isUnramifiedWRT_of_pow_eq_of_irreducible
      hπ he.2.1 hβ.1 hβ.2
  tfae_finish

/-- **Kummer characterization of tame ramification, existential form** (Stacks, Lemma 15.116.7,
(1) ⇔ (2)): `L` is tamely ramified with respect to `A` iff it embeds over `K` into an extension of
some tame Kummer extension `K(π ^ (1 / e))` that is unramified with respect to `A[π ^ (1 / e)]`. -/
@[stacks 0EXW "(1) ⇔ (2)"]
theorem isTamelyRamifiedWRT_iff_exists_kummer {π : A} (hπ : Irreducible π) :
    IsTamelyRamifiedWRT A L ↔
      ∃ e : ℕ, 1 ≤ e ∧ IsUnit (e : A ⧸ maximalIdeal A) ∧
        ∃ (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E) (_ : Algebra L E)
          (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E)
          (_ : FiniteDimensional K⟮β⟯ E) (_ : Algebra.IsSeparable K⟮β⟯ E)
          (_ : IsLocalRing (integralClosure A K⟮β⟯)),
          β ^ e = algebraMap A E π ∧ IsUnramifiedWRT (integralClosure A K⟮β⟯) E :=
  (isTamelyRamifiedWRT_tfae (K := K) (L := L) hπ).out 1 2

/-- **Kummer characterization of tame ramification, universal-multiple form** (Stacks, Lemma
15.116.7, (1) ⇔ (3)): `L` is tamely ramified with respect to `A` iff there exists `e₀ ≥ 1`
invertible in `κ_A` admitting an unramified Kummer witness at every tame multiple `d * e₀`. -/
@[stacks 0EXW "(1) ⇔ (3)"]
theorem isTamelyRamifiedWRT_iff_exists_forall_kummer {π : A} (hπ : Irreducible π) :
    IsTamelyRamifiedWRT A L ↔
      ∃ e₀ : ℕ, 1 ≤ e₀ ∧ IsUnit (e₀ : A ⧸ maximalIdeal A) ∧
        ∀ d : ℕ, IsUnit (d : A ⧸ maximalIdeal A) →
          ∃ (E : Type u) (_ : Field E) (_ : Algebra A E) (_ : Algebra K E) (_ : Algebra L E)
            (_ : IsScalarTower A K E) (_ : IsScalarTower K L E) (β : E)
            (_ : FiniteDimensional K⟮β⟯ E) (_ : Algebra.IsSeparable K⟮β⟯ E)
            (_ : IsLocalRing (integralClosure A K⟮β⟯)),
            β ^ (d * e₀) = algebraMap A E π ∧ IsUnramifiedWRT (integralClosure A K⟮β⟯) E :=
  (isTamelyRamifiedWRT_tfae (K := K) (L := L) hπ).out 1 3

/-- Inside an algebraically closed ambient extension `Ω` of `L`, `L` is tamely ramified with
respect to `A` iff there exist `e ≥ 1` invertible in `κ_A` and an `e`-th root `α ∈ Ω` of `π` such
that `L(α)` is unramified with respect to `integralClosure A K(α)`. -/
theorem isTamelyRamifiedWRT_iff_exists_adjoin_root {Ω : Type*} [Field Ω] [IsAlgClosed Ω]
    [Algebra K Ω] [Algebra L Ω] [Algebra A Ω] [IsScalarTower K L Ω] [IsScalarTower A K Ω]
    {π : A} (hπ : Irreducible π) :
    IsTamelyRamifiedWRT A L ↔
      ∃ (e : ℕ) (α : Ω), 1 ≤ e ∧ IsUnit (e : A ⧸ maximalIdeal A) ∧
        α ^ e = algebraMap A Ω π ∧
        letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
        ∃ _ : IsLocalRing (integralClosure A K⟮α⟯),
          IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ := by
  refine ⟨fun h ↦ ?_, fun hex ↦ hex.elim fun e hex ↦ hex.elim fun α hex ↦ ?_⟩
  · obtain ⟨e₀, he₀_pos, he₀_unit, hdvd⟩ := h.exists_ramificationIdx_dvd (K := K)
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A Ω π) he₀_pos
    have :=
      TauCeti.IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_adjoin (K := K) hπ hα
    exact ⟨e₀, α, he₀_pos, he₀_unit, hα, inferInstance, h.adjoin_root hπ hdvd hα⟩
  · refine hex.2.2.2.elim fun _ hunr ↦ ?_
    have he_unit := hex.2.1
    have hα := hex.2.2.1
    let := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
    have : IsScalarTower A L Ω := .of_algebraMap_eq fun a ↦ by
      simp [IsScalarTower.algebraMap_apply A K Ω, IsScalarTower.algebraMap_apply A K L,
        IsScalarTower.algebraMap_apply K L Ω]
    have :=
      TauCeti.IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_adjoin (K := K) hπ hα
    have hK₁ : IsTamelyRamifiedWRT A K⟮α⟯ :=
      TauCeti.IsDiscreteValuationRing.isTamelyRamifiedWRT_adjoin_of_pow_eq_of_irreducible
        hπ he_unit hα
    have : IsScalarTower A K L⟮α⟯ := .of_algebraMap_eq fun a ↦ by
      simp [IsScalarTower.algebraMap_apply A L L⟮α⟯,
        IsScalarTower.algebraMap_apply K L L⟮α⟯, ← IsScalarTower.algebraMap_apply A K L]
    have : IsScalarTower A K⟮α⟯ L⟮α⟯ :=
      IsScalarTower.of_algHom ((TauCeti.IntermediateField.adjoinBaseChange K L α).restrictScalars A)
    exact (hK₁.trans hunr.isTamelyRamifiedWRT).tower_bot K

end KummerCharacterization

end TauCeti.Algebra

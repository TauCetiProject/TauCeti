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
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.FieldTheory.IntermediateField.Adjoin.Defs
import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic
import TauCeti.RingTheory.DiscreteValuationRing.AbhyankarModel.Localization
import TauCeti.RingTheory.DiscreteValuationRing.BaseChange.Unramified
import TauCeti.RingTheory.DiscreteValuationRing.Kummer
import TauCeti.RingTheory.Etale.IntegralClosure
import TauCeti.RingTheory.IntegralClosure.TensorProduct
import TauCeti.RingTheory.Localization.AtPrime
import TauCeti.RingTheory.Localization.Integral
import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing

/-!
# Kummer characterization and base change of tamely ramified extensions

Let `A` be a discrete valuation ring with fraction field `K` and uniformizer `π`, and let `L / K`
be a finite separable extension. This file proves the Kummer characterization of tame ramification
(Stacks, Lemma 15.116.7 (0EXW)) and deduces stability of tamely ramified extensions under base
change along an arbitrary extension of discrete valuation rings (Stacks, Lemma 15.116.9 (0EXY),
the tame half).

The elimination of tame ramification follows SGA 1, Exposé X, Lemme 3.6 and Stacks, Lemma 15.116.4
(0BRM) via the local structure of the Abhyankar model
(`TauCeti.exists_algEquiv_localization_abhyankarModel`). If `L / K` is tamely ramified with respect
to `A` and `n` is a multiple of every ramification index over `A`, adjoining an `n`-th root `β` of
`π` produces an extension `L(β) / K(β)` that is unramified with respect to the integral closure
`A[β]` of `A` in `K(β)` (`TauCeti.Algebra.IsTamelyRamifiedWRT.adjoin_root`): each localization of
the integral closure of `A[β]` in `L(β)` at a maximal ideal is isomorphic to a localization of the
Abhyankar model over the corresponding discrete valuation ring of `L`, so `β` remains a uniformizer
there and the residue extension remains separable. Taking `e₀` to be the product of the ramification
indices over `A` gives an exponent invertible in `κ_A`, and any further multiple `d * e₀` (including
wild multiples when `d ≠ 0`) works the same way. Together with the converse
`TauCeti.IsDiscreteValuationRing.isTamelyRamifiedWRT_of_isUnramifiedWRT_of_pow_eq_of_irreducible`,
this gives the three-way equivalence of Lemma 15.116.7 (`TauCeti.Algebra.isTamelyRamifiedWRT_tfae`).

For base change along an extension of discrete valuation rings `A → A'` with fraction fields
`K → K'`, write the image of `π` in `A'` as `u' ϖ' ^ m` for a unit `u'` and a uniformizer `ϖ'` of
`A'`. Over an algebraic closure of a factor field `L'` of `K' ⊗[K] L`, extracting `e₀`-th roots
`β'` of `ϖ'` and `γ'` of `u'` gives an `e₀`-th root `α' = γ' β' ^ m` of `π`. Then `L(α') / K(α')`
is unramified over `A[α']`, while `K'(β', γ') / K'(β')` is unramified over `A'[β']` because `u'` and
`e₀` are units in `A'[β']` (`TauCeti.IsDiscreteValuationRing.isUnramifiedWRT_of_pow_eq_of_isUnit`).
Tensoring the two finite étale integral closures exhibits `L'(β', γ')` as a field quotient of the
generic fibre of a finite étale `A'[β']`-algebra, hence unramified over `A'[β']`, which forces
`L'` to be tamely ramified with respect to `A'`. As in the unramified case, `A → A'` need not be a
local homomorphism.

## Main results

* `TauCeti.IsDiscreteValuationRing.isUnramifiedWRT_of_pow_eq_of_isUnit`: adjoining an `n`-th root
  of a unit of `A`, with `n` invertible in `A`, gives an extension unramified with respect to `A`.
* `TauCeti.IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_adjoin`: for an `n`-th
  root `α` of a uniformizer of `A` in an extension of `K`, `integralClosure A K(α)` is a discrete
  valuation ring.
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
* `TauCeti.Algebra.IsTamelyRamifiedWRT.baseChange`: tamely ramified extensions of a discrete
  valuation ring are stable under base change (Stacks, Lemma 15.116.9, tame case).

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé X, Lemme 3.6.
* [Stacks Project, Lemma 15.116.4](https://stacks.math.columbia.edu/tag/0BRM).
* [Stacks Project, Lemma 15.116.7](https://stacks.math.columbia.edu/tag/0EXW).
* [Stacks Project, Lemma 15.116.9](https://stacks.math.columbia.edu/tag/0EXY).
-/

public section

universe u v

open scoped TensorProduct
open _root_.IntermediateField IsLocalRing Polynomial

namespace TauCeti.IsDiscreteValuationRing

section KummerHelpers

variable {A K L : Type*} [CommRing A] [IsDomain A] [_root_.IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]

omit [IsFractionRing A K] in
/-- When `L = K(γ)` for an `n`-th root `γ` of `u ∈ A` with `n` invertible in `A`, the generic fibre
`K ⊗[A] A[x]/(x ^ n - u)` maps surjectively onto `L`. -/
private theorem exists_surjective_tensor_standardTameCover {u : A} {n : ℕ} (hn : IsUnit (n : A))
    {γ : L} (hγ : γ ^ n = algebraMap A L u) (hgen : K⟮γ⟯ = ⊤) :
    ∃ χ : K ⊗[A] standardTameCover A u n →ₐ[K] L, Function.Surjective χ := by
  have hn₀ : n ≠ 0 := hn.neZero_natCast.out
  let ψ : standardTameCover A u n →ₐ[A] L :=
    AdjoinRoot.liftAlgHom (X ^ n - C u) (Algebra.ofId A L) γ (by simp [hγ])
  let χ : K ⊗[A] standardTameCover A u n →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) ψ fun _ _ ↦ .all _ _
  refine ⟨χ, ?_⟩
  have hγ_int : IsIntegral K γ :=
    (IsIntegral.of_pow (Nat.pos_of_ne_zero hn₀) (hγ ▸ isIntegral_algebraMap (R := A))).tower_top
  have hadj : Algebra.adjoin K ({γ} : Set L) = ⊤ :=
    (adjoin_simple_eq_top_iff_of_isAlgebraic hγ_int.isAlgebraic).mp hgen
  have hmem : γ ∈ χ.range :=
    ⟨1 ⊗ₜ[A] AdjoinRoot.root (X ^ n - C u), by simp [χ, ψ]⟩
  have htop : χ.range = ⊤ :=
    top_unique (hadj ▸ Algebra.adjoin_le (Set.singleton_subset_iff.mpr hmem))
  intro x
  have hx : x ∈ χ.range := htop ▸ Algebra.mem_top
  exact (AlgHom.mem_range χ).mp hx

/-- **Adjoining a tame root of a unit is unramified.** Let `A` be a discrete valuation ring with
fraction field `K`. If `L` is generated over `K` by an `n`-th root `γ` of a unit `u` of `A`, with
`n` invertible in `A`, then `L` is unramified with respect to `A`. -/
theorem isUnramifiedWRT_of_pow_eq_of_isUnit {u : A} (hu : IsUnit u) {n : ℕ} (hn : IsUnit (n : A))
    {γ : L} (hγ : γ ^ n = algebraMap A L u) (hgen : K⟮γ⟯ = ⊤) :
    Algebra.IsUnramifiedWRT A L := by
  have := hn.neZero_natCast
  have := standardTameCover_etale hu hn
  obtain ⟨χ, hχ⟩ := exists_surjective_tensor_standardTameCover hn hγ hgen
  exact χ.isUnramifiedWRT_of_surjective hχ

/-- Under the hypotheses of `isUnramifiedWRT_of_pow_eq_of_isUnit`, the integral closure of `A` in
`L` is finite étale over `A`. -/
private theorem etale_and_finite_integralClosure_of_pow_eq_of_isUnit {u : A} (hu : IsUnit u)
    {n : ℕ} (hn : IsUnit (n : A)) {γ : L} (hγ : γ ^ n = algebraMap A L u) (hgen : K⟮γ⟯ = ⊤) :
    Algebra.Etale A (integralClosure A L) ∧ Module.Finite A (integralClosure A L) := by
  have := hn.neZero_natCast
  have := standardTameCover_etale hu hn
  have : IsIntegrallyClosedIn A K :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mp inferInstance
  obtain ⟨χ, hχ⟩ := exists_surjective_tensor_standardTameCover hn hγ hgen
  have : FiniteDimensional K L := Module.Finite.of_surjective χ.toLinearMap hχ
  have : Algebra.Etale A (integralClosure A L) := χ.etale_integralClosure_of_surjective hχ
  have : Algebra.IsSeparable K L :=
    have : Algebra.FormallyUnramified K L := .of_surjective χ hχ
    (Algebra.FormallyUnramified.iff_isSeparable K L).mp this
  exact ⟨‹_›, IsIntegralClosure.finite A K L _⟩

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

/-- When `n` is invertible in `κ_A`, the subfield `K(α)` generated by an `n`-th root `α` of a
uniformizer `π` of `A` is tamely ramified with respect to `A`. -/
private theorem isTamelyRamifiedWRT_adjoin_of_pow_eq_of_irreducible {π : A} (hπ : Irreducible π)
    {n : ℕ} (hn : IsUnit (n : A ⧸ maximalIdeal A)) {α : L} (hα : α ^ n = algebraMap A L π) :
    Algebra.IsTamelyRamifiedWRT A K⟮α⟯ := by
  have hαK : AdjoinSimple.gen K α ^ n = algebraMap A K⟮α⟯ π :=
    Subtype.ext (by simpa [IsScalarTower.algebraMap_apply A K K⟮α⟯,
      IsScalarTower.algebraMap_apply A K L] using hα)
  exact (isTamelyRamifiedWRT_iff_of_pow_eq_of_irreducible hπ hαK
    (_root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α)).mpr hn

end KummerHelpers

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
    [Field E] [Algebra A E] [Algebra K E] [Algebra L E] [Algebra A₁ E] [Algebra C E] [Algebra C' E]
    [IsScalarTower A K E] [IsScalarTower K L E] [IsScalarTower A L E]
    [IsScalarTower A A₁ E] [IsScalarTower A₁ C' E] [IsScalarTower C C' E] [IsScalarTower C L E]
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

/-- Internal version of `adjoin_root` also returning `FiniteDimensional` and `IsSeparable`. -/
private theorem adjoin_root_aux {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra L Ω]
    [Algebra A Ω] [IsScalarTower K L Ω] [IsScalarTower A K Ω]
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {n : ℕ}
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ n)
    {α : Ω} [IsLocalRing (integralClosure A K⟮α⟯)] (hα : α ^ n = algebraMap A Ω π) :
    letI := (TauCeti.IntermediateField.adjoinBaseChange K L α).toAlgebra
    IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ ∧
      FiniteDimensional K⟮α⟯ L⟮α⟯ ∧ Algebra.IsSeparable K⟮α⟯ L⟮α⟯ := by
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
  exact isUnramifiedWRT_of_pow_eq_of_irreducible_aux h hπ hdvd hαK
    (_root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top α) hgenL

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
    IsUnramifiedWRT (integralClosure A K⟮α⟯) L⟮α⟯ :=
  (adjoin_root_aux h hπ hdvd hα).1

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
    [IsScalarTower K L Ω] [IsScalarTower A K Ω] [IsScalarTower A L Ω]
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

section BaseChange

/-- If `x` is integral over `F` and an `F`-subalgebra `S` of `M` contains the image of the
distinguished generator of `F(x)` under `f : F(x) →ₐ[F] M`, then `S` contains the entire image of
`f`. -/
private theorem map_mem_of_gen_mem_subalgebra {F Ω M : Type*} [Field F] [Field Ω] [Algebra F Ω]
    [CommSemiring M] [Algebra F M] {x : Ω} (hx : IsIntegral F x)
    (f : F⟮x⟯ →ₐ[F] M) {S : Subalgebra F M} (hmem : f (AdjoinSimple.gen F x) ∈ S)
    (z : F⟮x⟯) : f z ∈ S := by
  have hadj : Algebra.adjoin F ({AdjoinSimple.gen F x} : Set F⟮x⟯) = ⊤ :=
    (adjoin_simple_eq_top_iff_of_isAlgebraic
      ((AdjoinSimple.isIntegral_gen F x).mpr hx).isAlgebraic).mp
      (_root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top x)
  have hgen : AdjoinSimple.gen F x ∈ S.comap f := (Subalgebra.mem_comap _ _ _).mpr hmem
  have htop : S.comap f = ⊤ :=
    top_unique (hadj ▸ Algebra.adjoin_le (Set.singleton_subset_iff.mpr hgen))
  exact (Subalgebra.mem_comap _ _ _).mp (htop ▸ Algebra.mem_top : z ∈ S.comap f)

/-- Membership underlying `adjoinSimpleInclusionRingHom`. -/
private theorem mem_of_adjoin_simple_mem {F₁ F₂ Ω : Type*} [Field F₁] [Field F₂] [Field Ω]
    [Algebra F₁ Ω] [Algebra F₂ Ω] {x : Ω} {E : IntermediateField F₂ Ω}
    (hF₁ : ∀ c : F₁, algebraMap F₁ Ω c ∈ E) (hx : x ∈ E) {z : Ω} (hz : z ∈ F₁⟮x⟯) :
    z ∈ E :=
  let E' : IntermediateField F₁ Ω :=
    { E.toSubalgebra with algebraMap_mem' := hF₁, inv_mem' := E.inv_mem' }
  IsConcreteLE.le_iff.mp (adjoin_simple_le_iff (K := E').mpr hx) hz

/-- If `E : IntermediateField F₂ Ω` contains `x` and the image of `F₁`, then `F₁(x) ⊆ E` inside `Ω`,
yielding a canonical ring homomorphism `F₁(x) →+* E` preserving ambient values. -/
private def adjoinSimpleInclusionRingHom {F₁ F₂ Ω : Type*} [Field F₁] [Field F₂] [Field Ω]
    [Algebra F₁ Ω] [Algebra F₂ Ω] {x : Ω} {E : IntermediateField F₂ Ω}
    (hF₁ : ∀ c : F₁, algebraMap F₁ Ω c ∈ E) (hx : x ∈ E) : F₁⟮x⟯ →+* E where
  toFun z := ⟨z.1, mem_of_adjoin_simple_mem hF₁ hx z.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A ring homomorphism `g : K₁ →+* K'₂` compatible with `A → A'₁ → K'₂` restricts to a ring
homomorphism `integralClosure A K₁ →+* integralClosure A'₁ K'₂`. -/
private def mapIntegralClosure
    {A K₁ A'₁ K'₂ : Type*} [CommRing A] [CommRing K₁] [Algebra A K₁]
    [CommRing A'₁] [CommRing K'₂] [Algebra A'₁ K'₂]
    (φ : A →+* A'₁) (g : K₁ →+* K'₂)
    (hg : ∀ r : A, g (algebraMap A K₁ r) = algebraMap A'₁ K'₂ (φ r)) :
    integralClosure A K₁ →+* integralClosure A'₁ K'₂ where
  toFun a := ⟨g a.1, a.2.map_of_comp_eq φ g (RingHom.ext fun r ↦ (hg r).symm)⟩
  map_one' := Subtype.ext g.map_one
  map_mul' _ _ := Subtype.ext (g.map_mul _ _)
  map_zero' := Subtype.ext g.map_zero
  map_add' _ _ := Subtype.ext (g.map_add _ _)

/-- Surjectivity of the generic-fibre map onto the double root extension `L'(β', γ')` inside `Ω'`,
factored out from `isUnramifiedWRT_compositum_of_closures`. -/
private theorem surjective_compositum_lift
    {K L K' L' Ω' K₁ L₁ A₁ : Type*}
    [Field K] [Field L] [Algebra K L] [Field K'] [Algebra K K']
    [Field L'] [Algebra K' L'] [Algebra L L'] [Algebra K L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']
    [Field Ω'] [Algebra L' Ω'] [Algebra K' Ω'] [Algebra L Ω'] [Algebra K Ω']
    [IsScalarTower K' L' Ω'] [IsScalarTower L L' Ω'] [IsScalarTower K K' Ω']
    [CommRing A₁] [Field K₁] [Algebra A₁ K₁] [IsFractionRing A₁ K₁]
    [Field L₁] [Algebra A₁ L₁] [Algebra K₁ L₁] [IsScalarTower A₁ K₁ L₁]
    [Algebra.IsAlgebraic K₁ L₁] [Algebra L L₁]
    (φ : K' ⊗[K] L →ₐ[K'] L') (hφ : Function.Surjective φ)
    (hφL : ∀ l : L, φ (1 ⊗ₜ[K] l) = algebraMap L L' l)
    {β' γ' : Ω'} (hβ'_int : IsIntegral L' β') (hγ'_intL : IsIntegral L' γ')
    (hγ'_intK : IsIntegral K'⟮β'⟯ γ')
    (ιK : K₁ →+* (K'⟮β'⟯)⟮γ'⟯)
    (ιL₁ : L₁ →+* IntermediateField.adjoin L' ({β', γ'} : Set Ω'))
    (hιL : ∀ l : L, (ιL₁ (algebraMap L L₁ l) : Ω') = algebraMap L Ω' l)
    (hιsmul : ∀ (c : K₁) (x : L₁), (ιL₁ (c • x) : Ω') = (ιK c : Ω') * (ιL₁ x : Ω'))
    (ιK'₁ : K'⟮β'⟯ →+* IntermediateField.adjoin L' ({β', γ'} : Set Ω'))
    (hιK'₁ : ∀ x : K'⟮β'⟯, (ιK'₁ x : Ω') = x)
    (ιK'₂ : (K'⟮β'⟯)⟮γ'⟯ →+* IntermediateField.adjoin L' ({β', γ'} : Set Ω'))
    (hιK'₂ : ∀ x : (K'⟮β'⟯)⟮γ'⟯, (ιK'₂ x : Ω') = x)
    {T : Type*} [CommRing T]
    (χ : T →+* IntermediateField.adjoin L' ({β', γ'} : Set Ω'))
    (hK'₁_R : ∀ x : K'⟮β'⟯, ιK'₁ x ∈ χ.range)
    (hγ'_R : ιK'₂ (AdjoinSimple.gen K'⟮β'⟯ γ') ∈ χ.range)
    (hB₁_R : ∀ b : integralClosure A₁ L₁, ιL₁ b ∈ χ.range) :
    Function.Surjective χ := by
  let E'' : IntermediateField L' Ω' := IntermediateField.adjoin L' ({β', γ'} : Set Ω')
  let R : Subring E'' := χ.range
  have hK'₂_R : ∀ z : (K'⟮β'⟯)⟮γ'⟯, ιK'₂ z ∈ R := by
    let : Algebra K'⟮β'⟯ E'' := ιK'₁.toAlgebra
    have hιK'₂_alg (x : K'⟮β'⟯) :
        ιK'₂ (algebraMap K'⟮β'⟯ (K'⟮β'⟯)⟮γ'⟯ x) = algebraMap K'⟮β'⟯ E'' x :=
      Subtype.ext (by rw [hιK'₂, RingHom.algebraMap_toAlgebra, hιK'₁]; rfl)
    let ιK'₂_a : (K'⟮β'⟯)⟮γ'⟯ →ₐ[K'⟮β'⟯] E'' := { ιK'₂ with commutes' := hιK'₂_alg }
    let R_K'₁ : Subalgebra K'⟮β'⟯ E'' := { R with algebraMap_mem' := hK'₁_R }
    exact fun z ↦ map_mem_of_gen_mem_subalgebra hγ'_intK ιK'₂_a (S := R_K'₁) hγ'_R z
  have hL₁_R (w : L₁) : ιL₁ w ∈ R := by
    have hw : w ∈ Submodule.span K₁ (integralClosure A₁ L₁ : Set L₁) :=
      span_integralClosure_eq_top (A := A₁) (K := K₁) (L := L₁) ▸ Submodule.mem_top
    refine Submodule.span_induction (fun b hb ↦ hB₁_R ⟨b, hb⟩)
      (by rw [map_zero]; exact R.zero_mem)
      (fun x y _ _ hx hy ↦ by rw [map_add]; exact R.add_mem hx hy) (fun c x _ hx ↦ ?_) hw
    have hmul : ιL₁ (c • x) = ιK'₂ (ιK c) * ιL₁ x :=
      Subtype.ext (by rw [MulMemClass.coe_mul, hιK'₂, hιsmul])
    exact hmul ▸ R.mul_mem (hK'₂_R (ιK c)) hx
  have hL'_R (w : L') : algebraMap L' E'' w ∈ R := by
    obtain ⟨t, rfl⟩ := hφ w
    refine TensorProduct.inductionOn t (fun k' l ↦ ?_)
      (fun x y hx hy ↦ by rw [map_add, map_add]; exact R.add_mem hx hy)
    have hk' : algebraMap L' E'' (algebraMap K' L' k') = ιK'₁ (algebraMap K' K'⟮β'⟯ k') :=
      Subtype.ext (by rw [IntermediateField.coe_algebraMap_apply,
        ← IsScalarTower.algebraMap_apply K' L' Ω', hιK'₁, IntermediateField.coe_algebraMap_apply])
    have hl : algebraMap L' E'' (φ (1 ⊗ₜ[K] l)) = ιL₁ (algebraMap L L₁ l) :=
      Subtype.ext (by rw [hφL, IntermediateField.coe_algebraMap_apply,
        ← IsScalarTower.algebraMap_apply L L' Ω', hιL])
    have htmul : φ (k' ⊗ₜ[K] l) = algebraMap K' L' k' * φ (1 ⊗ₜ[K] l) := by
      have hk : k' ⊗ₜ[K] l = k' • ((1 : K') ⊗ₜ[K] l) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hk, map_smul, Algebra.smul_def]
    rw [htmul, map_mul, hk', hl]
    exact R.mul_mem (hK'₁_R _) (hL₁_R _)
  let R_L' : Subalgebra L' E'' := { R with algebraMap_mem' := hL'_R }
  have hsub : ({β', γ'} : Set Ω') ⊆ (R_L'.map E''.val : Subalgebra L' Ω') :=
    Set.insert_subset_iff.mpr
      ⟨⟨ιK'₁ (AdjoinSimple.gen K' β'), hK'₁_R _, hιK'₁ _⟩,
        Set.singleton_subset_iff.mpr ⟨ιK'₂ (AdjoinSimple.gen K'⟮β'⟯ γ'), hγ'_R, hιK'₂ _⟩⟩
  have halg : ∀ x ∈ ({β', γ'} : Set Ω'), IsAlgebraic L' x := fun x hx ↦ by
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · exact hx.symm ▸ hβ'_int.isAlgebraic
    · exact (Set.mem_singleton_iff.mp hx).symm ▸ hγ'_intL.isAlgebraic
  intro z
  have hz₀ : (z : Ω') ∈ E''.toSubalgebra := z.2
  rw [adjoin_toSubalgebra_of_isAlgebraic halg] at hz₀
  obtain ⟨w, hw, hwz⟩ := Subalgebra.mem_map.mp (Algebra.adjoin_le hsub hz₀)
  exact Subtype.ext hwz ▸ hw

/-- Assembles the `K'₁`-algebra map `K'₁ ⊗[A'₁] (A'₂ ⊗[A₁] B₁) →ₐ[K'₁] E''` from compatible ring
homomorphisms out of `A'₂` and `B₁`. -/
private def lift_compositum_tensor
    {A₁ A'₁ K'₁ A'₂ B₁ E'' : Type*} [CommRing A₁] [CommRing A'₁] [CommRing K'₁]
    [CommRing A'₂] [CommRing B₁] [CommRing E'']
    [Algebra A'₁ K'₁] [Algebra A'₁ A'₂] [Algebra A₁ A'₂] [Algebra A₁ B₁] [Algebra K'₁ E'']
    (fA'₂ : A'₂ →+* E'') (fB₁ : B₁ →+* E'')
    (hA₁ : ∀ a : A₁, fB₁ (algebraMap A₁ B₁ a) = fA'₂ (algebraMap A₁ A'₂ a))
    (hA'₁ : ∀ y : A'₁, fA'₂ (algebraMap A'₁ A'₂ y) = algebraMap K'₁ E'' (algebraMap A'₁ K'₁ y)) :
    K'₁ ⊗[A'₁] (A'₂ ⊗[A₁] B₁) →ₐ[K'₁] E'' :=
  letI : Algebra A₁ E'' := (fA'₂.comp (algebraMap A₁ A'₂)).toAlgebra
  letI : Algebra A'₁ E'' := ((algebraMap K'₁ E'').comp (algebraMap A'₁ K'₁)).toAlgebra
  haveI : IsScalarTower A'₁ K'₁ E'' := .of_algebraMap_eq fun _ ↦ rfl
  let fA'₂_a : A'₂ →ₐ[A₁] E'' := { fA'₂ with commutes' := fun _ ↦ rfl }
  let fB₁_a : B₁ →ₐ[A₁] E'' := { fB₁ with commutes' := hA₁ }
  let ψ₀ : A'₂ ⊗[A₁] B₁ →ₐ[A₁] E'' := Algebra.TensorProduct.lift fA'₂_a fB₁_a fun _ _ ↦ .all _ _
  let ψ : A'₂ ⊗[A₁] B₁ →ₐ[A'₁] E'' :=
    { ψ₀.toRingHom with
      commutes' := fun y ↦ by
        simp [ψ₀, fA'₂_a, Algebra.TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra,
          hA'₁] }
  Algebra.TensorProduct.lift (Algebra.ofId K'₁ E'') ψ fun _ _ ↦ .all _ _

private theorem lift_compositum_tensor_tmul_one
    {A₁ A'₁ K'₁ A'₂ B₁ E'' : Type*} [CommRing A₁] [CommRing A'₁] [CommRing K'₁]
    [CommRing A'₂] [CommRing B₁] [CommRing E'']
    [Algebra A'₁ K'₁] [Algebra A'₁ A'₂] [Algebra A₁ A'₂] [Algebra A₁ B₁] [Algebra K'₁ E'']
    (fA'₂ : A'₂ →+* E'') (fB₁ : B₁ →+* E'')
    (hA₁ : ∀ a : A₁, fB₁ (algebraMap A₁ B₁ a) = fA'₂ (algebraMap A₁ A'₂ a))
    (hA'₁ : ∀ y : A'₁, fA'₂ (algebraMap A'₁ A'₂ y) = algebraMap K'₁ E'' (algebraMap A'₁ K'₁ y))
    (x : K'₁) :
    lift_compositum_tensor fA'₂ fB₁ hA₁ hA'₁ (x ⊗ₜ[A'₁] (1 : A'₂ ⊗[A₁] B₁)) =
      algebraMap K'₁ E'' x := by
  simp [lift_compositum_tensor]

private theorem lift_compositum_tensor_one_tmul_left
    {A₁ A'₁ K'₁ A'₂ B₁ E'' : Type*} [CommRing A₁] [CommRing A'₁] [CommRing K'₁]
    [CommRing A'₂] [CommRing B₁] [CommRing E'']
    [Algebra A'₁ K'₁] [Algebra A'₁ A'₂] [Algebra A₁ A'₂] [Algebra A₁ B₁] [Algebra K'₁ E'']
    (fA'₂ : A'₂ →+* E'') (fB₁ : B₁ →+* E'')
    (hA₁ : ∀ a : A₁, fB₁ (algebraMap A₁ B₁ a) = fA'₂ (algebraMap A₁ A'₂ a))
    (hA'₁ : ∀ y : A'₁, fA'₂ (algebraMap A'₁ A'₂ y) = algebraMap K'₁ E'' (algebraMap A'₁ K'₁ y))
    (a : A'₂) :
    lift_compositum_tensor fA'₂ fB₁ hA₁ hA'₁ ((1 : K'₁) ⊗ₜ[A'₁] (a ⊗ₜ[A₁] (1 : B₁))) =
      fA'₂ a := by
  simp [lift_compositum_tensor]

private theorem lift_compositum_tensor_one_tmul_right
    {A₁ A'₁ K'₁ A'₂ B₁ E'' : Type*} [CommRing A₁] [CommRing A'₁] [CommRing K'₁]
    [CommRing A'₂] [CommRing B₁] [CommRing E'']
    [Algebra A'₁ K'₁] [Algebra A'₁ A'₂] [Algebra A₁ A'₂] [Algebra A₁ B₁] [Algebra K'₁ E'']
    (fA'₂ : A'₂ →+* E'') (fB₁ : B₁ →+* E'')
    (hA₁ : ∀ a : A₁, fB₁ (algebraMap A₁ B₁ a) = fA'₂ (algebraMap A₁ A'₂ a))
    (hA'₁ : ∀ y : A'₁, fA'₂ (algebraMap A'₁ A'₂ y) = algebraMap K'₁ E'' (algebraMap A'₁ K'₁ y))
    (b : B₁) :
    lift_compositum_tensor fA'₂ fB₁ hA₁ hA'₁ ((1 : K'₁) ⊗ₜ[A'₁] ((1 : A'₂) ⊗ₜ[A₁] b)) =
      fB₁ b := by
  simp [lift_compositum_tensor]

/-- Over an abstract discrete valuation ring `R`, an extension unramified with respect to `R` has
finite étale integral closure. -/
private theorem etale_and_finite_of_isUnramifiedWRT
    {R F E : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra R E] [Algebra F E] [IsScalarTower R F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (h : IsUnramifiedWRT R E) :
    Algebra.Etale R (integralClosure R E) ∧ Module.Finite R (integralClosure R E) :=
  ⟨(isUnramifiedWRT_iff_etale R F E).mp h, IsIntegralClosure.finite R F E _⟩

/-- Over abstract fields `K'₁` and `E''` and finite étale algebras `A'₂ / A'₁` and `B₁ / A₁`, if
the induced `K'₁`-algebra map `K'₁ ⊗[A'₁] (A'₂ ⊗[A₁] B₁) →ₐ[K'₁] E''` is surjective whenever its
range contains `algebraMap K'₁ E''`, `fA'₂ γ'₀`, and `fB₁`, then `E''` is unramified over `A'₁`. -/
private theorem isUnramifiedWRT_of_compositum_closures
    (A₁ B₁ A'₁ K'₁ A'₂ E'' : Type v)
    [CommRing A₁] [CommRing B₁] [Algebra A₁ B₁] [Algebra.Etale A₁ B₁] [Module.Finite A₁ B₁]
    [CommRing A'₁] [IsDomain A'₁] [IsDiscreteValuationRing A'₁]
    [Field K'₁] [Algebra A'₁ K'₁] [IsFractionRing A'₁ K'₁]
    [CommRing A'₂] [Algebra A'₁ A'₂] [Algebra.Etale A'₁ A'₂] [Module.Finite A'₁ A'₂]
    [Field E''] [Algebra A'₁ E''] [Algebra K'₁ E''] [IsScalarTower A'₁ K'₁ E'']
    (fA₁ : A₁ →+* A'₂) (fA'₂ : A'₂ →+* E'') (fB₁ : B₁ →+* E'')
    (hA₁ : ∀ a : A₁, fB₁ (algebraMap A₁ B₁ a) = fA'₂ (fA₁ a))
    (hA'₁ : ∀ y : A'₁, fA'₂ (algebraMap A'₁ A'₂ y) = algebraMap K'₁ E'' (algebraMap A'₁ K'₁ y))
    (γ'₀ : A'₂)
    (hsurj : ∀ {T : Type v} [CommRing T] (χ : T →+* E''),
      (∀ x : K'₁, algebraMap K'₁ E'' x ∈ χ.range) →
      fA'₂ γ'₀ ∈ χ.range →
      (∀ b : B₁, fB₁ b ∈ χ.range) →
      Function.Surjective χ) :
    IsUnramifiedWRT A'₁ E'' := by
  let : Algebra A₁ A'₂ := fA₁.toAlgebra
  let S' := A'₂ ⊗[A₁] B₁
  have : Algebra.Etale A'₁ S' := .comp A'₁ A'₂ S'
  have : Module.Finite A'₁ S' := .trans A'₂ S'
  let χ : K'₁ ⊗[A'₁] S' →ₐ[K'₁] E'' := lift_compositum_tensor fA'₂ fB₁ hA₁ hA'₁
  have hχ : Function.Surjective χ :=
    hsurj χ.toRingHom
      (fun x ↦ ⟨x ⊗ₜ[A'₁] (1 : S'), lift_compositum_tensor_tmul_one _ _ hA₁ hA'₁ x⟩)
      ⟨(1 : K'₁) ⊗ₜ[A'₁] (γ'₀ ⊗ₜ[A₁] (1 : B₁)),
        lift_compositum_tensor_one_tmul_left _ _ hA₁ hA'₁ γ'₀⟩
      (fun b ↦ ⟨(1 : K'₁) ⊗ₜ[A'₁] ((1 : A'₂) ⊗ₜ[A₁] b),
        lift_compositum_tensor_one_tmul_right _ _ hA₁ hA'₁ b⟩)
  exact χ.isUnramifiedWRT_of_surjective hχ

/-- If `γ' ^ e₀ = algebraMap A' Ω' x` with `0 < e₀`, the generator of `K'₁(γ')` is integral over
`integralClosure A' K'₁`. -/
private theorem isIntegral_adjoinSimple_gen_of_pow_eq
    {A' K'₁ Ω' : Type*} [CommRing A'] [Field K'₁] [Field Ω'] [Algebra A' K'₁]
    [Algebra A' Ω'] [Algebra K'₁ Ω'] [IsScalarTower A' K'₁ Ω']
    {γ' : Ω'} {e₀ : ℕ} (he₀_pos : 0 < e₀) {x : A'} (hγ' : γ' ^ e₀ = algebraMap A' Ω' x) :
    IsIntegral (integralClosure A' K'₁) (AdjoinSimple.gen K'₁ γ') := by
  have h : AdjoinSimple.gen K'₁ γ' ^ e₀ = algebraMap A' K'₁⟮γ'⟯ x := Subtype.ext (by
    rw [IsScalarTower.algebraMap_apply A' K'₁ K'₁⟮γ'⟯, IntermediateField.coe_algebraMap_apply,
      ← IsScalarTower.algebraMap_apply A' K'₁ Ω']
    exact hγ')
  exact (IsIntegral.of_pow he₀_pos (h ▸ isIntegral_algebraMap (R := A'))).tower_top

variable {A K L A' K' L' : Type*}
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [CommRing A'] [IsDomain A'] [IsDiscreteValuationRing A'] [Field K'] [Algebra A' K']
  [IsFractionRing A' K'] [Algebra A A'] [Algebra A K'] [Algebra K K'] [IsScalarTower A A' K']
  [IsScalarTower A K K'] [Field L'] [Algebra K' L'] [Algebra A' L'] [IsScalarTower A' K' L']

/-- For a tamely ramified extension `L / K` over `A` and an `e₀`-th root `α'` of a uniformizer `π`
of `A` in an extension `Ω'` of `L` (where `0 < e₀` is divisible by all ramification indices over
`A`), `integralClosure A K(α')` has fraction field `K(α')` and `integralClosure A[α'] L(α')` is
finite étale over `A[α'] := integralClosure A K(α')`. -/
private theorem etale_and_finite_over_adjoin_root_of_tame
    {Ω' : Type*} [Field Ω'] [Algebra K Ω'] [Algebra L Ω'] [Algebra A Ω']
    [IsScalarTower K L Ω'] [IsScalarTower A K Ω']
    (h : IsTamelyRamifiedWRT A L) {π : A} (hπ : Irreducible π) {e₀ : ℕ} (he₀_pos : 0 < e₀)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ e₀)
    {α' : Ω'} (hα' : α' ^ e₀ = algebraMap A Ω' π)
    [IsDiscreteValuationRing (integralClosure A K⟮α'⟯)] :
    letI := (TauCeti.IntermediateField.adjoinBaseChange K L α').toAlgebra
    IsFractionRing (integralClosure A K⟮α'⟯) K⟮α'⟯ ∧
      Algebra.IsAlgebraic K⟮α'⟯ L⟮α'⟯ ∧
      Algebra.Etale (integralClosure A K⟮α'⟯) (integralClosure (integralClosure A K⟮α'⟯) L⟮α'⟯) ∧
      Module.Finite (integralClosure A K⟮α'⟯)
        (integralClosure (integralClosure A K⟮α'⟯) L⟮α'⟯) := by
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α').toAlgebra
  obtain ⟨hunrL₁, _, _⟩ := adjoin_root_aux (K := K) h hπ hdvd hα'
  have hdegKα := TauCeti.IsDiscreteValuationRing.finrank_adjoin_of_pow_eq_of_irreducible
    (K := K) hπ hα'
  have : FiniteDimensional K K⟮α'⟯ := Module.finite_of_finrank_pos (hdegKα ▸ he₀_pos)
  have : IsFractionRing (integralClosure A K⟮α'⟯) K⟮α'⟯ :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K K⟮α'⟯ _
  obtain ⟨hetale, hfin⟩ := etale_and_finite_of_isUnramifiedWRT (F := K⟮α'⟯) hunrL₁
  exact ⟨‹_›, Algebra.IsAlgebraic.of_finite K⟮α'⟯ L⟮α'⟯, hetale, hfin⟩

/-- In an overfield `Ω'` of `K'` containing `e₀`-th roots `β'` of a uniformizer `ϖ'` of `A'` and
`γ'` of a unit `u'` of `A'` (with `e₀` invertible in `A'`), `K'(β')` is tamely ramified over `A'`
and `integralClosure A'₁ K'(β')(γ')` is finite étale over `A'₁ := integralClosure A' K'(β')`. -/
private theorem etale_and_finite_over_adjoin_uniformizer_root
    {Ω' : Type*} [Field Ω'] [Algebra K' Ω'] [Algebra A' Ω'] [IsScalarTower A' K' Ω']
    {ϖ' : A'} (hϖ' : Irreducible ϖ') {u' : A'ˣ} {e₀ : ℕ}
    (he₀_pos : 0 < e₀) (he₀_A' : IsUnit (e₀ : A'))
    (he₀_res' : IsUnit (e₀ : A' ⧸ maximalIdeal A'))
    {β' γ' : Ω'} (hβ' : β' ^ e₀ = algebraMap A' Ω' ϖ') (hγ' : γ' ^ e₀ = algebraMap A' Ω' u')
    [IsDiscreteValuationRing (integralClosure A' K'⟮β'⟯)] :
    IsTamelyRamifiedWRT A' K'⟮β'⟯ ∧
      IsFractionRing (integralClosure A' K'⟮β'⟯) K'⟮β'⟯ ∧
      Algebra.Etale (integralClosure A' K'⟮β'⟯)
        (integralClosure (integralClosure A' K'⟮β'⟯) (K'⟮β'⟯)⟮γ'⟯) ∧
      Module.Finite (integralClosure A' K'⟮β'⟯)
        (integralClosure (integralClosure A' K'⟮β'⟯) (K'⟮β'⟯)⟮γ'⟯) := by
  let K'₁ : IntermediateField K' Ω' := K'⟮β'⟯
  have : IsScalarTower A' K'₁ Ω' := .to₁₃₄ A' K' K'₁ Ω'
  let A'₁ := integralClosure A' K'₁
  have hK'₁_tame : IsTamelyRamifiedWRT A' K'₁ :=
    TauCeti.IsDiscreteValuationRing.isTamelyRamifiedWRT_adjoin_of_pow_eq_of_irreducible
      hϖ' he₀_res' hβ'
  have hdegK'₁ := TauCeti.IsDiscreteValuationRing.finrank_adjoin_of_pow_eq_of_irreducible
    (K := K') hϖ' hβ'
  have : FiniteDimensional K' K'₁ := Module.finite_of_finrank_pos (hdegK'₁ ▸ he₀_pos)
  have : IsFractionRing A'₁ K'₁ := IsIntegralClosure.isFractionRing_of_finite_extension A' K' K'₁ _
  let K'₂ : IntermediateField K'₁ Ω' := K'₁⟮γ'⟯
  have : IsScalarTower A'₁ K'₁ K'₂ := ⟨fun y k z ↦ smul_assoc (y : K'₁) k z⟩
  have : IsScalarTower A' A'₁ K'₂ := ⟨fun a y z ↦ smul_assoc a (y : K'₁) z⟩
  have hγ'K'₂ : AdjoinSimple.gen K'₁ γ' ^ e₀ = algebraMap A'₁ K'₂ (algebraMap A' A'₁ u') :=
    Subtype.ext (by
      rw [← IsScalarTower.algebraMap_apply A' A'₁ K'₂, IsScalarTower.algebraMap_apply A' K'₁ K'₂,
        IntermediateField.coe_algebraMap_apply, ← IsScalarTower.algebraMap_apply A' K'₁ Ω']
      exact hγ')
  have he₀_A'₁ : IsUnit (e₀ : A'₁) := by simpa using he₀_A'.map (algebraMap A' A'₁)
  obtain ⟨hetale, hfin⟩ :=
    TauCeti.IsDiscreteValuationRing.etale_and_finite_integralClosure_of_pow_eq_of_isUnit
      (K := K'₁) (L := K'₂) (u'.isUnit.map (algebraMap A' A'₁)) he₀_A'₁ hγ'K'₂
      (_root_.IntermediateField.adjoin_adjoinSimple_gen_eq_top γ')
  exact ⟨hK'₁_tame, ‹_›, hetale, hfin⟩

omit [IsDomain A'] [IsDiscreteValuationRing A'] [IsFractionRing A' K'] [Algebra A K']
  [IsScalarTower A A' K'] [IsScalarTower A K K'] [IsScalarTower A' K' L'] in
/-- Under the hypotheses of `isTamelyRamifiedWRT_of_roots_in_overfield`, the double root extension
`L'(β', γ')` inside `Ω'` is unramified with respect to `integralClosure A' K'(β')`. -/
private theorem isUnramifiedWRT_adjoin_roots_in_overfield
    [Algebra L L'] [Algebra K L']
    [IsScalarTower K K' L'] [IsScalarTower K L L']
    {Ω' : Type v} [Field Ω'] [Algebra L' Ω'] [Algebra K' Ω'] [Algebra A' Ω']
    [Algebra L Ω'] [Algebra K Ω'] [Algebra A Ω']
    [IsScalarTower K' L' Ω'] [IsScalarTower A' K' Ω'] [IsScalarTower A' L' Ω']
    [IsScalarTower L L' Ω'] [IsScalarTower K L Ω'] [IsScalarTower A K Ω']
    [IsScalarTower K K' Ω'] [IsScalarTower A A' Ω']
    (h : IsTamelyRamifiedWRT A L) (φ : K' ⊗[K] L →ₐ[K'] L') (hφ : Function.Surjective φ)
    (hφL : ∀ l : L, φ (1 ⊗ₜ[K] l) = algebraMap L L' l)
    {π : A} (hπ : Irreducible π) {ϖ' : A'} {u' : A'ˣ} {m e₀ : ℕ} (he₀_pos : 0 < e₀)
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ e₀)
    {β' γ' : Ω'} (hβ' : β' ^ e₀ = algebraMap A' Ω' ϖ') (hγ' : γ' ^ e₀ = algebraMap A' Ω' u')
    (hα' : (γ' * β' ^ m) ^ e₀ = algebraMap A Ω' π)
    [IsDiscreteValuationRing (integralClosure A' K'⟮β'⟯)]
    [IsFractionRing (integralClosure A' K'⟮β'⟯) K'⟮β'⟯]
    [Algebra.Etale (integralClosure A' K'⟮β'⟯)
      (integralClosure (integralClosure A' K'⟮β'⟯) (K'⟮β'⟯)⟮γ'⟯)]
    [Module.Finite (integralClosure A' K'⟮β'⟯)
      (integralClosure (integralClosure A' K'⟮β'⟯) (K'⟮β'⟯)⟮γ'⟯)]
    [Algebra K'⟮β'⟯ (IntermediateField.adjoin L' ({β', γ'} : Set Ω'))]
    [IsScalarTower (integralClosure A' K'⟮β'⟯) K'⟮β'⟯
      (IntermediateField.adjoin L' ({β', γ'} : Set Ω'))]
    (hιK'₁ : ∀ x : K'⟮β'⟯,
      (algebraMap K'⟮β'⟯ (IntermediateField.adjoin L' ({β', γ'} : Set Ω')) x : Ω') = x) :
    IsUnramifiedWRT (integralClosure A' K'⟮β'⟯)
      (IntermediateField.adjoin L' ({β', γ'} : Set Ω')) := by
  let α' : Ω' := γ' * β' ^ m
  have :=
    TauCeti.IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_adjoin (K := K) hπ hα'
  let := (TauCeti.IntermediateField.adjoinBaseChange K L α').toAlgebra
  let A₁ := integralClosure A K⟮α'⟯
  let B₁ := integralClosure A₁ L⟮α'⟯
  let A'₁ := integralClosure A' K'⟮β'⟯
  let A'₂ := integralClosure A'₁ (K'⟮β'⟯)⟮γ'⟯
  obtain ⟨_, _, _, _⟩ := etale_and_finite_over_adjoin_root_of_tame (K := K) h hπ he₀_pos hdvd hα'
  have : IsScalarTower A' K'⟮β'⟯ Ω' := .to₁₃₄ A' K' K'⟮β'⟯ Ω'
  have : IsScalarTower A' A'₁ (K'⟮β'⟯)⟮γ'⟯ := ⟨fun a y z ↦ smul_assoc a (y : K'⟮β'⟯) z⟩
  let E'' : IntermediateField L' Ω' := IntermediateField.adjoin L' ({β', γ'} : Set Ω')
  have hβ'_mem : β' ∈ E'' := IntermediateField.subset_adjoin L' _ (Set.mem_insert β' {γ'})
  have hγ'_mem : γ' ∈ E'' := IntermediateField.subset_adjoin L' _ (Set.mem_insert_of_mem β' rfl)
  let ιK'₂ : (K'⟮β'⟯)⟮γ'⟯ →+* E'' := adjoinSimpleInclusionRingHom
    (fun x ↦ by change (x : Ω') ∈ E''; rw [← hιK'₁ x]; exact (algebraMap K'⟮β'⟯ E'' x).2) hγ'_mem
  let ιK : K⟮α'⟯ →+* (K'⟮β'⟯)⟮γ'⟯ := adjoinSimpleInclusionRingHom
    (fun k ↦ by
      rw [IsScalarTower.algebraMap_apply K K' Ω']
      exact ((K'⟮β'⟯)⟮γ'⟯).algebraMap_mem (algebraMap K' K'⟮β'⟯ (algebraMap K K' k)))
    (mul_mem (mem_adjoin_simple_self K'⟮β'⟯ γ')
      (pow_mem (((K'⟮β'⟯)⟮γ'⟯).algebraMap_mem (AdjoinSimple.gen K' β')) m))
  let fA₁ : A₁ →+* A'₂ := mapIntegralClosure ((algebraMap A' A'₁).comp (algebraMap A A')) ιK
    (fun r ↦ Subtype.ext (by
      rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply A' A'₁ (K'⟮β'⟯)⟮γ'⟯,
        IsScalarTower.algebraMap_apply A' K'⟮β'⟯ (K'⟮β'⟯)⟮γ'⟯,
        IntermediateField.coe_algebraMap_apply, ← IsScalarTower.algebraMap_apply A' K'⟮β'⟯ Ω',
        ← IsScalarTower.algebraMap_apply A A' Ω']
      change (algebraMap A K⟮α'⟯ r : Ω') = algebraMap A Ω' r
      rw [IsScalarTower.algebraMap_apply A K K⟮α'⟯, IntermediateField.coe_algebraMap_apply,
        ← IsScalarTower.algebraMap_apply A K Ω']))
  let ιL₁ : L⟮α'⟯ →+* E'' := adjoinSimpleInclusionRingHom
    (fun l ↦ by rw [IsScalarTower.algebraMap_apply L L' Ω']; exact E''.algebraMap_mem _)
    (mul_mem hγ'_mem (pow_mem hβ'_mem m))
  have hγ'_intA' : IsIntegral A' γ' := IsIntegral.of_pow he₀_pos (hγ' ▸ isIntegral_algebraMap)
  exact isUnramifiedWRT_of_compositum_closures A₁ B₁ A'₁ K'⟮β'⟯ A'₂ E'' fA₁
    (ιK'₂.comp (algebraMap A'₂ (K'⟮β'⟯)⟮γ'⟯)) (ιL₁.comp (algebraMap B₁ L⟮α'⟯))
    (fun a ↦ Subtype.ext (TauCeti.IntermediateField.coe_adjoinBaseChange K L α' a.1))
    (fun y ↦ Subtype.ext (hιK'₁ y.1).symm)
    ⟨AdjoinSimple.gen K'⟮β'⟯ γ', isIntegral_adjoinSimple_gen_of_pow_eq he₀_pos hγ'⟩
    (fun χ h1 h2 h3 ↦ surjective_compositum_lift (K := K) (L := L) (K' := K') (L' := L')
      (Ω' := Ω') (K₁ := K⟮α'⟯) (L₁ := L⟮α'⟯) (A₁ := A₁) φ hφ hφL
      ((IsIntegral.of_pow he₀_pos (hβ' ▸ isIntegral_algebraMap (R := A'))).tower_top)
      hγ'_intA'.tower_top hγ'_intA'.tower_top ιK ιL₁ (fun _ ↦ rfl)
      (fun c x ↦ by
        rw [Algebra.smul_def]
        exact congrArg (· * (x : Ω')) (TauCeti.IntermediateField.coe_adjoinBaseChange K L α' c))
      (algebraMap K'⟮β'⟯ E'') hιK'₁ ιK'₂ (fun _ ↦ rfl) χ h1 h2 h3)

omit [Algebra A K'] [IsScalarTower A A' K'] [IsScalarTower A K K'] in
/-- Given an ambient overfield `Ω'` of `L'` containing `e₀`-th roots `β'` of a uniformizer `ϖ'` of
`A'` and `γ'` of a unit `u'` of `A'` with `(γ' * β' ^ m) ^ e₀ = π`, the compositum `L'(β', γ')` is
unramified over `integralClosure A' K'(β')`, so `L'` is tamely ramified with respect to `A'`. -/
private theorem isTamelyRamifiedWRT_of_roots_in_overfield
    [FiniteDimensional K' L'] [Algebra.IsSeparable K' L']
    [Algebra L L'] [Algebra K L'] [Algebra A L']
    [IsScalarTower K K' L'] [IsScalarTower A A' L'] [IsScalarTower K L L']
    [IsScalarTower A K L'] [IsScalarTower A L L']
    {Ω' : Type*} [Field Ω'] [Algebra L' Ω'] [Algebra K' Ω'] [Algebra A' Ω']
    [Algebra L Ω'] [Algebra K Ω'] [Algebra A Ω']
    [IsScalarTower K' L' Ω'] [IsScalarTower A' K' Ω'] [IsScalarTower A' L' Ω']
    [IsScalarTower L L' Ω'] [IsScalarTower K L Ω'] [IsScalarTower A K Ω']
    [IsScalarTower A L Ω'] [IsScalarTower K K' Ω'] [IsScalarTower A A' Ω']
    (h : IsTamelyRamifiedWRT A L) (φ : K' ⊗[K] L →ₐ[K'] L') (hφ : Function.Surjective φ)
    (hφL : ∀ l : L, φ (1 ⊗ₜ[K] l) = algebraMap L L' l)
    {π : A} (hπ : Irreducible π) {ϖ' : A'} (hϖ' : Irreducible ϖ') {u' : A'ˣ} {m e₀ : ℕ}
    (he₀_pos : 0 < e₀) (he₀_A' : IsUnit (e₀ : A'))
    (he₀_res' : IsUnit (e₀ : A' ⧸ maximalIdeal A'))
    (hdvd : ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A ∣ e₀)
    {β' γ' : Ω'} (hβ' : β' ^ e₀ = algebraMap A' Ω' ϖ') (hγ' : γ' ^ e₀ = algebraMap A' Ω' u')
    (hα' : (γ' * β' ^ m) ^ e₀ = algebraMap A Ω' π) :
    IsTamelyRamifiedWRT A' L' := by
  have :=
    TauCeti.IsDiscreteValuationRing.isDiscreteValuationRing_integralClosure_adjoin (K := K') hϖ' hβ'
  obtain ⟨hK'₁_tame, _, _, _⟩ :=
    etale_and_finite_over_adjoin_uniformizer_root (K' := K') hϖ' he₀_pos he₀_A' he₀_res' hβ' hγ'
  let E'' : IntermediateField L' Ω' := IntermediateField.adjoin L' ({β', γ'} : Set Ω')
  have hβ'_mem : β' ∈ E'' :=
    IntermediateField.subset_adjoin L' ({β', γ'} : Set Ω') (Set.mem_insert β' {γ'})
  let ιK'₁ : K'⟮β'⟯ →+* E'' :=
    adjoinSimpleInclusionRingHom
      (fun k' ↦ by rw [IsScalarTower.algebraMap_apply K' L' Ω']; exact E''.algebraMap_mem _)
      hβ'_mem
  let : Algebra K'⟮β'⟯ E'' := ιK'₁.toAlgebra
  have : IsScalarTower A' K'⟮β'⟯ E'' := .of_algebraMap_eq fun a ↦ Subtype.ext (by
    rw [IsScalarTower.algebraMap_apply A' L' E'', IntermediateField.coe_algebraMap_apply,
      ← IsScalarTower.algebraMap_apply A' L' Ω']
    change algebraMap A' Ω' a = (algebraMap A' K'⟮β'⟯ a : Ω')
    rw [IsScalarTower.algebraMap_apply A' K' K'⟮β'⟯, IntermediateField.coe_algebraMap_apply,
      ← IsScalarTower.algebraMap_apply A' K' Ω'])
  have hunr : IsUnramifiedWRT (integralClosure A' K'⟮β'⟯) E'' :=
    isUnramifiedWRT_adjoin_roots_in_overfield h φ hφ hφL hπ he₀_pos hdvd hβ' hγ' hα' (fun _ ↦ rfl)
  exact (hK'₁_tame.trans hunr.isTamelyRamifiedWRT).tower_bot K'

/-- Tamely ramified extensions of a discrete valuation ring are stable under base change: if `L` is
tamely ramified with respect to `A`, then every factor `L'` of `K' ⊗[K] L`, given by a surjective
`K'`-algebra map `φ : K' ⊗[K] L → L'`, is tamely ramified with respect to `A'`. -/
@[stacks 0EXY "tame case"]
theorem IsTamelyRamifiedWRT.baseChange (h : IsTamelyRamifiedWRT A L) (φ : K' ⊗[K] L →ₐ[K'] L')
    (hφ : Function.Surjective φ) : IsTamelyRamifiedWRT A' L' := by
  have : FiniteDimensional K' L' := Module.Finite.of_surjective φ.toLinearMap hφ
  have : Algebra.FormallyUnramified K L := .of_isSeparable K L
  have : Algebra.FormallyUnramified K' L' := .of_surjective φ hφ
  have : Algebra.IsSeparable K' L' := (Algebra.FormallyUnramified.iff_isSeparable K' L').mp ‹_›
  obtain ⟨π, hπ⟩ := _root_.IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨ϖ', hϖ'⟩ := _root_.IsDiscreteValuationRing.exists_irreducible A'
  have hπA' : algebraMap A A' π ≠ 0 := fun h0 ↦ by
    have hK' : algebraMap A K' π = 0 := by
      rw [IsScalarTower.algebraMap_apply A A' K', h0, map_zero]
    rw [IsScalarTower.algebraMap_apply A K K', map_eq_zero,
      IsFractionRing.to_map_eq_zero_iff] at hK'
    exact hπ.ne_zero hK'
  obtain ⟨m, u', hπ_eq⟩ := _root_.IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπA' hϖ'
  obtain ⟨e₀, he₀_pos, he₀_res, hdvd⟩ := h.exists_ramificationIdx_dvd (K := K)
  have he₀_A : IsUnit (e₀ : A) :=
    (isUnit_map_iff (residue A) _).mp (by rw [map_natCast]; exact he₀_res)
  have he₀_A' : IsUnit (e₀ : A') := by simpa using he₀_A.map (algebraMap A A')
  have he₀_res' : IsUnit (e₀ : A' ⧸ maximalIdeal A') := by
    simpa using he₀_A'.map (Ideal.Quotient.mk (maximalIdeal A'))
  -- Embed `L` into `L'` via `φ` and extract `e₀`-th roots in `AlgebraicClosure L'`.
  let jL : L →+* L' :=
    φ.toRingHom.comp (Algebra.TensorProduct.includeRight : L →ₐ[K] K' ⊗[K] L).toRingHom
  let : Algebra L L' := jL.toAlgebra
  let : Algebra K L' := ((algebraMap K' L').comp (algebraMap K K')).toAlgebra
  let : Algebra A L' := ((algebraMap A' L').comp (algebraMap A A')).toAlgebra
  have : IsScalarTower K K' L' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A A' L' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K L L' := .of_algebraMap_eq fun x ↦ by
    have hx : (1 : K') ⊗ₜ[K] algebraMap K L x =
        algebraMap K' (K' ⊗[K] L) (algebraMap K K' x) := by
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one, ← Algebra.TensorProduct.algebraMap_apply,
        IsScalarTower.algebraMap_apply K K' (K' ⊗[K] L)]
    exact (φ.commutes (algebraMap K K' x)).symm.trans (congrArg φ hx.symm)
  have : IsScalarTower A K L' := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply A K K',
      IsScalarTower.algebraMap_apply A A' K', ← IsScalarTower.algebraMap_apply A' K' L']
  have : IsScalarTower A L L' := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply K L L',
      ← IsScalarTower.algebraMap_apply A K L']
  let Ω' := AlgebraicClosure L'
  obtain ⟨β', hβ'⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A' Ω' ϖ') he₀_pos
  obtain ⟨γ', hγ'⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A' Ω' u') he₀_pos
  have hα' : (γ' * β' ^ m) ^ e₀ = algebraMap A Ω' π := by
    rw [mul_pow, ← pow_mul, mul_comm m e₀, pow_mul, hγ', hβ', ← map_pow, ← map_mul, ← hπ_eq,
      ← IsScalarTower.algebraMap_apply A A' Ω']
  exact isTamelyRamifiedWRT_of_roots_in_overfield h φ hφ (fun _ ↦ rfl) hπ hϖ' he₀_pos he₀_A'
    he₀_res' hdvd hβ' hγ' hα'

end BaseChange

end TauCeti.Algebra

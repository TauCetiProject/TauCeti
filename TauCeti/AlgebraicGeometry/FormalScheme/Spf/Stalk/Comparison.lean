/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.CompletedAtPrime.Stalk

import TauCeti.RingTheory.AdicCompletion.LocalRing
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.LocalRing.Localization

/-!
# Completion comparisons and special cases for stalks of `Spf A`

Building on `TauCeti.AlgebraicGeometry.FormalScheme.Spf.CompletedAtPrime.Stalk`, this module
establishes comparison properties of the canonical homomorphisms `A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭`:

* both maps induce a commutative triangle of ring isomorphisms between the maximal-ideal-adic
  completions of `A_𝔭`, `𝒪_{Spf A, p}`, and `Â_𝔭`;
* when `A` is discrete, or when `A` is a complete local adic ring and `p` is its closed point, both
  comparison homomorphisms are bijective (EGA I, Ch. 0, 7.6.15–7.6.18; Ch. I, 10.1.5–10.1.6).

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.6.15–7.6.18,
  and Ch. I, 10.1.5–10.1.6.
-/

public section

universe u

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry IsLocalRing

namespace TauCeti.FormalScheme.Spf

open AdicRing

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  (p : carrier A)

/-! ### Maximal-ideal-adic completions -/

section MaximalIdealCompletion

private theorem ideal_map_toStalk_le_maximalIdeal :
    (IsAdicRing.ideal A).map (toStalk p) ≤ maximalIdeal ((Spf A).presheaf.stalk p) := by
  rw [← map_maximalIdeal_localizationToStalk p, ← map_localizationToStalk_map p]
  exact Ideal.map_mono (ideal_map_le_maximalIdeal_localization p (IsAdicRing.ideal_spec A).2.1)

private theorem quotientMapPowBijective_map_ideal {R S : Type*} [CommRing R] [CommRing S]
    {φ : A →+* R} {g : R →+* S} {ψ : A →+* S} (hcomp : g.comp φ = ψ)
    (h : ∀ {J : Ideal A}, IsOpen (J : Set A) →
      ∀ {H : J.map φ ≤ (J.map ψ).comap g}, Function.Bijective (Ideal.quotientMap (J.map ψ) g H)) :
    g.QuotientMapPowBijective ((IsAdicRing.ideal A).map φ) := fun n _ ↦
  g.quotientMap_bijective_congr rfl (Ideal.map_pow _ _ _)
    (by rw [Ideal.map_map, hcomp, Ideal.map_pow])
    (h ((isAdic_iff.mp (IsAdicRing.ideal_spec A).2.1).1 n)
      (H := (by rw [Ideal.map_map, hcomp] : ((IsAdicRing.ideal A ^ n).map φ).map g = _) ▸
        Ideal.le_comap_map))

/-- The canonical isomorphism between the maximal-ideal-adic completions of `A_𝔭` and
`𝒪_{Spf A, p}`. -/
noncomputable def maximalIdealCompletionLocalizationEquivStalk :
    AdicCompletion (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) ≃+*
      AdicCompletion (maximalIdeal ((Spf A).presheaf.stalk p)) ((Spf A).presheaf.stalk p) :=
  (localizationToStalk p).adicCompletionMaximalIdealRingEquivOfQuotientMap
    (ideal_map_le_maximalIdeal_localization p (IsAdicRing.ideal_spec A).2.1)
    (quotientMapPowBijective_map_ideal (localizationToStalk_comp_algebraMap p)
      fun hJ ↦ quotientMap_localizationToStalk_bijective_of_isOpen p hJ)

/-- On elements of `A_𝔭`, `maximalIdealCompletionLocalizationEquivStalk` applies
`localizationToStalk p`. -/
@[simp]
theorem maximalIdealCompletionLocalizationEquivStalk_of
    (x : Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :
    maximalIdealCompletionLocalizationEquivStalk p (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (localizationToStalk p x) :=
  (localizationToStalk p).adicCompletionMaximalIdealRingEquivOfQuotientMap_of _ _ x

/-- Modulo `𝔪 ^ n`, `maximalIdealCompletionLocalizationEquivStalk` is the quotient map induced by
`localizationToStalk p`. -/
@[simp]
theorem evalₐ_maximalIdealCompletionLocalizationEquivStalk (n : ℕ)
    (x : AdicCompletion (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))
      (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) :
    AdicCompletion.evalₐ (maximalIdeal ((Spf A).presheaf.stalk p)) n
        (maximalIdealCompletionLocalizationEquivStalk p x) =
      Ideal.quotientMap (maximalIdeal ((Spf A).presheaf.stalk p) ^ n) (localizationToStalk p)
        (Ideal.pow_le_comap_pow_of_le_comap (localizationToStalk p)
          (map_maximalIdeal_localizationToStalk p ▸ Ideal.le_comap_map) n)
        (AdicCompletion.evalₐ
          (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) n x) :=
  (localizationToStalk p).evalₐ_adicCompletionMaximalIdealRingEquivOfQuotientMap _ _ n x

/-- The canonical isomorphism between the maximal-ideal-adic completions of `𝒪_{Spf A, p}` and
`Â_𝔭`. -/
noncomputable def maximalIdealCompletionStalkEquivCompletedAtPrime :
    AdicCompletion (maximalIdeal ((Spf A).presheaf.stalk p)) ((Spf A).presheaf.stalk p) ≃+*
      AdicCompletion (maximalIdeal (CompletedAtPrime p)) (CompletedAtPrime p) :=
  (stalkToCompletedAtPrime p).adicCompletionMaximalIdealRingEquivOfQuotientMap
    (ideal_map_toStalk_le_maximalIdeal p)
    (quotientMapPowBijective_map_ideal (stalkToCompletedAtPrime_comp_toStalk p)
      fun hJ ↦ quotientMap_stalkToCompletedAtPrime_bijective_of_isOpen p hJ)

/-- On elements of `𝒪_{Spf A, p}`, `maximalIdealCompletionStalkEquivCompletedAtPrime` applies
`stalkToCompletedAtPrime p`. -/
@[simp]
theorem maximalIdealCompletionStalkEquivCompletedAtPrime_of
    (x : (Spf A).presheaf.stalk p) :
    maximalIdealCompletionStalkEquivCompletedAtPrime p (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (stalkToCompletedAtPrime p x) :=
  (stalkToCompletedAtPrime p).adicCompletionMaximalIdealRingEquivOfQuotientMap_of _ _ x

/-- Modulo `𝔪 ^ n`, `maximalIdealCompletionStalkEquivCompletedAtPrime` is the quotient map induced
by `stalkToCompletedAtPrime p`. -/
@[simp]
theorem evalₐ_maximalIdealCompletionStalkEquivCompletedAtPrime (n : ℕ)
    (x : AdicCompletion (maximalIdeal ((Spf A).presheaf.stalk p)) ((Spf A).presheaf.stalk p)) :
    AdicCompletion.evalₐ (maximalIdeal (CompletedAtPrime p)) n
        (maximalIdealCompletionStalkEquivCompletedAtPrime p x) =
      Ideal.quotientMap (maximalIdeal (CompletedAtPrime p) ^ n) (stalkToCompletedAtPrime p)
        (Ideal.pow_le_comap_pow_of_le_comap (stalkToCompletedAtPrime p)
          (map_maximalIdeal_stalkToCompletedAtPrime p ▸ Ideal.le_comap_map) n)
        (AdicCompletion.evalₐ (maximalIdeal ((Spf A).presheaf.stalk p)) n x) :=
  (stalkToCompletedAtPrime p).evalₐ_adicCompletionMaximalIdealRingEquivOfQuotientMap _ _ n x

/-- The canonical isomorphism between the maximal-ideal-adic completions of `A_𝔭` and `Â_𝔭`. -/
noncomputable def maximalIdealCompletionLocalizationEquivCompletedAtPrime :
    AdicCompletion (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) ≃+*
      AdicCompletion (maximalIdeal (CompletedAtPrime p)) (CompletedAtPrime p) :=
  (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
      (CompletedAtPrime p)).adicCompletionMaximalIdealRingEquivOfQuotientMap
    (ideal_map_le_maximalIdeal_localization p (IsAdicRing.ideal_spec A).2.1)
    fun n _ ↦ AdicCompletion.quotientMap_algebraMap_bijective ((IsAdicRing.ideal_spec A).1.map _) n

/-- On elements of `A_𝔭`, `maximalIdealCompletionLocalizationEquivCompletedAtPrime` applies
`algebraMap A_𝔭 Â_𝔭`. -/
@[simp]
theorem maximalIdealCompletionLocalizationEquivCompletedAtPrime_of
    (x : Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :
    maximalIdealCompletionLocalizationEquivCompletedAtPrime p (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _
        (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (CompletedAtPrime p) x) :=
  (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
      (CompletedAtPrime p)).adicCompletionMaximalIdealRingEquivOfQuotientMap_of _ _ x

/-- Modulo `𝔪 ^ n`, `maximalIdealCompletionLocalizationEquivCompletedAtPrime` is the quotient map
induced by `algebraMap A_𝔭 Â_𝔭`. -/
@[simp]
theorem evalₐ_maximalIdealCompletionLocalizationEquivCompletedAtPrime (n : ℕ)
    (x : AdicCompletion (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))
      (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) :
    AdicCompletion.evalₐ (maximalIdeal (CompletedAtPrime p)) n
        (maximalIdealCompletionLocalizationEquivCompletedAtPrime p x) =
      Ideal.quotientMap (maximalIdeal (CompletedAtPrime p) ^ n)
        (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (CompletedAtPrime p))
        (Ideal.pow_le_comap_pow_of_le_comap _
          (Ideal.map_le_iff_le_comap.mp (map_maximalIdeal_le _)) n)
        (AdicCompletion.evalₐ
          (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) n x) :=
  (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
      (CompletedAtPrime p)).evalₐ_adicCompletionMaximalIdealRingEquivOfQuotientMap _ _ n x

/-- The three maximal-ideal-adic completion isomorphisms form a commutative triangle. -/
@[simp]
theorem maximalIdealCompletionLocalizationEquivStalk_trans :
    (maximalIdealCompletionLocalizationEquivStalk p).trans
        (maximalIdealCompletionStalkEquivCompletedAtPrime p) =
      maximalIdealCompletionLocalizationEquivCompletedAtPrime p :=
  RingHom.adicCompletionMaximalIdealRingEquivOfQuotientMap_trans
    (localizationToStalk p) _ _ (stalkToCompletedAtPrime p) _ _
    (stalkToCompletedAtPrime_comp_localizationToStalk p) _ _

/-- Pointwise form of `maximalIdealCompletionLocalizationEquivStalk_trans`. -/
@[simp]
theorem maximalIdealCompletionStalkEquivCompletedAtPrime_localizationEquivStalk
    (x : AdicCompletion (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))
      (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) :
    maximalIdealCompletionStalkEquivCompletedAtPrime p
        (maximalIdealCompletionLocalizationEquivStalk p x) =
      maximalIdealCompletionLocalizationEquivCompletedAtPrime p x :=
  DFunLike.congr_fun (maximalIdealCompletionLocalizationEquivStalk_trans p) x

end MaximalIdealCompletion

/-! ### Discrete rings and complete local adic rings -/

section SpecialCases

/-- For a discrete ring `A`, `A_𝔭 → 𝒪_{Spf A, p}` is bijective. -/
theorem localizationToStalk_bijective_of_discreteTopology [DiscreteTopology A] :
    Function.Bijective (localizationToStalk p) :=
  (localizationToStalk p).bijective_of_quotientMap_bot_bijective Ideal.map_bot Ideal.map_bot
    (quotientMap_localizationToStalk_bijective_of_isOpen p (J := ⊥) (isOpen_discrete _)
      (H := map_localizationToStalk_map p ⊥ ▸ Ideal.le_comap_map))

/-- For a discrete ring `A`, `𝒪_{Spf A, p} → Â_𝔭` is bijective. -/
theorem stalkToCompletedAtPrime_bijective_of_discreteTopology [DiscreteTopology A] :
    Function.Bijective (stalkToCompletedAtPrime p) :=
  (stalkToCompletedAtPrime p).bijective_of_quotientMap_bot_bijective Ideal.map_bot
    Ideal.map_bot (quotientMap_stalkToCompletedAtPrime_bijective_of_isOpen p (J := ⊥)
      (isOpen_discrete _) (H := map_stalkToCompletedAtPrime_map p ⊥ ▸ Ideal.le_comap_map))

/-- For a discrete ring `A`, `A_𝔭 → Â_𝔭` is bijective. -/
theorem algebraMap_completedAtPrime_bijective_of_discreteTopology [DiscreteTopology A] :
    Function.Bijective
      (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (CompletedAtPrime p)) := by
  rw [← stalkToCompletedAtPrime_comp_localizationToStalk p]
  exact (stalkToCompletedAtPrime_bijective_of_discreteTopology p).comp
    (localizationToStalk_bijective_of_discreteTopology p)

/-- For a complete local adic ring `A` at its closed point `p` (with `𝔭 = 𝔪_A`), `A_𝔭 → Â_𝔭`
is bijective. -/
theorem algebraMap_completedAtPrime_bijective_of_isLocalRing [IsLocalRing A]
    (hp : (p : PrimeSpectrum A).asIdeal = maximalIdeal A) :
    Function.Bijective
      (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (CompletedAtPrime p)) :=
  let e : A ≃+* Localization.AtPrime (p : PrimeSpectrum A).asIdeal :=
    RingEquiv.ofBijective _ (IsLocalRing.bijective_algebraMap_atPrime_of_eq_maximalIdeal hp)
  have : IsAdicComplete
      ((IsAdicRing.ideal A).map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
      (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
    (IsAdicComplete.congr_ringEquiv (IsAdicRing.ideal A) e).mpr (IsAdicRing.ideal_spec A).2.2
  AdicCompletion.of_bijective _ _

/-- For a complete local adic ring `A` at its unique closed point `p` (with `𝔭 = 𝔪_A`), the
canonical map `A → 𝒪_{Spf A, p}` is bijective. -/
theorem toStalk_bijective_of_isLocalRing [IsLocalRing A]
    (hp : (p : PrimeSpectrum A).asIdeal = maximalIdeal A) :
    Function.Bijective (toStalk p) := by
  have hcomp_bij : Function.Bijective (stalkToCompletedAtPrime p ∘ toStalk p) := by
    convert (algebraMap_completedAtPrime_bijective_of_isLocalRing p hp).comp
      (IsLocalRing.bijective_algebraMap_atPrime_of_eq_maximalIdeal hp)
    exact funext fun _ ↦ by simp [← IsScalarTower.algebraMap_apply]
  refine ⟨Function.Injective.of_comp hcomp_bij.1, fun s ↦ ?_⟩
  obtain ⟨f, x, rfl⟩ := exists_completedAway_rep p s
  have hf_unit : IsUnit f.elem := by rw [← notMem_maximalIdeal, ← hp]; exact f.notMem
  obtain ⟨a, ha⟩ := (CompletedAway.algebraMap_bijective_of_isUnit hf_unit).2 x
  exact ⟨a, (toStalk_eq_completedNeighbourhoodColimitIso p f a).trans (by rw [ha])⟩

/-- For a complete local adic ring `A` at its closed point `p`, `A_𝔭 → 𝒪_{Spf A, p}` is
bijective. -/
theorem localizationToStalk_bijective_of_isLocalRing [IsLocalRing A]
    (hp : (p : PrimeSpectrum A).asIdeal = maximalIdeal A) :
    Function.Bijective (localizationToStalk p) := by
  refine (Function.Bijective.of_comp_iff (localizationToStalk p)
    (IsLocalRing.bijective_algebraMap_atPrime_of_eq_maximalIdeal hp)).mp ?_
  convert toStalk_bijective_of_isLocalRing p hp
  exact funext (localizationToStalk_algebraMap_eq_toStalk p)

/-- For a complete local adic ring `A` at its closed point `p`, `𝒪_{Spf A, p} → Â_𝔭` is
bijective. -/
theorem stalkToCompletedAtPrime_bijective_of_isLocalRing [IsLocalRing A]
    (hp : (p : PrimeSpectrum A).asIdeal = maximalIdeal A) :
    Function.Bijective (stalkToCompletedAtPrime p) := by
  refine (Function.Bijective.of_comp_iff (stalkToCompletedAtPrime p)
    (localizationToStalk_bijective_of_isLocalRing p hp)).mp ?_
  convert algebraMap_completedAtPrime_bijective_of_isLocalRing p hp
  exact funext (stalkToCompletedAtPrime_localizationToStalk p)

end SpecialCases

end TauCeti.FormalScheme.Spf

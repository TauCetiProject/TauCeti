/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk.CompletedAtPrime
public import TauCeti.RingTheory.CohenMacaulay.Basic

import TauCeti.RingTheory.AdicCompletion.LocalRing
import TauCeti.RingTheory.CohenMacaulay.Flat
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.LocalRing.Quotient

/-!
# Completion comparisons and noetherian invariants for stalks of `Spf A`

Building on `TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk.CompletedAtPrime`, this module
establishes the deeper comparison properties of the canonical homomorphisms
`A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭`:

* both maps induce a commutative triangle of ring isomorphisms between the maximal-ideal-adic
  completions of `A_𝔭`, `𝒪_{Spf A, p}`, and `Â_𝔭`;
* when `A` is discrete, or when `A` is a complete local adic ring and `p` is its closed point, both
  comparison homomorphisms are bijective;
* when `A` is noetherian, `ringKrullDim ((Spf A).presheaf.stalk p) = ht 𝔭`, and `A_𝔭`,
  `𝒪_{Spf A, p}`, and `Â_𝔭` are simultaneously Cohen–Macaulay (EGA I, Ch. 0, 7.6.15–7.6.18;
  Ch. I, 10.1.5–10.1.6).

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.6.15–7.6.18,
  and Ch. I, 10.1.5–10.1.6.
* H. Matsumura, *Commutative Ring Theory*, Theorems 23.3 and 23.7 (flat local-homomorphism transfer
  of Krull dimension, regularity, and the Cohen–Macaulay property).
* [Stacks Project, Lemma 15.44.2](https://stacks.math.columbia.edu/tag/07NX) (Cohen–Macaulay
  invariance under completion).
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

private theorem pow_quotientMap_localizationToStalk_bijective (n : ℕ) (_ : 1 ≤ n) :
    Function.Bijective (Ideal.quotientMap
      ((((IsAdicRing.ideal A).map
        (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))).map
          (localizationToStalk p)) ^ n)
      (localizationToStalk p)
      ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))) :=
  Ideal.quotientMap_bijective_congr (localizationToStalk p) (Ideal.map_pow _ _ _)
    (by rw [map_localizationToStalk_map, Ideal.map_pow])
    (quotientMap_localizationToStalk_bijective_of_isOpen p
      ((isAdic_iff.mp (IsAdicRing.ideal_spec A).2.1).1 n)
      (H := map_localizationToStalk_map p (IsAdicRing.ideal A ^ n) ▸ Ideal.le_comap_map))

private theorem pow_quotientMap_stalkToCompletedAtPrime_bijective (n : ℕ) (_ : 1 ≤ n) :
    Function.Bijective (Ideal.quotientMap
      ((((IsAdicRing.ideal A).map (toStalk p)).map (stalkToCompletedAtPrime p)) ^ n)
      (stalkToCompletedAtPrime p)
      ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))) :=
  Ideal.quotientMap_bijective_congr (stalkToCompletedAtPrime p) (Ideal.map_pow _ _ _)
    (by rw [map_stalkToCompletedAtPrime_map, Ideal.map_pow])
    (quotientMap_stalkToCompletedAtPrime_bijective_of_isOpen p
      ((isAdic_iff.mp (IsAdicRing.ideal_spec A).2.1).1 n)
      (H := map_stalkToCompletedAtPrime_map p (IsAdicRing.ideal A ^ n) ▸ Ideal.le_comap_map))

private theorem pow_quotientMap_algebraMap_completedAtPrime_bijective (n : ℕ) (_ : 1 ≤ n) :
    Function.Bijective (Ideal.quotientMap
      ((((IsAdicRing.ideal A).map
        (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))).map
          (algebraMap _ (CompletedAtPrime p))) ^ n)
      (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (CompletedAtPrime p))
      ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))) :=
  AdicCompletion.quotientMap_algebraMap_bijective ((IsAdicRing.ideal_spec A).1.map _) n

/-- The canonical isomorphism between the maximal-ideal-adic completions of `A_𝔭` and
`𝒪_{Spf A, p}`. -/
noncomputable def maximalIdealCompletionLocalizationEquivStalk :
    AdicCompletion (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) ≃+*
      AdicCompletion (maximalIdeal ((Spf A).presheaf.stalk p)) ((Spf A).presheaf.stalk p) :=
  TauCeti.AdicCompletion.maximalIdealRingEquivOfQuotientMap (localizationToStalk p)
    (ideal_map_le_maximalIdeal_localization p (IsAdicRing.ideal_spec A).2.1)
    (pow_quotientMap_localizationToStalk_bijective p)

/-- On elements of `A_𝔭`, `maximalIdealCompletionLocalizationEquivStalk` applies
`localizationToStalk p`. -/
@[simp]
theorem maximalIdealCompletionLocalizationEquivStalk_of
    (x : Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :
    maximalIdealCompletionLocalizationEquivStalk p (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (localizationToStalk p x) :=
  TauCeti.AdicCompletion.maximalIdealRingEquivOfQuotientMap_of _ _ _ x

/-- Modulo `𝔪 ^ n`, `maximalIdealCompletionLocalizationEquivStalk` is the quotient map induced by
`localizationToStalk p`. -/
@[simp]
theorem evalₐ_maximalIdealCompletionLocalizationEquivStalk (n : ℕ)
    (x : AdicCompletion (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))
      (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) :
    AdicCompletion.evalₐ (maximalIdeal ((Spf A).presheaf.stalk p)) n
        (maximalIdealCompletionLocalizationEquivStalk p x) =
      Ideal.quotientMap (maximalIdeal ((Spf A).presheaf.stalk p) ^ n) (localizationToStalk p)
        ((Ideal.pow_right_mono
          (map_maximalIdeal_localizationToStalk p ▸ Ideal.le_comap_map) n).trans
          (Ideal.le_comap_pow _ n))
        (AdicCompletion.evalₐ
          (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) n x) :=
  TauCeti.AdicCompletion.evalₐ_maximalIdealRingEquivOfQuotientMap _ _ _ n x

/-- The canonical isomorphism between the maximal-ideal-adic completions of `𝒪_{Spf A, p}` and
`Â_𝔭`. -/
noncomputable def maximalIdealCompletionStalkEquivCompletedAtPrime :
    AdicCompletion (maximalIdeal ((Spf A).presheaf.stalk p)) ((Spf A).presheaf.stalk p) ≃+*
      AdicCompletion (maximalIdeal (CompletedAtPrime p)) (CompletedAtPrime p) :=
  TauCeti.AdicCompletion.maximalIdealRingEquivOfQuotientMap (stalkToCompletedAtPrime p)
    (ideal_map_toStalk_le_maximalIdeal p)
    (pow_quotientMap_stalkToCompletedAtPrime_bijective p)

/-- On elements of `𝒪_{Spf A, p}`, `maximalIdealCompletionStalkEquivCompletedAtPrime` applies
`stalkToCompletedAtPrime p`. -/
@[simp]
theorem maximalIdealCompletionStalkEquivCompletedAtPrime_of
    (x : (Spf A).presheaf.stalk p) :
    maximalIdealCompletionStalkEquivCompletedAtPrime p (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (stalkToCompletedAtPrime p x) :=
  TauCeti.AdicCompletion.maximalIdealRingEquivOfQuotientMap_of _ _ _ x

/-- Modulo `𝔪 ^ n`, `maximalIdealCompletionStalkEquivCompletedAtPrime` is the quotient map induced
by `stalkToCompletedAtPrime p`. -/
@[simp]
theorem evalₐ_maximalIdealCompletionStalkEquivCompletedAtPrime (n : ℕ)
    (x : AdicCompletion (maximalIdeal ((Spf A).presheaf.stalk p)) ((Spf A).presheaf.stalk p)) :
    AdicCompletion.evalₐ (maximalIdeal (CompletedAtPrime p)) n
        (maximalIdealCompletionStalkEquivCompletedAtPrime p x) =
      Ideal.quotientMap (maximalIdeal (CompletedAtPrime p) ^ n) (stalkToCompletedAtPrime p)
        ((Ideal.pow_right_mono
          (map_maximalIdeal_stalkToCompletedAtPrime p ▸ Ideal.le_comap_map) n).trans
          (Ideal.le_comap_pow _ n))
        (AdicCompletion.evalₐ (maximalIdeal ((Spf A).presheaf.stalk p)) n x) :=
  TauCeti.AdicCompletion.evalₐ_maximalIdealRingEquivOfQuotientMap _ _ _ n x

/-- The canonical isomorphism between the maximal-ideal-adic completions of `A_𝔭` and `Â_𝔭`. -/
noncomputable def maximalIdealCompletionLocalizationEquivCompletedAtPrime :
    AdicCompletion (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) ≃+*
      AdicCompletion (maximalIdeal (CompletedAtPrime p)) (CompletedAtPrime p) :=
  TauCeti.AdicCompletion.maximalIdealRingEquivOfQuotientMap
    (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (CompletedAtPrime p))
    (ideal_map_le_maximalIdeal_localization p (IsAdicRing.ideal_spec A).2.1)
    (pow_quotientMap_algebraMap_completedAtPrime_bijective p)

/-- On elements of `A_𝔭`, `maximalIdealCompletionLocalizationEquivCompletedAtPrime` applies
`algebraMap A_𝔭 Â_𝔭`. -/
@[simp]
theorem maximalIdealCompletionLocalizationEquivCompletedAtPrime_of
    (x : Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :
    maximalIdealCompletionLocalizationEquivCompletedAtPrime p (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _
        (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (CompletedAtPrime p) x) :=
  TauCeti.AdicCompletion.maximalIdealRingEquivOfQuotientMap_of _ _ _ x

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
        ((Ideal.pow_right_mono
          (Ideal.map_le_iff_le_comap.mp (map_maximalIdeal_le _)) n).trans
          (Ideal.le_comap_pow _ n))
        (AdicCompletion.evalₐ
          (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) n x) :=
  TauCeti.AdicCompletion.evalₐ_maximalIdealRingEquivOfQuotientMap _ _ _ n x

/-- The three maximal-ideal-adic completion isomorphisms form a commutative triangle. -/
@[simp]
theorem maximalIdealCompletionLocalizationEquivStalk_trans :
    (maximalIdealCompletionLocalizationEquivStalk p).trans
        (maximalIdealCompletionStalkEquivCompletedAtPrime p) =
      maximalIdealCompletionLocalizationEquivCompletedAtPrime p :=
  TauCeti.AdicCompletion.maximalIdealRingEquivOfQuotientMap_trans
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
  Ideal.bijective_of_quotientMap_bot_bijective (localizationToStalk p) Ideal.map_bot Ideal.map_bot
    (quotientMap_localizationToStalk_bijective_of_isOpen p (J := ⊥) (isOpen_discrete _)
      (H := map_localizationToStalk_map p ⊥ ▸ Ideal.le_comap_map))

/-- For a discrete ring `A`, `𝒪_{Spf A, p} → Â_𝔭` is bijective. -/
theorem stalkToCompletedAtPrime_bijective_of_discreteTopology [DiscreteTopology A] :
    Function.Bijective (stalkToCompletedAtPrime p) :=
  Ideal.bijective_of_quotientMap_bot_bijective (stalkToCompletedAtPrime p) Ideal.map_bot
    Ideal.map_bot (quotientMap_stalkToCompletedAtPrime_bijective_of_isOpen p (J := ⊥)
      (isOpen_discrete _) (H := map_stalkToCompletedAtPrime_map p ⊥ ▸ Ideal.le_comap_map))

private noncomputable def atPrimeAlgEquivOfIsLocalRing [IsLocalRing A]
    (hp : (p : PrimeSpectrum A).asIdeal = maximalIdeal A) :
    A ≃ₐ[A] Localization.AtPrime (p : PrimeSpectrum A).asIdeal :=
  IsLocalization.atUnits A (p : PrimeSpectrum A).asIdeal.primeCompl fun _ hx ↦ by
    rw [IsUnit.mem_submonoid_iff, ← notMem_maximalIdeal, ← hp]; exact hx

private lemma algebraMap_completedAtPrime_bijective_of_isLocalRing [IsLocalRing A]
    (hp : (p : PrimeSpectrum A).asIdeal = maximalIdeal A) :
    Function.Bijective
      (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (CompletedAtPrime p)) :=
  have he : ((atPrimeAlgEquivOfIsLocalRing p hp).toRingEquiv :
      A →+* Localization.AtPrime (p : PrimeSpectrum A).asIdeal) = algebraMap A _ :=
    RingHom.ext (atPrimeAlgEquivOfIsLocalRing p hp).commutes
  have : IsAdicComplete
      ((IsAdicRing.ideal A).map (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
      (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
    congrArg (IsAdicRing.ideal A).map he ▸
      (IsAdicComplete.congr_ringEquiv (IsAdicRing.ideal A)
        (atPrimeAlgEquivOfIsLocalRing p hp).toRingEquiv).mpr
        (IsAdicRing.ideal_spec A).2.2
  AdicCompletion.of_bijective _ _

/-- For a complete local adic ring `A` at its unique closed point `p` (with `𝔭 = 𝔪_A`), the
canonical map `A → 𝒪_{Spf A, p}` is bijective. -/
theorem toStalk_bijective_of_isLocalRing [IsLocalRing A]
    (hp : (p : PrimeSpectrum A).asIdeal = maximalIdeal A) :
    Function.Bijective (toStalk p) := by
  have hcomp_bij : Function.Bijective (stalkToCompletedAtPrime p ∘ toStalk p) := by
    convert (algebraMap_completedAtPrime_bijective_of_isLocalRing p hp).comp
      (bijective_algebraMap_of_linearEquiv (atPrimeAlgEquivOfIsLocalRing p hp).toLinearEquiv)
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
    (bijective_algebraMap_of_linearEquiv (atPrimeAlgEquivOfIsLocalRing p hp).toLinearEquiv)).mp ?_
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

/-! ### Flatness, dimension height, and Cohen–Macaulay transfer for noetherian `A` -/

section Noetherian

variable [IsNoetherianRing A]

/-- For noetherian `A`, `𝒪_{Spf A, p} → Â_𝔭` is flat (EGA I, Ch. 0, 7.6.17). -/
theorem flat_stalkToCompletedAtPrime : (stalkToCompletedAtPrime p).Flat :=
  (faithfullyFlat_stalkToCompletedAtPrime p).flat

/-- For noetherian `A`, the Krull dimension of the stalk `𝒪_{Spf A, p}` is the height of the prime
ideal `𝔭`. -/
theorem ringKrullDim_stalk_eq_height :
    ringKrullDim ((Spf A).presheaf.stalk p) =
      ((p : PrimeSpectrum A).asIdeal.height : WithBot ℕ∞) :=
  (ringKrullDim_stalk p).trans
    (IsLocalization.AtPrime.ringKrullDim_eq_height (p : PrimeSpectrum A).asIdeal _)

/-- For noetherian `A`, `Â_𝔭` is Cohen–Macaulay if and only if `𝒪_{Spf A, p}` is. -/
theorem isCohenMacaulay_completedAtPrime_iff_stalk :
    Module.IsCohenMacaulay (CompletedAtPrime p) (CompletedAtPrime p) ↔
      Module.IsCohenMacaulay ((Spf A).presheaf.stalk p) ((Spf A).presheaf.stalk p) := by
  algebraize [stalkToCompletedAtPrime p]
  have : Module.Flat _ _ := flat_stalkToCompletedAtPrime p
  exact Module.isCohenMacaulay_self_iff_of_flat_of_map_maximalIdeal_eq
    (map_maximalIdeal_stalkToCompletedAtPrime p)

/-- For noetherian `A`, `Â_𝔭` is Cohen–Macaulay if and only if `A_𝔭` is. -/
theorem isCohenMacaulay_completedAtPrime_iff :
    Module.IsCohenMacaulay (CompletedAtPrime p) (CompletedAtPrime p) ↔
      Module.IsCohenMacaulay (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  (isCohenMacaulay_completedAtPrime_iff_stalk p).trans (isCohenMacaulay_stalk_iff p)

end Noetherian

end TauCeti.FormalScheme.Spf

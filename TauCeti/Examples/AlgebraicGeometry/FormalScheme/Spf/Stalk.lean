/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk.Comparison
public import TauCeti.RingTheory.PowerSeries.AdicComplete
public import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
public import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# Examples of formal-spectrum stalks and completion comparisons

These checks exercise the stalk comparison API on `Spf A` without unfolding definitions:

* For the complete two-dimensional regular local ring `ℤ_[p]⟦X⟧` with its maximal-ideal-adic
  topology, `Spf ℤ_[p]⟦X⟧` has a single (closed) point, all three local rings
  `ℤ_[p]⟦X⟧_𝔪`, `𝒪_{Spf ℤ_[p]⟦X⟧, x}`, and `CompletedAtPrime x` are canonically isomorphic to
  `ℤ_[p]⟦X⟧` itself, and each is a regular Cohen–Macaulay local ring of Krull dimension `2`
  (distinct from the topological dimension `0` of the one-point carrier).
* For a discrete polynomial ring `k[X]` over a field `k` (ideal of definition `I = ⊥`), the closed
  point `(X)` has stalk and `I`-adic completed localisation both isomorphic to `k[X]_{(X)}` of
  dimension `1`, while their maximal-ideal-adic completions agree via the canonical commutative
  triangle (distinguishing `I`-adic completion from maximal-ideal completion). At the non-closed
  generic point `(0)`, the stalk has dimension `0`.
* For a general noetherian adic ring, the closed points of `carrier A` are homeomorphic to
  `MaximalSpectrum A`, and faithful flatness transfers dimension, regularity, and the
  Cohen–Macaulay property across `A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭`.
-/

public section

noncomputable section

open IsLocalRing Polynomial PowerSeries
open TauCeti TauCeti.FormalScheme TauCeti.FormalScheme.Spf

namespace TauCeti.Examples.FormalScheme.Spf.Stalk

section PadicPowerSeries

variable (p : ℕ) [Fact p.Prime]

/-- The maximal-ideal-adic topology on `ℤ_[p]⟦X⟧`. -/
local instance padicPowerSeriesTopology : TopologicalSpace ℤ_[p]⟦X⟧ :=
  (maximalIdeal ℤ_[p]⟦X⟧).adicTopology

/-- `ℤ_[p]⟦X⟧` is a topological ring for its maximal-ideal-adic topology. -/
local instance padicPowerSeriesTopologicalRing : IsTopologicalRing ℤ_[p]⟦X⟧ :=
  (Ideal.nonarchimedean (maximalIdeal ℤ_[p]⟦X⟧)).toIsTopologicalRing

/-- `ℤ_[p]⟦X⟧` with its maximal-ideal-adic topology is a complete adic ring. -/
local instance padicPowerSeriesIsAdicRing : IsAdicRing ℤ_[p]⟦X⟧ :=
  ⟨maximalIdeal ℤ_[p]⟦X⟧, IsNoetherian.noetherian _, rfl, inferInstance⟩

/-- The unique closed point of `Spf ℤ_[p]⟦X⟧`. -/
def padicPowerSeriesClosedPoint : carrier ℤ_[p]⟦X⟧ :=
  ⟨⟨maximalIdeal ℤ_[p]⟦X⟧, inferInstance⟩,
    mem_carrier_of_isMaximal (I := maximalIdeal ℤ_[p]⟦X⟧) rfl (IsAdicComplete.le_jacobson _)
      (maximalIdeal.isMaximal ℤ_[p]⟦X⟧)⟩

/-- `Spf ℤ_[p]⟦X⟧` has a single underlying point. -/
example : Subsingleton (carrier ℤ_[p]⟦X⟧) :=
  ⟨fun x y ↦ Subtype.ext (PrimeSpectrum.ext <| by
    have h (z : carrier ℤ_[p]⟦X⟧) : (z : PrimeSpectrum ℤ_[p]⟦X⟧).asIdeal = maximalIdeal _ :=
      ((maximalIdeal.isMaximal _).eq_of_le z.val.isPrime.ne_top
        ((mem_carrier_iff_le (I := maximalIdeal ℤ_[p]⟦X⟧) rfl).mp z.property)).symm
    exact (h x).trans (h y).symm)⟩

/-- The unique point of `Spf ℤ_[p]⟦X⟧` is closed. -/
example : IsClosed ({padicPowerSeriesClosedPoint p} : Set (carrier ℤ_[p]⟦X⟧)) :=
  (isClosed_singleton_iff_isMaximal (I := maximalIdeal ℤ_[p]⟦X⟧) rfl).mpr
    (maximalIdeal.isMaximal ℤ_[p]⟦X⟧)

/-- At the closed point of `Spf ℤ_[p]⟦X⟧`, all three canonical maps are bijective: the localisation,
the formal stalk, and the completed localisation are all `ℤ_[p]⟦X⟧` itself. -/
example :
    Function.Bijective (toStalk (padicPowerSeriesClosedPoint p)) ∧
    Function.Bijective (localizationToStalk (padicPowerSeriesClosedPoint p)) ∧
    Function.Bijective (stalkToCompletedAtPrime (padicPowerSeriesClosedPoint p)) :=
  ⟨toStalk_bijective_of_isLocalRing _ rfl, localizationToStalk_bijective_of_isLocalRing _ rfl,
   stalkToCompletedAtPrime_bijective_of_isLocalRing _ rfl⟩

/-- The localisation, stalk, and completed localisation of `Spf ℤ_[p]⟦X⟧` at its unique point all
have Krull dimension `2` (not the topological dimension `0` of its one-point carrier). -/
example :
    ringKrullDim (Localization.AtPrime
        (padicPowerSeriesClosedPoint p : PrimeSpectrum ℤ_[p]⟦X⟧).asIdeal) = 2 ∧
    ringKrullDim ((Spf ℤ_[p]⟦X⟧).presheaf.stalk (padicPowerSeriesClosedPoint p)) = 2 ∧
    ringKrullDim (CompletedAtPrime (padicPowerSeriesClosedPoint p)) = 2 := by
  have hstalk :
      ringKrullDim ((Spf ℤ_[p]⟦X⟧).presheaf.stalk (padicPowerSeriesClosedPoint p)) = 2 := by
    rw [← TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing (R := ℤ_[p])]
    exact (ringKrullDim_eq_of_ringEquiv
      (RingEquiv.ofBijective _ (toStalk_bijective_of_isLocalRing _ rfl))).symm
  exact ⟨(ringKrullDim_stalk _).symm.trans hstalk, hstalk,
    (ringKrullDim_completedAtPrime_eq_stalk _).trans hstalk⟩

/-- The localisation, stalk, and completed localisation of `Spf ℤ_[p]⟦X⟧` are all regular and
Cohen–Macaulay. -/
example :
    IsRegularLocalRing (Localization.AtPrime
        (padicPowerSeriesClosedPoint p : PrimeSpectrum ℤ_[p]⟦X⟧).asIdeal) ∧
    Module.IsCohenMacaulay
        (Localization.AtPrime (padicPowerSeriesClosedPoint p : PrimeSpectrum ℤ_[p]⟦X⟧).asIdeal)
        (Localization.AtPrime (padicPowerSeriesClosedPoint p : PrimeSpectrum ℤ_[p]⟦X⟧).asIdeal) ∧
    IsRegularLocalRing ((Spf ℤ_[p]⟦X⟧).presheaf.stalk (padicPowerSeriesClosedPoint p)) ∧
    Module.IsCohenMacaulay ((Spf ℤ_[p]⟦X⟧).presheaf.stalk (padicPowerSeriesClosedPoint p))
      ((Spf ℤ_[p]⟦X⟧).presheaf.stalk (padicPowerSeriesClosedPoint p)) ∧
    IsRegularLocalRing (CompletedAtPrime (padicPowerSeriesClosedPoint p)) ∧
    Module.IsCohenMacaulay (CompletedAtPrime (padicPowerSeriesClosedPoint p))
      (CompletedAtPrime (padicPowerSeriesClosedPoint p)) := by
  have hreg :
      IsRegularLocalRing ((Spf ℤ_[p]⟦X⟧).presheaf.stalk (padicPowerSeriesClosedPoint p)) :=
    .of_ringEquiv (RingEquiv.ofBijective _ (toStalk_bijective_of_isLocalRing _ rfl))
  have hcm := TauCeti.IsRegularLocalRing.isCohenMacaulay
    (R := (Spf ℤ_[p]⟦X⟧).presheaf.stalk (padicPowerSeriesClosedPoint p))
  exact ⟨(isRegularLocalRing_stalk_iff _).mp hreg, (isCohenMacaulay_stalk_iff _).mp hcm,
    hreg, hcm, (isRegularLocalRing_completedAtPrime_iff_stalk _).mpr hreg,
    (isCohenMacaulay_completedAtPrime_iff_stalk _).mpr hcm⟩

end PadicPowerSeries

section DiscretePolynomial

variable (k : Type*) [Field k]

/-- The discrete topology on `k[X]`, corresponding to the ideal of definition `I = ⊥`. -/
local instance discretePolyTopology : TopologicalSpace k[X] := ⊥
local instance discretePolyDiscrete : DiscreteTopology k[X] := ⟨rfl⟩

/-- The closed point `(X)` of discrete `Spf k[X]`. -/
def polyOrigin : carrier k[X] :=
  ⟨⟨Ideal.span {Polynomial.X}, (PrincipalIdealRing.isMaximal_of_irreducible
      (Polynomial.irreducible_X (R := k))).isPrime⟩,
    (mem_carrier_iff_le (is_bot_adic_iff.mpr inferInstance)).mpr bot_le⟩

/-- The non-closed generic point `(0)` of discrete `Spf k[X]`. -/
def polyGeneric : carrier k[X] :=
  ⟨⟨⊥, Ideal.isPrime_bot⟩, (mem_carrier_iff_le (is_bot_adic_iff.mpr inferInstance)).mpr bot_le⟩

/-- On discrete `Spf k[X]`, `(X)` is a closed point while `(0)` is not. -/
example :
    IsClosed ({polyOrigin k} : Set (carrier k[X])) ∧
    ¬ IsClosed ({polyGeneric k} : Set (carrier k[X])) := by
  have hbot : IsAdic (⊥ : Ideal k[X]) := is_bot_adic_iff.mpr inferInstance
  refine ⟨(isClosed_singleton_iff_isMaximal hbot).mpr
      (PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X), ?_⟩
  rw [isClosed_singleton_iff_isMaximal hbot]
  intro hmax
  have hlt : (⊥ : Ideal k[X]) < Ideal.span {Polynomial.X} :=
    bot_lt_iff_ne_bot.mpr (mt Ideal.span_singleton_eq_bot.mp Polynomial.X_ne_zero)
  exact hlt.ne (hmax.eq_of_le
    (PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X).ne_top hlt.le)

/-- For discrete `k[X]`, both `k[X]_{(X)} → 𝒪_{Spf k[X], (X)}` and
`𝒪_{Spf k[X], (X)} → CompletedAtPrime (X)` are bijective, while the maximal-ideal-adic completions
agree via the canonical commutative triangle. -/
example :
    Function.Bijective (localizationToStalk (polyOrigin k)) ∧
    Function.Bijective (stalkToCompletedAtPrime (polyOrigin k)) ∧
    (maximalIdealCompletionLocalizationEquivStalk (polyOrigin k)).trans
        (maximalIdealCompletionStalkEquivCompletedAtPrime (polyOrigin k)) =
      maximalIdealCompletionLocalizationEquivCompletedAtPrime (polyOrigin k) :=
  ⟨localizationToStalk_bijective_of_discreteTopology _,
   stalkToCompletedAtPrime_bijective_of_discreteTopology _,
   maximalIdealCompletionLocalizationEquivStalk_trans _⟩

/-- On discrete `k[X]`, the ideal of definition `I` maps to `⊥` in `CompletedAtPrime (X)`,
strictly smaller than the maximal ideal: `I`-adic completion stays `k[X]_{(X)}` rather than
`k⟦X⟧`. -/
example :
    (IsAdicRing.ideal k[X]).map (algebraMap k[X] (CompletedAtPrime (polyOrigin k))) = ⊥ ∧
    (IsAdicRing.ideal k[X]).map (algebraMap k[X] (CompletedAtPrime (polyOrigin k))) <
      maximalIdeal (CompletedAtPrime (polyOrigin k)) := by
  have hI : IsAdicRing.ideal k[X] = ⊥ := by
    obtain ⟨n, hn⟩ := (isAdic_iff.mp (IsAdicRing.ideal_spec k[X]).2.1).2 _
      (by simp : ((⊥ : Ideal k[X]) : Set k[X]) ∈ nhds 0)
    exact le_bot_iff.mp fun x hx ↦ eq_zero_of_pow_eq_zero (hn (Ideal.pow_mem_pow hx n))
  have hmap : (IsAdicRing.ideal k[X]).map (algebraMap k[X] (CompletedAtPrime (polyOrigin k))) = ⊥ :=
    le_bot_iff.mp (Ideal.map_le_iff_le_comap.mpr (hI.le.trans bot_le))
  refine ⟨hmap, hmap ▸ bot_lt_iff_ne_bot.mpr fun hbot ↦ ?_⟩
  have hne : (polyOrigin k : PrimeSpectrum k[X]).asIdeal ≠ ⊥ :=
    mt Ideal.span_singleton_eq_bot.mp Polynomial.X_ne_zero
  have : IsDiscreteValuationRing
      (Localization.AtPrime (polyOrigin k : PrimeSpectrum k[X]).asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain k[X] hne _
  have hinj : Function.Injective
      (algebraMap (Localization.AtPrime (polyOrigin k : PrimeSpectrum k[X]).asIdeal)
        (CompletedAtPrime (polyOrigin k))) := by
    rw [← stalkToCompletedAtPrime_comp_localizationToStalk]
    exact (stalkToCompletedAtPrime_bijective_of_discreteTopology _).1.comp
      (localizationToStalk_bijective_of_discreteTopology _).1
  exact IsDiscreteValuationRing.not_a_field' <| le_bot_iff.mp fun x hx ↦ hinj <| by
    rw [map_zero]
    exact Ideal.mem_bot.mp (hbot ▸ map_maximalIdeal_le _ (Ideal.mem_map_of_mem _ hx))

/-- At the closed point `(X)` of discrete `Spf k[X]`, the stalk has dimension `1`, whereas at the
generic point `(0)` the stalk has dimension `0`. -/
example :
    ringKrullDim ((Spf k[X]).presheaf.stalk (polyOrigin k)) = 1 ∧
    ringKrullDim ((Spf k[X]).presheaf.stalk (polyGeneric k)) = 0 := by
  refine ⟨?_, by rw [ringKrullDim_stalk_eq_height (polyGeneric k)]; simp [polyGeneric]⟩
  rw [ringKrullDim_stalk (polyOrigin k)]
  have hne : (polyOrigin k : PrimeSpectrum k[X]).asIdeal ≠ ⊥ :=
    mt Ideal.span_singleton_eq_bot.mp Polynomial.X_ne_zero
  have : IsDiscreteValuationRing
      (Localization.AtPrime (polyOrigin k : PrimeSpectrum k[X]).asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain k[X] hne _
  exact IsDiscreteValuationRing.ringKrullDim_eq_one _

end DiscretePolynomial

section GeneralNoetherian

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  [IsNoetherianRing A]

/-- Closed points of `Spf A` are canonically homeomorphic to `MaximalSpectrum A`. -/
example : MaximalSpectrum A ≃ₜ {p : carrier A // IsClosed ({p} : Set (carrier A))} :=
  have := (IsAdicRing.ideal_spec A).2.2
  maximalSpectrumHomeomorphClosedPoints (IsAdicRing.ideal_spec A).2.1 (IsAdicComplete.le_jacobson _)

/-- For any open prime `p` of a noetherian adic ring `A`, `A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭` are
faithfully flat local homomorphisms sharing their maximal-ideal completion, Krull dimension,
regularity, and Cohen–Macaulay property. -/
example (p : carrier A) :
    IsLocalHom (localizationToStalk p) ∧
    IsLocalHom (stalkToCompletedAtPrime p) ∧
    (localizationToStalk p).FaithfullyFlat ∧
    (stalkToCompletedAtPrime p).FaithfullyFlat ∧
    (maximalIdealCompletionLocalizationEquivStalk p).trans
        (maximalIdealCompletionStalkEquivCompletedAtPrime p) =
      maximalIdealCompletionLocalizationEquivCompletedAtPrime p ∧
    ringKrullDim ((Spf A).presheaf.stalk p) =
      ringKrullDim (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) ∧
    ringKrullDim (CompletedAtPrime p) = ringKrullDim ((Spf A).presheaf.stalk p) ∧
    (IsRegularLocalRing ((Spf A).presheaf.stalk p) ↔
      IsRegularLocalRing (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) ∧
    (IsRegularLocalRing (CompletedAtPrime p) ↔
      IsRegularLocalRing ((Spf A).presheaf.stalk p)) ∧
    (Module.IsCohenMacaulay ((Spf A).presheaf.stalk p) ((Spf A).presheaf.stalk p) ↔
      Module.IsCohenMacaulay (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) ∧
    (Module.IsCohenMacaulay (CompletedAtPrime p) (CompletedAtPrime p) ↔
      Module.IsCohenMacaulay ((Spf A).presheaf.stalk p) ((Spf A).presheaf.stalk p)) :=
  ⟨inferInstance, inferInstance, faithfullyFlat_localizationToStalk p,
   faithfullyFlat_stalkToCompletedAtPrime p, maximalIdealCompletionLocalizationEquivStalk_trans p,
   ringKrullDim_stalk p, ringKrullDim_completedAtPrime_eq_stalk p,
   isRegularLocalRing_stalk_iff p, isRegularLocalRing_completedAtPrime_iff_stalk p,
   isCohenMacaulay_stalk_iff p, isCohenMacaulay_completedAtPrime_iff_stalk p⟩

end GeneralNoetherian

end TauCeti.Examples.FormalScheme.Spf.Stalk

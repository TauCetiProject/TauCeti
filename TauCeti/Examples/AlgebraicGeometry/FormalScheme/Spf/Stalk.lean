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
  `ℤ_[p]⟦X⟧_𝔪`, `𝒪_{Spf ℤ_[p]⟦X⟧, x}`, and `LocalCompletion x` are canonically isomorphic to
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
    mem_carrier_of_isMaximal (I := maximalIdeal ℤ_[p]⟦X⟧) rfl (maximalIdeal ℤ_[p]⟦X⟧)⟩

/-- `Spf ℤ_[p]⟦X⟧` has a single underlying point. -/
example : Subsingleton (carrier ℤ_[p]⟦X⟧) := by
  refine ⟨fun x y ↦ Subtype.ext (PrimeSpectrum.ext ?_)⟩
  have hmax : ∀ z : carrier ℤ_[p]⟦X⟧,
      (z : PrimeSpectrum ℤ_[p]⟦X⟧).asIdeal = maximalIdeal ℤ_[p]⟦X⟧ :=
    fun z ↦ ((maximalIdeal.isMaximal ℤ_[p]⟦X⟧).eq_of_le z.1.isPrime.ne_top
      ((mem_carrier_iff_le (I := maximalIdeal ℤ_[p]⟦X⟧) rfl).mp z.2)).symm
  exact (hmax x).trans (hmax y).symm

/-- The unique point of `Spf ℤ_[p]⟦X⟧` is closed. -/
example : IsClosed ({padicPowerSeriesClosedPoint p} : Set (carrier ℤ_[p]⟦X⟧)) :=
  (isClosed_singleton_iff_isMaximal (I := maximalIdeal ℤ_[p]⟦X⟧) rfl
    (padicPowerSeriesClosedPoint p)).mpr (maximalIdeal.isMaximal ℤ_[p]⟦X⟧)

/-- At the closed point of `Spf ℤ_[p]⟦X⟧`, all three canonical maps are bijective: the localisation,
the formal stalk, and the completed localisation are all `ℤ_[p]⟦X⟧` itself. -/
example :
    Function.Bijective (toStalk (padicPowerSeriesClosedPoint p)) ∧
    Function.Bijective (localizationToStalk (padicPowerSeriesClosedPoint p)) ∧
    Function.Bijective (stalkToLocalCompletion (padicPowerSeriesClosedPoint p)) :=
  ⟨toStalk_bijective_of_isLocalRing _ rfl,
   localizationToStalk_bijective_of_isLocalRing _ rfl,
   stalkToLocalCompletion_bijective_of_isLocalRing _ rfl⟩

/-- The stalk and completed localisation of `Spf ℤ_[p]⟦X⟧` at its unique point have Krull dimension
`2` (not the topological dimension `0` of its one-point carrier). -/
example :
    ringKrullDim ((Spf ℤ_[p]⟦X⟧).presheaf.stalk (padicPowerSeriesClosedPoint p)) = 2 ∧
    ringKrullDim (LocalCompletion (padicPowerSeriesClosedPoint p)) = 2 := by
  have hA : ringKrullDim ℤ_[p]⟦X⟧ = 2 :=
    TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing
  have hstalk :
      ringKrullDim ((Spf ℤ_[p]⟦X⟧).presheaf.stalk (padicPowerSeriesClosedPoint p)) = 2 := by
    rw [← hA]
    exact (ringKrullDim_eq_of_ringEquiv
      (RingEquiv.ofBijective _ (toStalk_bijective_of_isLocalRing _ rfl))).symm
  refine ⟨hstalk, ?_⟩
  rw [ringKrullDim_localCompletion_eq_stalk (padicPowerSeriesClosedPoint p)]
  exact hstalk

/-- The stalk and completed localisation of `Spf ℤ_[p]⟦X⟧` are regular and Cohen–Macaulay. -/
example :
    IsRegularLocalRing ((Spf ℤ_[p]⟦X⟧).presheaf.stalk (padicPowerSeriesClosedPoint p)) ∧
    Module.IsCohenMacaulay ((Spf ℤ_[p]⟦X⟧).presheaf.stalk (padicPowerSeriesClosedPoint p))
      ((Spf ℤ_[p]⟦X⟧).presheaf.stalk (padicPowerSeriesClosedPoint p)) := by
  have hregStalk :
      IsRegularLocalRing ((Spf ℤ_[p]⟦X⟧).presheaf.stalk (padicPowerSeriesClosedPoint p)) :=
    IsRegularLocalRing.of_ringEquiv
      (RingEquiv.ofBijective _ (toStalk_bijective_of_isLocalRing _ rfl))
  exact ⟨hregStalk, TauCeti.IsRegularLocalRing.isCohenMacaulay⟩

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
  refine ⟨(isClosed_singleton_iff_isMaximal hbot (polyOrigin k)).mpr
      (PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X), ?_⟩
  rw [isClosed_singleton_iff_isMaximal hbot]
  intro hmax
  have hlt : (⊥ : Ideal k[X]) < Ideal.span {Polynomial.X} :=
    bot_lt_iff_ne_bot.mpr (mt Ideal.span_singleton_eq_bot.mp Polynomial.X_ne_zero)
  have hne : Ideal.span {(Polynomial.X : k[X])} ≠ ⊤ :=
    (PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X).ne_top
  exact hlt.ne (hmax.eq_of_le hne hlt.le)

/-- For discrete `k[X]`, both `k[X]_{(X)} → 𝒪_{Spf k[X], (X)}` and
`𝒪_{Spf k[X], (X)} → LocalCompletion (X)` are bijective, while the maximal-ideal-adic completions
agree via the canonical commutative triangle. -/
example :
    Function.Bijective (localizationToStalk (polyOrigin k)) ∧
    Function.Bijective (stalkToLocalCompletion (polyOrigin k)) ∧
    (maximalIdealCompletionLocalizationEquivStalk (polyOrigin k)).trans
        (maximalIdealCompletionStalkEquivLocalCompletion (polyOrigin k)) =
      maximalIdealCompletionLocalizationEquivLocalCompletion (polyOrigin k) :=
  ⟨localizationToStalk_bijective_of_discreteTopology _,
   stalkToLocalCompletion_bijective_of_discreteTopology _,
   maximalIdealCompletionLocalizationEquivStalk_trans _⟩

/-- On discrete `k[X]`, the ideal of definition `I` maps to `⊥` in `LocalCompletion (X)`, strictly
smaller than the maximal ideal: `I`-adic completion stays `k[X]_{(X)}` rather than `k⟦X⟧`. -/
example :
    (IsAdicRing.ideal k[X]).map (algebraMap k[X] (LocalCompletion (polyOrigin k))) <
      maximalIdeal (LocalCompletion (polyOrigin k)) := by
  have hI : IsAdicRing.ideal k[X] = ⊥ := by
    have htop : ((⊥ : Ideal k[X]) : Set k[X]) ∈ nhds (0 : k[X]) := by
      simp
    obtain ⟨n, hn⟩ := (isAdic_iff.mp (IsAdicRing.ideal_spec k[X]).2.1).2 _ htop
    have hpow : IsAdicRing.ideal k[X] ^ n = ⊥ := le_bot_iff.mp hn
    exact le_bot_iff.mp fun x hx ↦
      eq_zero_of_pow_eq_zero (Ideal.mem_bot.mp (hpow ▸ Ideal.pow_mem_pow hx n))
  have hmap :
      (IsAdicRing.ideal k[X]).map (algebraMap k[X] (LocalCompletion (polyOrigin k))) = ⊥ := by
    rw [← Ideal.map_bot (f := algebraMap k[X] (LocalCompletion (polyOrigin k)))]
    exact congrArg (Ideal.map (algebraMap k[X] (LocalCompletion (polyOrigin k)))) hI
  rw [hmap]
  refine bot_lt_iff_ne_bot.mpr fun hbot ↦ ?_
  have hX : algebraMap k[X] (LocalCompletion (polyOrigin k)) Polynomial.X ∈
      maximalIdeal (LocalCompletion (polyOrigin k)) := by
    rw [← stalkToLocalCompletion_toStalk, ← localizationToStalk_algebraMap,
      stalkToLocalCompletion_localizationToStalk, ← map_maximalIdeal_stalkToLocalCompletion,
      ← map_maximalIdeal_localizationToStalk, Ideal.map_map,
      stalkToLocalCompletion_comp_localizationToStalk]
    refine Ideal.mem_map_of_mem _ ?_
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (polyOrigin k : PrimeSpectrum k[X]).asIdeal]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span rfl)
  rw [hbot, Ideal.mem_bot] at hX
  have hinj : Function.Injective (algebraMap k[X] (LocalCompletion (polyOrigin k))) := by
    have hcomp : (algebraMap k[X] (LocalCompletion (polyOrigin k)) : _ → _) =
        stalkToLocalCompletion (polyOrigin k) ∘ localizationToStalk (polyOrigin k) ∘
          algebraMap k[X] (Localization.AtPrime (polyOrigin k : PrimeSpectrum k[X]).asIdeal) := by
      ext a
      simp [IsScalarTower.algebraMap_apply k[X]
        (Localization.AtPrime (polyOrigin k : PrimeSpectrum k[X]).asIdeal)
        (LocalCompletion (polyOrigin k))]
    rw [hcomp]
    exact (stalkToLocalCompletion_bijective_of_discreteTopology _).1.comp
      ((localizationToStalk_bijective_of_discreteTopology _).1.comp
        (IsLocalization.injective _
          (polyOrigin k : PrimeSpectrum k[X]).asIdeal.primeCompl_le_nonZeroDivisors))
  exact Polynomial.X_ne_zero (hinj (hX.trans (map_zero _).symm))

/-- At the closed point `(X)` of discrete `Spf k[X]`, the stalk has dimension `1`, whereas at the
generic point `(0)` the stalk has dimension `0`. -/
example :
    ringKrullDim ((Spf k[X]).presheaf.stalk (polyOrigin k)) = 1 ∧
    ringKrullDim ((Spf k[X]).presheaf.stalk (polyGeneric k)) = 0 := by
  constructor
  · rw [ringKrullDim_stalk_eq (polyOrigin k)]
    have hne : (polyOrigin k : PrimeSpectrum k[X]).asIdeal ≠ ⊥ :=
      mt Ideal.span_singleton_eq_bot.mp Polynomial.X_ne_zero
    have : IsDiscreteValuationRing
        (Localization.AtPrime (polyOrigin k : PrimeSpectrum k[X]).asIdeal) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain k[X] hne _
    exact IsDiscreteValuationRing.ringKrullDim_eq_one _
  · rw [ringKrullDim_stalk_eq_height (polyGeneric k)]
    change ((⊥ : Ideal k[X]).height : WithBot ℕ∞) = 0
    simp

end DiscretePolynomial

section GeneralNoetherian

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  [IsNoetherianRing A]

/-- Closed points of `Spf A` are canonically homeomorphic to `MaximalSpectrum A`. -/
example : MaximalSpectrum A ≃ₜ {p : carrier A // IsClosed ({p} : Set (carrier A))} :=
  have := (IsAdicRing.ideal_spec A).2.2
  maximalSpectrumHomeomorphClosedPoints (IsAdicRing.ideal_spec A).2.1

/-- For any open prime `p` of a noetherian adic ring `A`, `A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭` are
faithfully flat local homomorphisms sharing their maximal-ideal completion, Krull dimension,
regularity, and Cohen–Macaulay property. -/
example (p : carrier A) :
    (localizationToStalk p).FaithfullyFlat ∧
    (stalkToLocalCompletion p).FaithfullyFlat ∧
    ringKrullDim ((Spf A).presheaf.stalk p) =
      ringKrullDim (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) ∧
    (IsRegularLocalRing ((Spf A).presheaf.stalk p) ↔
      IsRegularLocalRing (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) ∧
    (Module.IsCohenMacaulay ((Spf A).presheaf.stalk p) ((Spf A).presheaf.stalk p) ↔
      Module.IsCohenMacaulay (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) :=
  ⟨faithfullyFlat_localizationToStalk p,
   faithfullyFlat_stalkToLocalCompletion p,
   ringKrullDim_stalk_eq p,
   isRegularLocalRing_stalk_iff p,
   isCohenMacaulay_stalk_iff p⟩

end GeneralNoetherian

end TauCeti.Examples.FormalScheme.Spf.Stalk

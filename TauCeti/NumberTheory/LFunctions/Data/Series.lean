/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.Basic
public import TauCeti.Analysis.Meromorphic.Continuation

/-!
# Canonical analytic cards from Dirichlet series

`AnalyticLFunctionData.ofSeries` constructs a card from coefficients, a conductor, gamma shifts
and a proposed polar divisor. Its completed function is the canonical meromorphic continuation
of the completed Dirichlet series from `Re s > 1`. Its root number is extracted as
`Λ(2) / conj Λ(-1)`, rather than supplied independently.

This construction alone does not assert existence of a continuation, correctness of the polar
divisor, or a functional equation. The comparison theorem `ofSeries_eq_normalized` identifies it
with any card having those properties, up to replacing the completed function by its meromorphic
normal form. That replacement matters at poles: arbitrary meromorphic representatives need not
have the canonical value zero there. `ofSeries_eq` gives exact recovery for a normal-form card.

The root-number extraction uses the functional equation at a regular point where the completed
function is nonzero. No Euler-product or gamma-factor nonvanishing assumption is hidden in the
constructor; applications supply nonvanishing at `2`.

The completion and functional-equation conventions are those of Iwaniec--Kowalski,
*Analytic Number Theory*, §5.1. Canonical continuation uses Mathlib's `toMeromorphicNFOn`
through `TauCeti.meromorphicContinuation`.
-/

public section

open Complex ComplexConjugate Set

namespace TauCeti.LFunctions.AnalyticLFunctionData

/-- The analytic card obtained by canonically continuing a completed Dirichlet series from
`Re s > 1`. The root number is `Λ(2) / conj Λ(-1)`. The supplied polar divisor is data, not a
claim about the resulting function. If no continuation exists, the completed function and root
number are zero, by the convention for `meromorphicContinuation`. -/
noncomputable def ofSeries (coeff : ℕ → ℂ) (conductor : ℕ+) (gammaR gammaC : Multiset ℂ)
    (polarOrder : ℂ →₀ ℕ) : AnalyticLFunctionData :=
  let Λ := meromorphicContinuation 1 fun s ↦ ((conductor : ℕ) : ℂ) ^ (s / 2) *
    ((gammaR.map fun μ ↦ Gammaℝ (s + μ)).prod * (gammaC.map fun ν ↦ Gammaℂ (s + ν)).prod) *
      LSeries coeff s
  { coeff := coeff
    conductor := conductor
    gammaR := gammaR
    gammaC := gammaC
    rootNumber := Λ 2 / conj (Λ (-1))
    completed := Λ
    polarOrder := polarOrder }

variable (a : ℕ → ℂ) (N : ℕ+) (μ ν : Multiset ℂ) (p : ℂ →₀ ℕ)

@[simp]
theorem ofSeries_coeff : (ofSeries a N μ ν p).coeff = a := (rfl)

@[simp]
theorem ofSeries_conductor : (ofSeries a N μ ν p).conductor = N := (rfl)

@[simp]
theorem ofSeries_gammaR : (ofSeries a N μ ν p).gammaR = μ := (rfl)

@[simp]
theorem ofSeries_gammaC : (ofSeries a N μ ν p).gammaC = ν := (rfl)

@[simp]
theorem ofSeries_polarOrder : (ofSeries a N μ ν p).polarOrder = p := (rfl)

/-- The completed function of the series card is its canonical meromorphic continuation. -/
theorem ofSeries_completed : (ofSeries a N μ ν p).completed =
    meromorphicContinuation 1 (fun s ↦ ((N : ℕ) : ℂ) ^ (s / 2) *
      (ofSeries a N μ ν p).gammaFactor s * LSeries a s) := by
  simp only [gammaFactor_def, ofSeries_gammaR, ofSeries_gammaC]
  rfl

/-- The root number of the series card is determined by two values of its completion. -/
@[simp]
theorem ofSeries_rootNumber : (ofSeries a N μ ν p).rootNumber =
    (ofSeries a N μ ν p).completed 2 / conj ((ofSeries a N μ ν p).completed (-1)) := (rfl)

/-- The constructed completion is in meromorphic normal form, even if continuation fails. -/
theorem meromorphicNFOn_ofSeries_completed :
    MeromorphicNFOn (ofSeries a N μ ν p).completed univ := by
  rw [ofSeries_completed]
  exact meromorphicNFOn_meromorphicContinuation _ _

/-- Existence of a normal-form continuation of the completed series gives Dirichlet agreement.
Normalization of the first coefficient and positivity of the degree are separate requirements. -/
theorem hasDirichletAgreement_ofSeries (ha : a 1 = 1) (hdeg : 0 < μ.card + 2 * ν.card)
    (h : ∃ F : ℂ → ℂ, MeromorphicNFOn F univ ∧
      EqOn F (fun s ↦ ((N : ℕ) : ℂ) ^ (s / 2) * (ofSeries a N μ ν p).gammaFactor s *
        LSeries a s) {s | 1 < s.re}) :
    (ofSeries a N μ ν p).HasDirichletAgreement where
  coeff_one := ha
  degree_pos := by simpa only [degree_def, ofSeries_gammaR, ofSeries_gammaC] using hdeg
  completed_eq s hs := by
    rw [ofSeries_completed]
    exact meromorphicContinuation_eqOn h hs

variable {d : AnalyticLFunctionData}

/-- A card with Dirichlet agreement, continuation and functional equation is recovered by
`ofSeries`, with its completed function replaced by the canonical normal form. The original
completion must be regular on the defining half-plane and nonzero at `2`. -/
theorem ofSeries_eq_normalized (hD : d.HasDirichletAgreement)
    (hM : d.HasMeromorphicContinuation) (hF : d.HasFunctionalEquation)
    (hreg : ∀ s : ℂ, 1 < s.re → d.polarOrder s = 0) (hne : d.completed 2 ≠ 0) :
    ofSeries d.coeff d.conductor d.gammaR d.gammaC d.polarOrder =
      { d with completed := toMeromorphicNFOn d.completed univ } := by
  have hcomp : (ofSeries d.coeff d.conductor d.gammaR d.gammaC d.polarOrder).completed =
      toMeromorphicNFOn d.completed univ := by
    rw [ofSeries_completed]
    apply meromorphicContinuation_eq_toMeromorphicNFOn hM.meromorphic
      (fun s hs ↦ hM.analyticAt s (hreg s hs))
    intro s hs
    simpa only [gammaFactor_def, ofSeries_gammaR, ofSeries_gammaC] using hD.completed_eq s hs
  have h2 : d.polarOrder 2 = 0 := hreg 2 (by norm_num)
  have hm1 : d.polarOrder (-1) = 0 := by
    simpa only [map_ofNat, (by norm_num : (1 : ℂ) - 2 = -1)] using
      (hF.polarOrder_one_sub_conj 2).trans h2
  have hval (s : ℂ) (hs : d.polarOrder s = 0) :
      toMeromorphicNFOn d.completed univ s = d.completed s := by
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hM.meromorphic.meromorphicOn (mem_univ s),
      toMeromorphicNFAt_eq_self.mpr (hM.analyticAt s hs).meromorphicNFAt]
  have hroot : (ofSeries d.coeff d.conductor d.gammaR d.gammaC d.polarOrder).rootNumber =
      d.rootNumber := by
    rw [ofSeries_rootNumber, hcomp, hval 2 h2, hval (-1) hm1]
    simpa only [map_ofNat, (by norm_num : (1 : ℂ) - 2 = -1)] using
      (hF.rootNumber_eq_div h2 hne).symm
  exact AnalyticLFunctionData.ext rfl rfl rfl rfl hroot hcomp rfl

/-- Exact recovery of a card already in meromorphic normal form. Unlike equality of arbitrary
meromorphic representatives, this equality includes the canonical values at poles. -/
theorem ofSeries_eq (hD : d.HasDirichletAgreement) (hF : d.HasFunctionalEquation)
    (hNF : MeromorphicNFOn d.completed univ) (h2 : d.polarOrder 2 = 0)
    (hne : d.completed 2 ≠ 0) :
    ofSeries d.coeff d.conductor d.gammaR d.gammaC d.polarOrder = d := by
  have hcomp : (ofSeries d.coeff d.conductor d.gammaR d.gammaC d.polarOrder).completed =
      d.completed := by
    rw [ofSeries_completed]
    apply meromorphicContinuation_eq hNF
    intro s hs
    simpa only [gammaFactor_def, ofSeries_gammaR, ofSeries_gammaC] using hD.completed_eq s hs
  have hroot : (ofSeries d.coeff d.conductor d.gammaR d.gammaC d.polarOrder).rootNumber =
      d.rootNumber := by
    rw [ofSeries_rootNumber, hcomp]
    simpa only [map_ofNat, (by norm_num : (1 : ℂ) - 2 = -1)] using
      (hF.rootNumber_eq_div h2 hne).symm
  exact AnalyticLFunctionData.ext rfl rfl rfl rfl hroot hcomp rfl

end TauCeti.LFunctions.AnalyticLFunctionData

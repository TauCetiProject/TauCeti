/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.ConvergenceRadius
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# `q`-coefficient vanishing and cusp-function growth

The dictionary between vanishing of the first `N` `q`-coefficients of a periodic function
on `ℍ` and `O(‖q‖^N)` growth of its cusp function at `0`, in both directions, together with
the limit of the function's values along `Im τ → ∞`. The general layer asks only for
analyticity of the cusp function at `0` (with periodicity for the limit); the corollaries
specialize to modular forms. These are the analytic inputs of the norm step of the
general-level valence reduction: growth bounds are multiplicative, so they transport
coefficient vanishing through the norm map to level one.

## Main declarations

* `TauCeti.UpperHalfPlane.cuspFunction_isBigO_pow_iff_qExpansion_coeff_eq_zero`: the
  dictionary, for any function on `ℍ` whose cusp function is analytic at `0`.
* `TauCeti.UpperHalfPlane.tendsto_valueAtInfty`: an `h`-periodic function with cusp
  function analytic at `0` tends to `valueAtInfty` along `atImInfty`.
* The `TauCeti.ModularFormClass` corollaries of both, for a modular form on a
  subgroup with `h` in its strict period set.

## References

Ported from AINTLIB's `LeanModularForms` project
([github.com/CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB), commit `2baa76f742`,
Apache 2.0, the file
`projects/LeanModularForms/LeanModularForms/Modularforms/DimGenCongLevels/Auxiliary.lean`),
generalized to the function level and reproved through Mathlib's power-series uniqueness
machinery instead of the source's circle-integral bounds.
-/

open UpperHalfPlane Filter

open scoped Topology

namespace TauCeti.UpperHalfPlane

noncomputable section

variable {h : ℝ} {f : ℍ → ℂ}

/-- A function on `ℍ` that is `h`-periodic with cusp function analytic at `0` tends to
`valueAtInfty` along `atImInfty`. -/
public lemma tendsto_valueAtInfty (hh : 0 < h) (hper : Function.Periodic (f ∘ ofComplex) h)
    (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0) :
    Tendsto f atImInfty (𝓝 (valueAtInfty f)) := by
  rw [← cuspFunction_apply_zero hh hfanalytic hper]
  exact (hfanalytic.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)).congr fun τ ↦
    eq_cuspFunction τ hh.ne' hper

/-- The cusp function of `f` is `O(‖q‖^N)` near `0` if and only if the first `N`
`q`-coefficients of `f` vanish, provided the cusp function is analytic at `0`. -/
public lemma cuspFunction_isBigO_pow_iff_qExpansion_coeff_eq_zero
    (hfanalytic : AnalyticAt ℂ (cuspFunction h f) 0) {N : ℕ} :
    cuspFunction h f =O[𝓝 (0 : ℂ)] (fun q : ℂ ↦ ‖q‖ ^ N) ↔
      ∀ n < N, (qExpansion h f).coeff n = 0 := by
  have hp := hasFPowerSeriesAt_cuspFunction hfanalytic
  -- A partial sum of the `q`-expansion vanishes once the coefficients below its length do.
  have hps {M : ℕ} (hM : ∀ n < M, (qExpansion h f).coeff n = 0) :
      (FormalMultilinearSeries.ofScalars ℂ fun m ↦ (qExpansion h f).coeff m).partialSum M = 0 := by
    ext q
    exact Finset.sum_eq_zero fun n hn ↦ by simp [hM n (Finset.mem_range.mp hn)]
  refine ⟨fun hO n hn ↦ ?_, fun hcoeff ↦ by
    simpa [hps hcoeff] using hp.isBigO_sub_partialSum_pow N⟩
  -- Conversely, once the coefficients below `n` vanish, the `n`-th term of the series is the
  -- cusp function up to `O(‖q‖^(n + 1))`, so it is itself `O(‖q‖^(n + 1))` and thus zero.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hON : cuspFunction h f =O[𝓝 (0 : ℂ)] fun q : ℂ ↦ ‖q‖ ^ (n + 1) := by
    refine hO.trans (Asymptotics.isBigO_iff.mpr ⟨1, ?_⟩)
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with q hq
    simpa [abs_of_nonneg (norm_nonneg q)] using
      pow_le_pow_of_le_one (norm_nonneg q) (mem_ball_zero_iff.mp hq).le hn
  have hterm : (fun q : ℂ ↦
      FormalMultilinearSeries.ofScalars ℂ (fun m ↦ (qExpansion h f).coeff m) n fun _ ↦ q)
        =O[𝓝 (0 : ℂ)] fun q : ℂ ↦ ‖q‖ ^ (n + 1) := by
    refine (hON.sub (by simpa only [zero_add] using hp.isBigO_sub_partialSum_pow (n + 1)))
      |>.congr_left fun q ↦ ?_
    simp [FormalMultilinearSeries.partialSum_succ, hps fun m hm ↦ ih m hm (hm.trans hn)]
  simpa [FormalMultilinearSeries.ofScalars_apply_eq] using
    hterm.continuousMultilinearMap_apply_eq_zero 1

end

end TauCeti.UpperHalfPlane

namespace TauCeti.ModularFormClass

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {h : ℝ} {F : Type*} [FunLike F ℍ ℂ]

/-- Values of a modular form tend to `valueAtInfty` along `atImInfty`. -/
public lemma tendsto_valueAtInfty [ModularFormClass F Γ k] (f : F) (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) :
    Tendsto f atImInfty (𝓝 (valueAtInfty f)) :=
  TauCeti.UpperHalfPlane.tendsto_valueAtInfty hh
    (SlashInvariantFormClass.periodic_comp_ofComplex (k := k) f hΓ)
    (_root_.ModularFormClass.analyticAt_cuspFunction_zero (F := F) (k := k) (f := f) hh hΓ)

/-- The cusp function of a modular form is `O(‖q‖^N)` near `0` if and only if its first `N`
`q`-coefficients vanish. -/
public lemma cuspFunction_isBigO_pow_iff_qExpansion_coeff_eq_zero [ModularFormClass F Γ k]
    (f : F) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {N : ℕ} :
    cuspFunction h f =O[𝓝 (0 : ℂ)] (fun q : ℂ ↦ ‖q‖ ^ N) ↔
      ∀ n < N, (qExpansion h f).coeff n = 0 :=
  TauCeti.UpperHalfPlane.cuspFunction_isBigO_pow_iff_qExpansion_coeff_eq_zero
    (_root_.ModularFormClass.analyticAt_cuspFunction_zero (F := F) (k := k) (f := f) hh hΓ)

end TauCeti.ModularFormClass

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import TauCeti.MeasureTheory.Function.Lp.Dual
import TauCeti.Analysis.Distribution.SchwartzSpace.Lp
import TauCeti.Analysis.Distribution.TemperateGrowth

/-!
# Norming `Lᵠ` functions by Schwartz functions

Let `μ` be a measure of temperate growth on a finite-dimensional real normed space, and let
`p < ∞` and `q` be Hölder conjugate. The Schwartz functions are dense in `Lᵖ(μ)`, so they norm the
dual space `Lᵠ(μ)`: for `B ≥ 0`, an `Lᵠ` function `h` whose pairings with Schwartz functions
satisfy `‖∫ g h‖ ≤ B ‖g‖_p` has `‖h‖_q ≤ B`
(`MeasureTheory.Lp.norm_le_of_forall_norm_toTemperedDistribution_apply_le`), and every
`r < ‖h‖_q` is exceeded by `‖∫ g h‖` for some Schwartz function `g` with `‖g‖_p < 1`
(`MeasureTheory.Lp.exists_lt_norm_toTemperedDistribution_apply_of_lt_norm`).

Conversely, for `1 ≤ p < ∞` and `B ≥ 0` every tempered distribution `u` with `‖u g‖ ≤ B ‖g‖_p`
for all Schwartz functions `g` is an `Lᵠ` function of norm at most `B`
(`TemperedDistribution.exists_eq_toTemperedDistribution_and_norm_le`). The bound extends `u` from
the dense Schwartz functions to a continuous linear functional on `Lᵖ(μ)`
(`SchwartzMap.exists_strongDual_apply_toLp_eq_and_norm_le`), and the dual of `Lᵖ(μ)` is `Lᵠ(μ)`
(`MeasureTheory.Lp.toDual_surjective`), including `L¹(μ)⋆ = L^∞(μ)` at `p = 1` for the
σ-finite measure `μ`. This is how an `Lᵠ` estimate for a
distribution is obtained by duality from estimates on test functions alone, for instance for the
blocks of a distribution in a Besov space of negative order.

## References

* G. B. Folland, *Real Analysis*, second edition, Theorem 6.16.
-/

public section

noncomputable section

open scoped ENNReal NNReal SchwartzMap

namespace MeasureTheory.Lp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.HasTemperateGrowth]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

omit [FiniteDimensional ℝ E] in
/-- The pairing of `h ∈ Lᵠ` with a Schwartz function `g`, as a tempered distribution, is the
value at `g` of the functional `MeasureTheory.Lp.toDual` of `h` on `Lᵖ`. -/
theorem toTemperedDistribution_apply_eq_toDual_apply [SigmaFinite μ] (h : Lp ℂ q μ)
    (g : 𝓢(E, ℂ)) :
    (h : 𝓢'(E, ℂ)) g = toDual ℂ μ q p h (g.toLp p μ) := by
  rw [toTemperedDistribution_apply, toDual_apply]
  refine integral_congr_ae ?_
  filter_upwards [g.coeFn_toLp p μ] with x hx
  rw [hx, smul_eq_mul, mul_comm]

/-- **Nearly norming Schwartz functions.** For `p < ∞`, `q` Hölder conjugate to `p` and
`h ∈ Lᵠ(μ)`, every `r < ‖h‖_q` is exceeded by `‖∫ g h‖` for some Schwartz function `g` with
`‖g‖_p < 1`. -/
theorem exists_lt_norm_toTemperedDistribution_apply_of_lt_norm (hp : p ≠ ∞) (h : Lp ℂ q μ)
    {r : ℝ} (hr : r < ‖h‖) :
    ∃ g : 𝓢(E, ℂ), ‖g.toLp p μ‖ < 1 ∧ r < ‖(h : 𝓢'(E, ℂ)) g‖ := by
  have := Measure.HasTemperateGrowth.isFiniteMeasureOnCompacts μ
  set Λ := toDual ℂ μ q p h
  -- The open set of `f` with `‖f‖ < 1` and `r < ‖Λ f‖` is nonempty, as `‖Λ‖ = ‖h‖`, so it meets
  -- the dense range of the Schwartz functions.
  obtain ⟨g, hg1, hg⟩ := (SchwartzMap.denseRange_toLpCLM (F := ℂ) hp (μ := μ)).exists_mem_open
    (s := {f | ‖f‖ < 1 ∧ r < ‖Λ f‖})
    ((isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const (continuous_norm.comp Λ.continuous)))
    (Λ.exists_lt_apply_of_lt_opNorm (by rwa [LinearIsometry.norm_map]))
  rw [SchwartzMap.toLpCLM_apply] at hg1 hg
  exact ⟨g, hg1, by rwa [toTemperedDistribution_apply_eq_toDual_apply (p := p)]⟩

/-- **Norming by Schwartz functions.** For `p < ∞` and `q` Hölder conjugate to `p`, if
`h ∈ Lᵠ(μ)` satisfies `‖∫ g h‖ ≤ B ‖g‖_p` for every Schwartz function `g` and some `B ≥ 0`, then
`‖h‖_q ≤ B`. -/
theorem norm_le_of_forall_norm_toTemperedDistribution_apply_le (hp : p ≠ ∞) (h : Lp ℂ q μ)
    {B : ℝ} (hB : 0 ≤ B) (hh : ∀ g : 𝓢(E, ℂ), ‖(h : 𝓢'(E, ℂ)) g‖ ≤ B * ‖g.toLp p μ‖) :
    ‖h‖ ≤ B := by
  by_contra! hBh
  obtain ⟨g, hg1, hg⟩ := exists_lt_norm_toTemperedDistribution_apply_of_lt_norm hp h hBh
  exact (hg.trans_le ((hh g).trans (mul_le_of_le_one_right hB hg1.le))).false

end MeasureTheory.Lp

namespace TemperedDistribution

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.HasTemperateGrowth]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- **Distributions bounded in `Lᵖ` are `Lᵠ` functions.** For `1 ≤ p < ∞` and `q` Hölder
conjugate to `p`, a tempered distribution `u` with `‖u g‖ ≤ B ‖g‖_p` for every Schwartz function
`g` and some `B ≥ 0` is the tempered distribution of some `h ∈ Lᵠ(μ)` with `‖h‖_q ≤ B`. -/
theorem exists_eq_toTemperedDistribution_and_norm_le (hp_top : p ≠ ∞)
    (u : 𝓢'(E, ℂ)) {B : ℝ} (hB : 0 ≤ B) (hu : ∀ g : 𝓢(E, ℂ), ‖u g‖ ≤ B * ‖g.toLp p μ‖) :
    ∃ h : Lp ℂ q μ, (h : 𝓢'(E, ℂ)) = u ∧ ‖h‖ ≤ B := by
  have := Measure.HasTemperateGrowth.isFiniteMeasureOnCompacts μ
  -- Extend `u` from the dense Schwartz functions to a functional `Λ` on `Lᵖ`.
  obtain ⟨Λ, hΛu, hΛ⟩ :=
    SchwartzMap.exists_strongDual_apply_toLp_eq_and_norm_le hp_top (u : 𝓢(E, ℂ) →ₗ[ℂ] ℂ) hB hu
  -- `Λ` is integration against some `h ∈ Lᵠ`, as the dual of `Lᵖ` is `Lᵠ`.
  obtain ⟨h, hh⟩ := Lp.toDual_surjective (p := q) hp_top Λ
  -- `h` represents `u`.
  refine ⟨h, ?_, by rwa [← (Lp.toDual ℂ μ q p).norm_map h, hh]⟩
  ext g
  rw [Lp.toTemperedDistribution_apply_eq_toDual_apply (p := p), hh, hΛu, LinearMap.coe_ofClass]

end TemperedDistribution

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import TauCeti.MeasureTheory.Function.Lp.Dual
import Mathlib.Analysis.Normed.Operator.Extend
import TauCeti.Analysis.Distribution.TemperateGrowth

/-!
# Norming `Lᵠ` functions by Schwartz functions

Let `μ` be a measure of temperate growth on a finite-dimensional real normed space, and let
`p < ∞` and `q` be Hölder conjugate. The Schwartz functions are dense in `Lᵖ(μ)`, so they norm the
dual space `Lᵠ(μ)`: an `Lᵠ` function `h` whose pairings with Schwartz functions satisfy
`‖∫ g h‖ ≤ B ‖g‖_p` has `‖h‖_q ≤ B`
(`MeasureTheory.Lp.norm_le_of_forall_norm_toTemperedDistribution_apply_le`), and every
`r < ‖h‖_q` is exceeded by `‖∫ g h‖` for some Schwartz function `g` with `‖g‖_p < 1`
(`MeasureTheory.Lp.exists_lt_norm_toTemperedDistribution_apply_of_lt_norm`).

Conversely, for `1 < p < ∞` every tempered distribution `u` with `‖u g‖ ≤ B ‖g‖_p` for all
Schwartz functions `g` is an `Lᵠ` function of norm at most `B`
(`TemperedDistribution.exists_eq_toTemperedDistribution_and_norm_le`): the bound extends `u` from
the dense Schwartz functions to a continuous linear functional on `Lᵖ(μ)`, and the dual of `Lᵖ(μ)`
is `Lᵠ(μ)` (`MeasureTheory.Lp.dualEquiv`). This is how an `Lᵠ` estimate for a distribution is
obtained by duality from estimates on test functions alone, for instance for the blocks of a
distribution in a Besov space of negative order.

## References

* G. B. Folland, *Real Analysis*, second edition, Theorem 6.16.
-/

public section

noncomputable section

open scoped ENNReal SchwartzMap

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
`h ∈ Lᵠ(μ)` satisfies `‖∫ g h‖ ≤ B ‖g‖_p` for every Schwartz function `g`, then `‖h‖_q ≤ B`. -/
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

/-- **Distributions bounded in `Lᵖ` are `Lᵠ` functions.** For `1 < p < ∞` and `q` Hölder
conjugate to `p`, a tempered distribution `u` with `‖u g‖ ≤ B ‖g‖_p` for every Schwartz function
`g` is the tempered distribution of some `h ∈ Lᵠ(μ)` with `‖h‖_q ≤ B`. -/
theorem exists_eq_toTemperedDistribution_and_norm_le (hp : 1 < p) (hp_top : p ≠ ∞)
    (u : 𝓢'(E, ℂ)) {B : ℝ} (hB : 0 ≤ B) (hu : ∀ g : 𝓢(E, ℂ), ‖u g‖ ≤ B * ‖g.toLp p μ‖) :
    ∃ h : Lp ℂ q μ, (h : 𝓢'(E, ℂ)) = u ∧ ‖h‖ ≤ B := by
  have := Measure.HasTemperateGrowth.isFiniteMeasureOnCompacts μ
  -- Extend `u` from the dense Schwartz functions to a functional `Λ` on `Lᵖ`.
  set e : 𝓢(E, ℂ) →ₗ[ℂ] Lp ℂ p μ := (SchwartzMap.toLpCLM ℂ ℂ p μ).toLinearMap
  have he : DenseRange e := by
    have hcoe : ⇑e = ⇑(SchwartzMap.toLpCLM ℝ ℂ p μ) := by
      ext g : 1
      simp [e]
    rw [DenseRange, hcoe]
    exact SchwartzMap.denseRange_toLpCLM hp_top
  set S : 𝓢(E, ℂ) →ₗ[ℂ] ℂ := (u : 𝓢(E, ℂ) →ₗ[ℂ] ℂ)
  have hS : ∀ g, ‖S g‖ ≤ B * ‖e g‖ := fun g ↦ by simpa [S, e] using hu g
  set Λ := S.extendOfNorm e
  have hΛ : ‖Λ‖ ≤ B := Λ.opNorm_le_bound hB (LinearMap.norm_extendOfNorm_apply_le he B hS)
  -- `Λ` is integration against some `h ∈ Lᵠ`, which represents `u`.
  refine ⟨(Lp.dualEquiv ℂ μ q p hp hp_top).symm Λ, ?_, by simpa using hΛ⟩
  ext g
  rw [Lp.toTemperedDistribution_apply_eq_toDual_apply (p := p), ← Lp.coe_dualEquiv hp hp_top,
    LinearIsometryEquiv.apply_symm_apply]
  simpa [S, e] using LinearMap.extendOfNorm_eq he ⟨B, hS⟩ g

end TemperedDistribution

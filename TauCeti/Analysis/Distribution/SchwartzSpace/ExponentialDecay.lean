/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Exp.Shift

/-!
# Schwartz functions and Bessel-potential regularity from exponential derivative decay

For any positive decay rate `c`, the radial exponential `exp (-c ‖x‖)` absorbs every polynomial
weight `‖x‖ ^ k` (`TauCeti.exists_rpow_mul_exp_neg_mul_le`). A smooth map between real normed
spaces whose iterated derivatives of each order are bounded by multiples of `exp (-c ‖x‖)` — either
globally or outside compact sets (`cocompact`) — is therefore a Schwartz function.

Every real-valued Schwartz function on a finite-dimensional real inner product space embeds into
complex Schwartz space through `Complex.ofRealCLM`, hence defines a tempered distribution lying in
every Bessel-potential space `H^{s,p}` (`SchwartzMap.coe_mem_realSobolevFunctions`). Combining the
two steps places smooth real functions with exponentially decaying derivatives in
`TemperedDistribution.realSobolevFunctions E s p` at all real orders `s` simultaneously.

## Main declarations

* `SchwartzMap.ofNormIteratedFDerivLeMulExp`: a smooth map whose `n`-th derivative is globally
  bounded by `Kₙ exp (-c ‖x‖)`, `c > 0`, as a Schwartz function.
* `SchwartzMap.ofIsBigOIteratedFDerivExp`: a smooth map whose `n`-th derivative is
  `O(exp (-c ‖x‖))` along `cocompact`, `c > 0`, as a Schwartz function.
* `SchwartzMap.coe_mem_realSobolevFunctions`: every real Schwartz function lies in
  `TemperedDistribution.realSobolevFunctions E s p` for all `s` and `1 ≤ p`.
* `TemperedDistribution.mem_realSobolevFunctions_of_isBigO_iteratedFDeriv_exp`,
  `TemperedDistribution.mem_realSobolevFunctions_of_norm_iteratedFDeriv_le_mul_exp`: smooth real
  functions with exponentially decaying iterated derivatives lie in `realSobolevFunctions E s p`
  for every `s`.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999,
  §8.1 and §9.3.
-/

public section

noncomputable section

open Asymptotics Filter MeasureTheory
open scoped ContDiff ENNReal SchwartzMap

namespace SchwartzMap

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **A smooth map with exponentially decaying derivatives is a Schwartz function.** If `f : E → F`
is smooth and there is a rate `c > 0` such that each iterated derivative `Dⁿf` is globally bounded
by `Kₙ exp (-c ‖x‖)`, then `f` belongs to `𝓢(E, F)`. -/
def ofNormIteratedFDerivLeMulExp {f : E → F} (hf : ContDiff ℝ ∞ f) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ n : ℕ, ∃ K, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ K * Real.exp (-(c * ‖x‖))) :
    𝓢(E, F) where
  toFun := f
  smooth' := hf
  decay' k n := by
    obtain ⟨K, hK⟩ := hbound n
    obtain ⟨M, -, hM⟩ := TauCeti.exists_rpow_mul_exp_neg_mul_le (Nat.cast_nonneg k) hc
    refine ⟨max K 0 * M, fun x ↦ ?_⟩
    have hexp : 0 ≤ Real.exp (-(c * ‖x‖)) := (Real.exp_pos _).le
    have hKx : ‖iteratedFDeriv ℝ n f x‖ ≤ max K 0 * Real.exp (-(c * ‖x‖)) :=
      (hK x).trans (mul_le_mul_of_nonneg_right (le_max_left K 0) hexp)
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖
        ≤ ‖x‖ ^ k * (max K 0 * Real.exp (-(c * ‖x‖))) :=
          mul_le_mul_of_nonneg_left hKx (pow_nonneg (norm_nonneg x) k)
      _ = max K 0 * ((‖x‖ : ℝ) ^ (k : ℝ) * Real.exp (-(c * ‖x‖))) := by
          rw [Real.rpow_natCast]; ring
      _ ≤ max K 0 * M := mul_le_mul_of_nonneg_left (hM ‖x‖ (norm_nonneg x)) (le_max_right K 0)

theorem ofNormIteratedFDerivLeMulExp_apply {f : E → F} (hf : ContDiff ℝ ∞ f) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ n : ℕ, ∃ K, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ K * Real.exp (-(c * ‖x‖))) (x : E) :
    ofNormIteratedFDerivLeMulExp hf hc hbound x = f x := (rfl)

@[simp]
theorem coe_ofNormIteratedFDerivLeMulExp {f : E → F} (hf : ContDiff ℝ ∞ f) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ n : ℕ, ∃ K, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ K * Real.exp (-(c * ‖x‖))) :
    ⇑(ofNormIteratedFDerivLeMulExp hf hc hbound) = f := (rfl)

/-- **A smooth map whose iterated derivatives are `O(exp (-c ‖x‖))` outside compact sets is a
Schwartz function.** Continuity of each `Dⁿf` upgrades the asymptotic bound along `cocompact E` to
a global exponential bound. -/
def ofIsBigOIteratedFDerivExp {f : E → F} (hf : ContDiff ℝ ∞ f) {c : ℝ} (hc : 0 < c)
    (hdecay : ∀ n : ℕ,
      iteratedFDeriv ℝ n f =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖))) :
    𝓢(E, F) :=
  ofNormIteratedFDerivLeMulExp hf hc fun n ↦ by
    obtain ⟨K, hK⟩ := (hdecay n).bound
    refine TauCeti.exists_forall_le_mul_exp_of_eventually_le
      ((hf.continuous_iteratedFDeriv (mod_cast le_top)).norm) (K := K) ?_
    filter_upwards [hK] with x hx
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hx

theorem ofIsBigOIteratedFDerivExp_apply {f : E → F} (hf : ContDiff ℝ ∞ f) {c : ℝ} (hc : 0 < c)
    (hdecay : ∀ n : ℕ,
      iteratedFDeriv ℝ n f =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖))) (x : E) :
    ofIsBigOIteratedFDerivExp hf hc hdecay x = f x := (rfl)

@[simp]
theorem coe_ofIsBigOIteratedFDerivExp {f : E → F} (hf : ContDiff ℝ ∞ f) {c : ℝ} (hc : 0 < c)
    (hdecay : ∀ n : ℕ,
      iteratedFDeriv ℝ n f =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖))) :
    ⇑(ofIsBigOIteratedFDerivExp hf hc hdecay) = f := (rfl)

end Normed

section Sobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Every real Schwartz function lies in every real Bessel-potential space.** -/
theorem coe_mem_realSobolevFunctions (u : 𝓢(E, ℝ)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (u : E → ℝ) ∈ TemperedDistribution.realSobolevFunctions E s p := by
  let uℂ : 𝓢(E, ℂ) := u.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
  refine TemperedDistribution.mem_realSobolevFunctions_of_ae_eq_ofReal
    (v := uℂ.toLp p (volume : Measure E)) ?_ (uℂ.coeFn_toLp p (volume : Measure E))
  rw [Lp.toTemperedDistribution_toLp_eq]
  exact uℂ.memSobolev

end Sobolev

end SchwartzMap

namespace TemperedDistribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Bessel-potential regularity from asymptotic exponential derivative decay.** A smooth real
function whose iterated derivatives of every order are `O(exp (-c ‖x‖))` outside compact sets for
some `c > 0` lies in `realSobolevFunctions E s p` at every real order `s`. -/
theorem mem_realSobolevFunctions_of_isBigO_iteratedFDeriv_exp {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {c : ℝ} (hc : 0 < c)
    (hdecay : ∀ n : ℕ, iteratedFDeriv ℝ n f =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)))
    (s : ℝ) : f ∈ realSobolevFunctions E s p :=
  (SchwartzMap.ofIsBigOIteratedFDerivExp hf hc hdecay).coe_mem_realSobolevFunctions s p

/-- **Bessel-potential regularity from global exponential derivative decay.** A smooth real
function whose iterated derivatives satisfy `‖Dⁿf(x)‖ ≤ Kₙ exp (-c ‖x‖)` for some `c > 0` lies in
`realSobolevFunctions E s p` at every real order `s`. -/
theorem mem_realSobolevFunctions_of_norm_iteratedFDeriv_le_mul_exp {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ n : ℕ, ∃ K, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ K * Real.exp (-(c * ‖x‖)))
    (s : ℝ) : f ∈ realSobolevFunctions E s p :=
  (SchwartzMap.ofNormIteratedFDerivLeMulExp hf hc hbound).coe_mem_realSobolevFunctions s p

end TemperedDistribution

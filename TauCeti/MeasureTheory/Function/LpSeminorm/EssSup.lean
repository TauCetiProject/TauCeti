/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Essential bounds from `Lᵖ` bounds as `p → ∞`

If `‖f‖_{L^{pₖ}(μ)} ≤ V^{1/pₖ} M` along a sequence of exponents `pₖ → ∞`, with `V` finite, then
`‖f‖ ≤ M` almost everywhere (`TauCeti.ae_enorm_le_of_eLpNorm_le_rpow_inv_mul`). For a finite
measure and `V = μ univ` this is the familiar statement that `‖f‖_∞ ≤ M` whenever the normalized
norms `(⨍ ‖f‖^{pₖ})^{1/pₖ}` are at most `M`. No measurability of `f` and no finiteness of `μ` are
needed: by Chebyshev's inequality the set `{t ≤ ‖f‖}` has measure at most `V (M / t)^{pₖ}`, which
tends to `0` for every `t > M`.

This is the last step of Moser's iteration, which bounds the `L^{pₖ}` norms of a function on a
shrinking sequence of balls with `pₖ` growing geometrically, uniformly in `k`, and concludes a
bound for its essential supremum on the limiting ball.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

variable {α ε : Type*} {m0 : MeasurableSpace α} [TopologicalSpace ε] [ContinuousENorm ε]
  {μ : Measure α}

/-- For `t > M`, the set `{t ≤ ‖f‖}` is null as soon as `‖f‖_{L^{pₖ}} ≤ V^{1/pₖ} M` along a
sequence of exponents `pₖ → ∞`, with `V` finite. -/
private theorem measure_setOf_le_enorm_eq_zero {f : α → ε} {p : ℕ → ℝ≥0∞}
    (hp0 : ∀ k, p k ≠ 0) (hptop : ∀ k, p k ≠ ∞) (hp : Tendsto (fun k => (p k).toReal) atTop atTop)
    {V M t : ℝ≥0∞} (hV : V ≠ ∞) (hMt : M < t) (ht : t ≠ ∞)
    (h : ∀ k, eLpNorm f (p k) μ ≤ V ^ (p k).toReal⁻¹ * M) :
    μ {x | t ≤ ‖f x‖ₑ} = 0 := by
  have ht0 : t ≠ 0 := (zero_le.trans_lt hMt).ne'
  have hM : M ≠ ∞ := (hMt.trans_le le_top).ne
  set r : ℝ := M.toReal / t.toReal
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 :=
    (div_lt_one (ENNReal.toReal_pos ht0 ht)).2 ((ENNReal.toReal_lt_toReal hM ht).2 hMt)
  -- Chebyshev's inequality at each exponent: `μ {t ≤ ‖f‖} ≤ V r^{pₖ}`.
  have hbound : ∀ k, μ {x | t ≤ ‖f x‖ₑ} ≤ V * ENNReal.ofReal (r ^ (p k).toReal) := by
    intro k
    have hpk : 0 < (p k).toReal := ENNReal.toReal_pos (hp0 k) (hptop k)
    have hcheb := mul_meas_ge_le_pow_eLpNorm' μ (hp0 k) (hptop k) t (f := f)
    have hpow : eLpNorm f (p k) μ ^ (p k).toReal ≤ V * M ^ (p k).toReal := by
      calc eLpNorm f (p k) μ ^ (p k).toReal ≤ (V ^ (p k).toReal⁻¹ * M) ^ (p k).toReal := by
            gcongr
            exact h k
        _ = V * M ^ (p k).toReal := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hpk.le, ← ENNReal.rpow_mul,
              inv_mul_cancel₀ hpk.ne', ENNReal.rpow_one]
    have htpos : t ^ (p k).toReal ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 ht0) ht).ne'
    have httop : t ^ (p k).toReal ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hpk.le ht
    calc μ {x | t ≤ ‖f x‖ₑ} = (t ^ (p k).toReal)⁻¹ * (t ^ (p k).toReal * μ {x | t ≤ ‖f x‖ₑ}) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel htpos httop, one_mul]
      _ ≤ (t ^ (p k).toReal)⁻¹ * (V * M ^ (p k).toReal) := mul_le_mul_right (hcheb.trans hpow) _
      _ = V * ENNReal.ofReal (r ^ (p k).toReal) := by
          rw [mul_left_comm, ← ENNReal.div_eq_inv_mul, ← ENNReal.div_rpow_of_nonneg _ _ hpk.le,
            ← ENNReal.ofReal_toReal (ENNReal.div_ne_top hM ht0), ENNReal.toReal_div,
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hpk.le]
  -- The right side tends to `0`, since `r < 1` and `pₖ → ∞`.
  have hlim : Tendsto (fun k => V * ENNReal.ofReal (r ^ (p k).toReal)) atTop (𝓝 0) := by
    have hreal : Tendsto (fun k => r ^ (p k).toReal) atTop (𝓝 0) :=
      (tendsto_rpow_atTop_of_base_lt_one r (by linarith) hr1).comp hp
    have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hreal) (Or.inr hV)
    rwa [ENNReal.ofReal_zero, mul_zero] at this
  exact le_antisymm (ge_of_tendsto' hlim hbound) zero_le

/-- **An essential bound from `Lᵖ` bounds as `p → ∞`.** If `‖f‖_{L^{pₖ}(μ)} ≤ V^{1/pₖ} M` for a
sequence of exponents `0 < pₖ < ∞` tending to infinity, with `V` finite, then `‖f‖ ≤ M` almost
everywhere. -/
theorem ae_enorm_le_of_eLpNorm_le_rpow_inv_mul {f : α → ε} {p : ℕ → ℝ≥0∞}
    (hp0 : ∀ k, p k ≠ 0) (hptop : ∀ k, p k ≠ ∞) (hp : Tendsto (fun k => (p k).toReal) atTop atTop)
    {V M : ℝ≥0∞} (hV : V ≠ ∞) (h : ∀ k, eLpNorm f (p k) μ ≤ V ^ (p k).toReal⁻¹ * M) :
    ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ M := by
  rcases eq_or_ne M ∞ with rfl | hM
  · exact Eventually.of_forall fun _ => le_top
  -- `{M < ‖f‖}` is the union of the null sets `{M + (n + 1)⁻¹ ≤ ‖f‖}`.
  have hnull : ∀ n : ℕ, μ {x | M + ((n : ℝ≥0∞) + 1)⁻¹ ≤ ‖f x‖ₑ} = 0 := fun n =>
    measure_setOf_le_enorm_eq_zero hp0 hptop hp hV
      (ENNReal.lt_add_right hM (ENNReal.inv_ne_zero.2 (by simp)))
      (ENNReal.add_ne_top.2 ⟨hM, by simp⟩) h
  refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null hnull)
  rw [Set.mem_compl_iff, Set.mem_ofPred, not_le] at hx
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (tsub_pos_of_lt hx).ne'
  refine Set.mem_iUnion.2 ⟨n, ?_⟩
  have hn' : ((n : ℝ≥0∞) + 1)⁻¹ ≤ ‖f x‖ₑ - M :=
    (ENNReal.inv_le_inv.2 le_self_add).trans hn.le
  exact (add_le_of_le_tsub_left_of_le hx.le hn')

end TauCeti

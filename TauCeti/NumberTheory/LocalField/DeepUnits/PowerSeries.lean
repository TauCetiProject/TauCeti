/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.DeepUnits.Basic
public import TauCeti.RingTheory.PowerSeries.EvalAt

/-!
# Power series interpolating powers of deep units

For a finite extension `K` of `ℚ_[p]`, let `u ∈ U(K,i)` with `e < (p - 1) * i`.
The formal series `rescale (log u) (PowerSeries.exp K)` has coefficients `(log u)^n / n!`.
This file proves that it converges at every integral argument `z` to `exp (z * log u)`,
and at each integer `b` to `u^b`. Thus integer powers admit a single convergent expansion,
including negative powers, rather than unrelated expansions for each exponent.

Its coefficients have the exact valuation `n v_K(u - 1) - e v_p(n!)` for `u ≠ 1`.
When `K` carries a norm inducing its given topology, this series is restricted at radius `1`.
Consequently the Taylor, Hasse derivative and finite-difference calculus for restricted series
applies to it. No normalization of that norm is assumed: the restriction to integral arguments
uses the valuation ring, whereas restrictedness is a statement about coefficient convergence.

## References

* K. Yu, *Linear forms in p-adic logarithms. II*, Compositio Math. 74 (1990), 15–113, §1.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section

open Filter Topology ValuativeRel IsNonarchimedeanLocalField NormedSpace

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {p : ℕ} [Fact p.Prime] [FinitePadicExtension K p] {i : ℕ}

/-- At every integral argument, the normal series of a deep unit sums to `exp (z * log u)`. -/
theorem hasSum_coeff_rescale_log_exp
    (hi : absoluteRamificationIndex K p < (p - 1) * i)
    {u : Kˣ} (hu : u ∈ unitFiltration K i) (z : 𝒪[K]) :
    letI := FinitePadicExtension.charZero K p
    HasSum (fun n => (PowerSeries.rescale (log (u : K)) (PowerSeries.exp K)).coeff n * (z : K) ^ n)
      (exp ((z : K) * log (u : K))) := by
  have := FinitePadicExtension.charZero K p
  obtain ⟨x, hx, hxu⟩ := exists_mem_maximalIdeal_pow_eq_log hi hu
  simpa only [← hxu] using hasSum_coeff_rescale_exp_of_mem_maximalIdeal_pow hi ⟨x, hx⟩ z

/-- At every integer argument, the normal series of a deep unit sums to its integer power. -/
theorem hasSum_coeff_rescale_log_exp_intCast
    (hi : absoluteRamificationIndex K p < (p - 1) * i)
    {u : Kˣ} (hu : u ∈ unitFiltration K i) (b : ℤ) :
    letI := FinitePadicExtension.charZero K p
    HasSum (fun n => (PowerSeries.rescale (log (u : K)) (PowerSeries.exp K)).coeff n * (b : K) ^ n)
      ((u : K) ^ b) := by
  have := FinitePadicExtension.charZero K p
  obtain ⟨x, hx, hxu⟩ := exists_mem_maximalIdeal_pow_eq_log hi hu
  have hexp := exp_zsmul_of_mem_maximalIdeal_pow hi (⟨x, hx⟩ : (𝓂[K] ^ i : Ideal 𝒪[K])) b
  rw [hxu, exp_log_of_mem_unitFiltration hi hu, zsmul_eq_mul] at hexp
  simpa only [Subring.coe_intCast, hexp] using hasSum_coeff_rescale_log_exp hi hu (b : 𝒪[K])

/-- Evaluating the normal series of a deep unit at an integral point gives its exponential. -/
theorem evalAt_rescale_log_exp
    (hi : absoluteRamificationIndex K p < (p - 1) * i)
    {u : Kˣ} (hu : u ∈ unitFiltration K i) (z : 𝒪[K]) :
    letI := FinitePadicExtension.charZero K p
    (PowerSeries.rescale (log (u : K)) (PowerSeries.exp K)).evalAt (z : K) =
      exp ((z : K) * log (u : K)) := by
  have := FinitePadicExtension.charZero K p
  simpa only [PowerSeries.evalAt_def, smul_eq_mul] using
    (hasSum_coeff_rescale_log_exp hi hu z).tsum_eq

/-- Evaluating the normal series of a deep unit at an integer gives its integer power. -/
theorem evalAt_rescale_log_exp_intCast
    (hi : absoluteRamificationIndex K p < (p - 1) * i)
    {u : Kˣ} (hu : u ∈ unitFiltration K i) (b : ℤ) :
    letI := FinitePadicExtension.charZero K p
    (PowerSeries.rescale (log (u : K)) (PowerSeries.exp K)).evalAt (b : K) = (u : K) ^ b := by
  have := FinitePadicExtension.charZero K p
  simpa only [PowerSeries.evalAt_def, smul_eq_mul] using
    (hasSum_coeff_rescale_log_exp_intCast hi hu b).tsum_eq

/-- The coefficients interpolating a nontrivial deep unit have valuation
`n v_K(u - 1) - e v_p(n!)`. In particular the ramification factor is retained in their
factorial denominators. -/
theorem log_normalizedValuationWithZero_coeff_rescale_log_exp
    (hi : absoluteRamificationIndex K p < (p - 1) * i)
    {u : Kˣ} (hu : u ∈ unitFiltration K i) (hu1 : u ≠ 1) (n : ℕ) :
    letI := FinitePadicExtension.charZero K p
    WithZero.log (normalizedValuationWithZero K
        ((PowerSeries.rescale (log (u : K)) (PowerSeries.exp K)).coeff n)) =
      (n : ℤ) * WithZero.log (normalizedValuationWithZero K ((u : K) - 1)) -
        absoluteRamificationIndex K p * padicValNat p n.factorial := by
  have := FinitePadicExtension.charZero K p
  have hsub : (u : K) - 1 ≠ 0 := sub_ne_zero.mpr (by simpa using hu1)
  have hlog : log (u : K) ≠ 0 := by
    intro h
    have hval := valuation_log hi hu
    rw [h, map_zero] at hval
    exact hsub ((Valuation.zero_iff _).mp hval.symm)
  have hv := (toAdd_normalizedValuation_eq_iff_valuation_eq
    (Units.mk0 (log (u : K)) hlog) (Units.mk0 ((u : K) - 1) hsub)).mpr
      (valuation_log hi hu)
  have hlogs : WithZero.log (normalizedValuationWithZero K (log (u : K))) =
      WithZero.log (normalizedValuationWithZero K ((u : K) - 1)) := by
    calc
      _ = (normalizedValuation K (Units.mk0 (log (u : K)) hlog)).toAdd :=
        congrArg WithZero.log (normalizedValuationWithZero_coe _)
      _ = _ := hv
      _ = _ := (congrArg WithZero.log (normalizedValuationWithZero_coe _)).symm
  rw [log_normalizedValuationWithZero_coeff_rescale_exp (p := p) hlog n, hlogs]

end TauCeti

namespace TauCeti

variable {K : Type*} [NormedField K] [ValuativeRel K] [IsNonarchimedeanLocalField K]
variable {p : ℕ} [Fact p.Prime] [FinitePadicExtension K p] {i : ℕ}

/-- The power series interpolating powers of a deep unit is restricted at radius `1`.
This makes the restricted Taylor and finite-difference calculus available for integer powers. -/
theorem isRestricted_rescale_log_exp
    (hi : absoluteRamificationIndex K p < (p - 1) * i)
    {u : Kˣ} (hu : u ∈ unitFiltration K i) :
    letI := FinitePadicExtension.charZero K p
    (PowerSeries.rescale (log (u : K)) (PowerSeries.exp K)).IsRestricted 1 := by
  have := FinitePadicExtension.charZero K p
  obtain ⟨x, hx, hxu⟩ := exists_mem_maximalIdeal_pow_eq_log hi hu
  simpa only [← hxu] using isRestricted_rescale_exp_of_mem_maximalIdeal_pow hi ⟨x, hx⟩

end TauCeti

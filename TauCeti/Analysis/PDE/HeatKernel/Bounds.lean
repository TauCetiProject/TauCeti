/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import TauCeti.Analysis.PDE.HeatKernel.Basic

/-!
# Gaussian bounds for the heat kernel and its derivatives

On a finite-dimensional real inner product space `E` of dimension `n`, the heat kernel
`K_t(x) = (4πt)^(-n/2) exp(-‖x‖² / (4t))` is controlled by the heat kernel at a later time:
trading time for decay absorbs polynomial weights and translations. This file records the bounds
used to differentiate heat convolutions under the integral sign:

* the comparison `K_s ≤ (s' / s)^(n/2) K_{s'}` for `0 < s ≤ s'`;
* translations: `K_t(z + h) ≤ 2^(n/2) exp(‖h‖² / (4t)) K_{2t}(z)`;
* polynomial weights: `(1 + ‖x‖)^m K_t(x) ≤ C K_{2t}(x)`;
* derivatives of every order: `‖D^k K_t(x)‖ ≤ C K_{2t}(x)`, so that each derivative is
  dominated, uniformly on unit translates, by an integrable function.

The derivative bound comes from Mathlib's Faà di Bruno estimate
`norm_iteratedFDeriv_comp_le` for `exp ∘ (-‖·‖² / (4t))`, together with the temperate growth of
`‖·‖²`.

## Main declarations

* `TauCeti.heatKernel_le_mul_heatKernel`: comparison of heat kernels at two times.
* `TauCeti.heatKernel_eq_mul_heatKernel_two_mul`: `K_t = 2^(n/2) exp(-‖x‖² / (8t)) K_{2t}`.
* `TauCeti.heatKernel_add_le`: the translation bound.
* `TauCeti.exists_one_add_norm_pow_mul_heatKernel_le`: polynomial weights.
* `TauCeti.exists_norm_iteratedFDeriv_heatKernel_le`: Gaussian bounds on all derivatives.
* `TauCeti.exists_integrable_norm_iteratedFDeriv_heatKernel_add_le`: integrable domination of the
  derivatives on unit translates.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Module Real
open scoped Nat

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The normalizing constant of the heat kernel at time `t` is `2^(n/2)` times the one at time
`2t`. -/
private theorem rpow_heatKernel_const_eq {t : ℝ} (ht : 0 < t) :
    (4 * π * t) ^ (-(finrank ℝ E : ℝ) / 2) =
      2 ^ ((finrank ℝ E : ℝ) / 2) * (4 * π * (2 * t)) ^ (-(finrank ℝ E : ℝ) / 2) := by
  rw [show 4 * π * (2 * t) = 2 * (4 * π * t) by ring,
    mul_rpow (x := 2) (y := 4 * π * t) (by norm_num) (by positivity), ← mul_assoc,
    ← rpow_add (by norm_num)]
  simp [neg_div]

/-- **Comparison of heat kernels.** For `0 < s ≤ s'`, `K_s ≤ (s' / s)^(n/2) K_{s'}`. -/
theorem heatKernel_le_mul_heatKernel {s s' : ℝ} (hs : 0 < s) (hss' : s ≤ s') (x : E) :
    heatKernel s x ≤ (s' / s) ^ ((finrank ℝ E : ℝ) / 2) * heatKernel s' x := by
  have hs' : 0 < s' := hs.trans_le hss'
  have hc : (4 * π * s) ^ (-(finrank ℝ E : ℝ) / 2) =
      (s' / s) ^ ((finrank ℝ E : ℝ) / 2) * (4 * π * s') ^ (-(finrank ℝ E : ℝ) / 2) := by
    rw [show 4 * π * s' = s' / s * (4 * π * s) by field_simp,
      mul_rpow (x := s' / s) (y := 4 * π * s) (by positivity) (by positivity), ← mul_assoc,
      ← rpow_add (by positivity)]
    simp [neg_div]
  have hexp : -‖x‖ ^ 2 / (4 * s) ≤ -‖x‖ ^ 2 / (4 * s') := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
  rw [heatKernel_apply, heatKernel_apply, hc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (exp_le_exp.2 hexp) (by positivity))
    (by positivity)

/-- The heat kernel at time `t` is the heat kernel at time `2t` times a Gaussian factor:
`K_t(x) = 2^(n/2) exp(-‖x‖² / (8t)) K_{2t}(x)`. -/
theorem heatKernel_eq_mul_heatKernel_two_mul {t : ℝ} (ht : 0 < t) (x : E) :
    heatKernel t x =
      2 ^ ((finrank ℝ E : ℝ) / 2) * exp (-‖x‖ ^ 2 / (8 * t)) * heatKernel (2 * t) x := by
  rw [heatKernel_apply, heatKernel_apply, rpow_heatKernel_const_eq ht,
    show -‖x‖ ^ 2 / (4 * t) = -‖x‖ ^ 2 / (8 * t) + -‖x‖ ^ 2 / (4 * (2 * t)) by field_simp; ring,
    exp_add]
  ring

/-- **Translating the heat kernel.** `K_t(z + h) ≤ 2^(n/2) exp(‖h‖² / (4t)) K_{2t}(z)`: a
translate of the heat kernel is dominated by the heat kernel at twice the time. -/
theorem heatKernel_add_le {t : ℝ} (ht : 0 < t) (z h : E) :
    heatKernel t (z + h) ≤
      2 ^ ((finrank ℝ E : ℝ) / 2) * exp (‖h‖ ^ 2 / (4 * t)) * heatKernel (2 * t) z := by
  -- `‖z‖² ≤ 2‖z + h‖² + 2‖h‖²` trades the translation for a slower Gaussian.
  have hz : ‖z‖ ^ 2 ≤ 2 * ‖z + h‖ ^ 2 + 2 * ‖h‖ ^ 2 := by
    have h1 : ‖z‖ ≤ ‖z + h‖ + ‖h‖ := by simpa using norm_sub_le (z + h) h
    nlinarith [sq_nonneg (‖z + h‖ - ‖h‖), mul_le_mul h1 h1 (norm_nonneg _) (by positivity)]
  have hexp : -‖z + h‖ ^ 2 / (4 * t) ≤ ‖h‖ ^ 2 / (4 * t) + -‖z‖ ^ 2 / (4 * (2 * t)) := by
    have : ‖h‖ ^ 2 / (4 * t) + -‖z‖ ^ 2 / (4 * (2 * t)) - -‖z + h‖ ^ 2 / (4 * t) =
        (2 * ‖z + h‖ ^ 2 + 2 * ‖h‖ ^ 2 - ‖z‖ ^ 2) / (8 * t) := by
      field_simp
      ring
    exact sub_nonneg.1 (this ▸ div_nonneg (by linarith) (by positivity))
  rw [heatKernel_apply, heatKernel_apply, rpow_heatKernel_const_eq ht]
  calc (2 : ℝ) ^ ((finrank ℝ E : ℝ) / 2) * (4 * π * (2 * t)) ^ (-(finrank ℝ E : ℝ) / 2) *
        exp (-‖z + h‖ ^ 2 / (4 * t))
      ≤ 2 ^ ((finrank ℝ E : ℝ) / 2) * (4 * π * (2 * t)) ^ (-(finrank ℝ E : ℝ) / 2) *
        (exp (‖h‖ ^ 2 / (4 * t)) * exp (-‖z‖ ^ 2 / (4 * (2 * t)))) := by
        rw [← exp_add]
        gcongr
    _ = _ := by ring

/-- **Polynomial weights.** For every `m`, `(1 + ‖x‖)^m K_t(x) ≤ C K_{2t}(x)` for some `C`. -/
theorem exists_one_add_norm_pow_mul_heatKernel_le {t : ℝ} (ht : 0 < t) (m : ℕ) :
    ∃ C, ∀ x : E, (1 + ‖x‖) ^ m * heatKernel t x ≤ C * heatKernel (2 * t) x := by
  refine ⟨2 ^ ((finrank ℝ E : ℝ) / 2) * (m ! * exp (1 + 2 * t)), fun x => ?_⟩
  set r := ‖x‖
  -- `(1 + r)^m ≤ m! exp(1 + r)` and `r - r² / (8t) ≤ 2t`.
  have hpow : (1 + r) ^ m ≤ m ! * exp (1 + r) := by
    have := pow_div_factorial_le_exp (1 + r) (by positivity) m
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have hquad : 1 + r + -r ^ 2 / (8 * t) ≤ 1 + 2 * t := by
    have : 1 + 2 * t - (1 + r + -r ^ 2 / (8 * t)) = (r - 4 * t) ^ 2 / (8 * t) := by
      field_simp
      ring
    exact sub_nonneg.1 (this ▸ div_nonneg (sq_nonneg _) (by positivity))
  have hK := (heatKernel_pos (E := E) (by positivity : 0 < 2 * t) x).le
  rw [heatKernel_eq_mul_heatKernel_two_mul ht]
  calc (1 + r) ^ m * (2 ^ ((finrank ℝ E : ℝ) / 2) * exp (-r ^ 2 / (8 * t)) * heatKernel (2 * t) x)
      = 2 ^ ((finrank ℝ E : ℝ) / 2) * ((1 + r) ^ m * exp (-r ^ 2 / (8 * t))) *
          heatKernel (2 * t) x := by ring
    _ ≤ 2 ^ ((finrank ℝ E : ℝ) / 2) * (m ! * exp (1 + 2 * t)) * heatKernel (2 * t) x := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by positivity)) hK
        calc (1 + r) ^ m * exp (-r ^ 2 / (8 * t)) ≤ m ! * exp (1 + r) * exp (-r ^ 2 / (8 * t)) := by
              gcongr
          _ = m ! * exp (1 + r + -r ^ 2 / (8 * t)) := by rw [exp_add (1 + r)]; ring
          _ ≤ m ! * exp (1 + 2 * t) := by gcongr

/-- **Gaussian bounds on the derivatives of the heat kernel.** For every order `k` there is a
constant `C` with `‖D^k K_t(x)‖ ≤ C K_{2t}(x)` for all `x`. -/
theorem exists_norm_iteratedFDeriv_heatKernel_le {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ∃ C, ∀ x : E, ‖iteratedFDeriv ℝ k (heatKernel t) x‖ ≤ C * heatKernel (2 * t) x := by
  set c : ℝ := (4 * π * t) ^ (-(finrank ℝ E : ℝ) / 2)
  set q : E → ℝ := fun x => -‖x‖ ^ 2 / (4 * t)
  have hKq : heatKernel t = c • (exp ∘ q) := funext fun x => by
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, q, c, heatKernel_apply]
  have hq : q.HasTemperateGrowth := by
    have : q = (fun _ => -(4 * t)⁻¹) * fun x : E => ‖x‖ ^ 2 :=
      funext fun x => by simp only [q, Pi.mul_apply]; ring
    rw [this]
    exact (Function.HasTemperateGrowth.const _).mul (Function.hasTemperateGrowth_norm_sq E)
  obtain ⟨j, C₀, hC₀, hj⟩ := hq.norm_iteratedFDeriv_le_uniform k
  obtain ⟨C₁, hC₁⟩ := exists_one_add_norm_pow_mul_heatKernel_le (E := E) ht (j * k)
  refine ⟨k ! * (1 + C₀) ^ k * C₁, fun x => ?_⟩
  -- Faà di Bruno: `‖D^k (exp ∘ q)(x)‖ ≤ k! exp(q x) D^k` with `D = (1 + C₀)(1 + ‖x‖)^j`.
  set D : ℝ := (1 + C₀) * (1 + ‖x‖) ^ j
  have hD₁ : 1 ≤ D := one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by simp))
  have hcomp : ‖iteratedFDeriv ℝ k (exp ∘ q) x‖ ≤ k ! * exp (q x) * D ^ k := by
    refine norm_iteratedFDeriv_comp_le contDiff_exp hq.1 (by exact_mod_cast le_top) x
      (fun i _ => ?_) (fun i hi hik => ?_)
    · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_exp,
        norm_of_nonneg (exp_pos _).le]
    · exact (hj i hik x).trans ((mul_le_mul_of_nonneg_right (by linarith) (by positivity) :
        C₀ * (1 + ‖x‖) ^ j ≤ D).trans (le_self_pow₀ hD₁ (by omega)))
  rw [hKq, iteratedFDeriv_const_smul_apply ((contDiff_exp.comp hq.1).contDiffAt.of_le
    (by exact_mod_cast le_top)), norm_smul, norm_of_nonneg (by positivity)]
  calc c * ‖iteratedFDeriv ℝ k (exp ∘ q) x‖ ≤ c * (k ! * exp (q x) * D ^ k) := by gcongr
    _ = k ! * (1 + C₀) ^ k * ((1 + ‖x‖) ^ (j * k) * heatKernel t x) := by
        rw [heatKernel_apply, pow_mul]
        simp only [D, q, c, mul_pow]
        ring
    _ ≤ k ! * (1 + C₀) ^ k * (C₁ * heatKernel (2 * t) x) :=
        mul_le_mul_of_nonneg_left (hC₁ x) (by positivity)
    _ = k ! * (1 + C₀) ^ k * C₁ * heatKernel (2 * t) x := by ring

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every derivative of the heat kernel is dominated, uniformly on unit translates, by an
integrable function (a multiple of `K_{4t}`). -/
theorem exists_integrable_norm_iteratedFDeriv_heatKernel_add_le {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ∃ w : E → ℝ, Integrable w ∧
      ∀ z h, ‖h‖ ≤ 1 → ‖iteratedFDeriv ℝ k (heatKernel t) (z + h)‖ ≤ w z := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_heatKernel_le (E := E) ht k
  have h2t : 0 < 2 * t := by positivity
  have hC₀ : 0 ≤ C := (mul_nonneg_iff_of_pos_right (heatKernel_pos (E := E) h2t 0)).1
    ((norm_nonneg _).trans (hC 0))
  refine ⟨fun z => C * (2 ^ ((finrank ℝ E : ℝ) / 2) * exp (1 / (4 * (2 * t)))) *
    heatKernel (2 * (2 * t)) z, (integrable_heatKernel (by positivity)).const_mul _,
    fun z h hh => (hC (z + h)).trans ?_⟩
  calc C * heatKernel (2 * t) (z + h)
      ≤ C * (2 ^ ((finrank ℝ E : ℝ) / 2) * exp (‖h‖ ^ 2 / (4 * (2 * t))) *
          heatKernel (2 * (2 * t)) z) := by gcongr; exact heatKernel_add_le h2t z h
    _ ≤ C * (2 ^ ((finrank ℝ E : ℝ) / 2) * exp (1 / (4 * (2 * t))) *
          heatKernel (2 * (2 * t)) z) := by
        gcongr
        · exact (heatKernel_pos (by positivity) z).le
        · exact pow_le_one₀ (norm_nonneg h) hh
    _ = _ := by ring

end TauCeti

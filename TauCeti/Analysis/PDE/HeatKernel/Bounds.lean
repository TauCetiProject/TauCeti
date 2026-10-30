/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import TauCeti.Analysis.PDE.HeatKernel.Basic
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.SpecialFunctions.Gaussian.Bounds

/-!
# Gaussian bounds for the heat kernel and its derivatives

On a finite-dimensional real inner product space `E` of dimension `n`, the heat kernel
`K_t(x) = (4πt)^(-n/2) exp(-‖x‖² / (4t))` is controlled by the heat kernel at a later time:
trading time for decay absorbs polynomial weights and translations. This file records the bounds
used to differentiate heat convolutions under the integral sign:

* the comparison `K_s ≤ (s' / s)^(n/2) K_{s'}` for `0 < s ≤ s'`;
* translations: `K_t(z + h) ≤ 2^(n/2) exp(‖h‖² / (4t)) K_{2t}(z)`;
* polynomial weights: `(1 + ‖x‖)^m K_t(x) ≤ C K_{2t}(x)` for some `C > 0`, and, for `α ≥ 0`,
  `‖x‖^α K_t(x) ≤ C t^(α / 2) K_{2t}(x)` with `C` independent of `t > 0`;
* derivatives of every order, against every polynomial weight:
  `(1 + ‖x‖)^p ‖D^k K_t(x)‖ ≤ C K_{2t}(x)` for some `C > 0`, so that each derivative is
  integrable and is dominated, uniformly on translates of any bounded radius, by an integrable
  function.

The derivative bound comes from Mathlib's Faà di Bruno estimate
`norm_iteratedFDeriv_comp_le` for `exp ∘ (-‖·‖² / (4t))`, together with the temperate growth of
`‖·‖²`.

## Main declarations

* `TauCeti.heatKernel_le_mul_heatKernel`: comparison of heat kernels at two times.
* `TauCeti.heatKernel_eq_mul_heatKernel_two_mul`: `K_t = 2^(n/2) exp(-‖x‖² / (8t)) K_{2t}`.
* `TauCeti.heatKernel_add_le`: the translation bound.
* `TauCeti.exists_one_add_norm_pow_mul_heatKernel_le`: polynomial weights.
* `TauCeti.exists_norm_rpow_mul_heatKernel_le`: absorbing the weight `‖x‖^α` into `K_{2t}`, with a
  constant independent of the time.
* `TauCeti.exists_one_add_norm_pow_mul_norm_iteratedFDeriv_heatKernel_le` and
  `TauCeti.exists_norm_iteratedFDeriv_heatKernel_le`: Gaussian bounds on all derivatives, with and
  without polynomial weights.
* `TauCeti.exists_integrable_norm_iteratedFDeriv_heatKernel_add_le`: integrable domination of the
  derivatives on translates of any bounded radius.
* `TauCeti.integrable_iteratedFDeriv_heatKernel`: every derivative is integrable.
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
    simpa [mul_add] using norm_sub_sq_le_two_mul z (0 : E) (-h)
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

/-- **Polynomial weights.** For every `m`, `(1 + ‖x‖)^m K_t(x) ≤ C K_{2t}(x)` for some
positive `C`. -/
theorem exists_one_add_norm_pow_mul_heatKernel_le {t : ℝ} (ht : 0 < t) (m : ℕ) :
    ∃ C > 0, ∀ x : E, (1 + ‖x‖) ^ m * heatKernel t x ≤ C * heatKernel (2 * t) x := by
  refine ⟨2 ^ ((finrank ℝ E : ℝ) / 2) * (m ! * exp (1 + 2 * t)), by positivity, fun x => ?_⟩
  have hK := (heatKernel_pos (E := E) (by positivity : 0 < 2 * t) x).le
  have hG : (1 + ‖x‖) ^ m * exp (-‖x‖ ^ 2 / (8 * t)) ≤ m ! * exp (1 + 2 * t) := by
    have h := one_add_pow_mul_exp_neg_mul_sq_le (a := (8 * t)⁻¹) (by positivity) m (norm_nonneg x)
    rwa [show (4 * (8 * t)⁻¹)⁻¹ = 2 * t by field_simp; ring, neg_mul, ← div_eq_inv_mul,
      ← neg_div] at h
  rw [heatKernel_eq_mul_heatKernel_two_mul ht]
  calc (1 + ‖x‖) ^ m *
        (2 ^ ((finrank ℝ E : ℝ) / 2) * exp (-‖x‖ ^ 2 / (8 * t)) * heatKernel (2 * t) x)
      = 2 ^ ((finrank ℝ E : ℝ) / 2) * ((1 + ‖x‖) ^ m * exp (-‖x‖ ^ 2 / (8 * t))) *
          heatKernel (2 * t) x := by ring
    _ ≤ 2 ^ ((finrank ℝ E : ℝ) / 2) * (m ! * exp (1 + 2 * t)) * heatKernel (2 * t) x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG (by positivity)) hK

/-- **Scale-invariant polynomial weights.** For `α ≥ 0` there is a constant `C > 0`, independent of
the time, with `‖x‖^α K_t(x) ≤ C t^(α/2) K_{2t}(x)` for all `t > 0` and all `x`. -/
theorem exists_norm_rpow_mul_heatKernel_le {α : ℝ} (hα : 0 ≤ α) :
    ∃ C > 0, ∀ t, 0 < t → ∀ x : E,
      ‖x‖ ^ α * heatKernel t x ≤ C * t ^ (α / 2) * heatKernel (2 * t) x := by
  obtain ⟨C, hC0, hC⟩ := exists_one_add_norm_pow_mul_heatKernel_le (E := E) one_pos ⌈α⌉₊
  simp only [mul_one] at hC
  refine ⟨C, hC0, fun t ht x => ?_⟩
  set y : E := (√t)⁻¹ • x
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hxα : ‖x‖ ^ α = t ^ (α / 2) * ‖y‖ ^ α := by
    have hx : ‖x‖ = √t * ‖y‖ := by
      rw [norm_smul, norm_inv, norm_of_nonneg (sqrt_nonneg t),
        mul_inv_cancel_left₀ (sqrt_pos.2 ht).ne']
    rw [hx, mul_rpow (sqrt_nonneg t) hy, rpow_div_two_eq_sqrt _ ht.le]
  have hyα : ‖y‖ ^ α ≤ (1 + ‖y‖) ^ ⌈α⌉₊ :=
    calc ‖y‖ ^ α ≤ (1 + ‖y‖) ^ α := rpow_le_rpow hy (by linarith) hα
      _ ≤ (1 + ‖y‖) ^ (⌈α⌉₊ : ℝ) := rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil α)
      _ = (1 + ‖y‖) ^ ⌈α⌉₊ := rpow_natCast _ _
  rw [heatKernel_eq_mul_heatKernel_one_smul ht, mul_comm 2 t,
    heatKernel_mul_eq_mul_heatKernel_smul ht two_pos, hxα]
  calc t ^ (α / 2) * ‖y‖ ^ α * ((√t)⁻¹ ^ finrank ℝ E * heatKernel 1 y)
      = t ^ (α / 2) * (√t)⁻¹ ^ finrank ℝ E * (‖y‖ ^ α * heatKernel 1 y) := by ring
    _ ≤ t ^ (α / 2) * (√t)⁻¹ ^ finrank ℝ E * ((1 + ‖y‖) ^ ⌈α⌉₊ * heatKernel 1 y) := by
        gcongr
        exact (heatKernel_pos one_pos y).le
    _ ≤ t ^ (α / 2) * (√t)⁻¹ ^ finrank ℝ E * (C * heatKernel 2 y) :=
        mul_le_mul_of_nonneg_left (hC y) (by positivity)
    _ = C * t ^ (α / 2) * ((√t)⁻¹ ^ finrank ℝ E * heatKernel 2 y) := by ring

/-- **Weighted Gaussian bounds on the derivatives of the heat kernel.** For every order `k` and
every weight exponent `p` there is a positive constant `C` with
`(1 + ‖x‖)^p ‖D^k K_t(x)‖ ≤ C K_{2t}(x)` for all `x`. -/
theorem exists_one_add_norm_pow_mul_norm_iteratedFDeriv_heatKernel_le {t : ℝ} (ht : 0 < t)
    (k p : ℕ) :
    ∃ C > 0, ∀ x : E,
      (1 + ‖x‖) ^ p * ‖iteratedFDeriv ℝ k (heatKernel t) x‖ ≤ C * heatKernel (2 * t) x := by
  set c : ℝ := (4 * π * t) ^ (-(finrank ℝ E : ℝ) / 2)
  set q : E → ℝ := fun x => -‖x‖ ^ 2 / (4 * t)
  have hKq : heatKernel t = c • (exp ∘ q) := funext fun x => by
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, q, c, heatKernel_apply]
  have hq : q.HasTemperateGrowth := by
    have : q = (fun _ => -(4 * t)⁻¹) * fun x : E => ‖x‖ ^ 2 :=
      funext fun x => by simp only [q, Pi.mul_apply]; ring
    rw [this]
    exact (Function.HasTemperateGrowth.const _).mul (Function.hasTemperateGrowth_norm_sq E)
  obtain ⟨j, C₀, hC₀, hcomp⟩ := hq.exists_norm_iteratedFDeriv_comp_le contDiff_exp k
  obtain ⟨C₁, hC₁₀, hC₁⟩ := exists_one_add_norm_pow_mul_heatKernel_le (E := E) ht (j * k + p)
  refine ⟨k ! * C₀ ^ k * C₁, by positivity, fun x => ?_⟩
  have hexp : ‖iteratedFDeriv ℝ k (exp ∘ q) x‖ ≤ k ! * exp (q x) * (C₀ * (1 + ‖x‖) ^ j) ^ k :=
    hcomp x _ fun i _ => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_exp,
        norm_of_nonneg (exp_pos _).le]
  rw [hKq, iteratedFDeriv_const_smul_apply ((contDiff_exp.comp hq.1).contDiffAt.of_le
    (by exact_mod_cast le_top)), norm_smul, norm_of_nonneg (by positivity)]
  calc (1 + ‖x‖) ^ p * (c * ‖iteratedFDeriv ℝ k (exp ∘ q) x‖)
      ≤ (1 + ‖x‖) ^ p * (c * (k ! * exp (q x) * (C₀ * (1 + ‖x‖) ^ j) ^ k)) := by gcongr
    _ = k ! * C₀ ^ k * ((1 + ‖x‖) ^ (j * k + p) * heatKernel t x) := by
        rw [heatKernel_apply, pow_add, pow_mul]
        simp only [q, c, mul_pow]
        ring
    _ ≤ k ! * C₀ ^ k * (C₁ * heatKernel (2 * t) x) :=
        mul_le_mul_of_nonneg_left (hC₁ x) (by positivity)
    _ = k ! * C₀ ^ k * C₁ * heatKernel (2 * t) x := by ring

/-- **Gaussian bounds on the derivatives of the heat kernel.** For every order `k` there is a
positive constant `C` with `‖D^k K_t(x)‖ ≤ C K_{2t}(x)` for all `x`. -/
theorem exists_norm_iteratedFDeriv_heatKernel_le {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ∃ C > 0, ∀ x : E, ‖iteratedFDeriv ℝ k (heatKernel t) x‖ ≤ C * heatKernel (2 * t) x := by
  simpa using exists_one_add_norm_pow_mul_norm_iteratedFDeriv_heatKernel_le (E := E) ht k 0

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every derivative of the heat kernel is dominated, uniformly on translates of norm at most
`R`, by an integrable function (a multiple of `K_{4t}`). -/
theorem exists_integrable_norm_iteratedFDeriv_heatKernel_add_le {t : ℝ} (ht : 0 < t) (k : ℕ)
    (R : ℝ) :
    ∃ w : E → ℝ, Integrable w ∧
      ∀ z h, ‖h‖ ≤ R → ‖iteratedFDeriv ℝ k (heatKernel t) (z + h)‖ ≤ w z := by
  obtain ⟨C, hC₀, hC⟩ := exists_norm_iteratedFDeriv_heatKernel_le (E := E) ht k
  have h2t : 0 < 2 * t := by positivity
  refine ⟨fun z => C * (2 ^ ((finrank ℝ E : ℝ) / 2) * exp (R ^ 2 / (4 * (2 * t)))) *
    heatKernel (2 * (2 * t)) z, (integrable_heatKernel (by positivity)).const_mul _,
    fun z h hh => (hC (z + h)).trans ?_⟩
  calc C * heatKernel (2 * t) (z + h)
      ≤ C * (2 ^ ((finrank ℝ E : ℝ) / 2) * exp (‖h‖ ^ 2 / (4 * (2 * t))) *
          heatKernel (2 * (2 * t)) z) := by gcongr; exact heatKernel_add_le h2t z h
    _ ≤ C * (2 ^ ((finrank ℝ E : ℝ) / 2) * exp (R ^ 2 / (4 * (2 * t))) *
          heatKernel (2 * (2 * t)) z) := by
        gcongr
        · exact (heatKernel_pos (by positivity) z).le
    _ = _ := by ring

/-- Every derivative of the heat kernel is integrable. -/
theorem integrable_iteratedFDeriv_heatKernel {t : ℝ} (ht : 0 < t) (m : ℕ) :
    Integrable (iteratedFDeriv ℝ m (heatKernel t : E → ℝ)) := by
  obtain ⟨C, -, hC⟩ := exists_norm_iteratedFDeriv_heatKernel_le (E := E) ht m
  exact ((integrable_heatKernel (by positivity : 0 < 2 * t)).const_mul C).mono'
    ((contDiff_heatKernel t).continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).aestronglyMeasurable (Filter.Eventually.of_forall hC)

end TauCeti

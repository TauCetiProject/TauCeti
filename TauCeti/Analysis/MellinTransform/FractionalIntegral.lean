/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MellinTransform.Continued
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
import TauCeti.Analysis.SpecialFunctions.Beta.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.MeasureTheory.Integral.Asymptotics
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.MeasureTheory.Integral.IntervalIntegral.PowerBounds
import TauCeti.MeasureTheory.Integral.Prod
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# Expansion of fractional integrals (DLMF 2.6.45, 2.6.47)

The Riemann–Liouville fractional integral of order `μ > 0` is
`I^μ f(x) = Γ(μ)⁻¹ ∫₀^x (x - t)^(μ - 1) f(t) dt` (DLMF 2.6.33). Let `f` be locally integrable on
`[0, ∞)` and continuous on `(0, ∞)`, with an expansion at `+∞`
`f(t) = ∑_{k<n} a_k t^{-k-α} + f_n(t)`, `f_n(t) = O(t^{-n-α})`, where `0 < α < 1`. Then for every
`x > 0` (DLMF 2.6.45)

`I^μ f(x) = ∑_{s<n} a_s Γ(1 - s - α) / Γ(μ + 1 - s - α) x^(μ - s - α)
  - ∑_{s=1}^n c_s / Γ(μ + 1 - s) x^(μ - s) + x⁻ⁿ δ_n(x)`,

`δ_n(x) = ∑_{j ≤ n} C(n, j) Γ(μ + 1) / Γ(μ + 1 - j) I^μ(t^(n - j) f_{n,j})(x)` (DLMF 2.6.47),

where `f_{n,j}` is the `j`-th repeated integral of `f_n` from `+∞` and
`(s - 1)! c_s = (-1)^s 𝓜f(s)`, with `𝓜f = mellinContAtTop f a (k ↦ k + α) n` the Mellin transform
of `f` continued through the first `n` terms of the expansion (DLMF 2.5.28), as for the Stieltjes
transform (`TauCeti.stieltjes_eq`). The first sum comes from termwise integration of the
expansion of `f`, with the Beta integrals continued past their poles; the second is the part that
termwise integration misses.

The case `α = 1` (DLMF 2.6.46), where logarithms appear, is not treated here.

## Main definitions

* `TauCeti.fractionalIntegral`: the Riemann–Liouville fractional integral `I^μ`.
* `TauCeti.repeatedIntegralAtTop`: the repeated integrals `g_j` of `g` from `+∞`, with
  `g_j' = g_{j-1}` (DLMF 2.6.15).

## Main results

* `TauCeti.fractionalIntegral_eq`: the exact identity DLMF 2.6.45 for every `x > 0`.
* `TauCeti.intervalIntegrable_rpow_sub_smul_pow_smul_repeatedIntegralAtTop`, with
  `TauCeti.intervalIntegrable_rpow_sub_smul_of_continuousOn` from
  `TauCeti.MeasureTheory.Integral.IntervalIntegral.PowerBounds`: the integrals in it converge
  absolutely.
* `TauCeti.sum_choose_mul_descPochhammer_smul_fractionalIntegral_succ`: integration by parts along
  a chain of antiderivatives, `δ_{n+1}(x) = x δ_n(x)` plus a boundary term at `0`.
* `TauCeti.repeatedIntegralAtTop_succ_eq_neg_integral`, `TauCeti.hasDerivAt_repeatedIntegralAtTop`:
  Cauchy's formula for repeated integration from `+∞` and the derivatives of the repeated
  integrals.
  Cauchy's formula rests on the Fubini step `TauCeti.integral_Ioi_integral_Ioi_pow_smul` of
  `TauCeti.MeasureTheory.Integral.Prod`, and the repeated integrals of `f_n` converge by
  `TauCeti.integrableOn_Ioi_sub_pow_smul` of `TauCeti.MeasureTheory.Integral.Asymptotics`.
* `TauCeti.fractionalIntegral_rpow`: the Beta integral
  `I^μ(t^β)(x) = Γ(β + 1) / Γ(β + μ + 1) x^(β + μ)`.

## Implementation notes

DLMF derives 2.6.45 by convolving distributions. Here it is proved by induction on `n`, without
distributions. Formally `δ_n(x) = xⁿ (d/dx)ⁿ I^μ f_{n,n}(x)`, and the step from `n` to `n + 1` is
the identity `δ_{n+1} = x δ'_n + Γ(μ)⁻¹ (μ - 1)⋯(μ - n) x^μ f_{n+1,n+1}(0)`, where `δ'_n` is
`δ_n` built from the repeated integrals of `f_{n+1}` instead of `f_n`. It is proved by the
fundamental theorem of calculus for the explicit primitive
`W(t) = -(x - t)^μ ∑_{j ≤ n} C(n, j) (μ - 1)⋯(μ - j) t^(n - j) f_{n+1,j+1}(t)`. The boundary value
`f_{n+1,n+1}(0)` is `-n! c_{n+1}`, and the difference `δ'_n - δ_n` comes from the repeated
integrals of the single power `a_n t^{-n-α}`, which are powers again; they sum to the first term
through the Chu–Vandermonde identity for falling factorials. The falling factorials
`μ (μ - 1) ⋯ (μ - j + 1)` are `(descPochhammer ℝ j).eval μ`; in the statement they are written
`Γ(μ + 1) / Γ(μ + 1 - j)` as in DLMF.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.6(iii), equations (2.6.33)–(2.6.47),
  <https://dlmf.nist.gov/2.6.iii>.
-/

public section

open Filter Set MeasureTheory Asymptotics
open scoped Topology Nat

namespace TauCeti

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Fractional integrals and repeated integrals -/

/-- The Riemann–Liouville fractional integral of order `μ` (DLMF 2.6.33),
`I^μ g(x) = Γ(μ)⁻¹ ∫₀^x (x - t)^(μ - 1) g(t) dt`. -/
noncomputable def fractionalIntegral (μ : ℝ) (g : ℝ → E) (x : ℝ) : E :=
  (Real.Gamma μ)⁻¹ • ∫ t in (0 : ℝ)..x, (x - t) ^ (μ - 1) • g t

/-- The defining formula of `TauCeti.fractionalIntegral`. -/
theorem fractionalIntegral_def (μ : ℝ) (g : ℝ → E) (x : ℝ) :
    fractionalIntegral μ g x = (Real.Gamma μ)⁻¹ • ∫ t in (0 : ℝ)..x, (x - t) ^ (μ - 1) • g t :=
  (rfl)

/-- The `j`-th repeated integral of `g` from `+∞` (DLMF 2.6.15): `g` itself for `j = 0`, and
`(-1)^j / (j - 1)! ∫_t^∞ (τ - t)^(j - 1) g(τ) dτ` for `j ≥ 1`. Where the integrals converge, its
derivative is the repeated integral of order `j - 1` (`TauCeti.hasDerivAt_repeatedIntegralAtTop`),
and it is `-∫_t^∞` of that one (`TauCeti.repeatedIntegralAtTop_succ_eq_neg_integral`). -/
noncomputable def repeatedIntegralAtTop (g : ℝ → E) : ℕ → ℝ → E
  | 0 => g
  | j + 1 => fun t ↦ ((-1) ^ (j + 1) / (j ! : ℝ)) • ∫ τ in Ioi t, (τ - t) ^ j • g τ

/-- The repeated integral of order `0` is the function itself. -/
@[simp]
theorem repeatedIntegralAtTop_zero (g : ℝ → E) : repeatedIntegralAtTop g 0 = g :=
  (rfl)

/-- The defining formula of the repeated integral of order `j + 1`. -/
theorem repeatedIntegralAtTop_succ (g : ℝ → E) (j : ℕ) (t : ℝ) :
    repeatedIntegralAtTop g (j + 1) t =
      ((-1) ^ (j + 1) / (j ! : ℝ)) • ∫ τ in Ioi t, (τ - t) ^ j • g τ :=
  (rfl)

/-- The repeated integral of order `1` is `-∫_t^∞ g`. -/
theorem repeatedIntegralAtTop_one (g : ℝ → E) (t : ℝ) :
    repeatedIntegralAtTop g 1 t = -∫ τ in Ioi t, g τ := by
  simp [repeatedIntegralAtTop_succ]

/-- The repeated integrals commute with scalar multiplication. -/
theorem repeatedIntegralAtTop_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (c : 𝕜) (g : ℝ → E) (j : ℕ) (t : ℝ) :
    repeatedIntegralAtTop (fun τ ↦ c • g τ) j t = c • repeatedIntegralAtTop g j t := by
  cases j with
  | zero => rfl
  | succ j =>
    simp only [repeatedIntegralAtTop_succ, smul_comm _ c, integral_smul]

/-- The repeated integrals are additive on functions whose defining integrals converge. -/
theorem repeatedIntegralAtTop_sub {g₁ g₂ : ℝ → E} {t : ℝ} {j : ℕ}
    (h₁ : IntegrableOn (fun τ ↦ (τ - t) ^ j • g₁ τ) (Ioi t))
    (h₂ : IntegrableOn (fun τ ↦ (τ - t) ^ j • g₂ τ) (Ioi t)) :
    repeatedIntegralAtTop (fun τ ↦ g₁ τ - g₂ τ) (j + 1) t =
      repeatedIntegralAtTop g₁ (j + 1) t - repeatedIntegralAtTop g₂ (j + 1) t := by
  simp only [repeatedIntegralAtTop_succ, smul_sub, integral_sub h₁ h₂]

/-- If `(τ - t)^j g(τ)` is integrable on `(t, ∞)`, then the repeated integral of order `j` is
integrable on `(t, ∞)`. -/
theorem integrableOn_repeatedIntegralAtTop [CompleteSpace E] {g : ℝ → E} {t : ℝ} {j : ℕ}
    (hg : IntegrableOn (fun τ ↦ (τ - t) ^ j • g τ) (Ioi t)) :
    IntegrableOn (repeatedIntegralAtTop g j) (Ioi t) := by
  cases j with
  | zero => simpa using hg
  | succ j =>
    refine IntegrableOn.congr_fun ?_ (fun s _ ↦ (repeatedIntegralAtTop_succ g j s).symm)
      measurableSet_Ioi
    exact (integral_Ioi_integral_Ioi_pow_smul hg).1.smul _

/-- **Repeated integration** (Cauchy's formula, from `+∞`): if `(τ - t)^j g(τ)` is integrable on
`(t, ∞)`, then the repeated integral of order `j + 1` at `t` is `-∫_t^∞` of the one of order
`j`. -/
theorem repeatedIntegralAtTop_succ_eq_neg_integral [CompleteSpace E] {g : ℝ → E} {t : ℝ} {j : ℕ}
    (hg : IntegrableOn (fun τ ↦ (τ - t) ^ j • g τ) (Ioi t)) :
    repeatedIntegralAtTop g (j + 1) t = -∫ s in Ioi t, repeatedIntegralAtTop g j s := by
  cases j with
  | zero => exact repeatedIntegralAtTop_one g t
  | succ j =>
    simp_rw [repeatedIntegralAtTop_succ]
    rw [integral_smul, (integral_Ioi_integral_Ioi_pow_smul hg).2, smul_smul, ← neg_smul]
    congr 1
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    field_simp
    ring

/-- One step of `TauCeti.hasDerivAt_repeatedIntegralAtTop`: if the repeated integral of order `j`
is continuous on `(a, ∞)`, then the one of order `j + 1` has it as derivative there. -/
private theorem hasDerivAt_repeatedIntegralAtTop_of_continuousOn [CompleteSpace E] {g : ℝ → E}
    {a : ℝ} {j : ℕ} (hc : ContinuousOn (repeatedIntegralAtTop g j) (Ioi a))
    (hint : ∀ s, a < s → IntegrableOn (fun τ ↦ (τ - s) ^ j • g τ) (Ioi s)) {t : ℝ} (ht : a < t) :
    HasDerivAt (repeatedIntegralAtTop g (j + 1)) (repeatedIntegralAtTop g j t) t := by
  have heq : (fun s ↦ -∫ u in Ioi s, repeatedIntegralAtTop g j u) =ᶠ[𝓝 t]
      repeatedIntegralAtTop g (j + 1) := by
    filter_upwards [Ioi_mem_nhds ht] with s (hs : a < s)
    exact (repeatedIntegralAtTop_succ_eq_neg_integral (hint s hs)).symm
  have h := (hasDerivAt_integral_Ioi_of_continuousOn
    (fun s hs ↦ integrableOn_repeatedIntegralAtTop (hint s hs)) hc ht).neg
  rw [neg_neg] at h
  exact h.congr_of_eventuallyEq heq.symm

/-- The repeated integrals of `g` differentiate down the chain: if `g` is continuous on `(a, ∞)`
and every `(τ - s)^i g(τ)`, `i ≤ j`, is integrable on `(s, ∞)` for `s > a`, then the repeated
integral of order `j + 1` has derivative the one of order `j` at every `t > a`. -/
theorem hasDerivAt_repeatedIntegralAtTop [CompleteSpace E] {g : ℝ → E} {a : ℝ}
    (hcont : ContinuousOn g (Ioi a)) {j : ℕ}
    (hint : ∀ i ≤ j, ∀ s, a < s → IntegrableOn (fun τ ↦ (τ - s) ^ i • g τ) (Ioi s))
    {t : ℝ} (ht : a < t) :
    HasDerivAt (repeatedIntegralAtTop g (j + 1)) (repeatedIntegralAtTop g j t) t := by
  induction j generalizing t with
  | zero =>
    refine hasDerivAt_repeatedIntegralAtTop_of_continuousOn (j := 0) ?_ (hint 0 le_rfl) ht
    rwa [repeatedIntegralAtTop_zero]
  | succ j ih =>
    refine hasDerivAt_repeatedIntegralAtTop_of_continuousOn (fun s hs ↦ ?_) (hint _ le_rfl) ht
    exact (ih (fun i hi ↦ hint i (hi.trans j.le_succ)) hs).continuousAt.continuousWithinAt

/-- The repeated integral of order `j + 1`, multiplied by `t ^ k`, is continuous from the right at
`0` when `τ^(k + j) g(τ)` is integrable on `(0, ∞)`. Its value at `0` is
`0 ^ k (-1)^(j + 1) / j! ∫_0^∞ τ^j g(τ) dτ`, which is `0` for `k ≥ 1`. -/
theorem continuousWithinAt_pow_smul_repeatedIntegralAtTop {g : ℝ → E} {k j : ℕ}
    (hg : IntegrableOn (fun τ ↦ τ ^ (k + j) • g τ) (Ioi 0)) :
    ContinuousWithinAt (fun t ↦ t ^ k • repeatedIntegralAtTop g (j + 1) t) (Ici 0) 0 := by
  set F : ℝ → ℝ → E := fun t τ ↦ (Ioi t).indicator (fun τ ↦ (t ^ k * (τ - t) ^ j) • g τ) τ
  have hrepr : ∀ t ∈ Ici (0 : ℝ), t ^ k • repeatedIntegralAtTop g (j + 1) t =
      ((-1) ^ (j + 1) / (j ! : ℝ)) • ∫ τ in Ioi 0, F t τ := by
    intro t (ht : 0 ≤ t)
    rw [repeatedIntegralAtTop_succ, smul_comm, ← integral_smul,
      integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr (Ioi_subset_Ioi ht)]
    simp_rw [smul_smul]
  refine (ContinuousWithinAt.const_smul ?_ _).congr (fun t ht ↦ hrepr t ht)
    (hrepr 0 self_mem_Ici)
  have hgm := aestronglyMeasurable_of_integrableOn_pow_smul (t := 0) (by simpa using hg)
  refine continuousWithinAt_of_dominated (bound := fun τ ↦ ‖τ ^ (k + j) • g τ‖) ?_ ?_ hg.norm ?_
  · refine Eventually.of_forall fun t ↦ ?_
    exact (((by fun_prop : Continuous fun τ : ℝ ↦ t ^ k * (τ - t) ^ j).aestronglyMeasurable.smul
      hgm).indicator measurableSet_Ioi)
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 ≤ t)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ (hτ : 0 < τ)
    by_cases htτ : t < τ
    · simp only [F, indicator, mem_Ioi, htτ, ite_true, norm_smul, norm_mul, norm_pow,
        Real.norm_of_nonneg ht, Real.norm_of_nonneg (sub_pos.mpr htτ).le,
        Real.norm_of_nonneg hτ.le, pow_add]
      gcongr
      · linarith
    · simp [F, indicator, htτ]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ (hτ : 0 < τ)
    have hev : (fun t ↦ (t ^ k * (τ - t) ^ j) • g τ) =ᶠ[𝓝[Ici 0] 0] fun t ↦ F t τ := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hτ)] with t (ht : t < τ)
      simp [F, indicator, ht]
    refine (ContinuousWithinAt.congr_of_eventuallyEq ?_ hev.symm ?_)
    · exact (by fun_prop : Continuous fun t : ℝ ↦ (t ^ k * (τ - t) ^ j) • g τ).continuousWithinAt
    · simp [F, indicator, hτ]

/-! ### Integration by parts along a chain of antiderivatives -/

open Polynomial in
/-- The coefficient identity behind `TauCeti.sum_deriv_eq_sub_sum` at an index `k + 1 ≤ m`:
it combines `C(m + 1, k + 1) = C(m, k) + C(m, k + 1)`, `(m - k) C(m, k) = (k + 1) C(m, k + 1)` and
`μ^{(k+1)} = μ (μ - 1)^{(k)}`. -/
private theorem chain_coeff_eq {m k : ℕ} (hk : k < m) (μ x s u : ℝ) :
    (m.choose (k + 1) : ℝ) * eval (μ - 1) (descPochhammer ℝ (k + 1)) * ((x - s) * u) *
        s ^ (m - (k + 1)) +
      ((m.choose k : ℝ) * eval (μ - 1) (descPochhammer ℝ k) * ((x - s) * u) *
          (↑(m - k) * s ^ (m - k - 1)) -
        (m.choose k : ℝ) * eval (μ - 1) (descPochhammer ℝ k) * μ * u * s ^ (m - k)) =
    x * (↑(m.choose (k + 1)) * eval μ (descPochhammer ℝ (k + 1)) * (u * s ^ (m - (k + 1)))) -
      ↑((m + 1).choose (k + 1)) * eval μ (descPochhammer ℝ (k + 1)) *
        (u * s ^ (m + 1 - (k + 1))) := by
  obtain ⟨r, rfl⟩ : ∃ r, m = k + 1 + r := ⟨m - (k + 1), by omega⟩
  have e₁ : k + 1 + r - (k + 1) = r := by omega
  have e₂ : k + 1 + r - k = r + 1 := by omega
  have e₃ : k + 1 + r + 1 - (k + 1) = r + 1 := by omega
  rw [e₁, e₂, Nat.add_sub_cancel, e₃, Nat.choose_succ_succ']
  have hA := descPochhammer_succ_eval_add_one (R := ℝ) k (μ - 1)
  rw [sub_add_cancel] at hA
  rw [hA, descPochhammer_succ_eval]
  have h3 := Nat.choose_succ_right_eq (k + 1 + r) k
  rw [e₂] at h3
  have h3' : ((k + 1 + r).choose (k + 1) : ℝ) * (k + 1) = ((k + 1 + r).choose k : ℝ) * (r + 1) := by
    exact_mod_cast h3
  push_cast
  linear_combination (-(eval (μ - 1) (descPochhammer ℝ k)) * (x - s) * u * s ^ r) * h3'

open Polynomial in
/-- The pointwise identity behind
`TauCeti.sum_choose_mul_descPochhammer_smul_fractionalIntegral_succ`:
the derivative of `W(s) = -(x - s)^μ ∑_{j ≤ m} C(m, j) (μ - 1)^{(j)} s^(m - j) g_{j+1}`, with
`(x - s)^μ = (x - s) u` and `g_{j+1}' = g_j`, collected against the two sums of the identity. -/
private theorem sum_deriv_eq_sub_sum (m : ℕ) (μ x s u : ℝ) (g : ℕ → E) :
    (∑ j ∈ Finset.range (m + 1),
      (((m.choose j : ℝ) * (descPochhammer ℝ j).eval (μ - 1) * ((x - s) * u)) •
          (s ^ (m - j) • g j + (((m - j : ℕ) : ℝ) * s ^ (m - j - 1)) • g (j + 1)) +
        ((m.choose j : ℝ) * (descPochhammer ℝ j).eval (μ - 1) * (-1 * μ * u)) •
          (s ^ (m - j) • g (j + 1)))) =
      x • ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ) * (descPochhammer ℝ j).eval μ) •
          (u • s ^ (m - j) • g j) -
        ∑ j ∈ Finset.range (m + 2), (((m + 1).choose j : ℝ) * (descPochhammer ℝ j).eval μ) •
          (u • s ^ (m + 1 - j) • g j) := by
  set w : ℕ → ℝ := fun j ↦ (m.choose j : ℝ) * (descPochhammer ℝ j).eval (μ - 1) with hw
  -- normal form of the left side
  have hL : ∀ j ∈ Finset.range (m + 1),
      ((w j * ((x - s) * u)) •
          (s ^ (m - j) • g j + (((m - j : ℕ) : ℝ) * s ^ (m - j - 1)) • g (j + 1)) +
        (w j * (-1 * μ * u)) • (s ^ (m - j) • g (j + 1))) =
      (w j * ((x - s) * u) * s ^ (m - j)) • g j +
        (w j * ((x - s) * u) * (((m - j : ℕ) : ℝ) * s ^ (m - j - 1)) -
          w j * μ * u * s ^ (m - j)) • g (j + 1) := fun j _ ↦ by
    simp only [smul_add, smul_smul, sub_smul]
    module
  rw [Finset.sum_congr rfl hL, Finset.sum_add_distrib, Finset.sum_range_succ',
    Finset.sum_range_succ (fun j ↦ (_ : ℝ) • g (j + 1))]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_range_succ' _ m, Finset.sum_range_succ' _ (m + 1), Finset.sum_range_succ _ m]
  have hS : ∀ k ∈ Finset.range m,
      (w (k + 1) * ((x - s) * u) * s ^ (m - (k + 1))) • g (k + 1) +
        (w k * ((x - s) * u) * (↑(m - k) * s ^ (m - k - 1)) - w k * μ * u * s ^ (m - k)) •
          g (k + 1) =
      (x * (↑(m.choose (k + 1)) * eval μ (descPochhammer ℝ (k + 1)) * (u * s ^ (m - (k + 1))))) •
          g (k + 1) -
        (↑((m + 1).choose (k + 1)) * eval μ (descPochhammer ℝ (k + 1)) *
          (u * s ^ (m + 1 - (k + 1)))) • g (k + 1) := fun k hk ↦ by
    rw [← add_smul, ← sub_smul, chain_coeff_eq (Finset.mem_range.mp hk)]
  have hsum := Finset.sum_congr rfl hS
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  have h0 : (w 0 * ((x - s) * u) * s ^ (m - 0)) • g 0 =
      (x * (↑(m.choose 0) * eval μ (descPochhammer ℝ 0) * (u * s ^ (m - 0)))) • g 0 -
        (↑((m + 1).choose 0) * eval μ (descPochhammer ℝ 0) * (u * s ^ (m + 1 - 0))) • g 0 := by
    rw [← sub_smul]
    congr 1
    simp only [hw, Nat.choose_zero_right, descPochhammer_zero, eval_one, Nat.cast_one,
      Nat.sub_zero, pow_succ]
    ring
  have hm : (w m * ((x - s) * u) * (↑(m - m) * s ^ (m - m - 1)) - w m * μ * u * s ^ (m - m)) •
      g (m + 1) = -((↑((m + 1).choose (m + 1)) * eval μ (descPochhammer ℝ (m + 1)) *
        (u * s ^ (m + 1 - (m + 1)))) • g (m + 1)) := by
    rw [← neg_smul]
    congr 1
    have hA := descPochhammer_succ_eval_add_one (R := ℝ) m (μ - 1)
    rw [sub_add_cancel] at hA
    simp only [hw, Nat.choose_self, Nat.sub_self, pow_zero, hA]
    push_cast
    ring
  rw [h0, hm]
  linear_combination (norm := module) hsum
/-- The derivative of the primitive `W` in
`TauCeti.sum_choose_mul_descPochhammer_smul_fractionalIntegral_succ`. -/
private theorem hasDerivAt_neg_sum_rpow_sub_smul_pow_smul {μ x s : ℝ} (hs : s < x) {m : ℕ}
    {G : ℕ → ℝ → E} (hderiv : ∀ j ≤ m, HasDerivAt (G (j + 1)) (G j s) s) :
    HasDerivAt (fun s ↦ -∑ j ∈ Finset.range (m + 1),
        ((m.choose j : ℝ) * (descPochhammer ℝ j).eval (μ - 1) * (x - s) ^ μ) •
          (s ^ (m - j) • G (j + 1) s))
      (∑ j ∈ Finset.range (m + 2), (((m + 1).choose j : ℝ) * (descPochhammer ℝ j).eval μ) •
          ((x - s) ^ (μ - 1) • s ^ (m + 1 - j) • G j s) -
        x • ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ) * (descPochhammer ℝ j).eval μ) •
          ((x - s) ^ (μ - 1) • s ^ (m - j) • G j s)) s := by
  have hxs : 0 < x - s := sub_pos.mpr hs
  have h := (HasDerivAt.fun_sum (u := Finset.range (m + 1)) fun j hj ↦
    ((((hasDerivAt_id' s).const_sub x).rpow_const (p := μ) (Or.inl hxs.ne')).const_mul
      ((m.choose j : ℝ) * (descPochhammer ℝ j).eval (μ - 1))).fun_smul
      ((hasDerivAt_pow (m - j) s).fun_smul
        (hderiv j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))))).fun_neg
  convert h using 1
  have hv : (x - s) ^ μ = (x - s) * (x - s) ^ (μ - 1) := by
    rw [Real.rpow_sub_one hxs.ne', mul_div_cancel₀ _ hxs.ne']
  simp only [hv]
  rw [sum_deriv_eq_sub_sum m μ x s ((x - s) ^ (μ - 1)) (fun j ↦ G j s), neg_sub]

/-- **Integration by parts along a chain of antiderivatives.** Let `G 0, …, G (m + 1)` satisfy
`(G (j + 1))' = G j` on `(0, x)`, with every `t^(m - j) G (j + 1)(t)` continuous on `[0, x]`, and
let the fractional integrals below converge absolutely. Then, for `μ > 0`,

`∑_{j ≤ m+1} C(m+1, j) μ^{(j)} I^μ(t^(m+1-j) G_j)(x)
  = x ∑_{j ≤ m} C(m, j) μ^{(j)} I^μ(t^(m-j) G_j)(x) + Γ(μ)⁻¹ (μ - 1)^{(m)} x^μ G_{m+1}(0)`,

where `μ^{(j)} = μ (μ - 1) ⋯ (μ - j + 1)` is the falling factorial `(descPochhammer ℝ j).eval μ`.
Formally, both sums are `x^n (d/dx)^n I^μ G_n(x)` for `n = m + 1` and `n = m`. -/
theorem sum_choose_mul_descPochhammer_smul_fractionalIntegral_succ [CompleteSpace E] {μ x : ℝ}
    (hμ : 0 < μ) (hx : 0 < x) {m : ℕ} {G : ℕ → ℝ → E}
    (hderiv : ∀ j ≤ m, ∀ t ∈ Ioo 0 x, HasDerivAt (G (j + 1)) (G j t) t)
    (hcont : ∀ j ≤ m, ContinuousOn (fun t ↦ t ^ (m - j) • G (j + 1) t) (Icc 0 x))
    (hint₁ : ∀ j ≤ m + 1, IntervalIntegrable
      (fun t ↦ (x - t) ^ (μ - 1) • t ^ (m + 1 - j) • G j t) volume 0 x)
    (hint₂ : ∀ j ≤ m, IntervalIntegrable
      (fun t ↦ (x - t) ^ (μ - 1) • t ^ (m - j) • G j t) volume 0 x) :
    ∑ j ∈ Finset.range (m + 2), (((m + 1).choose j : ℝ) * (descPochhammer ℝ j).eval μ) •
        fractionalIntegral μ (fun t ↦ t ^ (m + 1 - j) • G j t) x =
      x • ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ) * (descPochhammer ℝ j).eval μ) •
          fractionalIntegral μ (fun t ↦ t ^ (m - j) • G j t) x +
        ((Real.Gamma μ)⁻¹ * (descPochhammer ℝ m).eval (μ - 1) * x ^ μ) • G (m + 1) 0 := by
  set w : ℕ → ℝ := fun j ↦ (m.choose j : ℝ) * (descPochhammer ℝ j).eval (μ - 1)
  set c₁ : ℕ → ℝ := fun j ↦ ((m + 1).choose j : ℝ) * (descPochhammer ℝ j).eval μ
  set c₂ : ℕ → ℝ := fun j ↦ (m.choose j : ℝ) * (descPochhammer ℝ j).eval μ
  -- `W' = D` on `(0, x)`
  set W : ℝ → E := fun s ↦
    -∑ j ∈ Finset.range (m + 1), (w j * (x - s) ^ μ) • (s ^ (m - j) • G (j + 1) s) with hW
  set D₁ : ℝ → E := fun s ↦ ∑ j ∈ Finset.range (m + 2),
    c₁ j • ((x - s) ^ (μ - 1) • s ^ (m + 1 - j) • G j s)
  set D₂ : ℝ → E := fun s ↦ ∑ j ∈ Finset.range (m + 1),
    c₂ j • ((x - s) ^ (μ - 1) • s ^ (m - j) • G j s)
  have hmem {j : ℕ} (hj : j ∈ Finset.range (m + 1)) : j ≤ m :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hWc : ContinuousOn W (Icc 0 x) := by
    refine (continuousOn_finsetSum _ fun j hj ↦ ?_).neg
    exact (continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).rpow_const
      fun _ _ ↦ Or.inr hμ.le)).smul (hcont j (hmem hj))
  have hWd : ∀ s ∈ Ioo 0 x, HasDerivAt W (D₁ s - x • D₂ s) s := fun s hs ↦
    hasDerivAt_neg_sum_rpow_sub_smul_pow_smul hs.2 fun j hj ↦ hderiv j hj s hs
  have hD₁' (j : ℕ) (hj : j ∈ Finset.range (m + 2)) : IntervalIntegrable
      (fun t ↦ c₁ j • ((x - t) ^ (μ - 1) • t ^ (m + 1 - j) • G j t)) volume 0 x :=
    (hint₁ j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))).smul (c₁ j)
  have hD₂' (j : ℕ) (hj : j ∈ Finset.range (m + 1)) : IntervalIntegrable
      (fun t ↦ c₂ j • ((x - t) ^ (μ - 1) • t ^ (m - j) • G j t)) volume 0 x :=
    (hint₂ j (hmem hj)).smul (c₂ j)
  have hD₁ : IntervalIntegrable D₁ volume 0 x := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum _ hD₁'
  have hD₂ : IntervalIntegrable D₂ volume 0 x := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum _ hD₂'
  have hI₁ := intervalIntegral.integral_finsetSum hD₁'
  have hI₂ := intervalIntegral.integral_finsetSum hD₂'
  simp only [intervalIntegral.integral_smul] at hI₁ hI₂
  have hDi : IntervalIntegrable (fun s ↦ D₁ s - x • D₂ s) volume 0 x := hD₁.sub (hD₂.smul x)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.le hWc hWd hDi
  -- the endpoint values of `W`
  have hWx : W x = 0 := by simp [hW, Real.zero_rpow hμ.ne']
  have hW0 : W 0 = -((w m * x ^ μ) • G (m + 1) 0) := by
    simp only [hW, Finset.sum_range_succ, Nat.sub_self, pow_zero, one_smul, sub_zero]
    rw [Finset.sum_eq_zero fun j hj ↦ by
      rw [zero_pow (Nat.sub_ne_zero_of_lt (Finset.mem_range.mp hj)), zero_smul, smul_zero],
      zero_add]
  -- the integral of `D₁ - x • D₂`
  rw [hWx, hW0, sub_neg_eq_add, zero_add, intervalIntegral.integral_sub (f := D₁)
    (g := fun y ↦ x • D₂ y) hD₁ (hD₂.smul x), intervalIntegral.integral_smul] at hftc
  rw [hI₁, hI₂] at hftc
  simp only [fractionalIntegral_def, smul_comm _ (Real.Gamma μ)⁻¹, ← Finset.smul_sum]
  rw [← sub_eq_iff_eq_add', ← smul_sub, hftc, smul_smul]
  congr 1
  simp only [w, Nat.choose_self, Nat.cast_one, one_mul]
  ring

/-! ### Fractional integrals of powers -/

/-- The fractional integral at `x ≥ 0` only depends on the values on `(0, x]`. -/
theorem fractionalIntegral_congr {μ x : ℝ} (hx : 0 ≤ x) {g₁ g₂ : ℝ → E}
    (h : EqOn g₁ g₂ (Ioc 0 x)) : fractionalIntegral μ g₁ x = fractionalIntegral μ g₂ x := by
  simp only [fractionalIntegral_def]
  congr 1
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht ↦ ?_)
  rw [uIoc_of_le hx] at ht
  rw [h ht]

/-- The fractional integral is additive on functions whose defining integrals converge. -/
theorem fractionalIntegral_sub {μ x : ℝ} {g₁ g₂ : ℝ → E}
    (h₁ : IntervalIntegrable (fun t ↦ (x - t) ^ (μ - 1) • g₁ t) volume 0 x)
    (h₂ : IntervalIntegrable (fun t ↦ (x - t) ^ (μ - 1) • g₂ t) volume 0 x) :
    fractionalIntegral μ (fun t ↦ g₁ t - g₂ t) x =
      fractionalIntegral μ g₁ x - fractionalIntegral μ g₂ x := by
  simp only [fractionalIntegral_def, smul_sub, intervalIntegral.integral_sub h₁ h₂]

/-- The fractional integral commutes with scalar multiplication. -/
theorem fractionalIntegral_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (μ : ℝ) (c : 𝕜) (g : ℝ → E) (x : ℝ) :
    fractionalIntegral μ (fun t ↦ c • g t) x = c • fractionalIntegral μ g x := by
  simp only [fractionalIntegral_def, smul_comm _ c, intervalIntegral.integral_smul]

/-- The fractional integral of a scalar function times a constant vector. -/
theorem fractionalIntegral_smul_const [CompleteSpace E] (μ : ℝ) (g : ℝ → ℝ) (c : E) (x : ℝ) :
    fractionalIntegral μ (fun t ↦ g t • c) x = fractionalIntegral μ g x • c := by
  simp only [fractionalIntegral_def, smul_smul, smul_eq_mul]
  rw [intervalIntegral.integral_smul_const, smul_smul]

/-- The fractional integral of a power is a Beta integral:
`I^μ (t ↦ t^β)(x) = Γ(β + 1) / Γ(β + μ + 1) x^(β + μ)` for `β > -1`, `μ > 0` and `x > 0`. -/
theorem fractionalIntegral_rpow {μ β : ℝ} (hμ : 0 < μ) (hβ : -1 < β) {x : ℝ} (hx : 0 < x) :
    fractionalIntegral μ (fun t ↦ t ^ β) x =
      Real.Gamma (β + 1) / Real.Gamma (β + μ + 1) * x ^ (β + μ) := by
  have hsub : ∫ t in (0 : ℝ)..x, (x - t) ^ (μ - 1) • t ^ β =
      x ^ (β + μ) * ∫ u in (0 : ℝ)..1, u ^ (β + 1 - 1) * (1 - u) ^ (μ - 1) := by
    have h := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
      (fun t ↦ (x - t) ^ (μ - 1) • t ^ β) x
    simp only [mul_zero, mul_one] at h
    rw [← h, smul_eq_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu ↦ ?_
    rw [uIcc_of_le zero_le_one] at hu
    simp only [smul_eq_mul, add_sub_cancel_right]
    have hxu : x - x * u = x * (1 - u) := by ring
    rw [hxu, Real.mul_rpow hx.le (by linarith [hu.2]),
      Real.mul_rpow hx.le hu.1, Real.rpow_add hx, Real.rpow_sub_one hx.ne']
    field_simp
  have hβμ : β + 1 + μ = β + μ + 1 := by ring
  rw [fractionalIntegral_def, smul_eq_mul, hsub, integral_rpow_mul_one_sub_rpow (by linarith) hμ,
    ProbabilityTheory.beta, hβμ]
  have hΓ : Real.Gamma μ ≠ 0 := (Real.Gamma_pos_of_pos hμ).ne'
  field_simp

/-! ### Remainders of an expansion at `+∞` -/

variable {α : ℝ} {f : ℝ → E} {a : ℕ → E}

/-- The remainder `f_m(t) = f(t) - ∑_{k<m} a_k t^(-k-α)`, with real powers. -/
private noncomputable def rem (f : ℝ → E) (a : ℕ → E) (α : ℝ) (m : ℕ) (t : ℝ) : E :=
  f t - ∑ k ∈ Finset.range m, t ^ (-((k : ℝ) + α)) • a k

private theorem rem_succ (m : ℕ) (t : ℝ) :
    rem f a α (m + 1) t = rem f a α m t - t ^ (-((m : ℝ) + α)) • a m := by
  simp only [rem, Finset.sum_range_succ]
  abel

private theorem continuousOn_rem (hfc : ContinuousOn f (Ioi 0)) (m : ℕ) :
    ContinuousOn (rem f a α m) (Ioi 0) :=
  hfc.sub (continuousOn_finsetSum _ fun _ _ ↦
    (continuousOn_id.rpow_const fun _ ht ↦ Or.inl (ne_of_gt ht)).smul continuousOn_const)

/-- Near `0`, `t^k f_m(t)` is integrable on `(0, 1]` for `m ≤ k + 1`. -/
private theorem integrableOn_Ioc_pow_smul_rem (hα₁ : α < 1) (hf : LocallyIntegrableOn f (Ici 0))
    {k m : ℕ} (hkm : m ≤ k + 1) :
    IntegrableOn (fun t ↦ t ^ k • rem f a α m t) (Ioc 0 1) := by
  simp_rw [rem, smul_sub, Finset.smul_sum]
  refine IntegrableOn.sub ?_ (integrable_finsetSum _ fun s hs ↦ ?_)
  · exact ((hf.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc).continuousOn_smul
      (continuous_pow k).continuousOn isCompact_Icc).mono_set Ioc_subset_Icc_self
  · have hs' : (s : ℝ) ≤ k := by
      have := Finset.mem_range.mp hs
      exact_mod_cast (by omega : s ≤ k)
    have hint := ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (r := (k : ℝ) - (s + α)) (by linarith)).1).smul_const (a s)
    refine IntegrableOn.congr_fun hint (fun t (ht : t ∈ Ioc 0 1) ↦ ?_) measurableSet_Ioc
    simp only [smul_smul]
    rw [sub_eq_add_neg, Real.rpow_add ht.1, Real.rpow_natCast]

/-- `τ^(m - 1) f_m(τ)` is integrable on `(0, ∞)`. -/
private theorem integrableOn_Ioi_pow_smul_rem (hα₀ : 0 < α) (hα₁ : α < 1)
    (hf : LocallyIntegrableOn f (Ici 0)) (hfc : ContinuousOn f (Ioi 0)) {k m : ℕ}
    (hkm : k + 1 = m) (hn : rem f a α m =O[atTop] fun t ↦ t ^ (-((m : ℝ) + α))) :
    IntegrableOn (fun τ ↦ τ ^ k • rem f a α m τ) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine (integrableOn_Ioc_pow_smul_rem hα₁ hf hkm.ge).union ?_
  have h := integrableOn_Ioi_sub_pow_smul (continuousOn_rem hfc m) hn (i := k)
    (by rw [← hkm]; push_cast; linarith) one_pos 0
  simpa using h

/-! ### The repeated integrals of the remainder -/

private theorem integrableOn_Ioi_sub_pow_smul_rem (hfc : ContinuousOn f (Ioi 0)) {m : ℕ}
    (hn : rem f a α m =O[atTop] fun t ↦ t ^ (-((m : ℝ) + α))) (hα₀ : 0 < α) {i : ℕ} (hi : i < m)
    {s : ℝ} (hs : 0 < s) (u : ℝ) :
    IntegrableOn (fun τ ↦ (τ - u) ^ i • rem f a α m τ) (Ioi s) :=
  integrableOn_Ioi_sub_pow_smul (continuousOn_rem hfc m) hn
    (by have : (i : ℝ) + 1 ≤ m := by exact_mod_cast hi
        linarith) hs u

private theorem hasDerivAt_repeatedIntegralAtTop_rem [CompleteSpace E] (hα₀ : 0 < α)
    (hfc : ContinuousOn f (Ioi 0)) {m : ℕ}
    (hn : rem f a α m =O[atTop] fun t ↦ t ^ (-((m : ℝ) + α))) {j : ℕ} (hj : j < m) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (repeatedIntegralAtTop (rem f a α m) (j + 1))
      (repeatedIntegralAtTop (rem f a α m) j t) t :=
  hasDerivAt_repeatedIntegralAtTop (continuousOn_rem hfc m)
    (fun _ hi s hs ↦ integrableOn_Ioi_sub_pow_smul_rem hfc hn hα₀ (hi.trans_lt hj) hs s) ht

/-- `t^k` times the repeated integral of order `j + 1` of `f_m`, `k + j + 1 = m`, is continuous
on `[0, x]`. -/
private theorem continuousOn_pow_smul_repeatedIntegralAtTop_rem [CompleteSpace E] (hα₀ : 0 < α)
    (hα₁ : α < 1) (hf : LocallyIntegrableOn f (Ici 0)) (hfc : ContinuousOn f (Ioi 0)) {m : ℕ}
    (hn : rem f a α m =O[atTop] fun t ↦ t ^ (-((m : ℝ) + α))) {k j : ℕ} (hkj : k + (j + 1) = m)
    (x : ℝ) :
    ContinuousOn (fun t ↦ t ^ k • repeatedIntegralAtTop (rem f a α m) (j + 1) t) (Icc 0 x) := by
  intro t ht
  rcases ht.1.eq_or_lt with rfl | ht0
  · exact (continuousWithinAt_pow_smul_repeatedIntegralAtTop
      (integrableOn_Ioi_pow_smul_rem (k := k + j) hα₀ hα₁ hf hfc (by omega) hn)).mono
      Icc_subset_Ici_self
  · exact ((continuous_pow k).continuousAt.smul (hasDerivAt_repeatedIntegralAtTop_rem hα₀ hfc hn
      (by omega) ht0).continuousAt).continuousWithinAt

/-- The integrals `I^μ(t^(m - j) f_{m,j})(x)` converge absolutely, `j ≤ m`. -/
private theorem intervalIntegrable_rpow_sub_smul_pow_smul_rem [CompleteSpace E] {μ : ℝ}
    (hμ : 0 < μ) (hα₀ : 0 < α) (hα₁ : α < 1) (hf : LocallyIntegrableOn f (Ici 0))
    (hfc : ContinuousOn f (Ioi 0)) {m : ℕ}
    (hn : rem f a α m =O[atTop] fun t ↦ t ^ (-((m : ℝ) + α))) {x : ℝ} (hx : 0 < x) {j : ℕ}
    (hj : j ≤ m) :
    IntervalIntegrable (fun t ↦ (x - t) ^ (μ - 1) • t ^ (m - j) •
      repeatedIntegralAtTop (rem f a α m) j t) volume 0 x := by
  set c := min 1 (x / 2)
  have hc0 : 0 < c := lt_min one_pos (by linarith)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcx : c < x := (min_le_right _ _).trans_lt (by linarith)
  have hIcc : Icc c x ⊆ Ioi 0 := fun t ht ↦ hc0.trans_le ht.1
  refine intervalIntegrable_rpow_sub_smul hμ hc0 hcx ?_ ?_
  · cases j with
    | zero =>
      exact (integrableOn_Ioc_pow_smul_rem (k := m) hα₁ hf (by omega)).mono_set
        (Ioc_subset_Ioc_right hc1)
    | succ j =>
      exact ((continuousOn_pow_smul_repeatedIntegralAtTop_rem (k := m - (j + 1)) hα₀ hα₁ hf hfc
        hn (by omega) c).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  · cases j with
    | zero => exact (continuous_pow m).continuousOn.smul ((continuousOn_rem hfc m).mono hIcc)
    | succ j =>
      exact (continuousOn_pow_smul_repeatedIntegralAtTop_rem (k := m - (j + 1)) hα₀ hα₁ hf hfc
        hn (by omega) x).mono (Icc_subset_Icc_left hc0.le)

/-! ### The repeated integrals of a power -/

/-- The power `τ^(-(n + α)) c` times `(τ - u)^i`, `i < n`, is integrable on `(s, ∞)`, `s > 0`. -/
private theorem integrableOn_Ioi_sub_pow_smul_rpow_smul (hα₀ : 0 < α) (n : ℕ) (c : E) {i : ℕ}
    (hi : i < n) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    IntegrableOn (fun τ ↦ (τ - u) ^ i • τ ^ (-((n : ℝ) + α)) • c) (Ioi s) := by
  have hin : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
  exact integrableOn_Ioi_sub_pow_smul (h := fun τ ↦ τ ^ (-((n : ℝ) + α)) • c)
    ((continuousOn_id.rpow_const fun _ ht ↦ Or.inl (ne_of_gt ht)).smul continuousOn_const)
    (IsBigO.of_bound ‖c‖ (Eventually.of_forall fun τ ↦ by rw [norm_smul, mul_comm]))
    (by linarith) hs u

/-- The repeated integrals of `τ ↦ τ^(-(n + α)) c` of order `j ≤ n` are
`(-α)^{(n-j)} / (-α)^{(n)} t^(j - n - α) c`. -/
private theorem repeatedIntegralAtTop_rpow_smul [CompleteSpace E] (hα₀ : 0 < α) (n : ℕ) (c : E)
    {j : ℕ} (hj : j ≤ n) {t : ℝ} (ht : 0 < t) :
    repeatedIntegralAtTop (fun τ ↦ τ ^ (-((n : ℝ) + α)) • c) j t =
      ((descPochhammer ℝ (n - j)).eval (-α) / (descPochhammer ℝ n).eval (-α) *
        t ^ ((j : ℝ) - n - α)) • c := by
  have hd : (descPochhammer ℝ n).eval (-α) ≠ 0 :=
    descPochhammer_eval_ne_zero (fun m hm ↦ by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) n
  induction j generalizing t with
  | zero =>
    rw [repeatedIntegralAtTop_zero, Nat.sub_zero, div_self hd, one_mul]
    congr 2
    push_cast
    ring
  | succ j ih =>
    have hjn : j < n := hj
    have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
    rw [repeatedIntegralAtTop_succ_eq_neg_integral
      (integrableOn_Ioi_sub_pow_smul_rpow_smul hα₀ n c hjn ht t),
      setIntegral_congr_fun measurableSet_Ioi (fun τ (hτ : t < τ) ↦ ih hjn.le (ht.trans hτ)),
      integral_smul_const, integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith) ht, ← neg_smul]
    congr 1
    have hnj : n - j = n - (j + 1) + 1 := by omega
    have hexp : (j : ℝ) - n - α + 1 = ((j + 1 : ℕ) : ℝ) - n - α := by push_cast; ring
    rw [hnj, descPochhammer_succ_eval, Nat.cast_sub hjn, hexp]
    have hne : ((j + 1 : ℕ) : ℝ) - n - α ≠ 0 := by push_cast; linarith
    field_simp
    push_cast
    ring

/-- Subtracting the term `k = n` from the remainder subtracts the repeated integrals of that
power. -/
private theorem repeatedIntegralAtTop_rem_succ (hα₀ : 0 < α)
    (hfc : ContinuousOn f (Ioi 0)) {n : ℕ}
    (hn : rem f a α n =O[atTop] fun t ↦ t ^ (-((n : ℝ) + α))) {j : ℕ} (hj : j ≤ n) {t : ℝ}
    (ht : 0 < t) :
    repeatedIntegralAtTop (rem f a α (n + 1)) j t = repeatedIntegralAtTop (rem f a α n) j t -
      repeatedIntegralAtTop (fun τ ↦ τ ^ (-((n : ℝ) + α)) • a n) j t := by
  cases j with
  | zero => exact rem_succ n t
  | succ j =>
    simp only [repeatedIntegralAtTop_succ, ← smul_sub]
    rw [← integral_sub (integrableOn_Ioi_sub_pow_smul_rem hfc hn hα₀ (by omega) ht t)
      (integrableOn_Ioi_sub_pow_smul_rpow_smul hα₀ n (a n) (by omega) ht t)]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ ↦ ?_
    simp only [rem_succ, smul_sub]

/-- On `(0, ∞)`, `t^(n - j)` times the repeated integral of order `j ≤ n` of `τ^(-(n + α)) c` is
`t^(-α)` times a constant. -/
private theorem pow_smul_repeatedIntegralAtTop_rpow_smul [CompleteSpace E] (hα₀ : 0 < α) (n : ℕ)
    (c : E) {j : ℕ} (hj : j ≤ n) {t : ℝ} (ht : 0 < t) :
    t ^ (n - j) • repeatedIntegralAtTop (fun τ ↦ τ ^ (-((n : ℝ) + α)) • c) j t =
      t ^ (-α) • (((descPochhammer ℝ (n - j)).eval (-α) / (descPochhammer ℝ n).eval (-α)) • c) := by
  rw [repeatedIntegralAtTop_rpow_smul hα₀ n c hj ht, smul_smul, smul_smul]
  congr 1
  rw [← Real.rpow_natCast, Nat.cast_sub hj, mul_left_comm, ← Real.rpow_add ht]
  ring_nf

private theorem intervalIntegrable_rpow_sub_smul_pow_smul_repeatedIntegralAtTop_rpow_smul
    [CompleteSpace E] {μ : ℝ} (hμ : 0 < μ) (hα₀ : 0 < α) (hα₁ : α < 1) (n : ℕ) (c : E) {j : ℕ}
    (hj : j ≤ n) {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun t ↦ (x - t) ^ (μ - 1) • t ^ (n - j) •
      repeatedIntegralAtTop (fun τ ↦ τ ^ (-((n : ℝ) + α)) • c) j t) volume 0 x := by
  set e := ((descPochhammer ℝ (n - j)).eval (-α) / (descPochhammer ℝ n).eval (-α)) • c
  have he : ContinuousOn (fun t : ℝ ↦ t ^ (-α) • e) (Ioi 0) :=
    (continuousOn_id.rpow_const fun _ ht ↦ Or.inl (ne_of_gt ht)).smul continuousOn_const
  have h := intervalIntegrable_rpow_sub_smul (h := fun t ↦ t ^ (-α) • e) (x := x) (c := x / 2) hμ
    (half_pos hx)
    (by linarith) ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := x / 2)
      (by linarith : (-1 : ℝ) < -α)).1.smul_const e)
    (he.mono fun t ht ↦ (half_pos hx).trans_le ht.1)
  refine h.congr_ae ((ae_restrict_mem measurableSet_uIoc).mono fun t ht ↦ ?_)
  rw [uIoc_of_le hx.le] at ht
  simp only [pow_smul_repeatedIntegralAtTop_rpow_smul hα₀ n c hj ht.1, e]

/-- The terms of `δ_n` coming from the power `τ^(-(n + α)) c` sum to
`Γ(1 - n - α) / Γ(μ + 1 - n - α) x^(μ - α) c`. -/
private theorem sum_smul_fractionalIntegral_rpow_smul [CompleteSpace E] {μ : ℝ} (hμ : 0 < μ)
    (hα₀ : 0 < α) (hα₁ : α < 1) (n : ℕ) (c : E) {x : ℝ} (hx : 0 < x) :
    ∑ j ∈ Finset.range (n + 1), ((n.choose j : ℝ) * (descPochhammer ℝ j).eval μ) •
        fractionalIntegral μ (fun t ↦ t ^ (n - j) •
          repeatedIntegralAtTop (fun τ ↦ τ ^ (-((n : ℝ) + α)) • c) j t) x =
      (Real.Gamma (1 - n - α) * (Real.Gamma (μ + 1 - n - α))⁻¹ * x ^ (μ - α)) • c := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      fractionalIntegral μ (fun t ↦ t ^ (n - j) •
          repeatedIntegralAtTop (fun τ ↦ τ ^ (-((n : ℝ) + α)) • c) j t) x =
        (Real.Gamma (1 - α) / Real.Gamma (μ + 1 - α) * x ^ (μ - α)) •
          (((descPochhammer ℝ (n - j)).eval (-α) / (descPochhammer ℝ n).eval (-α)) • c) := by
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [fractionalIntegral_congr hx.le (g₂ := fun t ↦ t ^ (-α) •
        (((descPochhammer ℝ (n - j)).eval (-α) / (descPochhammer ℝ n).eval (-α)) • c))
        fun t (ht : t ∈ Ioc 0 x) ↦ pow_smul_repeatedIntegralAtTop_rpow_smul hα₀ n c hjn ht.1,
      fractionalIntegral_smul_const, fractionalIntegral_rpow hμ (by linarith) hx]
    congr 2 <;> ring_nf
  rw [Finset.sum_congr rfl fun j hj ↦ by rw [hterm j hj]]
  simp only [smul_smul, ← Finset.sum_smul]
  congr 1
  have hV := sum_choose_mul_descPochhammer_eval n (Commute.all μ (-α))
  have h₁ := Real.inv_Gamma_sub_natCast (1 - α) n
  have h₂ := Real.inv_Gamma_sub_natCast (μ + 1 - α) n
  have e₁ : 1 - α - (n : ℝ) = 1 - n - α := by ring
  have e₂ : (1 : ℝ) - α - 1 = -α := by ring
  have e₃ : μ + 1 - α - (n : ℝ) = μ + 1 - n - α := by ring
  have e₄ : μ + 1 - α - 1 = μ + -α := by ring
  rw [e₁, e₂] at h₁
  rw [e₃, e₄] at h₂
  rw [h₂, ← inv_inv (Real.Gamma (1 - n - α)), h₁, ← hV, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hd : (descPochhammer ℝ n).eval (-α) ≠ 0 :=
    descPochhammer_eval_ne_zero (fun m hm ↦ by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]) n
  field_simp

/-! ### The induction step -/

/-- The sum `δ_m(x) = ∑_{j ≤ m} C(m, j) μ^{(j)} I^μ(t^(m - j) f_{m,j})(x)` of DLMF 2.6.47. -/
private noncomputable def delta (μ : ℝ) (f : ℝ → E) (a : ℕ → E) (α : ℝ) (m : ℕ) (x : ℝ) : E :=
  ∑ j ∈ Finset.range (m + 1), ((m.choose j : ℝ) * (descPochhammer ℝ j).eval μ) •
    fractionalIntegral μ (fun t ↦ t ^ (m - j) • repeatedIntegralAtTop (rem f a α m) j t) x

/-- The induction step for `TauCeti.fractionalIntegral_eq`:
`δ_{n+1}(x) = x (δ_n(x) - Γ(1 - n - α) / Γ(μ + 1 - n - α) x^(μ - α) a_n)
  + Γ(μ)⁻¹ (μ - 1)^{(n)} x^μ f_{n+1,n+1}(0)`. -/
private theorem delta_succ [CompleteSpace E] {μ : ℝ} (hμ : 0 < μ) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hf : LocallyIntegrableOn f (Ici 0)) (hfc : ContinuousOn f (Ioi 0)) {n : ℕ}
    (hn : rem f a α (n + 1) =O[atTop] fun t ↦ t ^ (-(((n + 1 : ℕ) : ℝ) + α)))
    (hn' : rem f a α n =O[atTop] fun t ↦ t ^ (-((n : ℝ) + α))) {x : ℝ} (hx : 0 < x) :
    delta μ f a α (n + 1) x = x • (delta μ f a α n x -
        (Real.Gamma (1 - n - α) * (Real.Gamma (μ + 1 - n - α))⁻¹ * x ^ (μ - α)) • a n) +
      ((Real.Gamma μ)⁻¹ * (descPochhammer ℝ n).eval (μ - 1) * x ^ μ) •
        repeatedIntegralAtTop (rem f a α (n + 1)) (n + 1) 0 := by
  set P := repeatedIntegralAtTop (fun τ ↦ τ ^ (-((n : ℝ) + α)) • a n)
  -- on `(0, x]`, the repeated integrals of `f_{n+1}` are those of `f_n` minus those of the power
  have hdecomp {j : ℕ} (hj : j ≤ n) : EqOn
      (fun t ↦ t ^ (n - j) • repeatedIntegralAtTop (rem f a α (n + 1)) j t)
      (fun t ↦ t ^ (n - j) • repeatedIntegralAtTop (rem f a α n) j t - t ^ (n - j) • P j t)
      (Ioc 0 x) := fun t ht ↦ by
    simp only [repeatedIntegralAtTop_rem_succ hα₀ hfc hn' hj ht.1, smul_sub, P]
  have hint {j : ℕ} (hj : j ≤ n) := intervalIntegrable_rpow_sub_smul_pow_smul_rem hμ hα₀ hα₁ hf
    hfc hn' hx hj
  have hPint {j : ℕ} (hj : j ≤ n) :=
    intervalIntegrable_rpow_sub_smul_pow_smul_repeatedIntegralAtTop_rpow_smul hμ hα₀ hα₁ n (a n)
      hj hx
  have hchain := sum_choose_mul_descPochhammer_smul_fractionalIntegral_succ hμ hx (m := n)
    (G := repeatedIntegralAtTop (rem f a α (n + 1)))
    (fun j hj t ht ↦ hasDerivAt_repeatedIntegralAtTop_rem hα₀ hfc hn (by omega) ht.1)
    (fun j hj ↦ continuousOn_pow_smul_repeatedIntegralAtTop_rem (k := n - j) hα₀ hα₁ hf hfc hn
      (by omega) x)
    (fun j hj ↦ intervalIntegrable_rpow_sub_smul_pow_smul_rem hμ hα₀ hα₁ hf hfc hn hx hj)
    (fun j hj ↦ ((hint hj).sub (hPint hj)).congr_ae
      ((ae_restrict_mem measurableSet_uIoc).mono fun t ht ↦ by
        rw [uIoc_of_le hx.le] at ht
        simp only [hdecomp hj ht, smul_sub, P]))
  have hsplit : ∑ j ∈ Finset.range (n + 1), ((n.choose j : ℝ) * (descPochhammer ℝ j).eval μ) •
      fractionalIntegral μ (fun t ↦ t ^ (n - j) • repeatedIntegralAtTop (rem f a α (n + 1)) j t) x =
      delta μ f a α n x - ∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℝ) * (descPochhammer ℝ j).eval μ) •
          fractionalIntegral μ (fun t ↦ t ^ (n - j) • P j t) x := by
    rw [delta, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [← smul_sub, fractionalIntegral_congr hx.le (hdecomp hjn),
      fractionalIntegral_sub (by simpa only [smul_sub] using hint hjn) (hPint hjn)]
  have hidx : n + 1 + 1 = n + 2 := by omega
  rw [delta, hidx, hchain, hsplit,
    sum_smul_fractionalIntegral_rpow_smul hμ hα₀ hα₁ n (a n) hx]

end Real

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {α : ℝ} {f : ℝ → E} {a : ℕ → E}

/-- On `[0, ∞)`, the remainder with complex powers is the one with real powers. -/
private theorem sub_sum_cpow_smul_eq_rem (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    f t - ∑ k ∈ Finset.range m, (t : ℂ) ^ (-((k : ℂ) + α)) • a k = rem f a α m t := by
  simp only [rem]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← Complex.coe_smul, Complex.ofReal_cpow ht]
  push_cast
  rfl

private theorem repeatedIntegralAtTop_sub_sum_cpow_smul (m j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    repeatedIntegralAtTop
        (fun t ↦ f t - ∑ k ∈ Finset.range m, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) j t =
      repeatedIntegralAtTop (rem f a α m) j t := by
  cases j with
  | zero => exact sub_sum_cpow_smul_eq_rem m ht
  | succ j =>
    simp only [repeatedIntegralAtTop_succ]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi fun τ (hτ : t < τ) ↦ by
      rw [sub_sum_cpow_smul_eq_rem m (ht.trans hτ.le)]

private theorem isBigO_rem {m : ℕ}
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range m, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((m : ℂ) + α))) :
    rem f a α m =O[atTop] fun t ↦ t ^ (-((m : ℝ) + α)) := by
  refine (hn.trans_ofReal_cpow_rpow (eventually_gt_atTop 0) (by simp)).congr' ?_
    (Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact sub_sum_cpow_smul_eq_rem m ht

/-- **The remainder integrals converge** (DLMF 2.6.47): under the hypotheses of
`TauCeti.fractionalIntegral_eq`, the integrals `I^μ(t^(n - j) f_{n,j})(x)`, `j ≤ n`, converge
absolutely for every `x > 0`. -/
theorem intervalIntegrable_rpow_sub_smul_pow_smul_repeatedIntegralAtTop [CompleteSpace E] {μ : ℝ}
    (hμ : 0 < μ) (hα₀ : 0 < α) (hα₁ : α < 1) (hf : LocallyIntegrableOn f (Ici 0))
    (hfc : ContinuousOn f (Ioi 0)) {n : ℕ}
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + α)))
    {x : ℝ} (hx : 0 < x) {j : ℕ} (hj : j ≤ n) :
    IntervalIntegrable (fun t ↦ (x - t) ^ (μ - 1) • t ^ (n - j) • repeatedIntegralAtTop
      (fun t ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) j t) volume 0 x :=
  (intervalIntegrable_rpow_sub_smul_pow_smul_rem hμ hα₀ hα₁ hf hfc (isBigO_rem hn) hx hj).congr_ae
    ((ae_restrict_mem measurableSet_uIoc).mono fun t ht ↦ by
      rw [uIoc_of_le hx.le] at ht
      simp only [repeatedIntegralAtTop_sub_sum_cpow_smul n j ht.1.le])

/-! ### The expansion -/

/-- At `n + 1`, `𝓜f(n + 1)` is `∫₀^∞ tⁿ f_{n+1}(t) dt`, written with the real remainder. -/
private theorem mellinContAtTop_natCast_add_one_eq_integral_rem [CompleteSpace E] (hα₀ : 0 < α)
    (hα₁ : α < 1) (hf : LocallyIntegrableOn f (Ici 0)) {n : ℕ}
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range (n + 1), (t : ℂ) ^ (-((k : ℂ) + α)) • a k)
      =O[atTop] fun t ↦ (t : ℂ) ^ (-(((n + 1 : ℕ) : ℂ) + α))) :
    mellinContAtTop f a (fun k ↦ (k : ℂ) + α) (n + 1) ((n : ℂ) + 1) =
      ∫ t in Ioi (0 : ℝ), (t - 0) ^ n • rem f a α (n + 1) t := by
  rw [mellinContAtTop_natCast_add_one_eq_integral hα₀ hα₁ hf hn]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
  rw [sub_zero, sub_sum_cpow_smul_eq_rem (n + 1) ht.le, ← Complex.ofReal_pow, Complex.coe_smul]

/-- The expansion in the form proved by induction, with real powers in the remainder. -/
private theorem fractionalIntegral_eq_aux [CompleteSpace E] {μ : ℝ} (hμ : 0 < μ) (hα₀ : 0 < α)
    (hα₁ : α < 1) (hf : LocallyIntegrableOn f (Ici 0)) (hfc : ContinuousOn f (Ioi 0)) {n : ℕ}
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + α)))
    {x : ℝ} (hx : 0 < x) :
    fractionalIntegral μ f x =
      ∑ s ∈ Finset.range n,
          (Real.Gamma (1 - s - α) * (Real.Gamma (μ + 1 - s - α))⁻¹ * x ^ (μ - s - α)) • a s +
        ∑ s ∈ Finset.range n, ((-1) ^ s / (s ! : ℝ) * (Real.Gamma (μ - s))⁻¹ * x ^ (μ - s - 1)) •
          mellinContAtTop f a (fun k ↦ (k : ℂ) + α) n ((s : ℂ) + 1) +
        (x ^ n)⁻¹ • delta μ f a α n x := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, inv_one, one_smul, delta,
      Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, descPochhammer_zero,
      Polynomial.eval_one, mul_one, repeatedIntegralAtTop_zero, Nat.sub_zero]
    exact fractionalIntegral_congr hx.le fun t _ ↦ by simp [rem]
  | succ n ih =>
    have hn' := isBigO_sub_sum_of_succ hn
    have e₁ : μ - (n : ℝ) - α = μ - α - n := by ring
    have e₂ : μ - (n : ℝ) - 1 = μ - ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    have hM : ∑ s ∈ Finset.range n,
        ((-1) ^ s / (s ! : ℝ) * (Real.Gamma (μ - s))⁻¹ * x ^ (μ - s - 1)) •
          mellinContAtTop f a (fun k ↦ (k : ℂ) + α) (n + 1) ((s : ℂ) + 1) =
        ∑ s ∈ Finset.range n,
          ((-1) ^ s / (s ! : ℝ) * (Real.Gamma (μ - s))⁻¹ * x ^ (μ - s - 1)) •
            mellinContAtTop f a (fun k ↦ (k : ℂ) + α) n ((s : ℂ) + 1) :=
      Finset.sum_congr rfl fun s hs ↦ by
        rw [mellinContAtTop_succ_natCast_add_one hα₀ hf hn' (Finset.mem_range.mp hs)]
    rw [ih hn', Finset.sum_range_succ, Finset.sum_range_succ, hM,
      delta_succ hμ hα₀ hα₁ hf hfc (isBigO_rem hn) (isBigO_rem hn') hx, repeatedIntegralAtTop_succ,
      ← mellinContAtTop_natCast_add_one_eq_integral_rem hα₀ hα₁ hf hn,
      Real.inv_Gamma_sub_natCast μ n, e₁, Real.rpow_sub hx (μ - α) n, Real.rpow_natCast, e₂,
      Real.rpow_sub hx μ ((n + 1 : ℕ) : ℝ), Real.rpow_natCast]
    match_scalars <;> field_simp <;> ring

/-- **Expansion of fractional integrals** (DLMF 2.6.45, `0 < α < 1`). Let `μ > 0`, and let `f` be
locally integrable on `[0, ∞)` and continuous on `(0, ∞)`, with
`f(t) - ∑_{k<n} a_k t^{-k-α} = O(t^{-n-α})` as `t → +∞`. Then for every `x > 0` the
Riemann–Liouville integral `I^μ f(x) = Γ(μ)⁻¹ ∫₀^x (x - t)^(μ - 1) f(t) dt` is

`I^μ f(x) = ∑_{s<n} a_s Γ(1 - s - α) / Γ(μ + 1 - s - α) x^(μ - s - α)
  + ∑_{s<n} (-1)^s / s! 𝓜f(s + 1) / Γ(μ - s) x^(μ - s - 1) + x⁻ⁿ δ_n(x)`,

`δ_n(x) = ∑_{j ≤ n} C(n, j) Γ(μ + 1) / Γ(μ + 1 - j) I^μ(t^(n - j) f_{n,j})(x)` (DLMF 2.6.47),

where `f_n(t) = f(t) - ∑_{k<n} a_k t^{-k-α}`, `f_{n,j}` is its `j`-th repeated integral from `+∞`
(`TauCeti.repeatedIntegralAtTop`), and `𝓜f = mellinContAtTop f a (k ↦ k + α) n` is the continued
Mellin transform. In DLMF's notation `(s - 1)! c_s = (-1)^s 𝓜f(s)` (DLMF 2.6.18), so the second sum
is `-∑_{s=1}^n c_s / Γ(μ + 1 - s) x^(μ - s)`. Reciprocal Gamma factors are `(Real.Gamma _)⁻¹`,
which vanish at the poles, so the identity holds for every `μ > 0`, integers included. The
integrals on both sides converge absolutely
(`TauCeti.intervalIntegrable_rpow_sub_smul_of_continuousOn` and
`TauCeti.intervalIntegrable_rpow_sub_smul_pow_smul_repeatedIntegralAtTop`). -/
theorem fractionalIntegral_eq [CompleteSpace E] {μ : ℝ} (hμ : 0 < μ) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hf : LocallyIntegrableOn f (Ici 0)) (hfc : ContinuousOn f (Ioi 0)) {n : ℕ}
    (hn : (fun t : ℝ ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) =O[atTop]
      fun t ↦ (t : ℂ) ^ (-((n : ℂ) + α)))
    {x : ℝ} (hx : 0 < x) :
    fractionalIntegral μ f x =
      ∑ s ∈ Finset.range n,
          (Real.Gamma (1 - s - α) * (Real.Gamma (μ + 1 - s - α))⁻¹ * x ^ (μ - s - α)) • a s +
        ∑ s ∈ Finset.range n, ((-1) ^ s / (s ! : ℝ) * (Real.Gamma (μ - s))⁻¹ * x ^ (μ - s - 1)) •
          mellinContAtTop f a (fun k ↦ (k : ℂ) + α) n ((s : ℂ) + 1) +
        (x ^ n)⁻¹ • ∑ j ∈ Finset.range (n + 1),
          ((n.choose j : ℝ) * Real.Gamma (μ + 1) * (Real.Gamma (μ + 1 - j))⁻¹) •
            fractionalIntegral μ (fun t ↦ t ^ (n - j) • repeatedIntegralAtTop
              (fun t ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) j t) x := by
  rw [fractionalIntegral_eq_aux hμ hα₀ hα₁ hf hfc hn hx, delta]
  congr 2
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hΓ : Real.Gamma (μ + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  rw [Real.inv_Gamma_sub_natCast (μ + 1) j, add_sub_cancel_right,
    fractionalIntegral_congr hx.le (g₁ := fun t ↦ t ^ (n - j) • repeatedIntegralAtTop
      (fun t ↦ f t - ∑ k ∈ Finset.range n, (t : ℂ) ^ (-((k : ℂ) + α)) • a k) j t)
      (g₂ := fun t ↦ t ^ (n - j) • repeatedIntegralAtTop (rem f a α n) j t)
      fun t (ht : t ∈ Ioc 0 x) ↦ by
        simp only [repeatedIntegralAtTop_sub_sum_cpow_smul n j ht.1.le]]
  congr 1
  field_simp

end Complex

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Exp.Decay
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Exp.Unimodality
import TauCeti.Probability.Distributions.Gamma.Basic
import TauCeti.Probability.Distributions.Gamma.PDF

/-!
# The Gamma kernel

For `k : ℕ` and a real rate `a`, the *Gamma kernel* is `u ↦ u ^ k * exp (-(a * u)) / k !` on
`(0, ∞)`. If the real point `a` lies in the open half-plane of convergence of the Laplace
transform `Φ(s) = ∫₀^∞ g(u) e^(-su) du`, the coefficient `(-1) ^ k Φ⁽ᵏ⁾(a) / k !` of `t ^ k` in
the expansion of `Φ(a - t)` is the integral of `g` against it
(`TauCeti.hasLaplace_pow_div_factorial_smul_iteratedDeriv` in
`TauCeti.Analysis.LaplaceTransform.Basic`), which is how it enters Landau's theorem
(`TauCeti.Analysis.LaplaceTransform.Landau`) and its windowed form. It is written out as this
expression throughout, not given a name.
For a positive rate `a` and `u ≥ 0` it is `(a ^ (k + 1))⁻¹` times the probability density
`gammaPDFReal (k + 1) a u` of the Gamma distribution with shape `k + 1` and rate `a`: this is
`TauCeti.Probability.gammaPDFReal_nat_div_pow` at shape `k + 1`, and is not restated here.

## Main results

* `TauCeti.integral_pow_mul_exp_neg_mul_div_factorial_Ioi`: for `0 < a` its mass is
  `(a ^ (k + 1))⁻¹`. The equation is also true at `a = 0`, where the mass is infinite and both
  sides are `0` by convention.
* `TauCeti.pow_mul_exp_neg_mul_div_factorial_nonneg`,
  `TauCeti.pow_mul_exp_neg_mul_div_factorial_le_inv_pow`: on `[0, ∞)` it lies between `0` and,
  for `0 < a`, `(a ^ k)⁻¹`.
* `TauCeti.pow_mul_exp_neg_mul_div_factorial_eq_exp_neg_mul_mul`: changing the rate from `a` to
  `a - b` multiplies the kernel by `exp (b * u)`.
* `TauCeti.setIntegral_pow_mul_exp_neg_mul_div_factorial_le`: for `0 < a` its mass on any set
  contained in `(0, ∞)` up to a null set is at most the total mass.
* `TauCeti.setIntegral_Ioi_sdiff_Icc_pow_mul_exp_neg_mul_div_factorial_le`: a Chernoff bound for
  its mass off an interval `[U, V]`, with independent tilts for the two tails. Its consequence
  for the windows `[U, (1 + δ) U]` of the windowed form of Landau's theorem is in
  `TauCeti.Analysis.LaplaceTransform.Landau`.
* `TauCeti.pow_mul_exp_neg_mul_div_factorial_le_off_window`: for a suitable degree `k`, the
  kernel outside `[U, L U]` is bounded by `(a ^ k)⁻¹ * q ^ k`, with `q < 1` depending only on
  `L`. This controls the off-window contribution against an integrable input without a pointwise
  growth bound on that input.

## References

* L. Alpöge's Lean formalization of the Riemann hypothesis for Dirichlet L-functions
  (<https://github.com/leanprover-community/riemann-hypothesis>) is the source of the mass,
  basic upper bound, rate shift, and Chernoff estimate off an interval:
  `Deduction.kernel_integral` for the mass at a positive rate, `Deduction.landau_kernel_max` for
  the upper bound and shift, and `Deduction.landau_tails_chernoff` for the mass off an interval
  with one tilt `0 ≤ l < a` for both tails. Two extensions are added here: the mass equation at
  rate `0`, an equality of Bochner integrals by convention (see its docstring), and the
  independent tilts of the two tails.
-/

public section

open MeasureTheory Real Set
open scoped Nat

namespace TauCeti

/-- **Mass of the Gamma kernel.** For `0 < a`, `∫₀^∞ u ^ k e^(-a u) / k ! du = a^(-k-1)`. The
equation also holds at `a = 0`, but not as a statement about mass: the kernel `u ^ k / k !` has
infinite mass there, so it is not integrable, and both its Bochner integral and `0⁻¹` are `0` by
convention. -/
theorem integral_pow_mul_exp_neg_mul_div_factorial_Ioi (k : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ∫ u in Ioi 0, u ^ k * exp (-(a * u)) / k ! = (a ^ (k + 1))⁻¹ := by
  rcases ha.eq_or_lt with rfl | ha
  · simp only [zero_mul, neg_zero, exp_zero, mul_one, integral_div, ← rpow_natCast,
      setIntegral_Ioi_zero_rpow, zero_div, zero_pow k.succ_ne_zero, inv_zero]
  · rw [integral_div, integral_pow_mul_exp_neg_mul_Ioi k ha,
      div_div_cancel_left₀ (by positivity)]

/-- The Gamma kernel is nonnegative on `[0, ∞)`, at every rate. -/
theorem pow_mul_exp_neg_mul_div_factorial_nonneg (k : ℕ) (a : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ u ^ k * exp (-(a * u)) / k ! := by
  positivity

/-- **Upper bound for the Gamma kernel.** For `0 < a` and `0 ≤ u`,
`u ^ k * exp (-(a * u)) / k ! ≤ a^(-k)`. -/
theorem pow_mul_exp_neg_mul_div_factorial_le_inv_pow (k : ℕ) {a u : ℝ} (ha : 0 < a)
    (hu : 0 ≤ u) : u ^ k * exp (-(a * u)) / k ! ≤ (a ^ k)⁻¹ := by
  rw [div_le_iff₀ (by positivity), inv_mul_eq_div, ← neg_mul]
  exact pow_mul_exp_neg_mul_le ha hu k

/-- **Shift of the rate.** At all real rates `a` and `b`, the Gamma kernel of rate `a` is
`exp (-(b * u))` times the kernel of rate `a - b`. -/
theorem pow_mul_exp_neg_mul_div_factorial_eq_exp_neg_mul_mul (k : ℕ) (a b u : ℝ) :
    u ^ k * exp (-(a * u)) / k ! = exp (-(b * u)) * (u ^ k * exp (-((a - b) * u)) / k !) := by
  have h : -(a * u) = -(b * u) + -((a - b) * u) := by ring
  rw [h, exp_add]
  ring

/-- On any set `s` contained in `(0, ∞)` up to a null set, the mass of the Gamma kernel of rate
`0 < a` is at most its total mass `a^(-k-1)`. -/
theorem setIntegral_pow_mul_exp_neg_mul_div_factorial_le (k : ℕ) {a : ℝ} (ha : 0 < a) {s : Set ℝ}
    (hs : s ≤ᵐ[volume] Ioi 0) : ∫ u in s, u ^ k * exp (-(a * u)) / k ! ≤ (a ^ (k + 1))⁻¹ := by
  rw [← integral_pow_mul_exp_neg_mul_div_factorial_Ioi k ha.le]
  exact setIntegral_mono_set ((integrableOn_pow_mul_exp_neg_mul_Ioi k ha).div_const _)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu ↦
      pow_mul_exp_neg_mul_div_factorial_nonneg k a (mem_Ioi.1 hu).le) hs

open ProbabilityTheory in
/-- **Mass of the Gamma kernel off an interval** (a Chernoff bound). For tilts `0 ≤ l₁ < a` of
the upper tail and `0 ≤ l₂` of the lower tail, and any reals `U`, `V`, the mass of the kernel of
rate `a` on `(0, ∞) \ [U, V]` is at most
`exp (-(l₁ * V)) * (a - l₁)^(-k-1) + exp (l₂ * U) * (a + l₂)^(-k-1)`. The kernel is
`(a ^ (k + 1))⁻¹` times the density of the Gamma law of shape `k + 1` and rate `a`, and the two
terms are Mathlib's Chernoff bounds `ProbabilityTheory.measure_ge_le_exp_mul_mgf` at `l₁` and
`ProbabilityTheory.measure_le_le_exp_mul_mgf` at `-l₂` for that law, whose moment-generating
function is `TauCeti.Probability.mgf_id_gammaMeasure`. -/
theorem setIntegral_Ioi_sdiff_Icc_pow_mul_exp_neg_mul_div_factorial_le (k : ℕ) {a l₁ l₂ : ℝ}
    (hl₁ : 0 ≤ l₁) (hla : l₁ < a) (hl₂ : 0 ≤ l₂) (U V : ℝ) :
    ∫ u in Ioi 0 \ Icc U V, u ^ k * exp (-(a * u)) / k ! ≤
      exp (-(l₁ * V)) * ((a - l₁) ^ (k + 1))⁻¹ + exp (l₂ * U) * ((a + l₂) ^ (k + 1))⁻¹ := by
  have ha : 0 < a := hl₁.trans_lt hla
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  let μ := gammaMeasure (k + 1 : ℕ) a
  have : IsProbabilityMeasure μ := isProbabilityMeasure_gammaMeasure hk ha
  -- On `(0, ∞)` the kernel is the density of `μ` divided by `a ^ (k + 1)`.
  have hd (u : ℝ) (hu : u ∈ Ioi 0 \ Icc U V) := Nat.add_sub_cancel k 1 ▸
    Probability.gammaPDFReal_nat_div_pow (k := k + 1) (by omega) ha.ne' (mem_Ioi.1 hu.1).le
  have hμ : ∫ u in (Icc U V)ᶜ, gammaPDFReal (k + 1 : ℕ) a u = μ.real (Icc U V)ᶜ := by
    rw [← integral_indicator_one measurableSet_Icc.compl,
      Probability.integral_gammaMeasure_eq hk ha, ← integral_indicator measurableSet_Icc.compl]
    congr 1 with u
    by_cases hu : u ∈ (Icc U V)ᶜ <;> simp [hu]
  -- The Chernoff bounds for `μ` at `l₁` and at `-l₂`.
  have hup := (measure_ge_le_exp_mul_mgf (μ := μ) (X := id) V hl₁
    (Probability.integrable_exp_mul_id_gammaMeasure hk ha hla)).trans_eq
    (by rw [Probability.mgf_id_gammaMeasure hk ha hla])
  have hlow := (measure_le_le_exp_mul_mgf (μ := μ) (X := id) U (neg_nonpos.2 hl₂)
    (Probability.integrable_exp_mul_id_gammaMeasure hk ha (by linarith))).trans_eq
    (by rw [Probability.mgf_id_gammaMeasure hk ha (by linarith)])
  rw [setIntegral_congr_fun (measurableSet_Ioi.diff measurableSet_Icc) fun u hu ↦ (hd u hu).symm,
    integral_div]
  calc _ ≤ μ.real (Icc U V)ᶜ / a ^ (k + 1) := by
        rw [← hμ]
        gcongr
        exacts [ae_of_all _ (gammaPDFReal_nonneg hk ha),
          (Probability.integrable_gammaPDFReal hk ha).integrableOn, sdiff_subset_compl _ _]
    _ ≤ (μ.real {x | V ≤ x} + μ.real {x | x ≤ U}) / a ^ (k + 1) := by
        refine div_le_div_of_nonneg_right ((measureReal_mono fun u hu ↦ ?_).trans
          (measureReal_union_le _ _)) (by positivity)
        rw [mem_compl_iff, mem_Icc, not_and_or, not_le, not_le] at hu
        exact hu.symm.imp le_of_lt le_of_lt
    _ ≤ (exp (-l₁ * V) * (1 - l₁ / a) ^ (-((k + 1 : ℕ) : ℝ)) +
        exp (- -l₂ * U) * (1 - -l₂ / a) ^ (-((k + 1 : ℕ) : ℝ))) / a ^ (k + 1) := by
        gcongr
        exacts [hup, hlow]
    _ = _ := by
        have : 0 < a - l₁ := by linarith
        rw [neg_neg, neg_div, sub_neg_eq_add, one_sub_div ha.ne', one_add_div ha.ne',
          rpow_neg (by positivity), rpow_neg (by positivity), rpow_natCast, rpow_natCast,
          div_pow, div_pow]
        field_simp

/-- For degree `k = ⌈a √L U⌉`, the Gamma kernel outside `[U, L U]` is bounded by
`(a ^ k)⁻¹ * q ^ k`, so its ratio to `(a ^ k)⁻¹` decays exponentially in `k`. The factor `q`
is the larger of the profile values at `1 / √L` and `L^(1/4)`. The lower bound on `U` leaves
room to round the degree up. -/
theorem pow_mul_exp_neg_mul_div_factorial_le_off_window {a L U : ℝ} (hL : 1 < L)
    (ha : 1 ≤ a * √L) (hU : (a * √L * (√(√L) - 1))⁻¹ ≤ U) :
    let profile := fun t : ℝ ↦ t * exp (1 - t)
    let k := ⌈a * √L * U⌉₊
    let q := max (profile (√L)⁻¹) (profile (√(√L)))
    0 < q ∧ q < 1 ∧ U ≤ (k : ℝ) ∧
      ∀ u ≥ 0, u ∉ Icc U (L * U) →
        u ^ k * exp (-(a * u)) / (k ! : ℝ) ≤ (a ^ k)⁻¹ * q ^ k := by
  dsimp only
  set s := √L
  set r := √s
  set k := ⌈a * s * U⌉₊
  let profile := fun t : ℝ ↦ t * exp (1 - t)
  have hs : 1 < s := by simpa [s] using sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hL
  have hr : 1 < r := by simpa [r] using sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hs
  have ha₀ : 0 < a := pos_of_mul_pos_left (zero_lt_one.trans_le ha) (by positivity)
  have hsInv : s⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs
  have hden : 0 < a * s * (r - 1) := mul_pos (zero_lt_one.trans_le ha) (sub_pos.mpr hr)
  have hU₀ : 0 < U := (inv_pos.mpr hden).trans_le hU
  have hbase : a * s * U ≤ (k : ℝ) := Nat.le_ceil _
  have hkU : U ≤ (k : ℝ) := (le_mul_of_one_le_left hU₀.le ha).trans hbase
  have hk₀ : (0 : ℝ) < k := hU₀.trans_le hkU
  -- The cutoff leaves room for the ceiling between `a √L U` and `a L^(3/4) U`.
  have hkUpper : (k : ℝ) ≤ a * s * U * r := by
    have hroom := (inv_le_iff_one_le_mul₀ hden).mp hU
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ a * s * U)).le.trans (by nlinarith [hroom])
  refine ⟨lt_max_of_lt_left (by positivity : 0 < profile s⁻¹),
    max_lt (mul_exp_one_sub_lt_one hsInv.ne) (mul_exp_one_sub_lt_one hr.ne'), hkU, ?_⟩
  intro u hu hout
  let t := a * u / (k : ℝ)
  have ht : 0 ≤ t := by positivity
  have htail : profile t ≤ max (profile s⁻¹) (profile r) := by
    rcases not_and_or.mp (fun h ↦ hout (mem_Icc.mpr h)) with hl | hh
    · have ht' : t ≤ s⁻¹ := by
        dsimp only [t]
        rw [div_le_iff₀ hk₀, ← div_eq_inv_mul, le_div_iff₀ (by positivity : 0 < s)]
        have hlow : u ≤ U := le_of_not_ge hl
        calc
          a * u * s ≤ a * U * s := by gcongr
          _ = a * s * U := by ring
          _ ≤ k := hbase
      exact (strictMonoOn_mul_exp_one_sub.monotoneOn (ht'.trans hsInv.le) hsInv.le ht').trans
        (le_max_left ..)
    · have ht' : r ≤ t := by
        dsimp only [t]
        rw [le_div_iff₀ hk₀]
        calc
          r * (k : ℝ) ≤ r * (a * s * U * r) := by gcongr
          _ = a * (L * U) := by
            have hrs : r ^ 2 = s := sq_sqrt (by positivity)
            have hsL : s ^ 2 = L := sq_sqrt (by linarith)
            linear_combination hrs * (a * s * U) + hsL * (a * U)
          _ ≤ a * u := mul_le_mul_of_nonneg_left (le_of_not_ge hh) ha₀.le
      exact (strictAntiOn_mul_exp_one_sub.antitoneOn hr.le (hr.le.trans ht') ht').trans
        (le_max_right ..)
  exact (pow_mul_exp_neg_mul_div_factorial_le_profile ha₀ hu k).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg ht (exp_pos _).le) htail k) (by positivity))

end TauCeti

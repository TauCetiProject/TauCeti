/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import TauCeti.Analysis.Complex.Taylor.RapidDecay
import TauCeti.Analysis.LaplaceTransform.PostWidder
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Laplace
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.TauberianInputs

/-!
# Logarithmic decay of the signed prime remainder

At fixed modulus and odd coprime twisting prime, the signed prime remainder is smaller
than every inverse power of the logarithm. This gives a rate at which the smoothed prime
sum approaches its logarithmic main term and its specified constant.

The normalization and the Tauberian route are those of `New.eventually_abs_primeRemainder_le`
in `grh/src/New/Reduction/Zeros/PrimeNumberTheorem.lean` of lsernau/grh-lean at `72fead1`.
The approximation by Laplace coefficients uses Post–Widder inversion (Widder,
*The Laplace Transform*, Chapter VII).
-/

public section

open Filter
open scoped NNReal Topology

namespace TauCeti.OneSidedBound

/-- For an odd prime `d` coprime to `q`, the signed prime remainder with its specified centering
constant is bounded in absolute value by `(log y)⁻ᴮ` at all sufficiently large `y`. The threshold
may depend on both the modulus and the twisting prime. -/
theorem eventually_abs_primeRemainder_le {d q : ℕ} [Fact d.Prime] [NeZero q]
    (hd : d ≠ 2) (hc : q.Coprime d) (B : ℕ) :
    ∀ᶠ y : ℝ in atTop, |primeRemainder d q y| ≤ (Real.log y ^ B)⁻¹ := by
  let F : ℂ → ℂ := fun s ↦ logDerivMean d q s / s
  let R : ℝ → ℂ := fun v ↦ (primeRemainder d q (Real.exp v) : ℂ)
  have hLap (z : ℂ) (hz : 0 < z.re) : HasLaplace R z (dslope F 1 (1 + z)) := by
    have hz' : 1 < (1 + z).re := by simpa using hz
    have hne : 1 + z ≠ (1 : ℂ) := by intro he; simp [he] at hz'
    simpa only [R, F, dslope_of_ne F hne, slope_def_field, add_sub_cancel_left, div_one] using
      hasLaplace_primeRemainder hd hc hz'
  have hLip : LipschitzWith 26 R := by
    simpa only [one_mul, Function.comp_def, R] using
      Complex.isometry_ofReal.lipschitzWith.comp (lipschitzWith_primeRemainder_exp d q)
  -- Match the degree and center in the Cauchy bound and the Gamma average.
  have huv : ∀ᶠ u : ℝ in atTop, ‖R u‖ ≤ (u ^ B)⁻¹ := by
    have hC := eventually_norm_normalized_iteratedDeriv_dslope_le_inv_pow (F := F) (A := 26)
      ((eventually_analyticAt_and_norm_logDerivMean_div_le d q).mono fun _ h s hs hn ↦
        ⟨(h s hs hn).1.differentiableAt, (h s hs hn).2⟩) (2 * B + 3) (B + 1)
    filter_upwards [hC, eventually_ge_atTop (27 : ℝ)] with u hC hu
    let k := ⌊u ^ (2 * B + 3 + 1)⌋₊
    let H : ℝ := (k + 1 : ℝ) / u
    have hu₀ : 0 < u := by linarith
    have hH : 0 < H := by positivity
    have hpos : ∀ᶠ z : ℂ in 𝓝 (H : ℂ), 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simpa using hH)
    have hmean : ((k + 1 : ℕ) : ℝ) / H = u := by
      simpa [H, div_div_eq_mul_div] using mul_div_cancel_left₀ u (by positivity : (k : ℝ) + 1 ≠ 0)
    have herror := norm_smul_iteratedDeriv_sub_le_of_hasLaplace hH
      (hpos.mono hLap) hLip.lipschitzOnWith k
    rw [hmean, iteratedDeriv_comp_const_add] at herror
    have hscale : (H : ℂ) ^ (k + 1) * (-1) ^ k = (-(H : ℂ)) ^ k * H := by
      rw [neg_pow, pow_succ]; ring
    simp only [hscale, Nat.cast_add, Nat.cast_one, NNReal.coe_ofNat] at herror
    let a : ℂ := ((-(H : ℂ)) ^ k * H / k.factorial) •
      iteratedDeriv k (dslope F 1) (1 + (H : ℂ))
    have hsqrt : u ^ (B + 2) ≤ √((k : ℝ) + 1) := by
      refine (Real.le_sqrt (by positivity) (by positivity)).2 ?_
      rw [← pow_mul', show 2 * (B + 2) = 2 * B + 3 + 1 by omega]
      exact (Nat.lt_floor_add_one _).le
    have hspread : (26 : ℝ) * √((k : ℝ) + 1) / H ≤ 26 / u ^ (B + 1) := calc
      _ = 26 * u / √((k : ℝ) + 1) := by
        rw [div_div_eq_mul_div, mul_right_comm, mul_div_assoc, Real.sqrt_div_self']
        simp only [div_eq_mul_inv, one_mul]
      _ ≤ 26 * u / u ^ (B + 2) := by gcongr
      _ = 26 / u ^ (B + 1) := by rw [pow_succ']; field_simp
    calc
      _ ≤ ‖a‖ + ‖a - R u‖ := norm_le_norm_add_norm_sub a (R u)
      _ ≤ (u ^ (B + 1))⁻¹ + 26 / u ^ (B + 1) := add_le_add hC (herror.trans hspread)
      _ ≤ (u ^ B)⁻¹ := by
        rw [pow_succ' u B]
        field_simp; nlinarith only [hu, pow_pos hu₀ B]
  filter_upwards [Real.tendsto_log_atTop.eventually huv, eventually_gt_atTop (0 : ℝ)] with y hy hy₀
  simpa only [R, Real.exp_log hy₀, Complex.norm_real, Real.norm_eq_abs] using hy

end TauCeti.OneSidedBound

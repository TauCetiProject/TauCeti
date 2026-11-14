/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Deriv.Fract
public import TauCeti.Analysis.Complex.SectorBounds
public import TauCeti.Analysis.Complex.SlitPlane
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.SpecialFunctions.Integrability.Rpow
import TauCeti.Analysis.SpecialFunctions.Integrals.HalfLineRational
import TauCeti.Analysis.SpecialFunctions.Pow.ParametricIntegral

/-!
# Periodic-quadratic Stieltjes integrals on the slit plane

For `j : ℕ` and `z : ℂ`, this module studies the periodic-quadratic Stieltjes integral family

`∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (z + t) ^ (j + 2) dt`,

which governs the improper remainder in the Euler–Maclaurin expansion of `Complex.digamma` (`j = 1`)
and of `TauCeti.stirlingRemainder` together with all of its higher derivatives (`j ≥ 0`).

Because `0 ≤ (fract t - fract t ^ 2) / 2 ≤ 1 / 8` and `‖z + t‖` grows linearly on compact subsets
of `Complex.slitPlane`, every compact `K ⊆ slitPlane` admits a common integrable majorant on
`(0, ∞)`. Conversely, on `(-∞, 0]` the integrand fails to be integrable on `(0, ∞)` — even at a
nonpositive integer `z = -n`, where `fract t - fract t ^ 2` vanishes to first order at `t = n` and
leaves a non-integrable pole of order `j + 1 ≥ 1`. Rewriting `(z + t) ^ (-(j + 2))` as a principal
power and applying `TauCeti.hasDerivAt_integral_mul_ofReal_add_cpow` differentiates the family
under the integral sign on `slitPlane`, and combining the sharp half-angle inequality
`cos (arg z / 2) * (‖z‖ + t) ≤ ‖z + t‖` with `TauCeti.integral_Ioi_one_div_add_pow` yields Nemes's
explicit upper bound on the integral norm.

## Main declarations

* `TauCeti.exists_integrableOn_Ioi_majorant_fract_sub_fract_sq_div_add_pow`: every compact subset
  of `slitPlane` admits a common integrable majorant on `(0, ∞)`.
* `TauCeti.integrableOn_Ioi_fract_sub_fract_sq_div_add_pow_iff`: the periodic-quadratic Stieltjes
  integrand of order `j + 2` is integrable on `(0, ∞)` if and only if `z ∈ slitPlane`.
* `TauCeti.hasDerivAt_integral_fract_sub_fract_sq_div_add_pow`: differentiation under the integral
  sign for the periodic-quadratic Stieltjes family on `slitPlane`.
* `TauCeti.norm_integral_Ioi_fract_sub_fract_sq_div_add_pow_le`: Nemes's explicit slit-plane bound
  for the periodic-quadratic Stieltjes integral of order `j + 2`.

## References

* G. Nemes, *Error bounds and exponential improvements for the asymptotic expansions of the gamma
  function and its reciprocal*, Proc. Roy. Soc. Edinburgh Sect. A **145** (2015), 571–596, §2.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, 4th ed., §12.33.
-/

public section

open Complex Real Set MeasureTheory

namespace TauCeti

private noncomputable abbrev fractQuad (t : ℝ) : ℝ :=
  (Int.fract t - Int.fract t ^ 2) / 2

private theorem fractQuad_nonneg (t : ℝ) : 0 ≤ fractQuad t :=
  div_nonneg (Int.fract_sub_fract_sq_nonneg t) zero_le_two

private theorem fractQuad_le (t : ℝ) : fractQuad t ≤ 1 / 8 := by
  dsimp [fractQuad]
  linarith [Int.fract_sub_fract_sq_le t]

private theorem aestronglyMeasurable_stieltjesIntegrand {z : ℂ} (hz : z ∈ slitPlane) (j : ℕ) :
    AEStronglyMeasurable
      (fun t : ℝ ↦ (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ (j + 2))
      (volume.restrict (Ioi 0)) :=
  (((continuous_ofReal.comp (Int.continuous_fract_sub_fract_sq.div_const 2)).continuousOn.div
    ((continuousOn_const.add continuous_ofReal.continuousOn).pow (j + 2))
    fun t ht ↦ pow_ne_zero _ (mem_slitPlane_iff_add_ofReal_ne_zero.mp hz t (mem_Ioi.mp ht).le))
      |>.aestronglyMeasurable measurableSet_Ioi)

private theorem not_integrableOn_of_neg_nat (n j : ℕ) :
    ¬ IntegrableOn
      (fun t : ℝ ↦ (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (-(n : ℂ) + t) ^ (j + 2))
      (Ioi 0) := by
  intro h
  have hsub : Ioo (n : ℝ) (n + 1 / 2) ⊆ Ioi 0 :=
    fun t ht ↦ mem_Ioi.mpr (lt_of_le_of_lt (Nat.cast_nonneg n) ht.1)
  have hm1 : IntegrableOn (fun t : ℝ ↦ (1 / 4 : ℝ) * (t - n) ^ (-1 : ℝ))
      (Ioo (n : ℝ) (n + 1 / 2)) := by
    refine (h.mono_set hsub).re.mono' (((ContinuousOn.rpow_const
      (s := Ioo (n : ℝ) (n + 1 / 2)) (f := fun t : ℝ ↦ t - n) (by fun_prop)
      fun t ht ↦ Or.inl (by linarith [ht.1])).const_mul _).aestronglyMeasurable
      measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    set u : ℝ := t - n
    have hu0 : 0 < u := by dsimp [u]; linarith [ht.1]
    have huhalf : u < 1 / 2 := by dsimp [u]; linarith [ht.2]
    have hfr : Int.fract t = u := by
      have ht_eq : t = u + (n : ℤ) := by dsimp [u]; push_cast; ring
      rw [ht_eq, Int.fract_add_intCast]
      exact Int.fract_eq_self.mpr ⟨hu0.le, by linarith⟩
    have hzn : -(n : ℂ) + (t : ℂ) = (u : ℂ) := by dsimp [u]; push_cast; ring
    have hval : RCLike.re ((((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) /
        (-(n : ℂ) + t) ^ (j + 2)) = (u - u ^ 2) / (2 * u ^ (j + 2)) := by
      rw [RCLike.re_eq_complex_re, hzn, ← ofReal_pow, ← ofReal_div, ofReal_re, hfr, div_div]
    rw [hval, Real.norm_of_nonneg (by positivity), rpow_neg_one]
    have hpow : u ^ (j + 2) ≤ u ^ 2 := pow_le_pow_of_le_one hu0.le (by linarith) (by omega)
    calc
      (1 / 4 : ℝ) * u⁻¹ = (u / 2) / (2 * u ^ 2) := by field_simp; ring
      _ ≤ (u - u ^ 2) / (2 * u ^ 2) := div_le_div_of_nonneg_right (by nlinarith) (by positivity)
      _ ≤ (u - u ^ 2) / (2 * u ^ (j + 2)) :=
        div_le_div_of_nonneg_left (by nlinarith) (by positivity) (by gcongr)
  have hrpow : IntegrableOn (fun t : ℝ ↦ (t - (n : ℝ)) ^ (-1 : ℝ)) (Ioo (n : ℝ) (n + 1 / 2)) :=
    IntegrableOn.congr_fun (hm1.const_mul 4) (fun t _ ↦ by ring) measurableSet_Ioo
  linarith [(integrableOn_Ioo_sub_rpow_iff (by linarith : (n : ℝ) < n + 1 / 2)).mp hrpow]

private theorem not_integrableOn_of_neg_nonint {x : ℝ} (hx : 0 ≤ x) (hnat : ∀ n : ℕ, x ≠ n)
    (j : ℕ) :
    ¬ IntegrableOn
      (fun t : ℝ ↦ (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (-(x : ℂ) + t) ^ (j + 2))
      (Ioi 0) := by
  intro h
  have hfx0 : Int.fract x ≠ 0 := by
    rw [ne_eq, Int.fract_eq_zero_iff]
    rintro ⟨m, rfl⟩
    have hm : 0 ≤ m := by exact_mod_cast hx
    exact hnat m.toNat (by exact_mod_cast (Int.toNat_of_nonneg hm).symm)
  have hfx_pos : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) hfx0.symm
  have hq_pos : 0 < fractQuad x := by dsimp [fractQuad]; nlinarith [Int.fract_lt_one x]
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp
    ((Int.continuous_fract_sub_fract_sq.div_const 2).continuousAt (x := x))
    (fractQuad x / 2) (half_pos hq_pos)
  set r : ℝ := min δ 1
  have hr_pos : 0 < r := lt_min hδ_pos one_pos
  have hr1 : r ≤ 1 := min_le_right _ _
  have hsub : Ioo x (x + r) ⊆ Ioi 0 := fun t ht ↦ mem_Ioi.mpr (lt_of_le_of_lt hx ht.1)
  have hm1 : IntegrableOn (fun t : ℝ ↦ fractQuad x / 2 * (t - x) ^ (-1 : ℝ))
      (Ioo x (x + r)) := by
    refine (h.mono_set hsub).re.mono' (((ContinuousOn.rpow_const (s := Ioo x (x + r))
      (f := fun t : ℝ ↦ t - x) (by fun_prop)
      fun t ht ↦ Or.inl (by linarith [ht.1])).const_mul _).aestronglyMeasurable
      measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    set u : ℝ := t - x
    have hu0 : 0 < u := by dsimp [u]; linarith [ht.1]
    have hu1 : u ≤ 1 := by dsimp [u]; linarith [ht.2, hr1]
    have hdist : dist t x < δ := by
      rw [Real.dist_eq, abs_of_pos hu0]
      exact lt_of_lt_of_le (by dsimp [u]; linarith [ht.2]) (min_le_left _ _)
    have hqt : fractQuad x / 2 ≤ fractQuad t := by
      have := abs_lt.mp (Real.dist_eq (fractQuad t) (fractQuad x) ▸ hδ hdist)
      linarith
    have hzx : -(x : ℂ) + (t : ℂ) = (u : ℂ) := by dsimp [u]; push_cast; ring
    have hval : RCLike.re ((((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) /
        (-(x : ℂ) + t) ^ (j + 2)) = fractQuad t / u ^ (j + 2) := by
      rw [RCLike.re_eq_complex_re, hzx, ← ofReal_pow, ← ofReal_div, ofReal_re]
    have hq_nn := fractQuad_nonneg t
    rw [hval, Real.norm_of_nonneg (by positivity), rpow_neg_one]
    calc
      fractQuad x / 2 * u⁻¹ = (fractQuad x / 2) / u := div_eq_mul_inv _ _
      _ ≤ fractQuad t / u := div_le_div_of_nonneg_right hqt hu0.le
      _ ≤ fractQuad t / u ^ (j + 2) :=
        div_le_div_of_nonneg_left hq_nn (pow_pos hu0 _)
          (pow_le_of_le_one hu0.le hu1 (Nat.succ_ne_zero _))
  have hrpow : IntegrableOn (fun t : ℝ ↦ (t - x) ^ (-1 : ℝ)) (Ioo x (x + r)) :=
    IntegrableOn.congr_fun (hm1.const_mul (fractQuad x / 2)⁻¹)
      (fun t _ ↦ inv_mul_cancel_left₀ (half_pos hq_pos).ne' _) measurableSet_Ioo
  linarith [(integrableOn_Ioo_sub_rpow_iff (by linarith : x < x + r)).mp hrpow]

/-- Every compact subset `K ⊆ slitPlane` admits a common integrable majorant on `(0, ∞)` for the
periodic-quadratic Stieltjes kernel of order `j + 2`. -/
theorem exists_integrableOn_Ioi_majorant_fract_sub_fract_sq_div_add_pow {K : Set ℂ}
    (hK : IsCompact K) (hsub : K ⊆ slitPlane) (j : ℕ) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧ ∀ z ∈ K, ∀ t ∈ Ioi (0 : ℝ),
      ‖(((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ (j + 2)‖ ≤ g t := by
  obtain ⟨c, hc, hden⟩ := exists_pos_forall_mem_mul_one_add_le_norm_add_of_isCompact hK hsub
  refine ⟨fun t ↦ (8 * c ^ (j + 2))⁻¹ * (1 / (1 + t) ^ (j + 2)),
    (integrableOn_Ioi_one_div_add_pow_iff.mpr one_pos).const_mul _, fun z hz t ht ↦ ?_⟩
  have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
  have hpow : (c * (1 + t)) ^ (j + 2) ≤ ‖z + t‖ ^ (j + 2) :=
    pow_le_pow_left₀ (by positivity) (hden z hz t ht0) (j + 2)
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (fractQuad_nonneg t)]
  calc
    fractQuad t / ‖z + t‖ ^ (j + 2) ≤ (1 / 8) / (c * (1 + t)) ^ (j + 2) :=
      div_le_div₀ (by norm_num) (fractQuad_le t) (by positivity) hpow
    _ = (8 * c ^ (j + 2))⁻¹ * (1 / (1 + t) ^ (j + 2)) := by
      rw [mul_pow]
      field_simp

/-- The periodic-quadratic Stieltjes integrand `((fract t - fract t ^ 2) / 2) / (z + t) ^ (j + 2)`
is integrable on `(0, ∞)` if and only if `z ∈ slitPlane`. Even at nonpositive integers `z = -n`,
where `fract t - fract t ^ 2` vanishes to first order at `t = n`, a non-integrable pole of order
`j + 1 ≥ 1` remains. -/
theorem integrableOn_Ioi_fract_sub_fract_sq_div_add_pow_iff {z : ℂ} {j : ℕ} :
    IntegrableOn
      (fun t : ℝ ↦ (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ (j + 2))
      (Ioi 0) ↔ z ∈ slitPlane := by
  refine ⟨fun h ↦ ?_, fun hz ↦ ?_⟩
  · by_contra hz
    have him : z.im = 0 := im_eq_zero_of_notMem_slitPlane hz
    have hre : z.re ≤ 0 := le_of_not_gt fun hpos ↦ hz (mem_slitPlane_iff.mpr (Or.inl hpos))
    set x : ℝ := -z.re
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hz_eq : z = -(x : ℂ) := by
      apply Complex.ext <;> simp [x, him]
    rw [hz_eq] at h
    by_cases hnat : ∃ n : ℕ, x = n
    · obtain ⟨n, hn⟩ := hnat
      rw [hn] at h
      exact not_integrableOn_of_neg_nat n j (by simpa using h)
    · push Not at hnat
      exact not_integrableOn_of_neg_nonint hx hnat j h
  · obtain ⟨g, hg, hle⟩ := exists_integrableOn_Ioi_majorant_fract_sub_fract_sq_div_add_pow
      isCompact_singleton (singleton_subset_iff.mpr hz) j
    refine hg.mono' (aestronglyMeasurable_stieltjesIntegrand hz j) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hle z (mem_singleton z) t ht

/-- Differentiation under the integral sign for the periodic-quadratic Stieltjes family on
`slitPlane`. -/
theorem hasDerivAt_integral_fract_sub_fract_sq_div_add_pow {z : ℂ} (hz : z ∈ slitPlane) (j : ℕ) :
    HasDerivAt
      (fun w : ℂ ↦
        ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (w + t) ^ (j + 2))
      (-(j + 2 : ℂ) *
        ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ (j + 3))
      z := by
  let g : ℝ → ℂ := fun t ↦ (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ)
  have hcpow (w : ℂ) (t : ℝ) (n : ℕ) :
      g t * ((t : ℂ) + w) ^ (-((n : ℕ) : ℂ)) = g t / (w + t) ^ n := by
    rw [Complex.cpow_neg, Complex.cpow_natCast, add_comm (t : ℂ) w, div_eq_mul_inv]
  have hg_int :
      IntegrableOn (fun t : ℝ ↦ g t * ((t : ℂ) + z) ^ (-(((j + 2 : ℕ) : ℂ)))) (Ioi 0) :=
    (integrableOn_Ioi_fract_sub_fract_sq_div_add_pow_iff.mpr hz).congr_fun
      (fun t _ ↦ (hcpow z t (j + 2)).symm) measurableSet_Ioi
  have hd := hasDerivAt_integral_mul_ofReal_add_cpow hz hg_int
  have hfun :
      (fun w : ℂ ↦ ∫ t : ℝ in Ioi 0, g t * ((t : ℂ) + w) ^ (-(((j + 2 : ℕ) : ℂ)))) =
        fun w : ℂ ↦ ∫ t : ℝ in Ioi 0, g t / (w + t) ^ (j + 2) := by
    ext w
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ hcpow w t (j + 2)
  rw [hfun] at hd
  refine hd.congr_deriv ?_
  have hs1 : -(((j + 2 : ℕ) : ℂ)) - 1 = -(((j + 3 : ℕ) : ℂ)) := by push_cast; ring
  have hs0 : -(((j + 2 : ℕ) : ℂ)) = -(j + 2 : ℂ) := by push_cast; ring
  rw [hs1, hs0]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ hcpow z t (j + 3)

/-- Nemes's explicit slit-plane bound for the periodic-quadratic Stieltjes integral of order `j + 2`
(for `z ∉ slitPlane` the integrand is not integrable and the left-hand side vanishes):
`‖∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (z + t) ^ (j + 2) dt‖ ≤
  1 / (8 * (j + 1) * cos (arg z / 2) ^ (j + 2) * ‖z‖ ^ (j + 1))`. -/
theorem norm_integral_Ioi_fract_sub_fract_sq_div_add_pow_le (j : ℕ) (z : ℂ) :
    ‖∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ (j + 2)‖ ≤
      1 / (8 * (j + 1 : ℝ) * Real.cos (z.arg / 2) ^ (j + 2) * ‖z‖ ^ (j + 1)) := by
  by_cases hz : z ∈ slitPlane
  · have hc : 0 < Real.cos (z.arg / 2) := cos_half_arg_pos hz
    have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hz)
    let g : ℝ → ℝ := fun t ↦ (8 * Real.cos (z.arg / 2) ^ (j + 2))⁻¹ * (1 / (‖z‖ + t) ^ (j + 2))
    have hg_int : IntegrableOn g (Ioi 0) :=
      (integrableOn_Ioi_one_div_add_pow_iff.mpr hz0).const_mul _
    have hle :
        ‖∫ t : ℝ in Ioi 0,
            (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ (j + 2)‖ ≤
          ∫ t : ℝ in Ioi 0, g t := by
      refine MeasureTheory.norm_integral_le_of_norm_le hg_int ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
      have hden := cos_half_arg_mul_norm_add_le_norm_add_ofReal z t
      have hpow : (Real.cos (z.arg / 2) * (‖z‖ + t)) ^ (j + 2) ≤ ‖z + t‖ ^ (j + 2) :=
        pow_le_pow_left₀ (by positivity) hden (j + 2)
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (fractQuad_nonneg t)]
      calc
        fractQuad t / ‖z + t‖ ^ (j + 2)
            ≤ (1 / 8) / (Real.cos (z.arg / 2) * (‖z‖ + t)) ^ (j + 2) :=
          div_le_div₀ (by norm_num) (fractQuad_le t) (by positivity) hpow
        _ = g t := by
          dsimp [g]
          rw [mul_pow]
          field_simp
    refine hle.trans_eq ?_
    dsimp [g]
    rw [integral_const_mul, integral_Ioi_one_div_add_pow hz0.le j]
    field_simp
  · rw [integral_undef (mt integrableOn_Ioi_fract_sub_fract_sq_div_add_pow_iff.mp hz), norm_zero]
    have hcos : 0 ≤ Real.cos (z.arg / 2) := cos_half_arg_nonneg z
    positivity

end TauCeti

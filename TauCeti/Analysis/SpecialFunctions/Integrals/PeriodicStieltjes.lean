/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Deriv.Fract
public import TauCeti.Analysis.Complex.Sector.Bounds
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
* `TauCeti.norm_integral_Ioi_fract_sub_fract_sq_div_add_pow_le`,
  `TauCeti.norm_integral_Ioi_fract_sub_fract_sq_div_add_pow_le_of_abs_arg_le`: Nemes's explicit
  slit-plane and closed-sector bounds for the periodic-quadratic Stieltjes integral of order
  `j + 2`.

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

/-- For every `x ≥ 0` (integer or non-integer), the periodic-quadratic Stieltjes integrand at
`z = -x` dominates `(r / 2) * (t - x)⁻¹` on `(x, x + r)` with `r = (1 - fract x) / 2`, so it fails
to be integrable on `(0, ∞)`. -/
private theorem not_integrableOn_of_neg_ofReal {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    ¬ IntegrableOn
      (fun t : ℝ ↦ (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (-(x : ℂ) + t) ^ (j + 2))
      (Ioi 0) := by
  intro h
  set r : ℝ := (1 - Int.fract x) / 2
  have hr_pos : 0 < r := half_pos (sub_pos.mpr (Int.fract_lt_one x))
  have hr_le : r ≤ 1 / 2 := by dsimp [r]; linarith [Int.fract_nonneg x]
  have hsub : Ioo x (x + r) ⊆ Ioi 0 := fun t ht ↦ mem_Ioi.mpr (lt_of_le_of_lt hx ht.1)
  have hm1 : IntegrableOn (fun t : ℝ ↦ (r / 2) * (t - x) ^ (-1 : ℝ)) (Ioo x (x + r)) := by
    refine (h.mono_set hsub).re.mono' (((ContinuousOn.rpow_const (s := Ioo x (x + r))
      (f := fun t : ℝ ↦ t - x) (by fun_prop)
      fun t ht ↦ Or.inl (by linarith [ht.1])).const_mul _).aestronglyMeasurable
      measurableSet_Ioo) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    set u : ℝ := t - x
    have hu0 : 0 < u := by dsimp [u]; linarith [ht.1]
    have hur : u < r := by dsimp [u]; linarith [ht.2]
    -- On `(x, x + r)` we have `fract t = fract x + u`, giving `fractQuad t ≥ r * u / 2` and
    -- `u ^ (j + 2) ≤ u ^ 2`, hence `fractQuad t / u ^ (j + 2) ≥ (r / 2) * u⁻¹`.
    have hfr : Int.fract t = Int.fract x + u := by
      have ht_eq : t = (Int.fract x + u) + (⌊x⌋ : ℤ) := by
        dsimp [u]; linarith [Int.floor_add_fract x]
      rw [ht_eq, Int.fract_add_intCast]
      exact Int.fract_eq_self.mpr
        ⟨by linarith [Int.fract_nonneg x], by dsimp [r] at hur; linarith [Int.fract_lt_one x]⟩
    have hzx : -(x : ℂ) + (t : ℂ) = (u : ℂ) := by dsimp [u]; push_cast; ring
    have hval : RCLike.re ((((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) /
        (-(x : ℂ) + t) ^ (j + 2)) = fractQuad t / u ^ (j + 2) := by
      rw [RCLike.re_eq_complex_re, hzx, ← ofReal_pow, ← ofReal_div, ofReal_re]
    have hq_lb : r * u / 2 ≤ fractQuad t := by
      have h1 : r ≤ 1 - (Int.fract x + u) := by dsimp [r] at hur ⊢; linarith
      have h2 : u ≤ Int.fract x + u := by linarith [Int.fract_nonneg x]
      have hfac : fractQuad t = (Int.fract x + u) * (1 - (Int.fract x + u)) / 2 := by
        dsimp [fractQuad]; rw [hfr]; ring
      rw [hfac]
      linarith [mul_le_mul h2 h1 hr_pos.le (by linarith [Int.fract_nonneg x])]
    have hpow : u ^ (j + 2) ≤ u ^ 2 :=
      pow_le_pow_of_le_one hu0.le (by linarith) (by omega)
    rw [hval, Real.norm_of_nonneg (by positivity), rpow_neg_one]
    calc
      (r / 2) * u⁻¹ = (r * u / 2) / u ^ 2 := by field_simp
      _ ≤ fractQuad t / u ^ 2 := div_le_div_of_nonneg_right hq_lb (by positivity)
      _ ≤ fractQuad t / u ^ (j + 2) :=
        div_le_div_of_nonneg_left (fractQuad_nonneg t) (by positivity) hpow
  -- Rescale to contradict non-integrability of `(t - x) ^ (-1)` on `(x, x + r)`.
  have hrpow : IntegrableOn (fun t : ℝ ↦ (t - x) ^ (-1 : ℝ)) (Ioo x (x + r)) :=
    IntegrableOn.congr_fun (hm1.const_mul (r / 2)⁻¹)
      (fun t _ ↦ inv_mul_cancel_left₀ (half_pos hr_pos).ne' _) measurableSet_Ioo
  linarith [(integrableOn_Ioo_sub_rpow_iff (by linarith : x < x + r)).mp hrpow]

private theorem norm_stieltjesIntegrand_le {z : ℂ} {a c t : ℝ} (ha : 0 < a) (hc : 0 < c)
    (ht : 0 ≤ t) (hden : c * (a + t) ≤ ‖z + t‖) (j : ℕ) :
    ‖(((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ (j + 2)‖ ≤
      (8 * c ^ (j + 2))⁻¹ * (1 / (a + t) ^ (j + 2)) := by
  have hpow : (c * (a + t)) ^ (j + 2) ≤ ‖z + t‖ ^ (j + 2) :=
    pow_le_pow_left₀ (by positivity) hden (j + 2)
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (fractQuad_nonneg t)]
  calc
    fractQuad t / ‖z + t‖ ^ (j + 2) ≤ (1 / 8) / (c * (a + t)) ^ (j + 2) :=
      div_le_div₀ (by norm_num) (fractQuad_le t) (by positivity) hpow
    _ = (8 * c ^ (j + 2))⁻¹ * (1 / (a + t) ^ (j + 2)) := by
      rw [mul_pow]
      field_simp

/-- Every compact subset `K ⊆ slitPlane` admits a common integrable majorant on `(0, ∞)` for the
periodic-quadratic Stieltjes kernel of order `j + 2`. -/
theorem exists_integrableOn_Ioi_majorant_fract_sub_fract_sq_div_add_pow {K : Set ℂ}
    (hK : IsCompact K) (hsub : K ⊆ slitPlane) (j : ℕ) :
    ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧ ∀ z ∈ K, ∀ t ∈ Ioi (0 : ℝ),
      ‖(((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ (j + 2)‖ ≤ g t := by
  obtain ⟨c, hc, hden⟩ := exists_pos_forall_mem_mul_one_add_le_norm_add_of_isCompact hK hsub
  exact ⟨fun t ↦ (8 * c ^ (j + 2))⁻¹ * (1 / (1 + t) ^ (j + 2)),
    (integrableOn_Ioi_one_div_add_pow_iff.mpr one_pos).const_mul _,
    fun z hz t ht ↦ norm_stieltjesIntegrand_le one_pos hc (mem_Ioi.mp ht).le
      (hden z hz t (mem_Ioi.mp ht).le) j⟩

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
    rw [mem_slitPlane_iff_add_ofReal_ne_zero] at hz
    push Not at hz
    obtain ⟨x, hx, hzx⟩ := hz
    rw [eq_neg_of_add_eq_zero_left hzx] at h
    exact not_integrableOn_of_neg_ofReal hx j h
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
      exact norm_stieltjesIntegrand_le hz0 hc (mem_Ioi.mp ht).le
        (cos_half_arg_mul_norm_add_le_norm_add_ofReal z t) j
    refine hle.trans_eq ?_
    dsimp [g]
    rw [integral_const_mul, integral_Ioi_one_div_add_pow hz0.le j]
    field_simp
  · rw [integral_undef (mt integrableOn_Ioi_fract_sub_fract_sq_div_add_pow_iff.mp hz), norm_zero]
    have hcos : 0 ≤ Real.cos (z.arg / 2) := cos_half_arg_nonneg z
    positivity

/-- Nemes's explicit closed-sector bound for the periodic-quadratic Stieltjes integral of order
`j + 2`: for `0 < δ` and `|arg z| ≤ π - δ`,
`‖∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (z + t) ^ (j + 2) dt‖ ≤
  1 / (8 * (j + 1) * sin (δ / 2) ^ (j + 2) * ‖z‖ ^ (j + 1))`. -/
theorem norm_integral_Ioi_fract_sub_fract_sq_div_add_pow_le_of_abs_arg_le (j : ℕ) {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : |z.arg| ≤ Real.pi - δ) :
    ‖∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ (j + 2)‖ ≤
      1 / (8 * (j + 1 : ℝ) * Real.sin (δ / 2) ^ (j + 2) * ‖z‖ ^ (j + 1)) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [integral_undef
      (mt (integrableOn_Ioi_fract_sub_fract_sq_div_add_pow_iff (z := 0) (j := j)).mp (by simp))]
    simp
  · have hδπ : δ ≤ Real.pi := by linarith [abs_nonneg z.arg]
    have : 0 < Real.sin (δ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (half_pos hδ) (by linarith [Real.pi_pos])
    have : Real.sin (δ / 2) ≤ Real.cos (z.arg / 2) :=
      sin_half_le_cos_half_arg_of_abs_arg_le hδ.le hz
    have : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    exact (norm_integral_Ioi_fract_sub_fract_sq_div_add_pow_le j z).trans (by gcongr)

end TauCeti

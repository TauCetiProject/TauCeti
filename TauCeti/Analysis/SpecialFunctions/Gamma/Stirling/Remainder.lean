/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.SpecialFunctions.Integrals.HalfLineRational

/-!
# Stieltjes representation and higher derivatives of the Stirling remainder

On the slit plane `ℂ ∖ (-∞, 0]`, the remainder
`stirlingRemainder z = logGamma z - ((z - 1 / 2) * log z - z + log (2π) / 2)`
in Stirling's formula is given by the periodic-quadratic Stieltjes integral
`stirlingRemainder z = ∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (z + t) ^ 2 dt`.

Differentiating under the integral sign `j` times via local integrable majorants on `slitPlane`
yields, for every `j : ℕ` and `z ∈ slitPlane`,
`iteratedDeriv j stirlingRemainder z =
  (-1) ^ j * (j + 1)! * ∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (z + t) ^ (j + 2) dt`.

Combining `0 ≤ (fract t - fract t ^ 2) / 2 ≤ 1 / 8` with the sharp half-angle lower bound
`cos (arg z / 2) * (‖z‖ + t) ≤ ‖z + t‖` and the exact half-line evaluation
`∫_{t > 0} 1 / (a + t) ^ (j + 2) dt = 1 / ((j + 1) * a ^ (j + 1))` gives Nemes's explicit bound on
the whole slit plane:
`‖iteratedDeriv j stirlingRemainder z‖ ≤ j! / (8 * cos (arg z / 2) ^ (j + 2) * ‖z‖ ^ (j + 1))`.
On any closed sector `|arg z| ≤ π - δ` (`0 < δ`, `z ≠ 0`) this specializes to
`‖iteratedDeriv j stirlingRemainder z‖ ≤ j! / (8 * sin (δ / 2) ^ (j + 2) * ‖z‖ ^ (j + 1))`,
and hence `iteratedDeriv j stirlingRemainder =O ‖z‖ ^ (-(j + 1))` as `z → ∞` in the sector.
Along the positive real axis `(0, ∞)`, `iteratedDeriv j stirlingRemainder` is real-valued and
strictly alternates in sign: `0 < (-1) ^ j * (iteratedDeriv j stirlingRemainder x).re ≤
j! / (8 * x ^ (j + 1))`; in particular `(stirlingRemainder x).re > 0` and
`(deriv stirlingRemainder x).re < 0` for `x > 0`.

## Main declarations

* `TauCeti.integrableOn_Ioi_fract_sub_fract_sq_div_add_pow_iff`: the periodic-quadratic Stieltjes
  integrand of order `j + 2` is integrable on `(0, ∞)` if and only if `z ∈ slitPlane`.
* `TauCeti.exists_integrableOn_Ioi_majorant_fract_sub_fract_sq_div_add_pow`: every compact subset
  of `slitPlane` admits a common integrable majorant on `(0, ∞)`.
* `TauCeti.hasDerivAt_integral_fract_sub_fract_sq_div_add_pow`: differentiation under the integral
  sign for the periodic-quadratic Stieltjes family on `slitPlane`.
* `TauCeti.stirlingRemainder_eq_integral`: Stieltjes integral representation of
  `stirlingRemainder` on `slitPlane`.
* `TauCeti.iteratedDeriv_stirlingRemainder`, `TauCeti.iteratedDeriv_succ_stirlingRemainder`:
  integral representation of all iterated derivatives of `stirlingRemainder` and identification
  with iterated derivatives of `digamma z - log z + (2 * z)⁻¹`.
* `TauCeti.norm_iteratedDeriv_stirlingRemainder_le`,
  `TauCeti.norm_iteratedDeriv_stirlingRemainder_le_of_abs_arg_le`,
  `TauCeti.isBigO_iteratedDeriv_stirlingRemainder`: Nemes's sharp slit-plane and sector bounds for
  all `j : ℕ`, with specializations `TauCeti.norm_stirlingRemainder_le`,
  `TauCeti.norm_deriv_stirlingRemainder_le`, and `Complex.norm_digamma_sub_log_add_inv_two_mul_le`.
* `TauCeti.iteratedDeriv_stirlingRemainder_ofReal_im`,
  `TauCeti.mul_iteratedDeriv_stirlingRemainder_ofReal_re_pos`,
  `TauCeti.deriv_stirlingRemainder_ofReal_re_neg`: real-valuedness and strict sign alternation on
  `(0, ∞)`.

## References

* G. Nemes, *Error bounds and exponential improvements for the asymptotic expansions of the gamma
  function and its reciprocal*, Proc. Roy. Soc. Edinburgh Sect. A **145** (2015), 571–596, §2
  (eq. (2.5) and Lemma 2.1).
* [F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §5.11][dlmf_5_11]
  (<https://dlmf.nist.gov/5.11>).
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, 4th ed., §12.33.
-/

public section

open Complex Real Filter Set Topology MeasureTheory Asymptotics Bornology
open scoped NNReal

namespace TauCeti

/-! ### Periodic-quadratic Stieltjes kernel: integrability and parametric differentiation -/

private noncomputable abbrev fractQuad (t : ℝ) : ℝ :=
  (Int.fract t - Int.fract t ^ 2) / 2

private theorem continuous_fractQuad : Continuous fractQuad := by
  refine (Int.continuous_fract_sq_sub_fract.neg.div_const 2).congr fun t ↦ ?_
  dsimp [fractQuad]
  ring

private theorem fractQuad_nonneg (t : ℝ) : 0 ≤ fractQuad t :=
  div_nonneg (Int.fract_sub_fract_sq_nonneg t) zero_le_two

private theorem fractQuad_le (t : ℝ) : fractQuad t ≤ 1 / 8 := by
  dsimp [fractQuad]
  linarith [Int.fract_sub_fract_sq_le t]

private theorem aestronglyMeasurable_stieltjesIntegrand {z : ℂ} (hz : z ∈ slitPlane) (j : ℕ) :
    AEStronglyMeasurable
      (fun t : ℝ ↦ (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ (j + 2))
      (volume.restrict (Ioi 0)) := by
  refine (((continuous_ofReal.comp continuous_fractQuad).continuousOn.div
    ((continuousOn_const.add continuous_ofReal.continuousOn).pow (j + 2))
    fun t ht ↦ pow_ne_zero _ ?_).aestronglyMeasurable measurableSet_Ioi)
  rw [add_comm]
  exact slitPlane_ne_zero (ofReal_add_mem_slitPlane hz (mem_Ioi.mp ht).le)

private theorem not_integrableOn_Ioo_const_mul_sub_rpow_neg_one {a c r : ℝ} (hc : 0 < c)
    (hr : 0 < r) :
    ¬ IntegrableOn (fun t : ℝ ↦ c * (t - a) ^ (-1 : ℝ)) (Ioo a (a + r)) := by
  intro hm1
  have hi : IntervalIntegrable (fun t : ℝ ↦ (t - a) ^ (-1 : ℝ)) volume a (a + r) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)]
    exact IntegrableOn.congr_fun (hm1.const_mul c⁻¹)
      (fun t _ ↦ inv_mul_cancel_left₀ hc.ne' _) measurableSet_Ioo
  have hi0 : IntervalIntegrable (fun u : ℝ ↦ u ^ (-1 : ℝ)) volume 0 r := by
    simpa using hi.comp_add_right a
  have hlt := (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mp
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le).mp hi0)
  linarith

private theorem not_integrableOn_of_neg_nat (n j : ℕ) :
    ¬ IntegrableOn
      (fun t : ℝ ↦ (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (-(n : ℂ) + t) ^ (j + 2))
      (Ioi 0) := by
  intro h
  have hsub : Ioo (n : ℝ) (n + 1 / 2) ⊆ Ioi 0 :=
    fun t ht ↦ mem_Ioi.mpr (lt_of_le_of_lt (Nat.cast_nonneg n) ht.1)
  have hre := (h.mono_set hsub).re
  refine not_integrableOn_Ioo_const_mul_sub_rpow_neg_one (a := n) (c := 1 / 4) (r := 1 / 2)
    (by norm_num) (by norm_num) ?_
  refine hre.mono' (((ContinuousOn.rpow_const (s := Ioo (n : ℝ) (n + 1 / 2))
    (f := fun t : ℝ ↦ t - n) (by fun_prop)
    fun t ht ↦ Or.inl (by linarith [ht.1])).const_mul _).aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  set u : ℝ := t - n
  have hu0 : 0 < u := by dsimp [u]; linarith [ht.1]
  have huhalf : u < 1 / 2 := by dsimp [u]; linarith [ht.2]
  have hfr : Int.fract t = u := by
    have ht_eq : t = u + (n : ℤ) := by dsimp [u]; push_cast; ring
    rw [ht_eq, Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨hu0.le, by linarith⟩
  have hval : RCLike.re ((((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) /
      (-(n : ℂ) + t) ^ (j + 2)) = (u - u ^ 2) / (2 * u ^ (j + 2)) := by
    change ((((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (-(n : ℂ) + t) ^ (j + 2)).re = _
    have hzn : -(n : ℂ) + (t : ℂ) = (u : ℂ) := by dsimp [u]; push_cast; ring
    rw [hzn, ← ofReal_pow, ← ofReal_div, ofReal_re, hfr, div_div]
  rw [hval, Real.norm_of_nonneg (by positivity), rpow_neg_one]
  have hpow : u ^ (j + 2) ≤ u ^ 2 := pow_le_pow_of_le_one hu0.le (by linarith) (by omega)
  calc
    (1 / 4 : ℝ) * u⁻¹ = (u / 2) / (2 * u ^ 2) := by field_simp; ring
    _ ≤ (u - u ^ 2) / (2 * u ^ 2) := div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    _ ≤ (u - u ^ 2) / (2 * u ^ (j + 2)) :=
      div_le_div_of_nonneg_left (by nlinarith) (by positivity) (by gcongr)

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
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp (continuous_fractQuad.continuousAt (x := x))
    (fractQuad x / 2) (half_pos hq_pos)
  set r : ℝ := min δ 1
  have hr_pos : 0 < r := lt_min hδ_pos one_pos
  have hr1 : r ≤ 1 := min_le_right _ _
  have hre := (h.mono_set (fun t ht ↦ mem_Ioi.mpr (lt_of_le_of_lt hx ht.1) :
    Ioo x (x + r) ⊆ Ioi 0)).re
  refine not_integrableOn_Ioo_const_mul_sub_rpow_neg_one (a := x) (half_pos hq_pos) hr_pos ?_
  refine hre.mono' (((ContinuousOn.rpow_const (s := Ioo x (x + r))
    (f := fun t : ℝ ↦ t - x) (by fun_prop)
    fun t ht ↦ Or.inl (by linarith [ht.1])).const_mul _).aestronglyMeasurable measurableSet_Ioo) ?_
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
  have hval : RCLike.re ((((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) /
      (-(x : ℂ) + t) ^ (j + 2)) = fractQuad t / u ^ (j + 2) := by
    change ((((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (-(x : ℂ) + t) ^ (j + 2)).re = _
    have hzx : -(x : ℂ) + (t : ℂ) = (u : ℂ) := by dsimp [u]; push_cast; ring
    rw [hzx, ← ofReal_pow, ← ofReal_div, ofReal_re]
  have hq_nn := fractQuad_nonneg t
  rw [hval, Real.norm_of_nonneg (by positivity), rpow_neg_one]
  calc
    fractQuad x / 2 * u⁻¹ = (fractQuad x / 2) / u := div_eq_mul_inv _ _
    _ ≤ fractQuad t / u := div_le_div_of_nonneg_right hqt hu0.le
    _ ≤ fractQuad t / u ^ (j + 2) :=
      div_le_div_of_nonneg_left hq_nn (pow_pos hu0 _)
        (pow_le_of_le_one hu0.le hu1 (Nat.succ_ne_zero _))

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
    have hre : z.re ≤ 0 := by
      by_contra! hpos
      exact hz (mem_slitPlane_iff.mpr (Or.inl hpos))
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

private theorem hasDerivAt_stieltjesIntegrand {w : ℂ} {t : ℝ} (hwt : w + t ≠ 0) (j : ℕ) :
    HasDerivAt
      (fun u : ℂ ↦ (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (u + t) ^ (j + 2))
      (-(j + 2 : ℂ) *
        ((((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (w + t) ^ (j + 3))) w := by
  set q : ℂ := ((fractQuad t : ℝ) : ℂ)
  have hp : HasDerivAt (fun u : ℂ ↦ (u + t) ^ (j + 2))
      ((j + 2 : ℕ) * (w + t) ^ (j + 1) * 1) w :=
    ((hasDerivAt_id' w).add_const (t : ℂ)).pow (j + 2)
  have hd := (hp.inv (pow_ne_zero _ hwt)).const_mul q
  refine (hd.congr_of_eventuallyEq (Eventually.of_forall fun u ↦ ?_)).congr_deriv ?_
  · simp [q, div_eq_mul_inv]
  · change q * (-(((j + 2 : ℕ) : ℂ) * (w + t) ^ (j + 1) * 1) / ((w + t) ^ (j + 2)) ^ 2) =
      -(j + 2 : ℂ) * (q / (w + t) ^ (j + 3))
    have hp2 : ((w + (t : ℂ)) ^ (j + 2)) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hwt)
    have hp3 : (w + (t : ℂ)) ^ (j + 3) ≠ 0 := pow_ne_zero _ hwt
    rw [← mul_div_assoc, ← mul_div_assoc, div_eq_div_iff hp2 hp3]
    push_cast
    have hexp : (w + (t : ℂ)) ^ (j + 1) * (w + t) ^ (j + 3) = ((w + t) ^ (j + 2)) ^ 2 := by
      rw [← pow_add, ← pow_mul, show j + 1 + (j + 3) = (j + 2) * 2 by omega]
    linear_combination -(j + 2 : ℂ) * q * hexp

private theorem ball_subset_slitPlane_of_mul_one_add_le {z : ℂ} {c : ℝ} (hc : 0 < c)
    (hball : ∀ w ∈ Metric.ball z c, ∀ t : ℝ≥0, c * (1 + (t : ℝ)) ≤ ‖w + (t : ℝ)‖) :
    Metric.ball z c ⊆ slitPlane := by
  intro w hw
  by_contra hnw
  have him := im_eq_zero_of_notMem_slitPlane hnw
  have hre : w.re ≤ 0 := by
    by_contra! hp
    exact hnw (mem_slitPlane_iff.mpr (Or.inl hp))
  have hw_eq : w + ((-w.re : ℝ) : ℂ) = 0 := by
    apply Complex.ext <;> simp [him]
  have hb : c * (1 + -w.re) ≤ ‖w + ((-w.re : ℝ) : ℂ)‖ := hball w hw ⟨-w.re, by linarith⟩
  rw [hw_eq, norm_zero] at hb
  linarith [mul_pos hc (show (0 : ℝ) < 1 + -w.re by linarith)]

/-- Differentiation under the integral sign for the periodic-quadratic Stieltjes family on
`slitPlane`. -/
theorem hasDerivAt_integral_fract_sub_fract_sq_div_add_pow {z : ℂ} (hz : z ∈ slitPlane) (j : ℕ) :
    HasDerivAt
      (fun w : ℂ ↦
        ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (w + t) ^ (j + 2))
      (-(j + 2 : ℂ) *
        ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ (j + 3))
      z := by
  obtain ⟨c, hc, hball⟩ := exists_pos_forall_mem_ball_mul_one_add_le_norm_add hz
  have hball_slit := ball_subset_slitPlane_of_mul_one_add_le hc hball
  let F : ℂ → ℝ → ℂ := fun w t ↦
    (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (w + t) ^ (j + 2)
  let F' : ℂ → ℝ → ℂ := fun w t ↦
    -(j + 2 : ℂ) * ((((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (w + t) ^ (j + 3))
  let bound : ℝ → ℝ := fun t ↦ ((j + 2 : ℝ) / (8 * c ^ (j + 3))) * (1 / (1 + t) ^ (j + 3))
  have hmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) (volume.restrict (Ioi 0)) := by
    filter_upwards [Metric.ball_mem_nhds z hc] with w hw
    exact aestronglyMeasurable_stieltjesIntegrand (hball_slit hw) j
  have hF'_int : Integrable (F' z) (volume.restrict (Ioi 0)) :=
    ((integrableOn_Ioi_fract_sub_fract_sq_div_add_pow_iff (j := j + 1)).mpr hz).const_mul _
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) :=
    ((integrableOn_Ioi_one_div_add_pow_iff (j := j + 1)).mpr one_pos).const_mul _
  have hdom := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z hc) hmeas
    (integrableOn_Ioi_fract_sub_fract_sq_div_add_pow_iff.mpr hz) hF'_int.aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
      have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
      have hden : c * (1 + t) ≤ ‖w + (t : ℂ)‖ := hball w hw ⟨t, ht0⟩
      have hpow : (c * (1 + t)) ^ (j + 3) ≤ ‖w + t‖ ^ (j + 3) :=
        pow_le_pow_left₀ (by positivity) hden (j + 3)
      have hnj : ‖-(j + 2 : ℂ)‖ = (j + 2 : ℝ) := by
        rw [norm_neg, ← Nat.cast_ofNat, ← Nat.cast_add, Complex.norm_natCast]
        push_cast
        rfl
      dsimp [F', bound]
      rw [norm_mul, hnj, norm_div, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg (fractQuad_nonneg t)]
      calc
        (j + 2 : ℝ) * (fractQuad t / ‖w + t‖ ^ (j + 3))
            ≤ (j + 2 : ℝ) * ((1 / 8) / (c * (1 + t)) ^ (j + 3)) :=
          mul_le_mul_of_nonneg_left
            (div_le_div₀ (by norm_num) (fractQuad_le t) (by positivity) hpow) (by positivity)
        _ = (j + 2 : ℝ) / (8 * c ^ (j + 3)) * (1 / (1 + t) ^ (j + 3)) := by
          rw [mul_pow]
          field_simp)
    hbound_int
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
      have hne : w + (t : ℂ) ≠ 0 := by
        rw [add_comm]
        exact slitPlane_ne_zero (ofReal_add_mem_slitPlane (hball_slit hw) (mem_Ioi.mp ht).le)
      exact hasDerivAt_stieltjesIntegrand hne j)).2
  simpa [F, F', integral_const_mul] using hdom

/-! ### Stieltjes representation and iterated derivatives of `stirlingRemainder` -/

private noncomputable abbrev stieltjesKernel (j : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ (j + 2)

private theorem norm_stieltjesKernel_le_of_cos (j : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    ‖stieltjesKernel j z‖ ≤
      1 / (8 * (j + 1 : ℝ) * Real.cos (z.arg / 2) ^ (j + 2) * ‖z‖ ^ (j + 1)) := by
  have hc : 0 < Real.cos (z.arg / 2) := cos_half_arg_pos hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hz)
  let g : ℝ → ℝ := fun t ↦ (8 * Real.cos (z.arg / 2) ^ (j + 2))⁻¹ * (1 / (‖z‖ + t) ^ (j + 2))
  have hg_int : IntegrableOn g (Ioi 0) :=
    (integrableOn_Ioi_one_div_add_pow_iff.mpr hz0).const_mul _
  have hle : ‖stieltjesKernel j z‖ ≤ ∫ t : ℝ in Ioi 0, g t := by
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

/-- **Stieltjes integral representation of the Stirling remainder**
([DLMF 5.11.1](https://dlmf.nist.gov/5.11.E1)): for every `z ∈ slitPlane`,
`stirlingRemainder z = ∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (z + t) ^ 2 dt`. -/
theorem stirlingRemainder_eq_integral {z : ℂ} (hz : z ∈ slitPlane) :
    stirlingRemainder z =
      ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ 2 := by
  let d : ℂ → ℂ := fun w ↦ stirlingRemainder w - stieltjesKernel 0 w
  have hd_deriv : ∀ w ∈ slitPlane, HasDerivAt d 0 w := fun w hw ↦ by
    have h1 := hasDerivAt_stirlingRemainder hw
    have h2 : HasDerivAt (stieltjesKernel 0) (-2 * stieltjesKernel 1 w) w :=
      (hasDerivAt_integral_fract_sub_fract_sq_div_add_pow hw 0).congr_deriv (by ring)
    have h3 : Complex.digamma w - Complex.log w + (2 * w)⁻¹ = -2 * stieltjesKernel 1 w :=
      Complex.digamma_sub_log_add_inv_two_mul_eq_integral (Or.inl hw)
    have hd := h1.sub h2
    rw [h3, sub_self] at hd
    exact hd
  have hconn :=
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
  have hconst : ∀ n : ℕ, d z = d ((n : ℝ) + 1 : ℝ) := fun n ↦ by
    have hn : (((n : ℝ) + 1 : ℝ) : ℂ) ∈ slitPlane :=
      ofReal_mem_slitPlane.mpr (by positivity)
    exact isOpen_slitPlane.is_const_of_deriv_eq_zero hconn
      (fun w hw ↦ (hd_deriv w hw).differentiableAt.differentiableWithinAt)
      (fun w hw ↦ (hd_deriv w hw).deriv) hz hn
  have hk_lim : Tendsto (fun n : ℕ ↦ stieltjesKernel 0 ((n : ℝ) + 1 : ℝ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (g := fun n : ℕ ↦ (8 * ((n : ℝ) + 1))⁻¹) (fun _ ↦ norm_nonneg _)
      (fun n ↦ ?_) ?_
    · have hn : (0 : ℝ) < n + 1 := by positivity
      have hb := norm_stieltjesKernel_le_of_cos 0 (ofReal_mem_slitPlane.mpr hn)
      have harg : (((n : ℝ) + 1 : ℝ) : ℂ).arg = 0 := arg_ofReal_of_nonneg hn.le
      rw [harg, zero_div, Real.cos_zero, Complex.norm_real, Real.norm_of_nonneg hn.le] at hb
      simpa using hb
    · refine tendsto_inv_atTop_zero.comp (Tendsto.const_mul_atTop (by norm_num) ?_)
      exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hd_lim : Tendsto (fun n : ℕ ↦ d ((n : ℝ) + 1 : ℝ)) atTop (𝓝 0) := by
    simpa [d] using tendsto_stirlingRemainder_natCast_add_one.sub hk_lim
  have hd0 : d z = 0 := tendsto_const_nhds_iff.mp (hd_lim.congr fun n ↦ (hconst n).symm)
  exact sub_eq_zero.mp hd0

/-- Integral representation of all higher derivatives of the Stirling remainder on the slit plane:
for every `j : ℕ` and `z ∈ slitPlane`,
`iteratedDeriv j stirlingRemainder z =
  (-1) ^ j * (j + 1)! * ∫_{t > 0} ((fract t - fract t ^ 2) / 2) / (z + t) ^ (j + 2) dt`. -/
theorem iteratedDeriv_stirlingRemainder (j : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv j stirlingRemainder z = (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) *
      ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ (j + 2) := by
  induction j generalizing z with
  | zero =>
    simpa [iteratedDeriv_zero] using stirlingRemainder_eq_integral hz
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have heq : EqOn (iteratedDeriv j stirlingRemainder)
        (fun w ↦ (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * stieltjesKernel j w) slitPlane :=
      fun w hw ↦ ih hw
    have hd : HasDerivAt (fun w ↦ (-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * stieltjesKernel j w)
        ((-1 : ℂ) ^ j * ((j + 1).factorial : ℂ) * (-(j + 2 : ℂ) * stieltjesKernel (j + 1) z))
        z :=
      (hasDerivAt_integral_fract_sub_fract_sq_div_add_pow hz j).const_mul _
    rw [(heq.eventuallyEq_of_mem (isOpen_slitPlane.mem_nhds hz)).deriv_eq, hd.deriv]
    have hfac : ((j + 2).factorial : ℂ) = (j + 2 : ℂ) * ((j + 1).factorial : ℂ) := by
      rw [show j + 2 = (j + 1) + 1 by ring, Nat.factorial_succ]
      push_cast
      ring
    rw [pow_succ, hfac]
    dsimp [stieltjesKernel]
    ring

/-- For `j : ℕ` and `z ∈ slitPlane`, the `(j + 1)`-st derivative of `stirlingRemainder` coincides
with the `j`-th derivative of `w ↦ digamma w - log w + (2 * w)⁻¹`. -/
theorem iteratedDeriv_succ_stirlingRemainder (j : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv (j + 1) stirlingRemainder z =
      iteratedDeriv j (fun w ↦ Complex.digamma w - Complex.log w + (2 * w)⁻¹) z := by
  rw [iteratedDeriv_succ']
  exact EqOn.iteratedDeriv_of_isOpen (fun _ hw ↦ deriv_stirlingRemainder hw) isOpen_slitPlane j hz

/-- Explicit Stieltjes integral formula for `deriv stirlingRemainder` on the slit plane. -/
theorem deriv_stirlingRemainder_eq_integral {z : ℂ} (hz : z ∈ slitPlane) :
    deriv stirlingRemainder z =
      -2 * ∫ t : ℝ in Ioi 0, (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / (z + t) ^ 3 := by
  simpa [iteratedDeriv_one] using iteratedDeriv_stirlingRemainder 1 hz

/-! ### Sharp Nemes sector bounds for `stirlingRemainder` and its derivatives -/

/-- **Nemes's bound for higher derivatives of the Stirling remainder** on the slit plane (Nemes
2015, eq. (2.5) and Lemma 2.1): for every `j : ℕ` and `z ∈ slitPlane`,
`‖iteratedDeriv j stirlingRemainder z‖ ≤
  j! / (8 * cos (arg z / 2) ^ (j + 2) * ‖z‖ ^ (j + 1))`. -/
theorem norm_iteratedDeriv_stirlingRemainder_le (j : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    ‖iteratedDeriv j stirlingRemainder z‖ ≤
      (j.factorial : ℝ) / (8 * Real.cos (z.arg / 2) ^ (j + 2) * ‖z‖ ^ (j + 1)) := by
  rw [iteratedDeriv_stirlingRemainder j hz, norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, Complex.norm_natCast]
  calc
    ((j + 1).factorial : ℝ) * ‖stieltjesKernel j z‖
        ≤ ((j + 1).factorial : ℝ) *
          (1 / (8 * (j + 1 : ℝ) * Real.cos (z.arg / 2) ^ (j + 2) * ‖z‖ ^ (j + 1))) :=
      mul_le_mul_of_nonneg_left (norm_stieltjesKernel_le_of_cos j hz) (Nat.cast_nonneg _)
    _ = (j.factorial : ℝ) / (8 * Real.cos (z.arg / 2) ^ (j + 2) * ‖z‖ ^ (j + 1)) := by
      rw [Nat.factorial_succ]
      push_cast
      have hj1 : (j + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hj1]

/-- Sharp sector bound for higher derivatives of the Stirling remainder: for `0 < δ`, every
nonzero `z` with `|arg z| ≤ π - δ`, and every `j : ℕ`,
`‖iteratedDeriv j stirlingRemainder z‖ ≤ j! / (8 * sin (δ / 2) ^ (j + 2) * ‖z‖ ^ (j + 1))`.
Note that `δ ≤ π` follows automatically from `|arg z| ≤ π - δ`. -/
theorem norm_iteratedDeriv_stirlingRemainder_le_of_abs_arg_le (j : ℕ) {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : |z.arg| ≤ π - δ) (hz0 : z ≠ 0) :
    ‖iteratedDeriv j stirlingRemainder z‖ ≤
      (j.factorial : ℝ) / (8 * Real.sin (δ / 2) ^ (j + 2) * ‖z‖ ^ (j + 1)) := by
  have hslit := mem_slitPlane_of_abs_arg_le hδ hz hz0
  have hδπ : δ ≤ π := by linarith [abs_nonneg z.arg]
  have hsin : 0 < Real.sin (δ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (half_pos hδ) (by linarith [Real.pi_pos])
  have hsc := sin_half_le_cos_half_arg_of_abs_arg_le hδ.le hz
  refine (norm_iteratedDeriv_stirlingRemainder_le j hslit).trans ?_
  have hzn : 0 < ‖z‖ ^ (j + 1) := pow_pos (norm_pos_iff.mpr hz0) _
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsin.le hsc _) (by norm_num)) hzn.le)

/-- Sharp slit-plane bound for the Stirling remainder itself (`j = 0`):
`‖stirlingRemainder z‖ ≤ 1 / (8 * cos (arg z / 2) ^ 2 * ‖z‖)` for `z ∈ slitPlane`. -/
theorem norm_stirlingRemainder_le {z : ℂ} (hz : z ∈ slitPlane) :
    ‖stirlingRemainder z‖ ≤ 1 / (8 * Real.cos (z.arg / 2) ^ 2 * ‖z‖) := by
  simpa [iteratedDeriv_zero] using norm_iteratedDeriv_stirlingRemainder_le 0 hz

/-- Sharp closed-sector bound for the Stirling remainder (`j = 0`): for `0 < δ` and nonzero `z`
with `|arg z| ≤ π - δ`, `‖stirlingRemainder z‖ ≤ 1 / (8 * sin (δ / 2) ^ 2 * ‖z‖)`. -/
theorem norm_stirlingRemainder_le_of_abs_arg_le {z : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hz : |z.arg| ≤ π - δ) (hz0 : z ≠ 0) :
    ‖stirlingRemainder z‖ ≤ 1 / (8 * Real.sin (δ / 2) ^ 2 * ‖z‖) := by
  simpa [iteratedDeriv_zero] using norm_iteratedDeriv_stirlingRemainder_le_of_abs_arg_le 0 hδ hz hz0

/-- Sharp slit-plane bound for `deriv stirlingRemainder` (`j = 1`):
`‖deriv stirlingRemainder z‖ ≤ 1 / (8 * cos (arg z / 2) ^ 3 * ‖z‖ ^ 2)` for `z ∈ slitPlane`. -/
theorem norm_deriv_stirlingRemainder_le {z : ℂ} (hz : z ∈ slitPlane) :
    ‖deriv stirlingRemainder z‖ ≤ 1 / (8 * Real.cos (z.arg / 2) ^ 3 * ‖z‖ ^ 2) := by
  simpa [iteratedDeriv_one] using norm_iteratedDeriv_stirlingRemainder_le 1 hz

/-- Existential sector bound for higher derivatives of `stirlingRemainder`: for every `j : ℕ` and
`0 < δ`, there exists `C > 0` with `‖iteratedDeriv j stirlingRemainder z‖ ≤ C / ‖z‖ ^ (j + 1)`
whenever `|arg z| ≤ π - δ` and `z ≠ 0`. -/
theorem exists_norm_iteratedDeriv_stirlingRemainder_le (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ z : ℂ, |z.arg| ≤ π - δ → z ≠ 0 →
      ‖iteratedDeriv j stirlingRemainder z‖ ≤ C / ‖z‖ ^ (j + 1) := by
  rcases le_or_gt δ π with hδπ | hπδ
  · have hsin : 0 < Real.sin (δ / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (half_pos hδ) (by linarith [Real.pi_pos])
    refine ⟨(j.factorial : ℝ) / (8 * Real.sin (δ / 2) ^ (j + 2)),
      div_pos (Nat.cast_pos.mpr (Nat.factorial_pos j)) (by positivity),
      fun z hz hz0 ↦ ?_⟩
    rw [div_div]
    exact norm_iteratedDeriv_stirlingRemainder_le_of_abs_arg_le j hδ hz hz0
  · exact ⟨1, one_pos, fun z hz _ ↦ False.elim (by linarith [abs_nonneg z.arg])⟩

/-- Asymptotic `O(‖z‖ ^ (-(j + 1)))` bound for the `j`-th derivative of `stirlingRemainder` as
`z → ∞` in any closed sector `|arg z| ≤ π - δ` (`0 < δ`). -/
theorem isBigO_iteratedDeriv_stirlingRemainder (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    iteratedDeriv j stirlingRemainder
      =O[cobounded ℂ ⊓ 𝓟 {z : ℂ | |z.arg| ≤ π - δ}] fun z : ℂ ↦ (‖z‖ ^ (j + 1))⁻¹ := by
  obtain ⟨C, -, hC⟩ := exists_norm_iteratedDeriv_stirlingRemainder_le j hδ
  refine IsBigO.of_bound C ?_
  rw [eventually_inf_principal]
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with z hz0 hz
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg (norm_nonneg z) _)), ← div_eq_mul_inv]
  exact hC z hz (norm_pos_iff.mp hz0)

/-! ### Positive real axis: real-valuedness and strict sign alternation -/

private theorem iteratedDeriv_stirlingRemainder_ofReal_eq (j : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv j stirlingRemainder x =
      (((-1 : ℝ) ^ j * ((j + 1).factorial : ℝ) *
        ∫ t : ℝ in Ioi 0, ((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2) : ℝ) : ℂ) := by
  rw [iteratedDeriv_stirlingRemainder j (ofReal_mem_slitPlane.mpr hx)]
  have heq : (∫ t : ℝ in Ioi 0,
      (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / ((x : ℂ) + t) ^ (j + 2)) =
      ((∫ t : ℝ in Ioi 0,
        ((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2) : ℝ) : ℂ) := by
    calc
      (∫ t : ℝ in Ioi 0,
          (((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / ((x : ℂ) + t) ^ (j + 2))
          = ∫ t : ℝ in Ioi 0,
            ((((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2) : ℝ) : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
        push_cast
        rfl
      _ = ((∫ t : ℝ in Ioi 0,
            ((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2) : ℝ) : ℂ) :=
        integral_ofReal
  rw [heq]
  push_cast
  rfl

/-- For every `j : ℕ` and `0 < x`, `iteratedDeriv j stirlingRemainder x` is real-valued. -/
theorem iteratedDeriv_stirlingRemainder_ofReal_im (j : ℕ) {x : ℝ} (hx : 0 < x) :
    (iteratedDeriv j stirlingRemainder x).im = 0 := by
  rw [iteratedDeriv_stirlingRemainder_ofReal_eq j hx, ofReal_im]

/-- Real integral representation of `(iteratedDeriv j stirlingRemainder x).re` for `0 < x`. -/
theorem iteratedDeriv_stirlingRemainder_ofReal_re (j : ℕ) {x : ℝ} (hx : 0 < x) :
    (iteratedDeriv j stirlingRemainder x).re =
      (-1 : ℝ) ^ j * ((j + 1).factorial : ℝ) *
        ∫ t : ℝ in Ioi 0, ((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2) := by
  rw [iteratedDeriv_stirlingRemainder_ofReal_eq j hx, ofReal_re]

/-- Strict sign alternation of the Stirling remainder and its derivatives on `(0, ∞)`:
for every `j : ℕ` and `0 < x`, `0 < (-1) ^ j * (iteratedDeriv j stirlingRemainder x).re`. -/
theorem mul_iteratedDeriv_stirlingRemainder_ofReal_re_pos (j : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < (-1 : ℝ) ^ j * (iteratedDeriv j stirlingRemainder x).re := by
  rw [iteratedDeriv_stirlingRemainder_ofReal_re j hx, ← mul_assoc, ← mul_assoc, ← mul_pow,
    neg_one_mul, neg_neg, one_pow, one_mul]
  let f : ℝ → ℝ := fun t ↦ ((Int.fract t - Int.fract t ^ 2) / 2) / (x + t) ^ (j + 2)
  have hf_int : IntegrableOn f (Ioi 0) := by
    have hc := (integrableOn_Ioi_fract_sub_fract_sq_div_add_pow_iff (j := j)).mpr
      (ofReal_mem_slitPlane.mpr hx)
    refine hc.re.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    change ((((Int.fract t - Int.fract t ^ 2) / 2 : ℝ) : ℂ) / ((x : ℂ) + t) ^ (j + 2)).re = f t
    dsimp [f]
    rw [← ofReal_add, ← ofReal_pow, ← ofReal_div, ofReal_re]
  have hf_nn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hxt : 0 < x + t := by linarith [mem_Ioi.mp ht]
    exact div_nonneg (fractQuad_nonneg t) (pow_nonneg hxt.le _)
  have hint_pos : 0 < ∫ t : ℝ in Ioi 0, f t := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hf_nn hf_int]
    have hsub : Ioo (1 / 4 : ℝ) (3 / 4) ⊆ Function.support f ∩ Ioi 0 := by
      intro t ht
      refine ⟨Function.mem_support.mpr ?_, mem_Ioi.mpr (by linarith [ht.1])⟩
      have hfr : Int.fract t = t := Int.fract_eq_self.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hnum : 0 < (Int.fract t - Int.fract t ^ 2) / 2 := by
        rw [hfr]
        nlinarith [ht.1, ht.2]
      have hden : 0 < (x + t) ^ (j + 2) := pow_pos (by linarith [ht.1]) _
      exact (div_pos hnum hden).ne'
    have hvol : 0 < volume (Ioo (1 / 4 : ℝ) (3 / 4)) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by norm_num)
    exact hvol.trans_le (measure_mono hsub)
  exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) hint_pos

/-- Sharp upper bound on `(-1) ^ j * (iteratedDeriv j stirlingRemainder x).re` for `0 < x`:
`(-1) ^ j * (iteratedDeriv j stirlingRemainder x).re ≤ j! / (8 * x ^ (j + 1))`. -/
theorem mul_iteratedDeriv_stirlingRemainder_ofReal_re_le (j : ℕ) {x : ℝ} (hx : 0 < x) :
    (-1 : ℝ) ^ j * (iteratedDeriv j stirlingRemainder x).re ≤
      (j.factorial : ℝ) / (8 * x ^ (j + 1)) := by
  have hb := norm_iteratedDeriv_stirlingRemainder_le j (ofReal_mem_slitPlane.mpr hx)
  rw [arg_ofReal_of_nonneg hx.le, zero_div, Real.cos_zero, one_pow, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hx.le] at hb
  calc
    (-1 : ℝ) ^ j * (iteratedDeriv j stirlingRemainder x).re
        ≤ |(-1 : ℝ) ^ j * (iteratedDeriv j stirlingRemainder x).re| := le_abs_self _
    _ = |(iteratedDeriv j stirlingRemainder x).re| := by rw [abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul]
    _ ≤ ‖iteratedDeriv j stirlingRemainder x‖ := abs_re_le_norm _
    _ ≤ (j.factorial : ℝ) / (8 * x ^ (j + 1)) := hb

/-- On `(0, ∞)` the Stirling remainder has strictly positive real part. -/
theorem stirlingRemainder_ofReal_re_pos {x : ℝ} (hx : 0 < x) :
    0 < (stirlingRemainder x).re := by
  simpa [iteratedDeriv_zero] using mul_iteratedDeriv_stirlingRemainder_ofReal_re_pos 0 hx

/-- On `(0, ∞)` the Stirling remainder satisfies `(stirlingRemainder x).re ≤ 1 / (8 * x)`. -/
theorem stirlingRemainder_ofReal_re_le {x : ℝ} (hx : 0 < x) :
    (stirlingRemainder x).re ≤ 1 / (8 * x) := by
  simpa [iteratedDeriv_zero] using mul_iteratedDeriv_stirlingRemainder_ofReal_re_le 0 hx

/-- On `(0, ∞)` the Stirling remainder is strictly decreasing:
`(deriv stirlingRemainder x).re < 0` for `0 < x`. -/
theorem deriv_stirlingRemainder_ofReal_re_neg {x : ℝ} (hx : 0 < x) :
    (deriv stirlingRemainder x).re < 0 := by
  have h := mul_iteratedDeriv_stirlingRemainder_ofReal_re_pos 1 hx
  rw [pow_one, iteratedDeriv_one, neg_one_mul, neg_pos] at h
  exact h

/-- Sharp slit-plane bound for `ψ(z) - log z + 1 / (2z)` (`j = 1` of Nemes's bound; at `z = 0`
both sides vanish):
`‖digamma z - log z + 1 / (2z)‖ ≤ 1 / (8 * cos (arg z / 2) ^ 3 * ‖z‖ ^ 2)`. -/
theorem _root_.Complex.norm_digamma_sub_log_add_inv_two_mul_le {z : ℂ}
    (hz : z ∈ slitPlane ∪ {0}) :
    ‖Complex.digamma z - Complex.log z + (2 * z)⁻¹‖ ≤
      1 / (8 * Real.cos (z.arg / 2) ^ 3 * ‖z‖ ^ 2) := by
  rcases hz with hz | rfl
  · rw [← deriv_stirlingRemainder hz]
    exact norm_deriv_stirlingRemainder_le hz
  · simp [Complex.digamma_def, logDeriv_apply]

end TauCeti

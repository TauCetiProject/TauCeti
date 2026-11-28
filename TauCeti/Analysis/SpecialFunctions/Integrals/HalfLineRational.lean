/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import TauCeti.Analysis.Calculus.Deriv.Complex
import TauCeti.Analysis.Calculus.Deriv.ZPow
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.Pow.ParametricIntegral

/-!
# Rational integrals on the half-line

For all real `a` and `c`,

`∫_{y > 0} y² / ((y² + a²) (y² + c²)) dy = π / (2 (|a| + |c|))`,

where for `a = c = 0` the integrand is not integrable and both sides are zero.

The integrand is the product of the two functions `y / (y² + a²)` and `y / (y² + c²)`, and
integrals of this shape arise when two Lorentzian line shapes are paired on the half-line. It
depends on `a` and `c` only through their squares, so one may take `a, c ≥ 0`. For `a ≠ c` partial
fractions then give the antiderivative `(c arctan (y / c) - a arctan (y / a)) / (c² - a²)`, and
for `a = c > 0` the antiderivative is `arctan (y / a) / (2 a) - y / (2 (y² + a²))`. The integrand
is nonnegative, so integrability comes for free from the limits of these antiderivatives at
infinity.

We also evaluate the shifted inverse-power family `∫_{t > 0} 1 / (a + t) ^ (j + 2) dt =
1 / ((j + 1) * a ^ (j + 1))` for `0 ≤ a` and `j : ℕ`, characterizing integrability on `(0, ∞)` by
`0 < a`, as well as its complex slit-plane extension
`∫_{u > 0} 1 / (u + z) ^ (j + 2) du = 1 / ((j + 1) * z ^ (j + 1))` for `z ∈ Complex.slitPlane`.

Finally, for `c > 0` and `z` in the slit plane, `∫_c^∞ t⁻¹ (t + z)⁻¹ dt = z⁻¹ (log (c + z) - log c)`
with the principal logarithm, from the antiderivative `z⁻¹ (log t - log (t + z))`, which tends to
`0` at `+∞`. This is the model integral of the Stieltjes transform of `t⁻¹`, which diverges at `0`.

## Main results

* `TauCeti.hasDerivAt_mul_arctan_div`: `a arctan (y / a)` is an antiderivative of
  `a² / (y² + a²)` for every real `a`;
* `TauCeti.tendsto_mul_arctan_div`: `a arctan (y / a)` tends to `|a| π / 2` at infinity;
* `TauCeti.integrableOn_sq_div_sq_add_sq_mul_sq_add_sq_iff`: `y² / ((y² + a²) (y² + c²))` is
  integrable on `(0, ∞)` iff `a` and `c` are not both zero;
* `TauCeti.integral_Ioi_sq_div_sq_add_sq_mul_sq_add_sq`: the value of that integral;
* `TauCeti.integrableOn_Ioi_one_div_add_pow_iff` and `TauCeti.integral_Ioi_one_div_add_pow`:
  integrability criterion and exact value of `∫_{t > 0} 1 / (a + t) ^ (j + 2) dt`;
* `TauCeti.integrableOn_Ioi_one_div_ofReal_add_pow` and
  `TauCeti.integral_Ioi_one_div_ofReal_add_pow`: integrability and exact value of
  `∫_{u > 0} 1 / (u + z) ^ (j + 2) du` on `Complex.slitPlane`;
* `Complex.integrableOn_Ioi_inv_mul_inv_add` and `Complex.integral_Ioi_inv_mul_inv_add`:
  integrability and exact value of `∫_c^∞ t⁻¹ (t + z)⁻¹ dt` on `Complex.slitPlane`;
* `Real.integrableOn_Ioi_inv_mul_add` and `Real.integral_Ioi_inv_mul_add`: the real case
  `∫_c^∞ (t (t + r))⁻¹ dt = (log (c + r) - log c) / r` for `c, r > 0`.
-/

public section

open Filter MeasureTheory Real Set
open scoped Topology

namespace TauCeti

/-- `a arctan (y / a)` is an antiderivative of `a² / (y² + a²)`, for every real `a`; both sides
vanish when `a = 0`. -/
theorem hasDerivAt_mul_arctan_div (a y : ℝ) :
    HasDerivAt (fun y ↦ a * arctan (y / a)) (a ^ 2 / (y ^ 2 + a ^ 2)) y := by
  rcases eq_or_ne a 0 with rfl | ha
  · simpa using hasDerivAt_const y (0 : ℝ)
  refine (((hasDerivAt_id y).div_const a).arctan.const_mul a).congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- For every real `a`, `a arctan (y / a)` tends to `|a| π / 2` as `y → ∞`. -/
theorem tendsto_mul_arctan_div (a : ℝ) :
    Tendsto (fun y ↦ a * arctan (y / a)) atTop (𝓝 (|a| * (π / 2))) := by
  have key (y : ℝ) : a * arctan (y / a) = |a| * arctan (y / |a|) := by
    rcases abs_choice a with h | h <;> simp [h, div_neg, arctan_neg]
  simp_rw [key]
  rcases (abs_nonneg a).eq_or_lt with ha | ha
  · simp [← ha]
  exact ((tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp
    (tendsto_id.atTop_div_const ha)).const_mul |a|

/-- An antiderivative of `y² / ((y² + a²) (y² + c²))` on `[0, ∞)` vanishing at `0`, with limit
`π / (2 (a + c))` at infinity. -/
private theorem exists_antiderivative {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : 0 < a + c) :
    ∃ G : ℝ → ℝ, ContinuousWithinAt G (Ici 0) 0 ∧
      (∀ y ∈ Ioi (0 : ℝ), HasDerivAt G (y ^ 2 / ((y ^ 2 + a ^ 2) * (y ^ 2 + c ^ 2))) y) ∧
      Tendsto G atTop (𝓝 (π / (2 * (a + c)))) ∧ G 0 = 0 := by
  rcases ne_or_eq a c with hne | rfl
  · -- Partial fractions:
    -- `y² / ((y² + a²)(y² + c²)) = (c² / (y² + c²) - a² / (y² + a²)) / (c² - a²)`.
    have hd : c ^ 2 - a ^ 2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero (by linarith) (sub_ne_zero.mpr hne.symm)
    refine ⟨fun y ↦ (c * arctan (y / c) - a * arctan (y / a)) / (c ^ 2 - a ^ 2), ?_, fun y hy ↦ ?_,
      ?_, by simp⟩
    · exact Continuous.continuousWithinAt (by fun_prop)
    · have hy : 0 < y := hy
      refine (((hasDerivAt_mul_arctan_div c y).sub (hasDerivAt_mul_arctan_div a y)).div_const
        (c ^ 2 - a ^ 2)).congr_deriv ?_
      have h₁ : y ^ 2 + a ^ 2 ≠ 0 := by positivity
      have h₂ : y ^ 2 + c ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    · convert ((tendsto_mul_arctan_div c).sub (tendsto_mul_arctan_div a)).div_const
        (c ^ 2 - a ^ 2) using 2
      rw [abs_of_nonneg ha, abs_of_nonneg hc, eq_div_iff hd, sq_sub_sq]
      field_simp
      ring
  · -- Equal parameters: `y² / (y² + a²)² = d/dy (arctan (y / a) / (2 a) - y / (2 (y² + a²)))`.
    have ha' : 0 < a := by linarith
    refine ⟨fun y ↦ a * arctan (y / a) / (2 * a ^ 2) - y / (2 * (y ^ 2 + a ^ 2)), ?_,
      fun y _ ↦ ?_, ?_, by simp⟩
    · refine Continuous.continuousWithinAt (Continuous.sub (by fun_prop) ?_)
      exact continuous_id.div (by fun_prop) fun y ↦ by positivity
    · have h₁ : y ^ 2 + a ^ 2 ≠ 0 := by positivity
      have hq : HasDerivAt (fun y : ℝ ↦ 2 * (y ^ 2 + a ^ 2)) (2 * (2 * y)) y := by
        simpa using (((hasDerivAt_id y).pow 2).add_const (a ^ 2)).const_mul 2
      refine (((hasDerivAt_mul_arctan_div a y).div_const (2 * a ^ 2)).sub
        ((hasDerivAt_id y).div hq (by positivity))).congr_deriv ?_
      simp only [id]
      field_simp
      ring
    · have hlim : Tendsto (fun y : ℝ ↦ y / (2 * (y ^ 2 + a ^ 2))) atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
          tendsto_inv_atTop_zero ?_ ?_
        · filter_upwards [eventually_ge_atTop 0] with y hy
          positivity
        · filter_upwards [eventually_gt_atTop 0] with y hy
          rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ hy]
          nlinarith
      convert ((tendsto_mul_arctan_div a).div_const (2 * a ^ 2)).sub hlim using 2
      rw [abs_of_nonneg ha]
      field_simp
      ring

/-- The function `y² / ((y² + a²) (y² + c²))` is integrable on `(0, ∞)` exactly when `a` and `c`
are not both zero. -/
theorem integrableOn_sq_div_sq_add_sq_mul_sq_add_sq_iff {a c : ℝ} :
    IntegrableOn (fun y : ℝ ↦ y ^ 2 / ((y ^ 2 + a ^ 2) * (y ^ 2 + c ^ 2))) (Ioi 0) ↔
      a ≠ 0 ∨ c ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra! hac
    obtain ⟨rfl, rfl⟩ := hac
    refine not_integrableOn_Ioi_rpow (-2) (h.congr_fun (fun y hy ↦ ?_) measurableSet_Ioi)
    have hy : 0 < y := hy
    rw [rpow_neg hy.le, rpow_two]
    field_simp
    ring
  · have hac : 0 < |a| + |c| := by rcases h with h | h <;> positivity
    obtain ⟨G, hcont, hderiv, hlim, -⟩ := exists_antiderivative (abs_nonneg a) (abs_nonneg c) hac
    simp only [sq_abs] at hderiv
    exact integrableOn_Ioi_deriv_of_nonneg hcont hderiv (fun y _ ↦ by positivity) hlim

/-- For all real `a` and `c`,
`∫_{y > 0} y² / ((y² + a²) (y² + c²)) dy = π / (2 (|a| + |c|))`. When `a = c = 0` the integrand
is not integrable and both sides are zero. -/
theorem integral_Ioi_sq_div_sq_add_sq_mul_sq_add_sq (a c : ℝ) :
    ∫ y in Ioi 0, y ^ 2 / ((y ^ 2 + a ^ 2) * (y ^ 2 + c ^ 2)) = π / (2 * (|a| + |c|)) := by
  by_cases h : a ≠ 0 ∨ c ≠ 0
  · have hac : 0 < |a| + |c| := by rcases h with h | h <;> positivity
    obtain ⟨G, hcont, hderiv, hlim, hG⟩ := exists_antiderivative (abs_nonneg a) (abs_nonneg c) hac
    simp only [sq_abs] at hderiv
    rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv (fun y _ ↦ by positivity) hlim, hG,
      sub_zero]
  · rw [integral_undef (mt integrableOn_sq_div_sq_add_sq_mul_sq_add_sq_iff.mp h)]
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ c = 0 := by simpa using h
    simp

/-- The shifted inverse power `1 / (a + t) ^ (j + 2)` is integrable on `(0, ∞)` if and only if
`0 < a`: for `a ≤ 0` the pole `t = -a` lies in `[0, ∞)` and has order `j + 2 ≥ 2`. -/
theorem integrableOn_Ioi_one_div_add_pow_iff {a : ℝ} {j : ℕ} :
    IntegrableOn (fun t : ℝ ↦ 1 / (a + t) ^ (j + 2)) (Ioi 0) ↔ 0 < a := by
  have himg : (fun t : ℝ ↦ a + t) '' Ioi (0 : ℝ) = Ioi a := by
    rw [image_const_add_Ioi, add_zero]
  have htr : IntegrableOn (fun t : ℝ ↦ 1 / (a + t) ^ (j + 2)) (Ioi 0) ↔
      IntegrableOn (fun u : ℝ ↦ 1 / u ^ (j + 2)) (Ioi a) := by
    rw [← himg, (measurePreserving_add_left volume a).integrableOn_image
      (measurableEmbedding_addLeft a)]
    simp only [Function.comp_def]
  rw [htr]
  have hrpow {c : ℝ} (hc : 0 ≤ c) :
      IntegrableOn (fun u : ℝ ↦ 1 / u ^ (j + 2)) (Ioi c) ↔
        IntegrableOn (fun u : ℝ ↦ u ^ (-(j + 2 : ℝ))) (Ioi c) :=
    integrableOn_congr_fun (fun u hu ↦ by
      have hu0 : 0 < u := hc.trans_lt hu
      rw [show -(j + 2 : ℝ) = -(((j + 2 : ℕ) : ℝ)) by push_cast; ring, rpow_neg hu0.le,
        rpow_natCast, one_div]) measurableSet_Ioi
  refine ⟨fun h ↦ ?_, fun ha ↦ (hrpow ha.le).mpr (integrableOn_Ioi_rpow_of_lt (by linarith) ha)⟩
  by_contra! ha
  exact not_integrableOn_Ioi_rpow (-(j + 2 : ℝ))
    ((hrpow le_rfl).mp (h.mono_set (Ioi_subset_Ioi ha)))

/-- For `0 ≤ a` and `j : ℕ`, `∫_{t > 0} 1 / (a + t) ^ (j + 2) dt = 1 / ((j + 1) * a ^ (j + 1))`
(at `a = 0` the integrand is not integrable and both sides vanish). -/
theorem integral_Ioi_one_div_add_pow {a : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    ∫ t : ℝ in Ioi 0, 1 / (a + t) ^ (j + 2) = 1 / ((j + 1 : ℝ) * a ^ (j + 1)) := by
  rcases ha.eq_or_lt with rfl | ha'
  · rw [integral_undef (mt integrableOn_Ioi_one_div_add_pow_iff.mp (lt_irrefl 0))]
    simp [zero_pow (Nat.succ_ne_zero j)]
  · have himg : (fun t : ℝ ↦ a + t) '' Ioi (0 : ℝ) = Ioi a := by
      rw [image_const_add_Ioi, add_zero]
    rw [← (measurePreserving_add_left volume a).setIntegral_image_emb
      (measurableEmbedding_addLeft a) (fun u : ℝ ↦ 1 / u ^ (j + 2)) (Ioi 0), himg]
    have hcongr : ∫ u : ℝ in Ioi a, 1 / u ^ (j + 2) =
        ∫ u : ℝ in Ioi a, u ^ (-(j + 2 : ℝ)) :=
      setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ by
        have hu0 : 0 < u := ha'.trans hu
        rw [show -(j + 2 : ℝ) = -(((j + 2 : ℕ) : ℝ)) by push_cast; ring, rpow_neg hu0.le,
          rpow_natCast, one_div]
    rw [hcongr, integral_Ioi_rpow_of_lt (by linarith) ha',
      show -(j + 2 : ℝ) + 1 = -(((j + 1 : ℕ) : ℝ)) by push_cast; ring,
      rpow_neg ha'.le, rpow_natCast]
    push_cast
    field_simp [ha'.ne']

/-- For `z ∈ Complex.slitPlane` and `j : ℕ`, `u ↦ 1 / (u + z) ^ (j + 2)` is integrable on
`(0, ∞)`. -/
theorem integrableOn_Ioi_one_div_ofReal_add_pow {z : ℂ} (hz : z ∈ Complex.slitPlane) (j : ℕ) :
    IntegrableOn (fun u : ℝ ↦ 1 / ((u : ℂ) + z) ^ (j + 2)) (Ioi 0) :=
  integrableOn_div_ofReal_add_pow_of_norm_le aestronglyMeasurable_const (M := (1 : ℝ))
    (Eventually.of_forall fun _ ↦ by norm_num) hz (by omega)

/-- For `z ∈ Complex.slitPlane` and `j : ℕ`,
`∫_{u > 0} 1 / (u + z) ^ (j + 2) du = 1 / ((j + 1) * z ^ (j + 1))`. -/
theorem integral_Ioi_one_div_ofReal_add_pow {z : ℂ} (hz : z ∈ Complex.slitPlane) (j : ℕ) :
    ∫ u in Ioi (0 : ℝ), 1 / ((u : ℂ) + z) ^ (j + 2) =
      1 / (((j + 1 : ℕ) : ℂ) * z ^ (j + 1)) := by
  let F : ℝ → ℂ := fun t ↦ -(((j + 1 : ℕ) : ℂ))⁻¹ / ((t : ℂ) + z) ^ (j + 1)
  have hderiv : ∀ u ∈ Ici (0 : ℝ),
      HasDerivAt F (1 / ((u : ℂ) + z) ^ (j + 2)) u := fun u hu ↦ by
    have hne : (u : ℂ) + z ≠ 0 :=
      Complex.slitPlane_ne_zero (ofReal_add_mem_slitPlane hz (mem_Ici.mp hu))
    refine ((TauCeti.hasDerivAt_ofReal_add u z).const_div_pow hne
      (-(((j + 1 : ℕ) : ℂ))⁻¹) (j + 1)).congr_deriv ?_
    have hj1c : (((j + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    rw [Nat.add_assoc]
    field_simp
  have htend : Tendsto F atTop (𝓝 0) := by
    have hF : F = fun t : ℝ ↦
        (-(((j + 1 : ℕ) : ℂ))⁻¹) * ((t : ℂ) + z) ^ (-(((j + 1 : ℕ) : ℝ) : ℂ)) := by
      ext t
      simp only [F, Complex.ofReal_natCast, Complex.cpow_neg, Complex.cpow_natCast,
        div_eq_mul_inv]
    rw [hF]
    simpa using (Complex.tendsto_ofReal_add_cpow_neg z
      (by exact_mod_cast Nat.succ_pos j : (0 : ℝ) < ((j + 1 : ℕ) : ℝ))).const_mul
      (-(((j + 1 : ℕ) : ℂ))⁻¹)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_Ioi_one_div_ofReal_add_pow hz j) htend
  simpa [F, div_eq_mul_inv, mul_comm] using h

end TauCeti

namespace Complex

/-- For `c > 0` and `z` in the slit plane, `t ↦ t⁻¹ (t + z)⁻¹` is integrable on `(c, ∞)`. -/
theorem integrableOn_Ioi_inv_mul_inv_add {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ)⁻¹ * ((t : ℂ) + z)⁻¹) (Ioi c) := by
  obtain ⟨b, hb, hbz⟩ := TauCeti.exists_pos_mul_one_add_le_norm_ofReal_add hz
  refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc).const_mul b⁻¹).mono' ?_ ?_
  · exact (by fun_prop : Measurable fun t : ℝ ↦
      (t : ℂ)⁻¹ * ((t : ℂ) + z)⁻¹).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : c < t)
    have ht0 : 0 < t := hc.trans ht
    rw [norm_mul, norm_inv, norm_inv, norm_real, Real.norm_of_nonneg ht0.le,
      show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]
    calc t⁻¹ * ‖(t : ℂ) + z‖⁻¹ ≤ t⁻¹ * (b * (1 + t))⁻¹ := by
          gcongr
          exact hbz t ht0.le
      _ = b⁻¹ * (t⁻¹ * (1 + t)⁻¹) := by rw [mul_inv]; ring
      _ ≤ b⁻¹ * (t⁻¹ * t⁻¹) := by gcongr; linarith
      _ = b⁻¹ * (t ^ 2)⁻¹ := by rw [sq, mul_inv]

/-- **The Stieltjes transform of `t⁻¹` on `(c, ∞)`.** For `c > 0` and `z` in the slit plane,
`∫_c^∞ t⁻¹ (t + z)⁻¹ dt = z⁻¹ (log (c + z) - log c)`, with the principal logarithm. -/
theorem integral_Ioi_inv_mul_inv_add {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : z ∈ slitPlane) :
    ∫ t in Ioi c, (t : ℂ)⁻¹ * ((t : ℂ) + z)⁻¹ = z⁻¹ * (log (c + z) - log c) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hmem {t : ℝ} (ht : 0 ≤ t) : (t : ℂ) + z ∈ slitPlane :=
    TauCeti.ofReal_add_mem_slitPlane hz ht
  -- the antiderivative `z⁻¹ (log t - log (t + z))` tends to `0` at `+∞`
  have hderiv : ∀ t ∈ Ici c, HasDerivAt (fun t : ℝ ↦ z⁻¹ * (log (t : ℂ) - log ((t : ℂ) + z)))
      ((t : ℂ)⁻¹ * ((t : ℂ) + z)⁻¹) t := by
    intro t (ht : c ≤ t)
    have ht0 : 0 < t := hc.trans_le ht
    have hid : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 t := by
      simpa using (hasDerivAt_id' t).ofReal_comp
    have h₁ := HasDerivAt.clog_real hid (ofReal_mem_slitPlane.mpr ht0)
    have h₂ := HasDerivAt.clog_real (hid.add_const z) (hmem ht0.le)
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have htz : (t : ℂ) + z ≠ 0 := slitPlane_ne_zero (hmem ht0.le)
    refine ((h₁.sub h₂).const_mul z⁻¹).congr_deriv ?_
    field_simp
    ring
  have hlog : ∀ᶠ t : ℝ in atTop, z⁻¹ * (log (t : ℂ) - log ((t : ℂ) + z)) =
      z⁻¹ * -log (1 + z * ((t⁻¹ : ℝ) : ℂ)) := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have hfac : (t : ℂ) + z = t * (1 + z * ((t⁻¹ : ℝ) : ℂ)) := by
      rw [ofReal_inv]
      field_simp
    have hne : 1 + z * ((t⁻¹ : ℝ) : ℂ) ≠ 0 := by
      intro h
      exact slitPlane_ne_zero (hmem ht.le) (by rw [hfac, h, mul_zero])
    rw [hfac, log_ofReal_mul ht hne, ofReal_log ht.le]
    ring
  have hlim : Tendsto (fun t : ℝ ↦ z⁻¹ * (log (t : ℂ) - log ((t : ℂ) + z))) atTop (𝓝 0) := by
    refine Tendsto.congr' (EventuallyEq.symm hlog) ?_
    have h₁ : Tendsto (fun t : ℝ ↦ 1 + z * ((t⁻¹ : ℝ) : ℂ)) atTop (𝓝 1) := by
      simpa using (((continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero).const_mul
        z).const_add 1
    simpa using ((((continuousAt_clog one_mem_slitPlane).tendsto.comp h₁).neg).const_mul z⁻¹)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_Ioi_inv_mul_inv_add hc hz)
    hlim]
  ring


end Complex

namespace Real

open Complex

/-- For `c, r > 0`, `t ↦ (t (t + r))⁻¹` is integrable on `(c, ∞)`. -/
theorem integrableOn_Ioi_inv_mul_add {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ ↦ (t * (t + r))⁻¹) (Ioi c) := by
  have h := (Complex.integrableOn_Ioi_inv_mul_inv_add hc (ofReal_mem_slitPlane.mpr hr)).re
  refine h.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
  simp only [RCLike.re_to_complex, ← ofReal_add, ← ofReal_inv, ← ofReal_mul, ofReal_re, mul_inv]

/-- The real case of `Complex.integral_Ioi_inv_mul_inv_add`: for `c, r > 0`,
`∫_c^∞ (t (t + r))⁻¹ dt = (log (c + r) - log c) / r`. -/
theorem integral_Ioi_inv_mul_add {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    ∫ t in Ioi c, (t * (t + r))⁻¹ = (Real.log (c + r) - Real.log c) / r := by
  have h := Complex.integral_Ioi_inv_mul_inv_add hc (ofReal_mem_slitPlane.mpr hr)
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ ↦ (((t * (t + r))⁻¹ : ℝ) : ℂ))
      (fun t _ ↦ by push_cast; rw [mul_inv]), integral_complex_ofReal, ← ofReal_add,
    ← ofReal_log hc.le, ← ofReal_log (by positivity), ← ofReal_inv, ← ofReal_sub, ← ofReal_mul,
    ofReal_inj] at h
  rw [h, div_eq_inv_mul]

end Real

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# The Mellin weight `η t^(-1-η)` on `(1, ∞)`

For `η > 0` the density `η t^(-1-η)` is a probability density on `(1, ∞)`. This file studies the
normalized weighted integral

`mellinWeightIntegral η f = η ∫_{t > 1} t^(-1-η) f(t) dt`

of a function `f` with values in a real Banach space. After the substitution `t = exp u` the
density becomes the exponential density `η exp(-η u)` on `u > 0`, whose mean is `η⁻¹`. This is
the scalar half of the Mellin smoothing of weighted prime sums: a bound `A(t) ≤ f(t)` on a prime
sum becomes the bound `mellinWeightIntegral η f` on its smoothed version, and the integrals below
evaluate the majorants that occur.

## Main results

* `TauCeti.mellinWeightIntegral_eq_integral_exp`: the substitution `t = exp u`;
* `TauCeti.mellinWeightIntegral_def`, `TauCeti.mellinWeightIntegral_congr_ae`,
  `TauCeti.mellinWeightIntegral_congr`: unfolding the definition, and dependence only on the
  almost-everywhere class on `(1, ∞)`;
* `TauCeti.mellinWeightIntegral_add`, `TauCeti.mellinWeightIntegral_sub`,
  `TauCeti.mellinWeightIntegral_smul`, `TauCeti.mellinWeightIntegral_neg`: linearity;
* `TauCeti.mellinWeightIntegral_mono`, `TauCeti.norm_mellinWeightIntegral_le`: monotonicity and
  the norm bound under an integrable majorant;
* `TauCeti.mellinWeightIntegral_const`: `η ∫_{t > 1} t^(-1-η) dt = 1`, so constants integrate
  to themselves;
* `TauCeti.integrableOn_rpow_mul_log`, `TauCeti.integrableOn_rpow_mul_one_add_log_sq`:
  integrability of `t^(-1-η) log t` and `t^(-1-η) (1 + log t)²` on `(1, ∞)`, the latter via
  `TauCeti.one_add_log_sq_le`;
* `TauCeti.mellinWeightIntegral_log`: `η ∫_{t > 1} t^(-1-η) log t dt = η⁻¹`;
* `TauCeti.mellinWeightIntegral_log_log_le`: Jensen's bound
  `η ∫_{t > 1} t^(-1-η) log log(3t) dt ≤ log(log 3 + η⁻¹)`;
* `TauCeti.log_log_three_add_inv_le`: `log(log 3 + η⁻¹) ≤ 2 log(2/η)` for `0 < η ≤ 1`.
-/

public section

open MeasureTheory Real Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The normalized Mellin weight integral `η ∫_{t > 1} t^(-1-η) f(t) dt`. For `η > 0` the
weight `η t^(-1-η)` is a probability density on `(1, ∞)` (`mellinWeightIntegral_const`). -/
noncomputable def mellinWeightIntegral (η : ℝ) (f : ℝ → E) : E :=
  η • ∫ t in Ioi 1, t ^ (-1 - η) • f t

theorem mellinWeightIntegral_def (η : ℝ) (f : ℝ → E) :
    mellinWeightIntegral η f = η • ∫ t in Ioi 1, t ^ (-1 - η) • f t := (rfl)

/-- The Mellin weight integral depends only on the almost-everywhere class of `f` on
`(1, ∞)`. -/
theorem mellinWeightIntegral_congr_ae {η : ℝ} {f g : ℝ → E}
    (h : f =ᵐ[volume.restrict (Ioi 1)] g) :
    mellinWeightIntegral η f = mellinWeightIntegral η g := by
  rw [mellinWeightIntegral_def, mellinWeightIntegral_def,
    integral_congr_ae (h.mono fun t ht ↦ by rw [ht])]

/-- The Mellin weight integral depends only on the values of `f` on `(1, ∞)`. -/
theorem mellinWeightIntegral_congr {η : ℝ} {f g : ℝ → E} (h : ∀ t ∈ Ioi 1, f t = g t) :
    mellinWeightIntegral η f = mellinWeightIntegral η g :=
  mellinWeightIntegral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ h))

/-- The substitution `t = exp u` turns the Mellin weight into the exponential density
`η exp(-η u)` on `u > 0`. -/
theorem mellinWeightIntegral_eq_integral_exp (η : ℝ) (f : ℝ → E) :
    mellinWeightIntegral η f = η • ∫ u in Ioi 0, exp (-(η * u)) • f (exp u) := by
  have h := integral_comp_exp_Ioi (fun t ↦ t ^ (-1 - η) • f t) 0
  rw [exp_zero] at h
  rw [mellinWeightIntegral_def, ← h]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
  rw [smul_smul, rpow_def_of_pos (exp_pos u), log_exp, ← exp_add]
  congr 2
  ring

/-- The Mellin weight integral is additive on functions integrable against the weight. -/
theorem mellinWeightIntegral_add {η : ℝ} {f g : ℝ → E}
    (hf : IntegrableOn (fun t ↦ t ^ (-1 - η) • f t) (Ioi 1))
    (hg : IntegrableOn (fun t ↦ t ^ (-1 - η) • g t) (Ioi 1)) :
    mellinWeightIntegral η (f + g) = mellinWeightIntegral η f + mellinWeightIntegral η g := by
  simp only [mellinWeightIntegral_def, Pi.add_apply, smul_add, integral_add hf hg]

/-- The Mellin weight integral commutes with scalars; no integrability is needed. -/
@[simp] theorem mellinWeightIntegral_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (η : ℝ) (c : 𝕜) (f : ℝ → E) :
    mellinWeightIntegral η (c • f) = c • mellinWeightIntegral η f := by
  simp only [mellinWeightIntegral_def, Pi.smul_apply, smul_comm _ c, integral_smul]

/-- The Mellin weight integral commutes with negation; no integrability is needed. -/
@[simp] theorem mellinWeightIntegral_neg (η : ℝ) (f : ℝ → E) :
    mellinWeightIntegral η (-f) = -mellinWeightIntegral η f := by
  simpa using mellinWeightIntegral_smul η (-1 : ℝ) f

/-- The Mellin weight integral is subtractive on functions integrable against the weight. -/
theorem mellinWeightIntegral_sub {η : ℝ} {f g : ℝ → E}
    (hf : IntegrableOn (fun t ↦ t ^ (-1 - η) • f t) (Ioi 1))
    (hg : IntegrableOn (fun t ↦ t ^ (-1 - η) • g t) (Ioi 1)) :
    mellinWeightIntegral η (f - g) = mellinWeightIntegral η f - mellinWeightIntegral η g := by
  simp only [mellinWeightIntegral_def, Pi.sub_apply, smul_sub, integral_sub hf hg]

/-- Monotonicity of the Mellin weight integral for real functions that are integrable against
the weight. -/
theorem mellinWeightIntegral_mono {η : ℝ} (hη : 0 ≤ η) {f g : ℝ → ℝ}
    (hf : IntegrableOn (fun t ↦ t ^ (-1 - η) * f t) (Ioi 1))
    (hg : IntegrableOn (fun t ↦ t ^ (-1 - η) * g t) (Ioi 1)) (hfg : ∀ t ∈ Ioi 1, f t ≤ g t) :
    mellinWeightIntegral η f ≤ mellinWeightIntegral η g := by
  refine smul_le_smul_of_nonneg_left (setIntegral_mono_on hf hg measurableSet_Ioi fun t ht ↦ ?_) hη
  exact mul_le_mul_of_nonneg_left (hfg t ht) (rpow_nonneg (zero_le_one.trans (le_of_lt ht)) _)

/-- A real majorant `g` of `‖f‖` that is integrable against the weight bounds the Mellin weight
integral of `f`; no integrability of `f` is needed. -/
theorem norm_mellinWeightIntegral_le {η : ℝ} (hη : 0 ≤ η) {f : ℝ → E} {g : ℝ → ℝ}
    (hg : IntegrableOn (fun t ↦ t ^ (-1 - η) * g t) (Ioi 1)) (hfg : ∀ t ∈ Ioi 1, ‖f t‖ ≤ g t) :
    ‖mellinWeightIntegral η f‖ ≤ mellinWeightIntegral η g := by
  rw [mellinWeightIntegral_def, norm_smul, norm_of_nonneg hη, mellinWeightIntegral_def, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hg ?_) hη
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht ↦ ?_)
  have ht0 : 0 ≤ t ^ (-1 - η) := rpow_nonneg (zero_le_one.trans (le_of_lt ht)) _
  rw [norm_smul, norm_of_nonneg ht0]
  exact mul_le_mul_of_nonneg_left (hfg t ht) ht0

/-- The Mellin weight `t^(-1-η)` is integrable on `(1, ∞)` for `η > 0`. -/
theorem integrableOn_rpow_neg_one_sub {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun t : ℝ ↦ t ^ (-1 - η)) (Ioi 1) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one

/-- `η ∫_{t > 1} t^(-1-η) c dt = c`: the Mellin weight is a probability density. -/
theorem mellinWeightIntegral_const [CompleteSpace E] {η : ℝ} (hη : 0 < η) (c : E) :
    mellinWeightIntegral η (fun _ ↦ c) = c := by
  rw [mellinWeightIntegral_def, integral_smul_const,
    integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, smul_smul]
  simp [show -1 - η + 1 = -η by ring, hη.ne']

/-- For `η > 0`, `t ↦ t^(-1-η) log t` is integrable on `(1, ∞)`. -/
theorem integrableOn_rpow_mul_log {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun t ↦ t ^ (-1 - η) * log t) (Ioi 1) := by
  -- majorize by `(2 / η) t^(-1-η/2)`, using `log t ≤ (2 / η) t^(η/2)`
  refine ((integrableOn_Ioi_rpow_of_lt (a := -1 - η / 2) (by linarith) zero_lt_one).const_mul
    (2 / η)).mono' (by fun_prop) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht ↦ ?_)
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hlog : 0 ≤ log t := log_nonneg (le_of_lt ht)
  rw [norm_mul, norm_of_nonneg (rpow_nonneg ht0.le _), norm_of_nonneg hlog]
  calc t ^ (-1 - η) * log t ≤ t ^ (-1 - η) * (t ^ (η / 2) / (η / 2)) :=
        mul_le_mul_of_nonneg_left (log_le_rpow_div ht0.le (by positivity)) (rpow_nonneg ht0.le _)
    _ = 2 / η * t ^ (-1 - η / 2) := by
        rw [mul_div_assoc', ← rpow_add ht0]
        field_simp
        ring_nf

/-- `x^(-η) (log x / x) = log x / x^(1+η)` for `x > 0`. -/
theorem rpow_neg_mul_log_div {x η : ℝ} (hx : 0 < x) :
    x ^ (-η) * (log x / x) = log x / x ^ (1 + η) := by
  rw [rpow_add hx, rpow_one, rpow_neg hx.le]
  field_simp

/-- `(1 + log t)² ≤ exp(η/2) (4/η)² t^(η/2)` for `t ≥ 1`, from `log(e t) ≤ (e t)^(η/4) / (η/4)`. -/
theorem one_add_log_sq_le {η t : ℝ} (hη : 0 < η) (ht : 1 ≤ t) :
    (1 + log t) ^ 2 ≤ exp (η / 2) * (4 / η) ^ 2 * t ^ (η / 2) := by
  have ht0 : 0 < t := by linarith
  have h0 : 0 ≤ 1 + log t := by linarith [log_nonneg ht]
  have h1 : 1 + log t ≤ (exp 1 * t) ^ (η / 4) / (η / 4) := by
    have he : 1 + log t = log (exp 1 * t) := by rw [log_mul (exp_pos 1).ne' ht0.ne', log_exp]
    rw [he]
    exact log_le_rpow_div (by positivity) (by positivity)
  calc (1 + log t) ^ 2 ≤ ((exp 1 * t) ^ (η / 4) / (η / 4)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = exp (η / 2) * (4 / η) ^ 2 * t ^ (η / 2) := by
      rw [div_pow, ← rpow_natCast ((exp 1 * t) ^ (η / 4)), ← rpow_mul (by positivity),
        mul_rpow (exp_pos 1).le ht0.le, exp_one_rpow]
      push_cast
      rw [show η / 4 * 2 = η / 2 by ring]
      field_simp

/-- The majorant `t^(-1-η) (1 + log t)²` is integrable on `(1, ∞)` for `η > 0`. -/
theorem integrableOn_rpow_mul_one_add_log_sq {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun t ↦ t ^ (-1 - η) * (1 + log t) ^ 2) (Ioi 1) := by
  refine ((integrableOn_Ioi_rpow_of_lt (a := -1 - η / 2) (by linarith) zero_lt_one).const_mul
    (exp (η / 2) * (4 / η) ^ 2)).mono' (by fun_prop) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht ↦ ?_)
  have ht0 : 0 < t := zero_lt_one.trans ht
  rw [norm_mul, norm_of_nonneg (rpow_nonneg ht0.le _), norm_of_nonneg (sq_nonneg _)]
  calc t ^ (-1 - η) * (1 + log t) ^ 2
      ≤ t ^ (-1 - η) * (exp (η / 2) * (4 / η) ^ 2 * t ^ (η / 2)) :=
        mul_le_mul_of_nonneg_left (one_add_log_sq_le hη (le_of_lt ht)) (rpow_nonneg ht0.le _)
    _ = exp (η / 2) * (4 / η) ^ 2 * t ^ (-1 - η / 2) := by
        rw [mul_left_comm, ← rpow_add ht0]
        ring_nf

/-- `η ∫_{t > 1} t^(-1-η) log t dt = η⁻¹`: the exponential density `η exp(-η u)` has mean
`η⁻¹`. -/
theorem mellinWeightIntegral_log {η : ℝ} (hη : 0 < η) :
    mellinWeightIntegral η log = η⁻¹ := by
  rw [mellinWeightIntegral_eq_integral_exp]
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 2) two_pos hη
  rw [Gamma_two, mul_one] at h
  have : ∫ u in Ioi 0, exp (-(η * u)) • log (exp u) =
      ∫ u in Ioi (0 : ℝ), u ^ ((2 : ℝ) - 1) * exp (-(η * u)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
    rw [log_exp, smul_eq_mul, show (2 : ℝ) - 1 = 1 by norm_num, rpow_one, mul_comm]
  rw [this, h, smul_eq_mul, rpow_two]
  field_simp

/-- For `η > 0`, `t ↦ t^(-1-η) log log(3t)` is integrable on `(1, ∞)`. -/
theorem integrableOn_rpow_mul_log_log {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun t ↦ t ^ (-1 - η) * log (log (3 * t))) (Ioi 1) := by
  -- majorize `|log y|` by `y + (log 3)⁻¹` for `y = log (3t) ≥ log 3`, which is linear in `log t`
  have hlog3 : 0 < log 3 := log_pos (by norm_num)
  refine (((integrableOn_rpow_neg_one_sub hη).mul_const (log 3 + (log 3)⁻¹)).add
    (integrableOn_rpow_mul_log hη)).mono' (by fun_prop) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht ↦ ?_)
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hy : log 3 ≤ log (3 * t) := log_le_log (by norm_num) (by linarith [mem_Ioi.1 ht])
  have hy0 : 0 < log (3 * t) := hlog3.trans_le hy
  -- `|log y| ≤ y + (log 3)⁻¹` for `y = log (3 * t) ≥ log 3`
  have habs : |log (log (3 * t))| ≤ log (3 * t) + (log 3)⁻¹ := by
    refine abs_le.2 ⟨?_, (log_le_self hy0.le).trans (le_add_of_nonneg_right (by positivity))⟩
    have h := log_le_self (inv_pos.2 hy0).le
    rw [log_inv] at h
    linarith [inv_anti₀ hlog3 hy]
  rw [Pi.add_apply, norm_mul, norm_of_nonneg (rpow_nonneg ht0.le _), Real.norm_eq_abs, ← mul_add]
  refine mul_le_mul_of_nonneg_left (habs.trans_eq ?_) (rpow_nonneg ht0.le _)
  rw [log_mul (by norm_num) ht0.ne']
  ring

/-- **Jensen's bound** for the Mellin weight: `η ∫_{t > 1} t^(-1-η) log log(3t) dt` is at most
`log(log 3 + η⁻¹)`. After `t = exp u` this is Jensen's inequality for the concave `log` and the
exponential density, whose mean is `η⁻¹`. -/
theorem mellinWeightIntegral_log_log_le {η : ℝ} (hη : 0 < η) :
    mellinWeightIntegral η (fun t ↦ log (log (3 * t))) ≤ log (log 3 + η⁻¹) := by
  -- bound `log y` by its tangent line at `m = log 3 + η⁻¹`, which is affine in `log t`
  set m := log 3 + η⁻¹ with hm_def
  have hm : 0 < m := add_pos (log_pos (by norm_num)) (inv_pos.2 hη)
  set a := log m + (log 3 - m) / m with ha
  have hc : IntegrableOn (fun t ↦ t ^ (-1 - η) * a) (Ioi 1) :=
    (integrableOn_rpow_neg_one_sub hη).mul_const a
  have hl : IntegrableOn (fun t ↦ t ^ (-1 - η) * (m⁻¹ * log t)) (Ioi 1) :=
    IntegrableOn.congr_fun ((integrableOn_rpow_mul_log hη).const_mul m⁻¹) (fun t _ ↦ by ring)
      measurableSet_Ioi
  calc mellinWeightIntegral η (fun t ↦ log (log (3 * t)))
      ≤ mellinWeightIntegral η (fun t ↦ a + m⁻¹ * log t) := by
        refine mellinWeightIntegral_mono hη.le (integrableOn_rpow_mul_log_log hη)
          ((hc.add hl).congr_fun (fun t _ ↦ by simp only [Pi.add_apply]; ring) measurableSet_Ioi)
          fun t ht ↦ ?_
        have ht0 : 0 < t := zero_lt_one.trans ht
        have hy0 : 0 < log (3 * t) := log_pos (by linarith [mem_Ioi.1 ht])
        -- the tangent line of `log` at `m`
        have h := log_le_sub_one_of_pos (div_pos hy0 hm)
        rw [log_div hy0.ne' hm.ne'] at h
        rw [log_mul (by norm_num) ht0.ne'] at h ⊢
        have e : (log 3 + log t) / m = (log 3 - m) / m + 1 + m⁻¹ * log t := by
          field_simp
          ring
        rw [ha]
        linarith
    _ = mellinWeightIntegral η ((fun _ ↦ a) + m⁻¹ • log) :=
        mellinWeightIntegral_congr fun t _ ↦ by rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    _ = log m := by
        rw [mellinWeightIntegral_add (f := fun _ ↦ a) (g := m⁻¹ • log) hc hl,
          mellinWeightIntegral_const hη, mellinWeightIntegral_smul, mellinWeightIntegral_log hη,
          smul_eq_mul, ha, hm_def]
        ring

/-- The absolute form of Jensen's bound used for small `η`: `log(log 3 + η⁻¹) ≤ 2 log(2/η)` for
`0 < η ≤ 1`. -/
theorem log_log_three_add_inv_le {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    log (log 3 + η⁻¹) ≤ 2 * log (2 / η) := by
  have hlog3 : log 3 ≤ 2 := by linarith [log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)]
  have hinv : 1 ≤ η⁻¹ := (one_le_inv₀ hη).2 hη1
  rw [← log_rpow (by positivity), rpow_two]
  refine log_le_log (add_pos (log_pos (by norm_num)) (inv_pos.2 hη)) ?_
  rw [div_pow, div_eq_mul_inv, ← inv_pow]
  nlinarith

end TauCeti

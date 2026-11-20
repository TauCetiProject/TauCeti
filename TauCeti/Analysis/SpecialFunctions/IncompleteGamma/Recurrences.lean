/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Upper
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Complex.SlitPlane

/-!
# Recurrences of the complex incomplete Gamma functions

The recurrence relations in the parameter of the incomplete Gamma functions (DLMF §8.8). For the
lower functions `γ(a, z)`, `P(a, z)` and `Q(a, z)` they follow from the recurrence
`γ*(a, z) = z γ*(a + 1, z) + e^{−z} / Γ(a + 1)` of Tricomi's function. For the upper
function `Γ(a, z)`, defined by the integral along the horizontal ray from `z`, the one-step
recurrence is an integration by parts along that ray, which stays in the slit plane.

## Main results

* `Complex.lowerIncompleteGamma_add_one`, `Complex.upperIncompleteGamma_add_one`:
  `γ(a + 1, z) = a γ(a, z) − z^a e^{−z}` for `a ∉ −ℕ` (DLMF 8.8.1), and
  `Γ(a + 1, z) = a Γ(a, z) + z^a e^{−z}` on the slit plane for every `a` (DLMF 8.8.2);
* `Complex.lowerIncompleteGamma_add_two`, `Complex.upperIncompleteGamma_add_two`: the three-term
  recurrence `w(a + 2, z) = (a + z + 1) w(a + 1, z) − a z w(a, z)` (DLMF 8.8.3);
* `Complex.regularizedGamma_add_one`, `Complex.regularizedGammaQ_add_one`: the one-step
  recurrences of `P` and `Q` (DLMF 8.8.5–8.8.6), for `z ≠ 0` and every `a`;
* `Complex.lowerIncompleteGamma_add_natCast`,
  `Complex.lowerIncompleteGamma_eq_lowerIncompleteGamma_sub_natCast`,
  `Complex.upperIncompleteGamma_add_natCast`,
  `Complex.upperIncompleteGamma_eq_upperIncompleteGamma_sub_natCast`,
  `Complex.regularizedGamma_add_natCast`, `Complex.regularizedGammaQ_add_natCast`: the iterated
  recurrences (DLMF 8.8.7–8.8.12).

## Implementation notes

DLMF 8.8.4, `γ*(a − 1, z) = z γ*(a, z) + e^{−z} / Γ(a)`, is
`Complex.tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one` at `a − 1`.

The quotients of Gamma values in DLMF 8.8.7–8.8.10 are written as Pochhammer symbols:
`Γ(a + n) / Γ(a) = (a)ₙ`, `Γ(a + n) / Γ(a + k + 1) = (a + k + 1)_{n−k−1}`,
`Γ(a) / Γ(a − n) = (a − n)ₙ` and `Γ(a) / Γ(a − k) = (a − k)ₖ`. In this form the recurrences of
`Γ(a, z)` hold for every parameter `a`, including the poles of `Γ`.

## References

* NIST Digital Library of Mathematical Functions, §8.8, <https://dlmf.nist.gov/8.8>.

The statements follow the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), files
`DLMF/IncompleteGamma/SeriesRecurrences.lean`, `DLMF/IncompleteGamma/ContinuedProperties.lean`
and `DLMF/IncompleteGamma/Regularized.lean`. The proofs are new and work from the definitions
here; only the reversal of the summation for the downward recurrences follows lean-DLMF's
`incompleteGamma_shift_sum_reverse`.
-/

public section

noncomputable section

open Filter Finset MeasureTheory Set
open scoped Topology

namespace Complex

/-! ### The regularized functions `P` and `Q` -/

/-- **DLMF 8.8.5**: `P(a + 1, z) = P(a, z) − z^a e^{−z} / Γ(a + 1)` for `z ≠ 0`. -/
theorem regularizedGamma_add_one (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    regularizedGamma (a + 1) z = regularizedGamma a z - z ^ a * cexp (-z) / Gamma (a + 1) := by
  rw [regularizedGamma_def, regularizedGamma_def,
    tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one a z, cpow_add _ _ hz, cpow_one]
  ring

/-- **DLMF 8.8.6**: `Q(a + 1, z) = Q(a, z) + z^a e^{−z} / Γ(a + 1)` for `z ≠ 0`. -/
theorem regularizedGammaQ_add_one (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    regularizedGammaQ (a + 1) z = regularizedGammaQ a z + z ^ a * cexp (-z) / Gamma (a + 1) := by
  rw [regularizedGammaQ_def, regularizedGammaQ_def, regularizedGamma_add_one a hz]
  ring

/-- **DLMF 8.8.11**: `P(a + n, z) = P(a, z) − z^a e^{−z} ∑_{k<n} z^k / Γ(a + k + 1)` for
`z ≠ 0`. -/
theorem regularizedGamma_add_natCast (a : ℂ) {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    regularizedGamma (a + n) z =
      regularizedGamma a z - z ^ a * cexp (-z) * ∑ k ∈ range n, z ^ k / Gamma (a + k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, regularizedGamma_add_one _ hz, ih, sum_range_succ,
      cpow_add _ _ hz, cpow_natCast]
    ring

/-- **DLMF 8.8.12**: `Q(a + n, z) = Q(a, z) + z^a e^{−z} ∑_{k<n} z^k / Γ(a + k + 1)` for
`z ≠ 0`. -/
theorem regularizedGammaQ_add_natCast (a : ℂ) {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    regularizedGammaQ (a + n) z =
      regularizedGammaQ a z + z ^ a * cexp (-z) * ∑ k ∈ range n, z ^ k / Gamma (a + k + 1) := by
  rw [regularizedGammaQ_def, regularizedGammaQ_def, regularizedGamma_add_natCast a hz]
  ring

/-! ### The lower function `γ` -/

/-- The finite sum of the iterated recurrences satisfies
`S_{n+1} = (a + n) Sₙ + zⁿ`, where `Sₙ = ∑_{k<n} (a + k + 1)_{n−k−1} z^k`. -/
theorem sum_range_succ_ascPochhammer_mul_pow (a z : ℂ) (n : ℕ) :
    ∑ k ∈ range (n + 1), (ascPochhammer ℂ (n + 1 - k - 1)).eval (a + k + 1) * z ^ k =
      (a + n) * ∑ k ∈ range n, (ascPochhammer ℂ (n - k - 1)).eval (a + k + 1) * z ^ k +
        z ^ n := by
  rw [sum_range_succ, show n + 1 - n - 1 = 0 by omega, ascPochhammer_zero,
    Polynomial.eval_one, one_mul, mul_sum]
  congr 1
  refine sum_congr rfl fun k hk => ?_
  have hk : k < n := mem_range.mp hk
  rw [show n + 1 - k - 1 = n - k - 1 + 1 by omega, ascPochhammer_succ_eval,
    Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

/-- A parameter off `−ℕ` stays off `−ℕ` after adding a natural number. -/
private theorem add_natCast_ne_neg_natCast {a : ℂ} (ha : ∀ m : ℕ, a ≠ -m) (n m : ℕ) :
    a + n ≠ -m := fun h => ha (m + n) (by push_cast; linear_combination h)

/-- **DLMF 8.8.1**: `γ(a + 1, z) = a γ(a, z) − z^a e^{−z}` for `a ∉ −ℕ` and every `z`. -/
theorem lowerIncompleteGamma_add_one {a : ℂ} (ha : ∀ m : ℕ, a ≠ -m) (z : ℂ) :
    lowerIncompleteGamma (a + 1) z = a * lowerIncompleteGamma a z - z ^ a * cexp (-z) := by
  have ha0 : a ≠ 0 := by simpa using ha 0
  rcases eq_or_ne z 0 with rfl | hz
  · simp [zero_cpow ha0]
  have hG : Gamma (a + 1) ≠ 0 := Gamma_ne_zero (by simpa using add_natCast_ne_neg_natCast ha 1)
  rw [lowerIncompleteGamma_def, lowerIncompleteGamma_def, regularizedGamma_add_one a hz,
    mul_sub, mul_div_cancel₀ _ hG, Gamma_add_one a ha0]
  ring

/-- **DLMF 8.8.3** for `γ`: `γ(a + 2, z) = (a + z + 1) γ(a + 1, z) − a z γ(a, z)` for
`a ∉ −ℕ` and every `z`. -/
theorem lowerIncompleteGamma_add_two {a : ℂ} (ha : ∀ m : ℕ, a ≠ -m) (z : ℂ) :
    lowerIncompleteGamma (a + 2) z =
      (a + z + 1) * lowerIncompleteGamma (a + 1) z - a * z * lowerIncompleteGamma a z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have h0 := lowerIncompleteGamma_add_one ha z
  have h1 := lowerIncompleteGamma_add_one (by simpa using add_natCast_ne_neg_natCast ha 1) z
  rw [add_assoc, one_add_one_eq_two, cpow_add _ _ hz, cpow_one] at h1
  linear_combination h1 - z * h0

/-- **DLMF 8.8.7**: for `a ∉ −ℕ` and every `z`,
`γ(a + n, z) = (a)ₙ γ(a, z) − z^a e^{−z} ∑_{k<n} (a + k + 1)_{n−k−1} z^k`, where
`(a + k + 1)_{n−k−1} = Γ(a + n) / Γ(a + k + 1)`. -/
theorem lowerIncompleteGamma_add_natCast {a : ℂ} (ha : ∀ m : ℕ, a ≠ -m) (z : ℂ) (n : ℕ) :
    lowerIncompleteGamma (a + n) z =
      (ascPochhammer ℂ n).eval a * lowerIncompleteGamma a z -
        z ^ a * cexp (-z) *
          ∑ k ∈ range n, (ascPochhammer ℂ (n - k - 1)).eval (a + k + 1) * z ^ k := by
  have ha0 : a ≠ 0 := by simpa using ha 0
  rcases eq_or_ne z 0 with rfl | hz
  · simp [zero_cpow ha0]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, lowerIncompleteGamma_add_one (add_natCast_ne_neg_natCast ha n),
      ih, cpow_add _ _ hz, cpow_natCast, ascPochhammer_succ_eval,
      sum_range_succ_ascPochhammer_mul_pow]
    ring

/-- Reversing the order of summation turns the correction sum of the upward recurrences at
`a − n` into that of the downward recurrences:
`z^{a−n} ∑_{k<n} (a − n + k + 1)_{n−k−1} z^k = z^{a−1} ∑_{k<n} (a − k)ₖ / z^k` for `z ≠ 0`. -/
theorem cpow_sub_natCast_mul_sum_ascPochhammer_mul_pow (a : ℂ) {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    z ^ (a - n) * ∑ k ∈ range n, (ascPochhammer ℂ (n - k - 1)).eval (a - n + k + 1) * z ^ k =
      z ^ (a - 1) * ∑ k ∈ range n, (ascPochhammer ℂ k).eval (a - k) / z ^ k := by
  rw [mul_sum, mul_sum, ← sum_range_reflect]
  refine sum_congr rfl fun k hk => ?_
  have hk : k < n := mem_range.mp hk
  have hpow : z ^ (a - n) * z ^ (n - 1 - k) * z ^ k = z ^ (a - 1) := by
    rw [mul_assoc, ← pow_add, show n - 1 - k + k = n - 1 by omega, ← cpow_natCast,
      ← cpow_add _ _ hz, Nat.cast_sub (by omega)]
    congr 1
    push_cast
    ring
  rw [show n - (n - 1 - k) - 1 = k by omega, Nat.cast_sub (by omega), Nat.cast_sub (by omega),
    ← hpow]
  field_simp
  congr 2
  push_cast
  ring

/-- **DLMF 8.8.8**: for `a − n ∉ −ℕ` and every `z`,
`γ(a, z) = (a − n)ₙ γ(a − n, z) − z^{a−1} e^{−z} ∑_{k<n} (a − k)ₖ / z^k`, where
`(a − n)ₙ = Γ(a) / Γ(a − n)` and `(a − k)ₖ = Γ(a) / Γ(a − k)`. -/
theorem lowerIncompleteGamma_eq_lowerIncompleteGamma_sub_natCast {a : ℂ} {n : ℕ}
    (ha : ∀ m : ℕ, a - n ≠ -m) (z : ℂ) :
    lowerIncompleteGamma a z =
      (ascPochhammer ℂ n).eval (a - n) * lowerIncompleteGamma (a - n) z -
        z ^ (a - 1) * cexp (-z) * ∑ k ∈ range n, (ascPochhammer ℂ k).eval (a - k) / z ^ k := by
  rcases eq_or_ne z 0 with rfl | hz
  · rcases n with _ | n
    · simp
    have ha1 : a - 1 ≠ 0 := fun h => ha n (by push_cast; linear_combination h)
    simp [zero_cpow ha1]
  have h := lowerIncompleteGamma_add_natCast ha z n
  rw [sub_add_cancel] at h
  rw [h, mul_right_comm _ (cexp (-z)), mul_right_comm _ (cexp (-z)),
    cpow_sub_natCast_mul_sum_ascPochhammer_mul_pow a hz n]

/-! ### The upper function `Γ` -/

/-- The integrand `(z + t)^{a−1} e^{−(z+t)}` of `Γ(a, z)` along the horizontal ray is integrable
when `z` lies in the slit plane. -/
theorem integrableOn_cpow_mul_exp_neg_add {z : ℂ} (hz : z ∈ slitPlane) (a : ℂ) :
    IntegrableOn (fun t : ℝ => (z + t) ^ (a - 1) * cexp (-(z + t))) (Ioi 0) := by
  refine IntegrableOn.congr_fun
    ((integrableOn_upperIncompleteGamma_integrand a hz).const_mul (cexp (-z)))
    (fun t _ => ?_) measurableSet_Ioi
  rw [neg_add, exp_add]
  ring

/-- The derivative along the ray of `−(z + t)^a e^{−(z+t)}`, for `z` in the slit plane and real
`t ≥ 0`. -/
theorem hasDerivAt_neg_cpow_mul_exp_neg_add {z : ℂ} (hz : z ∈ slitPlane) (a : ℂ) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivAt (fun s : ℝ => -((z + s) ^ a * cexp (-(z + s))))
      ((z + t) ^ a * cexp (-(z + t)) - a * ((z + t) ^ (a - 1) * cexp (-(z + t)))) t := by
  have hmem : z + t ∈ slitPlane := by
    simpa only [add_comm] using TauCeti.ofReal_add_mem_slitPlane hz ht
  have hlin : HasDerivAt (fun w : ℂ => z + w) 1 t := (hasDerivAt_id _).const_add z
  have h : HasDerivAt (fun w : ℂ => -((z + w) ^ a * cexp (-(z + w))))
      (-(a * (z + t) ^ (a - 1) * 1 * cexp (-(z + t)) + (z + t) ^ a * (cexp (-(z + t)) * -1))) t :=
    ((hlin.cpow_const hmem).mul hlin.neg.cexp).neg
  convert h.comp_ofReal using 1
  ring

/-- **DLMF 8.8.2**: `Γ(a + 1, z) = a Γ(a, z) + z^a e^{−z}` for `z` in the slit plane and every
`a`. -/
theorem upperIncompleteGamma_add_one {z : ℂ} (hz : z ∈ slitPlane) (a : ℂ) :
    upperIncompleteGamma (a + 1) z = a * upperIncompleteGamma a z + z ^ a * cexp (-z) := by
  have h₁ := integrableOn_cpow_mul_exp_neg_add hz (a + 1)
  have h₀ := (integrableOn_cpow_mul_exp_neg_add hz a).const_mul a
  simp only [add_sub_cancel_right] at h₁
  have hderiv := fun t (ht : t ∈ Ici (0 : ℝ)) => hasDerivAt_neg_cpow_mul_exp_neg_add hz a ht
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (h₁.sub h₀)
    (tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
      (fun t ht => hderiv t (mem_Ici_of_Ioi ht)) (h₁.sub h₀) h₁.neg)
  rw [integral_sub h₁ h₀, integral_const_mul] at h
  rw [upperIncompleteGamma_eq_integral, upperIncompleteGamma_eq_integral, add_sub_cancel_right]
  simp only [ofReal_zero, add_zero, zero_sub, neg_neg] at h
  linear_combination h

/-- **DLMF 8.8.3** for `Γ`: `Γ(a + 2, z) = (a + z + 1) Γ(a + 1, z) − a z Γ(a, z)` for `z` in the
slit plane and every `a`. -/
theorem upperIncompleteGamma_add_two {z : ℂ} (hz : z ∈ slitPlane) (a : ℂ) :
    upperIncompleteGamma (a + 2) z =
      (a + z + 1) * upperIncompleteGamma (a + 1) z - a * z * upperIncompleteGamma a z := by
  have h0 := upperIncompleteGamma_add_one hz a
  have h1 := upperIncompleteGamma_add_one hz (a + 1)
  rw [add_assoc, one_add_one_eq_two, cpow_add _ _ (slitPlane_ne_zero hz), cpow_one] at h1
  linear_combination h1 - z * h0

/-- **DLMF 8.8.9**: for `z` in the slit plane and every `a`,
`Γ(a + n, z) = (a)ₙ Γ(a, z) + z^a e^{−z} ∑_{k<n} (a + k + 1)_{n−k−1} z^k`, where
`(a + k + 1)_{n−k−1} = Γ(a + n) / Γ(a + k + 1)`. -/
theorem upperIncompleteGamma_add_natCast {z : ℂ} (hz : z ∈ slitPlane) (a : ℂ) (n : ℕ) :
    upperIncompleteGamma (a + n) z =
      (ascPochhammer ℂ n).eval a * upperIncompleteGamma a z +
        z ^ a * cexp (-z) *
          ∑ k ∈ range n, (ascPochhammer ℂ (n - k - 1)).eval (a + k + 1) * z ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, upperIncompleteGamma_add_one hz, ih,
      cpow_add _ _ (slitPlane_ne_zero hz), cpow_natCast, ascPochhammer_succ_eval,
      sum_range_succ_ascPochhammer_mul_pow]
    ring

/-- **DLMF 8.8.10**: for `z` in the slit plane and every `a`,
`Γ(a, z) = (a − n)ₙ Γ(a − n, z) + z^{a−1} e^{−z} ∑_{k<n} (a − k)ₖ / z^k`, where
`(a − n)ₙ = Γ(a) / Γ(a − n)` and `(a − k)ₖ = Γ(a) / Γ(a − k)`. -/
theorem upperIncompleteGamma_eq_upperIncompleteGamma_sub_natCast {z : ℂ} (hz : z ∈ slitPlane)
    (a : ℂ) (n : ℕ) :
    upperIncompleteGamma a z =
      (ascPochhammer ℂ n).eval (a - n) * upperIncompleteGamma (a - n) z +
        z ^ (a - 1) * cexp (-z) * ∑ k ∈ range n, (ascPochhammer ℂ k).eval (a - k) / z ^ k := by
  have h := upperIncompleteGamma_add_natCast hz (a - n) n
  rw [sub_add_cancel] at h
  rw [h, mul_right_comm _ (cexp (-z)), mul_right_comm _ (cexp (-z)),
    cpow_sub_natCast_mul_sum_ascPochhammer_mul_pow a (slitPlane_ne_zero hz) n]

end Complex

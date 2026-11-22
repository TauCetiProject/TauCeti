/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Upper
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# Recurrences of the complex incomplete Gamma functions

The recurrence relations in the parameter of the incomplete Gamma functions (DLMF §8.8). For the
lower function `γ(a, z)` and the regularized lower function `P(a, z)` they follow from the
recurrence `γ*(a, z) = z γ*(a + 1, z) + e^{−z} / Γ(a + 1)` of Tricomi's function. The recurrences
of the regularized upper function `Q(a, z)` follow from those of `P` through `Q = 1 − P`. For the
upper function `Γ(a, z)`, defined by the integral along the horizontal ray from `z`, the one-step
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

In 8.8.4–8.8.6, 8.8.11 and 8.8.12 a quotient `w / Γ(b)` stands for `w` times the reciprocal Gamma
function `1 / Γ`, which is entire and vanishes at every nonpositive integer. Mathlib's
`Complex.Gamma` takes the value `0` at the nonpositive integers, and Lean's division by `0` gives
`0`, so the quotient written with Lean's division has exactly this value at the poles of `Γ`. The
formulas therefore hold at every parameter `a`.

The quotients of Gamma values in DLMF 8.8.7–8.8.10 are written as their polynomial extensions,
the Pochhammer symbols `(a)ₙ`, `(a + k + 1)_{n−k−1}`, `(a − n)ₙ` and `(a − k)ₖ`. Away from the
poles of `Γ` these equal `Γ(a + n) / Γ(a)`, `Γ(a + n) / Γ(a + k + 1)`, `Γ(a) / Γ(a − n)` and
`Γ(a) / Γ(a − k)`. In this form the recurrences of `Γ(a, z)` hold for every parameter `a`,
including the poles of `Γ`, where the quotients are not defined.

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

/-- **DLMF 8.8.5**: `P(a + 1, z) = P(a, z) − z^a e^{−z} / Γ(a + 1)` for `z ≠ 0` and every `a`.
At the poles of `Γ` the quotient is `0`, the value of the entire function `1 / Γ` there. -/
theorem regularizedGamma_add_one (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    regularizedGamma (a + 1) z = regularizedGamma a z - z ^ a * cexp (-z) / Gamma (a + 1) := by
  rw [regularizedGamma_def, regularizedGamma_def,
    tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one a z, cpow_add _ _ hz, cpow_one]
  ring

/-- **DLMF 8.8.6**: `Q(a + 1, z) = Q(a, z) + z^a e^{−z} / Γ(a + 1)` for `z ≠ 0` and every `a`.
At the poles of `Γ` the quotient is `0`, the value of the entire function `1 / Γ` there. -/
theorem regularizedGammaQ_add_one (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    regularizedGammaQ (a + 1) z = regularizedGammaQ a z + z ^ a * cexp (-z) / Gamma (a + 1) := by
  rw [regularizedGammaQ_def, regularizedGammaQ_def, regularizedGamma_add_one a hz]
  ring

/-- **DLMF 8.8.11**: `P(a + n, z) = P(a, z) − z^a e^{−z} ∑_{k<n} z^k / Γ(a + k + 1)` for
`z ≠ 0` and every `a`. A summand whose `a + k + 1` is a pole of `Γ` is `0`, the value of the
entire function `1 / Γ` there. -/
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
`z ≠ 0` and every `a`. A summand whose `a + k + 1` is a pole of `Γ` is `0`, the value of the
entire function `1 / Γ` there. -/
theorem regularizedGammaQ_add_natCast (a : ℂ) {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    regularizedGammaQ (a + n) z =
      regularizedGammaQ a z + z ^ a * cexp (-z) * ∑ k ∈ range n, z ^ k / Gamma (a + k + 1) := by
  rw [regularizedGammaQ_def, regularizedGammaQ_def, regularizedGamma_add_natCast a hz]
  ring

/-! ### The lower function `γ` -/

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
      TauCeti.sum_range_succ_ascPochhammer_mul_pow]
    ring

/-- The correction term of the upward recurrences 8.8.7 and 8.8.9 at `a − n` is the correction
term of the downward recurrences 8.8.8 and 8.8.10:
`z^{a−n} e^{−z} ∑_{k<n} (a − n + k + 1)_{n−k−1} z^k = z^{a−1} e^{−z} ∑_{k<n} (a − k)ₖ / z^k`
for `z ≠ 0`. -/
private lemma cpow_sub_natCast_mul_exp_mul_sum_ascPochhammer (a : ℂ) {z : ℂ} (hz : z ≠ 0)
    (n : ℕ) :
    z ^ (a - n) * cexp (-z) *
        ∑ k ∈ range n, (ascPochhammer ℂ (n - k - 1)).eval (a - n + k + 1) * z ^ k =
      z ^ (a - 1) * cexp (-z) * ∑ k ∈ range n, (ascPochhammer ℂ k).eval (a - k) / z ^ k := by
  simp only [TauCeti.ascPochhammer_eval_sub_natCast_add_add_one a n]
  rw [mul_right_comm _ (cexp (-z)), cpow_sub_natCast_mul_sum_mul_pow a hz n
    fun j => (ascPochhammer ℂ j).eval (a - j), mul_right_comm _ (cexp (-z))]

/-- **DLMF 8.8.8**: for `a − n ∉ −ℕ` and every `z`,
`γ(a, z) = (a − n)ₙ γ(a − n, z) − z^{a−1} e^{−z} ∑_{k<n} (a − k)ₖ / z^k`, where
`(a − n)ₙ = Γ(a) / Γ(a − n)` and `(a − k)ₖ = Γ(a) / Γ(a − k)`. The inverse powers use Lean's
totalized division: at `z = 0` the summands with `k > 0` are `0`, and the identity reduces to
`0 = 0`, since both `γ(a, 0)` and `γ(a − n, 0)` vanish and so does `0 ^ (a − 1)` for `n > 0`. -/
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
  rwa [sub_add_cancel, cpow_sub_natCast_mul_exp_mul_sum_ascPochhammer a hz n] at h

/-! ### The upper function `Γ` -/

/-- **DLMF 8.8.2**: `Γ(a + 1, z) = a Γ(a, z) + z^a e^{−z}` for `z` in the slit plane and every
`a`. -/
theorem upperIncompleteGamma_add_one {z : ℂ} (hz : z ∈ slitPlane) (a : ℂ) :
    upperIncompleteGamma (a + 1) z = a * upperIncompleteGamma a z + z ^ a * cexp (-z) := by
  have h₁ := integrableOn_upperIncompleteGamma_integrand (a + 1) hz
  have h₀ := (integrableOn_upperIncompleteGamma_integrand a hz).const_mul a
  simp only [add_sub_cancel_right] at h₁
  -- The derivative along the ray of `−(z + t)^a e^{−(z+t)}`; the ray stays in the slit plane.
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun s : ℝ => -((z + s) ^ a * cexp (-(z + s))))
      ((z + t) ^ a * cexp (-(z + t)) - a * ((z + t) ^ (a - 1) * cexp (-(z + t)))) t := by
    intro t ht
    have hmem : z + t ∈ slitPlane := by
      simpa only [add_comm] using TauCeti.ofReal_add_mem_slitPlane hz ht
    have hlin : HasDerivAt (fun w : ℂ => z + w) 1 t := (hasDerivAt_id _).const_add z
    have h : HasDerivAt (fun w : ℂ => -((z + w) ^ a * cexp (-(z + w))))
        (-(a * (z + t) ^ (a - 1) * 1 * cexp (-(z + t)) +
          (z + t) ^ a * (cexp (-(z + t)) * -1))) t :=
      ((hlin.cpow_const hmem).mul hlin.neg.cexp).neg
    convert h.comp_ofReal using 1
    ring
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
`Γ(a + n, z) = (a)ₙ Γ(a, z) + z^a e^{−z} ∑_{k<n} (a + k + 1)_{n−k−1} z^k`. The Pochhammer
coefficients `(a)ₙ` and `(a + k + 1)_{n−k−1}` are the polynomial extensions of the Gamma quotients
`Γ(a + n) / Γ(a)` and `Γ(a + n) / Γ(a + k + 1)` of DLMF, and agree with them away from the poles
of `Γ`. -/
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
      TauCeti.sum_range_succ_ascPochhammer_mul_pow]
    ring

/-- **DLMF 8.8.10**: for `z` in the slit plane and every `a`,
`Γ(a, z) = (a − n)ₙ Γ(a − n, z) + z^{a−1} e^{−z} ∑_{k<n} (a − k)ₖ / z^k`. The Pochhammer
coefficients `(a − n)ₙ` and `(a − k)ₖ` are the polynomial extensions of the Gamma quotients
`Γ(a) / Γ(a − n)` and `Γ(a) / Γ(a − k)` of DLMF, and agree with them away from the poles of
`Γ`. -/
theorem upperIncompleteGamma_eq_upperIncompleteGamma_sub_natCast {z : ℂ} (hz : z ∈ slitPlane)
    (a : ℂ) (n : ℕ) :
    upperIncompleteGamma a z =
      (ascPochhammer ℂ n).eval (a - n) * upperIncompleteGamma (a - n) z +
        z ^ (a - 1) * cexp (-z) * ∑ k ∈ range n, (ascPochhammer ℂ k).eval (a - k) / z ^ k := by
  have h := upperIncompleteGamma_add_natCast hz (a - n) n
  rwa [sub_add_cancel,
    cpow_sub_natCast_mul_exp_mul_sum_ascPochhammer a (slitPlane_ne_zero hz) n] at h

end Complex

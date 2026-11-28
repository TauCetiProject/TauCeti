/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Upper
import TauCeti.Analysis.Calculus.IteratedDeriv.Basic
import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Complementary
import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Recurrences

/-!
# Higher derivatives of the incomplete Gamma functions

The `n`-th derivatives in the argument of the incomplete Gamma functions, weighted by a power or
an exponential (DLMF 8.8.15–8.8.19). Each weighted function has a first derivative that is a
constant times the weighted function at the parameter `a + 1` or `a − 1`; the iteration is
`TauCeti.iteratedDeriv_eqOn_of_derivative_tower`.

## Main results

* `Complex.iteratedDeriv_cpow_neg_mul_lowerIncompleteGamma`:
  `dⁿ/dzⁿ (z^{−a} γ(a, z)) = (−1)ⁿ z^{−a−n} γ(a + n, z)` for `z ≠ 0` and
  `a ∉ {0, −1, …, −(n − 1)}` (DLMF 8.8.15);
* `Complex.iteratedDeriv_cpow_neg_mul_upperIncompleteGamma`:
  `dⁿ/dzⁿ (z^{−a} Γ(a, z)) = (−1)ⁿ z^{−a−n} Γ(a + n, z)` on the slit plane, for every `a`
  (DLMF 8.8.16);
* `Complex.iteratedDeriv_exp_mul_lowerIncompleteGamma`:
  `dⁿ/dzⁿ (e^z γ(a, z)) = (−1)ⁿ (1 − a)ₙ e^z γ(a − n, z)` on the slit plane, for
  `a ∉ {1, …, n}` (DLMF 8.8.17);
* `Complex.iteratedDeriv_cpow_mul_exp_mul_tricomiIncompleteGamma`:
  `dⁿ/dzⁿ (z^a e^z γ*(a, z)) = z^{a−n} e^z γ*(a − n, z)` on the slit plane, for every `a`
  (DLMF 8.8.18);
* `Complex.iteratedDeriv_exp_mul_upperIncompleteGamma`:
  `dⁿ/dzⁿ (e^z Γ(a, z)) = (−1)ⁿ (1 − a)ₙ e^z Γ(a − n, z)` on the slit plane, for every `a`
  (DLMF 8.8.19).

The first derivatives, the cases `n = 1`, are
`Complex.hasDerivAt_cpow_neg_mul_lowerIncompleteGamma`,
`Complex.hasDerivAt_cpow_neg_mul_upperIncompleteGamma`,
`Complex.hasDerivAt_exp_mul_lowerIncompleteGamma`,
`Complex.hasDerivAt_cpow_mul_exp_mul_tricomiIncompleteGamma` and
`Complex.hasDerivAt_exp_mul_upperIncompleteGamma`. Off `0`, `z^{−a} γ(a, z)` equals the entire
function `Γ(a) γ*(a, z)`, so 8.8.15 holds off `0` and not only on the slit plane.

## Implementation notes

The Pochhammer symbol `(1 − a)ₙ` is `(ascPochhammer ℂ n).eval (1 − a)`. DLMF states 8.8.15 for
`a ∉ −ℕ` and 8.8.17 for `a − n ∉ −ℕ`; the hypotheses here are weaker, using that `γ(−m, ·)` is
Mathlib's junk value `0` at the poles of `Γ`. 8.8.15 is stated for `a + k ≠ 0` for every `k < n`:
this admits the poles `a = −n, −n − 1, …`, where both sides are `0`, and excludes
`a = 0, −1, …, −(n − 1)`, where it fails (at `a = −1`, `n = 2` the left side is `0` and the
right side is `z^{−1} γ(1, z) ≠ 0`). 8.8.17 is stated for `a ∉ {1, …, n}`: this admits every
`a ∈ −ℕ`, where both sides are `0`; the excluded values are not poles of `Γ`, but there
`γ(a − n, ·)` hits a pole while `(1 − a)ₙ = 0`, and the formula fails (at `a = 1`, `n = 1` the
left side is the derivative `e^z` of `e^z γ(1, z) = e^z − 1` and the right side is `0`).

## References

* NIST Digital Library of Mathematical Functions, §8.8, <https://dlmf.nist.gov/8.8>.

The statements follow the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/IncompleteGamma/SeriesRecurrences.lean`: `lowerIncompleteGamma_iteratedDeriv_scaled_power`,
`upperIncompleteGamma_iteratedDeriv_scaled_power`, `lowerIncompleteGamma_iteratedDeriv_scaled_exp`,
`tricomiIncompleteGamma_iteratedDeriv_scaled`, `upperIncompleteGamma_iteratedDeriv_scaled_exp`,
`hasDerivAt_exp_mul_lowerIncompleteGamma` and `hasDerivAt_exp_mul_upperIncompleteGamma`. The
proofs of 8.8.17 and 8.8.19 follow lean-DLMF's (induction on the one-step derivatives, from the
recurrences 8.8.1–8.8.2). Those of 8.8.15, 8.8.16 and 8.8.18 are new: they work from Tricomi's
function `Complex.tricomiIncompleteGamma` and the recurrence 8.8.2, where lean-DLMF goes through
Kummer's functions.
-/

public section

noncomputable section

open Filter
open scoped Topology

namespace Complex

/-! ### First derivatives -/

/-- **DLMF 8.8.15** for `n = 1`: for `z ≠ 0`, `z^{−a} γ(a, z)` has derivative
`−z^{−a−1} γ(a + 1, z)` for `a ≠ 0`. At `a = −1, −2, …` both sides are `0`, since `γ(−m, ·)` is
Mathlib's junk value `0`. -/
theorem hasDerivAt_cpow_neg_mul_lowerIncompleteGamma {a : ℂ} (ha : a ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (fun t => t ^ (-a) * lowerIncompleteGamma a t)
      (-(z ^ (-a - 1) * lowerIncompleteGamma (a + 1) z)) z := by
  -- off `0` the function is the entire `Γ(a) γ*(a, ·)`
  have he : (fun t => Gamma a * tricomiIncompleteGamma a t) =ᶠ[𝓝 z]
      fun t => t ^ (-a) * lowerIncompleteGamma a t :=
    eventually_of_mem (isOpen_compl_singleton.mem_nhds hz) fun t ht =>
      (cpow_neg_mul_lowerIncompleteGamma ht a).symm
  refine (((hasDerivAt_tricomiIncompleteGamma a z).const_mul (Gamma a)).congr_of_eventuallyEq
    he.symm).congr_deriv ?_
  rw [show -a - 1 = -(a + 1) by ring, cpow_neg_mul_lowerIncompleteGamma hz, Gamma_add_one a ha]
  ring

/-- **DLMF 8.8.16** for `n = 1`: on the slit plane, `z^{−a} Γ(a, z)` has derivative
`−z^{−a−1} Γ(a + 1, z)` for every `a`. -/
theorem hasDerivAt_cpow_neg_mul_upperIncompleteGamma (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun t => t ^ (-a) * upperIncompleteGamma a t)
      (-(z ^ (-a - 1) * upperIncompleteGamma (a + 1) z)) z := by
  have hz0 := slitPlane_ne_zero hz
  refine (((hasDerivAt_id z).cpow_const hz).mul
    (hasDerivAt_upperIncompleteGamma hz a)).congr_deriv ?_
  simp only [id_eq, mul_one]
  rw [upperIncompleteGamma_add_one hz, cpow_sub _ _ hz0, cpow_sub _ _ hz0, cpow_one]
  ring

/-- **DLMF 8.8.17** for `n = 1`: on the slit plane, `e^z γ(a, z)` has derivative
`(a − 1) e^z γ(a − 1, z)` for `a ≠ 1`. At `a = 0, −1, …` both sides are `0`, since `γ(−m, ·)`
is Mathlib's junk value `0`. -/
theorem hasDerivAt_exp_mul_lowerIncompleteGamma {a : ℂ} (ha : a ≠ 1) {z : ℂ}
    (hz : z ∈ slitPlane) :
    HasDerivAt (fun t => cexp t * lowerIncompleteGamma a t)
      ((a - 1) * cexp z * lowerIncompleteGamma (a - 1) z) z := by
  by_cases ha' : ∀ m : ℕ, a ≠ -m
  swap
  · push Not at ha'
    obtain ⟨m, rfl⟩ := ha'
    rw [show -(m : ℂ) - 1 = -((m + 1 : ℕ) : ℂ) by push_cast; ring,
      lowerIncompleteGamma_neg_natCast, lowerIncompleteGamma_neg_natCast]
    simpa using hasDerivAt_const z (0 : ℂ)
  have ha1 : ∀ m : ℕ, a - 1 ≠ -m := by
    rintro (_ | m) h
    · exact ha (by simpa [sub_eq_zero] using h)
    · exact ha' m (by push_cast at h; linear_combination h)
  refine ((hasDerivAt_exp z).mul (hasDerivAt_lowerIncompleteGamma a ha' hz)).congr_deriv ?_
  have h := lowerIncompleteGamma_add_one ha1 z
  rw [sub_add_cancel] at h
  rw [h, mul_sub, exp_neg]
  field_simp
  ring

/-- **DLMF 8.8.18** for `n = 1`: on the slit plane, `z^a e^z γ*(a, z)` has derivative
`z^{a−1} e^z γ*(a − 1, z)` for every `a`. -/
theorem hasDerivAt_cpow_mul_exp_mul_tricomiIncompleteGamma (a : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    HasDerivAt (fun t => t ^ a * cexp t * tricomiIncompleteGamma a t)
      (z ^ (a - 1) * cexp z * tricomiIncompleteGamma (a - 1) z) z := by
  have hz0 := slitPlane_ne_zero hz
  refine ((((hasDerivAt_id z).cpow_const hz).mul (hasDerivAt_exp z)).mul
    (hasDerivAt_tricomiIncompleteGamma a z)).congr_deriv ?_
  have h₀ := tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one (a - 1) z
  have h₁ := tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one a z
  have hΓ := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one a
  have hp : z ^ a = z ^ (a - 1) * z := by
    rw [cpow_sub _ _ hz0, cpow_one, div_mul_cancel₀ _ hz0]
  rw [sub_add_cancel] at h₀
  simp only [id_eq, mul_one, div_eq_mul_inv, Pi.mul_apply] at h₀ h₁ hΓ ⊢
  rw [hp]
  linear_combination z ^ (a - 1) * cexp z * (a * h₁ - h₀) -
    z ^ (a - 1) * cexp z * cexp (-z) * hΓ

/-- **DLMF 8.8.19** for `n = 1`: on the slit plane, `e^z Γ(a, z)` has derivative
`(a − 1) e^z Γ(a − 1, z)` for every `a`. -/
theorem hasDerivAt_exp_mul_upperIncompleteGamma (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun t => cexp t * upperIncompleteGamma a t)
      ((a - 1) * cexp z * upperIncompleteGamma (a - 1) z) z := by
  refine ((hasDerivAt_exp z).mul (hasDerivAt_upperIncompleteGamma hz a)).congr_deriv ?_
  have h := upperIncompleteGamma_add_one hz (a - 1)
  rw [sub_add_cancel] at h
  rw [h, exp_neg]
  field_simp
  ring

/-! ### Higher derivatives -/

/-- **DLMF 8.8.15**: for `z ≠ 0`, `dⁿ/dzⁿ (z^{−a} γ(a, z)) = (−1)ⁿ z^{−a−n} γ(a + n, z)` for
`a ∉ {0, −1, …, −(n − 1)}`, in particular for `a ∉ −ℕ`. -/
theorem iteratedDeriv_cpow_neg_mul_lowerIncompleteGamma (n : ℕ) {a : ℂ}
    (ha : ∀ k < n, a + k ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    iteratedDeriv n (fun t => t ^ (-a) * lowerIncompleteGamma a t) z =
      (-1) ^ n * z ^ (-a - n) * lowerIncompleteGamma (a + n) z := by
  have h := TauCeti.iteratedDeriv_eqOn_of_derivative_tower
    (F := fun k t => (-1) ^ k * (t ^ (-(a + k)) * lowerIncompleteGamma (a + k) t))
    isOpen_compl_singleton (n := n) (fun k hk t ht => by
      convert ((hasDerivAt_cpow_neg_mul_lowerIncompleteGamma (ha k hk) ht).const_mul
        ((-1) ^ k)) using 1
      push_cast
      ring_nf) hz
  simp only [CharP.cast_eq_zero, add_zero, pow_zero, one_mul] at h
  rw [h, neg_add']
  ring

/-- **DLMF 8.8.16**: on the slit plane, `dⁿ/dzⁿ (z^{−a} Γ(a, z)) = (−1)ⁿ z^{−a−n} Γ(a + n, z)`
for every `a`. -/
theorem iteratedDeriv_cpow_neg_mul_upperIncompleteGamma (n : ℕ) (a : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => t ^ (-a) * upperIncompleteGamma a t) z =
      (-1) ^ n * z ^ (-a - n) * upperIncompleteGamma (a + n) z := by
  have h := TauCeti.iteratedDeriv_eqOn_of_derivative_tower
    (F := fun k t => (-1) ^ k * (t ^ (-(a + k)) * upperIncompleteGamma (a + k) t))
    isOpen_slitPlane (n := n) (fun k _ t ht => by
      convert ((hasDerivAt_cpow_neg_mul_upperIncompleteGamma (a + k) ht).const_mul
        ((-1) ^ k)) using 1
      push_cast
      ring_nf) hz
  simp only [CharP.cast_eq_zero, add_zero, pow_zero, one_mul] at h
  rw [h, neg_add']
  ring

/-- **DLMF 8.8.17**: on the slit plane,
`dⁿ/dzⁿ (e^z γ(a, z)) = (−1)ⁿ (1 − a)ₙ e^z γ(a − n, z)` for `a ∉ {1, …, n}`, in particular for
`a − n ∉ −ℕ`. -/
theorem iteratedDeriv_exp_mul_lowerIncompleteGamma (n : ℕ) {a : ℂ}
    (ha : ∀ k < n, a - k ≠ 1) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => cexp t * lowerIncompleteGamma a t) z =
      (-1) ^ n * (ascPochhammer ℂ n).eval (1 - a) * cexp z * lowerIncompleteGamma (a - n) z := by
  have h := TauCeti.iteratedDeriv_eqOn_of_derivative_tower
    (F := fun k t => (-1) ^ k * (ascPochhammer ℂ k).eval (1 - a) *
      (cexp t * lowerIncompleteGamma (a - k) t))
    isOpen_slitPlane (n := n) (fun k hk t ht => by
      convert (hasDerivAt_exp_mul_lowerIncompleteGamma (ha k hk) ht).const_mul
        ((-1) ^ k * (ascPochhammer ℂ k).eval (1 - a)) using 1
      rw [ascPochhammer_succ_eval]
      push_cast
      ring_nf) hz
  simp only [CharP.cast_eq_zero, sub_zero, pow_zero, ascPochhammer_zero, Polynomial.eval_one,
    one_mul] at h
  rw [h]
  ring

/-- **DLMF 8.8.18**: on the slit plane, `dⁿ/dzⁿ (z^a e^z γ*(a, z)) = z^{a−n} e^z γ*(a − n, z)`
for every `a`. -/
theorem iteratedDeriv_cpow_mul_exp_mul_tricomiIncompleteGamma (n : ℕ) (a : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => t ^ a * cexp t * tricomiIncompleteGamma a t) z =
      z ^ (a - n) * cexp z * tricomiIncompleteGamma (a - n) z := by
  have h := TauCeti.iteratedDeriv_eqOn_of_derivative_tower
    (F := fun k t => t ^ (a - k) * cexp t * tricomiIncompleteGamma (a - k) t)
    isOpen_slitPlane (n := n) (fun k _ t ht => by
      convert hasDerivAt_cpow_mul_exp_mul_tricomiIncompleteGamma (a - k) ht using 1
      push_cast
      ring_nf) hz
  simpa using h

/-- **DLMF 8.8.19**: on the slit plane,
`dⁿ/dzⁿ (e^z Γ(a, z)) = (−1)ⁿ (1 − a)ₙ e^z Γ(a − n, z)` for every `a`. -/
theorem iteratedDeriv_exp_mul_upperIncompleteGamma (n : ℕ) (a : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => cexp t * upperIncompleteGamma a t) z =
      (-1) ^ n * (ascPochhammer ℂ n).eval (1 - a) * cexp z * upperIncompleteGamma (a - n) z := by
  have h := TauCeti.iteratedDeriv_eqOn_of_derivative_tower
    (F := fun k t => (-1) ^ k * (ascPochhammer ℂ k).eval (1 - a) *
      (cexp t * upperIncompleteGamma (a - k) t))
    isOpen_slitPlane (n := n) (fun k _ t ht => by
      convert (hasDerivAt_exp_mul_upperIncompleteGamma (a - k) ht).const_mul
        ((-1) ^ k * (ascPochhammer ℂ k).eval (1 - a)) using 1
      rw [ascPochhammer_succ_eval]
      push_cast
      ring_nf) hz
  simp only [CharP.cast_eq_zero, sub_zero, pow_zero, ascPochhammer_zero, Polynomial.eval_one,
    one_mul] at h
  rw [h]
  ring

end Complex

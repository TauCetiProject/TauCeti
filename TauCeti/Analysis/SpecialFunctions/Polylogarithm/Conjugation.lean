/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Complex conjugation of integer-weight polylogarithms

The principal polylogarithm `TauCeti.Polylog.polylog n` has real power-series coefficients on the
unit disc, so it commutes with complex conjugation off the open cut `(1, ∞)`. More precisely:

* In nonpositive weights `n = -r`, `polylog (-(r : ℤ))` is generated from `z / (1 - z)` by repeated
  application of the real-coefficient Euler operator `z (d / dz)`. Since Mathlib's total derivative
  commutes with `f ↦ conj ∘ f ∘ conj`, conjugation commutes with `polylog (-(r : ℤ))` at **every**
  `z : ℂ`, including the totalised value at `z = 1`.
* In positive weights, Mathlib's principal logarithm satisfies `Log (conj w) = conj (Log w)`
  whenever `arg w ≠ π`. For `z` with `z.im ≠ 0 ∨ z.re ≤ 1` (the complement of `(1, ∞)`), every
  radial point `1 - t z` with `t ∈ [0, 1]` avoids the open negative real axis, so `polylog n`
  commutes with conjugation on `ℂ ∖ (1, ∞)`. This covers both the principal domain
  `{z | 1 - z ∈ Complex.slitPlane}` and the closed unit disc `‖z‖ ≤ 1`.

On the open ray `(1, ∞)` in positive weight `n ≥ 1`, `polylog n x` is the lower boundary value
whereas `conj (polylog n x)` is the upper boundary value, so conjugation does **not** commute with
the total function there.

## Main declarations

* `TauCeti.Polylog.polylog_neg_nat_conj`: `polylog (-r) (conj z) = conj (polylog (-r) z)` for all
  `z : ℂ`.
* `TauCeti.Polylog.polylog_conj_of_im_ne_zero_or_re_le_one`:
  `polylog n (conj z) = conj (polylog n z)` for all `n : ℤ` and `z ∉ (1, ∞)`.
* `TauCeti.Polylog.polylog_conj` and `TauCeti.Polylog.polylog_conj_of_norm_le_one`: specializations
  to `{z | 1 - z ∈ Complex.slitPlane}` and to the closed unit disc `‖z‖ ≤ 1`.
* `TauCeti.Polylog.im_polylog_ofReal_eq_zero`: `polylog n x` is real for every `n : ℤ` and real
  `x ≤ 1`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §§1.1–1.3, pp. 50–51.
-/

public section

open Set
open scoped ComplexConjugate

namespace TauCeti.Polylog

/-- In nonpositive weights, `polylog (-r)` commutes with complex conjugation everywhere on `ℂ`,
including the totalised value at `1`. -/
theorem polylog_neg_nat_conj (r : ℕ) (z : ℂ) :
    polylog (-(r : ℤ)) (conj z) = conj (polylog (-(r : ℤ)) z) := by
  induction r generalizing z with
  | zero =>
    simp [polylog_zero_weight]
  | succ r ih =>
    have hcomp : conj ∘ polylog (-(r : ℤ)) ∘ conj = polylog (-(r : ℤ)) := by
      ext w
      simp [ih]
    have hderiv : deriv (polylog (-(r : ℤ))) (conj z) =
        conj (deriv (polylog (-(r : ℤ))) z) := by
      have hd := congr_fun (deriv_conj_conj (f := polylog (-(r : ℤ)))) (conj z)
      simpa [hcomp] using hd
    rw [polylog_neg_nat_succ, polylog_neg_nat_succ, hderiv, map_mul]

/-- For `z` off the open ray `(1, ∞)` and `t ∈ [0, 1]`, the radial factor `1 - t z` never lies on
the open negative real axis, so its principal argument is not `π`. -/
private lemma arg_one_sub_ofReal_mul_ne_pi {z : ℂ} (hz : z.im ≠ 0 ∨ z.re ≤ 1) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ((1 : ℂ) - (t : ℂ) * z).arg ≠ Real.pi := by
  rw [ne_eq, Complex.arg_eq_pi_iff]
  rintro ⟨hre, him⟩
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_im, Complex.one_im, Complex.mul_im,
    add_zero, zero_sub, neg_eq_zero, mul_eq_zero] at hre him
  rcases hz with hzim | hzre
  · rcases him with rfl | hzim'
    · linarith
    · exact hzim hzim'
  · nlinarith [ht.1, ht.2]

/-- Every integer-weight polylogarithm commutes with complex conjugation off the open cut `(1, ∞)`,
that is, whenever `z.im ≠ 0 ∨ z.re ≤ 1`. -/
theorem polylog_conj_of_im_ne_zero_or_re_le_one (n : ℤ) {z : ℂ} (hz : z.im ≠ 0 ∨ z.re ≤ 1) :
    polylog n (conj z) = conj (polylog n z) := by
  cases n with
  | negSucc r =>
    simpa [Int.negSucc_eq] using polylog_neg_nat_conj (r + 1) z
  | ofNat m =>
    rcases m with _ | _ | k
    · simp [polylog_zero_weight]
    · rw [Int.ofNat_eq_natCast, zero_add, Nat.cast_one, polylog_one, polylog_one, map_neg]
      have harg : (1 - z).arg ≠ Real.pi := by
        simpa using arg_one_sub_ofReal_mul_ne_pi hz (right_mem_Icc.mpr zero_le_one)
      rw [← Complex.log_conj _ harg, map_sub, map_one]
    · rw [Int.ofNat_eq_natCast, polylog_nat_add_two, polylog_nat_add_two, map_mul, map_inv₀,
        map_natCast, ← intervalIntegral.intervalIntegral_conj]
      congr 1
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [uIcc_of_le zero_le_one] at ht
      have harg := arg_one_sub_ofReal_mul_ne_pi hz ht
      have hconj : (1 : ℂ) - (t : ℂ) * conj z = conj ((1 : ℂ) - (t : ℂ) * z) := by
        simp
      rw [hconj, Complex.log_conj _ harg]
      simp

/-- On the principal domain `{z | 1 - z ∈ Complex.slitPlane}`, every integer-weight polylogarithm
commutes with complex conjugation. -/
theorem polylog_conj (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    polylog n (conj z) = conj (polylog n z) := by
  refine polylog_conj_of_im_ne_zero_or_re_le_one n ?_
  rcases Complex.mem_slitPlane_iff.mp hz with hre | him
  · exact Or.inr (by simp only [Complex.sub_re, Complex.one_re] at hre; linarith)
  · exact Or.inl (by simp only [Complex.sub_im, Complex.one_im, zero_sub, ne_eq,
      neg_eq_zero] at him; exact him)

/-- On the closed unit disc `‖z‖ ≤ 1`, every integer-weight polylogarithm commutes with complex
conjugation. -/
theorem polylog_conj_of_norm_le_one (n : ℤ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    polylog n (conj z) = conj (polylog n z) :=
  polylog_conj_of_im_ne_zero_or_re_le_one n (Or.inr ((Complex.re_le_norm z).trans hz))

/-- Nonpositive-weight polylogarithms take real values at every real argument, including `1`. -/
@[simp]
theorem im_polylog_neg_nat_ofReal (r : ℕ) (x : ℝ) :
    (polylog (-(r : ℤ)) x).im = 0 :=
  Complex.conj_eq_iff_im.mp (by simpa using (polylog_neg_nat_conj r x).symm)

/-- Every integer-weight polylogarithm is real-valued on `(-∞, 1]`. -/
theorem im_polylog_ofReal_eq_zero (n : ℤ) {x : ℝ} (hx : x ≤ 1) :
    (polylog n x).im = 0 :=
  Complex.conj_eq_iff_im.mp
    (by simpa using (polylog_conj_of_im_ne_zero_or_re_le_one n (z := x) (Or.inr (by simpa))).symm)

/-- On `(-∞, 1]`, `polylog n x` equals the coercion of its real part. -/
theorem ofReal_re_polylog_of_le_one (n : ℤ) {x : ℝ} (hx : x ≤ 1) :
    ((polylog n x).re : ℂ) = polylog n x :=
  Complex.conj_eq_iff_re.mp
    (by simpa using (polylog_conj_of_im_ne_zero_or_re_le_one n (z := x) (Or.inr (by simpa))).symm)

/-- At `-1`, the dilogarithm is real. -/
theorem im_polylog_two_neg_one : (polylog 2 (-1)).im = 0 := by
  simpa using im_polylog_ofReal_eq_zero 2 (x := -1) (by norm_num)

/-- On the cut `(1, ∞)`, conjugation does not commute with `polylog 1`: at `3`, `polylog 1 3` has
imaginary part `-π` whereas `conj (polylog 1 3)` has imaginary part `+π`. -/
theorem polylog_one_conj_three_ne : polylog 1 (conj (3 : ℂ)) ≠ conj (polylog 1 3) := by
  intro h
  rw [map_ofNat] at h
  have him : (polylog 1 (3 : ℂ)).im = 0 := Complex.conj_eq_iff_im.mp h.symm
  rw [polylog_one_three] at him
  simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_re, mul_zero, Complex.I_im, mul_one, add_zero] at him
  linarith [Real.pi_pos]

end TauCeti.Polylog

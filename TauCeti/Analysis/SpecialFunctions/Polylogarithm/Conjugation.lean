/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Convex

/-!
# Complex conjugation of principal polylogarithms

The principal integer-weight polylogarithm commutes with complex conjugation on the principal
domain `ℂ ∖ [1, ∞) = {z : ℂ | 1 - z ∈ Complex.slitPlane}` in every integer weight, and on all of
`ℂ` (including the totalised value at `1`) in nonpositive weights. As a consequence, `polylog n`
takes real values on `(-∞, 1)` for every `n : ℤ` and on all of `ℝ` for `n ≤ 0`. On `(1, ∞)` in
positive weight, the totalised principal value selects the lower boundary determination, so
conjugation flips the sign of the non-vanishing imaginary part rather than fixing `polylog n x`.

## Main declarations

* `TauCeti.Polylog.polylog_conj_of_nonpos`: `polylog n (conj z) = conj (polylog n z)` for every
  `n ≤ 0` and every `z : ℂ`.
* `TauCeti.Polylog.polylog_conj`: `polylog n (conj z) = conj (polylog n z)` for every `n : ℤ` and
  `z : ℂ` with `1 - z ∈ Complex.slitPlane`.
* `TauCeti.Polylog.im_polylog_of_nonpos` and `TauCeti.Polylog.ofReal_re_polylog_of_nonpos`:
  reality of `polylog n x` for `n ≤ 0` and `x : ℝ`.
* `TauCeti.Polylog.im_polylog_of_lt_one` and `TauCeti.Polylog.ofReal_re_polylog_of_lt_one`:
  reality of `polylog n x` for `n : ℤ` and `x < 1`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §§1.1–1.3, pp. 50–51.
-/

public section

open Set
open scoped ComplexConjugate

namespace TauCeti.Polylog

/-- Nonpositive-weight polylogarithms commute with complex conjugation everywhere on `ℂ`,
including at the totalised pole `z = 1`. -/
private lemma polylog_neg_nat_conj (r : ℕ) (z : ℂ) :
    polylog (-(r : ℤ)) (conj z) = conj (polylog (-(r : ℤ)) z) := by
  induction r generalizing z with
  | zero => simp [polylog_zero_weight]
  | succ r ih =>
    have hcomp : conj ∘ polylog (-(r : ℤ)) ∘ conj = polylog (-(r : ℤ)) := by
      ext w
      simp [Function.comp_def, ih]
    have hderiv : deriv (polylog (-(r : ℤ))) (conj z) = conj (deriv (polylog (-(r : ℤ))) z) := by
      have h := congr_fun (congr_arg deriv hcomp) z
      rw [deriv_conj_conj] at h
      simpa [Function.comp_def] using congr_arg conj h
    rw [polylog_neg_nat_succ, polylog_neg_nat_succ, hderiv, map_mul]

/-- In nonpositive integer weight, `polylog n` commutes with complex conjugation on all of `ℂ`
(including the totalised value at `z = 1`). -/
theorem polylog_conj_of_nonpos {n : ℤ} (hn : n ≤ 0) (z : ℂ) :
    polylog n (conj z) = conj (polylog n z) := by
  lift -n to ℕ using neg_nonneg.2 hn with r hr
  have hn' : n = -(r : ℤ) := by omega
  rw [hn']
  exact polylog_neg_nat_conj r z

/-- On the principal domain `ℂ ∖ [1, ∞)`, every integer-weight polylogarithm commutes with
complex conjugation. -/
theorem polylog_conj (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    polylog n (conj z) = conj (polylog n z) := by
  rcases le_or_gt n 0 with hn | hn
  · exact polylog_conj_of_nonpos hn z
  · lift n to ℕ using hn.le with m
    rcases m with _ | _ | k
    · exact absurd rfl hn.ne'
    · simp only [zero_add, Nat.cast_one, polylog_one]
      have hsub : 1 - conj z = conj (1 - z) := by simp
      rw [hsub, Complex.log_conj _ (Complex.slitPlane_arg_ne_pi hz), map_neg]
    · rw [polylog_nat_add_two, polylog_nat_add_two, map_mul, map_inv₀, Complex.conj_natCast]
      congr 1
      have hcongr : EqOn
          (fun t : ℝ ↦ ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * conj z)) / t)
          (fun t : ℝ ↦
            conj (((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / t))
          (uIcc 0 1) := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        have hmem : 1 - (t : ℂ) * z ∈ Complex.slitPlane := by
          have hz' : 1 + -z ∈ Complex.slitPlane := by simpa [sub_eq_add_neg] using hz
          have h := Complex.starConvex_one_slitPlane.add_smul_mem hz' ht.1 ht.2
          rwa [Complex.real_smul, mul_neg, ← sub_eq_add_neg] at h
        have hsub : 1 - (t : ℂ) * conj z = conj (1 - (t : ℂ) * z) := by simp
        dsimp only
        rw [hsub, Complex.log_conj _ (Complex.slitPlane_arg_ne_pi hmem)]
        simp
      rw [intervalIntegral.integral_congr hcongr, intervalIntegral.intervalIntegral_conj]

/-- Nonpositive-weight polylogarithms have zero imaginary part at every real argument, including
at `1`. -/
@[simp] theorem im_polylog_of_nonpos {n : ℤ} (hn : n ≤ 0) (x : ℝ) :
    (polylog n x).im = 0 := by
  refine Complex.conj_eq_iff_im.1 ?_
  simpa using (polylog_conj_of_nonpos hn x).symm

/-- Nonpositive-weight polylogarithms are real at every real argument. -/
theorem ofReal_re_polylog_of_nonpos {n : ℤ} (hn : n ≤ 0) (x : ℝ) :
    ((polylog n x).re : ℂ) = polylog n x := by
  simpa [Complex.ext_iff] using (im_polylog_of_nonpos hn x).symm

/-- For every integer weight `n` and real `x < 1`, `polylog n x` has zero imaginary part. -/
theorem im_polylog_of_lt_one (n : ℤ) {x : ℝ} (hx : x < 1) :
    (polylog n x).im = 0 := by
  have hxΩ : 1 - (x : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inl (by simp [sub_pos.2 hx]))
  refine Complex.conj_eq_iff_im.1 ?_
  simpa using (polylog_conj n hxΩ).symm

/-- For every integer weight `n` and real `x < 1`, `polylog n x` equals its real part coerced to
`ℂ`. -/
theorem ofReal_re_polylog_of_lt_one (n : ℤ) {x : ℝ} (hx : x < 1) :
    ((polylog n x).re : ℂ) = polylog n x := by
  simpa [Complex.ext_iff] using (im_polylog_of_lt_one n hx).symm

/-- At `-1`, the dilogarithm is real. -/
theorem im_polylog_two_neg_one : (polylog 2 (-1 : ℂ)).im = 0 := by
  simpa using im_polylog_of_lt_one 2 (x := -1) (by norm_num)

/-- On the branch cut `(1, ∞)`, conjugation symmetry fails in positive weight: at `z = 3` in
weight `1`, `polylog 1 (conj 3)` is the lower boundary value while `conj (polylog 1 3)` is the
upper boundary value. -/
theorem polylog_one_conj_three_ne : polylog 1 (conj (3 : ℂ)) ≠ conj (polylog 1 3) := by
  intro h
  rw [map_ofNat] at h
  have him0 : (polylog 1 (3 : ℂ)).im = 0 := Complex.conj_eq_iff_im.1 h.symm
  rw [polylog_one_three, Complex.sub_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re] at him0
  linarith [Real.pi_pos]

end TauCeti.Polylog

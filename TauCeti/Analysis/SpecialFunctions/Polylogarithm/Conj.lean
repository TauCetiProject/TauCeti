/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic

/-!
# Complex conjugation of principal polylogarithms

The principal polylogarithm `Liₙ` has real Taylor coefficients, and it commutes with complex
conjugation wherever the principal logarithm does. This file proves
`Liₙ (conj z) = conj (Liₙ z)` directly from the defining formulas of
`TauCeti.Polylog.polylog`:

* in nonpositive weight the functions are Euler derivatives of the rational function
  `z / (1 - z)` with real coefficients, and the identity holds for **every** `z`, including the
  totalised value at the pole `1`;
* in positive weight the identity holds whenever `arg (1 - z) ≠ π`, that is on the principal
  domain `ℂ ∖ [1, ∞)` together with the point `1`. In weight one this is Mathlib's
  `Complex.log_conj`; in weight at least two the same holds for every `1 - t z` with
  `t ∈ [0, 1]`, so conjugation passes through the logarithmic radial integral.

The hypothesis `arg (1 - z) ≠ π` cannot be dropped in positive weight: on the cut `(1, ∞)` the
total function takes its lower boundary value, while the conjugate is the upper boundary value.
For instance `Li₁(3) = -log 2 - π i` is not equal to its conjugate.

Consequences are conjugation symmetry on the closed half-plane `re z ≤ 1`, and in particular on
the closed unit disc, and real values of every `Liₙ` on the real half-line `(-∞, 1]`.

## Main declarations

* `TauCeti.Polylog.polylog_neg_nat_conj`: conjugation symmetry of nonpositive weights on `ℂ`.
* `TauCeti.Polylog.polylog_conj`: conjugation symmetry in every weight off the cut `(1, ∞)`.
* `TauCeti.Polylog.polylog_conj_of_re_le_one`: conjugation symmetry on `re z ≤ 1`.
* `TauCeti.Polylog.polylog_ofReal_im`: `Liₙ x` is real for real `x ≤ 1`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §§1.1–1.3, pp. 50–51.
-/

public section

open ComplexConjugate

namespace TauCeti.Polylog

/-- Nonpositive weights commute with complex conjugation at every point, including the
totalised value at the pole `1`. -/
theorem polylog_neg_nat_conj (r : ℕ) (z : ℂ) :
    polylog (-(r : ℤ)) (conj z) = conj (polylog (-(r : ℤ)) z) := by
  suffices h : conj ∘ polylog (-(r : ℤ)) ∘ conj = polylog (-(r : ℤ)) by
    simpa using (congrFun h (conj z)).symm
  induction r with
  | zero =>
    funext w
    simp
  | succ r ih =>
    funext w
    -- Conjugating the Euler operator `w * deriv f w` conjugates `f`.
    have hd : deriv (polylog (-(r : ℤ))) w = conj (deriv (polylog (-(r : ℤ))) (conj w)) := by
      conv_lhs => rw [← ih, deriv_conj_conj]
      simp only [Function.comp_apply]
    simp only [Function.comp_apply, polylog_neg_nat_succ]
    rw [hd]
    simp

/-- Every integer-weight polylogarithm commutes with complex conjugation whenever
`arg (1 - z) ≠ π`, that is on the principal domain `ℂ ∖ [1, ∞)` together with the point `1`.
Nonpositive weights need no hypothesis, by `polylog_neg_nat_conj`. -/
theorem polylog_conj (n : ℤ) {z : ℂ} (hz : (1 - z).arg ≠ Real.pi) :
    polylog n (conj z) = conj (polylog n z) := by
  rcases le_or_gt n 0 with hn | hn
  · obtain ⟨r, rfl⟩ := Int.exists_eq_neg_ofNat hn
    exact polylog_neg_nat_conj r z
  obtain ⟨_ | _ | k, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
  · exact absurd hn (lt_irrefl 0)
  · rw [Nat.cast_one, polylog_one, polylog_one, map_neg, ← Complex.log_conj _ hz, map_sub,
      map_one]
  · rw [polylog_nat_add_two, polylog_nat_add_two, map_mul, map_inv₀, map_natCast,
      ← intervalIntegral.intervalIntegral_conj]
    refine congrArg ((Nat.factorial k : ℂ)⁻¹ * ·)
      (intervalIntegral.integral_congr fun t ht ↦ ?_)
    rw [Set.uIcc_of_le zero_le_one] at ht
    -- For `t ∈ [0, 1]`, the point `1 - t z` also avoids the negative real axis.
    have harg : (1 - t * z).arg ≠ Real.pi := by
      rw [Ne, Complex.arg_eq_pi_iff] at hz ⊢
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_im, Complex.one_im,
        Complex.mul_im, add_zero, zero_sub, neg_eq_zero, mul_eq_zero] at hz ⊢
      rintro ⟨hre, ht0 | him⟩
      · norm_num [ht0] at hre
      · exact hz ⟨by nlinarith [ht.1, ht.2], him⟩
    have hlog := Complex.log_conj _ harg
    simp only [map_sub, map_one, map_mul, Complex.conj_ofReal] at hlog
    simp [hlog]

/-- Every integer-weight polylogarithm commutes with complex conjugation on the closed
half-plane `re z ≤ 1`, in particular on the closed unit disc. -/
theorem polylog_conj_of_re_le_one (n : ℤ) {z : ℂ} (hz : z.re ≤ 1) :
    polylog n (conj z) = conj (polylog n z) := by
  refine polylog_conj n fun h ↦ ?_
  have := (Complex.arg_eq_pi_iff.1 h).1
  simp only [Complex.sub_re, Complex.one_re] at this
  linarith

/-- Every integer-weight polylogarithm is real on the real half-line `(-∞, 1]`. -/
theorem polylog_ofReal_im (n : ℤ) {x : ℝ} (hx : x ≤ 1) : (polylog n x).im = 0 := by
  rw [← Complex.conj_eq_iff_im, ← polylog_conj_of_re_le_one n (by simpa using hx),
    Complex.conj_ofReal]

/-- Conjugation symmetry fails on the cut: at `3`, weight one takes the lower boundary value
`-log 2 - π i`, whose conjugate is the upper boundary value. -/
theorem conj_polylog_one_three_ne : conj (polylog 1 3) ≠ polylog 1 (conj 3) := by
  rw [map_ofNat, polylog_one_three, Ne, Complex.conj_eq_iff_im]
  simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re]
  simp [Real.pi_ne_zero]

end TauCeti.Polylog

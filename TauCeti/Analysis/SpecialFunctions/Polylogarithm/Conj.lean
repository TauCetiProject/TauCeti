/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Complex conjugation of principal polylogarithms

The principal polylogarithm `Liₙ` has real Taylor coefficients, and it commutes with complex
conjugation wherever the principal logarithm does. This file proves
`Liₙ (conj z) = conj (Liₙ z)` directly from the defining formulas of
`TauCeti.Polylog.polylog`:

* in nonpositive weight the functions are Euler derivatives of the rational function
  `z / (1 - z)` with real coefficients, and the identity holds for **every** `z`, including the
  totalised value at the pole `1`;
* in positive weight the identity holds off the open cut `(1, ∞)`, that is whenever
  `z.im ≠ 0 ∨ z.re ≤ 1` (equivalently `arg (1 - z) ≠ π`). In weight one this is Mathlib's
  `Complex.log_conj`; in weight at least two the same holds for every `1 - t z` with
  `t ∈ [0, 1]`, so conjugation passes through the logarithmic radial integral.

The hypothesis `z.im ≠ 0 ∨ z.re ≤ 1` cannot be dropped in positive weight: on the cut `(1, ∞)` the
total function takes its lower boundary value, while the conjugate is the upper boundary value.
For instance `Li₁(3) = -log 2 - π i` is not equal to its conjugate.

Consequences are conjugation symmetry on the closed half-plane `re z ≤ 1`, and in particular on
the closed unit disc, and real values of every `Liₙ` on the real half-line `(-∞, 1]`.

## Main declarations

* `TauCeti.Polylog.polylog_neg_nat_conj`: conjugation symmetry of nonpositive weights on `ℂ`.
* `TauCeti.Polylog.polylog_conj`: conjugation symmetry for `n ≤ 0` on all of `ℂ`, and in positive
  weight off the cut `(1, ∞)` (in particular on `re z ≤ 1` and on the closed unit disc `‖z‖ ≤ 1`).
* `TauCeti.Polylog.polylog_neg_nat_ofReal_im`, `TauCeti.Polylog.ofReal_polylog_neg_nat_ofReal_re`,
  `TauCeti.Polylog.polylog_ofReal_im`, and `TauCeti.Polylog.ofReal_polylog_ofReal_re`: `Liₙ x` is
  real for `n ≤ 0` on all of `ℝ`, and for arbitrary `n : ℤ` on `(-∞, 1]`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §§1.1–1.3, pp. 50–51.
-/

public section

open ComplexConjugate

namespace TauCeti.Polylog

/-- Nonpositive weights commute with complex conjugation at every point, including the
totalised value at the pole `1`. -/
@[simp]
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

/-- Every integer-weight polylogarithm commutes with complex conjugation when `n ≤ 0` or off the
open cut `(1, ∞)` (`z.im ≠ 0 ∨ z.re ≤ 1`). -/
theorem polylog_conj (n : ℤ) {z : ℂ} (hz : n ≤ 0 ∨ z.im ≠ 0 ∨ z.re ≤ 1) :
    polylog n (conj z) = conj (polylog n z) := by
  rcases le_or_gt n 0 with hn | hn
  · obtain ⟨r, rfl⟩ := Int.exists_eq_neg_ofNat hn
    exact polylog_neg_nat_conj r z
  replace hz : z.im ≠ 0 ∨ z.re ≤ 1 := hz.resolve_left hn.not_ge
  have hzarg : (1 - z).arg ≠ Real.pi := by
    simpa using Complex.arg_one_sub_ofReal_mul_ne_pi z hz (Set.right_mem_Icc.mpr zero_le_one)
  obtain ⟨_ | _ | k, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
  · exact absurd hn (lt_irrefl 0)
  · rw [Nat.cast_one, polylog_one, polylog_one, map_neg, ← Complex.log_conj _ hzarg, map_sub,
      map_one]
  · rw [polylog_nat_add_two, polylog_nat_add_two, map_mul, map_inv₀, map_natCast,
      ← intervalIntegral.intervalIntegral_conj]
    refine congrArg ((Nat.factorial k : ℂ)⁻¹ * ·)
      (intervalIntegral.integral_congr fun t ht ↦ ?_)
    rw [Set.uIcc_of_le zero_le_one] at ht
    -- For `t ∈ [0, 1]`, the point `1 - t z` also avoids the negative real axis.
    have hlog := Complex.log_conj _ (Complex.arg_one_sub_ofReal_mul_ne_pi z hz ht)
    simp only [map_sub, map_one, map_mul, Complex.conj_ofReal] at hlog
    simp [hlog]

/-- Nonpositive-weight polylogarithms take real values at every real argument, including `1`. -/
@[simp]
theorem polylog_neg_nat_ofReal_im (r : ℕ) (x : ℝ) :
    (polylog (-(r : ℤ)) x).im = 0 :=
  Complex.conj_eq_iff_im.mp (by simpa using (polylog_neg_nat_conj r x).symm)

/-- On all of `ℝ` (including `1`), `polylog (-r) x` equals the coercion of its real part. -/
@[simp]
theorem ofReal_polylog_neg_nat_ofReal_re (r : ℕ) (x : ℝ) :
    ((polylog (-(r : ℤ)) x).re : ℂ) = polylog (-(r : ℤ)) x :=
  Complex.conj_eq_iff_re.mp (by simpa using (polylog_neg_nat_conj r x).symm)

/-- Every integer-weight polylogarithm is real for `n ≤ 0` on all of `ℝ`, and for all `n : ℤ` on
`(-∞, 1]`. -/
theorem polylog_ofReal_im (n : ℤ) {x : ℝ} (hx : n ≤ 0 ∨ x ≤ 1) : (polylog n x).im = 0 := by
  rw [← Complex.conj_eq_iff_im,
    ← polylog_conj n (hx.imp id fun hx' ↦ Or.inr (by simpa using hx')), Complex.conj_ofReal]

/-- For `n ≤ 0` on all of `ℝ`, and for arbitrary `n : ℤ` on `(-∞, 1]`, `polylog n x` equals the
coercion of its real part. -/
theorem ofReal_polylog_ofReal_re (n : ℤ) {x : ℝ} (hx : n ≤ 0 ∨ x ≤ 1) :
    ((polylog n x).re : ℂ) = polylog n x := by
  rw [← Complex.conj_eq_iff_re, Complex.conj_eq_iff_im]
  exact polylog_ofReal_im n hx

end TauCeti.Polylog

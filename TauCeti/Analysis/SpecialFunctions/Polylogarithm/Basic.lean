/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Principal polylogarithms of integer weight

`TauCeti.Polylog.polylog` is the principal integer-weight polylogarithm. Weight zero is
`z / (1 - z)`, weight one is `-Complex.log (1 - z)`, and higher weights are defined by
logarithmic radial integrals. Negative weights are iterated Euler derivatives of weight zero.
The logarithm in the integral uses Mathlib's principal argument, so values on the real cut
select the lower boundary convention.

This file gives the defining identities, vanishing at zero, the nonpositive-weight Euler
recursion, and analyticity of nonpositive weights away from their pole. The explicit
weight-minus-one formula and the value of weight one at 3 check the Euler operator and
logarithm conventions. No regularity at a pole is asserted for the totalised values.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762,
  Astérisque 216 (1993), §1.1, (1)–(3), pp. 50–51.
* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics,
  and Geometry II (2007), Part I, introduction, p. 5.
-/

public section

namespace TauCeti.Polylog

/-- The principal polylogarithm in integer weight. For weights at least two, the
logarithmic radial integral collapses the iterated radial integrals. Nonpositive
weights are Euler derivatives of the rational function `z / (1 - z)`.
Values at poles are totalised and carry no regularity assertion. -/
noncomputable def polylog : ℤ → ℂ → ℂ
  | .ofNat 0, z => z / (1 - z)
  | .ofNat 1, z => -Complex.log (1 - z)
  | .ofNat (k + 2), z =>
      (Nat.factorial k : ℂ)⁻¹ * ∫ t : ℝ in 0..1,
        ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ)
  | .negSucc r, z =>
      ((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w)^[r + 1])
        (fun w => w / (1 - w)) z

/-- The weight-zero normalization, including its totalised value at 1. -/
@[simp] theorem polylog_zero_weight (z : ℂ) : polylog 0 z = z / (1 - z) := by
  rfl

/-- Weight one uses Mathlib's principal logarithm. -/
@[simp] theorem polylog_one (z : ℂ) : polylog 1 z = -Complex.log (1 - z) := by
  rfl

/-- The defining logarithmic radial integral in positive weight at least two. -/
theorem polylog_nat_add_two (k : ℕ) (z : ℂ) :
    polylog (k + 2 : ℕ) z =
      (Nat.factorial k : ℂ)⁻¹ * ∫ t : ℝ in 0..1,
        ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ) := by
  rfl

/-- Nonpositive weights are iterated Euler derivatives of weight zero. -/
theorem polylog_neg_nat (r : ℕ) :
    polylog (-(r : ℤ)) =
      ((fun (f : ℂ → ℂ) (w : ℂ) => w * deriv f w)^[r])
        (fun w => w / (1 - w)) := by
  cases r with
  | zero => rfl
  | succ r => rfl

/-- The Euler recursion for nonpositive weights. It holds even at the totalised
pole because these weights are defined using the total derivative. -/
theorem polylog_neg_nat_succ (r : ℕ) (z : ℂ) :
    polylog (-((r + 1 : ℕ) : ℤ)) z = z * deriv (polylog (-(r : ℤ))) z := by
  rw [polylog_neg_nat, Function.iterate_succ_apply', ← polylog_neg_nat]

/-- Every integer-weight polylogarithm vanishes at zero. -/
@[simp] theorem polylog_zero (n : ℤ) : polylog n 0 = 0 := by
  cases n with
  | ofNat n =>
    rcases n with _ | _ | k
    · simp
    · simp
    · simp [polylog]
  | negSucc r =>
    simp [polylog, Function.iterate_succ_apply']

/-- Nonpositive weights are analytic away from 1, including across the
principal cut of the positive-weight functions. -/
theorem analyticAt_polylog_neg_nat (r : ℕ) {z : ℂ} (hz : z ≠ 1) :
    AnalyticAt ℂ (polylog (-(r : ℤ))) z := by
  induction r with
  | zero =>
    simp only [Nat.cast_zero, neg_zero]
    have hzero : polylog 0 = (fun w : ℂ => w / (1 - w)) :=
      funext polylog_zero_weight
    rw [hzero]
    have hid : AnalyticAt ℂ (fun w : ℂ => w) z := analyticAt_id
    have hconst : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z := analyticAt_const
    exact hid.div (hconst.sub hid) (sub_ne_zero.mpr hz.symm)
  | succ r ih =>
    have h : polylog (-((r + 1 : ℕ) : ℤ)) =
        fun w => w * deriv (polylog (-(r : ℤ))) w :=
      funext (polylog_neg_nat_succ r)
    rw [h]
    exact analyticAt_id.mul ih.deriv

/-- Nonpositive weights are holomorphic on the complement of their sole pole. -/
theorem analyticOnNhd_polylog_neg_nat (r : ℕ) :
    AnalyticOnNhd ℂ (polylog (-(r : ℤ))) {z | z ≠ 1} := by
  intro z hz
  exact analyticAt_polylog_neg_nat r hz

/-- The derivative of weight zero away from its pole. -/
theorem hasDerivAt_polylog_zero_weight {z : ℂ} (hz : z ≠ 1) :
    HasDerivAt (polylog 0) (1 / (1 - z) ^ 2) z := by
  have h := (hasDerivAt_id z).div
    ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)) (sub_ne_zero.mpr hz.symm)
  convert h using 1
  · ext w
    simp [polylog_zero_weight]
  · dsimp
    ring

/-- The first Euler derivative has numerator `z`, not `1`. -/
theorem polylog_neg_one {z : ℂ} (hz : z ≠ 1) :
    polylog (-1) z = z / (1 - z) ^ 2 := by
  have h : polylog (-1) z = z * deriv (polylog 0) z := polylog_neg_nat_succ 0 z
  rw [h, (hasDerivAt_polylog_zero_weight hz).deriv]
  ring

/-- Weight one agrees with Mathlib's logarithm Taylor series on the open disc. -/
theorem hasSum_polylog_one {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (k + 1) / (k + 1)) (polylog 1 z) := by
  simpa using Complex.hasSum_taylorSeries_neg_log' hz

/-- The weight-zero value at one half checks its numerator normalization. -/
theorem polylog_zero_weight_half : polylog 0 (1 / 2) = 1 := by
  norm_num

/-- The first negative weight at one half agrees with its Euler derivative. -/
theorem polylog_neg_one_half : polylog (-1) (1 / 2) = 2 := by
  rw [polylog_neg_one (by norm_num)]
  norm_num

/-- A signed rational value of the first negative weight. -/
theorem polylog_neg_one_neg_one : polylog (-1) (-1) = -(1 / 4) := by
  rw [polylog_neg_one (by norm_num)]
  norm_num

/-- On the cut, weight one uses the lower boundary value: its imaginary part
at 3 is `-π`, not `π`. -/
theorem polylog_one_three :
    polylog 1 3 = -(Real.log 2 : ℂ) - Real.pi * Complex.I := by
  rw [polylog_one]
  have h : (1 - 3 : ℂ) = (2 : ℝ) * (-1 : ℂ) := by norm_num
  rw [h, Complex.log_ofReal_mul (by norm_num) (by norm_num), Complex.log_neg_one]
  ring

end TauCeti.Polylog

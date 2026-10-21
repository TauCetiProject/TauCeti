/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Gaussian lattice sums

This file defines the Gaussian lattice sum
`Z(c, s) = ∑ n : ℤ, exp (-(n - c) ^ 2 / (2 * s ^ 2))`
and develops its elementary theory for a centre `c : ℝ` and a nonzero width `s : ℝ`.

The sum `Z(c, s)` is the normalizing constant of the discrete Gaussian law on `ℤ` with centre `c`
and width `s`, whose masses are `exp (-(n - c) ^ 2 / (2 * s ^ 2)) / Z(c, s)`. The moments of that
law are polynomially weighted lattice sums, and are obtained by differentiating `Z(c, s)` in the
centre `c`.

## Main declarations

* `Real.gaussianLatticeSum` — the Gaussian lattice sum `Z(c, s)`.
* `Real.hasSum_gaussianLatticeSum` and `Real.gaussianLatticeSum_pos` — convergence and positivity
  for `s ≠ 0`; `Real.gaussianLatticeSum_zero_right` records the totalized value `0` at `s = 0`.
* `Real.summable_pow_mul_exp_neg_sub_sq` — convergence of the lattice sums with polynomial weights.
* `Real.gaussianLatticeSum_add_intCast`, `Real.gaussianLatticeSum_periodic`,
  `Real.gaussianLatticeSum_neg_left` and `Real.gaussianLatticeSum_intCast_sub` — invariance under
  integer translations and reflections of the centre.
* `Real.gaussianLatticeSum_eq_jacobiTheta₂` — the expression
  `Z(c, s) = exp (-c ^ 2 / (2 * s ^ 2)) * Re (θ(-i c / (2π s ^ 2), i / (2π s ^ 2)))`
  through Mathlib's two-variable Jacobi theta function `jacobiTheta₂`.
* `Real.hasDerivAt_tsum_pow_mul_exp_neg_sub_sq` and `Real.hasDerivAt_gaussianLatticeSum` —
  termwise differentiation in the centre of the lattice sums with weight `n ^ k`.
* `Real.contDiff_gaussianLatticeSum`, `Real.continuousAt_gaussianLatticeSum` and
  `Real.measurable_gaussianLatticeSum` — analyticity in the centre, joint continuity on `s ≠ 0`,
  and joint measurability.

## References

* C. L. Canonne, G. Kamath and T. Steinke, *The Discrete Gaussian for Differential Privacy*,
  2020, arXiv:2004.00010.
-/

public section

noncomputable section

open Complex Filter Set
open scoped Topology

namespace Real

/-- The **Gaussian lattice sum** `Z(c, s) = ∑ n : ℤ, exp (-(n - c) ^ 2 / (2 * s ^ 2))` with centre
`c` and width `s`.

The series converges exactly when `s ≠ 0`; at `s = 0` every term is `1`, so the totalized sum is
`0` (see `Real.gaussianLatticeSum_zero_right`). -/
def gaussianLatticeSum (c s : ℝ) : ℝ :=
  ∑' n : ℤ, rexp (-((n : ℝ) - c) ^ 2 / (2 * s ^ 2))

theorem gaussianLatticeSum_def (c s : ℝ) :
    gaussianLatticeSum c s = ∑' n : ℤ, rexp (-((n : ℝ) - c) ^ 2 / (2 * s ^ 2)) :=
  (rfl)

/-- Gaussian lattice sums with absolute polynomial weights converge, by comparison with the
bound used for the terms of `jacobiTheta₂`. -/
private theorem summable_abs_pow_mul_exp_neg_sub_sq_div (k : ℕ) (c : ℝ) {b : ℝ} (hb : 0 < b) :
    Summable fun n : ℤ => |(n : ℝ)| ^ k * rexp (-((n : ℝ) - c) ^ 2 / b) := by
  have hT : 0 < (1 / b) / π := div_pos (one_div_pos.2 hb) pi_pos
  refine (summable_pow_mul_jacobiTheta₂_term_bound ((1 / b) * |c| / π) hT k).of_nonneg_of_le
    (fun n => by positivity) fun n => ?_
  rw [Int.cast_abs]
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by positivity)
  have hnc : (n : ℝ) * c ≤ |(n : ℝ)| * |c| := (le_abs_self _).trans (abs_mul _ _).le
  have hπ : π ≠ 0 := pi_ne_zero
  rw [div_eq_mul_one_div]
  field_simp
  nlinarith [sq_nonneg c, one_div_pos.2 hb]

/-- Gaussian lattice sums with polynomial weights `n ^ k` converge for every nonzero width. -/
theorem summable_pow_mul_exp_neg_sub_sq (k : ℕ) (c : ℝ) {s : ℝ} (hs : s ≠ 0) :
    Summable fun n : ℤ => (n : ℝ) ^ k * rexp (-((n : ℝ) - c) ^ 2 / (2 * s ^ 2)) :=
  (summable_abs_pow_mul_exp_neg_sub_sq_div k c
    (mul_pos two_pos (sq_pos_of_ne_zero hs))).of_norm_bounded fun n => by
    rw [norm_mul, norm_pow, norm_eq_abs, norm_of_nonneg (exp_nonneg _)]

/-- For a nonzero width, the Gaussian lattice series converges to `gaussianLatticeSum c s`. -/
theorem hasSum_gaussianLatticeSum (c : ℝ) {s : ℝ} (hs : s ≠ 0) :
    HasSum (fun n : ℤ => rexp (-((n : ℝ) - c) ^ 2 / (2 * s ^ 2))) (gaussianLatticeSum c s) := by
  simpa [gaussianLatticeSum_def] using (summable_pow_mul_exp_neg_sub_sq 0 c hs).hasSum

/-- At width zero every term of the Gaussian lattice series is `1`, so the totalized sum is `0`. -/
@[simp]
theorem gaussianLatticeSum_zero_right (c : ℝ) : gaussianLatticeSum c 0 = 0 := by
  simp [gaussianLatticeSum_def]

/-- For a nonzero width the Gaussian lattice sum is positive. -/
theorem gaussianLatticeSum_pos (c : ℝ) {s : ℝ} (hs : s ≠ 0) : 0 < gaussianLatticeSum c s :=
  (hasSum_gaussianLatticeSum c hs).summable.tsum_pos (fun _ => (exp_pos _).le) 0 (exp_pos _)

/-- The Gaussian lattice sum depends on the width only through its square. -/
@[simp]
theorem gaussianLatticeSum_neg_right (c s : ℝ) :
    gaussianLatticeSum c (-s) = gaussianLatticeSum c s := by
  simp [gaussianLatticeSum_def]

/-- The Gaussian lattice sum is invariant under integer translations of the centre. -/
@[simp]
theorem gaussianLatticeSum_add_intCast (c : ℝ) (k : ℤ) (s : ℝ) :
    gaussianLatticeSum (c + k) s = gaussianLatticeSum c s := by
  rw [gaussianLatticeSum_def, gaussianLatticeSum_def, ← (Equiv.addRight k).tsum_eq]
  congr! 4
  simp only [Equiv.coe_addRight, Int.cast_add]
  ring

/-- The Gaussian lattice sum is `1`-periodic in the centre. -/
theorem gaussianLatticeSum_periodic (s : ℝ) :
    Function.Periodic (fun c => gaussianLatticeSum c s) 1 := fun c => by
  simpa using gaussianLatticeSum_add_intCast c 1 s

/-- The Gaussian lattice sum is even in the centre. -/
@[simp]
theorem gaussianLatticeSum_neg_left (c s : ℝ) :
    gaussianLatticeSum (-c) s = gaussianLatticeSum c s := by
  rw [gaussianLatticeSum_def, gaussianLatticeSum_def, ← (Equiv.neg ℤ).tsum_eq]
  congr! 4
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring

/-- The Gaussian lattice sum is invariant under the reflection `c ↦ k - c` for every integer
`k`. -/
@[simp]
theorem gaussianLatticeSum_intCast_sub (k : ℤ) (c s : ℝ) :
    gaussianLatticeSum (k - c) s = gaussianLatticeSum c s := by
  rw [sub_eq_neg_add, gaussianLatticeSum_add_intCast, gaussianLatticeSum_neg_left]

/-- The terms of `jacobiTheta₂` at `z = -i c / (2π s ^ 2)` and `τ = i / (2π s ^ 2)` are the
terms of the Gaussian lattice series, rescaled by `exp (c ^ 2 / (2 * s ^ 2))`. -/
private theorem jacobiTheta₂_term_eq (n : ℤ) (c : ℝ) {s : ℝ} (hs : s ≠ 0) :
    jacobiTheta₂_term n (-I * c / (2 * π * s ^ 2)) (I / (2 * π * s ^ 2)) =
      ((rexp (c ^ 2 / (2 * s ^ 2)) * rexp (-((n : ℝ) - c) ^ 2 / (2 * s ^ 2)) : ℝ) : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 pi_ne_zero
  have hs' : (s : ℂ) ≠ 0 := ofReal_ne_zero.2 hs
  rw [← exp_add, ofReal_exp, jacobiTheta₂_term]
  congr 1
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **Theta-function expression of the Gaussian lattice sum**:
`Z(c, s) = exp (-c ^ 2 / (2 * s ^ 2)) * Re (θ(-i c / (2π s ^ 2), i / (2π s ^ 2)))`, where `θ` is
Mathlib's two-variable Jacobi theta function `jacobiTheta₂`.

At `s = 0` both sides vanish. -/
theorem gaussianLatticeSum_eq_jacobiTheta₂ (c s : ℝ) :
    gaussianLatticeSum c s = rexp (-c ^ 2 / (2 * s ^ 2)) *
      (jacobiTheta₂ (-I * c / (2 * π * s ^ 2)) (I / (2 * π * s ^ 2))).re := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [jacobiTheta₂_undef]
  rw [jacobiTheta₂, tsum_congr fun n => jacobiTheta₂_term_eq n c hs, ← ofReal_tsum, ofReal_re,
    tsum_mul_left, ← gaussianLatticeSum_def, ← mul_assoc, ← exp_add, neg_div, neg_add_cancel,
    exp_zero, one_mul]

/-- The derivative in the centre of a single term `n ^ k * exp (-(n - x) ^ 2 / (2 * s ^ 2))`. -/
private theorem hasDerivAt_pow_mul_exp_neg_sub_sq (k : ℕ) (n : ℤ) {s : ℝ} (hs : s ≠ 0) (x : ℝ) :
    HasDerivAt (fun y => (n : ℝ) ^ k * rexp (-((n : ℝ) - y) ^ 2 / (2 * s ^ 2)))
      ((n : ℝ) ^ k * (((n : ℝ) - x) / s ^ 2 * rexp (-((n : ℝ) - x) ^ 2 / (2 * s ^ 2)))) x := by
  refine (((((hasDerivAt_id x).const_sub (n : ℝ)).pow 2).neg.div_const (2 * s ^ 2)).exp.const_mul
    ((n : ℝ) ^ k)).congr_deriv ?_
  simp only [id, Nat.cast_ofNat, Pi.pow_apply, Pi.neg_apply]
  field_simp
  ring

/-- Near `c`, the termwise derivatives of the weighted lattice series are dominated by a
summable sequence independent of the point. -/
private theorem norm_deriv_pow_mul_exp_neg_sub_sq_le (k : ℕ) (n : ℤ) {c s x : ℝ} (hs : s ≠ 0)
    (hx : x ∈ Ioo (c - 1) (c + 1)) :
    ‖(n : ℝ) ^ k * (((n : ℝ) - x) / s ^ 2 * rexp (-((n : ℝ) - x) ^ 2 / (2 * s ^ 2)))‖ ≤
      (|(n : ℝ)| ^ (k + 1) * rexp (-((n : ℝ) - c) ^ 2 / (4 * s ^ 2)) +
        (|c| + 1) * (|(n : ℝ)| ^ k * rexp (-((n : ℝ) - c) ^ 2 / (4 * s ^ 2)))) *
        (rexp (1 / (2 * s ^ 2)) / s ^ 2) := by
  have hs2 : 0 < s ^ 2 := sq_pos_of_ne_zero hs
  have hxc : |x - c| < 1 := abs_sub_lt_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hnx : |(n : ℝ) - x| ≤ |(n : ℝ)| + (|c| + 1) := by
    calc |(n : ℝ) - x| ≤ |(n : ℝ)| + |x| := abs_sub _ _
      _ ≤ |(n : ℝ)| + (|c| + 1) := by
        gcongr
        linarith [abs_sub_abs_le_abs_sub x c]
  have hexp : rexp (-((n : ℝ) - x) ^ 2 / (2 * s ^ 2)) ≤
      rexp (1 / (2 * s ^ 2)) * rexp (-((n : ℝ) - c) ^ 2 / (4 * s ^ 2)) := by
    rw [← exp_add, exp_le_exp, div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have : ((n : ℝ) - c) ^ 2 ≤ 2 * ((n : ℝ) - x) ^ 2 + 2 := by
      nlinarith [abs_lt.1 hxc, sq_nonneg ((n : ℝ) - x + (x - c)), sq_nonneg ((n : ℝ) - x - (x - c))]
    nlinarith [mul_pos hs2 hs2]
  simp only [norm_mul, norm_div, norm_pow, norm_eq_abs, sq_abs, abs_exp]
  calc |(n : ℝ)| ^ k * (|(n : ℝ) - x| / s ^ 2 * rexp (-((n : ℝ) - x) ^ 2 / (2 * s ^ 2)))
      ≤ |(n : ℝ)| ^ k * ((|(n : ℝ)| + (|c| + 1)) / s ^ 2 *
          (rexp (1 / (2 * s ^ 2)) * rexp (-((n : ℝ) - c) ^ 2 / (4 * s ^ 2)))) := by gcongr
    _ = _ := by ring

/-- **Termwise differentiation of weighted Gaussian lattice sums**: for every natural weight
exponent `k` and nonzero width `s`, the derivative in the centre of
`x ↦ ∑ n : ℤ, n ^ k * exp (-(n - x) ^ 2 / (2 * s ^ 2))` is the sum of the termwise derivatives. -/
theorem hasDerivAt_tsum_pow_mul_exp_neg_sub_sq (k : ℕ) (c : ℝ) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun x => ∑' n : ℤ, (n : ℝ) ^ k * rexp (-((n : ℝ) - x) ^ 2 / (2 * s ^ 2)))
      (∑' n : ℤ, (n : ℝ) ^ k * (((n : ℝ) - c) / s ^ 2 *
        rexp (-((n : ℝ) - c) ^ 2 / (2 * s ^ 2)))) c := by
  have h4 : 0 < 4 * s ^ 2 := mul_pos four_pos (sq_pos_of_ne_zero hs)
  have hu := ((summable_abs_pow_mul_exp_neg_sub_sq_div (k + 1) c h4).add
    ((summable_abs_pow_mul_exp_neg_sub_sq_div k c h4).mul_left (|c| + 1))).mul_right
    (rexp (1 / (2 * s ^ 2)) / s ^ 2)
  have hc : c ∈ Ioo (c - 1) (c + 1) := ⟨by linarith, by linarith⟩
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    (fun n x _ => hasDerivAt_pow_mul_exp_neg_sub_sq k n hs x)
    (fun n x hx => norm_deriv_pow_mul_exp_neg_sub_sq_le k n hs hx) hc
    (summable_pow_mul_exp_neg_sub_sq k c hs) hc

/-- The derivative of the Gaussian lattice sum in the centre, computed termwise. -/
theorem hasDerivAt_gaussianLatticeSum (c : ℝ) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun x => gaussianLatticeSum x s)
      (∑' n : ℤ, ((n : ℝ) - c) / s ^ 2 * rexp (-((n : ℝ) - c) ^ 2 / (2 * s ^ 2))) c := by
  simpa [gaussianLatticeSum_def] using hasDerivAt_tsum_pow_mul_exp_neg_sub_sq 0 c hs

private theorem im_I_div_pos {s : ℝ} (hs : s ≠ 0) : 0 < (I / (2 * π * s ^ 2)).im := by
  have : (I / (2 * π * s ^ 2) : ℂ) = ((1 / (2 * π * s ^ 2) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [this, im_ofReal_mul, I_im, mul_one]
  have := sq_pos_of_ne_zero hs
  positivity

/-- The Gaussian lattice sum is analytic, in particular smooth, in the centre. -/
theorem contDiff_gaussianLatticeSum (s : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun c => gaussianLatticeSum c s := by
  rcases eq_or_ne s 0 with rfl | hs
  · simpa using contDiff_const
  simp_rw [gaussianLatticeSum_eq_jacobiTheta₂]
  have hθ : ContDiff ℝ n fun z => jacobiTheta₂ z (I / (2 * π * s ^ 2)) :=
    (Differentiable.contDiff fun z => differentiableAt_jacobiTheta₂_fst z
      (im_I_div_pos hs)).restrict_scalars ℝ
  have hz : ContDiff ℝ n fun c : ℝ => -I * c / (2 * π * s ^ 2) :=
    (contDiff_const.mul ofRealCLM.contDiff).div_const _
  exact (contDiff_exp.comp ((contDiff_id.pow 2).neg.div_const _)).mul
    (reCLM.contDiff.comp (hθ.comp hz))

/-- The Gaussian lattice sum is jointly continuous in the centre and the width at every nonzero
width. -/
theorem continuousAt_gaussianLatticeSum (c : ℝ) {s : ℝ} (hs : s ≠ 0) :
    ContinuousAt (fun p : ℝ × ℝ => gaussianLatticeSum p.1 p.2) (c, s) := by
  simp_rw [gaussianLatticeSum_eq_jacobiTheta₂]
  have hden : ((2 * π * s ^ 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (by positivity)
  have hd : ContinuousAt (fun p : ℝ × ℝ => ((2 * π * p.2 ^ 2 : ℝ) : ℂ)) (c, s) := by fun_prop
  have hφ : ContinuousAt (fun p : ℝ × ℝ =>
      ((-I * p.1 / (2 * π * p.2 ^ 2), I / (2 * π * p.2 ^ 2)) : ℂ × ℂ)) (c, s) := by
    push_cast at hd hden
    exact ((continuousAt_const.mul (continuous_ofReal.continuousAt.comp continuousAt_fst)).div
      hd hden).prodMk (continuousAt_const.div hd hden)
  refine ContinuousAt.mul ?_ (continuous_re.continuousAt.comp ?_)
  · exact continuous_exp.continuousAt.comp
      ((continuousAt_fst.pow 2).neg.div (continuousAt_const.mul (continuousAt_snd.pow 2))
        (by positivity))
  · have hθ : ContinuousAt (fun q : ℂ × ℂ => jacobiTheta₂ q.1 q.2)
        (-I * c / (2 * π * s ^ 2), I / (2 * π * s ^ 2)) :=
      continuousAt_jacobiTheta₂ _ (im_I_div_pos hs)
    exact hθ.comp_of_eq hφ rfl

/-- The Gaussian lattice sum is jointly measurable in the centre and the width. -/
theorem measurable_gaussianLatticeSum :
    Measurable fun p : ℝ × ℝ => gaussianLatticeSum p.1 p.2 := by
  classical
  have hS : IsOpen {p : ℝ × ℝ | p.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
  have heq : (fun p : ℝ × ℝ => gaussianLatticeSum p.1 p.2) =
      {p : ℝ × ℝ | p.2 ≠ 0}.piecewise (fun p => gaussianLatticeSum p.1 p.2) 0 := by
    ext p
    by_cases hp : p.2 = 0 <;> simp [Set.piecewise, hp]
  rw [heq]
  exact ContinuousOn.measurable_piecewise
    (fun p hp => (continuousAt_gaussianLatticeSum p.1 hp).continuousWithinAt)
    continuousOn_const hS.measurableSet

end Real

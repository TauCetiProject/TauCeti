/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Weierstrass primary factors of arbitrary genus

For each natural number `p`, the Weierstrass primary (elementary) factor of genus `p` is
`Complex.elementaryFactor p z = (1 - z) * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1))`.
At `p = 0` this is `1 - z`, and at `p = 1` it coincides with `Complex.weierstrassFactorOne`.

Cancelling the first `p` terms of the logarithmic Taylor series of `1 - z` gives the derivative
identity `deriv (elementaryFactor p) z = -z ^ p * exp (∑ k < p, z ^ (k + 1) / (k + 1))`.
Comparing the radial derivative along `[0, 1]` with the real case `z = 1` via the mean value
inequality yields Rudin's sharp closed-disc estimate `‖1 - elementaryFactor p z‖ ≤ ‖z‖ ^ (p + 1)`
for all `‖z‖ ≤ 1`, which supplies the summable compact-set majorants for canonical products of
arbitrary (fixed or variable) genus. Away from `z = 1`,
`elementaryFactor p z = exp (log (1 - z) + ∑ k < p, z ^ (k + 1) / (k + 1))`; the corresponding
Taylor remainder bounds on `log (1 - z)` live in
`TauCeti.Analysis.SpecialFunctions.Complex.LogBounds`.

## Main definitions

* `Complex.elementaryFactor p z`: the genus-`p` Weierstrass primary factor
  `(1 - z) * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1))`.

## Main results

* `Complex.elementaryFactor_zero_left`, `Complex.elementaryFactor_one_left`,
  `Complex.elementaryFactor_one_eq_weierstrassFactorOne`: specializations at genus `0` (`1 - z`)
  and genus `1` (`Complex.weierstrassFactorOne`).
* `Complex.elementaryFactor_mul_neg`, `Complex.elementaryFactor_one_mul_neg`: symmetric pairing
  `E_p(z) * E_p(-z) = E_{p / 2}(z ^ 2)`, in particular `E₁(z) * E₁(-z) = 1 - z ^ 2`.
* `Complex.hasDerivAt_elementaryFactor`, `Complex.logDeriv_elementaryFactor`: exact derivative and
  rational logarithmic derivative `-z ^ p / (1 - z)`.
* `Complex.analyticOrderAt_elementaryFactor`, `Complex.analyticOrderAt_elementaryFactor_mul`,
  `Complex.analyticOrderAt_elementaryFactor_div`: `E_p` has a unique simple zero at `1`, and
  `w ↦ E_p(w / a)` (`a ≠ 0`) has a unique simple zero at `a`.
* `Complex.norm_one_sub_elementaryFactor_le`, `Complex.norm_elementaryFactor_sub_one_le`:
  `‖1 - elementaryFactor p z‖ ≤ ‖z‖ ^ (p + 1)` on the closed unit disc `‖z‖ ≤ 1`.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill, 1987, Definition 15.7 and
  Lemma 15.8.
* Z. Yun, W. Zhang, *Shtukas and the Taylor expansion of L-functions*, *Ann. of Math.* (2) **186**
  (2017), no. 3, 767–911, Appendix B.1.
-/

public section

open Filter Set Topology
open scoped BigOperators

namespace Complex

/-- The Weierstrass primary (elementary) factor of genus `p`:
`E_p(z) = (1 - z) * exp (∑_{k=0}^{p-1} z ^ (k + 1) / (k + 1))`. -/
noncomputable def elementaryFactor (p : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1))

/-- Defining formula for `Complex.elementaryFactor`. -/
theorem elementaryFactor_def (p : ℕ) (z : ℂ) :
    elementaryFactor p z = (1 - z) * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) :=
  (rfl)

/-- At genus zero, the primary factor is `1 - z`. -/
@[simp]
theorem elementaryFactor_zero_left (z : ℂ) : elementaryFactor 0 z = 1 - z := by
  simp [elementaryFactor]

/-- At genus one, the primary factor agrees with `Complex.weierstrassFactorOne`. -/
theorem elementaryFactor_one_left (z : ℂ) : elementaryFactor 1 z = weierstrassFactorOne z := by
  simp [elementaryFactor, weierstrassFactorOne_def]

/-- Function-level equality between `elementaryFactor 1` and `weierstrassFactorOne`. -/
theorem elementaryFactor_one_eq_weierstrassFactorOne : elementaryFactor 1 = weierstrassFactorOne :=
  funext elementaryFactor_one_left

/-- Stepping from genus `p` to genus `p + 1` multiplies by `exp (z ^ (p + 1) / (p + 1))`. -/
theorem elementaryFactor_succ (p : ℕ) (z : ℂ) :
    elementaryFactor (p + 1) z = elementaryFactor p z * exp (z ^ (p + 1) / (p + 1)) := by
  rw [elementaryFactor_def, Finset.sum_range_succ, exp_add, ← mul_assoc, ← elementaryFactor_def]

/-- Every primary factor is normalized to `1` at the origin. -/
@[simp]
theorem elementaryFactor_zero (p : ℕ) : elementaryFactor p 0 = 1 := by
  simp [elementaryFactor]

/-- Every primary factor vanishes at `1`. -/
@[simp]
theorem elementaryFactor_one (p : ℕ) : elementaryFactor p 1 = 0 := by
  simp [elementaryFactor]

/-- The only zero of `elementaryFactor p` is `1`. -/
@[simp]
theorem elementaryFactor_eq_zero_iff {p : ℕ} {z : ℂ} :
    elementaryFactor p z = 0 ↔ z = 1 := by
  rw [elementaryFactor_def, mul_eq_zero, or_iff_left (exp_ne_zero _), sub_eq_zero, eq_comm]

/-- Away from `1`, `elementaryFactor p z` is the exponential of the `p`-th Taylor remainder of
`log (1 - z)`. -/
theorem elementaryFactor_eq_exp_log_add {p : ℕ} {z : ℂ} (hz : z ≠ 1) :
    elementaryFactor p z =
      exp (log (1 - z) + ∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) := by
  rw [exp_add, exp_log (sub_ne_zero.mpr (Ne.symm hz)), elementaryFactor_def]

/-- Symmetric pairing for primary factors: `E_p(z) * E_p(-z) = E_{p / 2}(z ^ 2)`. -/
theorem elementaryFactor_mul_neg (p : ℕ) (z : ℂ) :
    elementaryFactor p z * elementaryFactor p (-z) = elementaryFactor (p / 2) (z ^ 2) := by
  induction p with
  | zero =>
    simp only [Nat.zero_div, elementaryFactor_zero_left]
    ring
  | succ p ih =>
    rw [elementaryFactor_succ, elementaryFactor_succ, mul_mul_mul_comm, ih, ← exp_add]
    rcases Nat.even_or_odd (p + 1) with ⟨k, hk⟩ | ⟨k, hk⟩
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hp2 : p / 2 = m := by omega
      have hsucc2 : (p + 1) / 2 = m + 1 := by omega
      have heven : (-z) ^ (p + 1) = z ^ (p + 1) := Even.neg_pow ⟨m + 1, hk⟩ z
      have hterm : z ^ (p + 1) / ((p : ℂ) + 1) + (-z) ^ (p + 1) / ((p : ℂ) + 1) =
          (z ^ 2) ^ (m + 1) / ((m : ℂ) + 1) := by
        rw [heven, ← pow_mul, show 2 * (m + 1) = p + 1 by omega]
        have hm0 : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
        have hp1 : ((p : ℂ) + 1) = 2 * ((m : ℂ) + 1) := by
          have : p + 1 = 2 * (m + 1) := by omega
          exact_mod_cast this
        rw [hp1]
        field_simp
        ring
      rw [hterm, hp2, hsucc2, ← elementaryFactor_succ]
    · have hp2 : (p + 1) / 2 = p / 2 := by omega
      have hodd : (-z) ^ (p + 1) = -(z ^ (p + 1)) := (Odd.neg_pow ⟨k, hk⟩ z)
      rw [hp2, hodd, neg_div, add_neg_cancel, exp_zero, mul_one]

/-- Symmetric genus-one pairing: `E₁(z) * E₁(-z) = 1 - z ^ 2`. -/
theorem elementaryFactor_one_mul_neg (z : ℂ) :
    elementaryFactor 1 z * elementaryFactor 1 (-z) = 1 - z ^ 2 := by
  simpa using elementaryFactor_mul_neg 1 z

private theorem hasDerivAt_sum_pow_div_succ (p : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ ↦ ∑ k ∈ Finset.range p, w ^ (k + 1) / (k + 1))
      (∑ k ∈ Finset.range p, z ^ k) z := by
  have h := HasDerivAt.fun_sum (u := Finset.range p)
    (A := fun k (w : ℂ) ↦ w ^ (k + 1) / ((k : ℂ) + 1))
    (A' := fun k ↦ (((k + 1 : ℕ) : ℂ) * z ^ k) / ((k : ℂ) + 1))
    fun k _ ↦ by
      simpa [Nat.add_sub_cancel] using (hasDerivAt_pow (k + 1) z).div_const ((k : ℂ) + 1)
  refine h.congr_deriv (Finset.sum_congr rfl fun k _ ↦ ?_)
  have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
  rw [Nat.cast_add, Nat.cast_one, mul_div_cancel_left₀ _ hk]

/-- Derivative of `elementaryFactor p`: the polynomial in the exponent cancels the lower terms,
leaving `-z ^ p * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1))`. -/
theorem hasDerivAt_elementaryFactor (p : ℕ) (z : ℂ) :
    HasDerivAt (elementaryFactor p)
      (-z ^ p * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1))) z := by
  have hmul : HasDerivAt (elementaryFactor p)
      ((0 - 1) * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) +
        (1 - z) * (exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) *
          ∑ k ∈ Finset.range p, z ^ k)) z :=
    ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).mul
      (hasDerivAt_sum_pow_div_succ p z).cexp
  refine hmul.congr_deriv ?_
  calc
    (0 - 1) * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) +
        (1 - z) * (exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) *
          ∑ k ∈ Finset.range p, z ^ k)
      = (-1 + (1 - z) * ∑ k ∈ Finset.range p, z ^ k) *
          exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) := by ring
    _ = -z ^ p * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) := by
      rw [mul_neg_geom_sum]; ring

/-- Every Weierstrass primary factor is entire. -/
@[fun_prop]
theorem differentiable_elementaryFactor (p : ℕ) : Differentiable ℂ (elementaryFactor p) :=
  fun z ↦ (hasDerivAt_elementaryFactor p z).differentiableAt

/-- Every Weierstrass primary factor is analytic at every complex point. -/
@[fun_prop]
theorem analyticAt_elementaryFactor (p : ℕ) (z : ℂ) : AnalyticAt ℂ (elementaryFactor p) z := by
  rw [show elementaryFactor p = fun w : ℂ ↦
    (1 - w) * exp (∑ k ∈ Finset.range p, w ^ (k + 1) / (k + 1))
    from funext (elementaryFactor_def p)]
  fun_prop

/-- Explicit derivative formula for `elementaryFactor p`. -/
@[simp]
theorem deriv_elementaryFactor (p : ℕ) (z : ℂ) :
    deriv (elementaryFactor p) z =
      -z ^ p * exp (∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1)) :=
  (hasDerivAt_elementaryFactor p z).deriv

/-- The unique zero of `elementaryFactor p` at `1` is simple. -/
theorem analyticOrderAt_elementaryFactor_one (p : ℕ) :
    analyticOrderAt (elementaryFactor p) 1 = 1 := by
  apply (analyticAt_elementaryFactor p 1).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (elementaryFactor_one p)
  rw [deriv_elementaryFactor]
  simp [exp_ne_zero]

/-- Analytic order of `elementaryFactor p` at an arbitrary point `z : ℂ`. -/
theorem analyticOrderAt_elementaryFactor (p : ℕ) (z : ℂ) :
    analyticOrderAt (elementaryFactor p) z = if z = 1 then 1 else 0 := by
  split_ifs with hz
  · exact hz ▸ analyticOrderAt_elementaryFactor_one p
  · exact (analyticAt_elementaryFactor p z).analyticOrderAt_eq_zero.mpr
      (mt elementaryFactor_eq_zero_iff.mp hz)

/-- Analytic order of `w ↦ elementaryFactor p (c * w)` at an arbitrary point `z : ℂ`. -/
theorem analyticOrderAt_elementaryFactor_mul (p : ℕ) (c z : ℂ) :
    analyticOrderAt (fun w ↦ elementaryFactor p (c * w)) z = if c * z = 1 then 1 else 0 := by
  split_ifs with h
  · have hc : c ≠ 0 := fun hc ↦ by simp [hc] at h
    have hd : HasDerivAt (fun w ↦ c * w) c z := by simpa using (hasDerivAt_id z).const_mul c
    have hg : AnalyticAt ℂ (fun w ↦ c * w) z := by fun_prop
    have heq : (fun w ↦ elementaryFactor p (c * w)) = elementaryFactor p ∘ fun w ↦ c * w := rfl
    rw [heq, analyticOrderAt_comp_of_deriv_ne_zero hg (by rwa [hd.deriv]), h]
    exact analyticOrderAt_elementaryFactor_one p
  · have hana : AnalyticAt ℂ (fun w ↦ elementaryFactor p (c * w)) z := by fun_prop
    exact hana.analyticOrderAt_eq_zero.mpr (mt elementaryFactor_eq_zero_iff.mp h)

/-- For a nonzero root location `a`, `w ↦ elementaryFactor p (w / a)` has analytic order `1` at `a`
and `0` everywhere else. -/
theorem analyticOrderAt_elementaryFactor_div (p : ℕ) {a : ℂ} (ha : a ≠ 0) (z : ℂ) :
    analyticOrderAt (fun w ↦ elementaryFactor p (w / a)) z = if z = a then 1 else 0 := by
  simpa only [div_eq_inv_mul, inv_mul_eq_one₀ ha, eq_comm] using
    analyticOrderAt_elementaryFactor_mul p a⁻¹ z

/-- Rational logarithmic derivative of `elementaryFactor p`: `-z ^ p / (1 - z)` everywhere
(including `z = 1` under total division). -/
theorem logDeriv_elementaryFactor (p : ℕ) (z : ℂ) :
    logDeriv (elementaryFactor p) z = -z ^ p / (1 - z) := by
  rw [logDeriv_apply, deriv_elementaryFactor, elementaryFactor_def]
  exact mul_div_mul_right _ _ (exp_ne_zero _)

private theorem re_sum_pow_div_succ_le (p : ℕ) (w : ℂ) :
    (∑ k ∈ Finset.range p, w ^ (k + 1) / (k + 1)).re ≤
      ∑ k ∈ Finset.range p, ‖w‖ ^ (k + 1) / (k + 1) := by
  rw [re_sum]
  refine Finset.sum_le_sum fun k _ ↦ (re_le_norm _).trans_eq ?_
  rw [norm_div, norm_pow, ← Nat.cast_add_one, norm_natCast, Nat.cast_add_one]

/-- **Rudin's Lemma 15.8.** For every genus `p : ℕ` and every `z : ℂ` in the closed unit disc
`‖z‖ ≤ 1`, `‖1 - elementaryFactor p z‖ ≤ ‖z‖ ^ (p + 1)`. -/
theorem norm_one_sub_elementaryFactor_le (p : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖1 - elementaryFactor p z‖ ≤ ‖z‖ ^ (p + 1) := by
  -- Compare `t ↦ 1 - E_p(t z)` on `[0, 1]` with the real boundary `t ↦ ‖z‖^(p+1) (1 - E_p(t)).re`.
  let g : ℝ → ℂ := fun t ↦ 1 - elementaryFactor p (t • z)
  let g' : ℝ → ℂ := fun t ↦
    z * ((t • z) ^ p * exp (∑ k ∈ Finset.range p, (t • z) ^ (k + 1) / (k + 1)))
  let B : ℝ → ℝ := fun t ↦ ‖z‖ ^ (p + 1) * (1 - elementaryFactor p (t : ℂ)).re
  let B' : ℝ → ℝ := fun t ↦
    ‖z‖ ^ (p + 1) * (t ^ p * Real.exp (∑ k ∈ Finset.range p, t ^ (k + 1) / (k + 1)))
  have hg' (t : ℝ) : HasDerivAt g (g' t) t := by
    have hF : HasDerivAt (fun w : ℂ ↦ 1 - elementaryFactor p w)
        ((t • z) ^ p * exp (∑ k ∈ Finset.range p, (t • z) ^ (k + 1) / (k + 1))) (t • z) :=
      ((hasDerivAt_const (t • z) (1 : ℂ)).fun_sub
        (hasDerivAt_elementaryFactor p (t • z))).congr_deriv (by ring)
    have hsmul : HasDerivAt (fun s : ℝ ↦ s • z) z t := by
      simpa using (hasDerivAt_id t).smul_const z
    exact (hF.scomp t hsmul).congr_deriv (smul_eq_mul _ _)
  have hB' (t : ℝ) : HasDerivAt B (B' t) t := by
    have h := ((hasDerivAt_const (t : ℂ) (1 : ℂ)).fun_sub
      (hasDerivAt_elementaryFactor p t)).real_of_complex.const_mul (‖z‖ ^ (p + 1))
    refine h.congr_deriv ?_
    have hsum : (∑ k ∈ Finset.range p, (t : ℂ) ^ (k + 1) / (k + 1)) =
        ((∑ k ∈ Finset.range p, t ^ (k + 1) / (k + 1) : ℝ) : ℂ) := by
      push_cast; rfl
    dsimp only [B']
    rw [zero_sub, neg_mul_eq_neg_mul, neg_neg, hsum, ← ofReal_exp, ← ofReal_pow, ← ofReal_mul,
      ofReal_re]
  have hle := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := (0 : ℝ)) (b := 1)
    (continuous_iff_continuousAt.mpr fun t ↦ (hg' t).continuousAt).continuousOn
    (fun t _ ↦ (hg' t).hasDerivWithinAt) (by simp [g, B]) hB' (fun t ht ↦ ?_)
    (right_mem_Icc.mpr zero_le_one)
  · simpa [g, B] using hle
  · have htz : ‖t • z‖ ≤ t := by
      rw [norm_smul, Real.norm_of_nonneg ht.1]
      exact mul_le_of_le_one_right ht.1 hz
    calc
      ‖g' t‖ = ‖z‖ ^ (p + 1) * (t ^ p * Real.exp
          (∑ k ∈ Finset.range p, (t • z) ^ (k + 1) / (k + 1)).re) := by
        dsimp only [g']
        rw [norm_mul, norm_mul, norm_pow, norm_exp, norm_smul, Real.norm_of_nonneg ht.1, mul_pow,
          pow_succ]
        ring
      _ ≤ B' t := by
        dsimp only [B']
        have ht0 : 0 ≤ t := ht.1
        gcongr
        exact (re_sum_pow_div_succ_le p (t • z)).trans (Finset.sum_le_sum fun k _ ↦ by gcongr)

/-- Symmetric form of `norm_one_sub_elementaryFactor_le`: for `‖z‖ ≤ 1`,
`‖elementaryFactor p z - 1‖ ≤ ‖z‖ ^ (p + 1)`. -/
theorem norm_elementaryFactor_sub_one_le (p : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖elementaryFactor p z - 1‖ ≤ ‖z‖ ^ (p + 1) := by
  rw [norm_sub_rev]
  exact norm_one_sub_elementaryFactor_le p hz

/-! ### Examples -/

/-- Explicit evaluations of `E_p(-1)` for `p = 0, 1, 2`. -/
example :
    elementaryFactor 0 (-1) = 2 ∧
      elementaryFactor 1 (-1) = 2 * exp (-1) ∧
      elementaryFactor 2 (-1) = 2 * exp (-1 / 2) := by
  refine ⟨by norm_num [elementaryFactor], ?_, ?_⟩
  · simp only [elementaryFactor, Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one]
    norm_num
  · simp only [elementaryFactor, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      zero_add]
    norm_num

end Complex

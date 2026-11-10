/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic

/-!
# Differentiation of the regularized Kummer function

The regularized confluent hypergeometric function is
`Complex.regularizedHGFun {a} {b} z`. Its derivative shifts both parameters by one
and multiplies by `a`. Unlike the unregularized formula, this identity holds for
all lower parameters, including the poles of Gamma. It supplies the derivatives
needed for Kummer's and Weber's differential equations. We prove the coefficient
shift and derivative for arbitrary parameter multisets with at most as many upper
as lower parameters, then specialize to the Kummer function.

## References

* NIST Digital Library of Mathematical Functions, §13.3, equation 13.3.15,
  divided by `Γ(b)`, <https://dlmf.nist.gov/13.3#E15>.
-/

public section

noncomputable section

open scoped Nat

namespace Complex

/-- Shifting all parameters by one gives the coefficients of the derivative series,
without any exclusion on the lower parameters. -/
theorem mul_regularizedHGFunCoeff_add_one (a b : Multiset ℂ) (n : ℕ) :
    (n + 1 : ℂ) * regularizedHGFunCoeff a b (n + 1) =
      a.prod * regularizedHGFunCoeff (a.map (· + 1)) (b.map (· + 1)) n := by
  simp only [regularizedHGFunCoeff, Multiset.map_map, Function.comp_def,
    ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_one,
    Multiset.prod_map_mul, Multiset.map_id', Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hb : (fun x : ℂ => Gamma (x + (n + 1 : ℂ))) =
      (fun x : ℂ => Gamma (x + 1 + n)) := by
    funext x
    congr 1
    ring
  rw [hb]
  field_simp

/-- When there are at most as many upper as lower parameters, differentiation shifts all
parameters by one and multiplies by the product of the upper parameters. -/
theorem hasDerivAt_regularizedHGFun {a b : Multiset ℂ} (h : a.card ≤ b.card) (z : ℂ) :
    HasDerivAt (regularizedHGFun a b)
      (a.prod * regularizedHGFun (a.map (· + 1)) (b.map (· + 1)) z) z := by
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by positivity
  let c := regularizedHGFunCoeff a b
  let d := regularizedHGFunCoeff (a.map (· + 1)) (b.map (· + 1))
  have hshift : (a.map (· + 1)).card ≤ (b.map (· + 1)).card := by simpa using h
  have hcoeff (n : ℕ) : (n : ℂ) * c n =
      if n = 0 then 0 else a.prod * d (n - 1) := by
    cases n with
    | zero => simp
    | succ n => simpa [c, d] using mul_regularizedHGFunCoeff_add_one a b n
  have hu : Summable (fun n : ℕ => ‖(n : ℂ) * c n‖ * R ^ (n - 1)) := by
    apply (summable_nat_add_iff 1).1
    simp only [hcoeff, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel]
    have hs := (hasSum_regularizedHGFun hshift (R : ℂ)).summable.mul_left a.prod
    simpa [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hR.le, d, mul_assoc] using hs.norm
  have hd := hasDerivAt_tsum_of_isPreconnected (y₀ := 0) (y := z) hu
    Metric.isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected
    (g := fun n w => c n * w ^ n)
    (g' := fun n w => (n : ℂ) * c n * w ^ (n - 1))
    (fun n w _ => by convert (hasDerivAt_pow n w).const_mul (c n) using 1; ring)
    (fun n w hw => ?_)
    (by simpa only [Metric.mem_ball, dist_self] using hR)
    (hasSum_regularizedHGFun h 0).summable
    (by simp [R])
  · have heq : (fun w => ∑' n, c n * w ^ n) = regularizedHGFun a b := by
      funext w
      exact (hasSum_regularizedHGFun h w).tsum_eq
    rw [heq] at hd
    convert hd using 1
    symm
    apply HasSum.tsum_eq
    rw [← hasSum_nat_add_iff' 1]
    simpa only [Nat.add_sub_cancel, hcoeff, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, ↓reduceIte, zero_mul, Finset.sum_range_one, sub_zero, d, mul_assoc] using
      (hasSum_regularizedHGFun hshift z).mul_left a.prod
  · rw [norm_mul, norm_pow]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using (Metric.mem_ball.1 hw).le) _

/-- The derivative of the entire regularized hypergeometric function, as a function. -/
@[simp]
theorem deriv_regularizedHGFun {a b : Multiset ℂ} (h : a.card ≤ b.card) :
    deriv (regularizedHGFun a b) =
      fun z => a.prod * regularizedHGFun (a.map (· + 1)) (b.map (· + 1)) z :=
  funext fun z => (hasDerivAt_regularizedHGFun h z).deriv

/-- The derivative of the regularized Kummer function, valid at every parameter
(DLMF 13.3.15 after division by `Γ(b)`). -/
theorem hasDerivAt_regularizedHGFun_singleton (a b z : ℂ) :
    HasDerivAt (regularizedHGFun {a} {b})
      (a * regularizedHGFun {a + 1} {b + 1} z) z := by
  simpa using hasDerivAt_regularizedHGFun (a := {a}) (b := {b}) (by simp) z

/-- The derivative of the regularized Kummer function, as a function. -/
theorem deriv_regularizedHGFun_singleton (a b : ℂ) :
    deriv (regularizedHGFun {a} {b}) =
      fun z => a * regularizedHGFun {a + 1} {b + 1} z :=
  funext fun z => (hasDerivAt_regularizedHGFun_singleton a b z).deriv

end Complex

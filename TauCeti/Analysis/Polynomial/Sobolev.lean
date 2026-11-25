/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Sobolev
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Polynomial.AtInfinity
import TauCeti.Analysis.Sobolev.BesselPotential.Basic

/-!
# Sobolev regularity of rational functions of `1 + ‖P‖²`

Let `P` be a complex polynomial of degree `m` and let `φ = (1 + ‖P‖²)⁻¹`. For polynomials `A`, `B`
and `n : ℕ`, the function

`z ↦ φ(z) ^ n conj (A z) B z`

(`Polynomial.conjMulDivOneAddNormSqPow P n A B`, that is `conj A B / (1 + ‖P‖²) ^ n`, smooth by
`Polynomial.contDiff_conjMulDivOneAddNormSqPow`) decays at infinity like
`‖z‖ ^ (deg A + deg B - 2 m n)`. Its directional derivatives are again of this form, with the decay
improved by one power (`Polynomial.hasDerivAt_conjMulDivOneAddNormSqPow`): differentiating `φ ^ n`
gives `-n φ ^ (n + 1) (conj P P' v + P conj P' conj v)`, and differentiating `A` or `B` lowers its
degree. So if `deg A + deg B + 2 ≤ 2 m n`, so that the function is square integrable on the plane
(`Polynomial.memLp_conjMulDivOneAddNormSqPow`), every derivative is square integrable as well, and
the real part of the function lies in the Bessel-potential space `H^k(ℂ)` for every `k`
(`Polynomial.re_mem_realSobolevFunctions_of_add_two_le`).

In particular, for a nonconstant `P`, the defect `(1 + ‖P‖²)⁻¹` of the squared modulus
`‖P‖² / (1 + ‖P‖²)` from `1` (`Polynomial.inv_one_add_norm_eval_sq_mem_realSobolevFunctions`) and,
for every `P`, the density `‖P'‖² / (1 + ‖P‖²)²` of the pullback by `P` of the Fubini–Study area
form (`Polynomial.norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq_mem_realSobolevFunctions`)
lie in every `H^s(ℂ)`. These are the coefficients of Taubes's reduced vortex equation for the zero
divisor of `P`.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace Polynomial

open ComplexConjugate Filter MeasureTheory TemperedDistribution Topology
open scoped ContDiff

variable {P : ℂ[X]}

/-- The function `z ↦ conj (A z) B z / (1 + ‖P z‖²) ^ n`, written `φ(z) ^ n conj (A z) B z` with
`φ = (1 + ‖P‖²)⁻¹`. -/
def conjMulDivOneAddNormSqPow (P : ℂ[X]) (n : ℕ) (A B : ℂ[X]) (z : ℂ) : ℂ :=
  (((1 + ‖P.eval z‖ ^ 2)⁻¹ ^ n : ℝ) : ℂ) * (conj (A.eval z) * B.eval z)

theorem conjMulDivOneAddNormSqPow_apply (P : ℂ[X]) (n : ℕ) (A B : ℂ[X]) (z : ℂ) :
    conjMulDivOneAddNormSqPow P n A B z =
      (((1 + ‖P.eval z‖ ^ 2)⁻¹ ^ n : ℝ) : ℂ) * (conj (A.eval z) * B.eval z) :=
  (rfl)

/-- The function `φ ^ n conj A B` is smooth. -/
theorem contDiff_conjMulDivOneAddNormSqPow (P : ℂ[X]) (n : ℕ) (A B : ℂ[X]) :
    ContDiff ℝ ∞ (conjMulDivOneAddNormSqPow P n A B) := by
  have heval (A : ℂ[X]) : ContDiff ℝ ∞ fun z ↦ A.eval z := by
    simpa using (A.contDiff_aeval (𝕜 := ℂ) ∞).restrict_scalars ℝ
  have hN : ContDiff ℝ ∞ fun z ↦ ((1 + ‖P.eval z‖ ^ 2)⁻¹ ^ n : ℝ) :=
    ((contDiff_const.add ((contDiff_norm_sq ℝ).comp (heval P))).inv
      fun z ↦ (by positivity : (0 : ℝ) < 1 + ‖P.eval z‖ ^ 2).ne').pow n
  exact (Complex.ofRealCLM.contDiff.comp hN).mul
    ((Complex.conjCLE.contDiff.comp (heval A)).mul (heval B))

/-- The derivative of `φ ^ n conj A B` along the line `t ↦ z + t v` is again a sum of four
functions of the same form. -/
theorem hasDerivAt_conjMulDivOneAddNormSqPow (P : ℂ[X]) (n : ℕ) (A B : ℂ[X]) (z v : ℂ) :
    HasDerivAt (fun t : ℝ ↦ conjMulDivOneAddNormSqPow P n A B (z + t • v))
      (conjMulDivOneAddNormSqPow P (n + 1) (P * A) (C (-(n : ℂ) * v) * (derivative P * B)) z +
        conjMulDivOneAddNormSqPow P (n + 1) (C (-(n : ℂ) * v) * (derivative P * A)) (P * B) z +
        conjMulDivOneAddNormSqPow P n (C v * derivative A) B z +
        conjMulDivOneAddNormSqPow P n A (C v * derivative B) z) 0 := by
  have hγ : HasDerivAt (fun t : ℝ ↦ z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h0 : z + (0 : ℝ) • v = z := by simp
  have hpoly (Q : ℂ[X]) :
      HasDerivAt (fun t : ℝ ↦ Q.eval (z + t • v)) (Q.derivative.eval z * v) 0 := by
    have h := (Q.hasDerivAt (z + (0 : ℝ) • v)).comp (0 : ℝ) hγ
    rw [h0] at h
    exact h
  have hN : HasDerivAt (fun t : ℝ ↦ 1 + ‖P.eval (z + t • v)‖ ^ 2)
      (2 * inner ℝ (P.eval z) (P.derivative.eval z * v)) 0 := by
    have h := (hpoly P).norm_sq.const_add 1
    rwa [h0] at h
  have hNz : 1 + ‖P.eval z‖ ^ 2 ≠ 0 := by positivity
  have hφ := ((hN.inv (by rwa [h0])).pow n).ofReal_comp
  have hA := (hpoly A).star
  have hB := hpoly B
  have h := hφ.mul (hA.mul hB)
  simp only [h0] at h
  convert h using 1
  · ext t
    simp [conjMulDivOneAddNormSqPow]
  -- The product rule, with `2 ⟪p, p' v⟫ = conj p p' v + p conj (p' v)` and
  -- `n φ ^ (n - 1) / N ^ 2 = n φ ^ (n + 1)` for `φ = N⁻¹`.
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, zero_smul, add_zero,
    conjMulDivOneAddNormSqPow, eval_mul, eval_C, eval_neg, eval_natCast, map_mul, map_neg,
    map_natCast, Complex.inner, Complex.star_def]
  push_cast
  rw [Complex.re_eq_add_conj]
  simp only [map_mul, Complex.conj_conj]
  obtain _ | k := n
  · simp only [CharP.cast_eq_zero, pow_zero]
    ring
  · simp only [div_eq_mul_inv, ← inv_pow, Nat.add_sub_cancel]
    ring

/-- The directional derivatives of the real part of `φ ^ n conj A B`. -/
private theorem fderiv_re_conjMulDivOneAddNormSqPow (P : ℂ[X]) (n : ℕ) (A B : ℂ[X]) (z v : ℂ) :
    fderiv ℝ (fun z ↦ (conjMulDivOneAddNormSqPow P n A B z).re) z v =
      (conjMulDivOneAddNormSqPow P (n + 1) (P * A) (C (-(n : ℂ) * v) * (derivative P * B)) z).re +
        (conjMulDivOneAddNormSqPow P (n + 1) (C (-(n : ℂ) * v) * (derivative P * A)) (P * B) z).re +
        (conjMulDivOneAddNormSqPow P n (C v * derivative A) B z).re +
        (conjMulDivOneAddNormSqPow P n A (C v * derivative B) z).re := by
  have hD : DifferentiableAt ℝ (conjMulDivOneAddNormSqPow P n A B) z :=
    (contDiff_conjMulDivOneAddNormSqPow P n A B).differentiable (by simp) z
  have hre := (Complex.reCLM.hasFDerivAt.comp z hD.hasFDerivAt).fderiv
  have hline := (hD.hasFDerivAt.hasLineDerivAt v).unique
    (hasDerivAt_conjMulDivOneAddNormSqPow P n A B z v)
  simp only [Function.comp_def, Complex.reCLM_apply] at hre
  rw [hre, ContinuousLinearMap.comp_apply, Complex.reCLM_apply, hline]
  simp only [Complex.add_re]

/-- The function `φ ^ n conj A B` is square integrable when `deg A + deg B + 2 ≤ 2 m n`, since
its norm is `‖A‖ ‖B‖ / (1 + ‖P‖²) ^ n`. -/
theorem memLp_conjMulDivOneAddNormSqPow {n : ℕ} {A B : ℂ[X]}
    (h : A.natDegree + B.natDegree + 2 ≤ 2 * P.natDegree * n) :
    MemLp (conjMulDivOneAddNormSqPow P n A B) 2 := by
  refine (memLp_norm_eval_mul_norm_eval_div_one_add_norm_eval_sq_pow h).of_le
    (contDiff_conjMulDivOneAddNormSqPow P n A B).continuous.aestronglyMeasurable
    (.of_forall fun z ↦ le_of_eq ?_)
  have hN : |1 + ‖P.eval z‖ ^ 2| = 1 + ‖P.eval z‖ ^ 2 := abs_of_pos (by positivity)
  simp only [conjMulDivOneAddNormSqPow, norm_mul, Complex.norm_real, Complex.norm_conj, norm_pow,
    Real.norm_eq_abs, abs_inv, abs_pow, hN, abs_div, abs_mul, abs_norm]
  rw [inv_pow, div_eq_inv_mul]

/-- **Rational functions of `1 + ‖P‖²` lie in every Sobolev space.** Let `P`, `A`, `B` be complex
polynomials and `n : ℕ` with `deg A + deg B + 2 ≤ 2 (deg P) n`. Then the real part of
`conj (A z) B z / (1 + ‖P z‖²) ^ n` lies in `H^k(ℂ)` for every `k : ℕ`. -/
theorem re_mem_realSobolevFunctions_of_add_two_le {n : ℕ} {A B : ℂ[X]}
    (h : A.natDegree + B.natDegree + 2 ≤ 2 * P.natDegree * n) (k : ℕ) :
    (fun z ↦ ((((1 + ‖P.eval z‖ ^ 2)⁻¹ ^ n : ℝ) : ℂ) * (conj (A.eval z) * B.eval z)).re) ∈
      realSobolevFunctions ℂ k 2 := by
  simp only [← conjMulDivOneAddNormSqPow.eq_1]
  induction k generalizing n A B with
  | zero =>
    rw [Nat.cast_zero, mem_realSobolevFunctions_zero_iff]
    exact (memLp_conjMulDivOneAddNormSqPow h).re
  | succ k ih =>
    have hm : 0 < P.natDegree := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at h
    have hdP := natDegree_derivative_le P
    have hdA := natDegree_derivative_le A
    have hdB := natDegree_derivative_le B
    rw [Nat.cast_succ]
    refine mem_realSobolevFunctions_add_one_of_fderiv_apply (by norm_num) (by norm_num)
      ((Complex.reCLM.contDiff.comp (contDiff_conjMulDivOneAddNormSqPow P n A B)).of_le (by simp))
      (ih h)
      fun v ↦ ?_
    simp_rw [fderiv_re_conjMulDivOneAddNormSqPow]
    refine add_mem (add_mem (add_mem (ih ?_) (ih ?_)) (ih ?_)) (ih ?_)
    · have := natDegree_mul_le (p := P) (q := A)
      have := natDegree_C_mul_le (-(n : ℂ) * v) (derivative P * B)
      have := natDegree_mul_le (p := derivative P) (q := B)
      rw [mul_add_one]
      generalize 2 * P.natDegree * n = M at h ⊢
      omega
    · have := natDegree_mul_le (p := P) (q := B)
      have := natDegree_C_mul_le (-(n : ℂ) * v) (derivative P * A)
      have := natDegree_mul_le (p := derivative P) (q := A)
      rw [mul_add_one]
      generalize 2 * P.natDegree * n = M at h ⊢
      omega
    · have := natDegree_C_mul_le v (derivative A)
      omega
    · have := natDegree_C_mul_le v (derivative B)
      omega

/-- For a nonconstant complex polynomial `P`, the function `(1 + ‖P‖²)⁻¹` lies in `H^s(ℂ)` for
every real `s`. -/
theorem inv_one_add_norm_eval_sq_mem_realSobolevFunctions (hm : 0 < P.natDegree) (s : ℝ) :
    (fun z ↦ (1 + ‖P.eval z‖ ^ 2)⁻¹) ∈ realSobolevFunctions ℂ s 2 := by
  have h := re_mem_realSobolevFunctions_of_add_two_le (P := P) (n := 1) (A := 1) (B := 1)
    (by simp; omega) ⌈s⌉₊
  refine realSobolevFunctions_mono (by norm_num) ENNReal.ofNat_ne_top (Nat.le_ceil s) ?_
  convert h using 2 with z
  simp only [eval_one, map_one, mul_one, pow_one, Complex.ofReal_re]

/-- For every complex polynomial `P`, the function `‖P'‖² / (1 + ‖P‖²)²` lies in `H^s(ℂ)` for
every real `s`. -/
theorem norm_derivative_eval_sq_div_one_add_norm_eval_sq_sq_mem_realSobolevFunctions (P : ℂ[X])
    (s : ℝ) :
    (fun z ↦ ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2) ∈
      realSobolevFunctions ℂ s 2 := by
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hm
  · convert (realSobolevFunctions ℂ s 2).zero_mem using 1
    ext z
    simp [derivative_of_natDegree_zero h0]
  have hdP := natDegree_derivative_le P
  have h := re_mem_realSobolevFunctions_of_add_two_le (P := P) (n := 2) (A := derivative P)
    (B := derivative P) (by omega) ⌈s⌉₊
  refine realSobolevFunctions_mono (by norm_num) ENNReal.ofNat_ne_top (Nat.le_ceil s) ?_
  convert h using 2 with z
  simp only [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [div_eq_inv_mul, inv_pow]

end Polynomial

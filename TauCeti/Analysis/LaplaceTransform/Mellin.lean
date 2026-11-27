/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.LaplaceTransform.Elementary
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# From upper Mellin tails to Laplace transforms

The change of variable `y = exp u` identifies an upper Mellin tail with the Laplace transform
of `u ↦ f (exp u)`, including absolute convergence. In particular the tail above `1` becomes
an ordinary one-sided Laplace transform. This allows half-plane continuation results for
Laplace transforms to be used for Mellin transforms of arithmetic remainders. As an example,
the tail above `1` of the main terms `c y + m y log y` of first Riesz sums is computed.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- The Laplace transform of `f ∘ exp` on `(a, ∞)` equals the upper Mellin tail of `f` on
`(exp a, ∞)` at exponent `-(s + 1)`, with equivalent absolute convergence. -/
theorem hasLaplace_comp_exp_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (s : ℂ) (z : E) (a : ℝ) :
    HasLaplace (f ∘ Real.exp) s z (volume.restrict (Ioi a)) ↔
      IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ (-(s + 1)) • f y) (Ioi (Real.exp a)) ∧
      ∫ y in Ioi (Real.exp a), (y : ℂ) ^ (-(s + 1)) • f y = z := by
  let g (y : ℝ) := (y : ℂ) ^ (-(s + 1)) • f y
  have heq (u : ℝ) : Real.exp u • g (Real.exp u) = Complex.exp (-s * u) • f (Real.exp u) := by
    dsimp only [g]
    rw [← Complex.coe_smul, smul_smul, ofReal_exp_cpow, Complex.ofReal_exp, ← Complex.exp_add]
    ring_nf
  have hint := integrableOn_comp_exp_Ioi g a
  have hval := integral_comp_exp_Ioi g a
  simp only [heq, g] at hint hval
  rw [hasLaplace_iff, Function.comp_def]
  exact and_congr hint (by rw [hval])

/-- The upper Mellin tail above `1` of `y ↦ c y + m y log y` converges absolutely on
`1 < re s`, with value `c / (s - 1) + m / (s - 1) ^ 2`. These are the main terms subtracted
from first Riesz sums of coefficients of `-L′/L`. -/
theorem integrableOn_and_integral_mul_add_mul_log_mul_cpow (c m : ℂ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ ↦ (c * y + m * y * Real.log y) * (y : ℂ) ^ (-s - 1)) (Ioi 1) ∧
    ∫ y in Ioi (1 : ℝ), (c * y + m * y * Real.log y) * (y : ℂ) ^ (-s - 1) =
      c / (s - 1) + m / (s - 1) ^ 2 := by
  have hlin := (hasLaplace_cexp_mul (w := 1) (by simpa using hs)).const_smul c
  have hlog := (hasLaplace_cexp_mul_pow 1 (w := 1) (by simpa using hs)).const_smul m
  have heq : -(s + 1) = -s - 1 := by ring
  have h := (hlin.add hlog).congr_ae
    (g := (fun y : ℝ ↦ c * y + m * y * Real.log y) ∘ Real.exp)
    (Filter.Eventually.of_forall fun u ↦ by simp [smul_eq_mul, Complex.ofReal_exp, mul_assoc])
  simpa only [smul_eq_mul, Real.exp_zero, heq, mul_comm, Nat.factorial_one, Nat.cast_one,
    div_eq_mul_inv, one_mul, zero_add, Nat.reduceAdd] using (hasLaplace_comp_exp_iff _ _ _ 0).mp h

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# From upper Mellin tails to Laplace transforms

The change of variable `y = exp u` identifies an upper Mellin tail with the Laplace transform
of `u ↦ f (exp u)`, including absolute convergence. In particular the tail above `1` becomes
an ordinary one-sided Laplace transform. This allows half-plane continuation results for
Laplace transforms to be used for Mellin transforms of arithmetic remainders.
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

/-- Absolute convergence of an upper Mellin tail at `s` can be tested by integrating the norm
of the input against the real power with exponent `-(s.re + 1)`. -/
theorem integrableOn_cpow_smul_iff_rpow_mul_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {a : ℝ} (ha : 0 ≤ a) {f : ℝ → E}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi a))) (s : ℂ) :
    IntegrableOn (fun y : ℝ ↦ (y : ℂ) ^ (-(s + 1)) • f y) (Ioi a) ↔
      IntegrableOn (fun y : ℝ ↦ y ^ (-(s.re + 1)) * ‖f y‖) (Ioi a) := by
  have hnorm (y : ℝ) (hy : y ∈ Ioi a) :
      ‖(y : ℂ) ^ (-(s + 1)) • f y‖ = y ^ (-(s.re + 1)) * ‖f y‖ := by
    simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_lt hy),
      Complex.neg_re, Complex.add_re, Complex.one_re]
  rw [← integrableOn_congr_fun hnorm measurableSet_Ioi]
  exact (integrable_norm_iff ((Complex.measurable_ofReal.pow_const _).aestronglyMeasurable.smul
    hf)).symm

end TauCeti

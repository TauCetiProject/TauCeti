/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Negative real powers are completely monotone

This file adds the **negative-power (Stieltjes) kernels** to the `OneParameterSemigroups`
roadmap's catalogue of concrete completely monotone functions, alongside the exponentials
`t ↦ e^{-x t}` in `TauCeti.Analysis.CompletelyMonotone.Basic` and the plain reciprocals
`t ↦ (a + t)⁻¹` in `TauCeti.Analysis.CompletelyMonotone.Reciprocal`.

For a real exponent `s ≥ 0` the `n`-th derivative of `y ↦ y^{-s}` is
`(descPochhammer ℝ n)(-s) · y^{-s-n}`, and the falling factorial `(-s)(-s-1)⋯(-s-n+1)`
carries the sign `(-1)ⁿ`, so `(-1)ⁿ` times the derivative is `s(s+1)⋯(s+n-1) · y^{-s-n} ≥ 0`.
Two consequences:

* on the open half-line, `t ↦ t^{-s}` is completely monotone for every `s ≥ 0` — the case
  `s = 1` is `t ↦ 1/t`, whose (infinite) representing measure is Lebesgue measure, the
  Hausdorff–Bernstein–Widder example the roadmap flags for the open half-line;
* shifted by `a > 0`, the resolvent-power kernel `t ↦ (a + t)^{-s}` is completely monotone up
  to and including the boundary point `0` (its derivatives stay finite there), so it is a
  member of the closed-half-line class governed by Bernstein's theorem. The special case `a = 1`,
  `t ↦ (1 + t)^{-s}`, has the Gamma distribution as its representing measure and generalises the
  roadmap acceptance example `t ↦ 1/(1 + t)` (`s = 1`).

The iterated derivative of `y ↦ y^s` is Mathlib's `Real.iter_deriv_rpow_const`, and the sign of
the falling factorial at a negative argument is packaged in the private lemma
`neg_one_pow_mul_descPochhammer_neg_nonneg`.

## Main declarations

* `TauCeti.isCompletelyMonotoneOnIoi_rpow_neg`: for `s ≥ 0`, `t ↦ t^{-s}` is completely monotone
  on the open half-line `(0, ∞)`.
* `TauCeti.isCompletelyMonotone_rpow_neg_const_add`: for `a > 0` and `s ≥ 0`, the resolvent-power
  kernel `t ↦ (a + t)^{-s}` is completely monotone on the closed half-line `[0, ∞)`.
* `TauCeti.isCompletelyMonotone_rpow_neg_one_add`: the `a = 1` case `t ↦ (1 + t)^{-s}`, whose
  representing measure is the Gamma distribution with shape `s` for `s > 0` (and the Dirac mass `δ₀`
  at `s = 0`).

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012).
-/

public section

open Set
open scoped ContDiff

namespace TauCeti

/-- The falling factorial `(-s)(-s-1)⋯(-s-n+1) = (descPochhammer ℝ n)(-s)` carries the sign
`(-1)ⁿ` when `s ≥ 0`: multiplying it by `(-1)ⁿ` yields the nonnegative rising factorial
`s(s+1)⋯(s+n-1)`. This is the sign bookkeeping behind complete monotonicity of `t ↦ t^{-s}`. -/
private lemma neg_one_pow_mul_descPochhammer_neg_nonneg {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    0 ≤ (-1 : ℝ) ^ n * (descPochhammer ℝ n).eval (-s) := by
  rw [← ascPochhammer_eval_neg_eq_descPochhammer ℝ (-s) n, neg_neg]
  obtain rfl | hs := hs.eq_or_lt
  · by_cases hn : n = 0 <;> simp [hn]
  · exact (ascPochhammer_pos n s hs).le

/-- For `s ≥ 0`, the negative power `t ↦ t^{-s}` is completely monotone on the open half-line
`(0, ∞)`. The case `s = 1` is `t ↦ 1/t`, whose representing measure is (infinite) Lebesgue
measure; the demand for smoothness only on `(0, ∞)` is essential, as `t^{-s}` blows up at the
boundary for `s > 0`. -/
theorem isCompletelyMonotoneOnIoi_rpow_neg {s : ℝ} (hs : 0 ≤ s) :
    IsCompletelyMonotoneOnIoi (fun t => t ^ (-s)) := by
  refine ⟨fun t ht => (Real.contDiffAt_rpow_const_of_ne (mem_Ioi.mp ht).ne').contDiffWithinAt,
    fun n t ht => ?_⟩
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, ← mul_assoc]
  exact mul_nonneg (neg_one_pow_mul_descPochhammer_neg_nonneg hs n)
    (Real.rpow_pos_of_pos ht _).le

/-- For `a > 0` and `s ≥ 0`, the resolvent-power kernel `t ↦ (a + t)^{-s}` is completely
monotone on the closed half-line `[0, ∞)`. This generalises the reciprocal
`isCompletelyMonotone_inv_const_add` (the exponent `s = 1`), and its derivatives stay finite at
the boundary, so it belongs to the closed-half-line class of Bernstein's theorem. -/
theorem isCompletelyMonotone_rpow_neg_const_add {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s) :
    IsCompletelyMonotone (fun t => (a + t) ^ (-s)) := by
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 < a + t := fun t ht => by linarith
  -- Smoothness on `[0, ∞)`: `a + t` never vanishes there, so `y ↦ y^{-s}` composes smoothly.
  have hcat : ∀ (m : WithTop ℕ∞) (t : ℝ), 0 ≤ t →
      ContDiffAt ℝ m (fun t : ℝ => (a + t) ^ (-s)) t := fun m t ht =>
    (Real.contDiffAt_rpow_const_of_ne (hpos t ht).ne').comp t (by fun_prop)
  refine ⟨fun t ht => (hcat ∞ t ht).contDiffWithinAt, fun n t ht => ?_⟩
  have htpos : 0 < a + t := hpos t ht
  -- Reduce the iterated derivative *within* `[0, ∞)` to the ordinary one, then translate.
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) (hcat n t ht) (mem_Ici.mpr ht)]
  have hcomp : iteratedDeriv n (fun t : ℝ => (a + t) ^ (-s)) t
      = iteratedDeriv n (fun y : ℝ => y ^ (-s)) (a + t) :=
    congrFun (iteratedDeriv_comp_const_add n (fun y : ℝ => y ^ (-s)) a) t
  rw [hcomp, iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, ← mul_assoc]
  exact mul_nonneg (neg_one_pow_mul_descPochhammer_neg_nonneg hs n)
    (Real.rpow_pos_of_pos htpos _).le

/-- The roadmap acceptance example generalised in the exponent: for `s ≥ 0` the kernel
`t ↦ (1 + t)^{-s}` is completely monotone. For `s > 0` its representing measure under Bernstein's
theorem is the Gamma distribution with shape `s`, and the case `s = 1` is `t ↦ 1/(1 + t)` with the
exponential distribution `e^{-x} dx`; at the endpoint `s = 0` the kernel is the constant `1`, whose
representing measure is the Dirac mass `δ₀`. -/
theorem isCompletelyMonotone_rpow_neg_one_add {s : ℝ} (hs : 0 ≤ s) :
    IsCompletelyMonotone (fun t => (1 + t) ^ (-s)) :=
  isCompletelyMonotone_rpow_neg_const_add one_pos hs

end TauCeti

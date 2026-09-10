/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Composition
public import TauCeti.Analysis.CompletelyMonotone.Limits
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Bernstein functions are the exponents of completely monotone semigroups

`TauCeti.IsBernsteinFunction.isContinuousCompletelyMonotoneOnIoi_exp_neg_mul` produces, from a
Bernstein function `f`, the completely monotone functions `t ↦ e^{-x f(t)}` for every `x ≥ 0` —
the Laplace transforms of the convolution semigroup subordinate to `f`.  This file proves the
converse, so that the two classes determine each other:

**`f` is a Bernstein function if and only if `f` is nonnegative on `[0, ∞)` and, for every
`x > 0`, `e^{-x f}` is continuous on `[0, ∞)` and completely monotone on `(0, ∞)`.**

This is the standard correspondence between the two classes, and the form in which Bernstein
functions enter probability theory: `e^{-x f}` completely monotone for all `x > 0` says exactly
that `f` is the Laplace exponent of a subordinator.

Quantifying over *all* `x > 0` is essential, and the proof shows why: differentiating
`t ↦ e^{-x f(t)}` gives the exact identity

`- x⁻¹ · (e^{-x f})'(t) = f'(t) · e^{-x f(t)}`,

so the left-hand side is completely monotone by
`TauCeti.IsCompletelyMonotoneOnIoi.neg_deriv`, and letting `x ↓ 0` along `x = 1 / (n + 1)` makes
the right-hand side converge pointwise to `f'`.  Complete monotonicity survives that limit by
`TauCeti.isCompletelyMonotoneOnIoi_of_tendsto`, which is the whole content: a single `x` says far
less, since it constrains only one member of the family.

The remaining hypotheses of `TauCeti.IsBernsteinFunction` are recovered from the exponentials
rather than assumed: `f = -x⁻¹ log (e^{-x f})` inherits smoothness on `(0, ∞)` from `e^{-x f}`,
and continuity on `[0, ∞)` as soon as one exponential is continuous there.  Nonnegativity of `f`
is genuinely independent — the constant `-1` has `e^{x}` for its exponentials, and constants are
completely monotone.

## Main declarations

* `TauCeti.isCompletelyMonotoneOnIoi_deriv_mul_exp_neg_mul`: for `x > 0`, the function
  `t ↦ f'(t) · e^{-x f(t)}` is completely monotone on `(0, ∞)` whenever `e^{-x f}` is.
* `TauCeti.isBernsteinFunction_of_forall_isCompletelyMonotoneOnIoi_exp_neg_mul`: the converse
  direction, that the family of exponentials forces `f` to be a Bernstein function.
* `isBernsteinFunction_iff_nonneg_and_forall_isContinuousCompletelyMonotoneOnIoi_exp_neg_mul`: the
  resulting characterization of Bernstein functions.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Theorem 3.7.
-/

public section

open Filter Set
open scoped ContDiff Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-- Smoothness of `f` on `(0, ∞)` is inherited from a single exponential `e^{-x f}`: the
exponential is positive, so composing with the logarithm stays inside the domain of smoothness of
`Real.log`, and `Real.log_exp` recovers `f` from `e^{-x f}` on the nose. -/
lemma contDiffOn_of_contDiffOn_exp_neg_mul {x : ℝ} (hx : x ≠ 0) {s : Set ℝ}
    (h : ContDiffOn ℝ ∞ (fun t => Real.exp (-x * f t)) s) : ContDiffOn ℝ ∞ f s := by
  have hlog : ContDiffOn ℝ ∞ (fun t => -x⁻¹ * Real.log (Real.exp (-x * f t))) s :=
    (h.log fun t _ => (Real.exp_pos _).ne').const_smul (-x⁻¹)
  refine hlog.congr fun t _ => ?_
  simp only [Real.log_exp]
  field_simp

/-- Continuity of `f` on a set is inherited from a single exponential `e^{-x f}`. -/
lemma continuousOn_of_continuousOn_exp_neg_mul {x : ℝ} (hx : x ≠ 0) {s : Set ℝ}
    (h : ContinuousOn (fun t => Real.exp (-x * f t)) s) : ContinuousOn f s := by
  have hlog : ContinuousOn (fun t => -x⁻¹ * Real.log (Real.exp (-x * f t))) s :=
    continuousOn_const.mul (h.log fun t _ => (Real.exp_pos _).ne')
  refine hlog.congr fun t _ => ?_
  simp only [Real.log_exp]
  field_simp

/-- The derivative of `f` weighted by an exponential.  If `e^{-x f}` is completely monotone on
`(0, ∞)` for some `x > 0`, then so is `t ↦ f'(t) · e^{-x f(t)}`, because that function is
`-x⁻¹` times the derivative of `e^{-x f}`. -/
theorem isCompletelyMonotoneOnIoi_deriv_mul_exp_neg_mul {x : ℝ} (hx : 0 < x)
    (h : IsCompletelyMonotoneOnIoi fun t => Real.exp (-x * f t)) :
    IsCompletelyMonotoneOnIoi fun t => deriv f t * Real.exp (-x * f t) := by
  have hsmooth : ContDiffOn ℝ ∞ f (Ioi 0) :=
    contDiffOn_of_contDiffOn_exp_neg_mul hx.ne' h.contDiffOn
  refine (h.neg_deriv.smul (c := x⁻¹) (by positivity)).congr fun t ht => ?_
  have hdf : HasDerivAt f (deriv f t) t :=
    (hsmooth.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds ht) |>.hasDerivAt
  have hexp : HasDerivAt (fun t => Real.exp (-x * f t))
      (Real.exp (-x * f t) * (-x * deriv f t)) t := ((hdf.const_mul (-x)).exp)
  rw [Pi.smul_apply, smul_eq_mul, hexp.deriv]
  field_simp

/-- **The exponentials of a Bernstein function determine it.**  If `f` is nonnegative on `[0, ∞)`,
continuous there, and `e^{-x f}` is completely monotone on `(0, ∞)` for every `x > 0`, then `f` is
a Bernstein function.

This is the converse of
`TauCeti.IsBernsteinFunction.isContinuousCompletelyMonotoneOnIoi_exp_neg_mul`; smoothness of `f`
on `(0, ∞)` is not assumed, but deduced from the exponential at `x = 1`. -/
theorem isBernsteinFunction_of_forall_isCompletelyMonotoneOnIoi_exp_neg_mul
    (hcont : ContinuousOn f (Ici 0)) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    (h : ∀ x : ℝ, 0 < x → IsCompletelyMonotoneOnIoi fun t => Real.exp (-x * f t)) :
    IsBernsteinFunction f := by
  have hsmooth : ContDiffOn ℝ ∞ f (Ioi 0) :=
    contDiffOn_of_contDiffOn_exp_neg_mul one_ne_zero (h 1 one_pos).contDiffOn
  refine isBernsteinFunction_iff.mpr ⟨hcont, hsmooth, hnonneg, ?_⟩
  refine isCompletelyMonotoneOnIoi_of_tendsto (L := atTop)
    (F := fun n : ℕ => fun t => deriv f t * Real.exp (-(1 / ((n : ℝ) + 1)) * f t))
    (.of_forall fun n => isCompletelyMonotoneOnIoi_deriv_mul_exp_neg_mul (by positivity)
      (h _ (by positivity))) fun u _ => ?_
  have hc : Continuous fun y : ℝ => deriv f u * Real.exp (-y * f u) := by fun_prop
  simpa [Function.comp_def] using (hc.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat

/-- **The characterization of Bernstein functions by complete monotonicity of their
exponentials.**  A function is a Bernstein function exactly when it is nonnegative on `[0, ∞)` and
each `e^{-x f}`, `x > 0`, is completely monotone on `(0, ∞)` and continuous on `[0, ∞)`.

Continuity of `f` itself is not part of the right-hand side: it is recovered from continuity of
one exponential.  Nonnegativity is not: the constant `-1` satisfies every other clause. -/
theorem isBernsteinFunction_iff_nonneg_and_forall_isContinuousCompletelyMonotoneOnIoi_exp_neg_mul :
    IsBernsteinFunction f ↔
      (∀ t : ℝ, 0 ≤ t → 0 ≤ f t) ∧
        ∀ x : ℝ, 0 < x → IsContinuousCompletelyMonotoneOnIoi fun t => Real.exp (-x * f t) := by
  refine ⟨fun hf => ⟨fun t ht => hf.nonneg ht, fun x hx =>
    hf.isContinuousCompletelyMonotoneOnIoi_exp_neg_mul hx.le⟩, fun ⟨hnonneg, h⟩ => ?_⟩
  refine isBernsteinFunction_of_forall_isCompletelyMonotoneOnIoi_exp_neg_mul ?_ hnonneg
    fun x hx => (h x hx).isCompletelyMonotoneOnIoi
  exact continuousOn_of_continuousOn_exp_neg_mul one_ne_zero (h 1 one_pos).continuousOn

end TauCeti

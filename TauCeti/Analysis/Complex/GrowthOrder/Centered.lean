/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder.Logarithmic
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Centered global bounds for entire functions of order at most one

An entire function `f : ℂ → ℂ` satisfies `TauCeti.IsCenteredOrderOne f` when for every `ε > 0`
there exists `C > 0` such that `‖f z‖ ≤ exp (C * (1 + ‖z‖ ^ (1 + ε)))` for all `z : ℂ`. Unlike
`TauCeti.OrderLE`, this formulation bundles entirety with a single global bound valid across both
compact sets and infinity.

The main theorem `TauCeti.isCenteredOrderOne_iff` proves that `IsCenteredOrderOne f` is equivalent
to `Differentiable ℂ f ∧ OrderLE f 1`: a centered bound with exponent `1 + (A' - 1) / 2` is
dominated at infinity by `exp (‖z‖ ^ A')`, while conversely the asymptotic bound at `1 + ε` holds
outside a closed ball on which continuity of `f` supplies a uniform bound absorbed into `exp C`.

Consequently `IsCenteredOrderOne` is closed under ring operations, affine substitutions,
polynomials, linear exponentials, and logarithmic-exponential bounds of the form
`exp (C (1 + ‖s‖) log (2 + ‖s‖))` (such as `1 / Γ`), while excluding higher-order functions such
as `exp (z ^ 2)`.

## Main results

* `TauCeti.IsCenteredOrderOne`: global centered order-at-most-one predicate for entire functions.
* `TauCeti.isCenteredOrderOne_iff`: equivalence with `Differentiable ℂ f ∧ OrderLE f 1`.
* `TauCeti.IsCenteredOrderOne.add`, `TauCeti.IsCenteredOrderOne.const_mul`,
  `TauCeti.IsCenteredOrderOne.pow`, `TauCeti.IsCenteredOrderOne.comp_mul_add`,
  `Polynomial.isCenteredOrderOne_eval`, `TauCeti.isCenteredOrderOne_cexp_mul`: algebraic and
  analytic closure properties.
* `TauCeti.IsCenteredOrderOne.of_norm_le_exp_mul_log`: transfer from logarithmic-exponential bounds.
* `TauCeti.not_isCenteredOrderOne_cexp_sq`: `exp (z ^ 2)` does not satisfy `IsCenteredOrderOne`.

## References

* Z. Yun and W. Zhang, *Shtukas and the Taylor expansion of L-functions*, Ann. of Math. (2) **186**
  (2017), no. 3, 767–911, Appendix B.1.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 11.
-/

public section

open Complex Filter Metric Asymptotics Bornology Topology
open scoped BigOperators

namespace TauCeti

/-- Entire growth of order at most one in global centered form: `f` is complex differentiable on
`ℂ` and for every `ε > 0` there exists `C > 0` such that
`‖f z‖ ≤ exp (C * (1 + ‖z‖ ^ (1 + ε)))` for all `z : ℂ`. -/
def IsCenteredOrderOne (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖ ^ (1 + ε)))

variable {f g : ℂ → ℂ}

namespace IsCenteredOrderOne

/-- A function satisfying `IsCenteredOrderOne` is entire. -/
theorem differentiable (hf : IsCenteredOrderOne f) : Differentiable ℂ f :=
  hf.1

/-- A global centered order-one bound implies `OrderLE f 1`. -/
theorem orderLE_one (hf : IsCenteredOrderOne f) : OrderLE f 1 := by
  rw [orderLE_def]
  intro A' hA'
  have hε : 0 < (A' - 1) / 2 := by linarith
  obtain ⟨C, _, hC⟩ := hf.2 ((A' - 1) / 2) hε
  have hexp : 1 + (A' - 1) / 2 < A' := by linarith
  have hdom : f =O[cobounded ℂ] fun z : ℂ ↦ Real.exp (C * ‖z‖ ^ (1 + (A' - 1) / 2)) := by
    refine IsBigO.of_bound (Real.exp C) (Eventually.of_forall fun z ↦ ?_)
    rw [Real.norm_eq_abs, Real.abs_exp, ← Real.exp_add]
    exact (hC z).trans_eq (by ring_nf)
  exact hdom.trans (isBigO_exp_mul_norm_rpow C hexp)

end IsCenteredOrderOne

/-- An entire function of order at most one satisfies the global centered bound
`IsCenteredOrderOne`. -/
theorem OrderLE.isCenteredOrderOne (h : OrderLE f 1) (hf : Differentiable ℂ f) :
    IsCenteredOrderOne f := by
  refine ⟨hf, fun ε hε ↦ ?_⟩
  obtain ⟨c, _, hb⟩ := (h.isBigO (A' := 1 + ε) (by linarith)).exists_pos
  obtain ⟨R, _, hR⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp hb.bound
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (max R 0)).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  set C : ℝ := max 1 (max M c)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hMC : M ≤ C := (le_max_left M c).trans (le_max_right _ _)
  have hcC : c ≤ C := (le_max_right M c).trans (le_max_right _ _)
  refine ⟨C, zero_lt_one.trans_le hC1, fun z ↦ ?_⟩
  have hr : 0 ≤ ‖z‖ ^ (1 + ε) := Real.rpow_nonneg (norm_nonneg z) _
  by_cases hz : ‖z‖ ≤ max R 0
  · have hfz : ‖f z‖ ≤ M := hM z (mem_closedBall_zero_iff.mpr hz)
    have hle : M ≤ C * (1 + ‖z‖ ^ (1 + ε)) := by
      nlinarith
    exact hfz.trans (hle.trans ((le_add_of_nonneg_right zero_le_one).trans
      (Real.add_one_le_exp _)))
  · push Not at hz
    have hfz : ‖f z‖ ≤ c * Real.exp (‖z‖ ^ (1 + ε)) := by
      have hRz : R ≤ ‖z‖ := ((le_max_left R 0).trans_lt hz).le
      simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs, Real.abs_exp] using hR hRz
    have hc_exp : c ≤ Real.exp C :=
      hcC.trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp C))
    have hr_exp : Real.exp (‖z‖ ^ (1 + ε)) ≤ Real.exp (C * ‖z‖ ^ (1 + ε)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc ‖f z‖ ≤ c * Real.exp (‖z‖ ^ (1 + ε)) := hfz
      _ ≤ Real.exp C * Real.exp (C * ‖z‖ ^ (1 + ε)) :=
        mul_le_mul hc_exp hr_exp (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (C * (1 + ‖z‖ ^ (1 + ε))) := by
        rw [← Real.exp_add]
        ring_nf

/-- `IsCenteredOrderOne f` holds if and only if `f` is entire and has order at most one. -/
theorem isCenteredOrderOne_iff :
    IsCenteredOrderOne f ↔ Differentiable ℂ f ∧ OrderLE f 1 :=
  ⟨fun h ↦ ⟨h.differentiable, h.orderLE_one⟩, fun ⟨hf, h⟩ ↦ h.isCenteredOrderOne hf⟩

namespace IsCenteredOrderOne

/-- Any entire function of order at most `A ≤ 1` satisfies `IsCenteredOrderOne`. -/
theorem of_orderLE {A : ℝ} (hf : Differentiable ℂ f) (h : OrderLE f A) (hA : A ≤ 1) :
    IsCenteredOrderOne f :=
  (h.mono hA).isCenteredOrderOne hf

/-- An entire function bounded by `exp (C (1 + ‖s‖) log (2 + ‖s‖))` satisfies
`IsCenteredOrderOne`. -/
theorem of_norm_le_exp_mul_log {C : ℝ} (hf : Differentiable ℂ f)
    (hb : ∀ s, ‖f s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖))) :
    IsCenteredOrderOne f :=
  (orderLE_one_of_norm_le_exp_mul_log hb).isCenteredOrderOne hf

/-- A sum of two functions satisfying `IsCenteredOrderOne` satisfies `IsCenteredOrderOne`. -/
theorem add (hf : IsCenteredOrderOne f) (hg : IsCenteredOrderOne g) :
    IsCenteredOrderOne (fun z ↦ f z + g z) :=
  (hf.orderLE_one.add hg.orderLE_one).isCenteredOrderOne (hf.differentiable.add hg.differentiable)

/-- Scaling by a complex constant preserves `IsCenteredOrderOne`. -/
theorem const_mul (hf : IsCenteredOrderOne f) (c : ℂ) :
    IsCenteredOrderOne (fun z ↦ c * f z) :=
  (hf.orderLE_one.const_mul c).isCenteredOrderOne (hf.differentiable.const_mul c)

/-- Natural powers preserve `IsCenteredOrderOne`. -/
theorem pow (hf : IsCenteredOrderOne f) (n : ℕ) :
    IsCenteredOrderOne (fun z ↦ f z ^ n) :=
  (hf.orderLE_one.pow n).isCenteredOrderOne (hf.differentiable.pow n)

/-- Pullback along an affine map `z ↦ a * z + b` preserves `IsCenteredOrderOne`. -/
theorem comp_mul_add (hf : IsCenteredOrderOne f) (a b : ℂ) :
    IsCenteredOrderOne (fun z ↦ f (a * z + b)) :=
  (hf.orderLE_one.comp_mul_add a b).isCenteredOrderOne
    (hf.differentiable.comp ((differentiable_id.const_mul a).add_const b))

/-- Pullback along negation `z ↦ -z` preserves `IsCenteredOrderOne`. -/
theorem comp_neg (hf : IsCenteredOrderOne f) :
    IsCenteredOrderOne (fun z ↦ f (-z)) := by
  simpa using hf.comp_mul_add (-1) 0

end IsCenteredOrderOne

/-- Every constant function satisfies `IsCenteredOrderOne`. -/
@[simp]
theorem isCenteredOrderOne_const (c : ℂ) : IsCenteredOrderOne (fun _ ↦ c) :=
  (orderLE_const c 1).isCenteredOrderOne (differentiable_const c)

/-- Every complex polynomial satisfies `IsCenteredOrderOne`. -/
theorem _root_.Polynomial.isCenteredOrderOne_eval (p : Polynomial ℂ) :
    IsCenteredOrderOne p.eval :=
  IsCenteredOrderOne.of_orderLE (Polynomial.differentiable p) p.orderLE_eval zero_le_one

/-- The identity map `z ↦ z` satisfies `IsCenteredOrderOne`. -/
@[simp]
theorem isCenteredOrderOne_id : IsCenteredOrderOne (fun z ↦ z) := by
  simpa using (Polynomial.X : Polynomial ℂ).isCenteredOrderOne_eval

/-- For every `a : ℂ`, the linear exponential `z ↦ exp (a * z)` satisfies `IsCenteredOrderOne`. -/
theorem isCenteredOrderOne_cexp_mul (a : ℂ) : IsCenteredOrderOne (fun z ↦ cexp (a * z)) :=
  (orderLE_cexp_mul a).isCenteredOrderOne (by fun_prop)

/-- The complex exponential satisfies `IsCenteredOrderOne`. -/
theorem isCenteredOrderOne_cexp : IsCenteredOrderOne cexp := by
  simpa using isCenteredOrderOne_cexp_mul 1

/-- The Gaussian exponential `z ↦ exp (z ^ 2)` has order two and therefore fails
`IsCenteredOrderOne`. -/
theorem not_isCenteredOrderOne_cexp_sq : ¬ IsCenteredOrderOne (fun z ↦ cexp (z ^ 2)) := by
  rw [isCenteredOrderOne_iff, orderLE_cexp_pow_iff (by norm_num)]
  norm_num

end TauCeti

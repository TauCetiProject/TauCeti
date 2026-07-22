/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.Basic
public import TauCeti.Analysis.CompletelyMonotone.Power
public import TauCeti.Analysis.CompletelyMonotone.Reciprocal
import TauCeti.Analysis.CompletelyMonotone.Closure
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The standard catalogue of Bernstein functions

`TauCeti.Analysis.CompletelyMonotone.Bernstein.Basic` records that constants, the identity,
affine functions `t ↦ c + d t`, and the prototype `t ↦ 1 - e^{-x t}` are Bernstein functions.
This file adds the three transcendental members of the classical catalogue, each the Laplace
exponent of a well-known subordinator:

* the **fractional power** `t ↦ t^a` for `0 ≤ a ≤ 1` (the `a`-stable subordinator), whose
  derivative `a · t^{a-1} = a · t^{-(1-a)}` is completely monotone by
  `TauCeti.isCompletelyMonotoneOnIoi_rpow_neg`;
* the **logarithm** `t ↦ log(1 + t)` (the Gamma subordinator), whose derivative `(1 + t)^{-1}`
  is completely monotone by `TauCeti.isCompletelyMonotone_one_div_one_add`;
* the **saturating ramp** `t ↦ t / (1 + t)` (the Laplace exponent of a rate-one compound Poisson
  subordinator with exponential jumps), which equals `1 - (1 + t)^{-1}` and whose derivative
  `(1 + t)^{-2}` is completely monotone as a square of the resolvent kernel
  `TauCeti.isCompletelyMonotone_inv_const_add`.

Each proof is the same three-step recipe: check continuity and nonnegativity on `[0, ∞)` and
smoothness on `(0, ∞)` directly, compute the ordinary derivative on `(0, ∞)`, and transport the
relevant completely-monotone fact along that derivative with `IsBernsteinFunction`'s `congr`
lemma. The fractional power is stated at general `0 ≤ a ≤ 1`, with `t ↦ √t` recorded as the
`a = 1/2` corollary.

## Main declarations

* `TauCeti.isBernsteinFunction_rpow`: `t ↦ t^a` is a Bernstein function for `0 ≤ a ≤ 1`.
* `TauCeti.isBernsteinFunction_sqrt`: `t ↦ √t` is a Bernstein function.
* `TauCeti.isBernsteinFunction_log_one_add`: `t ↦ log(1 + t)` is a Bernstein function.
* `TauCeti.isBernsteinFunction_id_div_one_add`: `t ↦ t / (1 + t)` is a Bernstein function.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Chapter 16 (the table of complete Bernstein functions).
-/

public section

open Set
open scoped ContDiff Topology

namespace TauCeti

/-- The **fractional power** `t ↦ t^a` is a Bernstein function whenever `0 ≤ a ≤ 1`. On `(0, ∞)`
its derivative is `a · t^{a-1} = a · t^{-(1-a)}`, which is completely monotone because
`1 - a ≥ 0`. For `0 < a < 1` this is the Laplace exponent of the `a`-stable subordinator; the
endpoints recover the constant `1` (`a = 0`) and the identity (`a = 1`). -/
theorem isBernsteinFunction_rpow {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    IsBernsteinFunction (fun t : ℝ => t ^ a) := by
  refine isBernsteinFunction_iff.mpr
    ⟨(Real.continuous_rpow_const ha).continuousOn, ?_, fun t ht => Real.rpow_nonneg ht a, ?_⟩
  · exact fun t ht => (Real.contDiffAt_rpow_const_of_ne (mem_Ioi.mp ht).ne').contDiffWithinAt
  · -- The derivative on `(0, ∞)` is `a · t^{-(1-a)}`; use `1 - a ≥ 0` for complete monotonicity.
    have hcm : IsCompletelyMonotoneOnIoi (a • fun t : ℝ => t ^ (-(1 - a))) :=
      (isCompletelyMonotoneOnIoi_rpow_neg (by linarith)).smul ha
    refine hcm.congr fun t ht => ?_
    have htne : t ≠ 0 := (mem_Ioi.mp ht).ne'
    rw [(Real.hasDerivAt_rpow_const (Or.inl htne)).deriv, Pi.smul_apply, smul_eq_mul]
    congr 1
    rw [show a - 1 = -(1 - a) by ring]

/-- The **square root** `t ↦ √t` is a Bernstein function: the `a = 1/2` case of
`isBernsteinFunction_rpow`. Its derivative `t ↦ (2√t)⁻¹` blows up at the boundary, which is
exactly why the definition only demands smoothness on the open half-line. -/
theorem isBernsteinFunction_sqrt : IsBernsteinFunction (fun t : ℝ => Real.sqrt t) :=
  (isBernsteinFunction_rpow (a := 1 / 2) (by norm_num) (by norm_num)).congr fun t _ =>
    Real.sqrt_eq_rpow t

/-- The **logarithm** `t ↦ log(1 + t)` is a Bernstein function: on `(0, ∞)` its derivative is the
resolvent kernel `(1 + t)^{-1}`, completely monotone by `isCompletelyMonotone_one_div_one_add`.
This is the Laplace exponent of the Gamma subordinator. -/
theorem isBernsteinFunction_log_one_add :
    IsBernsteinFunction (fun t : ℝ => Real.log (1 + t)) := by
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 < 1 + t := fun t ht => by linarith
  refine isBernsteinFunction_iff.mpr ⟨ContinuousOn.log (by fun_prop) fun t ht => (hpos t ht).ne',
    ContDiffOn.log (by fun_prop) fun t ht => (hpos t (mem_Ioi.mp ht).le).ne',
    fun t ht => Real.log_nonneg (by linarith), ?_⟩
  -- The derivative on `(0, ∞)` is `t ↦ 1 / (1 + t)`.
  refine (isCompletelyMonotone_one_div_one_add.isCompletelyMonotoneOnIoi).congr fun t ht => ?_
  have hd : HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t := by
    have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by simpa using (hasDerivAt_id t).const_add 1
    have h := (Real.hasDerivAt_log (hpos t (mem_Ioi.mp ht).le).ne').comp t h1
    simpa [Function.comp_def, one_div] using h
  rw [hd.deriv]

/-- The **saturating ramp** `t ↦ t / (1 + t)` is a Bernstein function. It equals `1 - (1 + t)^{-1}`,
so on `(0, ∞)` its derivative is `(1 + t)^{-2}`, the square of the resolvent kernel and hence
completely monotone. -/
theorem isBernsteinFunction_id_div_one_add :
    IsBernsteinFunction (fun t : ℝ => t / (1 + t)) := by
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 < 1 + t := fun t ht => by linarith
  refine isBernsteinFunction_iff.mpr
    ⟨ContinuousOn.div (by fun_prop) (by fun_prop) fun t ht => (hpos t ht).ne',
    ContDiffOn.div (by fun_prop) (by fun_prop) fun t ht => (hpos t (mem_Ioi.mp ht).le).ne',
    fun t ht => div_nonneg ht (hpos t ht).le, ?_⟩
  -- The derivative on `(0, ∞)` is `t ↦ ((1 + t)²)⁻¹`, a square of the resolvent kernel.
  have hcm : IsCompletelyMonotoneOnIoi (fun t : ℝ => ((1 + t) ^ 2)⁻¹) := by
    have h2 := IsCompletelyMonotone.pow (isCompletelyMonotone_inv_const_add one_pos) 2
    have heq : (fun t : ℝ => ((1 + t) ^ 2)⁻¹) = (fun t : ℝ => (1 + t)⁻¹) ^ 2 := by
      funext t; rw [Pi.pow_apply, inv_pow]
    rw [heq]
    exact h2.isCompletelyMonotoneOnIoi
  refine hcm.congr fun t ht => ?_
  have htpos : 0 < 1 + t := hpos t (mem_Ioi.mp ht).le
  have hden : HasDerivAt (fun s : ℝ => 1 + s) 1 t := by simpa using (hasDerivAt_id t).const_add 1
  -- The quotient rule gives derivative `(1 · (1 + t) − t · 1) / (1 + t)² = ((1 + t)²)⁻¹`.
  have hd : HasDerivAt (fun s : ℝ => s / (1 + s)) (((1 + t) ^ 2)⁻¹) t := by
    have h : HasDerivAt (fun s : ℝ => s / (1 + s))
        ((1 * (1 + t) - t * 1) / (1 + t) ^ 2) t := (hasDerivAt_id t).div hden htpos.ne'
    rwa [show (1 * (1 + t) - t * 1) / (1 + t) ^ 2 = ((1 + t) ^ 2)⁻¹ by ring] at h
  exact hd.deriv

end TauCeti

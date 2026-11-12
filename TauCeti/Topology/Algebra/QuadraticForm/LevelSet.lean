/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Topology.Connected.PathConnected

/-!
# Paths in the level sets of a real quadratic form

A level set `{v | Q v = c}` of a real quadratic form with `c ≠ 0` need not be path-connected: for
`Q (x, y) = x² - y²` and `c = 1` it is a hyperbola whose two branches are exchanged by `v ↦ -v`.
This file shows that this sign is the only obstruction. If `Q a = Q b = c ≠ 0`, then
`Q ((1 - t) • b + t • a) / c = (1 - t)² + t² + t (1 - t) polar Q b a / c`, which is positive on
`[0, 1]` as soon as `polar Q b a` does not have the opposite sign to `c`. Rescaling the segment
from `b` to `a` back into the level set then joins `b` to `a` inside it. Otherwise the same
construction applies to `-a`, so every point of the level set is joined to `a` or to `-a`. A
vector of the level set orthogonal to `a` lies on both sides, and then `a` and `-a` are joined.

These paths are the input for the path-connectedness of the real Spin groups of indefinite
signature, whose elements are products of vectors in the level sets `Q = 1` and `Q = -1`.

## Main results

* `QuadraticMap.joinedIn_setOf_apply_eq_of_nonneg`: `b` is joined to `a` in the level set of `a`
  when `0 ≤ polar Q b a * Q a`.
* `QuadraticMap.joinedIn_setOf_apply_eq_or_joinedIn_neg`: every `b` in the level set of `a` is
  joined there to `a` or to `-a`.
* `QuadraticMap.joinedIn_setOf_apply_eq_neg_of_isOrtho`: `a` and `-a` are joined in their level
  set when it contains a vector orthogonal to `a`.
-/

public section

namespace QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousSMul ℝ V] (Q : QuadraticForm ℝ V)

/-- **The rescaled segment.** If `Q b = Q a ≠ 0` and `polar Q b a` does not have the opposite sign
to `Q a`, then the segment from `b` to `a`, rescaled back into the level set, joins `b` to `a`
inside the level set `{v | Q v = Q a}`. -/
theorem joinedIn_setOf_apply_eq_of_nonneg {a b : V} (hab : Q b = Q a) (ha : Q a ≠ 0)
    (h : 0 ≤ polar Q b a * Q a) : JoinedIn {v | Q v = Q a} b a := by
  -- `D t` is the ratio `Q ((1 - t) • b + t • a) / Q a`.
  set r := polar Q b a / Q a with hr
  have hr0 : 0 ≤ r := by
    rw [hr, ← mul_div_mul_right _ _ ha]
    exact div_nonneg h (mul_self_nonneg _)
  let D : ℝ → ℝ := fun t ↦ (1 - t) ^ 2 + t ^ 2 + (1 - t) * t * r
  have hD (t : unitInterval) : 0 < D t := by
    have h₁ : 0 ≤ (1 - (t : ℝ)) * t * r :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr t.2.2) t.2.1) hr0
    nlinarith [sq_nonneg (1 - 2 * (t : ℝ))]
  have hQD (t : ℝ) : Q ((1 - t) • b + t • a) = D t * Q a := by
    rw [QuadraticMap.map_add Q, polar_smul_left, polar_smul_right, QuadraticMap.map_smul,
      QuadraticMap.map_smul, hab]
    simp only [D, hr, smul_eq_mul]
    field_simp
  have hDc : Continuous fun t : unitInterval ↦ D t := by fun_prop
  let γ : Path b a :=
    { toFun t := (√(D t))⁻¹ • ((1 - (t : ℝ)) • b + (t : ℝ) • a)
      continuous_toFun :=
        (hDc.sqrt.inv₀ fun t ↦ (Real.sqrt_pos.mpr (hD t)).ne').smul (by fun_prop)
      source' := by simp [D]
      target' := by simp [D] }
  refine ⟨γ, fun t ↦ ?_⟩
  simp only [Set.mem_ofPred_eq, γ, Path.coe_mk_mk]
  rw [QuadraticMap.map_smul, hQD, smul_eq_mul, ← mul_inv, Real.mul_self_sqrt (hD t).le,
    ← mul_assoc, inv_mul_cancel₀ (hD t).ne', one_mul]

/-- **Every point of a level set is joined to `a` or to `-a`.** For `Q b = Q a ≠ 0`, the vector
`b` is joined inside the level set `{v | Q v = Q a}` to whichever of `a` and `-a` has polar product
with `b` of the sign of `Q a`. -/
theorem joinedIn_setOf_apply_eq_or_joinedIn_neg {a b : V} (hab : Q b = Q a) (ha : Q a ≠ 0) :
    JoinedIn {v | Q v = Q a} b a ∨ JoinedIn {v | Q v = Q a} b (-a) := by
  rcases le_total 0 (polar Q b a * Q a) with h | h
  · exact .inl (joinedIn_setOf_apply_eq_of_nonneg Q hab ha h)
  · right
    simpa only [QuadraticMap.map_neg] using joinedIn_setOf_apply_eq_of_nonneg Q (a := -a)
      (by rwa [QuadraticMap.map_neg]) (by rwa [QuadraticMap.map_neg])
      (by rwa [polar_neg_right, QuadraticMap.map_neg, neg_mul, neg_nonneg])

/-- **The antipode in a level set.** If the level set `{v | Q v = Q a}`, with `Q a ≠ 0`, contains
a vector orthogonal to `a`, then it joins `a` to `-a`. -/
theorem joinedIn_setOf_apply_eq_neg_of_isOrtho {a f : V} (hf : Q f = Q a) (ha : Q a ≠ 0)
    (haf : Q.IsOrtho a f) : JoinedIn {v | Q v = Q a} a (-a) := by
  have h₀ : polar Q f a = 0 := by rw [polar_comm, haf.polar_eq_zero]
  refine (joinedIn_setOf_apply_eq_of_nonneg Q hf ha (by rw [h₀, zero_mul])).symm.trans ?_
  simpa only [QuadraticMap.map_neg] using joinedIn_setOf_apply_eq_of_nonneg Q (a := -a)
    (by rwa [QuadraticMap.map_neg]) (by rwa [QuadraticMap.map_neg])
    (by rw [polar_neg_right, h₀, neg_zero, zero_mul])

end QuadraticMap

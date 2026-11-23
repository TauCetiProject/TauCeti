/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Analysis.Normed.Group.Defs

/-!
# Norm scaling under iterated scalar actions

If acting by `u` turns the weighted norm `‖e‖ * r` into `‖u • e‖ * s` for every `e`, then
acting by `u ^ n` turns `‖e‖ * r ^ n` into `‖u ^ n • e‖ * s ^ n`. Only a monoid action and a
real-valued norm are needed. With `s = 1` and `r = ‖u‖` this is the scaling law
`‖u ^ n • e‖ = ‖e‖ * ‖u‖ ^ n` for an element `u` by which acting scales every norm by `‖u‖`;
the weighted form also covers `s = 0`. For a family `u i` in a commutative monoid with weights
`s i` and `r i`, the monomial `uᵗ = ∏ᵢ u i ^ t i` scales weighted norms in the same way.

## Main results

* `TauCeti.norm_pow_smul_mul_pow`: `‖u ^ n • e‖ * s ^ n = ‖e‖ * r ^ n` whenever
  `‖u • e‖ * s = ‖e‖ * r` for every `e`.
* `TauCeti.norm_finsuppProd_pow_smul_mul_finsuppProd`: `‖uᵗ • e‖ * sᵗ = ‖e‖ * rᵗ` whenever
  `‖u i • e‖ * s i = ‖e‖ * r i` for every `i` and `e`.
-/

public section

namespace TauCeti

/-- If acting by `u` changes the weighted norm `‖e‖ * r` into `‖u • e‖ * s` for every `e`, then
acting by `u ^ n` changes `‖e‖ * r ^ n` into `‖u ^ n • e‖ * s ^ n`. -/
theorem norm_pow_smul_mul_pow {M E : Type*} [Monoid M] [MulAction M E] [Norm E] {u : M}
    {r s : ℝ} (hu : ∀ e : E, ‖u • e‖ * s = ‖e‖ * r) (n : ℕ) (e : E) :
    ‖u ^ n • e‖ * s ^ n = ‖e‖ * r ^ n := by
  induction n generalizing e with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', mul_smul]
    calc ‖u • u ^ n • e‖ * (s * s ^ n) = ‖u • u ^ n • e‖ * s * s ^ n := by ac_rfl
      _ = ‖u ^ n • e‖ * s ^ n * r := by rw [hu]; ac_rfl
      _ = ‖e‖ * (r * r ^ n) := by rw [ih]; ac_rfl

/-- If each `u i` scales norms by `r i / s i`, in the weighted form
`‖u i • e‖ * s i = ‖e‖ * r i`, then the monomial `uᵗ = ∏ᵢ u i ^ t i` scales the weighted norms:
`‖uᵗ • e‖ * sᵗ = ‖e‖ * rᵗ`. -/
theorem norm_finsuppProd_pow_smul_mul_finsuppProd {σ M E : Type*} [CommMonoid M] [MulAction M E]
    [Norm E] {r s : σ → ℝ} (u : σ → M) (hu : ∀ i (e : E), ‖u i • e‖ * s i = ‖e‖ * r i)
    (t : σ →₀ ℕ) (e : E) :
    ‖(t.prod fun i m ↦ u i ^ m) • e‖ * t.prod (s · ^ ·) = ‖e‖ * t.prod (r · ^ ·) := by
  classical
  simp only [Finsupp.prod]
  induction t.support using Finset.induction_on generalizing e with
  | empty => simp
  | insert i S hi ih =>
    simp only [Finset.prod_insert hi, mul_smul]
    calc ‖u i ^ t i • (∏ j ∈ S, u j ^ t j) • e‖ * (s i ^ t i * ∏ j ∈ S, s j ^ t j)
        = ‖u i ^ t i • (∏ j ∈ S, u j ^ t j) • e‖ * s i ^ t i * ∏ j ∈ S, s j ^ t j := by ac_rfl
      _ = ‖(∏ j ∈ S, u j ^ t j) • e‖ * (∏ j ∈ S, s j ^ t j) * r i ^ t i := by
          rw [norm_pow_smul_mul_pow (hu i)]; ac_rfl
      _ = ‖e‖ * (r i ^ t i * ∏ j ∈ S, r j ^ t j) := by rw [ih]; ac_rfl

end TauCeti

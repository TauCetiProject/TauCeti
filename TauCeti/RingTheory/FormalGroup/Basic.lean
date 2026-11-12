/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FormalGroup.Basic
-- Proof-only: the lowest-order effect of perturbing a substitution.
import TauCeti.RingTheory.MvPowerSeries.Order
-- Proof-only: the coefficients of `f(Y, X)`.
import TauCeti.RingTheory.MvPowerSeries.Substitution

/-!
# Coefficients of formal group laws

Mathlib states commutativity of a formal group law `F(X, Y)` as the identity `F(X, Y) = F(Y, X)`
of power series. This file records its coefficientwise form: the coefficient of `XⁱYʲ` in `F`
equals that of `XʲYⁱ`. It also records the lowest-order effect of perturbing an argument of a
formal group law: since `F(X, Y) = X + Y + ⋯`, perturbing `x` or `y` by a series `e` of order at
least `n ≥ 1` adds `e` to `F(x, y)`, up to terms of degree greater than `n`.

## Main results

* `FormalGroup.coeff_comm`: the coefficients of a commutative formal group law are symmetric.
* `FormalGroup.le_order_subst_add_left_sub`, `FormalGroup.le_order_subst_add_right_sub`:
  `F(x + e, y) ≡ F(x, y) + e` and `F(x, y + e) ≡ F(x, y) + e` modulo terms of degree greater than
  `n`, for `e` of order at least `n ≥ 1`.
-/

public section

open MvPowerSeries Finsupp

variable {A : Type*} [CommRing A]

namespace FormalGroup

/-- The coefficients of a commutative formal group law are symmetric: the coefficient of `XⁱYʲ`
equals that of `XʲYⁱ`. -/
theorem coeff_comm (F : FormalGroup A) [F.IsComm] (i j : ℕ) :
    coeff (single 0 i + single 1 j) F.toPowerSeries =
      coeff (single 0 j + single 1 i) F.toPowerSeries := by
  conv_lhs => rw [IsComm.comm (F := F)]
  simp [coeff_subst_X_one_X_zero]

section Perturbation

variable (F : FormalGroup A) {σ : Type*} {x y e : MvPowerSeries σ A}

/-- Perturbing the `i`-th argument of `F` by a series `e` of order at least `n ≥ 1` adds `e` to
`F(x, y)`, up to terms of degree greater than `n`. -/
private theorem le_order_subst_update_add_sub (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) (i : Fin 2) {n : ℕ} (hn : n ≠ 0) (he : n ≤ e.order) :
    ((n + 1 : ℕ) : ℕ∞) ≤ (F.toPowerSeries.subst (Function.update ![x, y] i (![x, y] i + e)) -
      F.toPowerSeries.subst ![x, y] - e).order := by
  have hxy₀ : ∀ j, constantCoeff (![x, y] j) = 0 := fun j ↦ by fin_cases j <;> simp [hx, hy]
  have h := MvPowerSeries.le_order_subst_update_add_sub F.toPowerSeries
    (hasSubst_of_constantCoeff_zero hxy₀) hxy₀ i hn he
  have hi : coeff (single i 1) F.toPowerSeries = 1 := by
    fin_cases i
    exacts [F.lin_coeff_X, F.lin_coeff_Y]
  rwa [hi, map_one, one_smul] at h

/-- Perturbing the first argument of `F` by a series `e` of order at least `n ≥ 1` adds `e` to
`F(x, y)`, up to terms of degree greater than `n`. -/
theorem le_order_subst_add_left_sub (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    {n : ℕ} (hn : n ≠ 0) (he : n ≤ e.order) :
    ((n + 1 : ℕ) : ℕ∞) ≤
      (F.toPowerSeries.subst ![x + e, y] - F.toPowerSeries.subst ![x, y] - e).order := by
  convert F.le_order_subst_update_add_sub hx hy 0 hn he using 5
  funext j
  fin_cases j <;> simp

/-- Perturbing the second argument of `F` by a series `e` of order at least `n ≥ 1` adds `e` to
`F(x, y)`, up to terms of degree greater than `n`. -/
theorem le_order_subst_add_right_sub (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    {n : ℕ} (hn : n ≠ 0) (he : n ≤ e.order) :
    ((n + 1 : ℕ) : ℕ∞) ≤
      (F.toPowerSeries.subst ![x, y + e] - F.toPowerSeries.subst ![x, y] - e).order := by
  convert F.le_order_subst_update_add_sub hx hy 1 hn he using 5
  funext j
  fin_cases j <;> simp

end Perturbation

end FormalGroup

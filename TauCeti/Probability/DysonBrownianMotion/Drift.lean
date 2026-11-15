/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Monovary
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# The drift of the Dyson system

The Dyson system of size `n` is the system of stochastic differential equations
`dλᵢ = √(2/(βn)) dBᵢ + n⁻¹ ∑_{j ≠ i} (λᵢ - λⱼ)⁻¹ dt` for `i = 1, …, n`. This file defines its
drift `TauCeti.Probability.dysonDrift n x i = n⁻¹ ∑_{j ≠ i} (xᵢ - xⱼ)⁻¹` and proves the two
deterministic properties of the drift that the theory of the system rests on.

* The drift is continuous at every point with pairwise distinct coordinates, so along a path
  that stays in the open chamber `{x₁ > ⋯ > xₙ}` it is a continuous function of time.
* The drift is monotone (dissipative) on the open chamber: for `x` and `y` with pairwise distinct
  coordinates, with `aᵢⱼ = xᵢ - xⱼ` and `bᵢⱼ = yᵢ - yⱼ`,
  `∑ᵢ (Fᵢ(x) - Fᵢ(y)) (xᵢ - yᵢ) = -(2n)⁻¹ ∑_{i,j} (aᵢⱼ - bᵢⱼ)² / (aᵢⱼ bᵢⱼ)`, and the right side
  is nonpositive when `x` and `y` are ordered in the same way. Since the noise of the Dyson
  system is additive, this inequality gives pathwise uniqueness of its solutions.

## Main declarations

* `TauCeti.Probability.dysonDrift`: the drift of the Dyson system.
* `TauCeti.Probability.continuousAt_dysonDrift`: continuity off the collision set.
* `TauCeti.Probability.sum_dysonDrift_sub_mul_sub`: the monotonicity identity.
* `TauCeti.Probability.sum_dysonDrift_sub_mul_sub_nonpos`: the monotonicity inequality.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §4.3.1, Lemma 4.3.3 and Proposition 4.3.5.
-/

public section

open Finset

namespace TauCeti.Probability

variable {n : ℕ}

/-- The drift of the Dyson system of size `n` at `x : Fin n → ℝ` in the coordinate `i`:
`n⁻¹ ∑_{j ≠ i} (xᵢ - xⱼ)⁻¹`. It is the physically meaningful drift on the open chamber, where
the coordinates of `x` are pairwise distinct. -/
noncomputable def dysonDrift (n : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j ∈ univ.erase i, (x i - x j)⁻¹

/-- The defining formula of the Dyson drift. -/
theorem dysonDrift_def (x : Fin n → ℝ) (i : Fin n) :
    dysonDrift n x i = (n : ℝ)⁻¹ * ∑ j ∈ univ.erase i, (x i - x j)⁻¹ :=
  (rfl)

/-- The term `j = i` contributes `(xᵢ - xᵢ)⁻¹ = 0` to the drift, so the sum may run over all `j`. -/
theorem dysonDrift_eq_sum (x : Fin n → ℝ) (i : Fin n) :
    dysonDrift n x i = (n : ℝ)⁻¹ * ∑ j, (x i - x j)⁻¹ := by
  rw [dysonDrift, sum_erase _ (by simp)]

/-- In size `1` the Dyson system has no drift. -/
@[simp]
theorem dysonDrift_one (x : Fin 1 → ℝ) (i : Fin 1) : dysonDrift 1 x i = 0 := by
  obtain rfl := Subsingleton.elim i 0
  simp [dysonDrift]

/-- The drift is continuous at every point whose coordinates are pairwise distinct. -/
theorem continuousAt_dysonDrift {x : Fin n → ℝ} (hx : Function.Injective x) (i : Fin n) :
    ContinuousAt (fun y : Fin n → ℝ ↦ dysonDrift n y i) x := by
  refine continuousAt_const.mul (tendsto_finsetSum _ fun j hj ↦ ?_)
  exact ((continuous_apply i).sub (continuous_apply j)).continuousAt.inv₀
    (sub_ne_zero.2 (hx.ne (ne_of_mem_erase hj).symm))

/-- **Monotonicity identity for the Dyson drift.** For `x` and `y` with pairwise distinct
coordinates, writing `aᵢⱼ = xᵢ - xⱼ` and `bᵢⱼ = yᵢ - yⱼ`,
`∑ᵢ (Fᵢ(x) - Fᵢ(y)) (xᵢ - yᵢ) = -(2n)⁻¹ ∑_{i,j} (aᵢⱼ - bᵢⱼ)² / (aᵢⱼ bᵢⱼ)`, where the diagonal
terms of the double sum vanish. Each unordered pair `{i, j}` thus contributes
`-n⁻¹ (aᵢⱼ - bᵢⱼ)² / (aᵢⱼ bᵢⱼ)`. -/
theorem sum_dysonDrift_sub_mul_sub {x y : Fin n → ℝ} (hx : Function.Injective x)
    (hy : Function.Injective y) :
    ∑ i, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) =
      -(2 * n : ℝ)⁻¹ *
        ∑ i, ∑ j, ((x i - x j) - (y i - y j)) ^ 2 / ((x i - x j) * (y i - y j)) := by
  set f : Fin n → Fin n → ℝ := fun i j ↦ ((x i - x j)⁻¹ - (y i - y j)⁻¹) * (x i - y i)
  -- Symmetrising the pair `(i, j) ↔ (j, i)` produces the summand of the right side.
  have hpair : ∀ i j, f i j + f j i =
      -(((x i - x j) - (y i - y j)) ^ 2 / ((x i - x j) * (y i - y j))) := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · simp [f]
    have ha : x i - x j ≠ 0 := sub_ne_zero.2 (hx.ne hij)
    have hb : y i - y j ≠ 0 := sub_ne_zero.2 (hy.ne hij)
    have ha' : x j - x i ≠ 0 := sub_ne_zero.2 (hx.ne hij.symm)
    have hb' : y j - y i ≠ 0 := sub_ne_zero.2 (hy.ne hij.symm)
    simp only [f]
    field_simp
    ring
  have hsum : ∑ i, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) =
      (n : ℝ)⁻¹ * ∑ i, ∑ j, f i j := by
    simp only [dysonDrift_eq_sum, ← mul_sub, ← sum_sub_distrib, mul_sum, sum_mul, f, mul_assoc]
  have hswap : 2 * ∑ i, ∑ j, f i j =
      -∑ i, ∑ j, ((x i - x j) - (y i - y j)) ^ 2 / ((x i - x j) * (y i - y j)) := by
    have hc : ∑ i, ∑ j, f i j = ∑ i, ∑ j, f j i := sum_comm
    calc 2 * ∑ i, ∑ j, f i j = ∑ i, ∑ j, f i j + ∑ i, ∑ j, f j i := by rw [two_mul, ← hc]
      _ = _ := by simp only [← sum_add_distrib, hpair, sum_neg_distrib]
  rw [hsum]
  linear_combination (n : ℝ)⁻¹ * (1 / 2 : ℝ) * hswap

/-- **Monotonicity of the Dyson drift.** If `x` and `y` have pairwise distinct coordinates and
are ordered in the same way, then `∑ᵢ (Fᵢ(x) - Fᵢ(y)) (xᵢ - yᵢ) ≤ 0`. This applies to any two
points of the open chamber `{x₁ > ⋯ > xₙ}`. -/
theorem sum_dysonDrift_sub_mul_sub_nonpos {x y : Fin n → ℝ} (hx : Function.Injective x)
    (hy : Function.Injective y) (hxy : Monovary x y) :
    ∑ i, (dysonDrift n x i - dysonDrift n y i) * (x i - y i) ≤ 0 := by
  rw [sum_dysonDrift_sub_mul_sub hx hy, neg_mul]
  refine neg_nonpos.2 (mul_nonneg (by positivity) (sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ ?_))
  exact div_nonneg (sq_nonneg _) (monovary_iff_forall_mul_nonneg.1 hxy j i)

end TauCeti.Probability

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.MetricSpace.Bounded

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The ordered cone and ordered projective simplex

For `n = d + 2 ≥ 2`, the **ordered cone** `H_n` (`TauCeti.orderedCone d`) consists of the nonzero
tuples `y = (y₁, …, y_n) ∈ ℝ^n` with `0 ≤ y₁ ≤ ⋯ ≤ y_n` and `y₁ + ⋯ + y_{n-1} = y_n`. Its linear
span is the hyperplane `{y | y₁ + ⋯ + y_{n-1} = y_n}` (`TauCeti.OrderedSimplex.coneSpan d`), with
basis `e_j + e_n` for `1 ≤ j ≤ n - 1` (`TauCeti.OrderedSimplex.coneSpanBasis d`).

Every `y ∈ H_n` has positive last coordinate `y_n > 0`. Dividing by `y_n` projects `H_n` onto the
ordered simplex `Δ_n = {0 ≤ w₁ ≤ ⋯ ≤ w_{n-1}, ∑ w_i = 1}`, which we chart in full dimension `d` by
its first `d` coordinates `x_i = w_{i+1}` with `w_{d+1} = 1 - ∑ k, x k`. This chart image is
`TauCeti.orderedSimplex d`. In chart coordinates, `orderedSimplex d` is a nonempty compact convex
body with nonempty interior (witnessed by `w_i = 2i / (n (n - 1))`), so within-derivatives on it
are unique (`TauCeti.uniqueDiffOn_orderedSimplex`).

## Main definitions

* `TauCeti.orderedSimplex d`: the chart image of `Δ_{d+2}` in `Fin d → ℝ`.
* `TauCeti.orderedCone d`: the homogeneous ordered cone `H_{d+2}` in `Fin (d + 2) → ℝ`.
* `TauCeti.OrderedSimplex.toProjective`: appends the last projective coordinate `1 - ∑ x`.
* `TauCeti.OrderedSimplex.toHomogeneous`: lifts a chart point `x` to
  `(w₁, …, w_{d+1}, 1) ∈ H_{d+2}`.
* `TauCeti.OrderedSimplex.normalizeCone`: projects `y ∈ H_{d+2}` to chart coordinates `y_i / y_n`.
* `TauCeti.OrderedSimplex.coneSpan` and `TauCeti.OrderedSimplex.coneSpanBasis`: the linear span of
  `H_{d+2}` and its basis `e_j + e_n`.

## References

* A. Gamburd, M. Magee and R. Ronan, *An asymptotic formula for integer points on Markoff–Hurwitz
  varieties*, Ann. of Math. (2) 190 (2019), no. 3, 751–809, (1.5), §4.1 and §5.1.
-/

public section

noncomputable section

open Finset Metric Set Topology

namespace TauCeti

/-! ### The ordered projective simplex -/

/-- The ordered projective simplex `Δ_{d+2}` in chart coordinates: `x i = w_{i+1}` for `i < d`
and `w_{d+1} = 1 - ∑ k, x k`, satisfying `0 ≤ w₁ ≤ ⋯ ≤ w_d ≤ w_{d+1}`. -/
def orderedSimplex (d : ℕ) : Set (Fin d → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ Monotone x ∧ ∀ i, x i ≤ 1 - ∑ k, x k}

/-- Membership in `orderedSimplex d` unfolds to nonnegativity, monotonicity, and domination by
the remaining mass `1 - ∑ k, x k`. -/
theorem mem_orderedSimplex_iff {d : ℕ} {x : Fin d → ℝ} :
    x ∈ orderedSimplex d ↔ (∀ i, 0 ≤ x i) ∧ Monotone x ∧ ∀ i, x i ≤ 1 - ∑ k, x k :=
  (Iff.rfl)

theorem coord_nonneg_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) (i : Fin d) : 0 ≤ x i :=
  hx.1 i

theorem monotone_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : Monotone x :=
  hx.2.1

theorem coord_le_one_sub_sum_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) (i : Fin d) : x i ≤ 1 - ∑ k, x k :=
  hx.2.2 i

/-- The sum of the chart coordinates on `orderedSimplex d` is at most `1`. -/
theorem sum_le_one_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : ∑ k, x k ≤ 1 := by
  cases d with
  | zero => simp
  | succ d =>
    have h0 := hx.1 0
    have h1 := hx.2.2 0
    linarith

/-- The last projective coordinate `1 - ∑ k, x k` is nonnegative on `orderedSimplex d`. -/
theorem one_sub_sum_nonneg_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : 0 ≤ 1 - ∑ k, x k :=
  sub_nonneg.2 (sum_le_one_of_mem_orderedSimplex hx)

/-- The last projective coordinate `1 - ∑ k, x k` is at most `1` on `orderedSimplex d`. -/
theorem one_sub_sum_le_one_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : 1 - ∑ k, x k ≤ 1 := by
  linarith [Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => hx.1 k]

/-- Every chart coordinate on `orderedSimplex d` satisfies `x i ≤ 1 / 2`. -/
theorem coord_le_half_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) (i : Fin d) : x i ≤ 1 / 2 := by
  have hle : x i ≤ ∑ k, x k :=
    Finset.single_le_sum (fun k _ => hx.1 k) (Finset.mem_univ i)
  have hlast := hx.2.2 i
  linarith

/-- The last projective coordinate `w_{d+1} = 1 - ∑ k, x k` is at least `1 / (d + 1)`. -/
theorem inv_le_one_sub_sum_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : ((d : ℝ) + 1)⁻¹ ≤ 1 - ∑ k, x k := by
  have hsum : ∑ k, x k ≤ (d : ℝ) * (1 - ∑ k, x k) := by
    calc ∑ k, x k ≤ ∑ _k : Fin d, (1 - ∑ j, x j) := Finset.sum_le_sum fun k _ => hx.2.2 k
      _ = (d : ℝ) * (1 - ∑ j, x j) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  linarith

/-- The ordered simplex lies inside the closed ball of radius `1 / 2` around `0`. -/
theorem orderedSimplex_subset_closedBall (d : ℕ) :
    orderedSimplex d ⊆ closedBall (0 : Fin d → ℝ) (1 / 2) := by
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_of_nonneg (hx.1 i)]
  exact coord_le_half_of_mem_orderedSimplex hx i

/-- The ordered simplex is closed in `Fin d → ℝ`. -/
theorem isClosed_orderedSimplex (d : ℕ) : IsClosed (orderedSimplex d) := by
  have h1 : IsClosed {x : Fin d → ℝ | ∀ i, 0 ≤ x i} := by
    simpa [Set.ofPred_forall] using isClosed_iInter fun i : Fin d =>
      isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {x : Fin d → ℝ | Monotone x} := by
    have heq : {x : Fin d → ℝ | Monotone x} =
        ⋂ (i : Fin d) (j : Fin d) (_ : i ≤ j), {x | x i ≤ x j} := by
      ext x; simp [Monotone]
    rw [heq]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply i) (continuous_apply j)
  have h3 : IsClosed {x : Fin d → ℝ | ∀ i, x i ≤ 1 - ∑ k, x k} := by
    simpa [Set.ofPred_forall] using isClosed_iInter fun i : Fin d =>
      isClosed_le (continuous_apply i) (by fun_prop)
  exact h1.inter (h2.inter h3)

/-- The ordered simplex is bounded in `Fin d → ℝ`. -/
theorem isBounded_orderedSimplex (d : ℕ) : Bornology.IsBounded (orderedSimplex d) :=
  isBounded_closedBall.subset (orderedSimplex_subset_closedBall d)

/-- The ordered simplex is compact. -/
theorem isCompact_orderedSimplex (d : ℕ) : IsCompact (orderedSimplex d) :=
  isCompact_of_isClosed_isBounded (isClosed_orderedSimplex d) (isBounded_orderedSimplex d)

/-- The ordered simplex is convex. -/
theorem convex_orderedSimplex (d : ℕ) : Convex ℝ (orderedSimplex d) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hx.2.1 hij) ha)
      (mul_le_mul_of_nonneg_left (hy.2.1 hij) hb)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hx' := mul_le_mul_of_nonneg_left (hx.2.2 i) ha
    have hy' := mul_le_mul_of_nonneg_left (hy.2.2 i) hb
    nlinarith

namespace OrderedSimplex

/-- The canonical interior point `w_i = 2 i / ((d + 2) (d + 1))` (`1 ≤ i ≤ d`) of
`orderedSimplex d`. Its coordinates are strictly positive and strictly increasing, with remaining
mass `2 / (d + 2)`. -/
def interiorPoint (d : ℕ) : Fin d → ℝ :=
  fun i => 2 * ((i : ℝ) + 1) / (((d : ℝ) + 2) * ((d : ℝ) + 1))

theorem interiorPoint_def (d : ℕ) (i : Fin d) :
    interiorPoint d i = 2 * ((i : ℝ) + 1) / (((d : ℝ) + 2) * ((d : ℝ) + 1)) :=
  (rfl)

/-- The sum of the coordinates of `interiorPoint d` is `d / (d + 2)`. -/
theorem sum_interiorPoint (d : ℕ) :
    ∑ i : Fin d, interiorPoint d i = (d : ℝ) / ((d : ℝ) + 2) := by
  have hsum : ∑ i : Fin d, (2 * ((i : ℝ) + 1)) = (d : ℝ) * ((d : ℝ) + 1) := by
    induction d with
    | zero => simp
    | succ k ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
      rw [ih]
      ring
  simp only [interiorPoint, ← Finset.sum_div, hsum]
  have h1 : (d : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- The remaining mass at `interiorPoint d` is `2 / (d + 2)`. -/
theorem one_sub_sum_interiorPoint (d : ℕ) :
    1 - ∑ i : Fin d, interiorPoint d i = 2 / ((d : ℝ) + 2) := by
  rw [sum_interiorPoint]
  have h2 : (d : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The canonical interior point lies in `interior (orderedSimplex d)`. -/
theorem interiorPoint_mem_interior (d : ℕ) :
    interiorPoint d ∈ interior (orderedSimplex d) := by
  let U : Set (Fin d → ℝ) :=
    {x | (∀ i, 0 < x i) ∧ StrictMono x ∧ ∀ i, x i < 1 - ∑ k, x k}
  have hU_open : IsOpen U := by
    have h1 : IsOpen {x : Fin d → ℝ | ∀ i, 0 < x i} := by
      simpa [Set.ofPred_forall] using isOpen_iInter_of_finite fun i : Fin d =>
        isOpen_lt continuous_const (continuous_apply i)
    have h2 : IsOpen {x : Fin d → ℝ | StrictMono x} := by
      have heq : {x : Fin d → ℝ | StrictMono x} =
          ⋂ (i : Fin d) (j : Fin d) (_ : i < j), {x | x i < x j} := by
        ext x; simp [StrictMono]
      rw [heq]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        isOpen_iInter_of_finite fun _ => isOpen_lt (continuous_apply i) (continuous_apply j)
    have h3 : IsOpen {x : Fin d → ℝ | ∀ i, x i < 1 - ∑ k, x k} := by
      simpa [Set.ofPred_forall] using isOpen_iInter_of_finite fun i : Fin d =>
        isOpen_lt (continuous_apply i) (by fun_prop)
    exact h1.inter (h2.inter h3)
  have hU_sub : U ⊆ orderedSimplex d := fun x hx =>
    ⟨fun i => (hx.1 i).le, hx.2.1.monotone, fun i => (hx.2.2 i).le⟩
  refine mem_interior.2 ⟨U, hU_sub, hU_open, ?_, ?_, ?_⟩
  · intro i
    dsimp only [interiorPoint]
    positivity
  · intro i j hij
    dsimp only [interiorPoint]
    have hlt : (i : ℝ) < (j : ℝ) := Nat.cast_lt.2 hij
    gcongr
  · intro i
    rw [one_sub_sum_interiorPoint]
    dsimp only [interiorPoint]
    have hden : (0 : ℝ) < ((d : ℝ) + 2) * ((d : ℝ) + 1) := by positivity
    have hlt : (i : ℝ) + 1 < (d : ℝ) + 1 := by
      have : (i : ℝ) < (d : ℝ) := Nat.cast_lt.2 i.isLt
      linarith
    rw [div_lt_div_iff₀ hden (by positivity)]
    nlinarith

/-- The canonical interior point lies in `orderedSimplex d`. -/
theorem interiorPoint_mem (d : ℕ) : interiorPoint d ∈ orderedSimplex d :=
  interior_subset (interiorPoint_mem_interior d)

end OrderedSimplex

/-- The ordered simplex has nonempty interior in `Fin d → ℝ`. -/
theorem nonempty_interior_orderedSimplex (d : ℕ) : (interior (orderedSimplex d)).Nonempty :=
  ⟨OrderedSimplex.interiorPoint d, OrderedSimplex.interiorPoint_mem_interior d⟩

/-- The ordered simplex is nonempty. -/
theorem nonempty_orderedSimplex (d : ℕ) : (orderedSimplex d).Nonempty :=
  ⟨OrderedSimplex.interiorPoint d, OrderedSimplex.interiorPoint_mem d⟩

/-- Within-derivatives on `orderedSimplex d` are unique. -/
theorem uniqueDiffOn_orderedSimplex (d : ℕ) : UniqueDiffOn ℝ (orderedSimplex d) :=
  uniqueDiffOn_convex (convex_orderedSimplex d) (nonempty_interior_orderedSimplex d)

/-! ### The homogeneous ordered cone and ray normalisation -/

/-- The homogeneous ordered cone `H_{d+2}` of nonzero tuples `y : Fin (d + 2) → ℝ` with
`0 ≤ y₀ ≤ ⋯ ≤ y_{d+1}` and `∑ i : Fin (d + 1), y i.castSucc = y (Fin.last (d + 1))`. -/
def orderedCone (d : ℕ) : Set (Fin (d + 2) → ℝ) :=
  {y | y ≠ 0 ∧ (∀ i, 0 ≤ y i) ∧ Monotone y ∧
    ∑ i : Fin (d + 1), y i.castSucc = y (Fin.last (d + 1))}

/-- Membership in `orderedCone d`. -/
theorem mem_orderedCone_iff {d : ℕ} {y : Fin (d + 2) → ℝ} :
    y ∈ orderedCone d ↔ y ≠ 0 ∧ (∀ i, 0 ≤ y i) ∧ Monotone y ∧
      ∑ i : Fin (d + 1), y i.castSucc = y (Fin.last (d + 1)) :=
  (Iff.rfl)

/-- The zero vector does not belong to `orderedCone d`. -/
@[simp]
theorem zero_not_mem_orderedCone (d : ℕ) : (0 : Fin (d + 2) → ℝ) ∉ orderedCone d :=
  fun h => h.1 rfl

/-- Every vector in `orderedCone d` has strictly positive last coordinate. -/
theorem last_pos_of_mem_orderedCone {d : ℕ} {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) : 0 < y (Fin.last (d + 1)) := by
  refine lt_of_le_of_ne (hy.2.1 (Fin.last (d + 1))) ?_
  intro h0
  apply hy.1
  ext i
  exact le_antisymm ((hy.2.2.1 (Fin.le_last i)).trans_eq h0.symm) (hy.2.1 i)

/-- The ordered cone is closed under positive scalar multiplication. -/
theorem smul_mem_orderedCone {d : ℕ} {y : Fin (d + 2) → ℝ} {c : ℝ}
    (hy : y ∈ orderedCone d) (hc : 0 < c) : c • y ∈ orderedCone d := by
  refine ⟨smul_ne_zero hc.ne' hy.1, fun i => mul_nonneg hc.le (hy.2.1 i),
    fun i j hij => mul_le_mul_of_nonneg_left (hy.2.2.1 hij) hc.le, ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hy.2.2.2]

namespace OrderedSimplex

/-- Full projective coordinates `(w₁, …, w_{d+1}) = (x₀, …, x_{d-1}, 1 - ∑ k, x k)`. -/
def toProjective {d : ℕ} (x : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) x (1 - ∑ k, x k)

@[simp]
theorem toProjective_castSucc {d : ℕ} (x : Fin d → ℝ) (i : Fin d) :
    toProjective x i.castSucc = x i := by
  simp [toProjective]

@[simp]
theorem toProjective_last {d : ℕ} (x : Fin d → ℝ) :
    toProjective x (Fin.last d) = 1 - ∑ k, x k := by
  simp [toProjective]

/-- The projective coordinates sum to `1`. -/
@[simp]
theorem sum_toProjective {d : ℕ} (x : Fin d → ℝ) :
    ∑ i : Fin (d + 1), toProjective x i = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp

/-- The projective coordinates of a point in `orderedSimplex d` are nonnegative. -/
theorem toProjective_nonneg {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d)
    (i : Fin (d + 1)) : 0 ≤ toProjective x i := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [toProjective_last]
    exact one_sub_sum_nonneg_of_mem_orderedSimplex hx
  · rw [toProjective_castSucc]
    exact hx.1 k

/-- The projective coordinates of a point in `orderedSimplex d` are at most `1`. -/
theorem toProjective_le_one {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d)
    (i : Fin (d + 1)) : toProjective x i ≤ 1 := by
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [toProjective_last]
    exact one_sub_sum_le_one_of_mem_orderedSimplex hx
  · rw [toProjective_castSucc]
    linarith [coord_le_half_of_mem_orderedSimplex hx k]

/-- The projective coordinates of a point in `orderedSimplex d` are nondecreasing. -/
theorem monotone_toProjective {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Monotone (toProjective x) := by
  intro i j
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · refine Fin.lastCases (fun _ => le_refl _) (fun i' _ => ?_) i
    rw [toProjective_castSucc, toProjective_last]
    exact hx.2.2 i'
  · refine Fin.lastCases (fun hij => ?_) (fun i' hij => ?_) i
    · exact absurd hij (not_le.2 (Fin.castSucc_lt_last j'))
    · rw [toProjective_castSucc, toProjective_castSucc]
      exact hx.2.1 (Fin.castSucc_le_castSucc_iff.1 hij)

/-- The homogeneous lift `(w₁, …, w_{d+1}, 1) ∈ ℝ^{d+2}` of a chart point `x`. -/
def toHomogeneous {d : ℕ} (x : Fin d → ℝ) : Fin (d + 2) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) (toProjective x) 1

@[simp]
theorem toHomogeneous_castSucc {d : ℕ} (x : Fin d → ℝ) (i : Fin (d + 1)) :
    toHomogeneous x i.castSucc = toProjective x i := by
  simp [toHomogeneous]

@[simp]
theorem toHomogeneous_last {d : ℕ} (x : Fin d → ℝ) :
    toHomogeneous x (Fin.last (d + 1)) = 1 := by
  simp [toHomogeneous]

/-- The homogeneous lift of a point in `orderedSimplex d` lies in `orderedCone d`. -/
theorem toHomogeneous_mem_orderedCone {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    toHomogeneous x ∈ orderedCone d := by
  refine ⟨fun h => (one_ne_zero : (1 : ℝ) ≠ 0) (by simpa using congrFun h (Fin.last (d + 1))),
    ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases (by simp) (fun k => ?_) i
    rw [toHomogeneous_castSucc]
    exact toProjective_nonneg hx k
  · intro i j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · refine Fin.lastCases (fun _ => le_refl _) (fun i' _ => ?_) i
      rw [toHomogeneous_castSucc, toHomogeneous_last]
      exact toProjective_le_one hx i'
    · refine Fin.lastCases (fun hij => ?_) (fun i' hij => ?_) i
      · exact absurd hij (not_le.2 (Fin.castSucc_lt_last j'))
      · rw [toHomogeneous_castSucc, toHomogeneous_castSucc]
        exact monotone_toProjective hx (Fin.castSucc_le_castSucc_iff.1 hij)
  · simp

/-- The hyperplane `{y : Fin (d + 2) → ℝ | ∑ i : Fin (d + 1), y i.castSucc = y (Fin.last (d + 1))}`
spanned by `orderedCone d`. -/
def coneSpan (d : ℕ) : Submodule ℝ (Fin (d + 2) → ℝ) where
  carrier := {y | ∑ i : Fin (d + 1), y i.castSucc = y (Fin.last (d + 1))}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at hx hy ⊢
    linarith
  zero_mem' := by simp
  smul_mem' c {x} hx := by
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hx ⊢
    rw [hx]

/-- Membership in `coneSpan d`. -/
@[simp]
theorem mem_coneSpan_iff {d : ℕ} {y : Fin (d + 2) → ℝ} :
    y ∈ coneSpan d ↔ ∑ i : Fin (d + 1), y i.castSucc = y (Fin.last (d + 1)) :=
  (Iff.rfl)

/-- Every point of `orderedCone d` lies in `coneSpan d`. -/
theorem orderedCone_subset_coneSpan (d : ℕ) :
    orderedCone d ⊆ (coneSpan d : Set (Fin (d + 2) → ℝ)) :=
  fun _ hy => hy.2.2.2

/-- Normalise a vector `y : Fin (d + 2) → ℝ` by its last coordinate to obtain the full
projective coordinates `(y₁ / y_n, …, y_{n-1} / y_n)`. -/
def normalizeProjective {d : ℕ} (y : Fin (d + 2) → ℝ) : Fin (d + 1) → ℝ :=
  fun i => y i.castSucc / y (Fin.last (d + 1))

theorem normalizeProjective_def {d : ℕ} (y : Fin (d + 2) → ℝ) (i : Fin (d + 1)) :
    normalizeProjective y i = y i.castSucc / y (Fin.last (d + 1)) :=
  (rfl)

/-- Full projective normalisation is invariant under nonzero scaling. -/
theorem normalizeProjective_smul {d : ℕ} {c : ℝ} (hc : c ≠ 0) (y : Fin (d + 2) → ℝ) :
    normalizeProjective (c • y) = normalizeProjective y := by
  ext i
  simp only [normalizeProjective, Pi.smul_apply, smul_eq_mul, mul_div_mul_left _ _ hc]

/-- Normalise a vector `y : Fin (d + 2) → ℝ` by its last coordinate to obtain chart coordinates
`(y₁ / y_n, …, y_d / y_n)`. -/
def normalizeCone {d : ℕ} (y : Fin (d + 2) → ℝ) : Fin d → ℝ :=
  fun i => y i.castSucc.castSucc / y (Fin.last (d + 1))

theorem normalizeCone_def {d : ℕ} (y : Fin (d + 2) → ℝ) (i : Fin d) :
    normalizeCone y i = y i.castSucc.castSucc / y (Fin.last (d + 1)) :=
  (rfl)

/-- Normalisation is invariant under nonzero scaling. -/
theorem normalizeCone_smul {d : ℕ} {c : ℝ} (hc : c ≠ 0) (y : Fin (d + 2) → ℝ) :
    normalizeCone (c • y) = normalizeCone y := by
  ext i
  simp only [normalizeCone, Pi.smul_apply, smul_eq_mul, mul_div_mul_left _ _ hc]

/-- Normalising the homogeneous lift recovers the original chart point. -/
@[simp]
theorem normalizeCone_toHomogeneous {d : ℕ} (x : Fin d → ℝ) :
    normalizeCone (toHomogeneous x) = x := by
  ext i
  simp [normalizeCone]

/-- On `coneSpan d` with nonzero last coordinate, the chart normalisation recovers the full
projective normalisation. -/
theorem toProjective_normalizeCone {d : ℕ} {y : Fin (d + 2) → ℝ}
    (hy : y ∈ coneSpan d) (hne : y (Fin.last (d + 1)) ≠ 0) :
    toProjective (normalizeCone y) = normalizeProjective y := by
  ext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [toProjective_last, normalizeProjective]
    have hsum : ∑ k : Fin d, y k.castSucc.castSucc =
        y (Fin.last (d + 1)) - y (Fin.last d).castSucc := by
      have hspan := mem_coneSpan_iff.1 hy
      rw [Fin.sum_univ_castSucc] at hspan
      linarith
    simp only [normalizeCone, ← Finset.sum_div, hsum]
    rw [eq_div_iff hne, sub_mul, one_mul, div_mul_cancel₀ _ hne]
    ring
  · simp [normalizeCone, normalizeProjective]

/-- Normalising a point of `orderedCone d` lands in `orderedSimplex d`. -/
theorem normalizeCone_mem_orderedSimplex {d : ℕ} {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) : normalizeCone y ∈ orderedSimplex d := by
  have hpos := last_pos_of_mem_orderedCone hy
  refine ⟨fun i => div_nonneg (hy.2.1 _) hpos.le,
    fun i j hij => div_le_div_of_nonneg_right
      (hy.2.2.1 (Fin.castSucc_le_castSucc_iff.2 (Fin.castSucc_le_castSucc_iff.2 hij))) hpos.le,
    fun i => ?_⟩
  have hlast : 1 - ∑ k, normalizeCone y k =
      y (Fin.last d).castSucc / y (Fin.last (d + 1)) := by
    have := congrFun (toProjective_normalizeCone hy.2.2.2 hpos.ne') (Fin.last d)
    simpa [normalizeProjective] using this
  rw [hlast, normalizeCone_def]
  exact div_le_div_of_nonneg_right
    (hy.2.2.1 (Fin.castSucc_le_castSucc_iff.2 (Fin.le_last i.castSucc))) hpos.le

/-- Multiplying the homogeneous lift of `normalizeCone y` by `y_n` recovers `y` on `coneSpan d`
whenever `y_n ≠ 0`. -/
theorem smul_toHomogeneous_normalizeCone {d : ℕ} {y : Fin (d + 2) → ℝ}
    (hy : y ∈ coneSpan d) (hne : y (Fin.last (d + 1)) ≠ 0) :
    y (Fin.last (d + 1)) • toHomogeneous (normalizeCone y) = y := by
  ext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp
  · simp only [Pi.smul_apply, smul_eq_mul, toHomogeneous_castSucc,
      toProjective_normalizeCone hy hne, normalizeProjective]
    exact mul_div_cancel₀ _ hne

/-- Two points of `orderedCone d` have the same normalisation if and only if they lie on the
same positive ray. -/
theorem normalizeCone_eq_iff {d : ℕ} {y y' : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) (hy' : y' ∈ orderedCone d) :
    normalizeCone y = normalizeCone y' ↔ ∃ c : ℝ, 0 < c ∧ y' = c • y := by
  constructor
  · intro h
    refine ⟨y' (Fin.last (d + 1)) / y (Fin.last (d + 1)),
      div_pos (last_pos_of_mem_orderedCone hy') (last_pos_of_mem_orderedCone hy), ?_⟩
    have hy1 := smul_toHomogeneous_normalizeCone hy.2.2.2 (last_pos_of_mem_orderedCone hy).ne'
    have hy2 := smul_toHomogeneous_normalizeCone hy'.2.2.2 (last_pos_of_mem_orderedCone hy').ne'
    rw [← h] at hy2
    calc y' = y' (Fin.last (d + 1)) • toHomogeneous (normalizeCone y) := hy2.symm
      _ = (y' (Fin.last (d + 1)) / y (Fin.last (d + 1)) * y (Fin.last (d + 1))) •
            toHomogeneous (normalizeCone y) := by
          rw [div_mul_cancel₀ _ (last_pos_of_mem_orderedCone hy).ne']
      _ = (y' (Fin.last (d + 1)) / y (Fin.last (d + 1))) • y := by rw [mul_smul, hy1]
  · rintro ⟨c, hc, rfl⟩
    exact (normalizeCone_smul hc.ne' y).symm

/-! ### Basis and linear span of the ordered cone -/

/-- The vector `e_j + e_n` in `coneSpan d` for `j : Fin (d + 1)`. -/
def coneSpanBasisVec (d : ℕ) (j : Fin (d + 1)) : coneSpan d :=
  ⟨Pi.single j.castSucc (1 : ℝ) + Pi.single (Fin.last (d + 1)) (1 : ℝ), by
    classical
    simp only [mem_coneSpan_iff, Pi.add_apply, Finset.sum_add_distrib]
    have h1 : ∑ i : Fin (d + 1), (Pi.single j.castSucc (1 : ℝ) : Fin (d + 2) → ℝ) i.castSucc =
        1 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        exact Pi.single_eq_of_ne (fun h => hb (Fin.castSucc_inj.1 h)) _
      · simp
    have h2 : ∑ i : Fin (d + 1),
        (Pi.single (Fin.last (d + 1)) (1 : ℝ) : Fin (d + 2) → ℝ) i.castSucc = 0 :=
      Finset.sum_eq_zero fun i _ => Pi.single_eq_of_ne (Fin.castSucc_lt_last i).ne _
    have h3 : (Pi.single j.castSucc (1 : ℝ) : Fin (d + 2) → ℝ) (Fin.last (d + 1)) = 0 :=
      Pi.single_eq_of_ne (Fin.castSucc_lt_last j).ne' _
    have h4 : (Pi.single (Fin.last (d + 1)) (1 : ℝ) : Fin (d + 2) → ℝ) (Fin.last (d + 1)) = 1 := by
      simp
    linarith⟩

@[simp]
theorem coe_coneSpanBasisVec (d : ℕ) (j : Fin (d + 1)) :
    (coneSpanBasisVec d j : Fin (d + 2) → ℝ) =
      Pi.single j.castSucc 1 + Pi.single (Fin.last (d + 1)) 1 :=
  (rfl)

/-- The vectors `e_j + e_n` (`j : Fin (d + 1)`) form a basis of `coneSpan d`. -/
def coneSpanBasis (d : ℕ) : Module.Basis (Fin (d + 1)) ℝ (coneSpan d) := by
  classical
  refine Module.Basis.ofEquivFun
    { toFun := fun y i => (y : Fin (d + 2) → ℝ) i.castSucc
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun c => ⟨Fin.snoc c (∑ i, c i), by simp⟩
      left_inv := fun y => by
        ext i
        refine Fin.lastCases ?_ (fun k => ?_) i
        · simp only [Fin.snoc_last]
          exact y.2
        · simp
      right_inv := fun c => by ext i; simp }

/-- The `j`-th basis vector of `coneSpanBasis d` is `e_j + e_n`. -/
@[simp]
theorem coneSpanBasis_apply (d : ℕ) (j : Fin (d + 1)) :
    coneSpanBasis d j = coneSpanBasisVec d j := by
  classical
  ext i
  have hcoe : (coneSpanBasis d j : Fin (d + 2) → ℝ) i =
      (Fin.snoc (α := fun _ => ℝ) (Pi.single j (1 : ℝ))
        (∑ k : Fin (d + 1), (Pi.single j (1 : ℝ) : Fin (d + 1) → ℝ) k)) i := by
    simp [coneSpanBasis, Module.Basis.coe_ofEquivFun]
  rw [hcoe, coe_coneSpanBasisVec, Pi.add_apply]
  refine Fin.lastCases ?_ (fun k => ?_) i
  · rw [Fin.snoc_last, Pi.single_eq_of_ne (Fin.castSucc_lt_last j).ne', Pi.single_eq_same,
      zero_add]
    simp
  · rw [Fin.snoc_castSucc, Pi.single_eq_of_ne (Fin.castSucc_lt_last k).ne, add_zero]
    by_cases hkj : k = j
    · subst hkj; simp
    · rw [Pi.single_eq_of_ne hkj, Pi.single_eq_of_ne (fun h => hkj (Fin.castSucc_inj.1 h))]

/-- The dimension of `coneSpan d` is `d + 1`. -/
theorem finrank_coneSpan (d : ℕ) : Module.finrank ℝ (coneSpan d) = d + 1 := by
  rw [Module.finrank_eq_card_basis (coneSpanBasis d), Fintype.card_fin]

private def stepConeVec (d : ℕ) (k : Fin (d + 1)) : Fin (d + 2) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) (fun i : Fin (d + 1) => if k ≤ i then (1 : ℝ) else 0)
    (∑ i : Fin (d + 1), if k ≤ i then (1 : ℝ) else 0)

private theorem stepConeVec_mem_orderedCone (d : ℕ) (k : Fin (d + 1)) :
    stepConeVec d k ∈ orderedCone d := by
  have hterm_nonneg : ∀ m : Fin (d + 1), 0 ≤ (if k ≤ m then (1 : ℝ) else 0) :=
    fun m => by split_ifs <;> norm_num
  refine ⟨?_, ?_, ?_, by simp [stepConeVec]⟩
  · intro h0
    have hlast := congrFun h0 (Fin.last d).castSucc
    simp [stepConeVec, Fin.le_last] at hlast
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [stepConeVec, Fin.snoc_last]
      exact Finset.sum_nonneg fun m _ => hterm_nonneg m
    · simp only [stepConeVec, Fin.snoc_castSucc]
      exact hterm_nonneg j
  · intro i j
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · refine Fin.lastCases (fun _ => le_refl _) (fun i' _ => ?_) i
      simp only [stepConeVec, Fin.snoc_castSucc, Fin.snoc_last]
      exact Finset.single_le_sum (fun m _ => hterm_nonneg m) (Finset.mem_univ i')
    · refine Fin.lastCases (fun hij => ?_) (fun i' hij => ?_) i
      · exact absurd hij (not_le.2 (Fin.castSucc_lt_last j'))
      · simp only [stepConeVec, Fin.snoc_castSucc]
        have h' : i' ≤ j' := Fin.castSucc_le_castSucc_iff.1 hij
        split_ifs with h1 h2
        · exact le_refl _
        · exact absurd (h1.trans h') h2
        · norm_num
        · exact le_refl _

private theorem stepConeVec_last_eq (d : ℕ) :
    (coneSpanBasisVec d (Fin.last d) : Fin (d + 2) → ℝ) = stepConeVec d (Fin.last d) := by
  classical
  ext i
  refine Fin.lastCases ?_ (fun m => ?_) i
  · simp only [coe_coneSpanBasisVec, Pi.add_apply, stepConeVec, Fin.snoc_last,
      Pi.single_eq_of_ne (Fin.castSucc_lt_last (Fin.last d)).ne', Pi.single_eq_same, zero_add]
    rw [Finset.sum_eq_single (Fin.last d)]
    · simp
    · intro b _ hb
      simp [not_le.2 (lt_of_le_of_ne (Fin.le_last b) hb)]
    · simp
  · simp only [coe_coneSpanBasisVec, Pi.add_apply, stepConeVec, Fin.snoc_castSucc,
      Pi.single_eq_of_ne (Fin.castSucc_lt_last m).ne, add_zero]
    by_cases hm : m = Fin.last d
    · subst hm; simp
    · rw [Pi.single_eq_of_ne (fun h => hm (Fin.castSucc_inj.1 h)),
        ite_eq_right_iff.2 (fun h => absurd (le_antisymm (Fin.le_last m) h) hm)]

private theorem stepConeVec_sub_eq (d : ℕ) (k : Fin d) :
    (coneSpanBasisVec d k.castSucc : Fin (d + 2) → ℝ) =
      stepConeVec d k.castSucc - stepConeVec d k.succ := by
  classical
  have hstep : ∀ m : Fin (d + 1),
      (if k.castSucc ≤ m then (1 : ℝ) else 0) - (if k.succ ≤ m then (1 : ℝ) else 0) =
        if m = k.castSucc then 1 else 0 := fun m => by
    by_cases hmk : m = k.castSucc
    · subst hmk; simp [not_le.2 k.castSucc_lt_succ]
    · by_cases hkb : k.castSucc ≤ m
      · have hsucc : k.succ ≤ m := by
          rw [Fin.le_iff_val_le_val] at hkb ⊢
          have hne : m.val ≠ k.val := fun h => hmk (Fin.ext h)
          simp only [Fin.val_succ, Fin.val_castSucc] at hkb ⊢
          omega
        simp [hmk, hkb, hsucc]
      · have hnsucc : ¬ k.succ ≤ m := fun h => hkb (k.castSucc_lt_succ.le.trans h)
        simp [hmk, hkb, hnsucc]
  ext i
  refine Fin.lastCases ?_ (fun m => ?_) i
  · simp only [coe_coneSpanBasisVec, Pi.add_apply, Pi.sub_apply, stepConeVec, Fin.snoc_last,
      Pi.single_eq_of_ne (Fin.castSucc_lt_last k.castSucc).ne', Pi.single_eq_same, zero_add,
      ← Finset.sum_sub_distrib, hstep]
    simp
  · simp only [coe_coneSpanBasisVec, Pi.add_apply, Pi.sub_apply, stepConeVec,
      Fin.snoc_castSucc, Pi.single_eq_of_ne (Fin.castSucc_lt_last m).ne, add_zero, hstep]
    by_cases hmk : m = k.castSucc
    · subst hmk; simp
    · rw [Pi.single_eq_of_ne (fun h => hmk (Fin.castSucc_inj.1 h)), ite_eq_right_iff.2 (by
        intro h; exact absurd h hmk)]

private theorem coneSpanBasisVec_mem_span_orderedCone (d : ℕ) (j : Fin (d + 1)) :
    (coneSpanBasisVec d j : Fin (d + 2) → ℝ) ∈ Submodule.span ℝ (orderedCone d) := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rw [stepConeVec_last_eq]
    exact Submodule.subset_span (stepConeVec_mem_orderedCone d (Fin.last d))
  · rw [stepConeVec_sub_eq]
    exact Submodule.sub_mem _ (Submodule.subset_span (stepConeVec_mem_orderedCone d k.castSucc))
      (Submodule.subset_span (stepConeVec_mem_orderedCone d k.succ))

/-- The linear span of `orderedCone d` equals the hyperplane `coneSpan d`. -/
theorem span_orderedCone_eq_coneSpan (d : ℕ) :
    Submodule.span ℝ (orderedCone d) = coneSpan d := by
  refine le_antisymm (Submodule.span_le.2 (orderedCone_subset_coneSpan d)) ?_
  intro y hy
  have hy_eq : (⟨y, hy⟩ : coneSpan d) =
      ∑ j : Fin (d + 1), (coneSpanBasis d).repr ⟨y, hy⟩ j • coneSpanBasis d j :=
    ((coneSpanBasis d).sum_repr ⟨y, hy⟩).symm
  have hval : y = ∑ j : Fin (d + 1),
      (coneSpanBasis d).repr ⟨y, hy⟩ j • (coneSpanBasisVec d j : Fin (d + 2) → ℝ) := by
    have := congrArg Subtype.val hy_eq
    simpa [coneSpanBasis_apply] using this
  rw [hval]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (coneSpanBasisVec_mem_span_orderedCone d j)

end OrderedSimplex

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The ordered Markoff–Hurwitz cone and its projective simplex chart

For `n = d + 2`, the ordered Markoff–Hurwitz cone `H_n` (`TauCeti.MarkoffHurwitz.orderedCone d`)
consists of the nonzero nonnegative nondecreasing tuples `y : Fin (d + 2) → ℝ` satisfying the sum
relation `y₀ + ⋯ + y_d = y_{d+1}`. Dividing by the positive last coordinate `y_{d+1}` identifies
the positive rays of `H_n` with the ordered `(d + 1)`-simplex `0 ≤ w₀ ≤ ⋯ ≤ w_d` of unit sum, and
dropping the redundant coordinate `w_d = 1 - ∑ k, x k` embeds that quotient into `Fin d → ℝ` as
the compact convex polytope `TauCeti.MarkoffHurwitz.orderedSimplex d`. Charting in dimension `d`
rather than `d + 1` gives a subset of `Fin d → ℝ` with nonempty interior, so within-derivatives on
the simplex are unique (`TauCeti.MarkoffHurwitz.uniqueDiffOn_orderedSimplex`).

This file develops the geometry of `orderedSimplex d` and `orderedCone d`:
* sharp coordinate enclosures `0 ≤ x j ≤ 1 / 2` and `1 / (d + 1) ≤ 1 - ∑ k, x k ≤ 1` on
  `orderedSimplex d`;
* compactness, convexity, the explicit strictly increasing interior point
  `x_i = 2 (i + 1) / ((d + 2)(d + 1))`, and uniqueness of within-derivatives;
* `chartToSimplex`, `orderedSimplexLift`, `orderedConeProject`, and positive-ray equivalence;
* identification of `Submodule.span ℝ (orderedCone d)` with the sum hyperplane and its basis
  `e_j + e_{d+1}` (`orderedConeSpanBasis`);
* the open strictly increasing positive subcone `strictOrderedCone d` and membership of the lifted
  interior point.

## References

* A. Gamburd, M. Magee, and R. Ronan, *An asymptotic formula for integer points on
  Markoff–Hurwitz varieties*, Annals of Mathematics 190 (2019), 751–809, (1.5), §4.1, and §5.1.
-/

public noncomputable section

open Set Topology

namespace TauCeti.MarkoffHurwitz

/-! ### The ordered projective simplex in chart coordinates -/

/-- The ordered projective simplex `Δ_{d+2}` in chart coordinates `x : Fin d → ℝ`, where
`x i` represents `w_{i+1}` and `1 - ∑ k, x k` represents the largest simplex coordinate
`w_{d+1}`: nonnegative nondecreasing coordinates bounded above by `1 - ∑ k, x k`
(Gamburd–Magee–Ronan 2019, (1.5) and §5.1). -/
def orderedSimplex (d : ℕ) : Set (Fin d → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ Monotone x ∧ ∀ i, x i ≤ 1 - ∑ k, x k}

/-- Membership in `orderedSimplex d` unfolded in coordinates. -/
theorem mem_orderedSimplex_iff {d : ℕ} {x : Fin d → ℝ} :
    x ∈ orderedSimplex d ↔ (∀ i, 0 ≤ x i) ∧ Monotone x ∧ ∀ i, x i ≤ 1 - ∑ k, x k := Iff.rfl

/-- Every chart coordinate of a point in `orderedSimplex d` is nonnegative. -/
theorem apply_nonneg_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d)
    (i : Fin d) : 0 ≤ x i := hx.1 i

/-- The chart coordinates of a point in `orderedSimplex d` are nondecreasing. -/
theorem monotone_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    Monotone x := hx.2.1

/-- Every chart coordinate of a point in `orderedSimplex d` is at most `1 - ∑ k, x k`. -/
theorem apply_le_one_sub_sum_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) (i : Fin d) : x i ≤ 1 - ∑ k, x k := hx.2.2 i

/-- In chart dimension `0` (`n = 2`), `orderedSimplex 0` is the whole one-point space. -/
@[simp]
theorem orderedSimplex_zero : orderedSimplex 0 = univ := by
  ext x; simp [mem_orderedSimplex_iff, Subsingleton.monotone]

/-- For `d = 1` (`n = 3`), `orderedSimplex 1` is the segment `0 ≤ x 0 ≤ 1 / 2`. -/
theorem orderedSimplex_one : orderedSimplex 1 = {x | x 0 ∈ Icc 0 (1 / 2)} := by
  ext x
  simp only [mem_orderedSimplex_iff, Fin.forall_fin_one, Fin.sum_univ_one, Subsingleton.monotone,
    true_and, mem_ofPred_eq, mem_Icc]
  constructor <;> intro ⟨h0, h1⟩ <;> exact ⟨h0, by linarith⟩

/-- The origin belongs to `orderedSimplex d` in every dimension. -/
@[simp]
theorem zero_mem_orderedSimplex (d : ℕ) : (0 : Fin d → ℝ) ∈ orderedSimplex d :=
  ⟨fun _ => le_rfl, monotone_const, fun _ => by simp⟩

/-- `orderedSimplex d` is nonempty in every dimension. -/
theorem orderedSimplex_nonempty (d : ℕ) : (orderedSimplex d).Nonempty :=
  ⟨0, zero_mem_orderedSimplex d⟩

/-- Every chart coordinate on `orderedSimplex d` is at most `1 / 2`. -/
theorem apply_le_half_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d)
    (i : Fin d) : x i ≤ 1 / 2 := by
  linarith [Finset.single_le_sum (fun k _ => hx.1 k) (Finset.mem_univ i), hx.2.2 i]

/-- Every chart coordinate on `orderedSimplex d` lies in `[0, 1 / 2]`. -/
theorem apply_mem_Icc_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d)
    (i : Fin d) : x i ∈ Icc 0 (1 / 2) :=
  ⟨hx.1 i, apply_le_half_of_mem_orderedSimplex hx i⟩

/-- `orderedSimplex d` is contained in the box `[0, 1 / 2]^d`. -/
theorem orderedSimplex_subset_Icc (d : ℕ) :
    orderedSimplex d ⊆ Icc 0 (fun _ => (1 / 2 : ℝ)) :=
  fun _ hx => ⟨fun i => hx.1 i, fun i => apply_le_half_of_mem_orderedSimplex hx i⟩

/-- The sum of the chart coordinates on `orderedSimplex d` is nonnegative. -/
theorem sum_nonneg_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ} (hx : x ∈ orderedSimplex d) :
    0 ≤ ∑ k, x k :=
  Finset.sum_nonneg fun k _ => hx.1 k

/-- The last simplex coordinate `1 - ∑ k, x k` is at least `1 / (d + 1)` on `orderedSimplex d`. -/
theorem one_div_add_one_le_one_sub_sum_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : 1 / ((d : ℝ) + 1) ≤ 1 - ∑ k, x k := by
  rw [div_le_iff₀ (by positivity)]
  linarith [show ∑ i : Fin d, x i ≤ (d : ℝ) * (1 - ∑ k, x k) by
    simpa using Finset.sum_le_card_nsmul Finset.univ x (1 - ∑ k, x k) fun i _ => hx.2.2 i]

/-- The last simplex coordinate `1 - ∑ k, x k` is at most `1` on `orderedSimplex d`. -/
theorem one_sub_sum_le_one_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : 1 - ∑ k, x k ≤ 1 := by
  linarith [sum_nonneg_of_mem_orderedSimplex hx]

/-- The last simplex coordinate `1 - ∑ k, x k` is strictly positive on `orderedSimplex d`. -/
theorem one_sub_sum_pos_of_mem_orderedSimplex {d : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : 0 < 1 - ∑ k, x k :=
  lt_of_lt_of_le (by positivity) (one_div_add_one_le_one_sub_sum_of_mem_orderedSimplex hx)

/-- `orderedSimplex d` is closed in `Fin d → ℝ`. -/
theorem isClosed_orderedSimplex (d : ℕ) : IsClosed (orderedSimplex d) := by
  simp only [orderedSimplex, ofPred_and]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_) <;> simp only [ofPred_forall, Monotone]
  · exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply i) (continuous_apply j)
  · exact isClosed_iInter fun i => isClosed_le (continuous_apply i) (by fun_prop)

/-- `orderedSimplex d` is compact in `Fin d → ℝ`. -/
theorem isCompact_orderedSimplex (d : ℕ) : IsCompact (orderedSimplex d) :=
  isCompact_Icc.of_isClosed_subset (isClosed_orderedSimplex d) (orderedSimplex_subset_Icc d)

/-- `orderedSimplex d` is convex over `ℝ`. -/
theorem convex_orderedSimplex (d : ℕ) : Convex ℝ (orderedSimplex d) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)),
    fun i j hij => add_le_add (mul_le_mul_of_nonneg_left (hx.2.1 hij) ha)
      (mul_le_mul_of_nonneg_left (hy.2.1 hij) hb), fun i => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith [hx.2.2 i, hy.2.2 i]

/-! ### Explicit interior point and uniqueness of within-derivatives -/

/-- The canonical interior chart point `x_i = 2 (i + 1) / ((d + 2)(d + 1))` of `orderedSimplex d`,
corresponding to `w_k = 2 k / (n (n - 1))` for `n = d + 2` (Gamburd–Magee–Ronan 2019, §5.1). -/
def orderedSimplexInteriorPoint (d : ℕ) : Fin d → ℝ :=
  fun i => 2 * ((i : ℝ) + 1) / (((d : ℝ) + 2) * ((d : ℝ) + 1))

/-- Coordinate formula for `orderedSimplexInteriorPoint d`. -/
theorem orderedSimplexInteriorPoint_apply (d : ℕ) (i : Fin d) :
    orderedSimplexInteriorPoint d i =
      2 * ((i : ℝ) + 1) / (((d : ℝ) + 2) * ((d : ℝ) + 1)) := (rfl)

/-- Every coordinate of `orderedSimplexInteriorPoint d` is strictly positive. -/
theorem orderedSimplexInteriorPoint_pos {d : ℕ} (i : Fin d) :
    0 < orderedSimplexInteriorPoint d i := by
  rw [orderedSimplexInteriorPoint_apply]; positivity

/-- The coordinates of `orderedSimplexInteriorPoint d` are strictly increasing. -/
theorem strictMono_orderedSimplexInteriorPoint (d : ℕ) :
    StrictMono (orderedSimplexInteriorPoint d) := fun i j hij => by
  simp only [orderedSimplexInteriorPoint_apply]
  exact div_lt_div_of_pos_right (by linarith [show (i : ℝ) < j from Nat.cast_lt.mpr hij])
    (by positivity)

/-- The sum of the chart coordinates of `orderedSimplexInteriorPoint d` is `d / (d + 2)`. -/
theorem sum_orderedSimplexInteriorPoint (d : ℕ) :
    ∑ k : Fin d, orderedSimplexInteriorPoint d k = (d : ℝ) / ((d : ℝ) + 2) := by
  have hgauss : ∑ k : Fin d, (2 * ((k : ℝ) + 1)) = (d : ℝ) * ((d : ℝ) + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun m : ℕ => 2 * ((m : ℝ) + 1)) d]
    induction d with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have hd1 : ((d : ℝ) + 1) ≠ 0 := by positivity
  simp only [orderedSimplexInteriorPoint_apply, ← Finset.sum_div, hgauss]
  field_simp

/-- At `orderedSimplexInteriorPoint d`, the remaining simplex coordinate `1 - ∑ k, x k` equals
`2 / (d + 2)`. -/
theorem one_sub_sum_orderedSimplexInteriorPoint (d : ℕ) :
    1 - ∑ k : Fin d, orderedSimplexInteriorPoint d k = 2 / ((d : ℝ) + 2) := by
  have hd2 : ((d : ℝ) + 2) ≠ 0 := by positivity
  rw [sum_orderedSimplexInteriorPoint]; field_simp; ring

/-- Every coordinate of `orderedSimplexInteriorPoint d` is strictly below `1 - ∑ k, x k`. -/
theorem orderedSimplexInteriorPoint_lt_one_sub_sum {d : ℕ} (i : Fin d) :
    orderedSimplexInteriorPoint d i < 1 - ∑ k : Fin d, orderedSimplexInteriorPoint d k := by
  rw [orderedSimplexInteriorPoint_apply, one_sub_sum_orderedSimplexInteriorPoint,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  have hi : (i : ℝ) + 1 < (d : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ i.isLt
  nlinarith

/-- `orderedSimplexInteriorPoint d` lies in the interior of `orderedSimplex d`. -/
theorem orderedSimplexInteriorPoint_mem_interior (d : ℕ) :
    orderedSimplexInteriorPoint d ∈ interior (orderedSimplex d) := by
  refine mem_interior.mpr ⟨{y | (∀ i, 0 < y i) ∧ StrictMono y ∧ ∀ i, y i < 1 - ∑ k, y k},
    fun y ⟨h1, h2, h3⟩ => ⟨fun i => (h1 i).le, h2.monotone, fun i => (h3 i).le⟩, ?_,
    orderedSimplexInteriorPoint_pos, strictMono_orderedSimplexInteriorPoint d,
    orderedSimplexInteriorPoint_lt_one_sub_sum⟩
  simp only [ofPred_and]
  refine IsOpen.inter ?_ (IsOpen.inter ?_ ?_) <;> simp only [ofPred_forall, StrictMono]
  · exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => isOpen_lt (continuous_apply i) (continuous_apply j)
  · exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) (by fun_prop)

/-- `orderedSimplexInteriorPoint d` belongs to `orderedSimplex d`. -/
theorem orderedSimplexInteriorPoint_mem (d : ℕ) :
    orderedSimplexInteriorPoint d ∈ orderedSimplex d :=
  interior_subset (orderedSimplexInteriorPoint_mem_interior d)

/-- `orderedSimplex d` has nonempty interior in `Fin d → ℝ`. -/
theorem interior_orderedSimplex_nonempty (d : ℕ) : (interior (orderedSimplex d)).Nonempty :=
  ⟨orderedSimplexInteriorPoint d, orderedSimplexInteriorPoint_mem_interior d⟩

/-- Within-derivatives on `orderedSimplex d` are unique. -/
theorem uniqueDiffOn_orderedSimplex (d : ℕ) : UniqueDiffOn ℝ (orderedSimplex d) :=
  uniqueDiffOn_convex (convex_orderedSimplex d) (interior_orderedSimplex_nonempty d)

/-! ### Full simplex coordinates, the homogeneous cone, and positive-ray normalization -/

/-- Reconstruct the full `(d + 1)`-tuple `(x₀, …, x_{d-1}, 1 - ∑ k, x k)` on the unit-sum
hyperplane from chart coordinates `x : Fin d → ℝ`. -/
def chartToSimplex {d : ℕ} (x : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.snoc x (1 - ∑ k, x k)

/-- Unfolded formula for `chartToSimplex x`. -/
theorem chartToSimplex_def {d : ℕ} (x : Fin d → ℝ) :
    chartToSimplex x = Fin.snoc x (1 - ∑ k, x k) := (rfl)

/-- `chartToSimplex x` agrees with `x` on the first `d` coordinates. -/
@[simp]
theorem chartToSimplex_castSucc {d : ℕ} (x : Fin d → ℝ) (i : Fin d) :
    chartToSimplex x (Fin.castSucc i) = x i :=
  Fin.snoc_castSucc _ _ _

/-- The last coordinate of `chartToSimplex x` is `1 - ∑ k, x k`. -/
@[simp]
theorem chartToSimplex_last {d : ℕ} (x : Fin d → ℝ) :
    chartToSimplex x (Fin.last d) = 1 - ∑ k, x k :=
  Fin.snoc_last _ _

/-- The coordinates of `chartToSimplex x` always sum to `1`. -/
@[simp]
theorem sum_chartToSimplex {d : ℕ} (x : Fin d → ℝ) :
    ∑ j : Fin (d + 1), chartToSimplex x j = 1 := by
  rw [Fin.sum_univ_castSucc]; simp

/-- A chart point `x` lies in `orderedSimplex d` if and only if `chartToSimplex x` has nonnegative
nondecreasing coordinates. -/
theorem mem_orderedSimplex_iff_chartToSimplex {d : ℕ} {x : Fin d → ℝ} :
    x ∈ orderedSimplex d ↔
      (∀ i, 0 ≤ chartToSimplex x i) ∧ Monotone (chartToSimplex x) := by
  refine ⟨fun hx => ⟨Fin.lastCases (by simpa using (one_sub_sum_pos_of_mem_orderedSimplex hx).le)
      fun i => by simpa using hx.1 i, ?_⟩, fun ⟨hnn, hmono⟩ =>
    ⟨fun i => by simpa using hnn (Fin.castSucc i),
      fun _ _ hij => by simpa using hmono (Fin.castSucc_le_castSucc_iff.mpr hij),
      fun i => by simpa using hmono (Fin.le_last (Fin.castSucc i))⟩⟩
  exact Fin.lastCases (fun j hj => by obtain rfl := le_antisymm (Fin.le_last j) hj; exact le_rfl)
    (fun i => Fin.lastCases (fun _ => by simpa using hx.2.2 i)
      fun j hij => by simpa using hx.2.1 (Fin.castSucc_le_castSucc_iff.mp hij))

/-- The homogeneous ordered Markoff–Hurwitz cone `H_{d+2}`: nonzero nonnegative nondecreasing
tuples `y : Fin (d + 2) → ℝ` satisfying `∑_{i < d + 1} y_i = y_{d+1}`
(Gamburd–Magee–Ronan 2019, (1.5)). -/
def orderedCone (d : ℕ) : Set (Fin (d + 2) → ℝ) :=
  {y | y ≠ 0 ∧ (∀ i, 0 ≤ y i) ∧ Monotone y ∧
    ∑ i : Fin (d + 1), y (Fin.castSucc i) = y (Fin.last (d + 1))}

/-- Membership in `orderedCone d` unfolded. -/
theorem mem_orderedCone_iff {d : ℕ} {y : Fin (d + 2) → ℝ} :
    y ∈ orderedCone d ↔
      y ≠ 0 ∧ (∀ i, 0 ≤ y i) ∧ Monotone y ∧
        ∑ i : Fin (d + 1), y (Fin.castSucc i) = y (Fin.last (d + 1)) := Iff.rfl

/-- Every point of `orderedCone d` has strictly positive last coordinate `y_{d+1} > 0`. -/
theorem last_pos_of_mem_orderedCone {d : ℕ} {y : Fin (d + 2) → ℝ} (hy : y ∈ orderedCone d) :
    0 < y (Fin.last (d + 1)) := by
  by_contra hle
  exact hy.1 (funext fun i => le_antisymm ((hy.2.2.1 (Fin.le_last i)).trans (not_lt.mp hle))
    (hy.2.1 i))

/-- `orderedCone d` is invariant under positive scalar multiplication. -/
theorem smul_mem_orderedCone {d : ℕ} {c : ℝ} (hc : 0 < c) {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) : c • y ∈ orderedCone d := by
  refine ⟨smul_ne_zero hc.ne' hy.1, fun i => mul_nonneg hc.le (hy.2.1 i),
    fun i j hij => mul_le_mul_of_nonneg_left (hy.2.2.1 hij) hc.le, ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hy.2.2.2]

/-- Lift a chart point `x : Fin d → ℝ` to the normalized homogeneous tuple
`(x₀, …, x_{d-1}, 1 - ∑ k, x k, 1)`. -/
def orderedSimplexLift {d : ℕ} (x : Fin d → ℝ) : Fin (d + 2) → ℝ :=
  Fin.snoc (chartToSimplex x) 1

/-- Unfolded formula for `orderedSimplexLift x`. -/
theorem orderedSimplexLift_def {d : ℕ} (x : Fin d → ℝ) :
    orderedSimplexLift x = Fin.snoc (chartToSimplex x) 1 := (rfl)

/-- `orderedSimplexLift x` agrees with `chartToSimplex x` on the first `d + 1` coordinates. -/
@[simp]
theorem orderedSimplexLift_castSucc {d : ℕ} (x : Fin d → ℝ) (i : Fin (d + 1)) :
    orderedSimplexLift x (Fin.castSucc i) = chartToSimplex x i :=
  Fin.snoc_castSucc _ _ _

/-- The last coordinate of `orderedSimplexLift x` is `1`. -/
@[simp]
theorem orderedSimplexLift_last {d : ℕ} (x : Fin d → ℝ) :
    orderedSimplexLift x (Fin.last (d + 1)) = 1 :=
  Fin.snoc_last _ _

/-- `orderedSimplexLift x` satisfies the homogeneous sum relation for every `x : Fin d → ℝ`. -/
theorem sum_castSucc_orderedSimplexLift {d : ℕ} (x : Fin d → ℝ) :
    ∑ i : Fin (d + 1), orderedSimplexLift x (Fin.castSucc i) =
      orderedSimplexLift x (Fin.last (d + 1)) := by simp

/-- `orderedSimplexLift x` lies in `orderedCone d` if and only if `x` lies in
`orderedSimplex d`. -/
@[simp]
theorem orderedSimplexLift_mem_orderedCone_iff {d : ℕ} {x : Fin d → ℝ} :
    orderedSimplexLift x ∈ orderedCone d ↔ x ∈ orderedSimplex d := by
  rw [mem_orderedSimplex_iff_chartToSimplex]
  refine ⟨fun ⟨_, hnn, hmono, _⟩ => ⟨fun i => by simpa using hnn (Fin.castSucc i),
    fun _ _ hij => by simpa using hmono (Fin.castSucc_le_castSucc_iff.mpr hij)⟩,
    fun ⟨hnn, hmono⟩ => ⟨fun h0 => by simpa using congrFun h0 (Fin.last (d + 1)),
      Fin.lastCases (by simp) fun i => by simpa using hnn i, ?_,
      sum_castSucc_orderedSimplexLift x⟩⟩
  refine Fin.lastCases (fun j hj => by obtain rfl := le_antisymm (Fin.le_last j) hj; exact le_rfl)
    fun i => Fin.lastCases (fun _ => ?_)
      fun j hij => by simpa using hmono (Fin.castSucc_le_castSucc_iff.mp hij)
  rw [orderedSimplexLift_castSucc, orderedSimplexLift_last, ← sum_chartToSimplex x]
  exact Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_univ i)

/-- Project a homogeneous tuple `y : Fin (d + 2) → ℝ` to chart coordinates by dividing its first
`d` coordinates by `y_{d+1}`. -/
def orderedConeProject {d : ℕ} (y : Fin (d + 2) → ℝ) : Fin d → ℝ :=
  fun i => y (Fin.castSucc (Fin.castSucc i)) / y (Fin.last (d + 1))

/-- Coordinate formula for `orderedConeProject y`. -/
theorem orderedConeProject_apply {d : ℕ} (y : Fin (d + 2) → ℝ) (i : Fin d) :
    orderedConeProject y i = y (Fin.castSucc (Fin.castSucc i)) / y (Fin.last (d + 1)) := (rfl)

/-- `orderedConeProject` left-inverts `orderedSimplexLift`. -/
@[simp]
theorem orderedConeProject_orderedSimplexLift {d : ℕ} (x : Fin d → ℝ) :
    orderedConeProject (orderedSimplexLift x) = x := by
  ext i; simp [orderedConeProject_apply]

/-- On the sum hyperplane `∑_{i < d + 1} y_i = y_{d+1}` with `y_{d+1} ≠ 0`, `chartToSimplex` of
`orderedConeProject y` recovers all `d + 1` normalized coordinates `y_i / y_{d+1}`. -/
theorem chartToSimplex_orderedConeProject {d : ℕ} {y : Fin (d + 2) → ℝ}
    (hsum : ∑ i : Fin (d + 1), y (Fin.castSucc i) = y (Fin.last (d + 1)))
    (hlast : y (Fin.last (d + 1)) ≠ 0) :
    chartToSimplex (orderedConeProject y) = fun i => y (Fin.castSucc i) / y (Fin.last (d + 1)) := by
  ext i
  induction i using Fin.lastCases with
  | cast j => simp [orderedConeProject_apply]
  | last =>
    rw [chartToSimplex_last]
    simp only [orderedConeProject_apply, ← Finset.sum_div]
    rw [Fin.sum_univ_castSucc] at hsum
    field_simp
    linarith

/-- Multiplying `orderedSimplexLift (orderedConeProject y)` by `y_{d+1}` recovers `y` for every
`y ∈ orderedCone d`. -/
theorem last_smul_orderedSimplexLift_orderedConeProject {d : ℕ} {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) :
    y (Fin.last (d + 1)) • orderedSimplexLift (orderedConeProject y) = y := by
  have hpos := last_pos_of_mem_orderedCone hy
  ext i
  refine Fin.lastCases (by simp) (fun j => ?_) i
  simp [chartToSimplex_orderedConeProject hy.2.2.2 hpos.ne', mul_div_cancel₀ _ hpos.ne']

/-- `orderedConeProject` maps `orderedCone d` into `orderedSimplex d`. -/
theorem orderedConeProject_mem_orderedSimplex {d : ℕ} {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedCone d) : orderedConeProject y ∈ orderedSimplex d := by
  rw [← orderedSimplexLift_mem_orderedCone_iff]
  have hpos := last_pos_of_mem_orderedCone hy
  have hscale := smul_mem_orderedCone (inv_pos.mpr hpos) hy
  nth_rw 2 [← last_smul_orderedSimplexLift_orderedConeProject hy] at hscale
  rwa [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul] at hscale

/-- `orderedConeProject` is invariant under nonzero scalar multiplication. -/
@[simp]
theorem orderedConeProject_smul {d : ℕ} {c : ℝ} (hc : c ≠ 0) (y : Fin (d + 2) → ℝ) :
    orderedConeProject (c • y) = orderedConeProject y := by
  ext i; simp [orderedConeProject_apply, mul_div_mul_left _ _ hc]

/-- Two points of `orderedCone d` have the same chart projection if and only if they lie on the
same open positive ray. -/
theorem orderedConeProject_eq_iff {d : ℕ} {y z : Fin (d + 2) → ℝ} (hy : y ∈ orderedCone d)
    (hz : z ∈ orderedCone d) :
    orderedConeProject y = orderedConeProject z ↔ ∃ c : ℝ, 0 < c ∧ z = c • y := by
  refine ⟨fun hproj => ?_, fun ⟨c, hc, hzy⟩ => hzy ▸ (orderedConeProject_smul hc.ne' y).symm⟩
  have hypos := last_pos_of_mem_orderedCone hy
  refine ⟨z (Fin.last (d + 1)) / y (Fin.last (d + 1)),
    div_pos (last_pos_of_mem_orderedCone hz) hypos, ?_⟩
  calc z = z (Fin.last (d + 1)) • orderedSimplexLift (orderedConeProject y) := by
          rw [hproj, last_smul_orderedSimplexLift_orderedConeProject hz]
    _ = (z (Fin.last (d + 1)) / y (Fin.last (d + 1))) • y := by
          nth_rw 3 [← last_smul_orderedSimplexLift_orderedConeProject hy]
          rw [smul_smul, div_mul_cancel₀ _ hypos.ne']

/-! ### The linear span of `orderedCone d` and its basis `e_j + e_{d+1}` -/

/-- The sum hyperplane `{y : Fin (d + 2) → ℝ | ∑_{i < d + 1} y_i = y_{d+1}}` containing
`orderedCone d`. -/
def orderedConeHyperplane (d : ℕ) : Submodule ℝ (Fin (d + 2) → ℝ) where
  carrier := {y | ∑ i : Fin (d + 1), y (Fin.castSucc i) = y (Fin.last (d + 1))}
  add_mem' {a b} ha hb := by rw [mem_ofPred_eq] at ha hb ⊢; simp [Finset.sum_add_distrib, ha, hb]
  zero_mem' := by simp
  smul_mem' c {a} ha := by rw [mem_ofPred_eq] at ha ⊢; simp [← Finset.mul_sum, ha]

/-- Membership in `orderedConeHyperplane d` unfolded. -/
@[simp]
theorem mem_orderedConeHyperplane_iff {d : ℕ} {y : Fin (d + 2) → ℝ} :
    y ∈ orderedConeHyperplane d ↔
      ∑ i : Fin (d + 1), y (Fin.castSucc i) = y (Fin.last (d + 1)) := Iff.rfl

/-- The `j`-th standard basis vector `e_j + e_{d+1}` of `orderedConeHyperplane d`
(Gamburd–Magee–Ronan 2019, p. 756). -/
def orderedConeBasisVec (d : ℕ) (j : Fin (d + 1)) : Fin (d + 2) → ℝ :=
  Pi.single (Fin.castSucc j) 1 + Pi.single (Fin.last (d + 1)) 1

/-- Coordinate evaluation of `orderedConeBasisVec d j` at `Fin.castSucc i`. -/
@[simp]
theorem orderedConeBasisVec_castSucc {d : ℕ} (j i : Fin (d + 1)) :
    orderedConeBasisVec d j (Fin.castSucc i) = if i = j then 1 else 0 := by
  simp [orderedConeBasisVec, Pi.single_apply, (Fin.castSucc_lt_last i).ne]

/-- Coordinate evaluation of `orderedConeBasisVec d j` at `Fin.last (d + 1)`. -/
@[simp]
theorem orderedConeBasisVec_last {d : ℕ} (j : Fin (d + 1)) :
    orderedConeBasisVec d j (Fin.last (d + 1)) = 1 := by
  simp [orderedConeBasisVec, (Fin.castSucc_lt_last j).ne']

/-- Every `orderedConeBasisVec d j` belongs to `orderedConeHyperplane d`. -/
theorem orderedConeBasisVec_mem_hyperplane (d : ℕ) (j : Fin (d + 1)) :
    orderedConeBasisVec d j ∈ orderedConeHyperplane d := by simp

/-- The vectors `orderedConeBasisVec d` are linearly independent over `ℝ`. -/
theorem linearIndependent_orderedConeBasisVec (d : ℕ) :
    LinearIndependent ℝ (orderedConeBasisVec d) := by
  rw [Fintype.linearIndependent_iff]
  exact fun c hc j => by simpa using congrFun hc (Fin.castSucc j)

/-- Every vector in `orderedConeHyperplane d` expands in `orderedConeBasisVec d` with its first
`d + 1` coordinates as coefficients. -/
theorem sum_orderedConeBasisVec_eq {d : ℕ} {y : Fin (d + 2) → ℝ}
    (hy : y ∈ orderedConeHyperplane d) :
    ∑ j : Fin (d + 1), y (Fin.castSucc j) • orderedConeBasisVec d j = y := by
  ext i
  exact Fin.lastCases (by simpa using mem_orderedConeHyperplane_iff.mp hy) (fun k => by simp) i

/-- The `j`-th extreme-ray suffix vector `∑_{i ≥ j} (e_i + e_{d+1})` of `orderedCone d`, with `0`
on slots `< j`, `1` on slots `j ≤ i ≤ d`, and `d + 1 - j` in the last slot. -/
def orderedConeSuffixVec (d : ℕ) (j : Fin (d + 1)) : Fin (d + 2) → ℝ :=
  ∑ i ∈ Finset.Ici j, orderedConeBasisVec d i

/-- Coordinate evaluation of `orderedConeSuffixVec d j` at `Fin.castSucc m`. -/
@[simp]
theorem orderedConeSuffixVec_castSucc {d : ℕ} (j m : Fin (d + 1)) :
    orderedConeSuffixVec d j (Fin.castSucc m) = if j ≤ m then 1 else 0 := by
  simp [orderedConeSuffixVec, Finset.mem_Ici]

/-- Coordinate evaluation of `orderedConeSuffixVec d j` at `Fin.last (d + 1)`. -/
@[simp]
theorem orderedConeSuffixVec_last {d : ℕ} (j : Fin (d + 1)) :
    orderedConeSuffixVec d j (Fin.last (d + 1)) = ((Finset.Ici j).card : ℝ) := by
  simp [orderedConeSuffixVec]

/-- Every suffix vector `orderedConeSuffixVec d j` belongs to `orderedCone d`. -/
theorem orderedConeSuffixVec_mem_orderedCone (d : ℕ) (j : Fin (d + 1)) :
    orderedConeSuffixVec d j ∈ orderedCone d := by
  have hhyp : orderedConeSuffixVec d j ∈ orderedConeHyperplane d :=
    Submodule.sum_mem _ fun i _ => orderedConeBasisVec_mem_hyperplane d i
  have h1 : (1 : ℝ) ≤ ((Finset.Ici j).card : ℝ) :=
    Nat.one_le_cast.mpr (Finset.one_le_card.mpr ⟨j, Finset.mem_Ici.mpr le_rfl⟩)
  refine ⟨fun h0 => by simpa using congrFun h0 (Fin.castSucc j),
    Fin.lastCases (by rw [orderedConeSuffixVec_last]; exact Nat.cast_nonneg _) fun m => by
      simp only [orderedConeSuffixVec_castSucc]; split_ifs <;> norm_num,
    ?_, mem_orderedConeHyperplane_iff.mp hhyp⟩
  refine Fin.lastCases (fun b hb => by obtain rfl := le_antisymm (Fin.le_last b) hb; exact le_rfl)
    fun a => Fin.lastCases (fun _ => by
      simp only [orderedConeSuffixVec_castSucc, orderedConeSuffixVec_last]; split_ifs <;> linarith)
      fun b hab => ?_
  have hab' := Fin.castSucc_le_castSucc_iff.mp hab
  simp only [orderedConeSuffixVec_castSucc]
  split_ifs with ha hb' <;> [exact le_rfl; exact absurd (ha.trans hab') hb'; norm_num; exact le_rfl]

/-- Each `orderedConeBasisVec d j` lies in the `ℝ`-linear span of `orderedCone d`. -/
theorem orderedConeBasisVec_mem_span_orderedCone (d : ℕ) (j : Fin (d + 1)) :
    orderedConeBasisVec d j ∈ Submodule.span ℝ (orderedCone d) := by
  by_cases hj : j = Fin.last d
  · subst hj
    have hIci : Finset.Ici (Fin.last d) = {Fin.last d} := by
      ext i
      simp only [Finset.mem_Ici, Finset.mem_singleton, le_antisymm_iff, Fin.le_last, true_and]
    have heq : orderedConeBasisVec d (Fin.last d) = orderedConeSuffixVec d (Fin.last d) := by
      simp [orderedConeSuffixVec, hIci]
    exact heq ▸ Submodule.subset_span (orderedConeSuffixVec_mem_orderedCone d (Fin.last d))
  · let j' : Fin (d + 1) := (j.castPred hj).succ
    have hiff : ∀ m : Fin (d + 1), j' ≤ m ↔ j < m := fun m => by
      rw [← Fin.castSucc_castPred j hj]
      simp only [j', Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc]; omega
    have hIci : Finset.Ici j = insert j (Finset.Ici j') := by
      ext m; simp [Finset.mem_Ici, hiff, le_iff_eq_or_lt, eq_comm]
    have hadd : orderedConeBasisVec d j + orderedConeSuffixVec d j' = orderedConeSuffixVec d j := by
      simp only [orderedConeSuffixVec]; rw [hIci, Finset.sum_insert (by simp [hiff])]
    rw [eq_sub_of_add_eq hadd]
    exact Submodule.sub_mem _
      (Submodule.subset_span (orderedConeSuffixVec_mem_orderedCone d j))
      (Submodule.subset_span (orderedConeSuffixVec_mem_orderedCone d j'))

/-- The `ℝ`-linear span of `orderedCone d` is the sum hyperplane `orderedConeHyperplane d`. -/
theorem span_orderedCone_eq_hyperplane (d : ℕ) :
    Submodule.span ℝ (orderedCone d) = orderedConeHyperplane d := by
  refine le_antisymm (Submodule.span_le.mpr fun y hy => hy.2.2.2) fun y hy => ?_
  rw [← sum_orderedConeBasisVec_eq hy]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (orderedConeBasisVec_mem_span_orderedCone d j)

/-- The vectors `e_j + e_{d+1}` (`0 ≤ j ≤ d`) span the same subspace as `orderedCone d`. -/
theorem span_range_orderedConeBasisVec (d : ℕ) :
    Submodule.span ℝ (range (orderedConeBasisVec d)) = Submodule.span ℝ (orderedCone d) := by
  rw [span_orderedCone_eq_hyperplane]
  refine le_antisymm (Submodule.span_le.mpr fun _ ⟨j, hj⟩ => hj ▸
    orderedConeBasisVec_mem_hyperplane d j) fun y hy => ?_
  rw [← sum_orderedConeBasisVec_eq hy]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self j))

/-- The canonical basis `e_j + e_{d+1}` (`j : Fin (d + 1)`) of the linear span of
`orderedCone d` (Gamburd–Magee–Ronan 2019, p. 756). -/
def orderedConeSpanBasis (d : ℕ) :
    Module.Basis (Fin (d + 1)) ℝ (Submodule.span ℝ (orderedCone d)) :=
  (Module.Basis.span (linearIndependent_orderedConeBasisVec d)).map
    (LinearEquiv.ofEq _ _ (span_range_orderedConeBasisVec d))

/-- Underlying vector of the `j`-th basis element of `orderedConeSpanBasis d`. -/
@[simp]
theorem coe_orderedConeSpanBasis_apply (d : ℕ) (j : Fin (d + 1)) :
    ((orderedConeSpanBasis d j : Submodule.span ℝ (orderedCone d)) : Fin (d + 2) → ℝ) =
      orderedConeBasisVec d j := by simp [orderedConeSpanBasis]

/-! ### The open strictly increasing subcone -/

/-- The open positive strictly increasing subcone of `orderedConeHyperplane d`: positive strictly
increasing homogeneous tuples satisfying `y₀ + ⋯ + y_d = y_{d+1}`. -/
def strictOrderedCone (d : ℕ) : Set (Fin (d + 2) → ℝ) :=
  {y | (∀ i, 0 < y i) ∧ StrictMono y ∧ y ∈ orderedConeHyperplane d}

/-- Membership in `strictOrderedCone d` unfolded. -/
@[simp]
theorem mem_strictOrderedCone_iff {d : ℕ} {y : Fin (d + 2) → ℝ} :
    y ∈ strictOrderedCone d ↔
      (∀ i, 0 < y i) ∧ StrictMono y ∧ y ∈ orderedConeHyperplane d := Iff.rfl

/-- Every point of `strictOrderedCone d` belongs to `orderedCone d`. -/
theorem strictOrderedCone_subset_orderedCone (d : ℕ) :
    strictOrderedCone d ⊆ orderedCone d := fun y ⟨hypos, hystrict, hyhyp⟩ => by
  rw [mem_orderedCone_iff]
  refine ⟨fun h0 => ?_, fun i => (hypos i).le, hystrict.monotone,
    mem_orderedConeHyperplane_iff.mp hyhyp⟩
  linarith [hypos 0, show y 0 = 0 from congrFun h0 0]

/-- For `1 ≤ d`, `orderedSimplexLift (orderedSimplexInteriorPoint d)` belongs to
`strictOrderedCone d`. -/
theorem orderedSimplexLift_interiorPoint_mem_strictOrderedCone {d : ℕ} (hd : 1 ≤ d) :
    orderedSimplexLift (orderedSimplexInteriorPoint d) ∈ strictOrderedCone d := by
  have hlast_lt : 1 - ∑ k : Fin d, orderedSimplexInteriorPoint d k < 1 := by
    rw [one_sub_sum_orderedSimplexInteriorPoint, div_lt_iff₀ (by positivity)]
    linarith [show (1 : ℝ) ≤ d from Nat.one_le_cast.mpr hd]
  have hcs_pos : ∀ k : Fin (d + 1), 0 < chartToSimplex (orderedSimplexInteriorPoint d) k :=
    Fin.lastCases (by
        rw [chartToSimplex_last, one_sub_sum_orderedSimplexInteriorPoint]; positivity)
      fun i => by simpa using orderedSimplexInteriorPoint_pos i
  have hcs_mono : StrictMono (chartToSimplex (orderedSimplexInteriorPoint d)) := by
    intro a b hab
    induction a using Fin.lastCases with
    | last => exact absurd hab (not_lt_of_ge (Fin.le_last b))
    | cast i =>
      induction b using Fin.lastCases with
      | last => simpa using orderedSimplexInteriorPoint_lt_one_sub_sum i
      | cast j =>
        simpa using strictMono_orderedSimplexInteriorPoint d (Fin.castSucc_lt_castSucc_iff.mp hab)
  refine ⟨Fin.lastCases (by simp) fun k => by simpa using hcs_pos k, fun a b hab => ?_,
    mem_orderedConeHyperplane_iff.mpr (sum_castSucc_orderedSimplexLift _)⟩
  induction a using Fin.lastCases with
  | last => exact absurd hab (not_lt_of_ge (Fin.le_last b))
  | cast a' =>
    induction b using Fin.lastCases with
    | last => simpa using (hcs_mono.monotone (Fin.le_last a')).trans_lt (by simpa using hlast_lt)
    | cast b' => simpa using hcs_mono (Fin.castSucc_lt_castSucc_iff.mp hab)

end TauCeti.MarkoffHurwitz

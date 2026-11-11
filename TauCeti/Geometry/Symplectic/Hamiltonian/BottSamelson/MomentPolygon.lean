/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The moment polygon of the word121 Bott–Samelson incidence variety

Let `P₀ = span(e₁, e₂) ⊆ ℂ³` and let `X` be the smooth projective threefold of triples
`(L₁, P, L)` of lines `L₁, L` and a plane `P` in `ℂ³` with `L₁ ⊆ P₀`, `L₁ ⊆ P` and `L ⊆ P`, the
Bott–Samelson variety of the word `s₁ s₂ s₁`. For weights `a, b, c > 0` the diagonal torus
`T = (S¹)³` acts on `X` in a Hamiltonian way, with moment map
`μ = a diag(Π_L₁) + b diag(Π_P) + c diag(Π_L)`, the weighted diagonal of the three orthogonal
projectors. The action has exactly eight fixed points, the triples of coordinate subspaces allowed
by the incidence conditions. Writing `e_i` for the line `span(e_i)` and `ij` for `span(e_i, e_j)`,
their moment values (`TauCeti.BottSamelson.fixedMoment a b c k`, for `k : Fin 8` in this order) are

| `k` | `(L₁, P, L)` | `μ` |
| --- | --- | --- |
| 0 | `(e₁, 12, e₁)` | `(a+b+c, b, 0)` |
| 1 | `(e₁, 12, e₂)` | `(a+b, b+c, 0)` |
| 2 | `(e₁, 13, e₁)` | `(a+b+c, 0, b)` |
| 3 | `(e₁, 13, e₃)` | `(a+b, 0, b+c)` |
| 4 | `(e₂, 12, e₁)` | `(b+c, a+b, 0)` |
| 5 | `(e₂, 12, e₂)` | `(b, a+b+c, 0)` |
| 6 | `(e₂, 23, e₂)` | `(0, a+b+c, b)` |
| 7 | `(e₂, 23, e₃)` | `(0, a+b, b+c)` |

By the convexity theorem of Atiyah and Guillemin–Sternberg, the moment image `μ(X)` is the convex
hull of these eight values. This file computes that convex hull from the values alone; neither the
variety nor the convexity theorem is used. It is the hexagon

`x + y + z = a + 2b + c,  0 ≤ x ≤ a+b+c,  0 ≤ y ≤ a+b+c,  0 ≤ z ≤ b+c`

in the trace plane (`TauCeti.BottSamelson.convexHull_range_fixedMoment`). Each horizontal slice
`z = const` of the hexagon is a segment whose two endpoints lie on edges joining fixed values, which
gives every point of the hexagon as an explicit convex combination. The six vertices, in cyclic
order, are the values of rows `0, 2, 3, 7, 6, 5`
(`TauCeti.BottSamelson.extremePoints_convexHull_range_fixedMoment`): each is the unique maximum on
the hexagon of a difference of two coordinates. Each of the six inequalities cuts out the edge
joining two consecutive vertices (`TauCeti.BottSamelson.segment_fixedMoment_zero_two` and its
siblings).

The two remaining fixed values, of rows `1` and `4`, lie on the edge `z = 0` joining rows `0` and
`5`, with coefficients `c / (a + c)` and `a / (a + c)` of row `5`, strictly inside it when
`a, c > 0` (`TauCeti.BottSamelson.lineMap_fixedMoment_zero_five_eq_one`,
`TauCeti.BottSamelson.lineMap_fixedMoment_zero_five_eq_four`). These two values agree exactly when
`a = c` (`TauCeti.BottSamelson.fixedMoment_one_eq_four_iff`), and for positive weights all other
pairs of values are distinct (`TauCeti.BottSamelson.fixedMoment_eq_fixedMoment_iff`). So for
`a ≠ c` there are eight distinct fixed values and for `a = c` seven, but always six vertices: fixed
points of this complexity-one action are not identified with vertices of its moment polygon. The
fixed values are therefore recorded as a family indexed by the eight fixed points rather than as a
set, so that coinciding values keep their separate labels.

The convex hull, its vertices and its edges are computed for all nonnegative weights.

## Main definitions

* `TauCeti.BottSamelson.fixedMoment a b c`: the moment values of the eight torus-fixed points.

## Main results

* `TauCeti.BottSamelson.convexHull_range_fixedMoment`: the convex hull of the fixed values is the
  hexagon cut out by the six inequalities in the trace plane.
* `TauCeti.BottSamelson.extremePoints_convexHull_range_fixedMoment`: its extreme points are the
  values of rows `0, 2, 3, 5, 6, 7`, which are exposed points
  (`TauCeti.BottSamelson.fixedMoment_mem_exposedPoints`).
* `TauCeti.BottSamelson.segment_fixedMoment_zero_two`, `segment_fixedMoment_two_three`,
  `segment_fixedMoment_three_seven`, `segment_fixedMoment_seven_six`,
  `segment_fixedMoment_six_five`, `segment_fixedMoment_five_zero`: the six edges.
* `TauCeti.BottSamelson.fixedMoment_one_mem_openSegment`,
  `TauCeti.BottSamelson.fixedMoment_four_mem_openSegment`: rows `1` and `4` lie strictly inside the
  edge `z = 0`.
* `TauCeti.BottSamelson.fixedMoment_eq_fixedMoment_iff`,
  `TauCeti.BottSamelson.injective_fixedMoment_iff`: for positive weights, two fixed values agree
  only for equal rows or for rows `1` and `4` with `a = c`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 27.1 (the convexity theorem).
* L. Escobar, *Brick manifolds and toric varieties of brick polytopes*, Electron. J. Combin.
  **23** (2016), no. 2, Paper 2.25, Sections 3.2 and 4.1 (Bott–Samelson varieties as subvarieties
  of products of Grassmannians, and their moment polytopes).
-/

public section

noncomputable section

open Set

namespace TauCeti.BottSamelson

/-- The moment values `μ = a diag(Π_L₁) + b diag(Π_P) + c diag(Π_L)` of the eight torus-fixed
points `(L₁, P, L)` of the word121 Bott–Samelson incidence variety, in the order
`(e₁, 12, e₁)`, `(e₁, 12, e₂)`, `(e₁, 13, e₁)`, `(e₁, 13, e₃)`, `(e₂, 12, e₁)`, `(e₂, 12, e₂)`,
`(e₂, 23, e₂)`, `(e₂, 23, e₃)`, where `e_i` is the line `span(e_i)` and `ij` is the plane
`span(e_i, e_j)`. -/
def fixedMoment (a b c : ℝ) : Fin 8 → Fin 3 → ℝ :=
  ![![a + b + c, b, 0], ![a + b, b + c, 0], ![a + b + c, 0, b], ![a + b, 0, b + c],
    ![b + c, a + b, 0], ![b, a + b + c, 0], ![0, a + b + c, b], ![0, a + b, b + c]]

variable {a b c : ℝ}

@[simp] theorem fixedMoment_zero : fixedMoment a b c 0 = ![a + b + c, b, 0] := (rfl)

@[simp] theorem fixedMoment_one : fixedMoment a b c 1 = ![a + b, b + c, 0] := (rfl)

@[simp] theorem fixedMoment_two : fixedMoment a b c 2 = ![a + b + c, 0, b] := (rfl)

@[simp] theorem fixedMoment_three : fixedMoment a b c 3 = ![a + b, 0, b + c] := (rfl)

@[simp] theorem fixedMoment_four : fixedMoment a b c 4 = ![b + c, a + b, 0] := (rfl)

@[simp] theorem fixedMoment_five : fixedMoment a b c 5 = ![b, a + b + c, 0] := (rfl)

@[simp] theorem fixedMoment_six : fixedMoment a b c 6 = ![0, a + b + c, b] := (rfl)

@[simp] theorem fixedMoment_seven : fixedMoment a b c 7 = ![0, a + b, b + c] := (rfl)

/-- Every fixed value lies in the trace plane `x + y + z = a + 2b + c`. -/
theorem sum_fixedMoment (k : Fin 8) : ∑ i, fixedMoment a b c k i = a + 2 * b + c := by
  fin_cases k <;> simp [Fin.sum_univ_three] <;> ring

/-- The fixed values of `(e₁, 12, e₂)` and `(e₂, 12, e₁)` agree exactly when `a = c`. -/
theorem fixedMoment_one_eq_four_iff : fixedMoment a b c 1 = fixedMoment a b c 4 ↔ a = c := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congrFun h 0
    simp only [fixedMoment_one, fixedMoment_four, Matrix.cons_val_zero] at this
    linarith
  · subst h
    ext i
    fin_cases i <;> simp [add_comm]

/-- For positive weights, two fixed values agree only for equal rows, or for the rows
`(e₁, 12, e₂)` and `(e₂, 12, e₁)` when `a = c`. -/
theorem fixedMoment_eq_fixedMoment_iff (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {i j : Fin 8} :
    fixedMoment a b c i = fixedMoment a b c j ↔
      i = j ∨ a = c ∧ (i = 1 ∧ j = 4 ∨ i = 4 ∧ j = 1) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    fin_cases i <;> fin_cases j <;> simp at h0 h1 h2 ⊢ <;> linarith
  · rintro (rfl | ⟨hac, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · rfl
    · exact fixedMoment_one_eq_four_iff.2 hac
    · exact (fixedMoment_one_eq_four_iff.2 hac).symm

/-- For positive weights, the eight fixed values are distinct exactly when `a ≠ c`. -/
theorem injective_fixedMoment_iff (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Function.Injective (fixedMoment a b c) ↔ a ≠ c := by
  refine ⟨fun h hac ↦ absurd (h (fixedMoment_one_eq_four_iff.2 hac)) (by decide), fun hac i j hij ↦
    ?_⟩
  rcases (fixedMoment_eq_fixedMoment_iff ha hb hc).1 hij with h | ⟨h, -⟩
  exacts [h, absurd h hac]

/-- The fixed value of `(e₁, 12, e₂)` lies on the line through rows `0` and `5`, with coefficient
`c / (a + c)` of row `5`. -/
theorem lineMap_fixedMoment_zero_five_eq_one (hac : a + c ≠ 0) :
    AffineMap.lineMap (fixedMoment a b c 0) (fixedMoment a b c 5) (c / (a + c)) =
      fixedMoment a b c 1 := by
  ext i
  fin_cases i <;> simp [AffineMap.lineMap_apply_module] <;> field_simp <;> ring

/-- The fixed value of `(e₂, 12, e₁)` lies on the line through rows `0` and `5`, with coefficient
`a / (a + c)` of row `5`. -/
theorem lineMap_fixedMoment_zero_five_eq_four (hac : a + c ≠ 0) :
    AffineMap.lineMap (fixedMoment a b c 0) (fixedMoment a b c 5) (a / (a + c)) =
      fixedMoment a b c 4 := by
  ext i
  fin_cases i <;> simp [AffineMap.lineMap_apply_module] <;> field_simp <;> ring

/-- For `a, c > 0`, the fixed value of `(e₁, 12, e₂)` lies strictly inside the edge joining
rows `0` and `5`. -/
theorem fixedMoment_one_mem_openSegment (ha : 0 < a) (hc : 0 < c) :
    fixedMoment a b c 1 ∈ openSegment ℝ (fixedMoment a b c 0) (fixedMoment a b c 5) := by
  rw [openSegment_eq_image_lineMap]
  exact ⟨c / (a + c), ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩,
    lineMap_fixedMoment_zero_five_eq_one (by positivity)⟩

/-- For `a, c > 0`, the fixed value of `(e₂, 12, e₁)` lies strictly inside the edge joining
rows `0` and `5`. -/
theorem fixedMoment_four_mem_openSegment (ha : 0 < a) (hc : 0 < c) :
    fixedMoment a b c 4 ∈ openSegment ℝ (fixedMoment a b c 0) (fixedMoment a b c 5) := by
  rw [openSegment_eq_image_lineMap]
  exact ⟨a / (a + c), ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩,
    lineMap_fixedMoment_zero_five_eq_four (by positivity)⟩

/-- A point of the hexagon at height `z ≤ b` lies on the horizontal segment joining the edge from
row `5` to row `6` with the edge from row `0` to row `2`. -/
private theorem mem_convexHull_range_fixedMoment_of_apply_two_le (hb : 0 ≤ b) {x : Fin 3 → ℝ}
    (hs : x 0 + x 1 + x 2 = a + 2 * b + c) (hn : ∀ i, 0 ≤ x i) (h0 : x 0 ≤ a + b + c)
    (h1 : x 1 ≤ a + b + c) (hzb : x 2 ≤ b) :
    x ∈ convexHull ℝ (range (fixedMoment a b c)) := by
  have := hn 0
  have := hn 1
  have hx2 := hn 2
  have key : x 2 / b * b = x 2 := div_mul_cancel_of_imp fun h ↦ by linarith
  have ht : x 2 / b ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hx2 hb, div_le_one_of_le₀ hzb hb⟩
  have hl : ![b - x 2, a + b + c, x 2] ∈ convexHull ℝ (range (fixedMoment a b c)) := by
    refine segment_subset_convexHull (mem_range_self 5) (mem_range_self 6) ?_
    rw [segment_eq_image']
    refine ⟨x 2 / b, ht, ?_⟩
    ext i
    fin_cases i <;> simp <;> linarith
  have hr : ![a + b + c, b - x 2, x 2] ∈ convexHull ℝ (range (fixedMoment a b c)) := by
    refine segment_subset_convexHull (mem_range_self 0) (mem_range_self 2) ?_
    rw [segment_eq_image']
    refine ⟨x 2 / b, ht, ?_⟩
    ext i
    fin_cases i <;> simp <;> linarith
  set s := (x 0 - (b - x 2)) / (a + b + c - (b - x 2))
  have key' : s * (a + b + c - (b - x 2)) = x 0 - (b - x 2) :=
    div_mul_cancel_of_imp fun h ↦ by linarith
  refine (convex_convexHull ℝ _).segment_subset hl hr ?_
  rw [segment_eq_image']
  refine ⟨s, ⟨div_nonneg (by linarith) (by linarith),
    div_le_one_of_le₀ (by linarith) (by linarith)⟩, ?_⟩
  ext i
  fin_cases i <;> simp
  · linear_combination key'
  · linear_combination -key' - hs

/-- A point of the hexagon at height `z ≥ b` lies on the horizontal segment joining the edge from
row `6` to row `7` with the edge from row `2` to row `3`. -/
private theorem mem_convexHull_range_fixedMoment_of_le_apply_two (hc : 0 ≤ c) {x : Fin 3 → ℝ}
    (hs : x 0 + x 1 + x 2 = a + 2 * b + c) (hn : ∀ i, 0 ≤ x i) (h2 : x 2 ≤ b + c)
    (hbz : b ≤ x 2) :
    x ∈ convexHull ℝ (range (fixedMoment a b c)) := by
  have hx0 := hn 0
  have := hn 1
  have key : (x 2 - b) / c * c = x 2 - b := div_mul_cancel_of_imp fun h ↦ by linarith
  have ht : (x 2 - b) / c ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith) hc, div_le_one_of_le₀ (by linarith) hc⟩
  have hl : ![0, a + 2 * b + c - x 2, x 2] ∈ convexHull ℝ (range (fixedMoment a b c)) := by
    refine segment_subset_convexHull (mem_range_self 6) (mem_range_self 7) ?_
    rw [segment_eq_image']
    refine ⟨(x 2 - b) / c, ht, ?_⟩
    ext i
    fin_cases i <;> simp
    · linear_combination -key
    · linear_combination key
  have hr : ![a + 2 * b + c - x 2, 0, x 2] ∈ convexHull ℝ (range (fixedMoment a b c)) := by
    refine segment_subset_convexHull (mem_range_self 2) (mem_range_self 3) ?_
    rw [segment_eq_image']
    refine ⟨(x 2 - b) / c, ht, ?_⟩
    ext i
    fin_cases i <;> simp
    · linear_combination -key
    · linear_combination key
  set s := x 0 / (a + 2 * b + c - x 2)
  have key' : s * (a + 2 * b + c - x 2) = x 0 := div_mul_cancel_of_imp fun h ↦ by linarith
  refine (convex_convexHull ℝ _).segment_subset hl hr ?_
  rw [segment_eq_image']
  refine ⟨s, ⟨div_nonneg hx0 (by linarith), div_le_one_of_le₀ (by linarith) (by linarith)⟩, ?_⟩
  ext i
  fin_cases i <;> simp
  · linear_combination key'
  · linear_combination -key' - hs

/-- **The word121 moment polygon.** For nonnegative weights, the convex hull of the eight fixed
values is the hexagon `x + y + z = a + 2b + c`, `0 ≤ x ≤ a + b + c`, `0 ≤ y ≤ a + b + c`,
`0 ≤ z ≤ b + c`. -/
theorem convexHull_range_fixedMoment (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    convexHull ℝ (range (fixedMoment a b c)) =
      {x | x 0 + x 1 + x 2 = a + 2 * b + c ∧ (∀ i, 0 ≤ x i) ∧
        x 0 ≤ a + b + c ∧ x 1 ≤ a + b + c ∧ x 2 ≤ b + c} := by
  refine Subset.antisymm (convexHull_min ?_ ?_) ?_
  · rintro _ ⟨k, rfl⟩
    refine ⟨?_, fun i ↦ ?_, ?_, ?_, ?_⟩ <;> fin_cases k <;> (try fin_cases i) <;> simp <;> linarith
  · intro x ⟨hs, hn, h0, h1, h2⟩ y ⟨hs', hn', h0', h1', h2'⟩ s t hs0 ht0 hst
    simp only [mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine ⟨by linear_combination s * hs + t * hs' + (a + 2 * b + c) * hst,
      fun i ↦ by have := hn i; have := hn' i; positivity, ?_, ?_, ?_⟩ <;>
    nlinarith [mul_le_mul_of_nonneg_left h0 hs0, mul_le_mul_of_nonneg_left h0' ht0,
      mul_le_mul_of_nonneg_left h1 hs0, mul_le_mul_of_nonneg_left h1' ht0,
      mul_le_mul_of_nonneg_left h2 hs0, mul_le_mul_of_nonneg_left h2' ht0]
  · rintro x ⟨hs, hn, h0, h1, h2⟩
    rcases le_total (x 2) b with hzb | hbz
    · exact mem_convexHull_range_fixedMoment_of_apply_two_le hb hs hn h0 h1 hzb
    · exact mem_convexHull_range_fixedMoment_of_le_apply_two hc hs hn h2 hbz

/-- For nonnegative weights, the values of rows `0, 2, 3, 5, 6, 7` are exposed points of the convex
hull of the fixed values: each is the unique maximum on the hexagon of a difference of two
coordinates. -/
theorem fixedMoment_mem_exposedPoints (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) {k : Fin 8}
    (hk : k ∈ ({0, 2, 3, 5, 6, 7} : Set (Fin 8))) :
    fixedMoment a b c k ∈ (convexHull ℝ (range (fixedMoment a b c))).exposedPoints ℝ := by
  refine exposed_point_def.2 ⟨subset_convexHull ℝ _ (mem_range_self k), ?_⟩
  rw [convexHull_range_fixedMoment ha hb hc]
  obtain ⟨i, j, hij⟩ : ∃ i j : Fin 3, ∀ y ∈ {x : Fin 3 → ℝ | x 0 + x 1 + x 2 = a + 2 * b + c ∧
      (∀ i, 0 ≤ x i) ∧ x 0 ≤ a + b + c ∧ x 1 ≤ a + b + c ∧ x 2 ≤ b + c},
      y i - y j ≤ fixedMoment a b c k i - fixedMoment a b c k j ∧
        (fixedMoment a b c k i - fixedMoment a b c k j ≤ y i - y j → y = fixedMoment a b c k) := by
    simp only [mem_insert_iff, mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      [refine ⟨0, 2, ?_⟩; refine ⟨0, 1, ?_⟩; refine ⟨2, 1, ?_⟩; refine ⟨1, 2, ?_⟩;
        refine ⟨1, 0, ?_⟩; refine ⟨2, 0, ?_⟩] <;>
    · rintro y ⟨hs, hn, h0, h1, h2⟩
      have := hn 0
      have := hn 1
      have := hn 2
      refine ⟨by simp; linarith, fun h ↦ ?_⟩
      simp at h
      ext i
      fin_cases i <;> simp <;> linarith
  exact ⟨ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 ↦ ℝ) i -
    ContinuousLinearMap.proj j, fun y hy ↦ by simpa using hij y hy⟩

/-- **The vertices of the word121 moment polygon.** For nonnegative weights, the extreme points of
the convex hull of the fixed values are the values of rows `0, 2, 3, 5, 6, 7`. -/
theorem extremePoints_convexHull_range_fixedMoment (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (convexHull ℝ (range (fixedMoment a b c))).extremePoints ℝ =
      fixedMoment a b c '' {0, 2, 3, 5, 6, 7} := by
  have hmem (k : Fin 8) : fixedMoment a b c k ∈ convexHull ℝ (range (fixedMoment a b c)) :=
    subset_convexHull ℝ _ (mem_range_self k)
  refine Subset.antisymm (fun x hx ↦ ?_) ?_
  · obtain ⟨k, rfl⟩ := extremePoints_convexHull_subset hx
    by_cases hk : k ∈ ({0, 2, 3, 5, 6, 7} : Set (Fin 8))
    · exact mem_image_of_mem _ hk
    have hk' : k = 1 ∨ k = 4 := by fin_cases k <;> simp_all
    -- Rows `1` and `4` coincide with a vertex when `a = 0` or `c = 0`, and otherwise lie strictly
    -- inside the edge joining rows `0` and `5`.
    rcases ha.eq_or_lt with rfl | ha'
    · rcases hk' with rfl | rfl
      · exact ⟨5, by simp, by ext i; fin_cases i <;> simp⟩
      · exact ⟨0, by simp, by ext i; fin_cases i <;> simp⟩
    rcases hc.eq_or_lt with rfl | hc'
    · rcases hk' with rfl | rfl
      · exact ⟨0, by simp, by ext i; fin_cases i <;> simp⟩
      · exact ⟨5, by simp, by ext i; fin_cases i <;> simp⟩
    have h05 := fun h ↦ (mem_extremePoints_iff_left.1 hx).2 _ (hmem 0) _ (hmem 5) h
    rcases hk' with rfl | rfl
    · have := congrFun (h05 (fixedMoment_one_mem_openSegment ha' hc')) 0
      simp at this
      linarith
    · have := congrFun (h05 (fixedMoment_four_mem_openSegment ha' hc')) 1
      simp at this
      linarith
  · rintro _ ⟨k, hk, rfl⟩
    exact exposedPoints_subset_extremePoints (fixedMoment_mem_exposedPoints ha hb hc hk)

/-- The inequality `x ≤ a + b + c` cuts out the edge joining rows `0` and `2`. -/
theorem segment_fixedMoment_zero_two (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    segment ℝ (fixedMoment a b c 0) (fixedMoment a b c 2) =
      {x ∈ convexHull ℝ (range (fixedMoment a b c)) | x 0 = a + b + c} := by
  refine Subset.antisymm
    (fun x hx ↦ ⟨segment_subset_convexHull (mem_range_self _) (mem_range_self _) hx, ?_⟩) ?_
  · rw [segment_eq_image'] at hx
    obtain ⟨t, -, rfl⟩ := hx
    simp
  · rintro x ⟨hx, hxk⟩
    obtain ⟨hs, hn, h0, h1, h2⟩ := (convexHull_range_fixedMoment ha hb hc).subset hx
    have := hn 0
    have := hn 1
    have := hn 2
    have key : x 2 / b * b = x 2 := div_mul_cancel_of_imp fun h ↦ by linarith
    rw [segment_eq_image']
    refine ⟨x 2 / b, ⟨div_nonneg (by linarith) (by linarith),
      div_le_one_of_le₀ (by linarith) (by linarith)⟩, ?_⟩
    ext i
    fin_cases i <;> simp <;> linarith

/-- The inequality `0 ≤ y` cuts out the edge joining rows `2` and `3`. -/
theorem segment_fixedMoment_two_three (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    segment ℝ (fixedMoment a b c 2) (fixedMoment a b c 3) =
      {x ∈ convexHull ℝ (range (fixedMoment a b c)) | x 1 = 0} := by
  refine Subset.antisymm
    (fun x hx ↦ ⟨segment_subset_convexHull (mem_range_self _) (mem_range_self _) hx, ?_⟩) ?_
  · rw [segment_eq_image'] at hx
    obtain ⟨t, -, rfl⟩ := hx
    simp
  · rintro x ⟨hx, hxk⟩
    obtain ⟨hs, hn, h0, h1, h2⟩ := (convexHull_range_fixedMoment ha hb hc).subset hx
    have := hn 0
    have := hn 1
    have := hn 2
    have key : (x 2 - b) / c * c = x 2 - b := div_mul_cancel_of_imp fun h ↦ by linarith
    rw [segment_eq_image']
    refine ⟨(x 2 - b) / c, ⟨div_nonneg (by linarith) (by linarith),
      div_le_one_of_le₀ (by linarith) (by linarith)⟩, ?_⟩
    ext i
    fin_cases i <;> simp <;> linarith

/-- The inequality `z ≤ b + c` cuts out the edge joining rows `3` and `7`. -/
theorem segment_fixedMoment_three_seven (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    segment ℝ (fixedMoment a b c 3) (fixedMoment a b c 7) =
      {x ∈ convexHull ℝ (range (fixedMoment a b c)) | x 2 = b + c} := by
  refine Subset.antisymm
    (fun x hx ↦ ⟨segment_subset_convexHull (mem_range_self _) (mem_range_self _) hx, ?_⟩) ?_
  · rw [segment_eq_image'] at hx
    obtain ⟨t, -, rfl⟩ := hx
    simp
  · rintro x ⟨hx, hxk⟩
    obtain ⟨hs, hn, h0, h1, h2⟩ := (convexHull_range_fixedMoment ha hb hc).subset hx
    have := hn 0
    have := hn 1
    have := hn 2
    have key : x 1 / (a + b) * (a + b) = x 1 := div_mul_cancel_of_imp fun h ↦ by linarith
    rw [segment_eq_image']
    refine ⟨x 1 / (a + b), ⟨div_nonneg (by linarith) (by linarith),
      div_le_one_of_le₀ (by linarith) (by linarith)⟩, ?_⟩
    ext i
    fin_cases i <;> simp <;> linarith

/-- The inequality `0 ≤ x` cuts out the edge joining rows `7` and `6`. -/
theorem segment_fixedMoment_seven_six (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    segment ℝ (fixedMoment a b c 7) (fixedMoment a b c 6) =
      {x ∈ convexHull ℝ (range (fixedMoment a b c)) | x 0 = 0} := by
  refine Subset.antisymm
    (fun x hx ↦ ⟨segment_subset_convexHull (mem_range_self _) (mem_range_self _) hx, ?_⟩) ?_
  · rw [segment_eq_image'] at hx
    obtain ⟨t, -, rfl⟩ := hx
    simp
  · rintro x ⟨hx, hxk⟩
    obtain ⟨hs, hn, h0, h1, h2⟩ := (convexHull_range_fixedMoment ha hb hc).subset hx
    have := hn 0
    have := hn 1
    have := hn 2
    have key : (x 1 - (a + b)) / c * c = x 1 - (a + b) := div_mul_cancel_of_imp fun h ↦ by linarith
    rw [segment_eq_image']
    refine ⟨(x 1 - (a + b)) / c, ⟨div_nonneg (by linarith) (by linarith),
      div_le_one_of_le₀ (by linarith) (by linarith)⟩, ?_⟩
    ext i
    fin_cases i <;> simp <;> linarith

/-- The inequality `y ≤ a + b + c` cuts out the edge joining rows `6` and `5`. -/
theorem segment_fixedMoment_six_five (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    segment ℝ (fixedMoment a b c 6) (fixedMoment a b c 5) =
      {x ∈ convexHull ℝ (range (fixedMoment a b c)) | x 1 = a + b + c} := by
  refine Subset.antisymm
    (fun x hx ↦ ⟨segment_subset_convexHull (mem_range_self _) (mem_range_self _) hx, ?_⟩) ?_
  · rw [segment_eq_image'] at hx
    obtain ⟨t, -, rfl⟩ := hx
    simp
  · rintro x ⟨hx, hxk⟩
    obtain ⟨hs, hn, h0, h1, h2⟩ := (convexHull_range_fixedMoment ha hb hc).subset hx
    have := hn 0
    have := hn 1
    have := hn 2
    have key : x 0 / b * b = x 0 := div_mul_cancel_of_imp fun h ↦ by linarith
    rw [segment_eq_image']
    refine ⟨x 0 / b, ⟨div_nonneg (by linarith) (by linarith),
      div_le_one_of_le₀ (by linarith) (by linarith)⟩, ?_⟩
    ext i
    fin_cases i <;> simp <;> linarith

/-- The inequality `0 ≤ z` cuts out the edge joining rows `5` and `0`. -/
theorem segment_fixedMoment_five_zero (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    segment ℝ (fixedMoment a b c 5) (fixedMoment a b c 0) =
      {x ∈ convexHull ℝ (range (fixedMoment a b c)) | x 2 = 0} := by
  refine Subset.antisymm
    (fun x hx ↦ ⟨segment_subset_convexHull (mem_range_self _) (mem_range_self _) hx, ?_⟩) ?_
  · rw [segment_eq_image'] at hx
    obtain ⟨t, -, rfl⟩ := hx
    simp
  · rintro x ⟨hx, hxk⟩
    obtain ⟨hs, hn, h0, h1, h2⟩ := (convexHull_range_fixedMoment ha hb hc).subset hx
    have := hn 0
    have := hn 1
    have := hn 2
    have key : (x 0 - b) / (a + c) * (a + c) = x 0 - b := div_mul_cancel_of_imp fun h ↦ by linarith
    rw [segment_eq_image']
    refine ⟨(x 0 - b) / (a + c), ⟨div_nonneg (by linarith) (by linarith),
      div_le_one_of_le₀ (by linarith) (by linarith)⟩, ?_⟩
    ext i
    fin_cases i <;> simp <;> linarith

end TauCeti.BottSamelson

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Topology.Algebra.Ring.Real

import TauCeti.Analysis.Convex.Segment
import Mathlib.Data.Fintype.Perm
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# The moment hexagon of the word `121` Bott–Samelson manifold

Let `X = {(L₁, P, L) : L₁ ⊂ span(e₁, e₂), L₁ ⊂ P, L ⊂ P}` be the Bott–Samelson manifold of the
word `121` in the flag manifold of `ℂ³`, with `L₁, L` lines and `P` a plane. For weights
`a, b, c > 0`, the diagonal torus `T = (S¹)³` acts on `X` with moment map
`(L₁, P, L) ↦ diag(a Π_L₁ + b Π_P + c Π_L)`, where `Π_V` is the orthogonal projector onto `V`.
It has eight fixed points, the triples of coordinate subspaces satisfying the incidences. Writing
`ij` for `span(e_i, e_j)`, their moment values are the eight rows

| row | `(L₁, P, L)` | value |
| --- | --- | --- |
| 1 | `(e₁, 12, e₁)` | `(a + b + c, b, 0)` |
| 2 | `(e₁, 12, e₂)` | `(a + b, b + c, 0)` |
| 3 | `(e₁, 13, e₁)` | `(a + b + c, 0, b)` |
| 4 | `(e₁, 13, e₃)` | `(a + b, 0, b + c)` |
| 5 | `(e₂, 12, e₁)` | `(b + c, a + b, 0)` |
| 6 | `(e₂, 12, e₂)` | `(b, a + b + c, 0)` |
| 7 | `(e₂, 23, e₂)` | `(0, a + b + c, b)` |
| 8 | `(e₂, 23, e₃)` | `(0, a + b, b + c)` |

(`TauCeti.BottSamelson.fixedMoment a b c`, indexed by `Fin 8`, so that row `k + 1` is
`fixedMoment a b c k`). By the convexity theorem for torus actions, the moment image of `X` is
the convex hull of these values. This file computes that convex hull: it is the hexagon

`x + y + z = a + 2b + c`, `0 ≤ x, y, z`, `x ≤ a + b + c`, `y ≤ a + b + c`, `z ≤ b + c`

(`TauCeti.BottSamelson.momentPolygon a b c`,
`TauCeti.BottSamelson.convexHull_range_fixedMoment`), lying in the affine plane of trace
`a + 2b + c` in which the moment map of the effective two-torus takes values. Its six vertices,
in cyclic order, are the rows `1, 3, 4, 8, 7, 6`
(`TauCeti.BottSamelson.extremePoints_momentPolygon`), and each of the six inequalities cuts out
the edge between two cyclically consecutive vertices. The remaining rows `2` and `5` lie strictly
inside the edge `z = 0` from row `1` to row `6`, as the points with parameters `c / (a + c)` and
`a / (a + c)` on it (`TauCeti.BottSamelson.fixedMoment_one_eq_lineMap`,
`TauCeti.BottSamelson.fixedMoment_four_eq_lineMap`). They coincide exactly when `a = c`, and these
are the only coincidences: there are eight distinct fixed values when `a ≠ c` and seven when
`a = c` (`TauCeti.BottSamelson.ncard_range_fixedMoment`), but always six vertices. So the
fixed points of this complexity-one action are not the vertices of its moment polygon, unlike for
a symplectic toric manifold.

The table is symmetric under exchanging `e₁` and `e₂`, which swaps the first two coordinates of
the values and relabels the fixed points by the involution `TauCeti.BottSamelson.fixedSwap`.
When `a = 0` the rows are the six rearrangements of `(b + c, b, 0)`
(`TauCeti.BottSamelson.range_fixedMoment_zero_left`), the vertices of the permutohedron that is the
moment image of the flag manifold for the eigenvalues `(b + c, b, 0)`.

The hexagon and its vertices are statements about the eight values alone, and they hold for all
nonnegative weights, where the hexagon may degenerate.

## Main definitions

* `TauCeti.BottSamelson.fixedMoment a b c`: the eight fixed values.
* `TauCeti.BottSamelson.momentPolygon a b c`: the hexagon cut out by the six inequalities.
* `TauCeti.BottSamelson.fixedSwap`: the relabeling of the fixed points by `e₁ ↔ e₂`.

## Main results

* `TauCeti.BottSamelson.convexHull_range_fixedMoment`: the convex hull of the fixed values is the
  hexagon.
* `TauCeti.BottSamelson.extremePoints_momentPolygon`,
  `TauCeti.BottSamelson.exposedPoints_momentPolygon`: its vertices are the rows `1, 3, 4, 8, 7, 6`.
* `TauCeti.BottSamelson.momentPolygon_inter_eq_segment_zero_two` and its five companions: each
  inequality cuts out an edge.
* `TauCeti.BottSamelson.fixedMoment_one_mem_openSegment`,
  `TauCeti.BottSamelson.fixedMoment_four_mem_openSegment`: rows `2` and `5` lie inside an edge.
* `TauCeti.BottSamelson.fixedMoment_eq_fixedMoment_iff`,
  `TauCeti.BottSamelson.ncard_range_fixedMoment`: rows `2` and `5` are the only rows that can
  coincide, exactly when `a = c`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 27.1 (convexity of the moment image of a torus action).
* L. Escobar, *Brick manifolds and toric varieties of brick polytopes*, Electronic Journal of
  Combinatorics 23(2) (2016), #P2.25, Sections 3.2 and 4.1 (Bott–Samelson manifolds as incidence
  varieties in products of Grassmannians, and their moment images).
-/

public section

noncomputable section

open Set

namespace TauCeti.BottSamelson

variable {a b c : ℝ}

/-- The moment values of the eight torus-fixed points of the word `121` Bott–Samelson manifold,
for the weights `a`, `b`, `c` of its three factors. Row `k + 1` of the table in the module
docstring is `fixedMoment a b c k`; the fixed points remain labeled by `Fin 8` even when two of
their values coincide. -/
def fixedMoment (a b c : ℝ) : Fin 8 → Fin 3 → ℝ :=
  ![![a + b + c, b, 0], ![a + b, b + c, 0], ![a + b + c, 0, b], ![a + b, 0, b + c],
    ![b + c, a + b, 0], ![b, a + b + c, 0], ![0, a + b + c, b], ![0, a + b, b + c]]

/-- The table of fixed values, as an explicit vector of vectors. -/
theorem fixedMoment_def (a b c : ℝ) :
    fixedMoment a b c =
      ![![a + b + c, b, 0], ![a + b, b + c, 0], ![a + b + c, 0, b], ![a + b, 0, b + c],
        ![b + c, a + b, 0], ![b, a + b + c, 0], ![0, a + b + c, b], ![0, a + b, b + c]] :=
  (rfl)

/-- Every fixed value lies in the affine plane of trace `a + 2b + c`. -/
@[simp]
theorem sum_fixedMoment (k : Fin 8) : ∑ i, fixedMoment a b c k i = a + 2 * b + c := by
  fin_cases k <;> simp [fixedMoment, Fin.sum_univ_three] <;> ring

/-- The fixed values are additive in the weights. -/
theorem fixedMoment_add (a b c a' b' c' : ℝ) :
    fixedMoment (a + a') (b + b') (c + c') = fixedMoment a b c + fixedMoment a' b' c' := by
  ext k i
  fin_cases k <;> fin_cases i <;> simp [fixedMoment] <;> ring

/-- The fixed values are homogeneous in the weights. -/
theorem fixedMoment_mul (t a b c : ℝ) :
    fixedMoment (t * a) (t * b) (t * c) = t • fixedMoment a b c := by
  ext k i
  fin_cases k <;> fin_cases i <;> simp [fixedMoment] <;> ring

/-! ### The symmetry exchanging `e₁` and `e₂` -/

/-- The involution of the fixed points induced by exchanging `e₁` and `e₂`: it exchanges the rows
`1 ↔ 6`, `2 ↔ 5`, `3 ↔ 7` and `4 ↔ 8` of the table, that is the indices `0 ↔ 5`, `1 ↔ 4`,
`2 ↔ 6` and `3 ↔ 7`. -/
def fixedSwap : Equiv.Perm (Fin 8) :=
  Function.Involutive.toPerm ![5, 4, 6, 7, 1, 0, 2, 3] fun k ↦ by fin_cases k <;> rfl

theorem fixedSwap_apply (k : Fin 8) : fixedSwap k = ![5, 4, 6, 7, 1, 0, 2, 3] k :=
  (rfl)

@[simp]
theorem fixedSwap_fixedSwap (k : Fin 8) : fixedSwap (fixedSwap k) = k := by
  fin_cases k <;> rfl

@[simp]
theorem fixedSwap_symm : fixedSwap.symm = fixedSwap :=
  (rfl)

/-- Relabeling the fixed points by `fixedSwap` swaps the first two coordinates of their values. -/
@[simp]
theorem fixedMoment_fixedSwap (k : Fin 8) :
    fixedMoment a b c (fixedSwap k) = fixedMoment a b c k ∘ Equiv.swap 0 1 := by
  ext i
  fin_cases k <;> fin_cases i <;> rfl

/-! ### Coincidences among the fixed values -/

/-- Rows `2` and `5` have the same value exactly when `a = c`. -/
theorem fixedMoment_one_eq_fixedMoment_four_iff :
    fixedMoment a b c 1 = fixedMoment a b c 4 ↔ a = c := by
  constructor
  · intro h
    have := congrFun h 0
    simp only [fixedMoment_def, Matrix.cons_val] at this
    linarith
  · rintro rfl
    ext i
    fin_cases i <;> simp [fixedMoment_def] <;> ring

/-- For positive weights, the only coincidence among the fixed values is that of rows `2` and `5`
when `a = c`. -/
theorem fixedMoment_eq_fixedMoment_iff (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {i j : Fin 8} :
    fixedMoment a b c i = fixedMoment a b c j ↔
      i = j ∨ a = c ∧ (i = 1 ∧ j = 4 ∨ i = 4 ∧ j = 1) := by
  constructor
  · intro h
    have h₀ := congrFun h 0
    have h₁ := congrFun h 1
    have h₂ := congrFun h 2
    fin_cases i <;> fin_cases j <;> simp [fixedMoment_def] at h₀ h₁ h₂ ⊢ <;> linarith
  · rintro (rfl | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩)
    · rfl
    · exact fixedMoment_one_eq_fixedMoment_four_iff.2 rfl
    · exact (fixedMoment_one_eq_fixedMoment_four_iff.2 rfl).symm

/-- For positive weights with `a ≠ c`, the eight fixed values are distinct. -/
theorem fixedMoment_injective (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hac : a ≠ c) :
    Function.Injective (fixedMoment a b c) := fun i j h ↦ by
  simpa [hac] using (fixedMoment_eq_fixedMoment_iff ha hb hc).1 h

/-- For positive weights there are eight distinct fixed values when `a ≠ c`, and seven when
`a = c`. -/
theorem ncard_range_fixedMoment (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (range (fixedMoment a b c)).ncard = if a = c then 7 else 8 := by
  split_ifs with hac
  · -- Row `5` repeats row `2`, so the other seven rows have the same values.
    have hrange :
        range (fixedMoment a b c ∘ (4 : Fin 8).succAbove) = range (fixedMoment a b c) := by
      refine (range_comp_subset_range _ _).antisymm ?_
      rintro _ ⟨k, rfl⟩
      by_cases hk : k = 4
      · subst hk
        exact ⟨1, fixedMoment_one_eq_fixedMoment_four_iff.2 hac⟩
      · obtain ⟨z, rfl⟩ := Fin.exists_succAbove_eq hk
        exact ⟨z, rfl⟩
    rw [← hrange, ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
    intro i j h
    have := (fixedMoment_eq_fixedMoment_iff ha hb hc).1 h
    rcases this with h | ⟨-, ⟨-, h₁⟩ | ⟨h₁, -⟩⟩
    · exact Fin.succAbove_right_injective h
    · exact absurd h₁ (Fin.succAbove_ne _ _)
    · exact absurd h₁ (Fin.succAbove_ne _ _)
  · rw [ncard_range_of_injective (fixedMoment_injective ha hb hc hac), Nat.card_eq_fintype_card,
      Fintype.card_fin]

/-- When `a = 0`, the fixed values are the six rearrangements of `(b + c, b, 0)`. -/
theorem range_fixedMoment_zero_left (b c : ℝ) :
    range (fixedMoment 0 b c) = range fun σ : Equiv.Perm (Fin 3) ↦ ![b + c, b, 0] ∘ σ := by
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨k, rfl⟩
    fin_cases k
    exacts [⟨1, by ext i; fin_cases i <;> simp [fixedMoment_def]⟩,
      ⟨Equiv.swap 0 1, by ext i; fin_cases i <;> simp [fixedMoment_def, Equiv.swap_apply_def]⟩,
      ⟨Equiv.swap 1 2, by ext i; fin_cases i <;> simp [fixedMoment_def, Equiv.swap_apply_def]⟩,
      ⟨Equiv.swap 0 1 * Equiv.swap 1 2,
        by ext i; fin_cases i <;> simp [fixedMoment_def, Equiv.swap_apply_def]⟩,
      ⟨1, by ext i; fin_cases i <;> simp [fixedMoment_def]⟩,
      ⟨Equiv.swap 0 1, by ext i; fin_cases i <;> simp [fixedMoment_def, Equiv.swap_apply_def]⟩,
      ⟨Equiv.swap 1 2 * Equiv.swap 0 1,
        by ext i; fin_cases i <;> simp [fixedMoment_def, Equiv.swap_apply_def]⟩,
      ⟨Equiv.swap 0 2, by ext i; fin_cases i <;> simp [fixedMoment_def, Equiv.swap_apply_def]⟩]
  · rintro _ ⟨σ, rfl⟩
    have : σ = 1 ∨ σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 1 2 ∨ σ = Equiv.swap 0 1 * Equiv.swap 1 2 ∨
        σ = Equiv.swap 1 2 * Equiv.swap 0 1 ∨ σ = Equiv.swap 0 2 := by
      revert σ
      decide
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨0, by ext i; fin_cases i <;> simp [fixedMoment_def]⟩,
      ⟨1, by ext i; fin_cases i <;> simp [fixedMoment_def, Equiv.swap_apply_def]⟩,
      ⟨2, by ext i; fin_cases i <;> simp [fixedMoment_def, Equiv.swap_apply_def]⟩,
      ⟨3, by ext i; fin_cases i <;> simp [fixedMoment_def, Equiv.swap_apply_def]⟩,
      ⟨6, by ext i; fin_cases i <;> simp [fixedMoment_def, Equiv.swap_apply_def]⟩,
      ⟨7, by ext i; fin_cases i <;> simp [fixedMoment_def, Equiv.swap_apply_def]⟩]

/-! ### The moment hexagon -/

/-- The hexagon `x + y + z = a + 2b + c`, `0 ≤ x, y, z`, `x ≤ a + b + c`, `y ≤ a + b + c`,
`z ≤ b + c` in the affine plane of trace `a + 2b + c`. For nonnegative weights it is the convex
hull of the fixed values (`TauCeti.BottSamelson.convexHull_range_fixedMoment`). -/
def momentPolygon (a b c : ℝ) : Set (Fin 3 → ℝ) :=
  {x | x 0 + x 1 + x 2 = a + 2 * b + c ∧ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 ∧ x 0 ≤ a + b + c ∧
    x 1 ≤ a + b + c ∧ x 2 ≤ b + c}

@[simp]
theorem mem_momentPolygon {x : Fin 3 → ℝ} :
    x ∈ momentPolygon a b c ↔ x 0 + x 1 + x 2 = a + 2 * b + c ∧ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ 0 ≤ x 2 ∧
      x 0 ≤ a + b + c ∧ x 1 ≤ a + b + c ∧ x 2 ≤ b + c :=
  Iff.rfl

/-- The hexagon is convex, as an intersection of half-spaces with a hyperplane. -/
theorem convex_momentPolygon : Convex ℝ (momentPolygon a b c) := by
  rintro x ⟨hx, hx₀, hx₁, hx₂, hx₃, hx₄, hx₅⟩ y ⟨hy, hy₀, hy₁, hy₂, hy₃, hy₄, hy₅⟩ s t hs ht hst
  simp only [mem_momentPolygon, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨by linear_combination s * hx + t * hy + (a + 2 * b + c) * hst, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left hx₃ hs, mul_le_mul_of_nonneg_left hy₃ ht]
  · nlinarith [mul_le_mul_of_nonneg_left hx₄ hs, mul_le_mul_of_nonneg_left hy₄ ht]
  · nlinarith [mul_le_mul_of_nonneg_left hx₅ hs, mul_le_mul_of_nonneg_left hy₅ ht]

/-- For nonnegative weights, every fixed value lies in the hexagon. -/
theorem fixedMoment_mem_momentPolygon (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (k : Fin 8) :
    fixedMoment a b c k ∈ momentPolygon a b c := by
  fin_cases k <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [fixedMoment_def] <;> linarith

/-! ### The edges of the hexagon -/

/-- The segment between two fixed values lying on a coordinate hyperplane lies in the edge that
the hyperplane cuts out of the hexagon. -/
private theorem segment_subset_momentPolygon_inter (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    {i j : Fin 8} {l : Fin 3} {m : ℝ} (hi : fixedMoment a b c i l = m)
    (hj : fixedMoment a b c j l = m) :
    segment ℝ (fixedMoment a b c i) (fixedMoment a b c j) ⊆
      momentPolygon a b c ∩ {x | x l = m} := by
  have hconv : Convex ℝ (momentPolygon a b c ∩ {x | x l = m}) :=
    convex_momentPolygon.inter
      (convex_hyperplane (f := fun x : Fin 3 → ℝ ↦ x l) (LinearMap.proj (R := ℝ) l).isLinear m)
  exact hconv.segment_subset ⟨fixedMoment_mem_momentPolygon ha hb hc i, hi⟩
    ⟨fixedMoment_mem_momentPolygon ha hb hc j, hj⟩

/-- The inequality `x ≤ a + b + c` cuts out the edge from row `1` to row `3`. -/
theorem momentPolygon_inter_eq_segment_zero_two (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    momentPolygon a b c ∩ {x | x 0 = a + b + c} =
      segment ℝ (fixedMoment a b c 0) (fixedMoment a b c 2) := by
  refine Subset.antisymm ?_ (segment_subset_momentPolygon_inter ha hb hc rfl rfl)
  rintro x ⟨⟨hx, -, hx₁, hx₂, -⟩, hx₀ : x 0 = _⟩
  convert add_smul_mem_segment (p := ![a + b + c, b, 0]) (v := ![0, -1, 1]) (t := x 2)
    (t₀ := 0) (t₁ := b) (Icc_subset_uIcc ⟨hx₂, by linarith⟩) using 2 <;>
    ext k <;> fin_cases k <;> simp [fixedMoment_def] <;> linarith

/-- The inequality `0 ≤ y` cuts out the edge from row `3` to row `4`. -/
theorem momentPolygon_inter_eq_segment_two_three (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    momentPolygon a b c ∩ {x | x 1 = 0} =
      segment ℝ (fixedMoment a b c 2) (fixedMoment a b c 3) := by
  refine Subset.antisymm ?_ (segment_subset_momentPolygon_inter ha hb hc rfl rfl)
  rintro x ⟨⟨hx, -, -, -, hx₃, -, hx₅⟩, hx₁ : x 1 = _⟩
  convert add_smul_mem_segment (p := ![a + 2 * b + c, 0, 0]) (v := ![-1, 0, 1]) (t := x 2)
    (t₀ := b) (t₁ := b + c) (Icc_subset_uIcc ⟨by linarith, hx₅⟩) using 2 <;>
    ext k <;> fin_cases k <;> simp [fixedMoment_def] <;> linarith

/-- The inequality `z ≤ b + c` cuts out the edge from row `4` to row `8`. -/
theorem momentPolygon_inter_eq_segment_three_seven (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    momentPolygon a b c ∩ {x | x 2 = b + c} =
      segment ℝ (fixedMoment a b c 3) (fixedMoment a b c 7) := by
  refine Subset.antisymm ?_ (segment_subset_momentPolygon_inter ha hb hc rfl rfl)
  rintro x ⟨⟨hx, hx₀, hx₁, -⟩, hx₂ : x 2 = _⟩
  convert add_smul_mem_segment (p := ![0, a + b, b + c]) (v := ![1, -1, 0]) (t := x 0)
    (t₀ := a + b) (t₁ := 0) (Icc_subset_uIcc' ⟨hx₀, by linarith⟩) using 2 <;>
    ext k <;> fin_cases k <;> simp [fixedMoment_def] <;> linarith

/-- The inequality `0 ≤ x` cuts out the edge from row `8` to row `7`. -/
theorem momentPolygon_inter_eq_segment_seven_six (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    momentPolygon a b c ∩ {x | x 0 = 0} =
      segment ℝ (fixedMoment a b c 7) (fixedMoment a b c 6) := by
  refine Subset.antisymm ?_ (segment_subset_momentPolygon_inter ha hb hc rfl rfl)
  rintro x ⟨⟨hx, -, -, -, -, hx₄, hx₅⟩, hx₀ : x 0 = _⟩
  convert add_smul_mem_segment (p := ![0, a + 2 * b + c, 0]) (v := ![0, -1, 1]) (t := x 2)
    (t₀ := b + c) (t₁ := b) (Icc_subset_uIcc' ⟨by linarith, hx₅⟩) using 2 <;>
    ext k <;> fin_cases k <;> simp [fixedMoment_def] <;> linarith

/-- The inequality `y ≤ a + b + c` cuts out the edge from row `7` to row `6`. -/
theorem momentPolygon_inter_eq_segment_six_five (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    momentPolygon a b c ∩ {x | x 1 = a + b + c} =
      segment ℝ (fixedMoment a b c 6) (fixedMoment a b c 5) := by
  refine Subset.antisymm ?_ (segment_subset_momentPolygon_inter ha hb hc rfl rfl)
  rintro x ⟨⟨hx, hx₀, -, hx₂, -⟩, hx₁ : x 1 = _⟩
  convert add_smul_mem_segment (p := ![0, a + b + c, b]) (v := ![1, 0, -1]) (t := x 0)
    (t₀ := 0) (t₁ := b) (Icc_subset_uIcc ⟨hx₀, by linarith⟩) using 2 <;>
    ext k <;> fin_cases k <;> simp [fixedMoment_def] <;> linarith

/-- The inequality `0 ≤ z` cuts out the edge from row `6` to row `1`. -/
theorem momentPolygon_inter_eq_segment_five_zero (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    momentPolygon a b c ∩ {x | x 2 = 0} =
      segment ℝ (fixedMoment a b c 5) (fixedMoment a b c 0) := by
  refine Subset.antisymm ?_ (segment_subset_momentPolygon_inter ha hb hc rfl rfl)
  rintro x ⟨⟨hx, -, -, -, hx₃, hx₄, -⟩, hx₂ : x 2 = _⟩
  convert add_smul_mem_segment (p := ![0, a + 2 * b + c, 0]) (v := ![1, -1, 0]) (t := x 0)
    (t₀ := b) (t₁ := a + b + c) (Icc_subset_uIcc ⟨by linarith, hx₃⟩) using 2 <;>
    ext k <;> fin_cases k <;> simp [fixedMoment_def] <;> linarith

/-! ### The convex hull of the fixed values -/

/-- **The moment hexagon of the word `121` Bott–Samelson manifold.** For nonnegative weights, the
convex hull of the eight fixed values is the hexagon
`x + y + z = a + 2b + c`, `0 ≤ x, y, z`, `x ≤ a + b + c`, `y ≤ a + b + c`, `z ≤ b + c`. -/
theorem convexHull_range_fixedMoment (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    convexHull ℝ (range (fixedMoment a b c)) = momentPolygon a b c := by
  refine (convexHull_min ?_ convex_momentPolygon).antisymm fun x hx ↦ ?_
  · rintro _ ⟨k, rfl⟩
    exact fixedMoment_mem_momentPolygon ha hb hc k
  -- Each point of the hexagon lies on the segment through it on which `z` is constant, between
  -- two endpoints on the boundary; each endpoint lies on an edge, a segment between two fixed
  -- values.
  have hedge : ∀ {i j : Fin 8} {y : Fin 3 → ℝ},
      y ∈ segment ℝ (fixedMoment a b c i) (fixedMoment a b c j) →
        y ∈ convexHull ℝ (range (fixedMoment a b c)) := fun hy ↦
    segment_subset_convexHull (mem_range_self _) (mem_range_self _) hy
  obtain ⟨hx, hx₀, hx₁, hx₂, hx₃, hx₄, hx₅⟩ := hx
  rcases le_total (x 2) b with hz | hz
  · -- The endpoints lie on the edges `y = a + b + c` and `x = a + b + c`.
    have hp : ![b - x 2, a + b + c, x 2] ∈ convexHull ℝ (range (fixedMoment a b c)) :=
      hedge <| (momentPolygon_inter_eq_segment_six_five ha hb hc).le
        (by
          refine ⟨mem_momentPolygon.2 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
            simp only [Matrix.cons_val, mem_ofPred_eq] <;> linarith)
    have hq : ![a + b + c, b - x 2, x 2] ∈ convexHull ℝ (range (fixedMoment a b c)) :=
      hedge <| (momentPolygon_inter_eq_segment_zero_two ha hb hc).le
        (by
          refine ⟨mem_momentPolygon.2 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
            simp only [Matrix.cons_val, mem_ofPred_eq] <;> linarith)
    refine (convex_convexHull ℝ _).segment_subset hp hq ?_
    convert add_smul_mem_segment (p := ![0, a + 2 * b + c - x 2, x 2]) (v := ![1, -1, 0])
      (t := x 0) (t₀ := b - x 2) (t₁ := a + b + c) (Icc_subset_uIcc ⟨by linarith, hx₃⟩)
      using 2 <;>
      ext k <;> fin_cases k <;> simp <;> linarith
  · -- The endpoints lie on the edges `x = 0` and `y = 0`.
    have hp : ![0, a + 2 * b + c - x 2, x 2] ∈ convexHull ℝ (range (fixedMoment a b c)) :=
      hedge <| (momentPolygon_inter_eq_segment_seven_six ha hb hc).le
        (by
          refine ⟨mem_momentPolygon.2 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
            simp only [Matrix.cons_val, mem_ofPred_eq] <;> linarith)
    have hq : ![a + 2 * b + c - x 2, 0, x 2] ∈ convexHull ℝ (range (fixedMoment a b c)) :=
      hedge <| (momentPolygon_inter_eq_segment_two_three ha hb hc).le
        (by
          refine ⟨mem_momentPolygon.2 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
            simp only [Matrix.cons_val, mem_ofPred_eq] <;> linarith)
    refine (convex_convexHull ℝ _).segment_subset hp hq ?_
    convert add_smul_mem_segment (p := ![0, a + 2 * b + c - x 2, x 2]) (v := ![1, -1, 0])
      (t := x 0) (t₀ := 0) (t₁ := a + 2 * b + c - x 2) (Icc_subset_uIcc ⟨hx₀, by linarith⟩)
      using 2 <;>
      ext k <;> fin_cases k <;> simp
    -- Only the `y`-coordinate of `x` needs the trace condition.
    linarith

/-! ### The vertices of the hexagon -/

/-- A point of the hexagon at which a difference of two coordinates attains its maximum over the
hexagon, and only there, is an exposed point of the hexagon. -/
private theorem mem_exposedPoints_momentPolygon_of {v : Fin 3 → ℝ} (i j : Fin 3)
    (hv : v ∈ momentPolygon a b c)
    (hle : ∀ y ∈ momentPolygon a b c, y i - y j ≤ v i - v j)
    (heq : ∀ y ∈ momentPolygon a b c, y i - y j = v i - v j → y = v) :
    v ∈ (momentPolygon a b c).exposedPoints ℝ := by
  refine ⟨hv, ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 ↦ ℝ) i -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 ↦ ℝ) j, fun y hy ↦ ?_⟩
  simp only [sub_apply, ContinuousLinearMap.proj_apply]
  exact ⟨hle y hy, fun h ↦ heq y hy (le_antisymm (hle y hy) h)⟩

/-- For nonnegative weights, rows `1, 3, 4, 8, 7, 6` are exposed points of the hexagon: each
maximizes a difference of two coordinates exactly there. -/
private theorem vertices_subset_exposedPoints_momentPolygon (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) :
    {fixedMoment a b c 0, fixedMoment a b c 2, fixedMoment a b c 3, fixedMoment a b c 7,
        fixedMoment a b c 6, fixedMoment a b c 5} ⊆ (momentPolygon a b c).exposedPoints ℝ := by
  have hmem := fixedMoment_mem_momentPolygon ha hb hc
  simp only [insert_subset_iff, singleton_subset_iff]
  refine ⟨mem_exposedPoints_momentPolygon_of 0 2 (hmem 0) ?_ ?_,
    mem_exposedPoints_momentPolygon_of 0 1 (hmem 2) ?_ ?_,
    mem_exposedPoints_momentPolygon_of 2 1 (hmem 3) ?_ ?_,
    mem_exposedPoints_momentPolygon_of 2 0 (hmem 7) ?_ ?_,
    mem_exposedPoints_momentPolygon_of 1 0 (hmem 6) ?_ ?_,
    mem_exposedPoints_momentPolygon_of 1 2 (hmem 5) ?_ ?_⟩ <;>
  rintro y ⟨hy, hy₀, hy₁, hy₂, hy₃, hy₄, hy₅⟩ <;>
  simp only [fixedMoment_def, Matrix.cons_val] <;>
  first
  | linarith
  | intro h; ext k; fin_cases k <;> simp <;> linarith

/-- **The vertices of the moment hexagon.** For nonnegative weights, the extreme points of the
hexagon are the rows `1, 3, 4, 8, 7, 6`, in cyclic order. -/
theorem extremePoints_momentPolygon (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (momentPolygon a b c).extremePoints ℝ =
      {fixedMoment a b c 0, fixedMoment a b c 2, fixedMoment a b c 3, fixedMoment a b c 7,
        fixedMoment a b c 6, fixedMoment a b c 5} := by
  refine Subset.antisymm (fun x hx ↦ ?_)
    ((vertices_subset_exposedPoints_momentPolygon ha hb hc).trans
      exposedPoints_subset_extremePoints)
  rw [← convexHull_range_fixedMoment ha hb hc] at hx
  obtain ⟨k, rfl⟩ := extremePoints_convexHull_subset hx
  rw [convexHull_range_fixedMoment ha hb hc, mem_extremePoints_iff_forall_segment] at hx
  -- Rows `2` and `5` lie on the edge from row `6` to row `1`, so an extreme point among them is
  -- one of its endpoints.
  have hedge : fixedMoment a b c k 2 = 0 →
      fixedMoment a b c 5 = fixedMoment a b c k ∨ fixedMoment a b c 0 = fixedMoment a b c k :=
    fun hk ↦ hx.2 _ (fixedMoment_mem_momentPolygon ha hb hc 5) _
      (fixedMoment_mem_momentPolygon ha hb hc 0)
      ((momentPolygon_inter_eq_segment_five_zero ha hb hc).le
        ⟨fixedMoment_mem_momentPolygon ha hb hc k, hk⟩)
  fin_cases k
  · simp
  · rcases hedge (by simp [fixedMoment_def]) with h | h <;> rw [← h] <;> simp
  · simp
  · simp
  · rcases hedge (by simp [fixedMoment_def]) with h | h <;> rw [← h] <;> simp
  all_goals simp

/-- For nonnegative weights, the exposed points of the hexagon are its vertices, the rows
`1, 3, 4, 8, 7, 6`. -/
theorem exposedPoints_momentPolygon (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (momentPolygon a b c).exposedPoints ℝ =
      {fixedMoment a b c 0, fixedMoment a b c 2, fixedMoment a b c 3, fixedMoment a b c 7,
        fixedMoment a b c 6, fixedMoment a b c 5} :=
  (exposedPoints_subset_extremePoints.trans (extremePoints_momentPolygon ha hb hc).le).antisymm
    (vertices_subset_exposedPoints_momentPolygon ha hb hc)

/-! ### Rows `2` and `5` -/

/-- Row `2` is the point with parameter `c / (a + c)` on the affine line through rows `1`
and `6`. For nonnegative weights `a`, `b`, `c` this parameter lies in `[0, 1]`, so the point
lies on that edge of the hexagon `momentPolygon a b c`. -/
theorem fixedMoment_one_eq_lineMap (h : a + c ≠ 0) :
    fixedMoment a b c 1 =
      AffineMap.lineMap (fixedMoment a b c 0) (fixedMoment a b c 5) (c / (a + c)) := by
  ext k
  fin_cases k <;> simp [fixedMoment_def, AffineMap.lineMap_apply_module] <;> field_simp <;> ring

/-- Row `5` is the point with parameter `a / (a + c)` on the affine line through rows `1`
and `6`. For nonnegative weights `a`, `b`, `c` this parameter lies in `[0, 1]`, so the point
lies on that edge of the hexagon `momentPolygon a b c`. -/
theorem fixedMoment_four_eq_lineMap (h : a + c ≠ 0) :
    fixedMoment a b c 4 =
      AffineMap.lineMap (fixedMoment a b c 0) (fixedMoment a b c 5) (a / (a + c)) := by
  ext k
  fin_cases k <;> simp [fixedMoment_def, AffineMap.lineMap_apply_module] <;> field_simp <;> ring

/-- For positive `a` and `c`, row `2` lies in the open segment from row `1` to row `6`. When
`b` is also nonnegative, this segment is an edge of the hexagon `momentPolygon a b c`. -/
theorem fixedMoment_one_mem_openSegment (ha : 0 < a) (hc : 0 < c) :
    fixedMoment a b c 1 ∈ openSegment ℝ (fixedMoment a b c 0) (fixedMoment a b c 5) := by
  rw [fixedMoment_one_eq_lineMap (by positivity)]
  exact lineMap_mem_openSegment ℝ _ _ ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩

/-- For positive `a` and `c`, row `5` lies in the open segment from row `1` to row `6`. When
`b` is also nonnegative, this segment is an edge of the hexagon `momentPolygon a b c`. -/
theorem fixedMoment_four_mem_openSegment (ha : 0 < a) (hc : 0 < c) :
    fixedMoment a b c 4 ∈ openSegment ℝ (fixedMoment a b c 0) (fixedMoment a b c 5) := by
  rw [fixedMoment_four_eq_lineMap (by positivity)]
  exact lineMap_mem_openSegment ℝ _ _ ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩

end TauCeti.BottSamelson

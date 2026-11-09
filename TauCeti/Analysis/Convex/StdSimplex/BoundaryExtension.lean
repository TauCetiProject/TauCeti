/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Rational extension of boundary data into the standard simplex

Let `Δ` be the standard simplex, the set of weight vectors of `Convexity.StdSimplex ℝ ι`, and
`∂Δ` its relative boundary, the points of `Δ` with some vanishing coordinate
(`TauCeti.stdSimplexBoundary`). Given a function `g` on `∂Δ` and a constant `α`, this file
extends `g` to `Δ` by an explicit rational formula in the barycentric coordinates. On the open
simplex the extension is the weighted average

`(w_* * α + ∑ i, w i * g (p i x)) / (w_* + ∑ i, w i)`,

with weights `w i = ∏ j ≠ i, x j` and `w_* = ∏ j, x j`, where `p i` is the central projection
from the vertex `i` onto the opposite facet (`TauCeti.stdSimplexFacetProjection`)
(`TauCeti.stdSimplexExtension_eq_weights`). Dividing by `w_*` gives the equivalent form
`(α + ∑ i, (x i)⁻¹ * g (p i x)) / (1 + ∑ i, (x i)⁻¹)`, which is used as the definition.

Near a boundary point the facets through it carry the dominant weights, so the extension
converges to the prescribed boundary value whenever `g` is continuous there within `∂Δ`, even if
`g` is discontinuous elsewhere: away from that point only boundedness of `g` is needed. Since
the weight of `α` is positive in the interior, the extension is strictly monotone in `α` there.

The second part fills a gap `a ≤ b` over the simplex. Boundary heights `c` with `a ≤ c ≤ b` are
normalized to `(c - a) / (b - a)`, extended, and rescaled to `a + (b - a) * E`
(`TauCeti.stdSimplexGapExtension`). This recovers `c` on the boundary, lies strictly inside an
open gap in the interior when `0 < α < 1`, and is continuous on the closed simplex provided the
gap collapses only on faces of codimension at least two. At a collapsed point the normalized
ratio may have no limit, but it is bounded and the width tends to zero.

Such heights fill the gaps between consecutive section heights over a simplex when a cylindrical
decomposition is lifted to a triangulation, as in J. Bochnak, M. Coste and M.-F. Roy,
*Real Algebraic Geometry*, Springer (1998), §9.2. A zero-dimensional simplex is a single point
with empty boundary, so there are no boundary data to extend; the order and continuity results
assume `Nontrivial ι`.

## Main results

* `TauCeti.stdSimplexExtension_of_forall_pos`, `TauCeti.stdSimplexExtension_eq_weights`: the
  interior formula, in reduced and in product-weight form; on the boundary the extension is the
  prescribed function (`TauCeti.stdSimplexExtension_of_apply_eq_zero`).
* `TauCeti.stdSimplexExtension_mem_Icc`, `TauCeti.stdSimplexExtension_lt_stdSimplexExtension`:
  bounds, and strict interior monotonicity in the constant.
* `TauCeti.continuousWithinAt_stdSimplexExtension_of_apply_eq_zero`: convergence to the
  boundary value at a boundary point where bounded data are continuous.
* `TauCeti.continuousOn_stdSimplexExtension`: continuous boundary data extend continuously.
* `TauCeti.stdSimplexGapExtension_mem_Ioo`,
  `TauCeti.stdSimplexGapExtension_lt_stdSimplexGapExtension`,
  `TauCeti.continuousOn_stdSimplexGapExtension`: gap heights lie strictly inside an open gap, are
  strictly ordered by their constants, and are continuous, also at collapsed boundary points.
-/

public section

noncomputable section

open Set Finset Filter Topology Convexity

namespace TauCeti

variable {ι : Type*}

/-! ### The relative boundary -/

section Boundary

variable (ι) in
/-- The relative boundary of the standard simplex: its points with some vanishing coordinate. -/
def stdSimplexBoundary : Set (ι → ℝ) :=
  {y ∈ (range fun s : StdSimplex ℝ ι => ⇑s.weights) | ∃ i, y i = 0}

/-- Membership in the relative boundary of the standard simplex. -/
theorem mem_stdSimplexBoundary {x : ι → ℝ} :
    x ∈ stdSimplexBoundary ι ↔ x ∈ (range fun s : StdSimplex ℝ ι => ⇑s.weights) ∧ ∃ i, x i = 0 :=
  Iff.rfl

/-- The relative boundary lies in the standard simplex. -/
theorem stdSimplexBoundary_subset :
    stdSimplexBoundary ι ⊆ range fun s : StdSimplex ℝ ι => ⇑s.weights :=
  fun _ hx => hx.1

/-- Membership in the standard simplex, as nonnegative coordinates summing to one. -/
private theorem mem_range_weights_iff [Fintype ι] {x : ι → ℝ} :
    x ∈ (range fun s : StdSimplex ℝ ι => ⇑s.weights) ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 := by
  rw [StdSimplex.range_toFun_comp_weights]
  simp

variable [Finite ι]

/-- The relative boundary of the standard simplex is compact. -/
theorem isCompact_stdSimplexBoundary : IsCompact (stdSimplexBoundary ι) := by
  have hZ : IsClosed {y : ι → ℝ | ∃ i, y i = 0} := by
    simpa only [ofPred_exists] using
      isClosed_iUnion_of_finite fun i => isClosed_eq (continuous_apply i) continuous_const
  exact (isCompact_range (StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous).inter_right
    hZ

/-- A point of the standard simplex lies on its relative boundary or in its open part. -/
private theorem mem_stdSimplexBoundary_or_forall_pos {x : ι → ℝ}
    (hx : x ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights) :
    x ∈ stdSimplexBoundary ι ∨ ∀ i, 0 < x i := by
  have := Fintype.ofFinite ι
  by_cases h : ∀ i, 0 < x i
  · exact Or.inr h
  · obtain ⟨i, hi⟩ := not_forall.1 h
    exact Or.inl ⟨hx, i, le_antisymm (not_lt.1 hi) ((mem_range_weights_iff.1 hx).1 i)⟩

/-- A coordinate of a point of the standard simplex is less than one if some other coordinate
is positive. -/
theorem apply_lt_one_of_mem_range_weights {x : ι → ℝ}
    (hx : x ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights) {i j : ι} (hij : j ≠ i)
    (hxj : 0 < x j) : x i < 1 := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨hx0, hx1⟩ := mem_range_weights_iff.1 hx
  have := sum_le_sum_of_subset_of_nonneg (subset_univ {i, j}) fun k _ _ => hx0 k
  rw [sum_pair hij.symm, hx1] at this
  linarith

end Boundary

/-! ### Facet projections -/

section FacetProjection

variable [DecidableEq ι]

/-- The central projection of the standard simplex from its vertex `i` onto the opposite facet
`{y | y i = 0}`: the `i`-th coordinate is set to zero and the others are divided by `1 - x i`. -/
def stdSimplexFacetProjection (i : ι) (x : ι → ℝ) : ι → ℝ :=
  (1 - x i)⁻¹ • (x - x i • Pi.single i 1)

/-- The facet projection from `i` lands in the facet opposite `i`. -/
@[simp]
theorem stdSimplexFacetProjection_apply_self (i : ι) (x : ι → ℝ) :
    stdSimplexFacetProjection i x i = 0 := by
  simp [stdSimplexFacetProjection]

/-- The coordinates of the facet projection away from `i`. -/
theorem stdSimplexFacetProjection_apply_of_ne {i j : ι} (h : j ≠ i) (x : ι → ℝ) :
    stdSimplexFacetProjection i x j = x j / (1 - x i) := by
  simp [stdSimplexFacetProjection, h, div_eq_inv_mul]

/-- A point of the facet opposite `i` is fixed by the projection from `i`. -/
theorem stdSimplexFacetProjection_of_apply_eq_zero {i : ι} {x : ι → ℝ} (h : x i = 0) :
    stdSimplexFacetProjection i x = x := by
  simp [stdSimplexFacetProjection, h]

/-- The point `x` lies at parameter `x i` on the segment from its facet projection to the vertex
`i`. -/
theorem apply_smul_single_add_smul_stdSimplexFacetProjection {i : ι} {x : ι → ℝ} (h : x i ≠ 1) :
    x i • Pi.single i 1 + (1 - x i) • stdSimplexFacetProjection i x = x := by
  rw [stdSimplexFacetProjection, smul_smul, mul_inv_cancel₀ (sub_ne_zero.2 h.symm), one_smul,
    add_sub_cancel]

/-- The facet projection from `i` keeps positive the coordinates other than `i`. -/
theorem stdSimplexFacetProjection_apply_pos {i j : ι} (hj : j ≠ i) {x : ι → ℝ} (hxj : 0 < x j)
    (h : x i < 1) : 0 < stdSimplexFacetProjection i x j := by
  rw [stdSimplexFacetProjection_apply_of_ne hj]
  exact div_pos hxj (sub_pos.2 h)

/-- The facet projection from `i` is continuous away from the hyperplane `x i = 1`. -/
theorem continuousAt_stdSimplexFacetProjection {i : ι} {x : ι → ℝ} (h : x i ≠ 1) :
    ContinuousAt (stdSimplexFacetProjection i) x :=
  (((continuous_const.sub (continuous_apply i)).continuousAt).inv₀ (sub_ne_zero.2 h.symm)).smul
    (continuousAt_id.sub ((continuous_apply i).continuousAt.smul continuousAt_const))

variable [Finite ι]

/-- The facet projection from `i` of a point of the simplex other than the vertex `i` lies in the
simplex. -/
theorem stdSimplexFacetProjection_mem_range_weights {i : ι} {x : ι → ℝ}
    (hx : x ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights) (h : x i < 1) :
    stdSimplexFacetProjection i x ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights := by
  have := Fintype.ofFinite ι
  have hpos : 0 < 1 - x i := sub_pos.2 h
  obtain ⟨hx0, hx1⟩ := mem_range_weights_iff.1 hx
  refine mem_range_weights_iff.2 ⟨fun j => ?_, ?_⟩
  · rcases eq_or_ne j i with rfl | hj
    · simp
    · rw [stdSimplexFacetProjection_apply_of_ne hj]
      exact div_nonneg (hx0 j) hpos.le
  · simp [stdSimplexFacetProjection, ← mul_sum, sum_sub_distrib, hx1, inv_mul_cancel₀ hpos.ne']

/-- The facet projections of a point of the open simplex lie on the relative boundary. -/
theorem stdSimplexFacetProjection_mem_stdSimplexBoundary [Nontrivial ι] {x : ι → ℝ}
    (hx : x ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights) (h : ∀ j, 0 < x j) (i : ι) :
    stdSimplexFacetProjection i x ∈ stdSimplexBoundary ι := by
  obtain ⟨j, hj⟩ := exists_ne i
  exact mem_stdSimplexBoundary.2 ⟨stdSimplexFacetProjection_mem_range_weights hx
    (apply_lt_one_of_mem_range_weights hx hj (h j)), i, stdSimplexFacetProjection_apply_self i x⟩

end FacetProjection

/-! ### The rational extension -/

variable [Fintype ι]

section Weights

variable {x : ι → ℝ}

/-- Each reciprocal coordinate of a point with positive coordinates is at most the denominator
of the interior formula. -/
private theorem inv_le_one_add_sum_inv (h : ∀ i, 0 < x i) (j : ι) :
    (x j)⁻¹ ≤ 1 + ∑ i, (x i)⁻¹ :=
  (single_le_sum (fun i _ => (inv_pos.2 (h i)).le) (mem_univ j)).trans
    (le_add_of_nonneg_left zero_le_one)

/-- The denominator of the interior formula is positive. -/
private theorem one_add_sum_inv_pos (h : ∀ i, 0 < x i) : 0 < 1 + ∑ i, (x i)⁻¹ :=
  add_pos_of_pos_of_nonneg one_pos (sum_nonneg fun i _ => (inv_pos.2 (h i)).le)

end Weights

variable [DecidableEq ι]

/-- The extension of boundary data `g` into the standard simplex with interior constant `α`.
On the open simplex it is the average of `α` and of the values of `g` at the facet projections
of `x`, with weights `1` and `(x i)⁻¹`; elsewhere it is `g` itself. -/
def stdSimplexExtension (α : ℝ) (g : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  if ∀ i, 0 < x i then
    (α + ∑ i, (x i)⁻¹ * g (stdSimplexFacetProjection i x)) / (1 + ∑ i, (x i)⁻¹)
  else g x

variable {α : ℝ} {g : (ι → ℝ) → ℝ} {x : ι → ℝ}

/-- The interior formula of the extension. -/
theorem stdSimplexExtension_of_forall_pos (h : ∀ i, 0 < x i) :
    stdSimplexExtension α g x =
      (α + ∑ i, (x i)⁻¹ * g (stdSimplexFacetProjection i x)) / (1 + ∑ i, (x i)⁻¹) :=
  ite_eq_left h

/-- On the relative boundary the extension is the prescribed function. -/
theorem stdSimplexExtension_of_apply_eq_zero {i : ι} (h : x i = 0) :
    stdSimplexExtension α g x = g x :=
  ite_eq_right fun h' => (h' i).ne' h

/-- The interior formula with the product weights `∏ j ≠ i, x j` of the facets and `∏ j, x j`
of the constant. -/
theorem stdSimplexExtension_eq_weights (h : ∀ i, 0 < x i) :
    stdSimplexExtension α g x =
      ((∏ j, x j) * α + ∑ i, (∏ j ∈ univ.erase i, x j) * g (stdSimplexFacetProjection i x)) /
        ((∏ j, x j) + ∑ i, ∏ j ∈ univ.erase i, x j) := by
  have hP : (∏ j, x j) ≠ 0 := prod_ne_zero_iff.2 fun j _ => (h j).ne'
  have hw (i : ι) : ∏ j ∈ univ.erase i, x j = (∏ j, x j) * (x i)⁻¹ := by
    rw [← prod_erase_mul univ x (mem_univ i), mul_inv_cancel_right₀ (h i).ne']
  rw [stdSimplexExtension_of_forall_pos h, ← mul_div_mul_left _ _ hP]
  simp only [hw, mul_add, mul_one, mul_sum, mul_assoc]

/-- The extension of a constant by the same constant is that constant. -/
@[simp]
theorem stdSimplexExtension_const (c : ℝ) (x : ι → ℝ) :
    stdSimplexExtension c (fun _ => c) x = c := by
  by_cases h : ∀ i, 0 < x i
  · rw [stdSimplexExtension_of_forall_pos h, div_eq_iff (one_add_sum_inv_pos h).ne', ← sum_mul]
    ring
  · exact ite_eq_right h

/-- The extension is monotone in the constant and in the boundary data. -/
theorem stdSimplexExtension_le_stdSimplexExtension [Nontrivial ι] {α₁ α₂ : ℝ}
    {g₁ g₂ : (ι → ℝ) → ℝ} (hα : α₁ ≤ α₂) (hg : ∀ y ∈ stdSimplexBoundary ι, g₁ y ≤ g₂ y)
    (hx : x ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights) :
    stdSimplexExtension α₁ g₁ x ≤ stdSimplexExtension α₂ g₂ x := by
  rcases mem_stdSimplexBoundary_or_forall_pos hx with hxB | h
  · obtain ⟨-, i, hi⟩ := id hxB
    rw [stdSimplexExtension_of_apply_eq_zero hi, stdSimplexExtension_of_apply_eq_zero hi]
    exact hg x hxB
  · rw [stdSimplexExtension_of_forall_pos h, stdSimplexExtension_of_forall_pos h]
    exact div_le_div_of_nonneg_right (add_le_add hα <| sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hg _ (stdSimplexFacetProjection_mem_stdSimplexBoundary hx h i))
        (inv_pos.2 (h i)).le) (one_add_sum_inv_pos h).le

/-- On the open simplex the extension is strictly monotone in the constant. -/
theorem stdSimplexExtension_lt_stdSimplexExtension [Nontrivial ι] {α₁ α₂ : ℝ}
    {g₁ g₂ : (ι → ℝ) → ℝ} (hα : α₁ < α₂) (hg : ∀ y ∈ stdSimplexBoundary ι, g₁ y ≤ g₂ y)
    (hx : x ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights) (h : ∀ i, 0 < x i) :
    stdSimplexExtension α₁ g₁ x < stdSimplexExtension α₂ g₂ x := by
  rw [stdSimplexExtension_of_forall_pos h, stdSimplexExtension_of_forall_pos h]
  exact div_lt_div_of_pos_right (add_lt_add_of_lt_of_le hα <| sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (hg _ (stdSimplexFacetProjection_mem_stdSimplexBoundary hx h i))
      (inv_pos.2 (h i)).le) (one_add_sum_inv_pos h)

/-- If the constant and the boundary data lie in `[m, M]`, so does the extension. -/
theorem stdSimplexExtension_mem_Icc [Nontrivial ι] {m M : ℝ} (hα : α ∈ Set.Icc m M)
    (hg : ∀ y ∈ stdSimplexBoundary ι, g y ∈ Set.Icc m M)
    (hx : x ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights) :
    stdSimplexExtension α g x ∈ Set.Icc m M := by
  refine ⟨?_, ?_⟩
  · simpa using stdSimplexExtension_le_stdSimplexExtension (g₁ := fun _ => m) hα.1
      (fun y hy => (hg y hy).1) hx
  · simpa using stdSimplexExtension_le_stdSimplexExtension (g₂ := fun _ => M) hα.2
      (fun y hy => (hg y hy).2) hx

/-- If the constant lies in `(m, M)` and the boundary data in `[m, M]`, the extension lies in
`(m, M)` on the open simplex. -/
theorem stdSimplexExtension_mem_Ioo [Nontrivial ι] {m M : ℝ} (hα : α ∈ Set.Ioo m M)
    (hg : ∀ y ∈ stdSimplexBoundary ι, g y ∈ Set.Icc m M)
    (hx : x ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights) (h : ∀ i, 0 < x i) :
    stdSimplexExtension α g x ∈ Set.Ioo m M := by
  refine ⟨?_, ?_⟩
  · simpa using stdSimplexExtension_lt_stdSimplexExtension (g₁ := fun _ => m) hα.1
      (fun y hy => (hg y hy).1) hx h
  · simpa using stdSimplexExtension_lt_stdSimplexExtension (g₂ := fun _ => M) hα.2
      (fun y hy => (hg y hy).2) hx h

/-! ### Continuity -/

/-- On the open simplex, the extension is a value `L` plus the combination of `α - L` and of the
deviations `g (p i x) - L` with weights `S⁻¹` and `(x i)⁻¹ * S⁻¹`, where `S` is the
denominator. -/
private theorem stdSimplexExtension_eq_add_sum (h : ∀ i, 0 < x i) (L : ℝ) :
    stdSimplexExtension α g x = L + ((α - L) * (1 + ∑ i, (x i)⁻¹)⁻¹ +
      ∑ i, (x i)⁻¹ * (1 + ∑ i, (x i)⁻¹)⁻¹ * (g (stdSimplexFacetProjection i x) - L)) := by
  have hS := (one_add_sum_inv_pos h).ne'
  have hsum : ∑ i, (x i)⁻¹ * (1 + ∑ i, (x i)⁻¹)⁻¹ * (g (stdSimplexFacetProjection i x) - L) =
      (1 + ∑ i, (x i)⁻¹)⁻¹ * ∑ i, (x i)⁻¹ * g (stdSimplexFacetProjection i x) -
        (1 + ∑ i, (x i)⁻¹)⁻¹ * L * ∑ i, (x i)⁻¹ := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [stdSimplexExtension_of_forall_pos h, hsum]
  generalize ∑ i, (x i)⁻¹ * g (stdSimplexFacetProjection i x) = G
  generalize ∑ i, (x i)⁻¹ = T at hS ⊢
  field_simp
  ring

/-- Approaching a boundary point `x` through the open simplex, the extension tends to `g x` if
`g` is bounded on the boundary and continuous at `x` within it. -/
private theorem tendsto_stdSimplexExtension_of_apply_eq_zero [Nontrivial ι] {i₀ : ι}
    (hi₀ : x i₀ = 0) {C : ℝ} (hC : ∀ y ∈ stdSimplexBoundary ι, |g y| ≤ C)
    (hg : ContinuousWithinAt g (stdSimplexBoundary ι) x) :
    Tendsto (stdSimplexExtension α g)
      (𝓝[{y ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights | ∀ j, 0 < y j}] x) (𝓝 (g x)) := by
  set U := {y ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights | ∀ j, 0 < y j}
  set L := g x
  have hU : ∀ᶠ y in 𝓝[U] x, y ∈ U := self_mem_nhdsWithin
  have hcoord (j : ι) : Tendsto (fun y : ι → ℝ => y j) (𝓝[U] x) (𝓝 (x j)) :=
    ((continuous_apply j).tendsto x).mono_left nhdsWithin_le_nhds
  -- The reciprocal of the denominator tends to zero, since it is at most `y i₀`.
  have hinv : Tendsto (fun y : ι → ℝ => (1 + ∑ i, (y i)⁻¹)⁻¹) (𝓝[U] x) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hi₀ ▸ hcoord i₀)
      (hU.mono fun y hy => (inv_pos.2 (one_add_sum_inv_pos hy.2)).le) (hU.mono fun y hy => ?_)
    simpa using inv_anti₀ (inv_pos.2 (hy.2 i₀)) (inv_le_one_add_sum_inv hy.2 i₀)
  have hterm (j : ι) : Tendsto (fun y : ι → ℝ => (y j)⁻¹ * (1 + ∑ i, (y i)⁻¹)⁻¹ *
      (g (stdSimplexFacetProjection j y) - L)) (𝓝[U] x) (𝓝 0) := by
    rcases eq_or_ne (x j) 0 with hxj | hxj
    · -- A facet through `x`: bounded weight, deviation tending to zero.
      refine isBoundedUnder_le_mul_tendsto_zero (isBoundedUnder_of_eventually_le (a := 1)
        (hU.mono fun y hy => ?_)) ?_
      · have hS := one_add_sum_inv_pos hy.2
        rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
          (inv_pos.2 (hy.2 j)).le (inv_pos.2 hS).le), ← div_eq_mul_inv]
        exact div_le_one_of_le₀ (inv_le_one_add_sum_inv hy.2 j) hS.le
      · have hp : Tendsto (stdSimplexFacetProjection j) (𝓝[U] x)
            (𝓝[stdSimplexBoundary ι] x) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, hU.mono fun y hy =>
            stdSimplexFacetProjection_mem_stdSimplexBoundary hy.1 hy.2 j⟩
          have := (continuousAt_stdSimplexFacetProjection (i := j) (x := x)
            (by rw [hxj]; norm_num)).tendsto.mono_left (nhdsWithin_le_nhds (s := U))
          rwa [stdSimplexFacetProjection_of_apply_eq_zero hxj] at this
        simpa [L] using (hg.tendsto.comp hp).sub_const L
    · -- A facet not through `x`: weight tending to zero, bounded deviation.
      refine Tendsto.zero_mul_isBoundedUnder_le ?_ (isBoundedUnder_of_eventually_le
        (a := C + |L|) (hU.mono fun y hy => ?_))
      · simpa using ((hcoord j).inv₀ hxj).mul hinv
      · rw [Function.comp_apply, Real.norm_eq_abs]
        exact (abs_sub _ _).trans (add_le_add_left
          (hC _ (stdSimplexFacetProjection_mem_stdSimplexBoundary hy.1 hy.2 j)) _)
  have hlim := (tendsto_const_nhds (x := L)).add
    ((tendsto_const_nhds (x := α - L)).mul hinv |>.add (tendsto_finsetSum univ fun j _ => hterm j))
  simp only [mul_zero, sum_const_zero, add_zero] at hlim
  exact hlim.congr' (hU.mono fun y hy => (stdSimplexExtension_eq_add_sum hy.2 L).symm)

/-- **Boundary limit.** At a boundary point where bounded boundary data `g` are continuous
within the boundary, the extension is continuous within the simplex: the facets through the
point carry the dominant weights. -/
theorem continuousWithinAt_stdSimplexExtension_of_apply_eq_zero [Nontrivial ι] {i₀ : ι}
    (hi₀ : x i₀ = 0) {C : ℝ} (hC : ∀ y ∈ stdSimplexBoundary ι, |g y| ≤ C)
    (hg : ContinuousWithinAt g (stdSimplexBoundary ι) x) :
    ContinuousWithinAt (stdSimplexExtension α g) (range fun s : StdSimplex ℝ ι => ⇑s.weights)
      x := by
  have hsplit : (range fun s : StdSimplex ℝ ι => ⇑s.weights) =
      stdSimplexBoundary ι ∪ {y ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights | ∀ j, 0 < y j} := by
    ext y
    exact ⟨fun hy => (mem_stdSimplexBoundary_or_forall_pos hy).imp id (⟨hy, ·⟩),
      fun hy => hy.elim (·.1) (·.1)⟩
  have hEx : stdSimplexExtension α g x = g x := stdSimplexExtension_of_apply_eq_zero hi₀
  rw [hsplit]
  refine ContinuousWithinAt.union (hg.congr (fun y hy => ?_) hEx) ?_
  · obtain ⟨j, hj⟩ := hy.2
    exact stdSimplexExtension_of_apply_eq_zero hj
  · rw [ContinuousWithinAt, hEx]
    exact tendsto_stdSimplexExtension_of_apply_eq_zero hi₀ hC hg

/-- **Interior continuity.** At a point of the open simplex the extension is continuous within
the simplex if the boundary data are continuous, within the boundary, at its facet
projections. -/
theorem continuousWithinAt_stdSimplexExtension_of_forall_pos [Nontrivial ι]
    (hx : x ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights) (h : ∀ i, 0 < x i)
    (hg : ∀ i, ContinuousWithinAt g (stdSimplexBoundary ι) (stdSimplexFacetProjection i x)) :
    ContinuousWithinAt (stdSimplexExtension α g) (range fun s : StdSimplex ℝ ι => ⇑s.weights)
      x := by
  have hU : IsOpen {y : ι → ℝ | ∀ i, 0 < y i} := by
    simpa only [ofPred_forall] using
      isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  rw [← continuousWithinAt_inter (hU.mem_nhds h)]
  refine ContinuousWithinAt.congr ?_ (fun y hy => stdSimplexExtension_of_forall_pos hy.2)
    (stdSimplexExtension_of_forall_pos h)
  have hinv (i : ι) : ContinuousWithinAt (fun y : ι → ℝ => (y i)⁻¹)
      ((range fun s : StdSimplex ℝ ι => ⇑s.weights) ∩ {y | ∀ i, 0 < y i}) x :=
    ((continuous_apply i).continuousAt.inv₀ (h i).ne').continuousWithinAt
  have hgp (i : ι) : ContinuousWithinAt (fun y => g (stdSimplexFacetProjection i y))
      ((range fun s : StdSimplex ℝ ι => ⇑s.weights) ∩ {y | ∀ i, 0 < y i}) x := by
    obtain ⟨j, hj⟩ := exists_ne i
    exact (hg i).comp (continuousAt_stdSimplexFacetProjection
      (apply_lt_one_of_mem_range_weights hx hj (h j)).ne).continuousWithinAt
      fun y hy => stdSimplexFacetProjection_mem_stdSimplexBoundary hy.1 hy.2 i
  exact (continuousWithinAt_const.add (tendsto_finsetSum univ fun i _ => (hinv i).mul (hgp i))).div
    (continuousWithinAt_const.add (tendsto_finsetSum univ fun i _ => hinv i))
    (one_add_sum_inv_pos h).ne'

/-- **Continuous extension.** Boundary data continuous on the relative boundary extend
continuously to the standard simplex. -/
theorem continuousOn_stdSimplexExtension [Nontrivial ι]
    (hg : ContinuousOn g (stdSimplexBoundary ι)) :
    ContinuousOn (stdSimplexExtension α g) (range fun s : StdSimplex ℝ ι => ⇑s.weights) := by
  obtain ⟨C, hC⟩ := isCompact_stdSimplexBoundary.exists_bound_of_continuousOn hg
  intro x hx
  rcases mem_stdSimplexBoundary_or_forall_pos hx with hxB | h
  · obtain ⟨-, i, hi⟩ := id hxB
    exact continuousWithinAt_stdSimplexExtension_of_apply_eq_zero hi
      (fun y hy => by simpa using hC y hy) (hg x hxB)
  · exact continuousWithinAt_stdSimplexExtension_of_forall_pos hx h fun i =>
      hg _ (stdSimplexFacetProjection_mem_stdSimplexBoundary hx h i)

/-! ### Heights in a gap -/

/-- The height in the gap between `a` and `b` over the standard simplex extending boundary
heights `c`: the normalized boundary ratio `(c - a) / (b - a)` is extended with interior
constant `α` and rescaled to the gap. -/
def stdSimplexGapExtension (a b c : (ι → ℝ) → ℝ) (α : ℝ) (x : ι → ℝ) : ℝ :=
  a x + (b x - a x) * stdSimplexExtension α (fun y => (c y - a y) / (b y - a y)) x

variable {a b c : (ι → ℝ) → ℝ}

/-- The gap height is `a + (b - a) * E` for the extension `E` of the normalized ratio. -/
theorem stdSimplexGapExtension_def (x : ι → ℝ) :
    stdSimplexGapExtension a b c α x =
      a x + (b x - a x) * stdSimplexExtension α (fun y => (c y - a y) / (b y - a y)) x :=
  (rfl)

/-- On the relative boundary the gap height is the prescribed height, also where the gap
collapses. -/
theorem stdSimplexGapExtension_of_apply_eq_zero {i : ι} (h : x i = 0)
    (hc : c x ∈ Set.Icc (a x) (b x)) : stdSimplexGapExtension a b c α x = c x := by
  rw [stdSimplexGapExtension_def, stdSimplexExtension_of_apply_eq_zero h]
  rcases eq_or_ne (b x) (a x) with hab | hab
  · rw [hab, sub_self, zero_mul, add_zero]
    exact (le_antisymm (hab ▸ hc.2) hc.1).symm
  · rw [mul_div_cancel₀ _ (sub_ne_zero.2 hab), add_sub_cancel]

/-- The normalized position of a height in a gap lies in `[0, 1]`. -/
private theorem div_sub_mem_Icc {a b c : ℝ} (hc : c ∈ Set.Icc a b) :
    (c - a) / (b - a) ∈ Set.Icc 0 1 :=
  ⟨div_nonneg (sub_nonneg.2 hc.1) (sub_nonneg.2 (hc.1.trans hc.2)),
    div_le_one_of_le₀ (sub_le_sub_right hc.2 a) (sub_nonneg.2 (hc.1.trans hc.2))⟩

/-- For a constant in `[0, 1]`, the gap height lies in the gap. -/
theorem stdSimplexGapExtension_mem_Icc [Nontrivial ι] (hα : α ∈ Set.Icc 0 1)
    (hc : ∀ y ∈ stdSimplexBoundary ι, c y ∈ Set.Icc (a y) (b y))
    (hx : x ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights) (hab : a x ≤ b x) :
    stdSimplexGapExtension a b c α x ∈ Set.Icc (a x) (b x) := by
  have hE := stdSimplexExtension_mem_Icc hα (fun y hy => div_sub_mem_Icc (hc y hy)) hx
  rw [stdSimplexGapExtension_def]
  constructor <;> nlinarith [hE.1, hE.2]

/-- For a constant in `(0, 1)`, the gap height lies strictly inside an open gap at each point of
the open simplex. -/
theorem stdSimplexGapExtension_mem_Ioo [Nontrivial ι] (hα : α ∈ Set.Ioo 0 1)
    (hc : ∀ y ∈ stdSimplexBoundary ι, c y ∈ Set.Icc (a y) (b y))
    (hx : x ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights) (h : ∀ i, 0 < x i)
    (hab : a x < b x) : stdSimplexGapExtension a b c α x ∈ Set.Ioo (a x) (b x) := by
  have hE := stdSimplexExtension_mem_Ioo hα (fun y hy => div_sub_mem_Icc (hc y hy)) hx h
  rw [stdSimplexGapExtension_def]
  constructor <;> nlinarith [hE.1, hE.2]

/-- Gap heights are monotone in the constant and in the boundary heights. -/
theorem stdSimplexGapExtension_le_stdSimplexGapExtension [Nontrivial ι] {c₁ c₂ : (ι → ℝ) → ℝ}
    {α₁ α₂ : ℝ} (hα : α₁ ≤ α₂) (hc : ∀ y ∈ stdSimplexBoundary ι, a y ≤ b y ∧ c₁ y ≤ c₂ y)
    (hx : x ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights) (hab : a x ≤ b x) :
    stdSimplexGapExtension a b c₁ α₁ x ≤ stdSimplexGapExtension a b c₂ α₂ x := by
  rw [stdSimplexGapExtension_def, stdSimplexGapExtension_def]
  refine (add_le_add_iff_left _).2 (mul_le_mul_of_nonneg_left
    (stdSimplexExtension_le_stdSimplexExtension hα (fun y hy => ?_) hx) (sub_nonneg.2 hab))
  exact div_le_div_of_nonneg_right (sub_le_sub_right (hc y hy).2 _) (sub_nonneg.2 (hc y hy).1)

/-- Over an open gap, gap heights with strictly ordered constants are strictly ordered on the
open simplex. -/
theorem stdSimplexGapExtension_lt_stdSimplexGapExtension [Nontrivial ι] {c₁ c₂ : (ι → ℝ) → ℝ}
    {α₁ α₂ : ℝ} (hα : α₁ < α₂) (hc : ∀ y ∈ stdSimplexBoundary ι, a y ≤ b y ∧ c₁ y ≤ c₂ y)
    (hx : x ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights) (h : ∀ i, 0 < x i)
    (hab : a x < b x) :
    stdSimplexGapExtension a b c₁ α₁ x < stdSimplexGapExtension a b c₂ α₂ x := by
  rw [stdSimplexGapExtension_def, stdSimplexGapExtension_def]
  refine (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left
    (stdSimplexExtension_lt_stdSimplexExtension hα (fun y hy => ?_) hx h) (sub_pos.2 hab))
  exact div_le_div_of_nonneg_right (sub_le_sub_right (hc y hy).2 _) (sub_nonneg.2 (hc y hy).1)

/-- **Continuity of gap heights.** Let `a` and `b` be continuous on the simplex, and let the
boundary heights `c` be continuous on the relative boundary and lie in the gap there. If the gap
collapses only on faces of codimension at least two, the gap height is continuous on the
simplex. -/
theorem continuousOn_stdSimplexGapExtension [Nontrivial ι]
    (ha : ContinuousOn a (range fun s : StdSimplex ℝ ι => ⇑s.weights))
    (hb : ContinuousOn b (range fun s : StdSimplex ℝ ι => ⇑s.weights))
    (hc : ContinuousOn c (stdSimplexBoundary ι))
    (hcab : ∀ y ∈ stdSimplexBoundary ι, c y ∈ Set.Icc (a y) (b y))
    (hcollapse : ∀ y ∈ (range fun s : StdSimplex ℝ ι => ⇑s.weights),
      a y = b y → ∃ i j, i ≠ j ∧ y i = 0 ∧ y j = 0) :
    ContinuousOn (stdSimplexGapExtension a b c α) (range fun s : StdSimplex ℝ ι => ⇑s.weights) := by
  set r : (ι → ℝ) → ℝ := fun y => (c y - a y) / (b y - a y)
  have hr (y : ι → ℝ) (hy : y ∈ stdSimplexBoundary ι) (hne : a y ≠ b y) :
      ContinuousWithinAt r (stdSimplexBoundary ι) y :=
    ((hc y hy).sub ((ha y hy.1).mono stdSimplexBoundary_subset)).div
      (((hb y hy.1).mono stdSimplexBoundary_subset).sub
        ((ha y hy.1).mono stdSimplexBoundary_subset))
      (sub_ne_zero.2 hne.symm)
  have hr01 (y : ι → ℝ) (hy : y ∈ stdSimplexBoundary ι) : r y ∈ Set.Icc 0 1 :=
    div_sub_mem_Icc (hcab y hy)
  have hrC (y : ι → ℝ) (hy : y ∈ stdSimplexBoundary ι) : |r y| ≤ 1 :=
    abs_le.2 ⟨by linarith [(hr01 y hy).1], (hr01 y hy).2⟩
  have hfun : stdSimplexGapExtension a b c α =
      fun y => a y + (b y - a y) * stdSimplexExtension α r y :=
    funext stdSimplexGapExtension_def
  rw [hfun]
  intro x hx
  rcases mem_stdSimplexBoundary_or_forall_pos hx with hxB | h
  · obtain ⟨-, i, hi⟩ := id hxB
    rcases ne_or_eq (a x) (b x) with hne | heq
    · exact (ha x hx).add (((hb x hx).sub (ha x hx)).mul
        (continuousWithinAt_stdSimplexExtension_of_apply_eq_zero hi hrC (hr x hxB hne)))
    -- At a collapsed point the bounded extension is multiplied by a vanishing width.
    have hE (y : ι → ℝ) (hy : y ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights) :
        |stdSimplexExtension α r y| ≤ |α| + 1 :=
      abs_le.2 <| stdSimplexExtension_mem_Icc
        ⟨by linarith [neg_abs_le α], by linarith [le_abs_self α]⟩
        (fun z hz => ⟨by linarith [(hr01 z hz).1, abs_nonneg α],
          by linarith [(hr01 z hz).2, abs_nonneg α]⟩) hy
    have hw : Tendsto (fun y => b y - a y)
        (𝓝[range fun s : StdSimplex ℝ ι => ⇑s.weights] x) (𝓝 0) := by
      have := ((hb x hx).sub (ha x hx)).tendsto
      rwa [Pi.sub_apply, heq, sub_self] at this
    have hlim := (ha x hx).tendsto.add (hw.zero_mul_isBoundedUnder_le
      (isBoundedUnder_of_eventually_le (a := |α| + 1)
        (eventually_nhdsWithin_of_forall fun y hy => hE y hy)))
    rw [add_zero] at hlim
    rwa [ContinuousWithinAt, heq, sub_self, zero_mul, add_zero, ← heq]
  · -- Each facet projection has a single vanishing coordinate, so the gap is open there.
    refine (ha x hx).add (((hb x hx).sub (ha x hx)).mul
      (continuousWithinAt_stdSimplexExtension_of_forall_pos hx h fun i => ?_))
    have hpB := stdSimplexFacetProjection_mem_stdSimplexBoundary hx h i
    refine hr _ hpB fun heq => ?_
    obtain ⟨j, k, hjk, hj, hk⟩ := hcollapse _ hpB.1 heq
    obtain ⟨l, hl, hl0⟩ : ∃ l, l ≠ i ∧ stdSimplexFacetProjection i x l = 0 := by
      rcases eq_or_ne j i with rfl | hji
      · exact ⟨k, hjk.symm, hk⟩
      · exact ⟨j, hji, hj⟩
    obtain ⟨m, hm⟩ := exists_ne i
    exact (stdSimplexFacetProjection_apply_pos hl (h l)
      (apply_lt_one_of_mem_range_weights hx hm (h m))).ne' hl0

end TauCeti

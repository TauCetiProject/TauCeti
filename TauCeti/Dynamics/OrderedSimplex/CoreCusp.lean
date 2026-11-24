/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.OrderedSimplex.Branch

/-!
# The core and the cusp of the ordered simplex

Write `b = w₁ + ⋯ + w_{n-2}` for a point `w` of the ordered projective simplex `Δ_n`, so that
`w_{n-1} = 1 - b`. Following Gamburd, Magee and Ronan, the region `Δ₀ = {b ≤ 1 / 2}`, where the
last coordinate dominates the sum of the others, splits into the closed pieces

* the *core* `Δ_core = {0 ≤ 1 - 2 b ≤ w_{n-2}}`, and
* the *cusp* `Δ_cusp = {1 - 2 b ≥ w_{n-2}}`,

which meet exactly where `1 - 2 b = w_{n-2}`. The unaccelerated branches `γ_j`, `j ≤ n - 2`, map
the whole simplex into the core, and `γ_{n-1}` maps it into the cusp; so every accelerated branch
`γ_{n-1}^A γ_j` maps the simplex into `Δ₀`. On these pieces the coordinates satisfy explicit
bounds, which feed the derivative estimates for short blocks of branches behind the uniform
contraction of long branch compositions.

In chart coordinates `x i = w_{i+1}`, the sum `b` is `∑ xᵢ` and `w_{n-2}` is the last chart
coordinate. The core and the cusp therefore live in `Fin (d + 1) → ℝ`, for `n = d + 3 ≥ 3`, where
that coordinate is `x (Fin.last d)`; `Δ₀` makes sense for every `d`.

## Main definitions

* `TauCeti.simplexHalf d`: the region `Δ₀` of the ordered simplex where `∑ xᵢ ≤ 1 / 2`.
* `TauCeti.simplexCore d`: the core `Δ_core` in `Fin (d + 1) → ℝ`.
* `TauCeti.simplexCusp d`: the cusp `Δ_cusp` in `Fin (d + 1) → ℝ`.

## Main results

* `TauCeti.simplexCore_union_simplexCusp`, `TauCeti.simplexCore_inter_simplexCusp`: the core and
  the cusp cover `Δ₀` and meet where `1 - 2 b = w_{n-2}`.
* `TauCeti.isCompact_simplexHalf`, `TauCeti.convex_simplexHalf` and their analogues: the three
  regions are compact and convex.
* `TauCeti.branchMap_zero_mem_simplexCore`, `TauCeti.lastMoveMap_mem_simplexCusp`: the
  unaccelerated moves map the simplex into the core and the cusp.
* `TauCeti.branchMap_mem_simplexCusp`, `TauCeti.branchMap_mem_simplexHalf`: accelerated branches
  map the simplex into the cusp, and every branch maps it into `Δ₀`.
* `TauCeti.le_one_div_two_mul_of_mem_simplexHalf`,
  `TauCeti.le_one_div_two_mul_add_one_of_mem_simplexCusp`: on `Δ₀`, `w_{n-j} ≤ 1 / (2 (j - 1))`,
  and on the cusp, `w_{n-j} ≤ 1 / (2 j - 1)`, for `2 ≤ j ≤ n - 1`; in particular
  `w_{n-3} ≤ 1 / 4` on `Δ₀`, and `w_{n-2} ≤ 1 / 3`, `w_{n-3} ≤ 1 / 5` on the cusp.

## References

* A. Gamburd, M. Magee, R. Ronan, *An asymptotic formula for integer points on Markoff–Hurwitz
  varieties*, Ann. of Math. 190 (2019), §5.1.
-/

public section

open Set

namespace TauCeti

variable {d : ℕ}

/-! ### The regions -/

/-- The region `Δ₀ = {w₁ + ⋯ + w_{n-2} ≤ 1 / 2}` of the ordered simplex in chart coordinates,
where the last coordinate `w_{n-1}` is at least the sum of the others. Every branch maps the
simplex into it. -/
def simplexHalf (d : ℕ) : Set (Fin d → ℝ) :=
  orderedSimplex d ∩ {x | ∑ k, x k ≤ 1 / 2}

theorem mem_simplexHalf_iff {x : Fin d → ℝ} :
    x ∈ simplexHalf d ↔ x ∈ orderedSimplex d ∧ ∑ k, x k ≤ 1 / 2 :=
  Iff.rfl

/-- The core `Δ_core = {0 ≤ 1 - 2 b ≤ w_{n-2}}` of the ordered simplex `Δ_{d+3}` in chart
coordinates, where `b = ∑ xᵢ` and `w_{n-2} = x (Fin.last d)` is the last chart coordinate. -/
def simplexCore (d : ℕ) : Set (Fin (d + 1) → ℝ) :=
  simplexHalf (d + 1) ∩ {x | 1 - 2 * ∑ k, x k ≤ x (Fin.last d)}

theorem mem_simplexCore_iff {x : Fin (d + 1) → ℝ} :
    x ∈ simplexCore d ↔
      x ∈ orderedSimplex (d + 1) ∧ 0 ≤ 1 - 2 * ∑ k, x k ∧ 1 - 2 * ∑ k, x k ≤ x (Fin.last d) := by
  simp only [simplexCore, mem_inter_iff, mem_simplexHalf_iff, mem_ofPred_eq, and_assoc]
  exact and_congr_right fun _ => and_congr_left fun _ => by constructor <;> intro h <;> linarith

/-- The cusp `Δ_cusp = {1 - 2 b ≥ w_{n-2}}` of the ordered simplex `Δ_{d+3}` in chart
coordinates, where `b = ∑ xᵢ` and `w_{n-2} = x (Fin.last d)` is the last chart coordinate. -/
def simplexCusp (d : ℕ) : Set (Fin (d + 1) → ℝ) :=
  orderedSimplex (d + 1) ∩ {x | x (Fin.last d) ≤ 1 - 2 * ∑ k, x k}

theorem mem_simplexCusp_iff {x : Fin (d + 1) → ℝ} :
    x ∈ simplexCusp d ↔ x ∈ orderedSimplex (d + 1) ∧ x (Fin.last d) ≤ 1 - 2 * ∑ k, x k :=
  Iff.rfl

theorem simplexHalf_subset_orderedSimplex : simplexHalf d ⊆ orderedSimplex d :=
  inter_subset_left

theorem simplexCore_subset_simplexHalf : simplexCore d ⊆ simplexHalf (d + 1) :=
  inter_subset_left

theorem simplexCusp_subset_simplexHalf : simplexCusp d ⊆ simplexHalf (d + 1) := by
  intro x hx
  obtain ⟨hx, hcusp⟩ := mem_simplexCusp_iff.mp hx
  have := (mem_orderedSimplex_iff.mp hx).1 (Fin.last d)
  exact mem_simplexHalf_iff.mpr ⟨hx, by linarith⟩

/-- The core and the cusp cover `Δ₀`. -/
theorem simplexCore_union_simplexCusp : simplexCore d ∪ simplexCusp d = simplexHalf (d + 1) := by
  refine Subset.antisymm (union_subset simplexCore_subset_simplexHalf
    simplexCusp_subset_simplexHalf) fun x hx => ?_
  rcases le_total (1 - 2 * ∑ k, x k) (x (Fin.last d)) with h | h
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr ⟨simplexHalf_subset_orderedSimplex hx, h⟩

/-- The core and the cusp meet exactly where `1 - 2 b = w_{n-2}`. -/
theorem simplexCore_inter_simplexCusp :
    simplexCore d ∩ simplexCusp d =
      {x | x ∈ orderedSimplex (d + 1) ∧ 1 - 2 * ∑ k, x k = x (Fin.last d)} := by
  ext x
  simp only [mem_inter_iff, mem_simplexCore_iff, mem_simplexCusp_iff, mem_ofPred_eq]
  refine ⟨fun ⟨⟨hx, _, h₁⟩, _, h₂⟩ => ⟨hx, le_antisymm h₁ h₂⟩, fun ⟨hx, h⟩ => ?_⟩
  have := (mem_orderedSimplex_iff.mp hx).1 (Fin.last d)
  exact ⟨⟨hx, by linarith, h.le⟩, hx, h.ge⟩

/-! ### Topology and convexity -/

theorem isClosed_simplexHalf (d : ℕ) : IsClosed (simplexHalf d) :=
  (isClosed_orderedSimplex d).inter (isClosed_le (by fun_prop) continuous_const)

theorem isClosed_simplexCore (d : ℕ) : IsClosed (simplexCore d) :=
  (isClosed_simplexHalf (d + 1)).inter (isClosed_le (by fun_prop) (continuous_apply _))

theorem isClosed_simplexCusp (d : ℕ) : IsClosed (simplexCusp d) :=
  (isClosed_orderedSimplex (d + 1)).inter (isClosed_le (continuous_apply _) (by fun_prop))

theorem isCompact_simplexHalf (d : ℕ) : IsCompact (simplexHalf d) :=
  (isCompact_orderedSimplex d).of_isClosed_subset (isClosed_simplexHalf d)
    simplexHalf_subset_orderedSimplex

theorem isCompact_simplexCore (d : ℕ) : IsCompact (simplexCore d) :=
  (isCompact_simplexHalf (d + 1)).of_isClosed_subset (isClosed_simplexCore d)
    simplexCore_subset_simplexHalf

theorem isCompact_simplexCusp (d : ℕ) : IsCompact (simplexCusp d) :=
  (isCompact_simplexHalf (d + 1)).of_isClosed_subset (isClosed_simplexCusp d)
    simplexCusp_subset_simplexHalf

theorem convex_simplexHalf (d : ℕ) : Convex ℝ (simplexHalf d) :=
  (convex_orderedSimplex d).inter (convex_halfSpace_le (f := fun x : Fin d → ℝ => ∑ k, x k)
    ⟨fun x y => by simp [Finset.sum_add_distrib], fun c x => by simp [Finset.mul_sum]⟩ (1 / 2))

/-- The linear form `w_{n-2} + 2 b` that cuts the core from the cusp. -/
private theorem isLinearMap_last_add_two_mul_sum :
    IsLinearMap ℝ fun x : Fin (d + 1) → ℝ => x (Fin.last d) + 2 * ∑ k, x k :=
  ⟨fun x y => by simp only [Pi.add_apply, Finset.sum_add_distrib]; ring,
    fun c x => by simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; ring⟩

theorem convex_simplexCore (d : ℕ) : Convex ℝ (simplexCore d) := by
  simp_rw [simplexCore, sub_le_iff_le_add]
  exact (convex_simplexHalf (d + 1)).inter
    (convex_halfSpace_ge isLinearMap_last_add_two_mul_sum 1)

theorem convex_simplexCusp (d : ℕ) : Convex ℝ (simplexCusp d) := by
  simp_rw [simplexCusp, le_sub_iff_add_le]
  exact (convex_orderedSimplex (d + 1)).inter
    (convex_halfSpace_le isLinearMap_last_add_two_mul_sum 1)

/-! ### Images of the moves -/

/-- Every branch maps the ordered simplex into `Δ₀`: the chart coordinates of `F_a (w)` sum to
`(1 - w_j) / q_a (w)`, which is at most `1 / 2`. -/
theorem branchMap_mem_simplexHalf (a : ℕ × Fin d) {x : Fin d → ℝ}
    (hx : x ∈ orderedSimplex d) : branchMap a x ∈ simplexHalf d := by
  have hq := branchDenom_pos_of_mem_orderedSimplex a hx
  have h0 := (mem_orderedSimplex_iff.mp hx).1 a.2
  refine ⟨branchMap_mem_orderedSimplex a hx, ?_⟩
  rw [mem_ofPred_eq, sum_branchMap, div_le_iff₀ hq, branchDenom_def]
  nlinarith [le_one_half_of_mem_orderedSimplex hx a.2, (a.1.cast_nonneg : (0 : ℝ) ≤ a.1)]

/-- Every branch maps the ordered simplex into `Δ₀`. -/
theorem mapsTo_branchMap_simplexHalf (a : ℕ × Fin d) :
    MapsTo (branchMap a) (orderedSimplex d) (simplexHalf d) :=
  fun _ hx => branchMap_mem_simplexHalf a hx

/-- The unaccelerated branches `γ_j`, `j ≤ n - 2`, map the ordered simplex into the core: for
`a = (0, j)`, `1 - 2 b` and `w_{n-2}` become `w_j / q_a (w)` and `w_{n-1} / q_a (w)`. -/
theorem branchMap_zero_mem_simplexCore (j : Fin (d + 1)) {x : Fin (d + 1) → ℝ}
    (hx : x ∈ orderedSimplex (d + 1)) : branchMap (0, j) x ∈ simplexCore d := by
  have hq := branchDenom_pos_of_mem_orderedSimplex (0, j) hx
  refine ⟨branchMap_mem_simplexHalf (0, j) hx, ?_⟩
  rw [mem_ofPred_eq, sum_branchMap, branchMap_apply_last, mul_div_assoc', one_sub_div hq.ne',
    div_le_div_iff_of_pos_right hq, branchDenom_def]
  have := (mem_orderedSimplex_iff.mp hx).2.2 j
  push_cast
  linarith

/-- The unaccelerated branches `γ_j`, `j ≤ n - 2`, map the ordered simplex into the core. -/
theorem mapsTo_branchMap_zero_simplexCore (j : Fin (d + 1)) :
    MapsTo (branchMap (0, j)) (orderedSimplex (d + 1)) (simplexCore d) :=
  fun _ hx => branchMap_zero_mem_simplexCore j hx

/-- The last move `γ_{n-1}` maps the ordered simplex into the cusp: `1 - 2 b` and `w_{n-2}` become
`w_{n-1} / (1 + b)` and `w_{n-2} / (1 + b)`. -/
theorem lastMoveMap_mem_simplexCusp {x : Fin (d + 1) → ℝ} (hx : x ∈ orderedSimplex (d + 1)) :
    lastMoveMap x ∈ simplexCusp d := by
  have hlast := (mem_orderedSimplex_iff.mp hx).2.2
  have hpos := one_add_sum_pos_of_mem_orderedSimplex hx
  refine ⟨lastMoveMap_mem_orderedSimplex hx, ?_⟩
  rw [mem_ofPred_eq, sum_lastMoveMap, lastMoveMap_apply, mul_div_assoc', one_sub_div hpos.ne',
    div_le_div_iff_of_pos_right hpos]
  linarith [hlast (Fin.last d)]

/-- The last move `γ_{n-1}` maps the ordered simplex into the cusp. -/
theorem mapsTo_lastMoveMap_simplexCusp :
    MapsTo lastMoveMap (orderedSimplex (d + 1)) (simplexCusp d) :=
  fun _ hx => lastMoveMap_mem_simplexCusp hx

/-- The accelerated branches `γ_{n-1}^A γ_j` with `A ≥ 1` map the ordered simplex into the cusp,
since they end with the last move. -/
theorem branchMap_mem_simplexCusp {a : ℕ × Fin (d + 1)} (ha : a.1 ≠ 0)
    {x : Fin (d + 1) → ℝ} (hx : x ∈ orderedSimplex (d + 1)) : branchMap a x ∈ simplexCusp d := by
  obtain ⟨A, j⟩ := a
  obtain ⟨A, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero ha
  rw [branchMap_succ A j (branchDenom_pos_of_mem_orderedSimplex (A, j) hx).ne']
  exact lastMoveMap_mem_simplexCusp (branchMap_mem_orderedSimplex (A, j) hx)

/-- The accelerated branches `γ_{n-1}^A γ_j` with `A ≥ 1` map the ordered simplex into the
cusp. -/
theorem mapsTo_branchMap_simplexCusp {a : ℕ × Fin (d + 1)} (ha : a.1 ≠ 0) :
    MapsTo (branchMap a) (orderedSimplex (d + 1)) (simplexCusp d) :=
  fun _ hx => branchMap_mem_simplexCusp ha hx

/-! ### Coordinate bounds -/

/-- On `Δ₀` the last coordinate `w_{n-1}` is at least `1 / 2`. -/
theorem one_half_le_one_sub_sum_of_mem_simplexHalf {x : Fin d → ℝ} (hx : x ∈ simplexHalf d) :
    1 / 2 ≤ 1 - ∑ k, x k := by
  linarith [(mem_simplexHalf_iff.mp hx).2]

/-- On `Δ₀`, `w_{n-j} ≤ 1 / (2 (j - 1))` for `2 ≤ j ≤ n - 1`: in chart coordinates,
`xᵢ ≤ 1 / (2 (d - i))`, since the `d - i` coordinates from `xᵢ` on are each at least `xᵢ` and sum
to at most `1 / 2`. -/
theorem le_one_div_two_mul_of_mem_simplexHalf {x : Fin d → ℝ} (hx : x ∈ simplexHalf d)
    (i : Fin d) : x i ≤ 1 / (2 * (d - i : ℕ)) := by
  have hm : (0 : ℝ) < (d - i : ℕ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt i.isLt)
  have h := sub_mul_le_sum_of_mem_orderedSimplex (simplexHalf_subset_orderedSimplex hx) i
  rw [le_div_iff₀ (by positivity)]
  linarith [(mem_simplexHalf_iff.mp hx).2]

/-- On `Δ₀`, `w_{n-3} ≤ 1 / 4`. -/
theorem le_one_div_four_of_mem_simplexHalf {x : Fin (d + 2) → ℝ} (hx : x ∈ simplexHalf (d + 2)) :
    x (Fin.last d).castSucc ≤ 1 / 4 := by
  have h := le_one_div_two_mul_of_mem_simplexHalf hx (Fin.last d).castSucc
  norm_num [show d + 2 - d = 2 by omega] at h
  exact h

/-- On the cusp, the last coordinate satisfies `w_{n-1} ≥ (1 + w_{n-2}) / 2`. -/
theorem one_add_div_two_le_one_sub_sum_of_mem_simplexCusp {x : Fin (d + 1) → ℝ}
    (hx : x ∈ simplexCusp d) : (1 + x (Fin.last d)) / 2 ≤ 1 - ∑ k, x k := by
  linarith [(mem_simplexCusp_iff.mp hx).2]

/-- On the cusp, `w_{n-j} ≤ 1 / (2 j - 1)` for `2 ≤ j ≤ n - 1`: in chart coordinates,
`xᵢ ≤ 1 / (2 (d + 1 - i) + 1)`, since `xᵢ ≤ w_{n-2}`, the `d + 1 - i` coordinates from `xᵢ` on
are each at least `xᵢ`, and `w_{n-2} + 2 b ≤ 1`. -/
theorem le_one_div_two_mul_add_one_of_mem_simplexCusp {x : Fin (d + 1) → ℝ}
    (hx : x ∈ simplexCusp d) (i : Fin (d + 1)) : x i ≤ 1 / (2 * (d + 1 - i : ℕ) + 1) := by
  obtain ⟨hx, hcusp⟩ := mem_simplexCusp_iff.mp hx
  have h := sub_mul_le_sum_of_mem_orderedSimplex hx i
  have hi := (mem_orderedSimplex_iff.mp hx).2.1 (Fin.le_last i)
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- On the cusp, `w_{n-2} ≤ 1 / 3`. -/
theorem le_one_div_three_of_mem_simplexCusp {x : Fin (d + 1) → ℝ} (hx : x ∈ simplexCusp d) :
    x (Fin.last d) ≤ 1 / 3 := by
  have h := le_one_div_two_mul_add_one_of_mem_simplexCusp hx (Fin.last d)
  norm_num at h
  exact h

/-- On the cusp, `w_{n-3} ≤ 1 / 5`. -/
theorem le_one_div_five_of_mem_simplexCusp {x : Fin (d + 2) → ℝ} (hx : x ∈ simplexCusp (d + 1)) :
    x (Fin.last d).castSucc ≤ 1 / 5 := by
  have h := le_one_div_two_mul_add_one_of_mem_simplexCusp hx (Fin.last d).castSucc
  norm_num [show d + 2 - d = 2 by omega] at h
  exact h

end TauCeti

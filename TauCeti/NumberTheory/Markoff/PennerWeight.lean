/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Markoff.Basic
public import Mathlib.Algebra.Field.Defs

import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Penner weights on the Markoff surface

Let `K` be a field in which `2` and `3` are nonzero. A point `x` of the nonzero locus `X*(K)` of
the Markoff surface `x₀² + x₁² + x₂² = 3 x₀ x₁ x₂` carries three *Penner weights*
`w₀(x), w₁(x), w₂(x) ∈ K`. When the two coordinates other than `x_i` are nonzero,
`w_i(x) = x_i / (3 x_{i+1} x_{i+2})`; otherwise one of them vanishes and `w_i(x) = 1/2`. A point
of `X*(K)` has at most one vanishing coordinate (`apply_ne_zero_of_mem_markoffSetNonzero`), so
if `x_{i₀} = 0` its weights are `w_{i₀} = 0` and `1/2` at the other two indices.

The weights have two properties, which together give Chen's divisibility theorem for Markoff
graphs:

* they sum to `1` at every point of `X*(K)`, which for points with no vanishing coordinate is the
  Markoff equation divided by `3 x₀ x₁ x₂`;
* the `i`-th Vieta move exchanges `w_i` with `1 - w_i`, at every triple of `K³`, because it
  replaces `x_i` by the other root `3 x_{i+1} x_{i+2} - x_i`.

In particular a triple fixed by the `i`-th move has `w_i = 1/2`.

## Main definitions

* `TauCeti.pennerWeight i x`: the `i`-th Penner weight of a triple `x : Fin 3 → K`.

## Main results

* `TauCeti.sum_pennerWeight`: the three weights of a point of `X*(K)` sum to `1`.
* `TauCeti.pennerWeight_add_pennerWeight_markoffVieta`: `w_i(x) + w_i(R_i x) = 1`.
* `TauCeti.pennerWeight_comp_perm`: the weights are equivariant under coordinate permutations.

## References

* D. E. Martin, *A new proof of Chen's theorem for Markoff graphs*, Invent. Math. 241 (2025),
  623–626, §2, equation (2.1).
-/

public section

namespace TauCeti

variable {K : Type*} [Field K]

open Classical in
/-- The `i`-th Penner weight of a triple `x : Fin 3 → K`: it is `x_i / (3 x_{i+1} x_{i+2})` when
`x_{i+1} x_{i+2} ≠ 0`, and `1/2` otherwise. On the nonzero locus `X*(K)` the second case occurs
exactly when one of the two coordinates other than `x_i` vanishes. The weights are meaningful on
`X*(K)` when `2` and `3` are nonzero in `K`; elsewhere they carry no assertion. -/
noncomputable def pennerWeight (i : Fin 3) (x : Fin 3 → K) : K :=
  if x (i + 1) * x (i + 2) = 0 then 2⁻¹ else x i / (3 * x (i + 1) * x (i + 2))

/-- When the two coordinates other than `x_i` are nonzero, `w_i(x) = x_i / (3 x_{i+1} x_{i+2})`;
this includes the case `x_i = 0`, where the weight is `0`. -/
theorem pennerWeight_of_mul_ne_zero {i : Fin 3} {x : Fin 3 → K}
    (h : x (i + 1) * x (i + 2) ≠ 0) :
    pennerWeight i x = x i / (3 * x (i + 1) * x (i + 2)) := by
  simp [pennerWeight, h]

/-- When one of the two coordinates other than `x_i` vanishes, `w_i(x) = 1/2`. -/
theorem pennerWeight_of_mul_eq_zero {i : Fin 3} {x : Fin 3 → K}
    (h : x (i + 1) * x (i + 2) = 0) : pennerWeight i x = 2⁻¹ := by
  simp [pennerWeight, h]

/-- If a coordinate `x_j` with `j ≠ i` vanishes, then `w_i(x) = 1/2`. -/
theorem pennerWeight_eq_inv_two_of_apply_eq_zero_of_ne {i j : Fin 3} {x : Fin 3 → K} (h : x j = 0)
    (hij : i ≠ j) : pennerWeight i x = 2⁻¹ := by
  refine pennerWeight_of_mul_eq_zero ?_
  fin_cases i <;> fin_cases j <;> simp_all

/-- At a point of `X*(K)` whose `i`-th coordinate vanishes, `w_i(x) = 0`: the two other
coordinates are then nonzero. -/
theorem pennerWeight_eq_zero_of_apply_eq_zero {i : Fin 3} {x : Fin 3 → K}
    (hx : x ∈ markoffSetNonzero K) (h : x i = 0) : pennerWeight i x = 0 := by
  have h1 : x (i + 1) ≠ 0 := apply_ne_zero_of_mem_markoffSetNonzero hx h (by simp)
  have h2 : x (i + 2) ≠ 0 := apply_ne_zero_of_mem_markoffSetNonzero hx h (by simp)
  rw [pennerWeight_of_mul_ne_zero (mul_ne_zero h1 h2), h, zero_div]

/-- The Penner weights are equivariant under coordinate permutations: with `P_σ x = x ∘ σ⁻¹`, so
that `(P_σ x) (σ i) = x i`, one has `w_{σ i}(P_σ x) = w_i(x)`. -/
@[simp]
theorem pennerWeight_comp_perm (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (x : Fin 3 → K) :
    pennerWeight (σ i) (x ∘ σ.symm) = pennerWeight i x := by
  have hmul : (x ∘ σ.symm) (σ i + 1) * (x ∘ σ.symm) (σ i + 2) = x (i + 1) * x (i + 2) :=
    apply_add_one_mul_apply_add_two_comp_perm σ i x
  by_cases h : x (i + 1) * x (i + 2) = 0
  · rw [pennerWeight_of_mul_eq_zero h, pennerWeight_of_mul_eq_zero (hmul ▸ h)]
  · rw [pennerWeight_of_mul_ne_zero h, pennerWeight_of_mul_ne_zero (hmul ▸ h)]
    simp [mul_assoc, apply_add_one_mul_apply_add_two_comp_perm]

/-- **The Penner weights sum to one.** If `2` and `3` are nonzero in `K`, the three weights of a
point of the nonzero locus `X*(K)` sum to `1`. -/
theorem sum_pennerWeight (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {x : Fin 3 → K}
    (hx : x ∈ markoffSetNonzero K) : ∑ i, pennerWeight i x = 1 := by
  by_cases hzero : ∃ k, x k = 0
  · -- One coordinate vanishes: its weight is `0` and the other two are `1/2`.
    obtain ⟨k, hk⟩ := hzero
    have hw : ∀ i, pennerWeight i x = if i = k then 0 else 2⁻¹ := fun i => by
      split_ifs with hik
      · exact pennerWeight_eq_zero_of_apply_eq_zero hx (hik ▸ hk)
      · exact pennerWeight_eq_inv_two_of_apply_eq_zero_of_ne hk hik
    fin_cases k <;> simp [hw, Fin.sum_univ_three, ← two_mul, h2]
  · -- No coordinate vanishes: divide the Markoff equation by `3 x₀ x₁ x₂`.
    push Not at hzero
    have hm := mem_markoffSet.mp (markoffSetNonzero_subset_markoffSet hx)
    simp only [Fin.sum_univ_three]
    rw [pennerWeight_of_mul_ne_zero (mul_ne_zero (hzero _) (hzero _)),
      pennerWeight_of_mul_ne_zero (mul_ne_zero (hzero _) (hzero _)),
      pennerWeight_of_mul_ne_zero (mul_ne_zero (hzero _) (hzero _))]
    simp only [Fin.isValue, Fin.reduceAdd]
    field_simp [hzero 0, hzero 1, hzero 2]
    linear_combination hm

/-- **The Vieta moves complement the Penner weights.** If `2` and `3` are nonzero in `K`, then
`w_i(x) + w_i(R_i x) = 1` for every triple `x : Fin 3 → K`, on the Markoff surface or not: the
move keeps `x_{i+1}` and `x_{i+2}` and replaces `x_i` by `3 x_{i+1} x_{i+2} - x_i`. -/
theorem pennerWeight_add_pennerWeight_markoffVieta (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (i : Fin 3) (x : Fin 3 → K) :
    pennerWeight i x + pennerWeight i (markoffVieta i x) = 1 := by
  have hR1 : markoffVieta i x (i + 1) = x (i + 1) := markoffVieta_apply_of_ne (by simp) x
  have hR2 : markoffVieta i x (i + 2) = x (i + 2) := markoffVieta_apply_of_ne (by simp) x
  by_cases h : x (i + 1) * x (i + 2) = 0
  · rw [pennerWeight_of_mul_eq_zero h, pennerWeight_of_mul_eq_zero (by rwa [hR1, hR2])]
    field_simp
    norm_num
  · rw [pennerWeight_of_mul_ne_zero h, pennerWeight_of_mul_ne_zero (by rwa [hR1, hR2]), hR1, hR2,
      markoffVieta_apply_self]
    obtain ⟨h1, h2'⟩ := mul_ne_zero_iff.mp h
    field_simp
    ring

/-- A triple fixed by the `i`-th Vieta move has `i`-th Penner weight `1/2`, provided `2` and `3`
are nonzero in `K`. -/
theorem pennerWeight_eq_inv_two_of_markoffVieta_eq (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {i : Fin 3} {x : Fin 3 → K} (h : markoffVieta i x = x) : pennerWeight i x = 2⁻¹ := by
  have hadd := pennerWeight_add_pennerWeight_markoffVieta h2 h3 i x
  rw [h, ← two_mul] at hadd
  exact eq_inv_of_mul_eq_one_right hadd

end TauCeti

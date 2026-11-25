/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.GelfandTsetlin

/-!
# The top hive

For dominant weights `λ` and `μ`, the output `γ = λ + μ` has exactly one integer hive with
boundary `(λ, μ, γ*)`: the **top hive** `TauCeti.Hive.topHive λ μ`, with value
`λ₁ + ⋯ + λ_{y+z} + μ₁ + ⋯ + μ_z` at `(x, y, z)`. It is the hive `TauCeti.Hive.ofGTPattern` of
the highest-weight pattern `TauCeti.GTPattern.highest μ` over `λ`. Conversely, the difference
pattern `h.toGTPattern` of a hive `h` with this boundary has top row `μ` and weight `γ - λ = μ`,
so it is the highest-weight pattern (`TauCeti.GTPattern.eq_highest_iff`), and `h` is the top
hive. Hence `hiveCount (productBoundary λ μ (λ + μ)) = 1`.

## Main definitions

* `TauCeti.Hive.topHive`: the unique integer hive with boundary `(λ, μ, (λ + μ)*)`.

## Main results

* `TauCeti.Hive.boundary_topHive`: the boundary of the top hive.
* `TauCeti.Hive.eq_topHive_of_productBoundary`, `TauCeti.Hive.hiveCount_productBoundary_add`: the
  top hive is the only integer hive with its boundary.

## References

* A. Knutson, T. Tao, and C. Woodward, *A positive proof of the Littlewood–Richardson rule using
  the octahedron recurrence*, Electron. J. Combin. **11** (2004), R61, §4, Proposition 4.
-/

public section

namespace TauCeti.Hive

variable {n : ℕ}

/-- Over `λ`, the highest-weight pattern of `μ` completes to `λ₁ + ⋯ + λⱼ + μ₁ + ⋯ + μᵢ` at the
product-chart vertex in column `i` of row `j`. -/
theorem gtCompletion_highest (lam μ : DominantWeight n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    gtCompletion lam (GTPattern.highest μ) i j = prefixSum j lam.val + prefixSum i μ.val := by
  rw [gtCompletion_def, ← GTPattern.rowSum_highest μ (hij.trans hj), GTPattern.rowSum_def]
  congr 1
  exact Finset.sum_congr rfl fun k hk => by
    have := Finset.mem_range.mp hk
    rw [GTPattern.highest_apply_of_lt_of_le μ (by omega) hj,
      GTPattern.highest_apply_of_lt_of_le μ this (by omega)]

theorem isGTCompletable_highest (lam μ : DominantWeight n) :
    IsGTCompletable lam (GTPattern.highest μ) := by
  rw [isGTCompletable_def]
  intro i j hij hj
  rw [gtCompletion_highest lam μ hij (by omega), gtCompletion_highest lam μ (by omega) hj,
    gtCompletion_highest lam μ (by omega : i ≤ j + 1) (by omega),
    gtCompletion_highest lam μ (by omega : i + 1 ≤ j + 1) (by omega)]
  have := prefixSum_add_prefixSum_add_two_le lam.antitone hj
  omega

/-- The **top hive** of `(λ, μ)`: the hive of the highest-weight pattern of `μ` over `λ`, with value
`λ₁ + ⋯ + λ_{y+z} + μ₁ + ⋯ + μ_z` at `(x, y, z)` (`TauCeti.Hive.topHive_apply`). Its boundary is
`(λ, μ, (λ + μ)*)` (`TauCeti.Hive.boundary_topHive`), and it is the only integer hive with that
boundary (`TauCeti.Hive.eq_topHive_of_productBoundary`). -/
def topHive (lam μ : DominantWeight n) : IntegerHive n :=
  ofGTPattern lam (GTPattern.highest μ) (isGTCompletable_highest lam μ)

@[simp] theorem topHive_apply (lam μ : DominantWeight n) (p : Vertex n) :
    topHive lam μ p = prefixSum (p.y + p.z) lam.val + prefixSum p.z μ.val := by
  have hp := p.sum_eq
  rw [topHive, ofGTPattern_apply, gtCompletion_highest lam μ (by omega) (Nat.sub_le n p.x),
    show n - p.x = p.y + p.z by omega]

/-- The difference pattern of the top hive is the highest-weight pattern of `μ`. -/
@[simp] theorem toGTPattern_topHive (lam μ : DominantWeight n) :
    (topHive lam μ).toGTPattern = GTPattern.highest μ :=
  toGTPattern_ofGTPattern ..

@[simp] theorem topHive_zero : topHive (0 : DominantWeight n) 0 = 0 := by
  ext p; simp

/-- The top hive is additive in the pair of inputs. -/
theorem topHive_add (lam₁ lam₂ μ₁ μ₂ : DominantWeight n) :
    topHive (lam₁ + lam₂) (μ₁ + μ₂) = topHive lam₁ μ₁ + topHive lam₂ μ₂ := by
  ext p; simp only [topHive_apply, add_apply, DominantWeight.coe_add, prefixSum_add]; abel

/-- The top hive has boundary `(λ, μ, (λ + μ)*)`. -/
@[simp] theorem boundary_topHive (lam μ : DominantWeight n) :
    (topHive lam μ).boundary = productBoundary lam μ (lam + μ) :=
  boundary_ofGTPattern_eq_productBoundary (GTPattern.topRow_highest μ)
    (by rw [GTPattern.rowWeight_highest, DominantWeight.coe_add, add_sub_cancel_left]) _

/-- **Uniqueness of the top hive**: every integer hive with boundary `(λ, μ, (λ + μ)*)` is
`TauCeti.Hive.topHive λ μ`. -/
theorem eq_topHive_of_productBoundary {lam μ : DominantWeight n} {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ (lam + μ)) : h = topHive lam μ := by
  refine eq_of_boundary_zero_eq_of_toGTPattern_eq
    (by rw [hb, topHive, boundary_ofGTPattern_zero, productBoundary_zero]) ?_
  rw [toGTPattern_topHive, GTPattern.eq_highest_iff]
  exact ⟨topRow_toGTPattern_of_productBoundary hb, by
    rw [rowWeight_toGTPattern_of_productBoundary hb, DominantWeight.coe_add, add_sub_cancel_left]⟩

/-- The integer hives with boundary `(λ, μ, (λ + μ)*)` form a one-element type, whose `default`
is `TauCeti.Hive.topHive λ μ`. -/
instance (lam μ : DominantWeight n) :
    Unique (FixedIntegerHive (productBoundary lam μ (lam + μ))) where
  default := ⟨topHive lam μ, boundary_topHive lam μ⟩
  uniq h := Subtype.ext (eq_topHive_of_productBoundary h.property)

/-- **The top coefficient is one**: the hive count of `(λ, μ, (λ + μ)*)` is `1`. For partitions
`λ` and `μ` this says that `V_{λ + μ}` occurs exactly once in `V_λ ⊗ V_μ`. -/
@[simp] theorem hiveCount_productBoundary_add (lam μ : DominantWeight n) :
    hiveCount (productBoundary lam μ (lam + μ)) = 1 := by
  rw [← card_fixedIntegerHive]; exact Fintype.card_unique

/-- For `λ = μ = (1, 0)`, the top hive is the hive `exampleTwo` of the output `(2, 0)`. -/
theorem topHive_two_std_std : topHive ⟨![1, 0], by decide⟩ ⟨![1, 0], by decide⟩ = exampleTwo :=
  (eq_topHive_of_productBoundary (boundary_exampleTwo.trans (by
    congr 1; ext i; fin_cases i <;> simp [DominantWeight.coe_add]))).symm

end TauCeti.Hive

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hive.GelfandTsetlin
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.RowSubset

/-!
# The direct vertical Pieri rule for hives

In the product chart `Vertex.ofChart n i j`, the vertex `(x, y, z)` sits in column `i = z` of row
`j = y + z`. For an integer hive `h` with boundary `(λ, μ, γ*)`, the steps
`h(i + 1, j) - h(i, j)` along the rows form the Gelfand–Tsetlin pattern `h.toGTPattern`, with top
row `μ` and weight `γ - λ`, and `h` is recovered from `λ` and this pattern
(`TauCeti.Hive.apply_eq_gtCompletion_of_productBoundary`). If every entry of `μ` is `0` or `1`, then
so is every entry of the pattern, so it is the row-subset pattern `TauCeti.GTPattern.rowSubset I`
of the rows `I` at which `γ - λ` is `1` (`TauCeti.GTPattern.mem_range_rowSubset`), and each row of
the product chart rises with slope one and then stays flat. Hence the integer hive with boundary
`(λ, μ, γ*)` is `TauCeti.Hive.verticalPieriHive`, and it exists exactly when `γ - λ` is a `0`/`1`
vector with `|γ| = |λ| + |μ|`: the hive count is `1` in that case and `0` otherwise. This is proved
directly from the hive inequalities, without passing through tableaux.

The hive statements hold for all dominant weights, including those with negative coordinates. For
partitions `λ` and `μ = (1^k, 0^(n - k))`, where `k = μ₁ + ⋯ + μₙ`, they are the vertical Pieri rule
`s_λ e_k = ∑ s_γ` in `n` variables, the sum over the partitions `γ` with at most `n` parts such
that `γ / λ` is a vertical strip of size `k`. Adding a `0`/`1` vector to `λ` gives a dominant
weight exactly when the vector decreases weakly along each block of equal coordinates of `λ`
(`TauCeti.DominantWeight.antitone_add_iff_of_zero_le_le_one`).

## Main definitions

* `TauCeti.Hive.verticalPieriHive`: for dominant weights `λ`, `γ` with `γ - λ` a `0`/`1` vector,
  the hive of the row-subset pattern of the rows where `γ - λ` is `1`. Its boundary is
  `(λ, μ, γ*)` for every `0`/`1` weight `μ` with `|μ| = |γ| - |λ|`.

## Main results

* `TauCeti.Hive.le_and_le_add_one_of_productBoundary_of_zero_le_le_one`,
  `TauCeti.Hive.eq_verticalPieriHive_of_productBoundary_of_zero_le_le_one`,
  `TauCeti.Hive.nonempty_fixedIntegerHive_productBoundary_iff_of_zero_le_le_one`,
  `TauCeti.Hive.hiveCount_productBoundary_of_zero_le_le_one`: the direct vertical Pieri rule.
* `TauCeti.Hive.hiveCount_productBoundary_zero_right`,
  `TauCeti.Hive.hiveCount_productBoundary_zero_shift_one_right`: the cases `k = 0` and `k = n`.

## References

* A. Knutson and T. Tao, *The honeycomb model of GLₙ(ℂ) tensor products I: proof of the saturation
  conjecture*, J. Amer. Math. Soc. **12** (1999), Appendix 2.
* I. G. Macdonald, *Symmetric functions and Hall polynomials*, 2nd ed., Oxford University Press,
  1995, Chapter I, (5.17).
-/

public section

namespace TauCeti

namespace Hive

variable {n : ℕ}

/-! ### Vertical Pieri -/

section VerticalPieri

open Finset

variable {lam μ γ : DominantWeight n}

/-- When `γ - λ` is a `0`/`1` vector, it is the weight of the row-subset pattern of the rows where
it is `1`. -/
private theorem rowWeight_rowSubset_eq_sub
    (hγ : ∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1) :
    (GTPattern.rowSubset {r | γ.val r = lam.val r + 1}).rowWeight = γ.val - lam.val := by
  funext r
  have := hγ r
  simp only [GTPattern.rowWeight_rowSubset, Pi.sub_apply, mem_filter, mem_univ, true_and]
  split_ifs <;> omega

/-- Over `λ`, the row-subset pattern of the rows where `γ - λ` is `1` completes to
`λ₁ + ⋯ + λⱼ + min i ((γ - λ)₁ + ⋯ + (γ - λ)ⱼ)` at the product-chart vertex in column `i` of
row `j`. -/
private theorem gtCompletion_rowSubset
    (hγ : ∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1) (i : ℕ) {j : ℕ} (hj : j ≤ n) :
    gtCompletion lam (GTPattern.rowSubset {r | γ.val r = lam.val r + 1}) i j =
      prefixSum j lam.val + min (i : ℤ) (prefixSum j γ.val - prefixSum j lam.val) := by
  rw [gtCompletion_def, GTPattern.sum_range_rowSubset _ hj, Nat.cast_min,
    ← GTPattern.rowSum_rowSubset _ hj, ← GTPattern.prefixSum_rowWeight _ hj,
    rowWeight_rowSubset_eq_sub hγ, prefixSum_sub]

private theorem isGTCompletable_rowSubset
    (hγ : ∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1) :
    IsGTCompletable lam (GTPattern.rowSubset {r | γ.val r = lam.val r + 1}) := by
  rw [isGTCompletable_def]
  intro i j _ hj
  simp only [gtCompletion_rowSubset hγ _ (by omega : j ≤ n),
    gtCompletion_rowSubset hγ _ (by omega : j + 1 ≤ n), gtCompletion_rowSubset hγ _ hj]
  have h₁ := prefixSum_succ (k := j) (by omega) lam.val
  have h₂ : prefixSum (j + 2) lam.val = prefixSum (j + 1) lam.val + lam.val ⟨j + 1, by omega⟩ :=
    prefixSum_succ (by omega) lam.val
  have h₃ := prefixSum_succ (k := j) (by omega) γ.val
  have h₄ : prefixSum (j + 2) γ.val = prefixSum (j + 1) γ.val + γ.val ⟨j + 1, by omega⟩ :=
    prefixSum_succ (by omega) γ.val
  have := prefixSum_add_prefixSum_add_two_le lam.antitone hj
  have := prefixSum_add_prefixSum_add_two_le γ.antitone hj
  have := hγ ⟨j, by omega⟩
  have := hγ ⟨j + 1, by omega⟩
  push_cast; omega

/-- The **vertical Pieri hive** of `λ ⊆ γ`, for `γ - λ` a `0`/`1` vector: the hive over `λ` of the
row-subset pattern of the rows where `γ - λ` is `1`. Its value at `(x, y, z)` is
`λ₁ + ⋯ + λⱼ + min z ((γ - λ)₁ + ⋯ + (γ - λ)ⱼ)` with `j = y + z`
(`TauCeti.Hive.verticalPieriHive_apply`), so each row of the product chart rises with slope one
and then stays flat. Its boundary is `(λ, μ, γ*)` for the `0`/`1` weight `μ` with
`|μ| = |γ| - |λ|` (`TauCeti.Hive.boundary_verticalPieriHive`). -/
def verticalPieriHive (lam γ : DominantWeight n)
    (hγ : ∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1) : IntegerHive n :=
  ofGTPattern lam (GTPattern.rowSubset {r | γ.val r = lam.val r + 1}) (isGTCompletable_rowSubset hγ)

@[simp] theorem verticalPieriHive_apply (hγ : ∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1)
    (p : Vertex n) :
    verticalPieriHive lam γ hγ p = prefixSum (p.y + p.z) lam.val +
      min (p.z : ℤ) (prefixSum (p.y + p.z) γ.val - prefixSum (p.y + p.z) lam.val) := by
  have hp := p.sum_eq
  rw [verticalPieriHive, ofGTPattern_apply, gtCompletion_rowSubset hγ _ (Nat.sub_le n p.x),
    show n - p.x = p.y + p.z by omega]

/-- The difference pattern of the vertical Pieri hive of `λ ⊆ γ` is the row-subset pattern of the
rows where `γ - λ` is `1`. -/
@[simp] theorem toGTPattern_verticalPieriHive
    (hγ : ∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1) :
    (verticalPieriHive lam γ hγ).toGTPattern = GTPattern.rowSubset {r | γ.val r = lam.val r + 1} :=
  toGTPattern_ofGTPattern ..

/-- The side `A → B` of the vertical Pieri hive of `λ ⊆ γ` is `λ`. -/
@[simp] theorem boundary_verticalPieriHive_zero
    (hγ : ∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1) :
    (verticalPieriHive lam γ hγ).boundary 0 = lam.val :=
  boundary_ofGTPattern_zero _ _ _

/-- The side `B → C` of the vertical Pieri hive of `λ ⊆ γ` is the `0`/`1` weight whose entry `i` is
`1` exactly when `i < |γ| - |λ|`. -/
@[simp] theorem boundary_verticalPieriHive_one
    (hγ : ∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1) :
    (verticalPieriHive lam γ hγ).boundary 1 =
      fun i : Fin n => if ((i : ℕ) : ℤ) < ∑ r, γ.val r - ∑ r, lam.val r then 1 else 0 := by
  have hcard : ∑ r, γ.val r - ∑ r, lam.val r = #{r | γ.val r = lam.val r + 1} := by
    rw [← sum_sub_distrib, ← Pi.sub_def, ← rowWeight_rowSubset_eq_sub hγ,
      GTPattern.rowWeight_rowSubset, sum_boole, filter_mem_eq_inter, univ_inter]
  rw [verticalPieriHive, boundary_ofGTPattern_one, GTPattern.topRow_rowSubset, hcard]
  simp only [Nat.cast_lt]

/-- The side `C → A` of the vertical Pieri hive of `λ ⊆ γ` is the dual `γ*` of `γ`. -/
@[simp] theorem boundary_verticalPieriHive_two
    (hγ : ∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1) :
    (verticalPieriHive lam γ hγ).boundary 2 = fun r => -γ.val r.rev := by
  rw [verticalPieriHive, boundary_ofGTPattern_two, rowWeight_rowSubset_eq_sub hγ]
  simp

/-- The vertical Pieri hive has boundary `(λ, μ, γ*)` for every `0`/`1` weight `μ` with
`|λ| + |μ| = |γ|`. -/
theorem boundary_verticalPieriHive (hγ : ∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1)
    (hμ : ∀ i, 0 ≤ μ.val i ∧ μ.val i ≤ 1) (hsum : ∑ i, γ.val i = ∑ i, lam.val i + ∑ i, μ.val i) :
    (verticalPieriHive lam γ hγ).boundary = productBoundary lam μ γ := by
  refine boundary_ofGTPattern_eq_productBoundary ?_ (rowWeight_rowSubset_eq_sub hγ) _
  -- A weakly decreasing `0`/`1` weight is `1` exactly before its sum.
  have hcard : (#{j | 1 ≤ μ.val j} : ℤ) = ∑ r, γ.val r - ∑ r, lam.val r := by
    rw [hsum, add_sub_cancel_left, natCast_card_filter]
    exact sum_congr rfl fun j _ => by have := hμ j; split_ifs <;> omega
  have h₁ := boundary_verticalPieriHive_one hγ
  rw [verticalPieriHive, boundary_ofGTPattern_one] at h₁
  rw [h₁, ← hcard]
  funext i
  have hi := Tuple.lt_card_ge_iff_apply_ge_of_antitone (j := i) (a := (1 : ℤ)) μ.antitone
  have := hμ i
  split_ifs with h
  · have := hi.mp (by exact_mod_cast h)
    omega
  · have := mt hi.mpr (by exact_mod_cast h)
    omega

/-- The entries of a `0`/`1` weight lie in `[0, 1]`, so its last entry is at least `0` and its first
entry is at most `1`. -/
private theorem zero_le_last_and_first_le_one (hμ : ∀ i, 0 ≤ μ.val i ∧ μ.val i ≤ 1) (hn : 0 < n) :
    0 ≤ μ.val ⟨n - 1, by omega⟩ ∧ μ.val ⟨0, hn⟩ ≤ 1 :=
  ⟨(hμ _).1, (hμ _).2⟩

/-- **Vertical strip condition**: if an integer hive has boundary `(λ, μ, γ*)` with `μ` a `0`/`1`
weight, then `γ - λ` is a `0`/`1` vector. -/
theorem le_and_le_add_one_of_productBoundary_of_zero_le_le_one {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hμ : ∀ i, 0 ≤ μ.val i ∧ μ.val i ≤ 1) (k : Fin n) :
    lam.val k ≤ γ.val k ∧ γ.val k ≤ lam.val k + 1 := by
  have := k.isLt
  have hk := sub_mem_Icc_of_productBoundary hb k
  have := zero_le_last_and_first_le_one hμ (by omega)
  simp only [Set.mem_Icc] at hk
  omega

/-- **Uniqueness for vertical Pieri**: an integer hive with boundary `(λ, μ, γ*)` for a `0`/`1`
weight `μ` is `TauCeti.Hive.verticalPieriHive λ γ _`. -/
theorem eq_verticalPieriHive_of_productBoundary_of_zero_le_le_one {h : IntegerHive n}
    (hb : h.boundary = productBoundary lam μ γ) (hμ : ∀ i, 0 ≤ μ.val i ∧ μ.val i ≤ 1) :
    h = verticalPieriHive lam γ (le_and_le_add_one_of_productBoundary_of_zero_le_le_one hb hμ) := by
  -- The difference pattern has entries in `{0, 1}`, so it is a row-subset pattern, and its weight
  -- `γ - λ` identifies the subset.
  have h01 (i j : ℕ) : h.toGTPattern i j = 0 ∨ h.toGTPattern i j = 1 := by
    by_cases hij : i < j ∧ j ≤ n
    · have hk := h.toGTPattern.entry_mem_Icc hij.1 hij.2
      rw [topRow_toGTPattern_of_productBoundary hb] at hk
      have := zero_le_last_and_first_le_one hμ (by omega)
      simp only [Set.mem_Icc] at hk
      omega
    · exact Or.inl (h.toGTPattern.entry_eq_zero (by omega))
  obtain ⟨I, hI⟩ := GTPattern.mem_range_rowSubset.mpr h01
  have hIγ : I = ({r | γ.val r = lam.val r + 1} : Finset (Fin n)) := by
    ext r
    have hw := congrFun (rowWeight_toGTPattern_of_productBoundary hb) r
    simp only [← hI, GTPattern.rowWeight_rowSubset, Pi.sub_apply] at hw
    simp only [mem_filter, mem_univ, true_and]
    by_cases hr : r ∈ I <;> simp only [hr, ite_true, ite_false, true_iff, false_iff] at hw ⊢ <;>
      omega
  refine eq_of_boundary_zero_eq_of_toGTPattern_eq
    (by rw [hb, boundary_verticalPieriHive_zero, productBoundary_zero]) ?_
  rw [toGTPattern_verticalPieriHive, ← hIγ, hI]

/-- For a `0`/`1` weight `μ`, there is at most one integer hive with boundary `(λ, μ, γ*)`. -/
theorem subsingleton_fixedIntegerHive_productBoundary_of_zero_le_le_one
    (hμ : ∀ i, 0 ≤ μ.val i ∧ μ.val i ≤ 1) :
    Subsingleton (FixedIntegerHive (productBoundary lam μ γ)) :=
  ⟨fun h₁ h₂ => Subtype.ext <|
    (eq_verticalPieriHive_of_productBoundary_of_zero_le_le_one h₁.property hμ).trans
      (eq_verticalPieriHive_of_productBoundary_of_zero_le_le_one h₂.property hμ).symm⟩

/-- **Direct vertical Pieri rule for hives**: when `μ` is a `0`/`1` weight (the highest weight of
an exterior power `Λᵏ ℂⁿ`, `k = |μ|`), the integer hives with boundary `(λ, μ, γ*)` exist
exactly when `γ - λ` is a `0`/`1` vector with `|γ| = |λ| + |μ|`. -/
theorem nonempty_fixedIntegerHive_productBoundary_iff_of_zero_le_le_one
    (hμ : ∀ i, 0 ≤ μ.val i ∧ μ.val i ≤ 1) :
    Nonempty (FixedIntegerHive (productBoundary lam μ γ)) ↔
      (∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1) ∧
        ∑ i, γ.val i = ∑ i, lam.val i + ∑ i, μ.val i :=
  ⟨fun ⟨⟨_, hb⟩⟩ => ⟨le_and_le_add_one_of_productBoundary_of_zero_le_le_one hb hμ,
    (sum_eq_of_productBoundary hb).symm⟩,
   fun ⟨hγ, hsum⟩ => ⟨⟨verticalPieriHive lam γ hγ, boundary_verticalPieriHive hγ hμ hsum⟩⟩⟩

/-- **Vertical Pieri rule as a hive count**: for a `0`/`1` weight `μ`, the hive count of
`(λ, μ, γ*)` is `1` when `γ - λ` is a `0`/`1` vector with `|γ| = |λ| + |μ|`, and `0` otherwise. -/
theorem hiveCount_productBoundary_of_zero_le_le_one (hμ : ∀ i, 0 ≤ μ.val i ∧ μ.val i ≤ 1) :
    hiveCount (productBoundary lam μ γ) =
      if (∀ i, lam.val i ≤ γ.val i ∧ γ.val i ≤ lam.val i + 1) ∧
          ∑ i, γ.val i = ∑ i, lam.val i + ∑ i, μ.val i then 1 else 0 := by
  have := subsingleton_fixedIntegerHive_productBoundary_of_zero_le_le_one (lam := lam) (γ := γ) hμ
  split_ifs with hc
  · rw [← card_fixedIntegerHive]
    have : Nonempty (FixedIntegerHive (productBoundary lam μ γ)) :=
      (nonempty_fixedIntegerHive_productBoundary_iff_of_zero_le_le_one hμ).mpr hc
    exact Fintype.card_eq_one_iff_nonempty_unique.mpr
      ⟨uniqueOfSubsingleton (Classical.choice this)⟩
  · rw [hiveCount_eq_zero_iff]
    exact not_nonempty_iff.mp fun hne =>
      hc ((nonempty_fixedIntegerHive_productBoundary_iff_of_zero_le_le_one hμ).mp hne)

/-- **Vertical Pieri with `k = 0`**: the hive count of `(λ, 0, γ*)` is `1` for `γ = λ` and `0`
otherwise. -/
theorem hiveCount_productBoundary_zero_right (lam γ : DominantWeight n) :
    hiveCount (productBoundary lam 0 γ) = if γ = lam then 1 else 0 := by
  rw [hiveCount_productBoundary_of_zero_le_le_one fun _ => by simp]
  refine if_congr ⟨fun ⟨hle, hsum⟩ => Subtype.ext (funext fun i => ?_), ?_⟩ rfl rfl
  · simp only [DominantWeight.coe_zero, Pi.zero_apply, sum_const_zero, add_zero] at hsum
    exact ((sum_eq_sum_iff_of_le fun i _ => (hle i).1).mp hsum.symm i (mem_univ i)).symm
  · rintro rfl
    simp

/-- **Vertical Pieri with `k = n`**: the hive count of `(λ, (1, …, 1), γ*)` is `1` for the
determinant twist `γ = λ + (1, …, 1)` and `0` otherwise. -/
theorem hiveCount_productBoundary_zero_shift_one_right (lam γ : DominantWeight n) :
    hiveCount (productBoundary lam ((0 : DominantWeight n).shift 1) γ) =
      if γ = lam.shift 1 then 1 else 0 := by
  rw [hiveCount_productBoundary_of_zero_le_le_one fun _ => by simp [DominantWeight.shift_apply]]
  refine if_congr ⟨fun ⟨hle, hsum⟩ => Subtype.ext (funext fun i => ?_), ?_⟩ rfl rfl
  · simp only [DominantWeight.shift_apply, DominantWeight.zero_apply, zero_add] at hle hsum ⊢
    rw [← sum_add_distrib] at hsum
    exact (sum_eq_sum_iff_of_le fun i _ => (hle i).2).mp hsum i (mem_univ i)
  · rintro rfl
    simp [DominantWeight.shift_apply, sum_add_distrib]

end VerticalPieri

/-! ### Rank-`2` checks -/

section Checks

/-- Rank-`2` vertical Pieri check `c^{(3, 0)}_{(2, 0), (1, 0)} = 1`. -/
theorem hiveCount_two_sym_std_three_zero :
    hiveCount
      (productBoundary ⟨![2, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![3, 0], by decide⟩) = 1 := by
  rw [hiveCount_productBoundary_of_zero_le_le_one (by decide)]; decide

/-- Rank-`2` vertical Pieri check `c^{(2, 1)}_{(2, 0), (1, 0)} = 1`. -/
theorem hiveCount_two_sym_std_two_one :
    hiveCount
      (productBoundary ⟨![2, 0], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 1], by decide⟩) = 1 := by
  rw [hiveCount_productBoundary_of_zero_le_le_one (by decide)]; decide

/-- Rank-`2` vertical Pieri check `c^{(2, 1)}_{(1, 1), (1, 0)} = 1`. -/
theorem hiveCount_two_det_std_two_one :
    hiveCount
      (productBoundary ⟨![1, 1], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 1], by decide⟩) = 1 := by
  rw [hiveCount_productBoundary_of_zero_le_le_one (by decide)]; decide

/-- Rank-`2` vertical Pieri exclusion `c^{(2, 0)}_{(1, 1), (1, 0)} = 0`: the difference `(1, -1)`
of `(2, 0)` with `λ = (1, 1)` is not a `0`/`1` vector. -/
theorem hiveCount_two_det_std_two_zero :
    hiveCount
      (productBoundary ⟨![1, 1], by decide⟩ ⟨![1, 0], by decide⟩ ⟨![2, 0], by decide⟩) = 0 := by
  rw [hiveCount_productBoundary_of_zero_le_le_one (by decide)]; decide

/-- For `λ = (1, 1)`, of the two `0`/`1` candidates `λ + (1, 0) = (2, 1)` and `λ + (0, 1) = (1, 2)`
for `k = 1`, the dominance criterion rejects `(1, 2)`. -/
theorem not_antitone_two_one_one_add_zero_one :
    ¬ Antitone ((⟨![1, 1], by decide⟩ : DominantWeight 2).val + ![0, 1]) := by
  rw [DominantWeight.antitone_add_iff_of_zero_le_le_one _ (by decide)]
  intro h
  exact absurd (h (show (0 : Fin 2) ≤ 1 by decide) rfl) (by decide)

end Checks

end TauCeti.Hive

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.ConvexSpace.Defs

/-!
# Cumulative prefix-sum coordinates on standard simplices

A point `w` of the finite standard simplex `Convexity.StdSimplex R (Fin n)` has `n` nonnegative
weights summing to `1`. Its cumulative prefix sums `w.prefixSum : Fin (n + 1) → R` form a monotone
sequence from `0` to `1` whose successive differences recover the weights. Conversely, every
monotone sequence `0 = t₀ ≤ t₁ ≤ ⋯ ≤ t_n = 1` arises in this way
(`Convexity.StdSimplex.equivPrefixSum`), with strictly increasing sequences corresponding to the
open interior where every weight is positive.

Embedding a facet along `p.succAbove` repeats the `p`-th cumulative sum via `p.predAbove`, while
merging two adjacent vertices `p.castSucc` and `p.succ` along `p.predAbove` deletes the internal
sum `t_{p+1}`.

## Main definitions

* `Convexity.StdSimplex.prefixSum`: cumulative prefix sums `0 = t₀ ≤ ⋯ ≤ t_n = 1` of a point of
  `StdSimplex R (Fin n)`.
* `Convexity.StdSimplex.equivPrefixSum`: the equivalence between `StdSimplex R (Fin n)` and
  monotone sequences in `[0, 1]` from `0` to `1`.

## Main results

* `Convexity.StdSimplex.strictMono_prefixSum_iff`: the prefix sums strictly increase exactly when
  every barycentric weight is strictly positive.
* `Convexity.StdSimplex.prefixSum_map_of_lt_iff`, `Convexity.StdSimplex.prefixSum_map_finCongr`,
  `Convexity.StdSimplex.prefixSum_map_succAbove`, `Convexity.StdSimplex.prefixSum_map_predAbove`:
  how general maps, reindexing, facet inclusions, and adjacent-vertex merges act on cumulative
  prefix sums.
-/

public section

namespace Convexity.StdSimplex

/-- The `k`-th cumulative prefix sum `∑_{j < k} w_j` of a point `w` of `StdSimplex R (Fin n)`,
for `k : Fin (n + 1)`. It runs from `0` at `k = 0` to `1` at `k = n` (when `R` is nontrivial or
`n` is nonzero). -/
def prefixSum {R : Type*} [LE R] [AddCommMonoid R] [One R] {n : ℕ}
    (w : StdSimplex R (Fin n)) (k : Fin (n + 1)) : R :=
  TauCeti.prefixSum k.val w.weights

/-- The defining formula of `prefixSum` in terms of `TauCeti.prefixSum` on weights. -/
theorem prefixSum_def {R : Type*} [LE R] [AddCommMonoid R] [One R] {n : ℕ}
    (w : StdSimplex R (Fin n)) (k : Fin (n + 1)) :
    w.prefixSum k = TauCeti.prefixSum k.val w.weights :=
  (rfl)

/-- The initial prefix sum at `0` is `0`. -/
@[simp]
theorem prefixSum_zero {R : Type*} [LE R] [AddCommMonoid R] [One R] {n : ℕ}
    (w : StdSimplex R (Fin n)) : w.prefixSum 0 = 0 := by
  simp [prefixSum_def]

/-- Advancing past the `j`-th vertex adds its weight to the cumulative prefix sum. -/
theorem prefixSum_castSucc_add_weights {R : Type*} [LE R] [AddCommMonoid R] [One R] {n : ℕ}
    (w : StdSimplex R (Fin n)) (j : Fin n) :
    w.prefixSum j.castSucc + w.weights j = w.prefixSum j.succ :=
  (TauCeti.prefixSum_succ j.isLt w.weights).symm

/-- The final prefix sum at `Fin.last n` is `1`, the total weight of the simplex point. -/
@[simp]
theorem prefixSum_last {R : Type*} [LE R] [AddCommMonoid R] [One R] {n : ℕ}
    (w : StdSimplex R (Fin n)) : w.prefixSum (Fin.last n) = 1 := by
  rw [prefixSum_def, Fin.val_last, TauCeti.prefixSum_of_le le_rfl]
  simpa [Finsupp.sum_fintype] using w.total

/-- Each weight is the difference of the two adjacent cumulative prefix sums. -/
@[simp]
theorem prefixSum_succ_sub_castSucc {R : Type*} [LE R] [AddCommGroup R] [One R] {n : ℕ}
    (w : StdSimplex R (Fin n)) (j : Fin n) :
    w.prefixSum j.succ - w.prefixSum j.castSucc = w.weights j := by
  rw [← w.prefixSum_castSucc_add_weights j, add_sub_cancel_left]

/-- A point of `StdSimplex R (Fin n)` is determined by its cumulative prefix sums. -/
theorem prefixSum_injective {R : Type*} [LE R] [AddCommGroup R] [One R] {n : ℕ} :
    Function.Injective (prefixSum (R := R) (n := n)) := by
  intro w₁ w₂ h
  have hw : w₁.weights = w₂.weights := by
    ext j
    rw [← w₁.prefixSum_succ_sub_castSucc j, ← w₂.prefixSum_succ_sub_castSucc j,
      congrFun h j.succ, congrFun h j.castSucc]
  cases w₁
  cases w₂
  congr 1

/-- Two points of `StdSimplex R (Fin n)` have the same cumulative prefix sums if and only if they
are equal. -/
@[simp]
theorem prefixSum_inj {R : Type*} [LE R] [AddCommGroup R] [One R] {n : ℕ}
    {w₁ w₂ : StdSimplex R (Fin n)} :
    w₁.prefixSum = w₂.prefixSum ↔ w₁ = w₂ :=
  prefixSum_injective.eq_iff

/-- The cumulative prefix sums of a simplex point are monotone. -/
theorem monotone_prefixSum {R : Type*} [Preorder R] [AddCommMonoid R] [IsOrderedAddMonoid R]
    [One R] {n : ℕ} (w : StdSimplex R (Fin n)) : Monotone w.prefixSum :=
  fun _ _ h ↦ TauCeti.monotone_prefixSum w.nonneg h

/-- The cumulative prefix sums strictly increase exactly when every barycentric weight is strictly
positive, that is, when the point lies in the open interior of the simplex. -/
theorem strictMono_prefixSum_iff {R : Type*} [PartialOrder R] [AddCommMonoid R]
    [IsOrderedCancelAddMonoid R] [One R] {n : ℕ} (w : StdSimplex R (Fin n)) :
    StrictMono w.prefixSum ↔ ∀ j, 0 < w.weights j := by
  rw [Fin.strictMono_iff_lt_succ]
  refine forall_congr' fun j ↦ ?_
  rw [← w.prefixSum_castSucc_add_weights j, lt_add_iff_pos_right]

/-- The cumulative prefix sums of the `j`-th vertex `single j` jump from `0` to `1` after `j`. -/
@[simp]
theorem prefixSum_single {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] {n : ℕ}
    (j : Fin n) (k : Fin (n + 1)) :
    (single j : StdSimplex R (Fin n)).prefixSum k = if j.castSucc < k then 1 else 0 := by
  rw [prefixSum_def, TauCeti.prefixSum_def]
  split_ifs with hj
  · rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · intro hnot
      exact absurd (Fin.lt_def.mp hj) (by simpa using hnot)
  · refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hij : i ≠ j := fun h ↦ hj (h ▸ Fin.lt_def.mpr (Finset.mem_filter.mp hi).2)
    simp [hij]

/-- Scalar pushforward transforms cumulative prefix sums by the same homomorphism. -/
@[simp]
theorem prefixSum_mapRange {R S : Type*} [PartialOrder R] [Semiring R] [PartialOrder S]
    [Semiring S] {n : ℕ} (f : R →+* S) (hf : ∀ r, 0 ≤ r → 0 ≤ f r) (w : StdSimplex R (Fin n))
    (k : Fin (n + 1)) : (w.mapRange f hf).prefixSum k = f (w.prefixSum k) := by
  rw [prefixSum_def, prefixSum_def, TauCeti.map_prefixSum f]
  congr 1
  funext i
  simp

/-- The cumulative prefix sum of `w.map g` at `k` equals that of `w` at `k'` whenever `g` maps
precisely the indices below `k'` to indices below `k`. -/
theorem prefixSum_map_of_lt_iff {R : Type*} [PartialOrder R] [Semiring R]
    [IsStrictOrderedRing R] {m n : ℕ} {g : Fin m → Fin n} (w : StdSimplex R (Fin m))
    (k : Fin (n + 1)) (k' : Fin (m + 1))
    (h : ∀ j : Fin m, (g j).val < k.val ↔ j.val < k'.val) :
    (w.map g).prefixSum k = w.prefixSum k' := by
  rw [prefixSum_def, prefixSum_def, TauCeti.prefixSum_def, TauCeti.prefixSum_def,
    sum_filter_weights_map]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext j
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h j

/-- Reindexing a standard simplex along `finCongr h` shifts cumulative prefix sums by
`Fin.cast`. -/
@[simp]
theorem prefixSum_map_finCongr {R : Type*} [PartialOrder R] [Semiring R]
    [IsStrictOrderedRing R] {m n : ℕ} (h : m = n) (w : StdSimplex R (Fin m))
    (k : Fin (n + 1)) :
    (w.map (finCongr h)).prefixSum k = w.prefixSum (k.cast (congrArg (· + 1) h.symm)) := by
  subst h
  simp

/-- Including the facet opposite `p` along `p.succAbove` repeats the `p`-th cumulative prefix sum
via `p.predAbove`. -/
@[simp]
theorem prefixSum_map_succAbove {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
    {n : ℕ} (p : Fin (n + 1)) (w : StdSimplex R (Fin n)) (k : Fin (n + 2)) :
    (w.map p.succAbove).prefixSum k = w.prefixSum (p.predAbove k) :=
  prefixSum_map_of_lt_iff w k (p.predAbove k) fun j ↦ by
    rcases lt_or_ge j.castSucc p with hj | hj <;> rcases le_or_gt k p.castSucc with hk | hk
    · rw [Fin.succAbove_of_castSucc_lt _ _ hj, Fin.predAbove_of_le_castSucc _ _ hk]
      simp
    · rw [Fin.succAbove_of_castSucc_lt _ _ hj, Fin.predAbove_of_castSucc_lt _ _ hk]
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_pred] at hj hk ⊢
      omega
    · rw [Fin.succAbove_of_le_castSucc _ _ hj, Fin.predAbove_of_le_castSucc _ _ hk]
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ, Fin.coe_castPred] at hj hk ⊢
      omega
    · rw [Fin.succAbove_of_le_castSucc _ _ hj, Fin.predAbove_of_castSucc_lt _ _ hk]
      simp only [Fin.le_def, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.val_pred] at hj hk ⊢
      omega

/-- Merging two adjacent vertices `p.castSucc` and `p.succ` along `p.predAbove` deletes the
internal prefix sum `p.castSucc.succ`. -/
@[simp]
theorem prefixSum_map_predAbove {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
    {n : ℕ} (p : Fin n) (w : StdSimplex R (Fin (n + 1))) (k : Fin (n + 1)) :
    (w.map p.predAbove).prefixSum k = w.prefixSum (p.castSucc.succ.succAbove k) :=
  prefixSum_map_of_lt_iff w k (p.castSucc.succ.succAbove k) fun j ↦ by
    rcases le_or_gt j p.castSucc with hj | hj <;>
      rcases lt_or_ge k.castSucc p.castSucc.succ with hk | hk
    · rw [Fin.predAbove_of_le_castSucc _ _ hj, Fin.succAbove_of_castSucc_lt _ _ hk]
      simp
    · rw [Fin.predAbove_of_le_castSucc _ _ hj, Fin.succAbove_of_le_castSucc _ _ hk]
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ, Fin.coe_castPred] at hj hk ⊢
      omega
    · rw [Fin.predAbove_of_castSucc_lt _ _ hj, Fin.succAbove_of_castSucc_lt _ _ hk]
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.val_pred] at hj hk ⊢
      omega
    · rw [Fin.predAbove_of_castSucc_lt _ _ hj, Fin.succAbove_of_le_castSucc _ _ hk]
      simp only [Fin.lt_def, Fin.le_def, Fin.val_castSucc, Fin.val_succ, Fin.val_pred] at hj hk ⊢
      omega

private theorem prefixSum_sub_eq {R : Type*} [AddCommGroup R] {n : ℕ} (t : Fin (n + 1) → R)
    (h0 : t 0 = 0) (i : ℕ) (hi : i ≤ n) :
    TauCeti.prefixSum i (fun j : Fin n ↦ t j.succ - t j.castSucc) =
      t ⟨i, Nat.lt_succ_of_le hi⟩ := by
  induction i with
  | zero => simp [h0]
  | succ i ih =>
    rw [TauCeti.prefixSum_succ (by omega), ih (by omega)]
    exact add_sub_cancel _ _

/-- The equivalence between `StdSimplex R (Fin n)` and monotone prefix-sum sequences
`0 = t₀ ≤ t₁ ≤ ⋯ ≤ t_n = 1`. -/
noncomputable def equivPrefixSum (R : Type*) [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] [One R] (n : ℕ) :
    StdSimplex R (Fin n) ≃
      {t : Fin (n + 1) → R // t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t} where
  toFun w := ⟨w.prefixSum, w.prefixSum_zero, w.prefixSum_last, w.monotone_prefixSum⟩
  invFun t :=
    { weights := Finsupp.equivFunOnFinite.symm fun j ↦ t.val j.succ - t.val j.castSucc
      nonneg j := by
        simpa using sub_nonneg.mpr (t.property.2.2 j.castSucc_lt_succ.le)
      total := by
        rw [Finsupp.sum_fintype _ _ (by simp)]
        simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
        have h := prefixSum_sub_eq t.val t.property.1 n le_rfl
        rw [TauCeti.prefixSum_of_le le_rfl] at h
        exact h.trans t.property.2.1 }
  left_inv w := by
    have hw : (Finsupp.equivFunOnFinite.symm fun j : Fin n ↦
        w.prefixSum j.succ - w.prefixSum j.castSucc) = w.weights := by
      ext j
      simp
    cases w
    dsimp only
    congr 1
  right_inv t := by
    apply Subtype.ext
    funext k
    have hcoe :
        (⇑(Finsupp.equivFunOnFinite.symm fun j : Fin n ↦ t.val j.succ - t.val j.castSucc) :
          Fin n → R) = fun j ↦ t.val j.succ - t.val j.castSucc := by
      ext j
      simp
    simpa only [prefixSum_def, hcoe] using
      prefixSum_sub_eq t.val t.property.1 k.val (Nat.le_of_lt_succ k.isLt)

/-- Applying `equivPrefixSum` recovers `prefixSum`. -/
@[simp]
theorem equivPrefixSum_apply_coe {R : Type*} [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] [One R] {n : ℕ}
    (w : StdSimplex R (Fin n)) : (equivPrefixSum R n w).val = w.prefixSum :=
  (rfl)

/-- The cumulative prefix sums of `(equivPrefixSum R n).symm t` recover `t`. -/
@[simp]
theorem prefixSum_equivPrefixSum_symm {R : Type*} [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] [One R] {n : ℕ}
    (t : {t : Fin (n + 1) → R // t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t}) :
    ((equivPrefixSum R n).symm t).prefixSum = t.val :=
  congrArg Subtype.val ((equivPrefixSum R n).apply_symm_apply t)

/-- The inverse of `equivPrefixSum` assigns successive differences of prefix sums as weights. -/
@[simp]
theorem weights_equivPrefixSum_symm_apply {R : Type*} [AddCommGroup R] [PartialOrder R]
    [IsOrderedAddMonoid R] [One R] {n : ℕ}
    (t : {t : Fin (n + 1) → R // t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t})
    (j : Fin n) :
    ((equivPrefixSum R n).symm t).weights j = t.val j.succ - t.val j.castSucc := by
  simp [equivPrefixSum]

end Convexity.StdSimplex

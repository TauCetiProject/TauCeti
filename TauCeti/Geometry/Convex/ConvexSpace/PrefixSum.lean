/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import TauCeti.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Order.Interval.Set.Infinite

/-!
# Cumulative break coordinates and scalar pushforward on standard simplices

A point `w` of the finite standard simplex `Convexity.StdSimplex R (Fin (n + 1))` has `n + 1`
nonnegative weights summing to `1`. Its cumulative prefix sums `w.breakTime : Fin (n + 2) → R`
form a monotone sequence from `0` to `1` whose successive differences recover the weights.
Conversely, every monotone sequence `0 = t₀ ≤ t₁ ≤ ⋯ ≤ t_{n+1} = 1` arises in this way
(`Convexity.StdSimplex.equivBreakTime`), with strictly increasing sequences corresponding to
the open interior where every weight is positive. Merging two adjacent vertices `p.castSucc` and
`p.succ` along `p.predAbove` deletes the internal break `t_{p+1}`.

This file also defines scalar pushforward `Convexity.StdSimplex.mapRange` along a monotone
semiring homomorphism, such as casting rational barycentric weights to a real or ordered-field
simplex, and records that positive-dimensional simplices are infinite over densely ordered rings
and uncountable over `ℝ`.

## Main definitions

* `Convexity.StdSimplex.mapRange`: push weights of a standard simplex forward along a monotone
  semiring homomorphism.
* `Convexity.StdSimplex.breakTime`: cumulative prefix sums `0 = t₀ ≤ ⋯ ≤ t_{n+1} = 1` of a point
  of `StdSimplex R (Fin (n + 1))`.
* `Convexity.StdSimplex.equivBreakTime`: the equivalence between `StdSimplex R (Fin (n + 1))` and
  monotone sequences in `[0, 1]` from `0` to `1`.

## Main results

* `Convexity.StdSimplex.strictMono_breakTime_iff`: the break times strictly increase exactly when
  every barycentric weight is strictly positive.
* `Convexity.StdSimplex.breakTime_map_predAbove`: merging adjacent vertices `p.castSucc` and
  `p.succ` removes the `(p + 1)`-st break time.
* `Convexity.StdSimplex.infinite`, `Convexity.StdSimplex.not_countable_real`: standard simplices
  on nontrivial vertex types are infinite over densely ordered rings and uncountable over `ℝ`.
-/

public section

namespace Convexity.StdSimplex

section MapRange

variable {R S X Y : Type*} [PartialOrder R] [Semiring R] [PartialOrder S] [Semiring S]

/-- Push a point of a standard simplex forward along a monotone semiring homomorphism on its
weights, such as casting rational barycentric coordinates into an ordered field. -/
noncomputable def mapRange (f : R →+* S) (hf : Monotone f) (w : StdSimplex R X) :
    StdSimplex S X where
  weights := w.weights.mapRange f (map_zero f)
  nonneg x := by
    simpa only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.mapRange_apply, ← map_zero f] using
      hf (w.nonneg x)
  total := by
    rw [Finsupp.sum_mapRange_index (by simp), ← map_finsuppSum f w.weights fun _ r ↦ r,
      w.total, map_one]

/-- Scalar pushforward applies `Finsupp.mapRange` to the weight vector. -/
theorem weights_mapRange (f : R →+* S) (hf : Monotone f) (w : StdSimplex R X) :
    (w.mapRange f hf).weights = w.weights.mapRange f (map_zero f) :=
  (rfl)

/-- Scalar pushforward applies the homomorphism to each weight. -/
@[simp]
theorem weights_mapRange_apply (f : R →+* S) (hf : Monotone f) (w : StdSimplex R X) (x : X) :
    (w.mapRange f hf).weights x = f (w.weights x) := by
  rw [weights_mapRange, Finsupp.mapRange_apply]

/-- Scalar pushforward along an injective homomorphism is injective. -/
theorem mapRange_injective {f : R →+* S} (hf : Monotone f) (hfinj : Function.Injective f) :
    Function.Injective (mapRange (X := X) f hf) := by
  intro w₁ w₂ h
  ext x
  exact hfinj (by simpa only [weights_mapRange_apply] using congrArg (fun u ↦ u.weights x) h)

/-- Scalar pushforward along an injective homomorphism preserves the support of weights. -/
@[simp]
theorem support_weights_mapRange {f : R →+* S} (hf : Monotone f) (hfinj : Function.Injective f)
    (w : StdSimplex R X) : (w.mapRange f hf).weights.support = w.weights.support := by
  ext x
  simp [Finsupp.mem_support_iff, map_eq_zero_iff f hfinj]

/-- Scalar pushforward sends each vertex point mass to the corresponding vertex point mass. -/
@[simp]
theorem mapRange_single [IsStrictOrderedRing R] [IsStrictOrderedRing S]
    (f : R →+* S) (hf : Monotone f) (x : X) :
    (single x).mapRange f hf = single x := by
  ext y
  by_cases h : x = y <;> simp [h]

/-- Scalar pushforward commutes with pushing vertices forward along a map. -/
theorem mapRange_map [IsStrictOrderedRing R] [IsStrictOrderedRing S]
    (f : R →+* S) (hf : Monotone f) (g : X → Y) (w : StdSimplex R X) :
    (w.map g).mapRange f hf = (w.mapRange f hf).map g := by
  ext y
  rw [weights_mapRange_apply, weights_map, weights_map, weights_mapRange,
    Finsupp.mapDomain, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_apply,
    map_finsuppSum, Finsupp.sum_mapRange_index (by simp)]
  refine Finsupp.sum_congr fun x _ ↦ ?_
  by_cases h : g x = y <;> simp [h]

/-- Scalar pushforward along the identity homomorphism is the identity. -/
@[simp]
theorem mapRange_id (w : StdSimplex R X) : w.mapRange (RingHom.id R) monotone_id = w := by
  ext x
  simp

end MapRange

section BreakTime

/-- The `k`-th cumulative break time `∑_{j < k} w_j` of a point `w` of the standard `n`-simplex,
for `k : Fin (n + 2)`. It runs from `0` at `k = 0` to `1` at `k = n + 1`. -/
def breakTime {R : Type*} [LE R] [AddCommMonoid R] [One R] {n : ℕ}
    (w : StdSimplex R (Fin (n + 1))) (k : Fin (n + 2)) : R :=
  TauCeti.prefixSum k.val w.weights

/-- The defining formula of `breakTime` as a prefix sum of weights. -/
theorem breakTime_def {R : Type*} [LE R] [AddCommMonoid R] [One R] {n : ℕ}
    (w : StdSimplex R (Fin (n + 1))) (k : Fin (n + 2)) :
    w.breakTime k = TauCeti.prefixSum k.val w.weights :=
  (rfl)

/-- The initial break time is `0`. -/
@[simp]
theorem breakTime_zero {R : Type*} [LE R] [AddCommMonoid R] [One R] {n : ℕ}
    (w : StdSimplex R (Fin (n + 1))) : w.breakTime 0 = 0 := by
  simp [breakTime_def]

/-- Advancing past the `j`-th vertex adds its weight to the cumulative break time. -/
theorem breakTime_castSucc_add_weights {R : Type*} [LE R] [AddCommMonoid R] [One R] {n : ℕ}
    (w : StdSimplex R (Fin (n + 1))) (j : Fin (n + 1)) :
    w.breakTime j.castSucc + w.weights j = w.breakTime j.succ :=
  (TauCeti.prefixSum_succ j.isLt w.weights).symm

/-- The final break time is `1`, the total weight of the simplex point. -/
@[simp]
theorem breakTime_last {R : Type*} [PartialOrder R] [Semiring R] {n : ℕ}
    (w : StdSimplex R (Fin (n + 1))) : w.breakTime (Fin.last (n + 1)) = 1 := by
  rw [breakTime_def, Fin.val_last, TauCeti.prefixSum_of_le le_rfl, w.total_of_fintype]

/-- Each weight is the difference of the two adjacent cumulative break times. -/
@[simp]
theorem breakTime_succ_sub_castSucc {R : Type*} [Ring R] [PartialOrder R] {n : ℕ}
    (w : StdSimplex R (Fin (n + 1))) (j : Fin (n + 1)) :
    w.breakTime j.succ - w.breakTime j.castSucc = w.weights j := by
  rw [← w.breakTime_castSucc_add_weights j, add_sub_cancel_left]

/-- The cumulative break times of a simplex point are monotone. -/
theorem monotone_breakTime {R : Type*} [PartialOrder R] [AddCommMonoid R] [IsOrderedAddMonoid R]
    [One R] {n : ℕ} (w : StdSimplex R (Fin (n + 1))) : Monotone w.breakTime :=
  fun _ _ h ↦ TauCeti.monotone_prefixSum w.nonneg h

/-- Every cumulative break time is nonnegative. -/
theorem breakTime_nonneg {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] {n : ℕ}
    (w : StdSimplex R (Fin (n + 1))) (k : Fin (n + 2)) : 0 ≤ w.breakTime k :=
  w.prefixSum_weights_nonneg k.val

/-- Every cumulative break time is at most `1`. -/
theorem breakTime_le_one {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R] {n : ℕ}
    (w : StdSimplex R (Fin (n + 1))) (k : Fin (n + 2)) : w.breakTime k ≤ 1 :=
  w.prefixSum_weights_le_one k.val

/-- The cumulative break times strictly increase exactly when every barycentric weight is strictly
positive, that is, when the point lies in the open interior of the simplex. -/
theorem strictMono_breakTime_iff {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    {n : ℕ} (w : StdSimplex R (Fin (n + 1))) :
    StrictMono w.breakTime ↔ ∀ j, 0 < w.weights j := by
  rw [Fin.strictMono_iff_lt_succ]
  refine forall_congr' fun j ↦ ?_
  rw [← sub_pos, w.breakTime_succ_sub_castSucc]

/-- Scalar pushforward transforms cumulative break times by the same homomorphism. -/
@[simp]
theorem breakTime_mapRange {R S : Type*} [PartialOrder R] [Semiring R] [PartialOrder S]
    [Semiring S] {n : ℕ} (f : R →+* S) (hf : Monotone f) (w : StdSimplex R (Fin (n + 1)))
    (k : Fin (n + 2)) : (w.mapRange f hf).breakTime k = f (w.breakTime k) := by
  rw [breakTime_def, breakTime_def, TauCeti.map_prefixSum f]
  rfl

/-- Merging two adjacent vertices `p.castSucc` and `p.succ` along `p.predAbove` deletes the
internal break time `p.castSucc.succ`. -/
@[simp]
theorem breakTime_map_predAbove {R : Type*} [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
    {n : ℕ} (p : Fin (n + 1)) (w : StdSimplex R (Fin (n + 2))) (k : Fin (n + 2)) :
    (w.map p.predAbove).breakTime k = w.breakTime (p.castSucc.succ.succAbove k) := by
  rw [breakTime_def, breakTime_def, TauCeti.prefixSum_def, TauCeti.prefixSum_def,
    sum_filter_weights_map]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.succAbove, Fin.predAbove,
    Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val, Fin.val_pred, Fin.coe_castPred,
    dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

/-- The equivalence between the standard `n`-simplex over `R` and monotone break-time sequences
`0 = t₀ ≤ t₁ ≤ ⋯ ≤ t_{n+1} = 1`. -/
noncomputable def equivBreakTime (R : Type*) [Ring R] [PartialOrder R] [IsOrderedRing R] (n : ℕ) :
    StdSimplex R (Fin (n + 1)) ≃
      {t : Fin (n + 2) → R // t 0 = 0 ∧ t (Fin.last (n + 1)) = 1 ∧ Monotone t} where
  toFun w := ⟨w.breakTime, w.breakTime_zero, w.breakTime_last, w.monotone_breakTime⟩
  invFun t :=
    { weights := Finsupp.equivFunOnFinite.symm fun j ↦ t.1 j.succ - t.1 j.castSucc
      nonneg j := by
        simpa using sub_nonneg.mpr (t.2.2.2 j.castSucc_lt_succ.le)
      total := by
        rw [Finsupp.sum_fintype _ _ (by simp)]
        simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
        rw [← Finset.Iic_top, Fin.top_eq_last, Fin.sum_Iic_sub, Fin.succ_last,
          t.2.2.1, t.2.1, sub_zero] }
  left_inv w := by
    ext j
    simp
  right_inv t := by
    apply Subtype.ext
    funext k
    have hcoe :
        (⇑(Finsupp.equivFunOnFinite.symm fun j : Fin (n + 1) ↦ t.1 j.succ - t.1 j.castSucc) :
          Fin (n + 1) → R) = fun j ↦ t.1 j.succ - t.1 j.castSucc := by
      ext j
      simp
    have hval (i : ℕ) (hi : i ≤ n + 1) :
        TauCeti.prefixSum i (fun j : Fin (n + 1) ↦ t.1 j.succ - t.1 j.castSucc) =
          t.1 ⟨i, Nat.lt_succ_of_le hi⟩ := by
      induction i with
      | zero => simp [t.2.1]
      | succ i ih =>
        rw [TauCeti.prefixSum_succ (by omega), ih (by omega)]
        exact add_sub_cancel _ _
    simpa only [breakTime_def, hcoe] using hval k.val (Nat.le_of_lt_succ k.isLt)

/-- Applying `equivBreakTime` recovers `breakTime`. -/
@[simp]
theorem equivBreakTime_apply_coe {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] {n : ℕ}
    (w : StdSimplex R (Fin (n + 1))) : (equivBreakTime R n w).1 = w.breakTime :=
  (rfl)

/-- The inverse of `equivBreakTime` assigns successive differences of break times as weights. -/
@[simp]
theorem weights_equivBreakTime_symm_apply {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    {n : ℕ} (t : {t : Fin (n + 2) → R // t 0 = 0 ∧ t (Fin.last (n + 1)) = 1 ∧ Monotone t})
    (j : Fin (n + 1)) : ((equivBreakTime R n).symm t).weights j = t.1 j.succ - t.1 j.castSucc := by
  simp [equivBreakTime]

end BreakTime

section Cardinality

private theorem exists_injective_icc_to_stdSimplex {R X : Type*} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] [Nontrivial X] :
    ∃ g : Set.Icc (0 : R) 1 → StdSimplex R X, Function.Injective g := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  have hinj : Function.Injective ![x, y] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  exact ⟨fun t ↦ (equivIcc.symm t).map ![x, y], (map_injective hinj).comp equivIcc.symm.injective⟩

/-- Over a densely ordered strict ordered ring (such as `ℚ` or `ℝ`), any standard simplex on a
type with at least two vertices is infinite: the unit interval embeds as the edge between two
distinct vertices. -/
theorem infinite {R X : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [DenselyOrdered R] [Nontrivial X] : Infinite (StdSimplex R X) := by
  obtain ⟨g, hg⟩ := exists_injective_icc_to_stdSimplex (R := R) (X := X)
  have : Infinite (Set.Icc (0 : R) 1) := Set.Icc.infinite zero_lt_one
  exact Infinite.of_injective g hg

/-- Over `ℝ`, any standard simplex on a type with at least two vertices is uncountable. -/
theorem not_countable_real {X : Type*} [Nontrivial X] : ¬ Countable (StdSimplex ℝ X) := by
  obtain ⟨g, hg⟩ := exists_injective_icc_to_stdSimplex (R := ℝ) (X := X)
  intro hcount
  have hIcc : (Set.Icc (0 : ℝ) 1).Countable :=
    Set.countable_coe_iff.mp (hg.countable)
  exact (Cardinal.Real.Icc_countable_iff.mp hIcc).not_gt zero_lt_one

end Cardinality

end Convexity.StdSimplex

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Branching.Columns
import Mathlib.Tactic.Ring

/-!
# The branching exponent of a definite theta-lift chain

The weight at the top of the definite chain has columns of height one and at the
successive starting ranks of the lifts. To branch to the corank-one space, keep the
same number of columns at each starting rank and shorten all the other columns by one.
The resulting interlacing pair has branching exponent `a - m * g`, where `a` counts the
height-one columns and `g` is the half-gap between lift weights. This exponent determines
the power of the level generator in the restriction map.

The column multiplicities and exponent are those of `New.Data.columnCount`,
`New.Data.keptColumns` and `New.Data.branchExponent_eq` in
`grh/src/New/UpperBound/Objects/Weights.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open Finset

namespace TauCeti.ThetaLift

/-- The multiplicity at height `h` in a definite chain with `m` steps, initial rank `k`
and rank increment `2 * step`. There are `a` extra height-one columns, `first` columns
at rank `k`, and `tail` columns at each of the later starting ranks. -/
def definiteColumnCount (k step m a first tail h : ℕ) : ℕ :=
  (if h = 1 then a else 0) +
    ∑ j ∈ range m, if h = k + j * (2 * step) then (if j = 0 then first else tail) else 0

/-- The column count is the sum of the contributions from the height-one columns and from
all lifts with starting rank `h`. -/
theorem definiteColumnCount_def (k step m a first tail h : ℕ) :
    definiteColumnCount k step m a first tail h = (if h = 1 then a else 0) +
      ∑ j ∈ range m, if h = k + j * (2 * step) then (if j = 0 then first else tail) else 0 :=
  (rfl)

/-- Increasing the numbers of columns at the first and subsequent ranks increases every
column multiplicity, as does increasing the extra height-one count. -/
theorem definiteColumnCount_mono {k step m a a' first first' tail tail' : ℕ}
    (ha : a ≤ a') (hfirst : first ≤ first') (htail : tail ≤ tail') (h : ℕ) :
    definiteColumnCount k step m a first tail h ≤
      definiteColumnCount k step m a' first' tail' h := by
  simp only [definiteColumnCount_def]
  refine add_le_add (by split <;> simp_all) (sum_le_sum fun j _ ↦ ?_)
  split
  · split <;> assumption
  · exact le_rfl

/-- Without extra height-one columns, the multiplicity at the final rank minus one is zero:
all starting ranks are at least two below the final rank. -/
theorem definiteColumnCount_pred_finalRank {step : ℕ} (hs : 0 < step) (k m first tail : ℕ) :
    definiteColumnCount k step (m + 1) 0 first tail (k + (m + 1) * (2 * step) - 1) = 0 := by
  have hrank : k + m * (2 * step) < k + (m + 1) * (2 * step) - 1 := by
    rw [Nat.add_mul m 1, one_mul, ← add_assoc]
    omega
  simp only [definiteColumnCount_def, ite_self, zero_add]
  refine sum_eq_zero fun j hj ↦ ite_eq_right ?_
  exact ne_of_gt (lt_of_le_of_lt (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (mem_range.mp hj))) _) hrank)

/-- Count all columns of the top weight, not their boxes. Every starting rank of a lift
lies strictly between zero and the final rank. -/
theorem sum_definiteColumnCount {k step : ℕ} (hk : 0 < k) (hs : 0 < step)
    (m a first tail : ℕ) :
    ∑ h ∈ Ioo 0 (k + (m + 1) * (2 * step)), definiteColumnCount k step (m + 1) a first tail h =
      a + first + m * tail := by
  have hrank : 1 < k + (m + 1) * (2 * step) := by rw [Nat.succ_mul]; omega
  simp_rw [definiteColumnCount_def]
  rw [sum_add_distrib, sum_ite_eq', ite_eq_left (mem_Ioo.mpr ⟨by decide, hrank⟩), sum_comm]
  have hmem (j : ℕ) (hj : j ∈ range (m + 1)) :
      k + j * (2 * step) ∈ Ioo 0 (k + (m + 1) * (2 * step)) := by
    refine mem_Ioo.mpr ⟨by omega, Nat.add_lt_add_left ?_ _⟩
    exact Nat.mul_lt_mul_of_pos_right (mem_range.mp hj) (by omega)
  simp_rw [sum_ite_eq']
  rw [sum_congr rfl (fun j hj ↦ ite_eq_left (hmem j hj)), sum_range_succ']
  simp [add_assoc, add_comm]

/-- At the top of a chain of `m + 1` theta lifts, the prescribed kept columns give an
interlacing highest weight of rank `n`, one less than the final rank. Here `step` is half
of the rank increment, `g` is the half-gap, and `κ₁` is the first lift weight. -/
theorem interlaces_definiteColumnCount {k step g κ₁ : ℕ}
    (h₁ : g - step ≤ κ₁ - (k / 2 + step)) (m a : ℕ) (e : ℤ) :
    let n := k + (m + 1) * (2 * step) - 1
    let c := definiteColumnCount k step (m + 1) a (κ₁ - (k / 2 + step)) (2 * (g - step))
    let kept := definiteColumnCount k step (m + 1) 0 (g - step) (g - step)
    Interlaces (fun i : Fin (n + 1) ↦ columnHighestWeight (n + 1) c e i)
      (fun i : Fin n ↦ columnHighestWeight n (branchColumnCount c kept) e i) := by
  intro n c kept
  rcases Nat.eq_zero_or_pos n with hn | hn
  · refine interlaces_iff.mpr fun i ↦ False.elim ?_
    have hi := i.isLt
    omega
  have hkept : kept n = 0 := by
    rcases Nat.eq_zero_or_pos step with rfl | hs
    · have hnk : n ≠ k := by simp [n] at hn ⊢; omega
      simp [kept, definiteColumnCount_def, hnk]
    · exact definiteColumnCount_pred_finalRank hs k m _ _
  exact interlaces_columnHighestWeight_branchColumnCount
    (fun h _ ↦ definiteColumnCount_mono (Nat.zero_le _) h₁ (by omega) h) hkept e

/-- The difference of the two highest-weight sums at the top of a definite chain is
`a - (m + 1) * g`. Use the determinant shift from the last lift in both weights. -/
theorem branchExponent_eq {k step g κ₁ : ℕ} (hk : 0 < k) (hs : 0 < step)
    (hg : step ≤ g) (hκ : k / 2 + g ≤ κ₁) (m a : ℕ) :
    let n := k + (m + 1) * (2 * step) - 1
    let c := definiteColumnCount k step (m + 1) a (κ₁ - (k / 2 + step)) (2 * (g - step))
    let kept := definiteColumnCount k step (m + 1) 0 (g - step) (g - step)
    let e : ℤ := (k / 2 : ℕ) + (m : ℤ) * step - ((κ₁ : ℤ) + m * (2 * (g : ℤ)))
    (∑ i : Fin (n + 1), columnHighestWeight (n + 1) c e i) -
      (∑ i : Fin n, columnHighestWeight n (branchColumnCount c kept) e i) =
        (a : ℤ) - (m + 1 : ℤ) * g := by
  intro n c kept e
  have hle (h : ℕ) : kept h ≤ c h :=
    definiteColumnCount_mono (Nat.zero_le a) (by omega) (by omega) h
  have hn : kept n = 0 := definiteColumnCount_pred_finalRank hs k m _ _
  have hn' : n + 1 = k + (m + 1) * (2 * step) := by
    dsimp only [n]
    rw [Nat.add_mul m 1, one_mul]
    omega
  rw [sum_columnHighestWeight_sub_sum_branchColumnCount (fun h _ ↦ hle h) hn, hn']
  simp only [Nat.cast_sub (hle _), sum_sub_distrib, ← Nat.cast_sum]
  dsimp only [c, kept, e]
  rw [sum_definiteColumnCount hk hs, sum_definiteColumnCount hk hs]
  have hκ' : k / 2 + step ≤ κ₁ := by omega
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, zero_add,
    Nat.cast_sub hg, Nat.cast_sub hκ']
  push_cast
  ring

end TauCeti.ThetaLift

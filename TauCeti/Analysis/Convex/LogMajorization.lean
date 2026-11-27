/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.Analysis.Convex.Majorization

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import TauCeti.Order.Fin.Basic

/-!
# Weak log-majorization

For antitone nonnegative real tuples `x y : Fin n → ℝ`, `x` is *weakly log-majorized* by `y`
when every product of the first `k` coordinates of `x` is at most the corresponding product for
`y`. This is the multiplicative counterpart of weak majorization `TauCeti.IsWeaklyMajorizedBy`,
and the form in which products of eigenvalue moduli and of singular values are compared (Weyl's
majorant theorem, Horn's product inequality).

On positive tuples, weak log-majorization is weak majorization of the logarithms, which may be
negative. The transfer to sums of `φ`-values for `φ` monotone on `[0, ∞)` with `φ ∘ exp` convex
therefore goes through `TauCeti.prefixSum_comp_le_of_prefixSum_le`, the monotone convex transfer
for real tuples of any sign. Zero coordinates are allowed: the positive coordinates of `x` are
its first `m` coordinates, those of `y` are positive too, and from `m` on `φ (x i) = φ 0` is at
most `φ (y i)`; no continuity of `φ` at `0` is needed.

## Main definitions

* `TauCeti.IsWeaklyLogMajorizedBy x y`: weak log-majorization of antitone nonnegative tuples.

## Main results

* `TauCeti.IsWeaklyLogMajorizedBy.prefixSum_comp_le`: if `x` is weakly log-majorized by `y`,
  the prefix sums of `φ ∘ x` are bounded by those of `φ ∘ y` for `φ` monotone on `[0, ∞)`
  with `φ ∘ exp` convex.
* `TauCeti.IsWeaklyLogMajorizedBy.isWeaklyMajorizedBy`: weak log-majorization implies weak
  majorization.
* `TauCeti.IsWeaklyLogMajorizedBy.mul`: weak log-majorization is preserved by coordinatewise
  products.
* `TauCeti.IsWeaklyLogMajorizedBy.pos_right`, `TauCeti.IsWeaklyLogMajorizedBy.prefixSum_log_le`:
  where `x` is positive, so is `y`, and on such an initial segment the logarithms of `x` are
  weakly majorized by those of `y`.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer (1997), (II.3.5)
  and (III.14)–(III.16).
* R. A. Horn, C. R. Johnson, *Topics in Matrix Analysis*, Cambridge University Press (1991),
  Corollary 3.3.10.
* A. W. Marshall, I. Olkin, B. C. Arnold, *Inequalities: Theory of Majorization and Its
  Applications*, 2nd ed., Springer (2011), Definition 1.A.7 and 5.A.2.
-/

public section

open Finset Function

namespace TauCeti

variable {n : ℕ}

/-- **Weak log-majorization** of antitone nonnegative tuples: every product of the first `k`
coordinates of `x` is at most the corresponding product for `y`. The multiplicative counterpart
of `TauCeti.IsWeaklyMajorizedBy`, with the same sortedness and sign fields. -/
structure IsWeaklyLogMajorizedBy (x y : Fin n → ℝ) : Prop where
  /-- The left tuple is antitone. -/
  antitone_left : Antitone x
  /-- The right tuple is antitone. -/
  antitone_right : Antitone y
  /-- The left tuple is nonnegative. -/
  nonneg_left : 0 ≤ x
  /-- The right tuple is nonnegative. -/
  nonneg_right : 0 ≤ y
  /-- Every prefix product of `x` is at most the corresponding prefix product of `y`. -/
  prod_le : ∀ k : ℕ, ∏ i : Fin n with i.val < k, x i ≤ ∏ i : Fin n with i.val < k, y i

namespace IsWeaklyLogMajorizedBy

variable {x y z u v : Fin n → ℝ}

/-- Every antitone nonnegative tuple weakly log-majorizes itself. -/
theorem refl (hx : Antitone x) (hx0 : 0 ≤ x) : IsWeaklyLogMajorizedBy x x :=
  ⟨hx, hx, hx0, hx0, fun _ ↦ le_rfl⟩

/-- Weak log-majorization is transitive. -/
@[trans]
theorem trans (hxy : IsWeaklyLogMajorizedBy x y) (hyz : IsWeaklyLogMajorizedBy y z) :
    IsWeaklyLogMajorizedBy x z :=
  ⟨hxy.antitone_left, hyz.antitone_right, hxy.nonneg_left, hyz.nonneg_right,
    fun k ↦ (hxy.prod_le k).trans (hyz.prod_le k)⟩

/-- Weak log-majorization is preserved by coordinatewise products of two weakly log-majorized
pairs. -/
theorem mul (h₁ : IsWeaklyLogMajorizedBy x y) (h₂ : IsWeaklyLogMajorizedBy u v) :
    IsWeaklyLogMajorizedBy (x * u) (y * v) :=
  ⟨fun i j hij ↦ mul_le_mul (h₁.antitone_left hij) (h₂.antitone_left hij) (h₂.nonneg_left j)
      (h₁.nonneg_left i),
    fun i j hij ↦ mul_le_mul (h₁.antitone_right hij) (h₂.antitone_right hij)
      (h₂.nonneg_right j) (h₁.nonneg_right i),
    fun i ↦ mul_nonneg (h₁.nonneg_left i) (h₂.nonneg_left i),
    fun i ↦ mul_nonneg (h₁.nonneg_right i) (h₂.nonneg_right i),
    fun k ↦ by
      simpa only [Pi.mul_apply, prod_mul_distrib] using mul_le_mul (h₁.prod_le k) (h₂.prod_le k)
        (prod_nonneg fun i _ ↦ h₂.nonneg_left i) (prod_nonneg fun i _ ↦ h₁.nonneg_right i)⟩

/-- If `x` is weakly log-majorized by `y`, then `y` is positive wherever `x` is. -/
theorem pos_right (h : IsWeaklyLogMajorizedBy x y) {i : Fin n} (hi : 0 < x i) : 0 < y i := by
  -- The prefix product of `x` up to `i` is positive, hence so is that of `y`.
  have hprod : 0 < ∏ j : Fin n with j.val < i.val + 1, x j :=
    prod_pos fun j hj ↦
      hi.trans_le (h.antitone_left (Fin.le_def.2 (by simpa [Nat.lt_succ_iff] using hj)))
  exact (h.nonneg_right i).lt_of_ne'
    (prod_ne_zero_iff.1 (hprod.trans_le (h.prod_le _)).ne' i (by simp))

/-- If the first `k` coordinates of `x` are positive, then the prefix sum of length `k` of the
logarithms of `x` is at most that of the logarithms of `y`. -/
theorem prefixSum_log_le (h : IsWeaklyLogMajorizedBy x y) {k : ℕ}
    (hk : ∀ i : Fin n, (i : ℕ) < k → 0 < x i) :
    prefixSum k (Real.log ∘ x) ≤ prefixSum k (Real.log ∘ y) := by
  have hpos : ∀ i ∈ ({i | (i : ℕ) < k} : Finset (Fin n)), 0 < x i :=
    fun i hi ↦ hk i (mem_filter.1 hi).2
  rw [prefixSum_def, prefixSum_def, comp_def, comp_def,
    ← Real.log_prod fun i hi ↦ (hpos i hi).ne',
    ← Real.log_prod fun i hi ↦ (h.pos_right (hpos i hi)).ne']
  exact Real.log_le_log (prod_pos hpos) (h.prod_le k)

/-- **Transfer to `φ`-sums.** If `x` is weakly log-majorized by `y`, then every prefix sum of
`φ ∘ x` is at most the corresponding prefix sum of `φ ∘ y`, provided `φ` is monotone on
`[0, ∞)` and `φ ∘ exp` is convex. Zero coordinates are allowed. -/
theorem prefixSum_comp_le (h : IsWeaklyLogMajorizedBy x y) {φ : ℝ → ℝ}
    (hφ : MonotoneOn φ (Set.Ici 0)) (hφe : ConvexOn ℝ Set.univ (φ ∘ Real.exp)) (k : ℕ) :
    prefixSum k (φ ∘ x) ≤ prefixSum k (φ ∘ y) := by
  -- The positive entries of the antitone tuple `x` are its first `m` entries.
  obtain ⟨m, hm⟩ := (Fin.isLowerSet_iff_exists_eq_setOf_val_lt (s := {i | 0 < x i})).1
    fun i j hji (hi : 0 < x i) ↦ (hi.trans_le (h.antitone_left hji) : 0 < x j)
  replace hm (i : Fin n) : 0 < x i ↔ (i : ℕ) < m := Set.ext_iff.1 hm i
  -- Take logarithms of the first `m` entries, and replace the others by a common value `L`
  -- below all of them, so that the transfer for weak majorization applies.
  set L := -∑ i, |Real.log (x i)|
  set a : Fin n → ℝ := fun i ↦ if (i : ℕ) < m then Real.log (x i) else L
  set b : Fin n → ℝ := fun i ↦ if (i : ℕ) < m then Real.log (y i) else L
  have ha : Antitone a := by
    intro i j hij
    simp only [a]
    split_ifs with hj hi hi
    · exact Real.log_le_log ((hm j).2 hj) (h.antitone_left hij)
    · exact absurd ((Fin.le_def.1 hij).trans_lt hj) hi
    · exact (neg_le_neg (single_le_sum (fun j _ ↦ abs_nonneg (Real.log (x j)))
        (mem_univ i))).trans (neg_abs_le _)
    · exact le_rfl
  have hab : ∀ j, prefixSum j a ≤ prefixSum j b := by
    intro j
    -- The two tuples differ only in the first `min j m` coordinates.
    have hlog := h.prefixSum_log_le (k := min j m) fun i hi ↦ (hm i).2 (lt_min_iff.1 hi).2
    rw [← sub_nonpos, ← prefixSum_sub] at hlog ⊢
    refine le_of_eq_of_le ?_ hlog
    rw [prefixSum_def, prefixSum_def, sum_filter, sum_filter]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [Pi.sub_apply, comp_apply, a, b, lt_min_iff]
    split_ifs <;> simp_all
  have hψ : Monotone (φ ∘ Real.exp) := fun s t hst ↦
    hφ (Real.exp_pos s).le (Real.exp_pos t).le (Real.exp_le_exp.2 hst)
  -- Put back the entries from `m` on, where `x` vanishes and `φ (y i) ≥ φ 0`.
  set c : Fin n → ℝ := fun i ↦ if (i : ℕ) < m then 0 else φ 0 - φ (Real.exp L)
  have hx : φ ∘ x = (φ ∘ Real.exp) ∘ a + c := funext fun i ↦ by
    simp only [comp_apply, Pi.add_apply, a, c]
    split_ifs with hi
    · rw [Real.exp_log ((hm i).2 hi), add_zero]
    · rw [le_antisymm (not_lt.1 (mt (hm i).1 hi)) (h.nonneg_left i)]
      ring
  have hy : (φ ∘ Real.exp) ∘ b + c ≤ φ ∘ y := fun i ↦ by
    simp only [comp_apply, Pi.add_apply, b, c]
    split_ifs with hi
    · rw [Real.exp_log (h.pos_right ((hm i).2 hi)), add_zero]
    · linarith [hφ Set.self_mem_Ici (h.nonneg_right i) (h.nonneg_right i)]
  calc prefixSum k (φ ∘ x) = prefixSum k ((φ ∘ Real.exp) ∘ a) + prefixSum k c := by
        rw [hx, prefixSum_add]
    _ ≤ prefixSum k ((φ ∘ Real.exp) ∘ b) + prefixSum k c :=
        add_le_add_left (prefixSum_comp_le_of_prefixSum_le ha hab hψ hφe k) _
    _ = prefixSum k ((φ ∘ Real.exp) ∘ b + c) := (prefixSum_add k _ _).symm
    _ ≤ prefixSum k (φ ∘ y) := prefixSum_mono k hy

/-- Weak log-majorization implies weak majorization. -/
theorem isWeaklyMajorizedBy (h : IsWeaklyLogMajorizedBy x y) : IsWeaklyMajorizedBy x y :=
  ⟨h.antitone_left, h.antitone_right, h.nonneg_left, h.nonneg_right, fun k ↦ by
    simpa using h.prefixSum_comp_le monotoneOn_id (by simpa using convexOn_exp) k⟩

end IsWeaklyLogMajorizedBy

end TauCeti

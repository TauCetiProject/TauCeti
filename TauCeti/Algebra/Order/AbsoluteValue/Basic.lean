/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Lattice

/-!
# Sums under a weakened triangle inequality

An absolute value satisfies `v (a + b) ≤ c * max (v a) (v b)` with `c = 2`, and with `c = 1` when
it is nonarchimedean. Iterating this inequality bounds a sum of `n` terms of size at most `T` by
`c ^ n * T` (`AbsoluteValue.apply_sum_le_pow_mul`). Unlike the triangle inequality, which gives
`n * T`, the bound specializes to `T` itself in the nonarchimedean case.

The same inequality bounds one step of elimination with partial pivoting: subtracting from `a` the
multiple `p / q * b` of a pivot column, whose pivot `q` dominates `b` relative to the row weights,
costs only the factor `c` (`AbsoluteValue.apply_sub_div_mul_le`), and a maximizing pivot exists
(`AbsoluteValue.exists_pos_forall_apply_div_le`).
-/

public section

open Finset

namespace AbsoluteValue

/-- The triangle inequality gives `v (n * x) ≤ n * v x` for a natural number `n`, without using
`v 1 = 1` (so for an absolute value valued in any ordered semiring). -/
theorem apply_natCast_mul_le {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S]
    [IsOrderedRing S] (v : AbsoluteValue R S) (n : ℕ) (x : R) : v ((n : R) * x) ≤ n * v x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Nat.cast_succ, add_mul, one_mul]
    exact (v.add_le _ _).trans (add_le_add_left ih _)

variable {R S : Type*} [Semiring R] [Semiring S] [LinearOrder S] [IsOrderedRing S]

/-- A sum of `card s` terms of size at most `T` has size at most `c ^ card s * T`, for an
absolute value satisfying `v (a + b) ≤ c * max (v a) (v b)` with `1 ≤ c`. -/
theorem apply_sum_le_pow_mul {v : AbsoluteValue R S} {c : S} (hc : 1 ≤ c)
    (hv : ∀ a b, v (a + b) ≤ c * max (v a) (v b)) {ι : Type*} (s : Finset ι) (f : ι → R)
    {T : S} (hT : 0 ≤ T) (hf : ∀ i ∈ s, v (f i) ≤ T) : v (∑ i ∈ s, f i) ≤ c ^ s.card * T := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hT
  | insert a s ha ih =>
    rw [sum_insert ha, card_insert_of_notMem ha, pow_succ', mul_assoc]
    have hs := ih fun i hi ↦ hf i (mem_insert_of_mem hi)
    have hTs : T ≤ c ^ s.card * T := le_mul_of_one_le_left hT (one_le_pow₀ hc)
    calc v (f a + ∑ i ∈ s, f i) ≤ c * max (v (f a)) (v (∑ i ∈ s, f i)) := hv _ _
      _ ≤ c * (c ^ s.card * T) := by
        have : 0 ≤ c := zero_le_one.trans hc
        gcongr
        exact max_le ((hf a (mem_insert_self a s)).trans hTs) hs

/-- One elimination step: if the pivot `q` maximizes `v (·) / s` in its column, then subtracting
`p / q` times that column from a column bounded by `M` (in units of the row weights `s`, `t`)
keeps it bounded by `c * M`, for an absolute value satisfying `v (a + b) ≤ c * max (v a) (v b)`. -/
theorem apply_sub_div_mul_le {K F : Type*} [DivisionRing K] [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {v : AbsoluteValue K F} {c : F} (hc : 0 ≤ c)
    (hv : ∀ a b, v (a + b) ≤ c * max (v a) (v b)) {a b p q : K} {s t M : F} (hs : 0 < s)
    (ht : 0 < t) (hq : 0 < v q) (ha : v a ≤ s * M) (hp : v p ≤ t * M)
    (hb : v b / s ≤ v q / t) : v (a - p / q * b) ≤ c * (s * M) := by
  have hM : 0 ≤ M := (mul_nonneg_iff_of_pos_left ht).mp ((v.nonneg _).trans hp)
  have hratio : v b / v q ≤ s / t := by
    rw [div_le_div_iff₀ hs ht] at hb
    rw [div_le_div_iff₀ hq ht]
    linarith
  have hsub : v (p / q * b) ≤ s * M := by
    rw [map_mul, map_div₀, div_mul_eq_mul_div, mul_div_assoc]
    calc v p * (v b / v q) ≤ (t * M) * (s / t) :=
          mul_le_mul hp hratio (div_nonneg (v.nonneg _) hq.le) (mul_nonneg ht.le hM)
      _ = s * M := by field_simp [ht.ne']
  calc v (a - p / q * b) ≤ c * max (v a) (v (-(p / q * b))) := by
        rw [sub_eq_add_neg]
        exact hv _ _
    _ ≤ c * (s * M) := by
        rw [map_neg_eq_map]
        exact mul_le_mul_of_nonneg_left (max_le ha hsub) hc

/-- **The growth factor of one addition**: `v (a + b) ≤ 2 * max (v a) (v b)`. At a nonarchimedean
absolute value the factor `2` can be replaced by `1` (`IsNonarchimedean`). -/
theorem apply_add_le_two_mul_max (v : AbsoluteValue R S) (a b : R) :
    v (a + b) ≤ 2 * max (v a) (v b) := by
  rw [two_mul]
  exact (v.add_le a b).trans (add_le_add (le_max_left _ _) (le_max_right _ _))

/-- **Partial pivoting at one place**: a nonzero family of elements of a semiring has an index `r₀`
maximizing `v (f r) / ν r` for positive weights `ν`, and the value there is positive. -/
theorem exists_pos_forall_apply_div_le {ρ T : Type*} [Finite ρ]
    [Semifield T] [LinearOrder T] [IsStrictOrderedRing T] (v : AbsoluteValue R T)
    {f : ρ → R} (hf : ∃ r, f r ≠ 0) {ν : ρ → T} (hν : ∀ r, 0 < ν r) :
    ∃ r₀, 0 < v (f r₀) ∧ ∀ r, v (f r) / ν r ≤ v (f r₀) / ν r₀ := by
  obtain ⟨r₁, hr₁⟩ := hf
  have : Nonempty ρ := ⟨r₁⟩
  obtain ⟨r₀, hr₀⟩ := Finite.exists_max fun r ↦ v (f r) / ν r
  exact ⟨r₀, (div_pos_iff_of_pos_right (hν r₀)).mp
    ((div_pos (v.pos hr₁) (hν r₁)).trans_le (hr₀ r₁)), hr₀⟩

end AbsoluteValue

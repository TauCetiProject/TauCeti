/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.RootOperator

/-!
# Root operators and concatenation

The actual root operators on piecewise-linear paths satisfy the tensor product rule.
Writing `φ(p) = f p.endpoint - p.minHeight f` and `ε(q) = -q.minHeight f`, lowering
acts on the left factor when `ε(q) + 1 ≤ φ(p)`, and on the right when `φ(p) ≤ ε(q)`.
Raising has the opposite tie convention: it acts on the left when `ε(q) ≤ φ(p)`,
and on the right when `φ(p) + 1 ≤ ε(q)`.

These ambient formulas require no integrality assumptions. For the exhaustive conditional
formulas `lower_mul` and `raise_mul`, only the comparison gap `φ(p) - ε(q)` must be integral;
separate integrality of the string lengths is unnecessary. A fractional gap strictly between
zero and one can make lowering change both factors, so the two ambient cases are not exhaustive.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §2 (concatenation and the tensor product rule).
-/

public section

namespace TauCeti.PLPath

open Module

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] {f : Dual 𝕜 V} {x : V} {p q : PLPath 𝕜 V}

/-- Lowering a concatenation acts on its first factor when its lowering height exceeds
the second factor's raising height by at least one. -/
theorem lower_mul_of_add_one_le
    (h : -q.minHeight f + 1 ≤ f p.endpoint - p.minHeight f) :
    lower f x (p * q) = (lower f x p).map (· * q) := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  obtain ⟨m, rfl⟩ := ofSegments_surjective q
  simp only [minHeight_ofSegments, endpoint_ofSegments] at h
  have hm := listMinHeight_nonpos (f := f) m
  have he := listMinHeight_le_apply_sum (f := f) m
  have hmin : listMinHeight f (l ++ m) = listMinHeight f l := by
    rw [listMinHeight_append, min_eq_left (by linarith)]
  have hl : 1 ≤ f l.sum - listMinHeight f l := by linarith
  have hlm : 1 ≤ f (l ++ m).sum - listMinHeight f (l ++ m) := by
    simp only [List.sum_append, map_add, hmin]
    linarith
  have hcap : listMinHeight f l + 1 - f l.sum ≤ listMinHeight f m := by linarith
  rw [← ofSegments_append, lower_ofSegments, lower_ofSegments, listLower_def,
    listLower_def, ite_eq_left hlm, ite_eq_left hl, hmin, reflectRecords_append,
    min_eq_left (by linarith), reflectRecords_of_le_listMinHeight hcap]
  simp only [Option.map_some, ofSegments_append]

/-- Lowering a concatenation acts on its second factor when the first factor's lowering
height is at most the second factor's raising height, including equality. -/
theorem lower_mul_of_le (h : f p.endpoint - p.minHeight f ≤ -q.minHeight f) :
    lower f x (p * q) = (lower f x q).map (p * ·) := by
  obtain ⟨l, rfl⟩ := ofSegments_surjective p
  obtain ⟨m, rfl⟩ := ofSegments_surjective q
  simp only [minHeight_ofSegments, endpoint_ofSegments] at h
  have hmin : listMinHeight f (l ++ m) = f l.sum + listMinHeight f m := by
    rw [listMinHeight_append, min_eq_right (by linarith)]
  have hguard : 1 ≤ f (l ++ m).sum - listMinHeight f (l ++ m) ↔
      1 ≤ f m.sum - listMinHeight f m := by
    simp only [List.sum_append, map_add, hmin]
    constructor <;> intro hh <;> linarith
  rw [← ofSegments_append, lower_ofSegments, lower_ofSegments, listLower_def,
    listLower_def]
  simp only [hguard]
  split_ifs
  · rw [hmin, reflectRecords_append,
      min_eq_right (by linarith), reflectRecords_of_le_listMinHeight (by linarith)]
    have hcap : f l.sum + listMinHeight f m + 1 - f l.sum = listMinHeight f m + 1 := by
      ring
    rw [hcap]
    simp only [Option.map_some, ofSegments_append]
  · rfl

/-- Raising a concatenation acts on its first factor when the second factor's raising
height is at most the first factor's lowering height, including equality. -/
theorem raise_mul_of_le (h : -q.minHeight f ≤ f p.endpoint - p.minHeight f) :
    raise f x (p * q) = (raise f x p).map (· * q) := by
  have hr : f q.reverse.endpoint - q.reverse.minHeight f ≤ -p.reverse.minHeight f := by
    simp only [endpoint_reverse, map_neg, minHeight_reverse]
    linarith
  rw [raise_def, reverse_mul, lower_mul_of_le hr, Option.map_map, raise_def,
    Option.map_map]
  congr 1
  funext r
  simp only [Function.comp_apply, reverse_mul, reverse_reverse]

/-- Raising a concatenation acts on its second factor when its raising height exceeds
the first factor's lowering height by at least one. -/
theorem raise_mul_of_add_one_le
    (h : f p.endpoint - p.minHeight f + 1 ≤ -q.minHeight f) :
    raise f x (p * q) = (raise f x q).map (p * ·) := by
  have hr : -p.reverse.minHeight f + 1 ≤
      f q.reverse.endpoint - q.reverse.minHeight f := by
    simp only [endpoint_reverse, map_neg, minHeight_reverse]
    linarith
  rw [raise_def, reverse_mul, lower_mul_of_add_one_le hr, Option.map_map, raise_def,
    Option.map_map]
  congr 1
  funext r
  simp only [Function.comp_apply, reverse_mul, reverse_reverse]

/-- The tensor product rule for lowering, with equality assigned to the second factor.
Only integrality of the comparison gap is needed. -/
theorem lower_mul (h : ∃ n : ℤ,
    f p.endpoint - p.minHeight f + q.minHeight f = (n : 𝕜)) :
    lower f x (p * q) =
      if -q.minHeight f < f p.endpoint - p.minHeight f then
        (lower f x p).map (· * q) else (lower f x q).map (p * ·) := by
  split_ifs with hh
  · obtain ⟨n, hn⟩ := h
    have hnpos : (0 : 𝕜) < (n : 𝕜) := by linarith
    have hnint : (1 : ℤ) ≤ n := by
      have : (0 : ℤ) < n := by exact_mod_cast hnpos
      omega
    have : (1 : 𝕜) ≤ (n : 𝕜) := by exact_mod_cast hnint
    exact lower_mul_of_add_one_le (by linarith)
  · exact lower_mul_of_le (not_lt.mp hh)

/-- The tensor product rule for raising, with equality assigned to the first factor.
Only integrality of the comparison gap is needed. -/
theorem raise_mul (h : ∃ n : ℤ,
    f p.endpoint - p.minHeight f + q.minHeight f = (n : 𝕜)) :
    raise f x (p * q) =
      if -q.minHeight f ≤ f p.endpoint - p.minHeight f then
        (raise f x p).map (· * q) else (raise f x q).map (p * ·) := by
  split_ifs with hh
  · exact raise_mul_of_le hh
  · obtain ⟨n, hn⟩ := h
    have hnneg : (n : 𝕜) < 0 := by linarith
    have hnint : n ≤ (-1 : ℤ) := by
      have : n < (0 : ℤ) := by exact_mod_cast hnneg
      omega
    have : (n : 𝕜) ≤ -1 := by exact_mod_cast hnint
    exact raise_mul_of_add_one_le (by linarith)

end TauCeti.PLPath

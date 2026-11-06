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

Lowering also has a simple form on a path that rises monotonically from a minimum to one more than
the minimum and stays there or higher afterwards: it reflects that rising piece and keeps the rest
(`TauCeti.PLPath.lower_ofSegments_append_append`). When the height rises strictly from a minimum
at the vertex `k₀` and first reaches the minimum plus one inside the segment `k₁ - 1`, never to
return below it, the rising piece ends inside that segment, which is cut there
(`TauCeti.PLPath.lower_ofSegments_eq_of_strictly_rising`). This is the shape of the height of a
Lakshmibai–Seshadri path at a lowering step.

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

/-- **Lowering a path that rises from a minimum to the next level.** Suppose the path presented by
`l₁ ++ l₂ ++ l₃` attains its minimal height at the end of `l₁`, rises monotonically along `l₂` by
exactly one, and stays at least that high along `l₃`. Then lowering reflects `l₂` and keeps `l₁`
and `l₃`. -/
theorem lower_ofSegments_append_append {l₁ l₂ l₃ : List V}
    (h₁ : f l₁.sum ≤ listMinHeight f l₁) (h₂ : ∀ v ∈ l₂, 0 ≤ f v) (h₂₁ : f l₂.sum = 1)
    (h₃ : 0 ≤ listMinHeight f l₃) :
    lower f x (ofSegments 𝕜 (l₁ ++ l₂ ++ l₃)) =
      some (ofSegments 𝕜 (l₁ ++ l₂.map (preReflection x f) ++ l₃)) := by
  have hmin₂₃ : listMinHeight f (l₂ ++ l₃) = 0 := by
    rw [listMinHeight_append, listMinHeight_eq_zero_of_forall_nonneg h₂, h₂₁]
    exact min_eq_left (by linarith)
  have hmin : listMinHeight f (l₁ ++ (l₂ ++ l₃)) = f l₁.sum := by
    rw [listMinHeight_append, hmin₂₃, add_zero, min_eq_right h₁]
  have hguard : 1 ≤ f (l₁ ++ (l₂ ++ l₃)).sum - listMinHeight f (l₁ ++ (l₂ ++ l₃)) := by
    have := listMinHeight_le_apply_sum (f := f) l₃
    simp only [hmin, List.sum_append, map_add, h₂₁]
    linarith
  rw [List.append_assoc, lower_ofSegments, listLower_def, ite_eq_left hguard, hmin,
    reflectRecords_append, reflectRecords_append, Option.map_some]
  -- The three pieces under the caps that capped reflection induces on them.
  have hr₁ : reflectRecords f x (min (f l₁.sum + 1) (f l₁.sum + listMinHeight f (l₂ ++ l₃))) l₁ =
      l₁ :=
    reflectRecords_of_le_listMinHeight (by rw [hmin₂₃, add_zero]; exact (min_le_right _ _).trans h₁)
  have hr₂ : ofSegments 𝕜
      (reflectRecords f x (min (f l₁.sum + 1 - f l₁.sum) (f l₂.sum + listMinHeight f l₃)) l₂) =
      ofSegments 𝕜 (l₂.map (preReflection x f)) := by
    have hcap : min (f l₁.sum + 1 - f l₁.sum) (f l₂.sum + listMinHeight f l₃) = f l₂.sum := by
      rw [add_sub_cancel_left, h₂₁]
      exact min_eq_left (by linarith)
    rw [hcap, ofSegments_reflectRecords_of_forall_nonneg h₂]
  have hr₃ : reflectRecords f x (f l₁.sum + 1 - f l₁.sum - f l₂.sum) l₃ = l₃ :=
    reflectRecords_of_le_listMinHeight (by rw [h₂₁]; linarith)
  rw [hr₁, hr₃]
  simp only [ofSegments_append, hr₂, mul_assoc]

/-- Cutting a segment `v` of a path at the fraction `θ ∈ [0, 1]`, in the middle of the segments
`a ++ m ++ v :: r`, does not change the path presented by the segments. -/
theorem ofSegments_append_cut_eq {a m r : List V} {v : V} {θ : 𝕜} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    ofSegments 𝕜 (a ++ (m ++ [θ • v]) ++ ((1 - θ) • v :: r)) =
      ofSegments 𝕜 (a ++ m ++ v :: r) := by
  have hr : a ++ (m ++ [θ • v]) ++ ((1 - θ) • v :: r) =
      (a ++ m) ++ (θ • v :: (1 - θ) • v :: r) := by
    simp only [List.append_assoc, List.singleton_append]
  rw [hr, ofSegments_append (a ++ m), ofSegments_append (a ++ m),
    ofSegments_smul_cons_smul_cons hθ₀ (sub_nonneg.mpr hθ₁), add_sub_cancel, one_smul]

/-- **Lowering a path whose height rises strictly from a minimum.** Let `h` be the minimal height of
the path presented by `l`, attained at the vertex `k₀`. Suppose the height rises strictly from the
vertex `k₀` to the vertex `k₁`, is at most `h + 1` at the vertex `k₁ - 1`, and is at least
`h + 1` at every vertex from `k₁` on. If `θ` is the fraction of the segment `v = l[k₁ - 1]` at which
the height reaches `h + 1`, then lowering reflects the piece of the path between the vertex `k₀`
and that point, and keeps the rest. -/
theorem lower_ofSegments_eq_of_strictly_rising {l : List V} {k₀ k₁ : ℕ} {θ : 𝕜}
    (hk₀₁ : k₀ < k₁) (hk₁ : k₁ ≤ l.length) (h₀ : f (l.take k₀).sum = listMinHeight f l)
    (hrise : ∀ j, k₀ ≤ j → j < k₁ → f (l.take j).sum < f (l.take (j + 1)).sum)
    (hθ : f (l.take (k₁ - 1)).sum + θ * f l[k₁ - 1] = listMinHeight f l + 1)
    (hcut : f (l.take (k₁ - 1)).sum ≤ listMinHeight f l + 1)
    (habove : ∀ j, k₁ ≤ j → listMinHeight f l + 1 ≤ f (l.take j).sum) :
    lower f x (ofSegments 𝕜 l) = some (ofSegments 𝕜 (l.take k₀ ++
      ((l.take (k₁ - 1)).drop k₀ ++ [θ • l[k₁ - 1]]).map (preReflection x f) ++
        (1 - θ) • l[k₁ - 1] :: l.drop k₁)) := by
  set v := l[k₁ - 1]
  set m := (l.take (k₁ - 1)).drop k₀
  -- The vertex heights along the cut segment `v`.
  have hstep : ∀ j (hj : j < l.length), f (l.take (j + 1)).sum = f (l.take j).sum + f l[j] := by
    intro j hj
    rw [List.sum_take_succ _ _ hj, map_add]
  have hv : f (l.take (k₁ - 1)).sum + f v = f (l.take k₁).sum := by
    rw [← hstep _ (by omega), Nat.sub_add_cancel (by omega : 1 ≤ k₁)]
  have hvpos : 0 < f v := by
    have := hrise (k₁ - 1) (by omega) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k₁)] at this
    linarith
  have hθv : θ * f v ≤ f v := by
    have := habove k₁ le_rfl
    linarith
  have hθ₀ : 0 ≤ θ := by
    by_contra! hneg
    have : θ * f v < 0 := mul_neg_of_neg_of_pos hneg hvpos
    linarith
  -- Split `l` around the cut segment.
  have htake : l.take (k₁ - 1) = l.take k₀ ++ m := by
    rw [← List.take_append_drop k₀ (l.take (k₁ - 1)), List.take_take, min_eq_left (by omega)]
  have hdrop : l.drop (k₁ - 1) = v :: l.drop k₁ := by
    rw [List.drop_eq_getElem_cons (by omega), Nat.sub_add_cancel (by omega : 1 ≤ k₁)]
  have hsplit : ofSegments 𝕜 l =
      ofSegments 𝕜 (l.take k₀ ++ (m ++ [θ • v]) ++ ((1 - θ) • v :: l.drop k₁)) := by
    rw [ofSegments_append_cut_eq hθ₀
      ((mul_le_iff_le_one_left hvpos).mp hθv), ← htake, ← hdrop, List.take_append_drop]
  rw [hsplit, lower_ofSegments_append_append]
  · -- The minimum is attained at the end of `l.take k₀`.
    have hsplit₀ := listMinHeight_append (f := f) (l.take k₀) (l.drop k₀)
    rw [List.take_append_drop] at hsplit₀
    rw [h₀, hsplit₀]
    exact min_le_left _ _
  · -- The heights rise along `m` and along the initial piece of `v`.
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hw
      have hlen : m.length = k₁ - 1 - k₀ := by
        simp only [m, List.length_drop, List.length_take]
        omega
      simp only [m, List.getElem_drop, List.getElem_take]
      have := hrise (k₀ + n) (by omega) (by omega)
      rw [hstep _ (by omega)] at this
      linarith
    · rw [List.mem_singleton.mp hw, map_smul, smul_eq_mul]
      exact mul_nonneg hθ₀ hvpos.le
  · -- They rise by exactly one in total.
    have hm : f m.sum = f (l.take (k₁ - 1)).sum - f (l.take k₀).sum := by
      rw [htake, List.sum_append, map_add, add_sub_cancel_left]
    rw [List.sum_append, map_add, hm, List.sum_singleton, map_smul, smul_eq_mul, h₀]
    linarith
  · -- Afterwards they stay at least `h + 1`.
    obtain ⟨n, hn⟩ := exists_listMinHeight_eq (f := f) ((1 - θ) • v :: l.drop k₁)
    rw [hn]
    obtain _ | n := n
    · simp
    rw [List.take_succ_cons, List.sum_cons, map_add, map_smul, smul_eq_mul]
    have hafter : f (l.take (k₁ + n)).sum = f (l.take k₁).sum + f ((l.drop k₁).take n).sum := by
      rw [List.take_add, List.sum_append, map_add]
    have := habove (k₁ + n) (by omega)
    linarith

end TauCeti.PLPath

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
(`TauCeti.PLPath.lower_ofSegments_eq_of_strictly_rising`). Dually, raising reflects a piece that
falls monotonically from one more than the minimum down to the minimum
(`TauCeti.PLPath.raise_ofSegments_append_append`,
`TauCeti.PLPath.raise_ofSegments_eq_of_strictly_falling`). These are the shapes of the height of a
Lakshmibai–Seshadri path at a lowering or raising step.

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

/-- **Raising a path that falls from one above a minimum to the minimum.** Suppose the path
presented by `l₁ ++ l₂ ++ l₃` stays at least as high as the end of `l₁` along `l₁`, falls
monotonically along `l₂` by exactly one to its global minimum, and stays at least at that minimum
along `l₃`. Then raising reflects `l₂` and keeps `l₁` and `l₃`. -/
theorem raise_ofSegments_append_append {l₁ l₂ l₃ : List V}
    (h₁ : f l₁.sum ≤ listMinHeight f l₁) (h₂ : ∀ v ∈ l₂, f v ≤ 0) (h₂₁ : f l₂.sum = -1)
    (h₃ : 0 ≤ listMinHeight f l₃) :
    raise f x (ofSegments 𝕜 (l₁ ++ l₂ ++ l₃)) =
      some (ofSegments 𝕜 (l₁ ++ l₂.map (preReflection x f) ++ l₃)) := by
  set m₁ := (l₃.map Neg.neg).reverse
  set m₂ := (l₂.map Neg.neg).reverse
  set m₃ := (l₁.map Neg.neg).reverse
  have hrev : (ofSegments 𝕜 (l₁ ++ l₂ ++ l₃)).reverse = ofSegments 𝕜 (m₁ ++ m₂ ++ m₃) := by
    simp only [m₁, m₂, m₃, ofSegments_append, reverse_mul, reverse_ofSegments, mul_assoc]
  have hlow := lower_ofSegments_append_append (x := x) (f := f) (l₁ := m₁) (l₂ := m₂) (l₃ := m₃)
    (by simp only [m₁, listMinHeight_reverse_map_neg, ← List.sum_neg_reverse, map_neg]; linarith)
    (by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hv)
      rw [map_neg]
      linarith [h₂ w hw])
    (by simp only [m₂, ← List.sum_neg_reverse, map_neg, h₂₁, neg_neg])
    (by simp only [m₃, listMinHeight_reverse_map_neg]; linarith)
  rw [raise_def, hrev, hlow, Option.map_some]
  congr 1
  have hm₂ : (ofSegments 𝕜 (m₂.map (preReflection x f))).reverse =
      ofSegments 𝕜 (l₂.map (preReflection x f)) := by
    rw [reverse_ofSegments]
    congr 1
    simp only [m₂, List.map_reverse, List.reverse_reverse, List.map_map, Function.comp_def,
      map_neg, neg_neg]
  simp only [m₁, m₃, ofSegments_append, reverse_mul, ← reverse_ofSegments, reverse_reverse, hm₂,
    mul_assoc]

/-- **Raising a path whose height falls strictly to a minimum.** Let `h` be the minimal height of
the path presented by `l`, attained at the vertex `k₁`. Suppose the height is at least `h + 1` at
every vertex up to `k₀`, falls strictly from the vertex `k₀` to the vertex `k₁`, and is at most
`h + 1` at the vertex `k₀ + 1`. If `θ` is the fraction of the segment `v = l[k₀]` at which the
height reaches `h + 1`, then raising reflects the piece of the path between that point and the
vertex `k₁`, and keeps the rest. -/
theorem raise_ofSegments_eq_of_strictly_falling {l : List V} {k₀ k₁ : ℕ} {θ : 𝕜}
    (hk₀₁ : k₀ < k₁) (hk₁ : k₁ ≤ l.length) (h₁ : f (l.take k₁).sum = listMinHeight f l)
    (habove : ∀ j ≤ k₀, listMinHeight f l + 1 ≤ f (l.take j).sum)
    (hfall : ∀ j, k₀ ≤ j → j < k₁ → f (l.take (j + 1)).sum < f (l.take j).sum)
    (hθ : f (l.take k₀).sum + θ * f l[k₀] = listMinHeight f l + 1)
    (hcut : f (l.take (k₀ + 1)).sum ≤ listMinHeight f l + 1) :
    raise f x (ofSegments 𝕜 l) = some (ofSegments 𝕜 ((l.take k₀ ++ [θ • l[k₀]]) ++
      ((1 - θ) • l[k₀] :: (l.take k₁).drop (k₀ + 1)).map (preReflection x f) ++
        l.drop k₁)) := by
  set v := l[k₀]
  set m := (l.take k₁).drop (k₀ + 1)
  have hstep : ∀ j (hj : j < l.length), f (l.take (j + 1)).sum = f (l.take j).sum + f l[j] := by
    intro j hj
    rw [List.sum_take_succ _ _ hj, map_add]
  have hv : f (l.take k₀).sum + f v = f (l.take (k₀ + 1)).sum := (hstep k₀ (by omega)).symm
  have hvneg : f v < 0 := by
    have := hfall k₀ le_rfl hk₀₁
    linarith
  have hθ₀ : 0 ≤ θ := by
    by_contra! hneg
    have : 0 < θ * f v := mul_pos_of_neg_of_neg hneg hvneg
    linarith [habove k₀ le_rfl]
  have hθ₁ : θ ≤ 1 := by
    by_contra! hgt
    have : θ * f v < f v := by
      have : (θ - 1) * f v < 0 := mul_neg_of_pos_of_neg (by linarith) hvneg
      linarith
    linarith
  -- Split `l` around the cut segment `v = l[k₀]`.
  have htake : l.take k₁ = l.take k₀ ++ v :: m := by
    rw [← List.take_append_drop (k₀ + 1) (l.take k₁), List.take_take, min_eq_left (by omega),
      ← List.take_append_drop k₀ (l.take (k₀ + 1)), List.take_take, min_eq_left (by omega)]
    have hd : (l.take (k₀ + 1)).drop k₀ = [v] := by
      rw [List.drop_take, List.drop_eq_getElem_cons (l := l) (by omega : k₀ < l.length),
        show k₀ + 1 - k₀ = 1 by omega, List.take_succ_cons, List.take_zero]
    rw [hd, List.append_assoc, List.singleton_append]
  have hdrop : l.drop k₀ = v :: (m ++ l.drop k₁) := by
    have hl : l = l.take k₀ ++ v :: (m ++ l.drop k₁) := by
      calc
        l = l.take k₁ ++ l.drop k₁ := (List.take_append_drop k₁ l).symm
        _ = l.take k₀ ++ v :: (m ++ l.drop k₁) := by
          rw [htake, List.append_assoc, List.cons_append]
    have hlen : (l.take k₀).length = k₀ := List.length_take_of_le (by omega)
    conv_lhs => rw [hl]
    simp [hlen]
  have hsplit : ofSegments 𝕜 l =
      ofSegments 𝕜 ((l.take k₀ ++ [θ • v]) ++ ((1 - θ) • v :: m) ++ l.drop k₁) := by
    have hcut' := ofSegments_append_cut_eq (a := l.take k₀) (m := []) (r := m ++ l.drop k₁)
      (v := v) hθ₀ hθ₁
    simp only [List.nil_append, List.append_nil, ← hdrop, List.take_append_drop] at hcut'
    simpa only [List.append_assoc, List.cons_append] using hcut'.symm
  rw [hsplit, raise_ofSegments_append_append]
  · -- Up to the cut, the height stays at least `h + 1`.
    have hl₁sum : f (l.take k₀ ++ [θ • v]).sum = listMinHeight f l + 1 := by
      rw [List.sum_append, List.sum_singleton, map_add, map_smul, smul_eq_mul, hθ]
    obtain ⟨n, hn⟩ := exists_listMinHeight_eq (f := f) (l.take k₀ ++ [θ • v])
    rw [hl₁sum, hn]
    by_cases hnk : n ≤ k₀
    · rw [List.take_append_of_le_length (by simp; omega), List.take_take, min_eq_left hnk]
      exact habove n hnk
    · rw [List.take_of_length_le (by simp; omega), hl₁sum]
  · -- Along `(1 - θ) • v :: m`, the segments have nonpositive height.
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · rw [map_smul, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hvneg.le
    · obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hw
      have hmlen : m.length = k₁ - (k₀ + 1) := by simp [m]; omega
      simp only [m, List.getElem_drop, List.getElem_take]
      have := hfall (k₀ + 1 + n) (by omega) (by omega)
      rw [hstep _ (by omega)] at this
      linarith
  · -- The falling piece drops by `-1` from `h + 1` to `h`.
    have hsum₁ : f (l.take k₁).sum = f (l.take k₀).sum + f v + f m.sum := by
      rw [htake, List.sum_append, List.sum_cons, map_add, map_add, add_assoc]
    rw [List.sum_cons, map_add, map_smul, smul_eq_mul]
    linarith
  · -- After `k₁`, the height never drops below `h`.
    have hsplit₁ := listMinHeight_append (f := f) (l.take k₁) (l.drop k₁)
    rw [List.take_append_drop] at hsplit₁
    have : listMinHeight f l ≤ f (l.take k₁).sum + listMinHeight f (l.drop k₁) := by
      rw [hsplit₁]
      exact min_le_right _ _
    linarith

end TauCeti.PLPath

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Reduce

/-!
# The Nielsen property of a homomorphism of free groups

A homomorphism `f : F(α) → F(β)` of free groups has the *Nielsen property* with respect to a
relation `r` between words of `F(α)`, its *blocks*, ([IFT], Definition 32) if every block `u`
occurring in `r` has a factorisation of the reduced word of `f u` into a left part, a nonempty
middle and a right part such that for `r u u'` the left part and the middle of `u`, and the middle
and the right part of `u'`, survive as a prefix and a suffix of the reduced word of `f u * f u'`
(`FreeGroup.IsNielsenDecomposition`, `FreeGroup.HasNielsenProperty`). In [IFT] the blocks are the
letters and the exceptional words, and `r` relates two blocks whose product is a subword, but not
an exceptional word, of a word of a set `W`; this contains the relation between consecutive blocks
of the irreducible decompositions of the words of `W` (Definition 31, `List.maximalBlocks`), and
the property passes to smaller relations (`FreeGroup.HasNielsenProperty.mono`).

Then, in the image of a product of blocks whose consecutive blocks are related by `r`, the middle of
every block survives, as written and in its place
(`FreeGroup.IsNielsenDecomposition.toWord_map_flatten`, [IFT], Lemma 52): cancellation between the
images of the blocks never reaches a middle.

## Main definitions

* `FreeGroup.IsNielsenDecomposition`, `FreeGroup.HasNielsenProperty`: the Nielsen property.

## Main results

* `FreeGroup.IsNielsenDecomposition.toWord_map_flatten`: the middles survive ([IFT], Lemma 52).

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §7.1, Definitions 31 and 32, Lemma 52, and the remark before Lemma 61 (the middles
  are nonempty).
-/

public section

namespace FreeGroup

variable {α β : Type*} [DecidableEq β]

/-- The functions `L`, `M`, `R` are a *Nielsen decomposition* of `f` with respect to a relation `r`
between blocks ([IFT], Definition 32): for `r u u'`, the reduced words of `f u` and `f u'` are
`L u ++ M u ++ R u` and `L u' ++ M u' ++ R u'` with nonempty middles ([IFT], the remark before
Lemma 61: the middle "cannot" be empty), and `L u ++ M u` and `M u' ++ R u'` are a prefix and a
suffix of the reduced word of `f u * f u'`. -/
def IsNielsenDecomposition (f : FreeGroup α →* FreeGroup β)
    (r : List (α × Bool) → List (α × Bool) → Prop) (L M R : List (α × Bool) → List (β × Bool)) :
    Prop :=
  ∀ u u', r u u' →
    (f (mk u)).toWord = L u ++ M u ++ R u ∧ M u ≠ [] ∧
    (f (mk u')).toWord = L u' ++ M u' ++ R u' ∧ M u' ≠ [] ∧
    L u ++ M u <+: (f (mk u) * f (mk u')).toWord ∧
    M u' ++ R u' <:+ (f (mk u) * f (mk u')).toWord

/-- A homomorphism `f` of free groups has the *Nielsen property* with respect to a relation `r`
between blocks if it has a Nielsen decomposition with respect to `r` ([IFT], Definition 32). -/
def HasNielsenProperty (f : FreeGroup α →* FreeGroup β)
    (r : List (α × Bool) → List (α × Bool) → Prop) : Prop :=
  ∃ L M R : List (α × Bool) → List (β × Bool), IsNielsenDecomposition f r L M R

variable {f : FreeGroup α →* FreeGroup β} {r r' : List (α × Bool) → List (α × Bool) → Prop}
  {L M R : List (α × Bool) → List (β × Bool)}

/-- The defining property of a Nielsen decomposition. -/
theorem isNielsenDecomposition_iff : IsNielsenDecomposition f r L M R ↔ ∀ u u', r u u' →
      (f (mk u)).toWord = L u ++ M u ++ R u ∧ M u ≠ [] ∧
      (f (mk u')).toWord = L u' ++ M u' ++ R u' ∧ M u' ≠ [] ∧
      L u ++ M u <+: (f (mk u) * f (mk u')).toWord ∧
      M u' ++ R u' <:+ (f (mk u) * f (mk u')).toWord :=
  Iff.rfl

/-- The defining property of the Nielsen property. -/
theorem hasNielsenProperty_iff :
    HasNielsenProperty f r ↔ ∃ L M R : List (α × Bool) → List (β × Bool),
      IsNielsenDecomposition f r L M R :=
  Iff.rfl

/-- A Nielsen decomposition with respect to a relation is one with respect to every smaller
relation. -/
theorem IsNielsenDecomposition.mono (h : IsNielsenDecomposition f r' L M R) (hr : r ≤ r') :
    IsNielsenDecomposition f r L M R :=
  isNielsenDecomposition_iff.2 fun u u' huu' => isNielsenDecomposition_iff.1 h u u' (hr u u' huu')

/-- The Nielsen property with respect to a relation implies it with respect to every smaller
relation. -/
theorem HasNielsenProperty.mono (h : HasNielsenProperty f r') (hr : r ≤ r') :
    HasNielsenProperty f r :=
  let ⟨L, M, R, h⟩ := hasNielsenProperty_iff.1 h
  hasNielsenProperty_iff.2 ⟨L, M, R, h.mono hr⟩

namespace IsNielsenDecomposition

-- For related blocks `u` and `u'`, the left part and the middle of `u` and the middle and the
-- right part of `u'` survive disjointly in the reduced word of `f u * f u'`.
private theorem exists_toWord_mul_eq (h : IsNielsenDecomposition f r L M R) {u u' : List (α × Bool)}
    (huu' : r u u') :
    ∃ J, (f (mk u) * f (mk u')).toWord = L u ++ M u ++ J ++ (M u' ++ R u') := by
  obtain ⟨hu, -, hu', -, hp, hs⟩ := isNielsenDecomposition_iff.1 h u u' huu'
  exact exists_toWord_mul_eq_append_append (hu ▸ List.prefix_append _ _) hp
    ⟨L u', by rw [hu', List.append_assoc]⟩ hs

-- The middle of the last block survives: the reduced word of `f` of the product of the blocks
-- `vs ++ [w]` is the reduced word of `f` of the product of `vs` times the left part of `w`,
-- followed by the middle and the right part of `w`.
private theorem toWord_map_flatten_append_singleton (h : IsNielsenDecomposition f r L M R)
    {vs : List (List (α × Bool))} {w : List (α × Bool)} (hc : (vs ++ [w]).IsChain r)
    (hw : (f (mk w)).toWord = L w ++ M w ++ R w) :
    (f (mk (vs ++ [w]).flatten)).toWord = (f (mk vs.flatten) * mk (L w)).toWord ++ M w ++ R w := by
  induction vs using List.reverseRecOn generalizing w with
  | nil =>
    have : IsReduced (L w) := isReduced_toWord.infix ⟨[], M w ++ R w, by rw [hw]; simp⟩
    simp [hw, ← one_eq_mk, this.reduce_eq]
  | append_singleton vs v ih =>
    obtain ⟨hc', hvw⟩ : (vs ++ [v]).IsChain r ∧ r v w := by simpa using hc
    obtain ⟨hv, hMv, -⟩ := isNielsenDecomposition_iff.1 h v w hvw
    obtain ⟨J, hJ⟩ := h.exists_toWord_mul_eq hvw
    set X := f (mk (vs ++ [v]).flatten)
    set A := (f (mk vs.flatten) * mk (L v)).toWord ++ M v ++ J
    -- Glue the last block `w` to the product of the blocks before it, along the middle of `v`.
    have key : (X * f (mk w)).toWord = A ++ (M w ++ R w) := by
      rw [toWord_mul_eq_of_middle (ih hc' hv) hv hMv (y := f (mk w)) (Q := J ++ (M w ++ R w))
        (by rw [hJ]; simp)]
      simp [A]
    -- Hence `X * L w` is reduced as `A`: cancel `M w ++ R w` on the right.
    have hXL : X * mk (L w) = mk A := by
      have e : X * mk (L w) * mk (M w ++ R w) = mk A * mk (M w ++ R w) := by
        rw [mul_assoc, mul_mk, ← List.append_assoc, ← hw, mk_toWord, ← mk_toWord (x := X * _),
          key, mul_mk]
      exact mul_right_cancel e
    have hA : IsReduced A := isReduced_toWord.infix ⟨[], M w ++ R w, by rw [key]; simp⟩
    rw [List.flatten_append, List.flatten_singleton, ← mul_mk, _root_.map_mul, key, hXL, toWord_mk,
      hA.reduce_eq]
    simp [A]

-- The middle of the first block survives: the reduced word of `f` of the product of the blocks
-- `w :: vs` is the left part and the middle of `w`, followed by the reduced word of the right part
-- of `w` times `f` of the product of `vs`.
private theorem toWord_map_flatten_cons (h : IsNielsenDecomposition f r L M R) {w : List (α × Bool)}
    {vs : List (List (α × Bool))} (hc : (w :: vs).IsChain r)
    (hw : (f (mk w)).toWord = L w ++ M w ++ R w) :
    (f (mk (w :: vs).flatten)).toWord = L w ++ M w ++ (mk (R w) * f (mk vs.flatten)).toWord := by
  induction vs generalizing w with
  | nil =>
    have : IsReduced (R w) := isReduced_toWord.infix ⟨L w ++ M w, [], by rw [hw]; simp⟩
    simp [hw, ← one_eq_mk, this.reduce_eq]
  | cons v vs ih =>
    obtain ⟨hwv, hc'⟩ := List.isChain_cons_cons.1 hc
    obtain ⟨-, -, hv, hMv, -⟩ := isNielsenDecomposition_iff.1 h w v hwv
    obtain ⟨J, hJ⟩ := h.exists_toWord_mul_eq hwv
    set Y := f (mk (v :: vs).flatten)
    -- Glue the first block `w` to the product of the blocks after it, along the middle of `v`.
    have key : (f (mk w) * Y).toWord =
        L w ++ M w ++ (J ++ M v ++ (mk (R v) * f (mk vs.flatten)).toWord) := by
      have hY : Y = f (mk v) * f (mk vs.flatten) := by simp [Y, ← mul_mk]
      rw [hY, ← mul_assoc, toWord_mul_eq_of_middle (P := L w ++ M w ++ J) (by rw [hJ]; simp) hv
        hMv (by rw [← _root_.map_mul, mul_mk, ← List.flatten_cons]; exact ih hc' hv)]
      simp
    -- Hence `R w * Y` is reduced as the rest: cancel `L w ++ M w` on the left.
    have hRY : mk (R w) * Y = mk (invRev (L w ++ M w)) * (f (mk w) * Y) := by
      rw [← inv_mk, ← mk_toWord (x := f (mk w)), hw, ← mul_mk (L₁ := L w ++ M w), mul_assoc,
        inv_mul_cancel_left]
    have hdrop := toWord_mk_mul_of_invRev_prefix (x := invRev (L w ++ M w)) (g := f (mk w) * Y)
      (by rw [invRev_invRev, key]; exact List.prefix_append _ _)
    rw [List.flatten_cons, ← mul_mk, _root_.map_mul, key, hRY, hdrop, key, invRev_length,
      List.drop_left]

-- Every block of a chain of at least two blocks is related to a neighbour, so it has its
-- decomposition.
private theorem toWord_getElem (h : IsNielsenDecomposition f r L M R) {us : List (List (α × Bool))}
    (hus : us.IsChain r) (hus₂ : 2 ≤ us.length) {i : ℕ} (hi : i < us.length) :
    (f (mk us[i])).toWord = L us[i] ++ M us[i] ++ R us[i] ∧ M us[i] ≠ [] := by
  by_cases hi' : i + 1 < us.length
  · obtain ⟨hu, hM, -⟩ := isNielsenDecomposition_iff.1 h _ _ (hus.getElem i hi')
    exact ⟨hu, hM⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by lia⟩
    obtain ⟨-, -, hu, hM, -⟩ := isNielsenDecomposition_iff.1 h _ _ (hus.getElem j (by lia))
    exact ⟨hu, hM⟩

/-- **The middles survive** ([IFT], Lemma 52): if `L`, `M`, `R` is a Nielsen decomposition of `f`
with respect to `r` and consecutive blocks of a list `us` of at least two blocks are related by `r`,
then the reduced word of `f` of the product of the blocks is the reduced word of `f` of the first
`i` blocks times `L` of the `i`-th block, followed by its middle, followed by the reduced word of
`R` of the `i`-th block times `f` of the remaining blocks. -/
theorem toWord_map_flatten (h : IsNielsenDecomposition f r L M R) {us : List (List (α × Bool))}
    (hus : us.IsChain r) (hus₂ : 2 ≤ us.length) {i : ℕ} (hi : i < us.length) :
    (f (mk us.flatten)).toWord = (f (mk (us.take i).flatten) * mk (L us[i])).toWord ++ M us[i] ++
      (mk (R us[i]) * f (mk (us.drop (i + 1)).flatten)).toWord := by
  obtain ⟨hd, hM⟩ := h.toWord_getElem hus hus₂ hi
  have hl := h.toWord_map_flatten_append_singleton (vs := us.take i)
    (by rw [List.take_append_getElem hi]; exact hus.take (i + 1)) hd
  have hr := h.toWord_map_flatten_cons (vs := us.drop (i + 1))
    (by rw [← List.drop_eq_getElem_cons hi]; exact hus.drop i) hd
  have hsplit : us.flatten = (us.take i ++ [us[i]]).flatten ++ (us.drop (i + 1)).flatten := by
    rw [← List.flatten_append, List.take_append_getElem hi, List.take_append_drop]
  rw [hsplit, ← mul_mk, _root_.map_mul]
  -- Glue the two sides along the middle of `us[i]`.
  refine toWord_mul_eq_of_middle hl hd hM ?_
  rw [← _root_.map_mul, mul_mk, ← List.flatten_cons]
  exact hr

end IsNielsenDecomposition

/-- The endomorphism `a ↦ a b`, `b ↦ b` of the free group on two generators has the Nielsen
property with respect to the relation that puts the letter `a` or the letter `b` after the letter
`a`, with `L = []` and the middles `a` and `b`: no letter cancels in `a b a b` or `a b b`. (After
`a`, the letter `b⁻¹` is excluded: the image of `a b⁻¹` is `a`.) -/
example : HasNielsenProperty (FreeGroup.lift fun i : Fin 2 => if i = 0 then of 0 * of 1 else of 1)
    (fun u u' => u = [(0, true)] ∧ (u' = [(0, true)] ∨ u' = [(1, true)])) := by
  refine hasNielsenProperty_iff.2 ⟨fun _ => [],
    fun u => if u = [(0, true)] then [(0, true)] else [(1, true)],
    fun u => if u = [(0, true)] then [(1, true)] else [], isNielsenDecomposition_iff.2 ?_⟩
  rintro u u' ⟨rfl, rfl | rfl⟩ <;> decide

end FreeGroup

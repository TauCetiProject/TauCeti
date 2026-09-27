/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem.Length
public import TauCeti.GroupTheory.TitsSystem.Bruhat.Subword
public import TauCeti.GroupTheory.TitsSystem.Bruhat.Uniqueness

/-!
# Bruhat cell multiplication and the length function

Let `(B, N)` be a Tits system with Weyl group `W` and length function `ℓ`, the word length with
respect to the simple reflections. The rank-one multiplication law leaves two possibilities for the
product of a simple cell with an arbitrary cell:

```text
(B s B)(B w B) = B (s w) B    or    (B s B)(B w B) = B (s w) B ∪ B w B.
```

This file decides between them by the length function: the first alternative holds exactly when
`ℓ (s w) > ℓ w`, the second exactly when `ℓ (s w) < ℓ w` (Bourbaki, Chapter IV, §2, no. 4,
Theorem 2). Multiplication of Bruhat cells by simple cells is thereby governed entirely by the
length function on the Weyl group, which is the input for the exchange condition in
`TauCeti.GroupTheory.TitsSystem.Bruhat.Exchange`.

Conversely the cells control the length: since one of the two alternatives always holds, a simple
reflection never preserves the length, `ℓ (s w) = ℓ w ± 1`.

Every statement has a `_right` variant for multiplication by a simple cell on the right, because
inversion carries the cell at `w` to the cell at `w⁻¹` and preserves the length.

## Main declarations

* `TauCeti.TitsSystem.bruhatCell_mul_eq_of_wordLength_le`: **length-increasing multiplication**,
  `(B s B)(B w B) = B (s w) B` when `ℓ w ≤ ℓ (s w)`.
* `TauCeti.TitsSystem.bruhatCell_mul_eq_union_of_wordLength_lt`: **length-decreasing
  multiplication**, `(B s B)(B w B) = B (s w) B ∪ B w B` when `ℓ (s w) < ℓ w`.
* `TauCeti.TitsSystem.wordLength_simple_mul_ne` and `TauCeti.TitsSystem.wordLength_simple_mul`:
  a simple reflection changes the length by exactly one.
* `TauCeti.TitsSystem.bruhatCell_mul_eq_iff_wordLength_lt` and
  `TauCeti.TitsSystem.bruhatCell_mul_eq_union_iff_wordLength_lt`: the two alternatives of the
  rank-one law are characterized by the length function.
* The `_right` variants of the above, for multiplication by a simple cell on the right.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §2, no. 4, Theorem 2.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Section 29.3.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), Section 8.3.
-/

public section

open scoped Pointwise

namespace TauCeti.TitsSystem

universe u

variable {G : Type u} [Group G] (T : TitsSystem G)

local prefix:100 "ℓ " => T.simpleGenerators.wordLength

/-! ### The rank-one law decided by the length function -/

/-- **Length-increasing multiplication.** If `ℓ w ≤ ℓ (s w)`, then `(B s B)(B w B) = B (s w) B`. -/
@[simp]
theorem bruhatCell_mul_eq_of_wordLength_le {s : T.WeylGroup} (hs : s ∈ T.simple)
    {w : T.WeylGroup} (hw : ℓ w ≤ ℓ (s * w)) :
    T.bruhatCell s * T.bruhatCell w = T.bruhatCell (s * w) := by
  -- Induction on an upper bound for the length of `w`, peeling off the last letter of a reduced
  -- word `w = w' s'`.
  suffices key : ∀ n : ℕ, ∀ w : T.WeylGroup, ℓ w ≤ n → ℓ w ≤ ℓ (s * w) →
      T.bruhatCell s * T.bruhatCell w = T.bruhatCell (s * w) from key _ w le_rfl hw
  intro n
  induction n with
  | zero =>
    intro w hw _
    rw [Nat.le_zero, Group.Generators.wordLength_eq_zero_iff] at hw
    subst hw
    rw [mul_one, T.bruhatCell_one, T.bruhatCell_mul_subgroupB]
  | succ n ih =>
    intro w hwn hw
    obtain ⟨l, hl, hlen, rfl⟩ := T.exists_prod_eq_of_wordLength w
    rcases List.eq_nil_or_concat l with rfl | ⟨l', s', rfl⟩
    · rw [List.prod_nil, mul_one, T.bruhatCell_one, T.bruhatCell_mul_subgroupB]
    rw [List.concat_eq_append, List.forall_mem_append, List.forall_mem_singleton] at hl
    obtain ⟨hl', hs'⟩ := hl
    rw [List.concat_eq_append, List.prod_append, List.prod_singleton] at hw hwn hlen ⊢
    rw [List.length_append, List.length_singleton] at hlen
    have hw'len : ℓ l'.prod ≤ n := (T.wordLength_prod_le hl').trans (by omega)
    -- The shortened word still satisfies the length hypothesis.
    have hw'inc : ℓ l'.prod ≤ ℓ (s * l'.prod) := by
      have h1 := T.wordLength_mul_simple_le (s * l'.prod) hs'
      have h2 := T.wordLength_prod_le hl'
      rw [mul_assoc] at h1
      omega
    have hih := ih l'.prod hw'len hw'inc
    have hsub : T.bruhatCell s * T.bruhatCell (l'.prod * s') ⊆
        T.bruhatCell (s * (l'.prod * s')) ∪ T.bruhatCell (s * l'.prod) := by
      calc T.bruhatCell s * T.bruhatCell (l'.prod * s')
          ⊆ T.bruhatCell s * (T.bruhatCell l'.prod * T.bruhatCell s') :=
            Set.mul_subset_mul_left (T.subset_bruhatCell_mul_of_mem_simple_right l'.prod hs')
        _ = T.bruhatCell (s * l'.prod) * T.bruhatCell s' := by rw [← mul_assoc, hih]
        _ ⊆ T.bruhatCell (s * l'.prod * s') ∪ T.bruhatCell (s * l'.prod) :=
            T.bruhatCell_mul_subset_union_of_mem_simple_right (s * l'.prod) hs'
        _ = T.bruhatCell (s * (l'.prod * s')) ∪ T.bruhatCell (s * l'.prod) := by rw [mul_assoc]
    rcases T.bruhatCell_mul_eq_or_eq_union_of_mem_simple hs (l'.prod * s') with h | h
    · exact h
    exfalso
    have hcontain : T.bruhatCell (l'.prod * s') ⊆
        T.bruhatCell (s * (l'.prod * s')) ∪ T.bruhatCell (s * l'.prod) :=
      (h ▸ Set.subset_union_right).trans hsub
    rcases T.eq_or_eq_of_bruhatCell_subset_union hcontain with h1 | h1
    · exact T.simple_ne_one hs (by simpa using h1)
    · -- Then `s w = w'`, whose length is less than `ℓ w`.
      have h2 : s * (l'.prod * s') = l'.prod := by
        rw [h1, T.simple_mul_simple_cancel_left hs]
      have h3 := T.wordLength_prod_le hl'
      rw [h2] at hw
      omega

/-- **Length-decreasing multiplication.** If `ℓ (s w) < ℓ w`, then
`(B s B)(B w B) = B (s w) B ∪ B w B`. -/
@[simp]
theorem bruhatCell_mul_eq_union_of_wordLength_lt {s : T.WeylGroup} (hs : s ∈ T.simple)
    {w : T.WeylGroup} (hw : ℓ (s * w) < ℓ w) :
    T.bruhatCell s * T.bruhatCell w = T.bruhatCell (s * w) ∪ T.bruhatCell w := by
  -- Apply the length-increasing case to `s w` and multiply by `(B s B)(B s B) = B ∪ B s B`.
  have hkey : T.bruhatCell s * T.bruhatCell (s * w) = T.bruhatCell w := by
    have h := T.bruhatCell_mul_eq_of_wordLength_le hs (w := s * w)
      (by rw [T.simple_mul_simple_cancel_left hs]; exact hw.le)
    rwa [T.simple_mul_simple_cancel_left hs] at h
  calc T.bruhatCell s * T.bruhatCell w
      = T.bruhatCell s * (T.bruhatCell s * T.bruhatCell (s * w)) := by rw [hkey]
    _ = (T.bruhatCell 1 ∪ T.bruhatCell s) * T.bruhatCell (s * w) := by
        rw [← mul_assoc, T.bruhatCell_mul_self_eq_union_of_mem_simple hs]
    _ = T.bruhatCell (s * w) ∪ T.bruhatCell w := by
        rw [Set.union_mul, T.bruhatCell_one, T.subgroupB_mul_bruhatCell, hkey]

/-- A simple reflection never preserves the length. -/
theorem wordLength_simple_mul_ne {s : T.WeylGroup} (hs : s ∈ T.simple) (w : T.WeylGroup) :
    ℓ (s * w) ≠ ℓ w := by
  -- Otherwise the length-increasing case applies to both `w` and `s w`, and
  -- `(B s B)(B s B)(B w B) = B ∪ B s B` times `B w B` would collapse to the single cell `B w B`.
  intro h
  have h1 := T.bruhatCell_mul_eq_of_wordLength_le hs (w := w) h.ge
  have h2 := T.bruhatCell_mul_eq_of_wordLength_le hs (w := s * w)
    (by rw [T.simple_mul_simple_cancel_left hs]; exact h.le)
  rw [T.simple_mul_simple_cancel_left hs] at h2
  have h3 : T.bruhatCell (s * w) ⊆ T.bruhatCell w := by
    calc T.bruhatCell (s * w) ⊆ T.bruhatCell w ∪ T.bruhatCell (s * w) := Set.subset_union_right
      _ = (T.bruhatCell 1 ∪ T.bruhatCell s) * T.bruhatCell w := by
          rw [Set.union_mul, T.bruhatCell_one, T.subgroupB_mul_bruhatCell, h1]
      _ = T.bruhatCell s * T.bruhatCell s * T.bruhatCell w := by
          rw [T.bruhatCell_mul_self_eq_union_of_mem_simple hs]
      _ = T.bruhatCell w := by rw [mul_assoc, h1, h2]
  exact T.simple_ne_one hs (by simpa using T.bruhatCell_subset_iff.mp h3)

/-- A simple reflection changes the length by exactly one on the left. -/
theorem wordLength_simple_mul {s : T.WeylGroup} (hs : s ∈ T.simple) (w : T.WeylGroup) :
    ℓ (s * w) = ℓ w + 1 ∨ ℓ (s * w) + 1 = ℓ w := by
  have h1 := T.wordLength_simple_mul_le hs w
  have h2 := T.wordLength_le_wordLength_simple_mul_add_one hs w
  have h3 := T.wordLength_simple_mul_ne hs w
  omega

/-- The two alternatives of the rank-one law are decided by the length: `(B s B)(B w B)` is the
single cell `B (s w) B` exactly when `s` increases the length of `w`. -/
@[simp]
theorem bruhatCell_mul_eq_iff_wordLength_lt {s : T.WeylGroup} (hs : s ∈ T.simple)
    (w : T.WeylGroup) :
    T.bruhatCell s * T.bruhatCell w = T.bruhatCell (s * w) ↔ ℓ w < ℓ (s * w) := by
  refine ⟨fun h ↦ ?_, fun h ↦ T.bruhatCell_mul_eq_of_wordLength_le hs h.le⟩
  by_contra hlt
  have hlt' : ℓ (s * w) < ℓ w :=
    lt_of_le_of_ne (not_lt.mp hlt) (T.wordLength_simple_mul_ne hs w)
  have h2 := T.bruhatCell_mul_eq_union_of_wordLength_lt hs hlt'
  rw [h] at h2
  have h3 : T.bruhatCell w ⊆ T.bruhatCell (s * w) := h2 ▸ Set.subset_union_right
  exact T.simple_ne_one hs (by simpa using T.bruhatCell_subset_iff.mp h3)

/-- The two alternatives of the rank-one law are decided by the length: `(B s B)(B w B)` is the
union `B (s w) B ∪ B w B` exactly when `s` decreases the length of `w`. -/
@[simp]
theorem bruhatCell_mul_eq_union_iff_wordLength_lt {s : T.WeylGroup} (hs : s ∈ T.simple)
    (w : T.WeylGroup) :
    T.bruhatCell s * T.bruhatCell w = T.bruhatCell (s * w) ∪ T.bruhatCell w ↔
      ℓ (s * w) < ℓ w := by
  refine ⟨fun h ↦ ?_, T.bruhatCell_mul_eq_union_of_wordLength_lt hs⟩
  by_contra hlt
  have hlt' : ℓ w < ℓ (s * w) :=
    lt_of_le_of_ne (not_lt.mp hlt) (T.wordLength_simple_mul_ne hs w).symm
  rw [(T.bruhatCell_mul_eq_iff_wordLength_lt hs w).mpr hlt'] at h
  have h3 : T.bruhatCell w ⊆ T.bruhatCell (s * w) := h ▸ Set.subset_union_right
  exact T.simple_ne_one hs (by simpa using T.bruhatCell_subset_iff.mp h3)

/-! ### The right-handed versions -/

/-- A simple reflection never preserves the length, on the right. -/
theorem wordLength_mul_simple_ne (w : T.WeylGroup) {s : T.WeylGroup} (hs : s ∈ T.simple) :
    ℓ (w * s) ≠ ℓ w := by
  rw [T.wordLength_mul_simple_eq_wordLength_simple_mul_inv w hs,
    ← Group.Generators.wordLength_inv _ w]
  exact T.wordLength_simple_mul_ne hs w⁻¹

/-- A simple reflection changes the length by exactly one on the right. -/
theorem wordLength_mul_simple (w : T.WeylGroup) {s : T.WeylGroup} (hs : s ∈ T.simple) :
    ℓ (w * s) = ℓ w + 1 ∨ ℓ (w * s) + 1 = ℓ w := by
  rw [T.wordLength_mul_simple_eq_wordLength_simple_mul_inv w hs,
    ← Group.Generators.wordLength_inv _ w]
  exact T.wordLength_simple_mul hs w⁻¹

/-- **Length-increasing multiplication on the right.** If `ℓ w ≤ ℓ (w s)`, then
`(B w B)(B s B) = B (w s) B`. -/
@[simp]
theorem bruhatCell_mul_eq_of_wordLength_le_right (w : T.WeylGroup) {s : T.WeylGroup}
    (hs : s ∈ T.simple) (hw : ℓ w ≤ ℓ (w * s)) :
    T.bruhatCell w * T.bruhatCell s = T.bruhatCell (w * s) := by
  have hw' : ℓ w⁻¹ ≤ ℓ (s * w⁻¹) := by
    rwa [← T.wordLength_mul_simple_eq_wordLength_simple_mul_inv w hs,
      Group.Generators.wordLength_inv]
  have h := congrArg Inv.inv (T.bruhatCell_mul_eq_of_wordLength_le hs hw')
  simpa only [mul_inv_rev, inv_bruhatCell, inv_inv, T.inv_simple hs] using h

/-- **Length-decreasing multiplication on the right.** If `ℓ (w s) < ℓ w`, then
`(B w B)(B s B) = B (w s) B ∪ B w B`. -/
@[simp]
theorem bruhatCell_mul_eq_union_of_wordLength_lt_right (w : T.WeylGroup) {s : T.WeylGroup}
    (hs : s ∈ T.simple) (hw : ℓ (w * s) < ℓ w) :
    T.bruhatCell w * T.bruhatCell s = T.bruhatCell (w * s) ∪ T.bruhatCell w := by
  have hw' : ℓ (s * w⁻¹) < ℓ w⁻¹ := by
    rwa [← T.wordLength_mul_simple_eq_wordLength_simple_mul_inv w hs,
      Group.Generators.wordLength_inv]
  have h := congrArg Inv.inv (T.bruhatCell_mul_eq_union_of_wordLength_lt hs hw')
  simpa only [mul_inv_rev, inv_bruhatCell, inv_inv, T.inv_simple hs, Set.union_inv] using h

/-- On the right, `(B w B)(B s B)` is the single cell `B (w s) B` exactly when `s` increases the
length of `w`. -/
@[simp]
theorem bruhatCell_mul_eq_iff_wordLength_lt_right (w : T.WeylGroup) {s : T.WeylGroup}
    (hs : s ∈ T.simple) :
    T.bruhatCell w * T.bruhatCell s = T.bruhatCell (w * s) ↔ ℓ w < ℓ (w * s) := by
  refine ⟨fun h ↦ ?_, fun h ↦ T.bruhatCell_mul_eq_of_wordLength_le_right w hs h.le⟩
  by_contra hlt
  have hlt' : ℓ (w * s) < ℓ w :=
    lt_of_le_of_ne (not_lt.mp hlt) (T.wordLength_mul_simple_ne w hs)
  have h2 := T.bruhatCell_mul_eq_union_of_wordLength_lt_right w hs hlt'
  rw [h] at h2
  have h3 : T.bruhatCell w ⊆ T.bruhatCell (w * s) := h2 ▸ Set.subset_union_right
  exact T.simple_ne_one hs (by simpa using T.bruhatCell_subset_iff.mp h3)

/-- On the right, `(B w B)(B s B)` is the union `B (w s) B ∪ B w B` exactly when `s` decreases the
length of `w`. -/
@[simp]
theorem bruhatCell_mul_eq_union_iff_wordLength_lt_right (w : T.WeylGroup) {s : T.WeylGroup}
    (hs : s ∈ T.simple) :
    T.bruhatCell w * T.bruhatCell s = T.bruhatCell (w * s) ∪ T.bruhatCell w ↔
      ℓ (w * s) < ℓ w := by
  refine ⟨fun h ↦ ?_, T.bruhatCell_mul_eq_union_of_wordLength_lt_right w hs⟩
  by_contra hlt
  have hlt' : ℓ w < ℓ (w * s) :=
    lt_of_le_of_ne (not_lt.mp hlt) (T.wordLength_mul_simple_ne w hs).symm
  rw [(T.bruhatCell_mul_eq_iff_wordLength_lt_right w hs).mpr hlt'] at h
  have h3 : T.bruhatCell w ⊆ T.bruhatCell (w * s) := h ▸ Set.subset_union_right
  exact T.simple_ne_one hs (by simpa using T.bruhatCell_subset_iff.mp h3)

end TauCeti.TitsSystem

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.FreeCancellation.Basic
public import TauCeti.KnotTheory.BraidWord.SeifertMatrix.Basic
public import TauCeti.KnotTheory.SeifertMatrix.Enlargement
public import TauCeti.KnotTheory.TristramLevine.Enlargement
public import TauCeti.LinearAlgebra.Matrix.Congruence

/-!
# Free cancellation and the Seifert matrix of a closed braid

Inserting an inverse pair `σᵢ^ε σᵢ^(-ε)` into a braid word adds two bands of opposite twist between
the discs `Dᵢ` and `Dᵢ₊₁` of the canonical Seifert surface of the closure, the surface whose
Seifert matrix is `TauCeti.BraidWord.seifertMatrix`. When level `i` already carries a band, the two
new bands form a tube on the old surface, so the Seifert matrix changes by an elementary enlargement
up to unimodular congruence: a row enlargement for `σᵢ σᵢ⁻¹` and a column enlargement for
`σᵢ⁻¹ σᵢ`. Hence the Alexander polynomial and the Tristram–Levine signatures of the Seifert matrix
do not change under a free insertion or deletion that keeps the set of levels carrying a letter.

The comparison is made in explicit bases. Write `p` for the insertion point, so that the new bands
sit at positions `p` and `p + 1`. The loops after the insertion are the old loops with their bands
moved past the insertion point, the loop `β = (p, p + 1)` through the two new bands, which is the
meridian of the tube, and the loops ending at `p` or starting at `p + 1`, which exist when a band of
level `i` precedes or follows the insertion point. If both exist, they replace the old loop `γ` of
level `i` across the insertion point, and `γ` is the sum of them and `β`. In the basis where that
sum stands in for `γ`, the old loops keep their entries, the column of `β` vanishes and its row is
`±1` times the coordinate vector of one remaining new loop (for `ε = 1`; transposed for `ε = -1`).
That is the shape recognised by `TauCeti.KnotTheory.exists_mul_mul_transpose_eq_enlargeRow`.

The hypothesis that level `i` is already in use is needed. On two strands, the empty word has the
`0 × 0` Seifert matrix while `σ₁ σ₁⁻¹` has the matrix `[0]`, because the canonical surface of the
empty word is disconnected.

## Main results

* `TauCeti.BraidWord.exists_seifertMatrix_insert_congr_enlargeRow`: inserting `σᵢ σᵢ⁻¹` on a level
  in use turns the Seifert matrix into a row enlargement of the old one, up to relabelling and a
  unimodular congruence.
* `TauCeti.BraidWord.exists_seifertMatrix_insert_congr_enlargeColumn`: the same for `σᵢ⁻¹ σᵢ`,
  with a column enlargement.
* `TauCeti.BraidWord.alexander_seifertMatrix_insert` and
  `TauCeti.BraidWord.tristramLevineSignature_seifertMatrix_insert`: such an insertion keeps the
  Alexander polynomial and the Tristram–Levine signatures of the Seifert matrix.
* `TauCeti.BraidWord.FreeCancelStep.alexander_seifertMatrix_eq` and
  `TauCeti.BraidWord.FreeCancelStep.tristramLevineSignature_seifertMatrix_eq`: the same for a free
  insertion or deletion step that keeps the set of levels in use.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 6
  (Seifert matrices) and Chapter 8 (S-equivalence: adding a tube to a Seifert surface enlarges its
  Seifert matrix).
-/

public section

namespace TauCeti

namespace BraidWord

open KnotTheory Matrix

variable {n : ℕ}

/-! ### Positions -/

/-- Position `k` of `u ++ v` is position `insShift u.length k` of `u ++ [x, y] ++ v`. -/
private def insShift (p k : ℕ) : ℕ := if k < p then k else k + 2

private theorem insShift_of_lt {p k : ℕ} (h : k < p) : insShift p k = k := by
  simp [insShift, h]

@[simp] private theorem insShift_lt_insShift {p a b : ℕ} :
    insShift p a < insShift p b ↔ a < b := by
  unfold insShift; split_ifs <;> omega

@[simp] private theorem insShift_inj {p a b : ℕ} : insShift p a = insShift p b ↔ a = b := by
  unfold insShift; split_ifs <;> omega

@[simp] private theorem insShift_ne_self (p a : ℕ) : insShift p a ≠ p := by
  unfold insShift; split_ifs <;> omega

@[simp] private theorem insShift_ne_succ (p a : ℕ) : insShift p a ≠ p + 1 := by
  unfold insShift; split_ifs <;> omega

@[simp] private theorem self_ne_insShift (p a : ℕ) : p ≠ insShift p a :=
  (insShift_ne_self p a).symm

@[simp] private theorem succ_ne_insShift (p a : ℕ) : p + 1 ≠ insShift p a :=
  (insShift_ne_succ p a).symm

@[simp] private theorem insShift_lt_iff {p a : ℕ} : insShift p a < p ↔ a < p := by
  unfold insShift; split_ifs <;> omega

@[simp] private theorem lt_insShift_iff {p a : ℕ} : p < insShift p a ↔ p ≤ a := by
  unfold insShift; split_ifs <;> omega

@[simp] private theorem succ_lt_insShift_iff {p a : ℕ} : p + 1 < insShift p a ↔ p ≤ a := by
  unfold insShift; split_ifs <;> omega

private theorem insShift_lt_succ_iff {p a : ℕ} : insShift p a < p + 1 ↔ a < p := by
  unfold insShift; split_ifs <;> omega

private theorem eq_or_eq_or_exists_insShift (p k : ℕ) :
    k = p ∨ k = p + 1 ∨ ∃ j, k = insShift p j := by
  rcases lt_or_ge k p with h | h
  · exact Or.inr (Or.inr ⟨k, (insShift_of_lt h).symm⟩)
  · rcases (show k = p ∨ k = p + 1 ∨ p + 2 ≤ k by omega) with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr ⟨k - 2, by unfold insShift; split_ifs <;> omega⟩)

section Insert

variable (u v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ)

private theorem getElem?_insert_insShift (k : ℕ) :
    (u ++ (i, ε) :: (i, -ε) :: v)[insShift u.length k]? = (u ++ v)[k]? := by
  unfold insShift
  split_ifs with h
  · rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
      show k + 2 - u.length = k - u.length + 1 + 1 by omega]
    simp

@[simp] private theorem levelAt_insert_insShift (k : ℕ) :
    (u ++ (i, ε) :: (i, -ε) :: v).levelAt (insShift u.length k) = (u ++ v).levelAt k := by
  rw [levelAt_def, levelAt_def, getElem?_insert_insShift]

@[simp] private theorem signAt_insert_insShift (k : ℕ) :
    (u ++ (i, ε) :: (i, -ε) :: v).signAt (insShift u.length k) = (u ++ v).signAt k := by
  rw [signAt_def, signAt_def, getElem?_insert_insShift]

private theorem levelAt_insert_length :
    (u ++ (i, ε) :: (i, -ε) :: v).levelAt u.length = some (i : ℕ) := by
  simp

private theorem levelAt_insert_length_succ :
    (u ++ (i, ε) :: (i, -ε) :: v).levelAt (u.length + 1) = some (i : ℕ) := by
  simp

private theorem signAt_insert_length :
    (u ++ (i, ε) :: (i, -ε) :: v).signAt u.length = ε := by
  simp

private theorem signAt_insert_length_succ :
    (u ++ (i, ε) :: (i, -ε) :: v).signAt (u.length + 1) = -(ε : ℤ) := by
  simp

private theorem insShift_lt_length_insert_iff (k : ℕ) :
    insShift u.length k < (u ++ (i, ε) :: (i, -ε) :: v).length ↔ k < (u ++ v).length := by
  rw [← levelAt_ne_none_iff, ← levelAt_ne_none_iff, levelAt_insert_insShift]

/-! ### Loops of the canonical Seifert surface after an insertion -/

/-- A loop of `u ++ v` keeps being a loop after the insertion, with its bands moved, unless it
runs on level `i` across the insertion point. -/
private theorem isSeifertLoop_insert_insShift_iff (c : ℕ × ℕ) :
    (u ++ (i, ε) :: (i, -ε) :: v).IsSeifertLoop (insShift u.length c.1, insShift u.length c.2) ↔
      (u ++ v).IsSeifertLoop c ∧
        ¬((u ++ v).levelAt c.1 = some (i : ℕ) ∧ c.1 < u.length ∧ u.length ≤ c.2) := by
  simp only [isSeifertLoop_iff, insShift_lt_insShift, levelAt_insert_insShift,
    insShift_lt_length_insert_iff]
  constructor
  · rintro ⟨h12, h2, hl, hb⟩
    refine ⟨⟨h12, h2, hl, fun k hk hk' ↦ ?_⟩, fun ⟨hi, h1, h2'⟩ ↦ ?_⟩
    · simpa using hb (insShift u.length k) (by simpa using hk) (by simpa using hk')
    · exact hb u.length (by simpa using h2') (by simpa using h1) (by simp [hi])
  · rintro ⟨⟨h12, h2, hl, hb⟩, hs⟩
    refine ⟨h12, h2, hl, fun k hk hk' ↦ ?_⟩
    rcases eq_or_eq_or_exists_insShift u.length k with rfl | rfl | ⟨j, rfl⟩
    · simp only [lt_insShift_iff, insShift_lt_iff] at hk hk'
      rw [levelAt_insert_length]
      exact fun h ↦ hs ⟨h.symm, hk', hk⟩
    · simp only [succ_lt_insShift_iff, insShift_lt_succ_iff] at hk hk'
      rw [levelAt_insert_length_succ]
      exact fun h ↦ hs ⟨h.symm, hk', hk⟩
    · simpa using hb j (by simpa using hk) (by simpa using hk')

/-- The two inserted bands span a loop. -/
private theorem isSeifertLoop_insert_mid :
    (u ++ (i, ε) :: (i, -ε) :: v).IsSeifertLoop (u.length, u.length + 1) :=
  (isSeifertLoop_iff _).2 ⟨by omega, by simp, by simp, fun k hk hk' ↦ by omega⟩

/-- The loop ending at the first inserted band. -/
private theorem isSeifertLoop_insert_left_iff {t : ℕ} (ht : t < u.length) :
    (u ++ (i, ε) :: (i, -ε) :: v).IsSeifertLoop (t, u.length) ↔
      (u ++ v).levelAt t = some (i : ℕ) ∧
        ∀ k, t < k → k < u.length → (u ++ v).levelAt k ≠ some (i : ℕ) := by
  have hlev : ∀ k < u.length, (u ++ (i, ε) :: (i, -ε) :: v).levelAt k = (u ++ v).levelAt k :=
    fun k hk ↦ by simpa [insShift_of_lt hk] using levelAt_insert_insShift u v i ε k
  simp only [isSeifertLoop_iff, levelAt_insert_length, hlev t ht]
  constructor
  · rintro ⟨-, -, hl, hb⟩
    exact ⟨hl.symm, fun k hk hk' ↦ by rw [← hlev k hk', hl]; exact hb k hk' hk⟩
  · rintro ⟨hl, hb⟩
    exact ⟨ht, by simp, hl.symm, fun k hk' hk ↦ by rw [hlev k hk', hl]; exact hb k hk hk'⟩

/-- The loop starting at the second inserted band. -/
private theorem isSeifertLoop_insert_right_iff {t : ℕ} (ht : u.length ≤ t) :
    (u ++ (i, ε) :: (i, -ε) :: v).IsSeifertLoop (u.length + 1, insShift u.length t) ↔
      t < (u ++ v).length ∧ (u ++ v).levelAt t = some (i : ℕ) ∧
        ∀ k, u.length ≤ k → k < t → (u ++ v).levelAt k ≠ some (i : ℕ) := by
  simp only [isSeifertLoop_iff, levelAt_insert_length_succ, levelAt_insert_insShift,
    insShift_lt_length_insert_iff, succ_lt_insShift_iff, ht, true_and]
  constructor
  · rintro ⟨h2, hl, hb⟩
    refine ⟨h2, hl, fun k hk hk' ↦ ?_⟩
    simpa using hb (insShift u.length k) (by simpa using hk') (by simpa using hk)
  · rintro ⟨h2, hl, hb⟩
    refine ⟨h2, hl, fun k hk hk' ↦ ?_⟩
    rcases eq_or_eq_or_exists_insShift u.length k with rfl | rfl | ⟨j, rfl⟩
    · omega
    · omega
    · simp only [insShift_lt_insShift, succ_lt_insShift_iff] at hk hk'
      simpa using hb j hk' hk

/-- Every loop after the insertion is a moved loop, the loop between the two inserted bands, or
a loop ending at the first or starting at the second inserted band. -/
private theorem IsSeifertLoop.insert_cases {z : ℕ × ℕ}
    (hz : (u ++ (i, ε) :: (i, -ε) :: v).IsSeifertLoop z) :
    z = (u.length, u.length + 1) ∨
      (∃ t, u.length ≤ t ∧ z = (u.length + 1, insShift u.length t)) ∨
      (∃ t < u.length, z = (t, u.length)) ∨
      ∃ c : ℕ × ℕ, z = (insShift u.length c.1, insShift u.length c.2) := by
  obtain ⟨h12, -, hl, hb⟩ := (isSeifertLoop_iff _).1 hz
  rcases eq_or_eq_or_exists_insShift u.length z.1 with h1 | h1 | ⟨j, h1⟩
  · exact Or.inl (hz.eq_of_fst_eq (isSeifertLoop_insert_mid u v i ε) h1)
  · rcases eq_or_eq_or_exists_insShift u.length z.2 with h2 | h2 | ⟨t, h2⟩
    · omega
    · omega
    · refine Or.inr (Or.inl ⟨t, ?_, Prod.ext h1 h2⟩)
      rw [h1, h2, succ_lt_insShift_iff] at h12
      exact h12
  · rcases eq_or_eq_or_exists_insShift u.length z.2 with h2 | h2 | ⟨t, h2⟩
    · rw [h1, h2, insShift_lt_iff] at h12
      exact Or.inr (Or.inr (Or.inl ⟨j, h12, Prod.ext (h1.trans (insShift_of_lt h12)) h2⟩))
    · rw [h1, h2, insShift_lt_succ_iff] at h12
      exfalso
      refine hb u.length (by omega) (by rw [h1, insShift_lt_iff]; exact h12) ?_
      rw [← hl, h2, levelAt_insert_length, levelAt_insert_length_succ]
    · exact Or.inr (Or.inr (Or.inr ⟨(j, t), Prod.ext h1 h2⟩))

/-! ### Entries of the Seifert matrix after an insertion -/

/-- Moving the bands of two loops past the insertion point keeps their entry. -/
private theorem seifertMatrix_insert_moved {a b : (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops}
    {c d : (u ++ v).seifertLoops} (ha : a.1 = (insShift u.length c.1.1, insShift u.length c.1.2))
    (hb : b.1 = (insShift u.length d.1.1, insShift u.length d.1.2)) :
    (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix a b = (u ++ v).seifertMatrix c d := by
  have hab : a = b ↔ c = d := by
    rw [Subtype.ext_iff, Subtype.ext_iff (a1 := c), ha, hb, Prod.ext_iff (x := c.1)]
    simp
  rw [seifertMatrix_apply, seifertMatrix_apply]
  simp only [hab]
  rw [ha, hb]
  simp only [levelAt_insert_insShift, signAt_insert_insShift, insShift_lt_insShift, insShift_inj]

/-- The row of the loop between the two inserted bands. -/
private theorem seifertMatrix_insert_mid_apply {β z : (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops}
    (hβ : β.1 = (u.length, u.length + 1)) (hz : z ≠ β) :
    (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix β z =
      if u.length + 1 = z.1.1 then (if (ε : ℤ) = 1 then -1 else 0)
      else if z.1.2 = u.length then (if (ε : ℤ) = 1 then 1 else 0) else 0 := by
  obtain ⟨⟨z₁, z₂⟩, hzmem⟩ := z
  obtain ⟨h12, -, hl, -⟩ := (isSeifertLoop_iff _).1 ((mem_seifertLoops _).1 hzmem)
  simp only at h12 hl ⊢
  rw [seifertMatrix_apply, hβ]
  simp only [Ne.symm hz, ite_false, levelAt_insert_length, signAt_insert_length,
    signAt_insert_length_succ]
  by_cases hi : some (i : ℕ) = (u ++ (i, ε) :: (i, -ε) :: v).levelAt z₁
  · simp [hi]
  · have h1 : u.length + 1 ≠ z₁ := fun h ↦ hi (by rw [← h, levelAt_insert_length_succ])
    have h2 : z₂ ≠ u.length := fun h ↦ hi (by rw [← hl, h, levelAt_insert_length])
    simp only [hi, h1, h2, ite_false]
    split_ifs <;> first | rfl | omega

/-- The column of the loop between the two inserted bands. -/
private theorem seifertMatrix_insert_apply_mid {β z : (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops}
    (hβ : β.1 = (u.length, u.length + 1)) (hz : z ≠ β) :
    (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix z β =
      if z.1.2 = u.length then (if (ε : ℤ) = -1 then -1 else 0)
      else if u.length + 1 = z.1.1 then (if (ε : ℤ) = -1 then 1 else 0) else 0 := by
  obtain ⟨⟨z₁, z₂⟩, hzmem⟩ := z
  obtain ⟨h12, -, hl, -⟩ := (isSeifertLoop_iff _).1 ((mem_seifertLoops _).1 hzmem)
  simp only at h12 hl ⊢
  rw [seifertMatrix_apply, hβ]
  simp only [hz, ite_false, levelAt_insert_length]
  by_cases hi : (u ++ (i, ε) :: (i, -ε) :: v).levelAt z₁ = some (i : ℕ)
  · simp only [hi, ite_true]
    by_cases h2 : z₂ = u.length
    · subst h2
      simp
    · by_cases h1 : u.length + 1 = z₁
      · subst h1
        simp [h2, neg_eq_iff_eq_neg]
      · simp [h1, h2]
  · have h1 : u.length + 1 ≠ z₁ := fun h ↦ hi (by rw [← h, levelAt_insert_length_succ])
    have h2 : z₂ ≠ u.length := fun h ↦ hi (by rw [← hl, h, levelAt_insert_length])
    simp only [hi, h1, h2, ite_false]
    split_ifs <;> first | rfl | omega

section Crossing

/-! The loop `γ = (t₀, t₁)` of level `i` running across the insertion point is cut by the two new
bands into the loops `α = (t₀, p)`, `(p, p + 1)` and `δ = (p + 1, t₁)` (positions after the
insertion). As a class on the new surface, `γ` is their sum, and the entries below say that this
sum links every moved loop as `γ` did. -/

variable {γ : (u ++ v).seifertLoops} (hγi : (u ++ v).levelAt γ.1.1 = some (i : ℕ))
  (hγ₁ : γ.1.1 < u.length) (hγ₂ : u.length ≤ γ.1.2)
  {α δ : (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops}
include hγi hγ₁ hγ₂

/-- The two cut pieces of `γ` other than the middle loop link a moved loop as `γ` did. -/
private theorem seifertMatrix_insert_cut_add (hα : α.1 = (insShift u.length γ.1.1, u.length))
    (hδ : δ.1 = (u.length + 1, insShift u.length γ.1.2)) {d : (u ++ v).seifertLoops} (hd : d ≠ γ)
    {z : (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops}
    (hz : z.1 = (insShift u.length d.1.1, insShift u.length d.1.2)) :
    (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix α z +
        (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix δ z = (u ++ v).seifertMatrix γ d := by
  have hαz : α ≠ z := fun h ↦ by
    have := congrArg Prod.snd (hα.symm.trans ((congrArg Subtype.val h).trans hz))
    simp at this
  have hδz : δ ≠ z := fun h ↦ by
    have := congrArg Prod.fst (hδ.symm.trans ((congrArg Subtype.val h).trans hz))
    simp at this
  obtain ⟨⟨t₀, t₁⟩, hγmem⟩ := γ
  obtain ⟨⟨d₁, d₂⟩, hdmem⟩ := d
  obtain ⟨hγ12, hγ2, hγl, -⟩ := (isSeifertLoop_iff _).1 ((mem_seifertLoops _).1 hγmem)
  obtain ⟨hd12, hd2, hdl, -⟩ := (isSeifertLoop_iff _).1 ((mem_seifertLoops _).1 hdmem)
  simp only at hγi hγ₁ hγ₂ hα hδ hz hγ12 hγ2 hγl hd12 hd2 hdl
  have hγd : ¬(t₀ = d₁ ∧ t₁ = d₂) := fun h ↦ hd (by simp [h.1, h.2])
  obtain ⟨l, hl⟩ : ∃ l, (u ++ v).levelAt d₁ = some l :=
    Option.ne_none_iff_exists'.1 ((levelAt_ne_none_iff _).2 (hd12.trans hd2))
  have hne₁ : l ≠ i → d₁ ≠ t₀ ∧ d₁ ≠ t₁ ∧ d₂ ≠ t₀ ∧ d₂ ≠ t₁ := fun hli ↦ by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> simp_all
  rw [seifertMatrix_apply, seifertMatrix_apply, seifertMatrix_apply]
  simp only [hαz, hδz, Subtype.mk.injEq, Prod.mk.injEq, hγd, ite_false, hα, hδ, hz,
    levelAt_insert_insShift, levelAt_insert_length_succ, signAt_insert_insShift, hγi, hl,
    Option.map_some, Option.some_inj, insShift_lt_insShift, insShift_inj, insShift_lt_iff,
    lt_insShift_iff, succ_lt_insShift_iff, insShift_lt_succ_iff, self_ne_insShift,
    insShift_ne_succ]
  by_cases hli : (i : ℕ) = l
  · simp only [hli, ite_true]
    split_ifs <;> omega
  · obtain ⟨h1, h2, h3, h4⟩ := hne₁ (Ne.symm hli)
    simp only [hli, ite_false]
    split_ifs <;> omega

/-- A moved loop links the two cut pieces of `γ` other than the middle loop as it linked `γ`. -/
private theorem seifertMatrix_insert_add_cut (hα : α.1 = (insShift u.length γ.1.1, u.length))
    (hδ : δ.1 = (u.length + 1, insShift u.length γ.1.2)) {d : (u ++ v).seifertLoops} (hd : d ≠ γ)
    {z : (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops}
    (hz : z.1 = (insShift u.length d.1.1, insShift u.length d.1.2)) :
    (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix z α +
        (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix z δ = (u ++ v).seifertMatrix d γ := by
  have hαz : z ≠ α := fun h ↦ by
    have := congrArg Prod.snd (hα.symm.trans ((congrArg Subtype.val h.symm).trans hz))
    simp at this
  have hδz : z ≠ δ := fun h ↦ by
    have := congrArg Prod.fst (hδ.symm.trans ((congrArg Subtype.val h.symm).trans hz))
    simp at this
  obtain ⟨⟨t₀, t₁⟩, hγmem⟩ := γ
  obtain ⟨⟨d₁, d₂⟩, hdmem⟩ := d
  obtain ⟨hγ12, hγ2, hγl, -⟩ := (isSeifertLoop_iff _).1 ((mem_seifertLoops _).1 hγmem)
  obtain ⟨hd12, hd2, hdl, -⟩ := (isSeifertLoop_iff _).1 ((mem_seifertLoops _).1 hdmem)
  simp only at hγi hγ₁ hγ₂ hα hδ hz hγ12 hγ2 hγl hd12 hd2 hdl
  have hγd : ¬(d₁ = t₀ ∧ d₂ = t₁) := fun h ↦ hd (by simp [h.1, h.2])
  obtain ⟨l, hl⟩ : ∃ l, (u ++ v).levelAt d₁ = some l :=
    Option.ne_none_iff_exists'.1 ((levelAt_ne_none_iff _).2 (hd12.trans hd2))
  have hne₁ : l ≠ i → d₁ ≠ t₀ ∧ d₁ ≠ t₁ ∧ d₂ ≠ t₀ ∧ d₂ ≠ t₁ := fun hli ↦ by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> simp_all
  rw [seifertMatrix_apply, seifertMatrix_apply, seifertMatrix_apply]
  simp only [hαz, hδz, Subtype.mk.injEq, Prod.mk.injEq, hγd, ite_false, hα, hδ, hz,
    levelAt_insert_insShift, levelAt_insert_length_succ, 
    signAt_insert_insShift, hγi, hl, Option.map_some, Option.some_inj, insShift_lt_insShift,
    insShift_inj, insShift_lt_iff, lt_insShift_iff, succ_lt_insShift_iff, insShift_lt_succ_iff,
    self_ne_insShift, insShift_ne_succ]
  by_cases hli : l = (i : ℕ)
  · simp only [hli, ite_true]
    split_ifs <;> omega
  · obtain ⟨h1, h2, h3, h4⟩ := hne₁ hli
    simp only [hli, ite_false]
    split_ifs <;> omega

/-- The three cut pieces of `γ` together link themselves as `γ` linked itself. -/
private theorem seifertMatrix_insert_cut_cut (hα : α.1 = (insShift u.length γ.1.1, u.length))
    (hδ : δ.1 = (u.length + 1, insShift u.length γ.1.2))
    {β : (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops} (hβ : β.1 = (u.length, u.length + 1)) :
    (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix α α +
      (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix α β +
      (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix α δ +
      (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix β α +
      (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix β β +
      (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix β δ +
      (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix δ α +
      (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix δ β +
      (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix δ δ = (u ++ v).seifertMatrix γ γ := by
  have hne : ∀ {x y : (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops}, x.1.2 ≠ y.1.2 → x ≠ y :=
    fun h h' ↦ h (by rw [h'])
  have hαβ : α ≠ β := hne (by rw [hα, hβ]; simp)
  have hδβ : δ ≠ β := hne (by rw [hδ, hβ]; simp)
  have hαδ : α ≠ δ := hne (by rw [hα, hδ]; simp)
  rw [seifertMatrix_insert_mid_apply u v i ε hβ hαβ, seifertMatrix_insert_mid_apply u v i ε hβ hδβ,
    seifertMatrix_insert_apply_mid u v i ε hβ hαβ, seifertMatrix_insert_apply_mid u v i ε hβ hδβ,
    seifertMatrix_apply _ α δ, seifertMatrix_apply _ δ α, seifertMatrix_apply_self,
    seifertMatrix_apply_self, seifertMatrix_apply_self, seifertMatrix_apply_self]
  obtain ⟨⟨t₀, t₁⟩, hγmem⟩ := γ
  obtain ⟨hγ12, hγ2, hγl, -⟩ := (isSeifertLoop_iff _).1 ((mem_seifertLoops _).1 hγmem)
  simp only at hγi hγ₁ hγ₂ hα hδ hγ12 hγ2 hγl
  simp only [hαδ, Ne.symm hαδ, ite_false, hα, hβ, hδ, levelAt_insert_insShift,
    levelAt_insert_length_succ, signAt_insert_insShift,
    signAt_insert_length, signAt_insert_length_succ, hγi, insShift_inj, 
    succ_ne_insShift, insShift_ne_self, ite_true]
  rcases signAt_eq_one_or_eq_neg_one (u ++ v) (hγ12.trans hγ2) with h₀ | h₀ <;>
    rcases signAt_eq_one_or_eq_neg_one (u ++ v) hγ2 with h₁ | h₁ <;>
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [h₀, h₁] <;> omega

end Crossing

/-! ### Matching the loops before and after the insertion -/

/-- Where a loop of `u ++ v` goes after the insertion: a loop of level `i` across the insertion
point is cut short at the first inserted band, and every other loop just has its bands moved. -/
private def insertLoop (c : ℕ × ℕ) : ℕ × ℕ :=
  if (u ++ v).levelAt c.1 = some (i : ℕ) ∧ c.1 < u.length ∧ u.length ≤ c.2 then (c.1, u.length)
  else (insShift u.length c.1, insShift u.length c.2)

private theorem insertLoop_of_not {c : ℕ × ℕ}
    (h : ¬((u ++ v).levelAt c.1 = some (i : ℕ) ∧ c.1 < u.length ∧ u.length ≤ c.2)) :
    insertLoop u v i c = (insShift u.length c.1, insShift u.length c.2) :=
  ite_eq_right h

private theorem insertLoop_fst (c : ℕ × ℕ) :
    (insertLoop u v i c).1 = insShift u.length c.1 := by
  unfold insertLoop
  split_ifs with h
  · exact (insShift_of_lt h.2.1).symm
  · rfl

private theorem isSeifertLoop_insertLoop {c : ℕ × ℕ} (hc : (u ++ v).IsSeifertLoop c) :
    (u ++ (i, ε) :: (i, -ε) :: v).IsSeifertLoop (insertLoop u v i c) := by
  unfold insertLoop
  split_ifs with h
  · obtain ⟨-, -, hl, hb⟩ := (isSeifertLoop_iff _).1 hc
    refine (isSeifertLoop_insert_left_iff u v i ε h.2.1).2 ⟨h.1, fun k hk hk' ↦ ?_⟩
    rw [← h.1]
    exact hb k (by omega) hk
  · exact (isSeifertLoop_insert_insShift_iff u v i ε c).2 ⟨hc, h⟩

/-- At most one loop of level `i` runs across the insertion point. -/
private theorem eq_of_straddle {c d : ℕ × ℕ} (hc : (u ++ v).IsSeifertLoop c)
    (hd : (u ++ v).IsSeifertLoop d)
    (hc' : (u ++ v).levelAt c.1 = some (i : ℕ) ∧ c.1 < u.length ∧ u.length ≤ c.2)
    (hd' : (u ++ v).levelAt d.1 = some (i : ℕ) ∧ d.1 < u.length ∧ u.length ≤ d.2) : c = d := by
  refine hc.eq_of_fst_eq hd ?_
  obtain ⟨-, -, -, hcb⟩ := (isSeifertLoop_iff _).1 hc
  obtain ⟨-, -, -, hdb⟩ := (isSeifertLoop_iff _).1 hd
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact hcb d.1 (by omega) h (by rw [hc'.1, hd'.1])
  · exact hdb c.1 (by omega) h (by rw [hc'.1, hd'.1])

/-- The loops of `u ++ v`, followed by the two loops `a` and `(p, p + 1)`, are the loops after the
insertion, provided `a` is the one loop after the insertion that is not of the form
`insertLoop c` or `(p, p + 1)`. -/
private theorem bijective_insertLoop {a β : (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops}
    (hβ : β.1 = (u.length, u.length + 1))
    (haF : ∀ c, (u ++ v).IsSeifertLoop c → insertLoop u v i c ≠ a.1) (haβ : a ≠ β)
    (hcover : ∀ z, (u ++ (i, ε) :: (i, -ε) :: v).IsSeifertLoop z → z ≠ (u.length, u.length + 1) →
      (∀ c, (u ++ v).IsSeifertLoop c → insertLoop u v i c ≠ z) → z = a.1) :
    Function.Bijective (Sum.elim
      (fun c : (u ++ v).seifertLoops ↦ (⟨insertLoop u v i c.1, (mem_seifertLoops _).2
        (isSeifertLoop_insertLoop u v i ε ((mem_seifertLoops _).1 c.2))⟩ :
          (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops))
      ![a, β]) := by
  have hcβ : ∀ c, insertLoop u v i c ≠ β.1 := fun c h ↦ by
    simpa [hβ, insertLoop_fst] using congrArg Prod.fst h
  refine ⟨?_, fun z ↦ ?_⟩
  · rintro (c | x) (d | y) h
    · have h₁ := congrArg (fun z : (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops ↦ z.1.1) h
      simp only [Sum.elim_inl, insertLoop_fst, insShift_inj] at h₁
      exact congrArg Sum.inl (Subtype.ext (((mem_seifertLoops _).1 c.2).eq_of_fst_eq
        ((mem_seifertLoops _).1 d.2) h₁))
    · fin_cases y
      · exact absurd (congrArg Subtype.val h) (haF _ ((mem_seifertLoops _).1 c.2))
      · exact absurd (congrArg Subtype.val h) (hcβ _)
    · fin_cases x
      · exact absurd (congrArg Subtype.val h).symm (haF _ ((mem_seifertLoops _).1 d.2))
      · exact absurd (congrArg Subtype.val h).symm (hcβ _)
    · fin_cases x <;> fin_cases y
      · rfl
      · exact absurd h haβ
      · exact absurd h.symm haβ
      · rfl
  · by_cases hzβ : z = β
    · exact ⟨.inr 1, by simp [hzβ]⟩
    by_cases hzF : ∃ c, (u ++ v).IsSeifertLoop c ∧ insertLoop u v i c = z.1
    · obtain ⟨c, hc, hcz⟩ := hzF
      exact ⟨.inl ⟨c, (mem_seifertLoops _).2 hc⟩, Subtype.ext hcz⟩
    · refine ⟨.inr 0, Subtype.ext (hcover z.1 ((mem_seifertLoops _).1 z.2) ?_ ?_).symm⟩
      · exact fun h ↦ hzβ (Subtype.ext (h.trans hβ.symm))
      · exact fun c hc h ↦ hzF ⟨c, hc, h⟩

/-- A loop away from the insertion point does not meet the loop between the two inserted bands. -/
private theorem seifertMatrix_insert_mid_insertLoop
    {β z : (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops} (hβ : β.1 = (u.length, u.length + 1))
    {c : ℕ × ℕ}
    (hc : ¬((u ++ v).levelAt c.1 = some (i : ℕ) ∧ c.1 < u.length ∧ u.length ≤ c.2))
    (hz : z.1 = insertLoop u v i c) :
    (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix β z = 0 ∧
      (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix z β = 0 := by
  rw [insertLoop_of_not u v i hc] at hz
  have hzβ : z ≠ β := fun h ↦ by simpa [hz, hβ] using congrArg (fun z ↦ z.1.1) h
  rw [seifertMatrix_insert_mid_apply u v i ε hβ hzβ, seifertMatrix_insert_apply_mid u v i ε hβ hzβ,
    hz]
  simp

end Insert

/-! ### Assembling the congruence -/

section Assemble

variable (u v : BraidWord n) (i : Fin (n - 1)) (ε : ℤˣ)

/-- The loop between the two inserted bands has self-linking zero: its bands have opposite
signs. -/
private theorem seifertMatrix_insert_mid_self {β : (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops}
    (hβ : β.1 = (u.length, u.length + 1)) :
    (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix β β = 0 := by
  rw [seifertMatrix_apply_self, hβ]
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

/-- If no loop of level `i` runs across the insertion point, the matched loops already have the
Seifert matrix of `u ++ v`, and the two new loops meet only each other. -/
private theorem exists_insert_congr_of_not_straddle
    (hno : ∀ c, (u ++ v).IsSeifertLoop c →
      ¬((u ++ v).levelAt c.1 = some (i : ℕ) ∧ c.1 < u.length ∧ u.length ≤ c.2))
    (G : (u ++ v).seifertLoops ⊕ Fin 2 ≃ (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops)
    (hGl : ∀ c, (G (.inl c)).1 = insertLoop u v i c.1)
    (hG1 : (G (.inr 1)).1 = (u.length, u.length + 1)) {s : ℤˣ}
    (hrow : (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix (G (.inr 1)) (G (.inr 0)) =
      if (ε : ℤ) = 1 then (s : ℤ) else 0)
    (hcol : (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix (G (.inr 0)) (G (.inr 1)) =
      if (ε : ℤ) = 1 then 0 else (s : ℤ)) :
    ∃ T : Matrix ((u ++ v).seifertLoops ⊕ Fin 2) ((u ++ v).seifertLoops ⊕ Fin 2) ℤ,
      IsUnit T.det ∧
      (T * (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix.submatrix G G * Tᵀ).toBlocks₁₁ =
        (u ++ v).seifertMatrix ∧
      (T * (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix.submatrix G G * Tᵀ) (.inr 1) =
        Pi.single (.inr 0) (if (ε : ℤ) = 1 then (s : ℤ) else 0) ∧
      (T * (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix.submatrix G G * Tᵀ).col (.inr 1) =
        Pi.single (.inr 0) (if (ε : ℤ) = 1 then 0 else (s : ℤ)) := by
  have hno' := fun c : (u ++ v).seifertLoops ↦ hno c.1 ((mem_seifertLoops _).1 c.2)
  refine ⟨1, by simp, ?_, ?_, ?_⟩ <;> simp only [Matrix.one_mul, transpose_one, Matrix.mul_one]
  · ext c d
    simp only [toBlocks₁₁, of_apply, submatrix_apply]
    exact seifertMatrix_insert_moved u v i ε (by rw [hGl, insertLoop_of_not u v i (hno' c)])
      (by rw [hGl, insertLoop_of_not u v i (hno' d)])
  · ext (d | k)
    · simpa using (seifertMatrix_insert_mid_insertLoop u v i ε hG1 (hno' d) (hGl d)).1
    · fin_cases k
      · simpa using hrow
      · simpa using seifertMatrix_insert_mid_self u v i ε hG1
  · ext (d | k)
    · simpa using (seifertMatrix_insert_mid_insertLoop u v i ε hG1 (hno' d) (hGl d)).2
    · fin_cases k
      · simpa using hcol
      · simpa using seifertMatrix_insert_mid_self u v i ε hG1

/-- If the loop `γ` of level `i` runs across the insertion point, replacing its cut-short image
`α` by `α + δ + β`, the sum of its three pieces, gives back the Seifert matrix of `u ++ v`, and the
two new loops `δ` and `β` meet only each other. -/
private theorem exists_insert_congr_of_straddle {γ : (u ++ v).seifertLoops}
    (hγ : (u ++ v).levelAt γ.1.1 = some (i : ℕ) ∧ γ.1.1 < u.length ∧ u.length ≤ γ.1.2)
    (G : (u ++ v).seifertLoops ⊕ Fin 2 ≃ (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops)
    (hGl : ∀ c, (G (.inl c)).1 = insertLoop u v i c.1)
    (hG0 : (G (.inr 0)).1 = (u.length + 1, insShift u.length γ.1.2))
    (hG1 : (G (.inr 1)).1 = (u.length, u.length + 1)) :
    ∃ T : Matrix ((u ++ v).seifertLoops ⊕ Fin 2) ((u ++ v).seifertLoops ⊕ Fin 2) ℤ,
      IsUnit T.det ∧
      (T * (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix.submatrix G G * Tᵀ).toBlocks₁₁ =
        (u ++ v).seifertMatrix ∧
      (T * (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix.submatrix G G * Tᵀ) (.inr 1) =
        Pi.single (.inr 0) (if (ε : ℤ) = 1 then -(ε : ℤ) else 0) ∧
      (T * (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix.submatrix G G * Tᵀ).col (.inr 1) =
        Pi.single (.inr 0) (if (ε : ℤ) = 1 then 0 else -(ε : ℤ)) := by
  have hα : (G (.inl γ)).1 = (insShift u.length γ.1.1, u.length) := by
    rw [hGl, insertLoop, ite_eq_left hγ, insShift_of_lt hγ.2.1]
  have hGd : ∀ d, d ≠ γ → (G (.inl d)).1 = (insShift u.length d.1.1, insShift u.length d.1.2) :=
    fun d hd ↦ by
      rw [hGl, insertLoop_of_not u v i fun h ↦ hd (Subtype.ext (eq_of_straddle u v i
        ((mem_seifertLoops _).1 d.2) ((mem_seifertLoops _).1 γ.2) h hγ))]
  have hnd : ∀ d, d ≠ γ →
      ¬((u ++ v).levelAt d.1.1 = some (i : ℕ) ∧ d.1.1 < u.length ∧ u.length ≤ d.1.2) :=
    fun d hd h ↦ hd (Subtype.ext (eq_of_straddle u v i ((mem_seifertLoops _).1 d.2)
      ((mem_seifertLoops _).1 γ.2) h hγ))
  have hne : ∀ {x y : (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops}, x.1.2 ≠ y.1.2 → x ≠ y :=
    fun h h' ↦ h (by rw [h'])
  have hαβ : G (.inl γ) ≠ G (.inr 1) := hne (by rw [hα, hG1]; simp)
  have hδβ : G (.inr 0) ≠ G (.inr 1) := hne (by rw [hG0, hG1]; simp)
  have hmid : ∀ d, d ≠ γ → _ := fun d hd ↦
    seifertMatrix_insert_mid_insertLoop u v i ε hG1 (hnd d hd) (hGl d)
  refine ⟨1 + vecMulVec (Pi.single (.inl γ) 1) (Pi.single (.inr 0) 1 + Pi.single (.inr 1) 1),
    by
      rw [det_one_add_vecMulVec_single_add_single (by simp) (by simp)]
      exact isUnit_one, ?_, ?_, ?_⟩
  -- the old block: entries involving `γ` add up over its three pieces, the others are moved
  · ext c d
    simp only [toBlocks₁₁, of_apply, one_add_vecMulVec_single_add_single_mul_mul_transpose_apply,
      submatrix_apply, Sum.inl.injEq]
    by_cases hc : c = γ <;> by_cases hd : d = γ
    · subst hc hd
      simp only [and_self, ite_true]
      linear_combination seifertMatrix_insert_cut_cut u v i ε hγ.1 hγ.2.1 hγ.2.2 hα hG0 hG1
    · subst hc
      simp only [hd, and_false, ite_true, ite_false, add_zero]
      linear_combination seifertMatrix_insert_cut_add u v i ε hγ.1 hγ.2.1 hγ.2.2 hα hG0 hd
        (hGd d hd) + (hmid d hd).1
    · subst hd
      simp only [hc, false_and, ite_true, ite_false, add_zero]
      linear_combination seifertMatrix_insert_add_cut u v i ε hγ.1 hγ.2.1 hγ.2.2 hα hG0 hc
        (hGd c hc) + (hmid c hc).2
    · simp only [hc, hd, false_and, ite_false, add_zero]
      exact seifertMatrix_insert_moved u v i ε (hGd c hc) (hGd d hd)
  -- the row of `β`: it meets the two pieces of `γ` next to it with opposite signs
  · ext (d | k)
    · simp only [one_add_vecMulVec_single_add_single_mul_mul_transpose_apply, submatrix_apply,
        reduceCtorEq, false_and, ite_false, add_zero, Sum.inl.injEq]
      by_cases hd : d = γ
      · subst hd
        rw [seifertMatrix_insert_mid_apply u v i ε hG1 hαβ,
          seifertMatrix_insert_mid_apply u v i ε hG1 hδβ, seifertMatrix_insert_mid_self u v i ε hG1,
          hα, hG0]
        rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
      · simp [hd, (hmid d hd).1]
    · fin_cases k
      · simp only [Fin.zero_eta, one_add_vecMulVec_single_add_single_mul_mul_transpose_apply,
          submatrix_apply, reduceCtorEq, false_and, ite_false, add_zero]
        rw [seifertMatrix_insert_mid_apply u v i ε hG1 hδβ, hG0]
        rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
      · simp only [Fin.mk_one, one_add_vecMulVec_single_add_single_mul_mul_transpose_apply,
          submatrix_apply, reduceCtorEq, and_false, ite_false, add_zero,
          seifertMatrix_insert_mid_self u v i ε hG1]
        simp
  -- the column of `β`, likewise
  · ext (d | k)
    · simp only [col_apply, one_add_vecMulVec_single_add_single_mul_mul_transpose_apply,
        submatrix_apply, reduceCtorEq, and_false, ite_false, add_zero, Sum.inl.injEq]
      by_cases hd : d = γ
      · subst hd
        rw [seifertMatrix_insert_apply_mid u v i ε hG1 hαβ,
          seifertMatrix_insert_apply_mid u v i ε hG1 hδβ, seifertMatrix_insert_mid_self u v i ε hG1,
          hα, hG0]
        rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
      · simp [hd, (hmid d hd).2]
    · fin_cases k
      · simp only [Fin.zero_eta, col_apply,
          one_add_vecMulVec_single_add_single_mul_mul_transpose_apply,
          submatrix_apply, reduceCtorEq, and_false, ite_false, add_zero]
        rw [seifertMatrix_insert_apply_mid u v i ε hG1 hδβ, hG0]
        rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
      · simp only [Fin.mk_one, col_apply,
          one_add_vecMulVec_single_add_single_mul_mul_transpose_apply, submatrix_apply,
          reduceCtorEq, and_false, ite_false, add_zero,
          seifertMatrix_insert_mid_self u v i ε hG1]
        simp

/-- The outcome of the comparison for one insertion: after matching the loops by `G` and changing
basis by `T`, the matrix restricts to the Seifert matrix of `u ++ v` and the new loop `inr 1`
pairs only with `inr 0`, by a unit `s`, on the side fixed by the sign `ε`. -/
private def InsertCongruence : Prop :=
  ∃ (G : (u ++ v).seifertLoops ⊕ Fin 2 ≃ (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops)
    (T : Matrix ((u ++ v).seifertLoops ⊕ Fin 2) ((u ++ v).seifertLoops ⊕ Fin 2) ℤ) (s : ℤˣ),
    IsUnit T.det ∧
    (T * (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix.submatrix G G * Tᵀ).toBlocks₁₁ =
      (u ++ v).seifertMatrix ∧
    (T * (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix.submatrix G G * Tᵀ) (.inr 1) =
      Pi.single (.inr 0) (if (ε : ℤ) = 1 then (s : ℤ) else 0) ∧
    (T * (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix.submatrix G G * Tᵀ).col (.inr 1) =
      Pi.single (.inr 0) (if (ε : ℤ) = 1 then 0 else (s : ℤ))

/-- A loop of level `i` across the insertion point. -/
private theorem insertCongruence_of_straddle {γ : ℕ × ℕ} (hγ : (u ++ v).IsSeifertLoop γ)
    (hγs : (u ++ v).levelAt γ.1 = some (i : ℕ) ∧ γ.1 < u.length ∧ u.length ≤ γ.2) :
    InsertCongruence u v i ε := by
  obtain ⟨-, h2, hl, hb⟩ := (isSeifertLoop_iff _).1 hγ
  have hδ := (isSeifertLoop_insert_right_iff u v i ε hγs.2.2).2
    ⟨h2, by rw [hl, hγs.1], fun k hk hk' ↦ by rw [← hγs.1]; exact hb k hk' (by omega)⟩
  have hbij := bijective_insertLoop u v i ε (a := ⟨_, (mem_seifertLoops _).2 hδ⟩)
    (β := ⟨_, (mem_seifertLoops _).2 (isSeifertLoop_insert_mid u v i ε)⟩) rfl
    (fun c _ h ↦ by simpa [insertLoop_fst] using congrArg Prod.fst h)
    (fun h ↦ by simpa using congrArg (fun z ↦ z.1.1) h) fun z hz hzβ hzF ↦ ?_
  · obtain ⟨T, hT, h₁, h₂, h₃⟩ := exists_insert_congr_of_straddle u v i ε
      (γ := ⟨γ, (mem_seifertLoops _).2 hγ⟩) hγs (Equiv.ofBijective _ hbij) (fun _ ↦ rfl) rfl rfl
    exact ⟨_, T, -ε, hT, h₁, by simpa using h₂, by simpa using h₃⟩
  rcases IsSeifertLoop.insert_cases u v i ε hz with h | ⟨t, -, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨c, rfl⟩
  · exact absurd h hzβ
  · exact hz.eq_of_fst_eq hδ rfl
  · -- a loop ending at the first inserted band starts at the first band of `γ`
    obtain ⟨htl, htb⟩ := (isSeifertLoop_insert_left_iff u v i ε ht).1 hz
    refine absurd ?_ (hzF γ hγ)
    rw [insertLoop, ite_eq_left hγs]
    refine Prod.ext ?_ rfl
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hb t (by omega) h (by rw [htl, hγs.1])
    · exact htb γ.1 h hγs.2.1 hγs.1
  · obtain ⟨hc, hcs⟩ := (isSeifertLoop_insert_insShift_iff u v i ε c).1 hz
    exact absurd (insertLoop_of_not u v i hcs) (hzF c hc)

/-- No loop of level `i` across the insertion point, but a letter of level `i` after it. -/
private theorem insertCongruence_of_right
    (hno : ∀ c, (u ++ v).IsSeifertLoop c →
      ¬((u ++ v).levelAt c.1 = some (i : ℕ) ∧ c.1 < u.length ∧ u.length ≤ c.2))
    (hright : ∃ t, u.length ≤ t ∧ (u ++ v).levelAt t = some (i : ℕ)) :
    InsertCongruence u v i ε := by
  classical
  obtain ⟨ht₁p, ht₁⟩ := Nat.find_spec hright
  have hmin : ∀ k, u.length ≤ k → k < Nat.find hright → (u ++ v).levelAt k ≠ some (i : ℕ) :=
    fun k hk hk' h ↦ Nat.find_min hright hk' ⟨hk, h⟩
  have ht₁len : Nat.find hright < (u ++ v).length := by
    rw [← levelAt_ne_none_iff, ht₁]
    exact Option.some_ne_none _
  have hδ := (isSeifertLoop_insert_right_iff u v i ε ht₁p).2 ⟨ht₁len, ht₁, hmin⟩
  have hβ := isSeifertLoop_insert_mid u v i ε
  have hbij := bijective_insertLoop u v i ε (a := ⟨_, (mem_seifertLoops _).2 hδ⟩)
    (β := ⟨_, (mem_seifertLoops _).2 hβ⟩) rfl
    (fun c _ h ↦ by simpa [insertLoop_fst] using congrArg Prod.fst h)
    (fun h ↦ by simpa using congrArg (fun z ↦ z.1.1) h) fun z hz hzβ hzF ↦ ?_
  · have hδβ : (⟨_, (mem_seifertLoops _).2 hδ⟩ : (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops) ≠
        ⟨_, (mem_seifertLoops _).2 hβ⟩ := fun h ↦ by simpa using congrArg (fun z ↦ z.1.1) h
    have e₀ : Equiv.ofBijective _ hbij (.inr 0) = ⟨_, (mem_seifertLoops _).2 hδ⟩ := rfl
    have e₁ : Equiv.ofBijective _ hbij (.inr 1) = ⟨_, (mem_seifertLoops _).2 hβ⟩ := rfl
    obtain ⟨T, hT, h₁, h₂, h₃⟩ := exists_insert_congr_of_not_straddle u v i ε hno
      (Equiv.ofBijective _ hbij) (fun _ ↦ rfl) rfl (s := -ε)
      (by rw [e₀, e₁, seifertMatrix_insert_mid_apply u v i ε rfl hδβ]
          rcases Int.units_eq_one_or ε with rfl | rfl <;> simp)
      (by rw [e₀, e₁, seifertMatrix_insert_apply_mid u v i ε rfl hδβ]
          rcases Int.units_eq_one_or ε with rfl | rfl <;> simp)
    exact ⟨_, T, _, hT, h₁, h₂, h₃⟩
  rcases IsSeifertLoop.insert_cases u v i ε hz with h | ⟨t, -, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨c, rfl⟩
  · exact absurd h hzβ
  · exact hz.eq_of_fst_eq hδ rfl
  · -- such a loop would come from a loop of level `i` across the insertion point
    obtain ⟨htl, htb⟩ := (isSeifertLoop_insert_left_iff u v i ε ht).1 hz
    refine absurd ⟨htl, ht, ht₁p⟩ (hno (t, Nat.find hright) ((isSeifertLoop_iff _).2
      ⟨by omega, ht₁len, by rw [ht₁, htl], fun k hk hk' ↦ ?_⟩))
    rw [htl]
    rcases lt_or_ge k u.length with hkp | hkp
    · exact htb k hk' hkp
    · exact hmin k hkp hk
  · obtain ⟨hc, hcs⟩ := (isSeifertLoop_insert_insShift_iff u v i ε c).1 hz
    exact absurd (insertLoop_of_not u v i hcs) (hzF c hc)

/-- Every letter of level `i` lies before the insertion point. -/
private theorem insertCongruence_of_left
    (hno : ∀ c, (u ++ v).IsSeifertLoop c →
      ¬((u ++ v).levelAt c.1 = some (i : ℕ) ∧ c.1 < u.length ∧ u.length ≤ c.2))
    (hright : ¬∃ t, u.length ≤ t ∧ (u ++ v).levelAt t = some (i : ℕ))
    (h : ∃ k, (u ++ v).levelAt k = some (i : ℕ)) :
    InsertCongruence u v i ε := by
  classical
  obtain ⟨k, hk⟩ := h
  have hkp : k < u.length := by_contra fun h' ↦ hright ⟨k, by omega, hk⟩
  set t₀ := Nat.findGreatest (fun t ↦ (u ++ v).levelAt t = some (i : ℕ)) u.length
  have ht₀ : (u ++ v).levelAt t₀ = some (i : ℕ) :=
    Nat.findGreatest_spec (P := fun t ↦ (u ++ v).levelAt t = some (i : ℕ)) hkp.le hk
  have ht₀p : t₀ < u.length :=
    lt_of_le_of_ne (Nat.findGreatest_le _) fun h' ↦ hright ⟨t₀, h'.ge, ht₀⟩
  have hgt : ∀ k, t₀ < k → k < u.length → (u ++ v).levelAt k ≠ some (i : ℕ) :=
    fun k hk hk' ↦ Nat.findGreatest_is_greatest hk hk'.le
  have hα := (isSeifertLoop_insert_left_iff u v i ε ht₀p).2 ⟨ht₀, hgt⟩
  have hβ := isSeifertLoop_insert_mid u v i ε
  have hbij := bijective_insertLoop u v i ε (a := ⟨_, (mem_seifertLoops _).2 hα⟩)
    (β := ⟨_, (mem_seifertLoops _).2 hβ⟩) rfl
    (fun c hc h ↦ by
      simpa [insertLoop_of_not u v i (hno c hc)] using congrArg Prod.snd h)
    (fun h ↦ by simpa [ht₀p.ne] using congrArg (fun z ↦ z.1.1) h) fun z hz hzβ hzF ↦ ?_
  · have hαβ : (⟨_, (mem_seifertLoops _).2 hα⟩ : (u ++ (i, ε) :: (i, -ε) :: v).seifertLoops) ≠
        ⟨_, (mem_seifertLoops _).2 hβ⟩ := fun h ↦ by
      simpa [ht₀p.ne] using congrArg (fun z ↦ z.1.1) h
    have e₀ : Equiv.ofBijective _ hbij (.inr 0) = ⟨_, (mem_seifertLoops _).2 hα⟩ := rfl
    have e₁ : Equiv.ofBijective _ hbij (.inr 1) = ⟨_, (mem_seifertLoops _).2 hβ⟩ := rfl
    obtain ⟨T, hT, h₁, h₂, h₃⟩ := exists_insert_congr_of_not_straddle u v i ε hno
      (Equiv.ofBijective _ hbij) (fun _ ↦ rfl) rfl (s := ε)
      (by rw [e₀, e₁, seifertMatrix_insert_mid_apply u v i ε rfl hαβ]
          have : u.length + 1 ≠ t₀ := by omega
          rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [this])
      (by rw [e₀, e₁, seifertMatrix_insert_apply_mid u v i ε rfl hαβ]
          rcases Int.units_eq_one_or ε with rfl | rfl <;> simp)
    exact ⟨_, T, _, hT, h₁, h₂, h₃⟩
  rcases IsSeifertLoop.insert_cases u v i ε hz with h | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨c, rfl⟩
  · exact absurd h hzβ
  · obtain ⟨-, htl, -⟩ := (isSeifertLoop_insert_right_iff u v i ε ht).1 hz
    exact absurd ⟨t, ht, htl⟩ hright
  · -- a loop ending at the first inserted band starts at the last letter of level `i`
    obtain ⟨htl, htb⟩ := (isSeifertLoop_insert_left_iff u v i ε ht).1 hz
    refine Prod.ext ?_ rfl
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact htb t₀ h ht₀p ht₀
    · exact hgt t h ht htl
  · obtain ⟨hc, hcs⟩ := (isSeifertLoop_insert_insShift_iff u v i ε c).1 hz
    exact absurd (insertLoop_of_not u v i hcs) (hzF c hc)

private theorem insertCongruence (h : ∃ x ∈ u ++ v, x.1 = i) : InsertCongruence u v i ε := by
  by_cases hγ : ∃ c, (u ++ v).IsSeifertLoop c ∧
      ((u ++ v).levelAt c.1 = some (i : ℕ) ∧ c.1 < u.length ∧ u.length ≤ c.2)
  · obtain ⟨γ, hγ, hγs⟩ := hγ
    exact insertCongruence_of_straddle u v i ε hγ hγs
  have hno := fun c hc hcs ↦ hγ ⟨c, hc, hcs⟩
  by_cases hright : ∃ t, u.length ≤ t ∧ (u ++ v).levelAt t = some (i : ℕ)
  · exact insertCongruence_of_right u v i ε hno hright
  · obtain ⟨x, hx, hxi⟩ := h
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact insertCongruence_of_left u v i ε hno hright ⟨k, by simp [levelAt_of_lt _ hk, hxi]⟩

end Assemble

/-! ### Free insertion is an S-equivalence -/

section Main

variable (u v : BraidWord n) (i : Fin (n - 1))

/-- **Inserting `σᵢ σᵢ⁻¹` enlarges the Seifert matrix by a row.** If the level `i` already carries
a letter of `u ++ v`, inserting the inverse pair `σᵢ σᵢ⁻¹` changes the Seifert matrix of the
closure, after relabelling the loops by `ι` and a unimodular change of basis `P`, into a row
enlargement of the Seifert matrix of `u ++ v`. -/
theorem exists_seifertMatrix_insert_congr_enlargeRow (h : ∃ x ∈ u ++ v, x.1 = i) :
    ∃ (ι : (u ++ v).seifertLoops ⊕ Fin 2 ≃ (u ++ (i, 1) :: (i, -1) :: v).seifertLoops)
      (P : Matrix ((u ++ v).seifertLoops ⊕ Fin 2) ((u ++ v).seifertLoops ⊕ Fin 2) ℤ)
      (η : (u ++ v).seifertLoops → ℤ), IsUnit P.det ∧
      P * (u ++ (i, 1) :: (i, -1) :: v).seifertMatrix.submatrix ι ι * Pᵀ =
        enlargeRow (u ++ v).seifertMatrix η := by
  obtain ⟨G, T, s, hT, h₁, h₂, h₃⟩ := insertCongruence u v i 1 h
  simp only [Units.val_one, ite_true] at h₂ h₃
  obtain ⟨Q, η, hQ, hQW⟩ := exists_mul_mul_transpose_eq_enlargeRow _ h₂
    fun x ↦ by simpa using congrFun h₃ x
  refine ⟨G, Q * T, η, by rw [det_mul]; exact hQ.mul hT, ?_⟩
  rw [← h₁, ← hQW, transpose_mul]
  simp only [Matrix.mul_assoc]

/-- **Inserting `σᵢ⁻¹ σᵢ` enlarges the Seifert matrix by a column.** If the level `i` already
carries a letter of `u ++ v`, inserting the inverse pair `σᵢ⁻¹ σᵢ` changes the Seifert matrix of the
closure, after relabelling the loops by `ι` and a unimodular change of basis `P`, into a column
enlargement of the Seifert matrix of `u ++ v`. -/
theorem exists_seifertMatrix_insert_congr_enlargeColumn (h : ∃ x ∈ u ++ v, x.1 = i) :
    ∃ (ι : (u ++ v).seifertLoops ⊕ Fin 2 ≃ (u ++ (i, -1) :: (i, 1) :: v).seifertLoops)
      (P : Matrix ((u ++ v).seifertLoops ⊕ Fin 2) ((u ++ v).seifertLoops ⊕ Fin 2) ℤ)
      (ξ : (u ++ v).seifertLoops → ℤ), IsUnit P.det ∧
      P * (u ++ (i, -1) :: (i, 1) :: v).seifertMatrix.submatrix ι ι * Pᵀ =
        enlargeColumn (u ++ v).seifertMatrix ξ := by
  have hcongr := insertCongruence u v i (-1) h
  unfold InsertCongruence at hcongr
  rw [neg_neg] at hcongr
  obtain ⟨G, T, s, hT, h₁, h₂, h₃⟩ := hcongr
  simp only [Units.val_neg, Units.val_one, Int.reduceNeg, ite_false, show (-1 : ℤ) ≠ 1 by decide]
    at h₂ h₃
  obtain ⟨Q, ξ, hQ, hQW⟩ := exists_mul_mul_transpose_eq_enlargeColumn _ h₃
    fun x ↦ by simpa using congrFun h₂ x
  refine ⟨G, Q * T, ξ, by rw [det_mul]; exact hQ.mul hT, ?_⟩
  rw [← h₁, ← hQW, transpose_mul]
  simp only [Matrix.mul_assoc]

/-- Inserting an inverse pair of letters on a level already in use keeps the Alexander polynomial
of the Seifert matrix. -/
theorem alexander_seifertMatrix_insert (ε : ℤˣ) (h : ∃ x ∈ u ++ v, x.1 = i) :
    alexander (u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix = alexander (u ++ v).seifertMatrix := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · obtain ⟨ι, P, η, hP, hPV⟩ := exists_seifertMatrix_insert_congr_enlargeRow u v i h
    rw [← alexander_enlargeRow _ η, ← hPV,
      alexander_congruence_of_det_sq_eq_one _ (Int.isUnit_sq hP),
      Matrix.alexander_submatrix_equiv_self]
  · obtain ⟨ι, P, ξ, hP, hPV⟩ := exists_seifertMatrix_insert_congr_enlargeColumn u v i h
    rw [neg_neg, ← alexander_enlargeColumn _ ξ, ← hPV,
      alexander_congruence_of_det_sq_eq_one _ (Int.isUnit_sq hP),
      Matrix.alexander_submatrix_equiv_self]

/-- Inserting an inverse pair of letters on a level already in use keeps the Tristram–Levine
signatures of the Seifert matrix. -/
theorem tristramLevineSignature_seifertMatrix_insert (ε : ℤˣ) (h : ∃ x ∈ u ++ v, x.1 = i)
    (ω : ℂ) :
    tristramLevineSignature ((u ++ (i, ε) :: (i, -ε) :: v).seifertMatrix.map ((↑) : ℤ → ℝ)) ω =
      tristramLevineSignature ((u ++ v).seifertMatrix.map ((↑) : ℤ → ℝ)) ω := by
  simp only [← Int.coe_castRingHom]
  rcases Int.units_eq_one_or ε with rfl | rfl
  · obtain ⟨ι, P, η, hP, hPV⟩ := exists_seifertMatrix_insert_congr_enlargeRow u v i h
    have hPℝ : IsUnit (P.map (Int.castRingHom ℝ)).det :=
      (Int.castRingHom ℝ).map_det P ▸ hP.map (Int.castRingHom ℝ)
    have := congrArg (fun M ↦ tristramLevineSignature (M.map (Int.castRingHom ℝ)) ω) hPV
    simp only [Matrix.map_mul, transpose_map, map_enlargeRow,
      tristramLevineSignature_congr hPℝ, tristramLevineSignature_enlargeRow,
      ← submatrix_map] at this
    rwa [← ι.symm_symm, tristramLevineSignature_submatrix_equiv_self] at this
  · obtain ⟨ι, P, ξ, hP, hPV⟩ := exists_seifertMatrix_insert_congr_enlargeColumn u v i h
    have hPℝ : IsUnit (P.map (Int.castRingHom ℝ)).det :=
      (Int.castRingHom ℝ).map_det P ▸ hP.map (Int.castRingHom ℝ)
    have := congrArg (fun M ↦ tristramLevineSignature (M.map (Int.castRingHom ℝ)) ω) hPV
    simp only [Matrix.map_mul, transpose_map, map_enlargeColumn,
      tristramLevineSignature_congr hPℝ, tristramLevineSignature_enlargeColumn,
      ← submatrix_map] at this
    rw [neg_neg]
    rwa [← ι.symm_symm, tristramLevineSignature_submatrix_equiv_self] at this

end Main

namespace FreeCancelStep

variable {w w' : BraidWord n}

/-- A free insertion or deletion of an inverse pair that does not change which levels carry a
letter keeps the Alexander polynomial of the Seifert matrix. -/
theorem alexander_seifertMatrix_eq (h : FreeCancelStep w w')
    (hlevel : ∀ l, (∃ x ∈ w, x.1 = l) ↔ ∃ x ∈ w', x.1 = l) :
    alexander w.seifertMatrix = alexander w'.seifertMatrix := by
  cases h with
  | insert u v i ε =>
    rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
    exact (alexander_seifertMatrix_insert u v i ε ((hlevel i).2 ⟨(i, ε), by simp, rfl⟩)).symm
  | delete u v i ε =>
    rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
    exact alexander_seifertMatrix_insert u v i ε ((hlevel i).1 ⟨(i, ε), by simp, rfl⟩)

/-- A free insertion or deletion of an inverse pair that does not change which levels carry a
letter keeps the Tristram–Levine signatures of the Seifert matrix. -/
theorem tristramLevineSignature_seifertMatrix_eq (h : FreeCancelStep w w')
    (hlevel : ∀ l, (∃ x ∈ w, x.1 = l) ↔ ∃ x ∈ w', x.1 = l) (ω : ℂ) :
    tristramLevineSignature (w.seifertMatrix.map ((↑) : ℤ → ℝ)) ω =
      tristramLevineSignature (w'.seifertMatrix.map ((↑) : ℤ → ℝ)) ω := by
  cases h with
  | insert u v i ε =>
    rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
    exact (tristramLevineSignature_seifertMatrix_insert u v i ε
      ((hlevel i).2 ⟨(i, ε), by simp, rfl⟩) ω).symm
  | delete u v i ε =>
    rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
    exact tristramLevineSignature_seifertMatrix_insert u v i ε
      ((hlevel i).1 ⟨(i, ε), by simp, rfl⟩) ω

end FreeCancelStep

end BraidWord

end TauCeti


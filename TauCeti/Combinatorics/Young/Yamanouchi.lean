/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.BenderKnuth

/-!
# Yamanouchi tableaux and Stembridge's involution

Fix a Young diagram `λ` and a semistandard Young tableau `T` of shape `μ`. Write `T_{≥j}` for the
part of `T` in the columns `j, j + 1, …` and `c(T_{≥j})` for its content. Following Stembridge,
`T` is **`λ`-Yamanouchi** if `λ + c(T_{≥j})` is a partition for every `j`: reading the columns of
`T` from right to left and adding their letters one column at a time to the rows of `λ` never
makes a row longer than the one above it. For `λ = ∅` and `j = 0` this says that the content of
`T` is a partition.

The `λ`-Yamanouchi tableaux of shape `μ` are what the Littlewood–Richardson rule sums over in
Stembridge's form `s_λ s_μ = ∑_T s_{λ + c(T)}`. The rule comes out of an alternant computation in
which the tableaux that are not `λ`-Yamanouchi have to cancel in pairs. This file builds the
pairing, **Stembridge's involution** `SemistandardYoungTableau.stembridgeInvolution`. For a tableau
`T` that is not `λ`-Yamanouchi, let `j` be the rightmost column for which `λ + c(T_{≥j})` is not a
partition, and `k` the first row where it fails, so that
`λ_k + c_k(T_{≥j}) < λ_{k+1} + c_{k+1}(T_{≥j})`. Since `λ + c(T_{≥j+1})` is a partition and a
column holds each letter at most once, column `j` contains `k + 1` but not `k`, and
`λ_k + c_k(T_{≥j}) + 1 = λ_{k+1} + c_{k+1}(T_{≥j})`. The involution applies the Bender–Knuth
involution at `k` to the columns of `T` left of `j` and leaves the rest of `T` alone. Because
column `j` contains no `k`, the result is again semistandard; its columns from `j` on are those of
`T`, so it has the same `j` and `k`, and applying the construction twice gives back `T`.

The effect on the content is what the cancellation needs
(`SemistandardYoungTableau.exists_intCast_rowLen_add_content_stembridgeInvolution`): writing
`e_x = λ_x + c_x(T) - x`, the involution replaces `e` by `e ∘ (k k+1)`. In the alternant
computation the exponent vector `λ + c(T) + δ` is thereby transposed at `k` and `k + 1`, so the
two alternants differ by a sign.

## Main definitions

* `SemistandardYoungTableau.contentFromCol T j k`: the number of entries `k` of `T` in the columns
  `j, j + 1, …`.
* `SemistandardYoungTableau.IsYamanouchi λ T`: `λ + c(T_{≥j})` is a partition for every `j`.
* `SemistandardYoungTableau.stembridgeInvolution λ T`: Stembridge's involution, the identity on
  the `λ`-Yamanouchi tableaux.

## Main results

* `SemistandardYoungTableau.IsYamanouchi.antitone`: for a `λ`-Yamanouchi tableau, `λ + c(T)` is
  weakly decreasing.
* `SemistandardYoungTableau.stembridgeInvolution_stembridgeInvolution`: it is an involution.
* `SemistandardYoungTableau.isYamanouchi_stembridgeInvolution_iff`: it preserves being
  `λ`-Yamanouchi.
* `SemistandardYoungTableau.exists_intCast_rowLen_add_content_stembridgeInvolution`: off the
  `λ`-Yamanouchi tableaux it transposes the shifted content `λ_x + c_x(T) - x` at two adjacent
  letters `k` and `k + 1`, the letter `k + 1` occurring in `T`, and writes no new letter other
  than `k` and `k + 1`.

## References

* J. R. Stembridge, *A concise proof of the Littlewood–Richardson rule*, Electron. J. Combin.
  **9** (2002), Note 5.
* E. A. Bender and D. E. Knuth, *Enumeration of plane partitions*, J. Combinatorial Theory **13**
  (1972), 40--54.
-/

public section

namespace SemistandardYoungTableau

open Finset

variable {μ lam : YoungDiagram} {T : SemistandardYoungTableau μ}

/-! ### The content of a range of columns -/

/-- The content of the part `T_{≥j}` of `T` in the columns `j, j + 1, …`: the number of cells of
the shape in a column at least `j` whose entry is `k`. -/
def contentFromCol (T : SemistandardYoungTableau μ) (j k : ℕ) : ℕ :=
  #{c ∈ μ.cells | j ≤ c.2 ∧ T c.1 c.2 = k}

theorem contentFromCol_def (T : SemistandardYoungTableau μ) (j k : ℕ) :
    T.contentFromCol j k = #{c ∈ μ.cells | j ≤ c.2 ∧ T c.1 c.2 = k} :=
  (rfl)

/-- All the columns together carry the whole content. -/
@[simp]
theorem contentFromCol_zero (T : SemistandardYoungTableau μ) (k : ℕ) :
    T.contentFromCol 0 k = T.content k := by
  simp [contentFromCol, content_apply]

/-- Past the first row there are no columns left. -/
theorem contentFromCol_eq_zero_of_rowLen_le (T : SemistandardYoungTableau μ) {j : ℕ}
    (hj : μ.rowLen 0 ≤ j) (k : ℕ) : T.contentFromCol j k = 0 := by
  refine card_eq_zero.mpr (filter_eq_empty_iff.mpr fun c hc ⟨hjc, _⟩ => ?_)
  have hc' := YoungDiagram.mem_iff_lt_rowLen.mp ((YoungDiagram.mem_cells c).mp hc)
  have := μ.rowLen_anti 0 c.1 (Nat.zero_le _)
  omega

/-- The number of entries `k` of `T` in column `j`. -/
private def colCount (T : SemistandardYoungTableau μ) (j k : ℕ) : ℕ :=
  #{c ∈ μ.cells | c.2 = j ∧ T c.1 c.2 = k}

/-- A column holds each letter at most once, its entries increasing strictly. -/
private theorem colCount_le_one (T : SemistandardYoungTableau μ) (j k : ℕ) :
    colCount T j k ≤ 1 := by
  refine card_le_one.mpr fun a ha b hb => ?_
  simp only [mem_filter, YoungDiagram.mem_cells] at ha hb
  obtain ⟨ha, haj, hak⟩ := ha
  obtain ⟨hb, hbj, hbk⟩ := hb
  have hcol : a.2 = b.2 := haj.trans hbj.symm
  rcases lt_trichotomy a.1 b.1 with h | h | h
  · have hb' : (b.1, a.2) ∈ μ := hcol ▸ hb
    have := T.col_strict h hb'
    rw [hcol] at this hak
    omega
  · exact Prod.ext h hcol
  · have ha' : (a.1, b.2) ∈ μ := hcol ▸ ha
    have := T.col_strict h ha'
    rw [← hcol] at this hbk
    omega

/-- Peeling off the leftmost of the columns `j, j + 1, …`. -/
private theorem contentFromCol_eq_colCount_add (T : SemistandardYoungTableau μ) (j k : ℕ) :
    T.contentFromCol j k = colCount T j k + T.contentFromCol (j + 1) k := by
  rw [contentFromCol, colCount, contentFromCol, ← card_union_of_disjoint]
  · congr 1
    ext c
    simp only [mem_filter, mem_union]
    grind
  · refine disjoint_filter.mpr fun c _ h h' => ?_
    omega

/-! ### Yamanouchi tableaux -/

/-- **A `λ`-Yamanouchi tableau**, in Stembridge's sense: for every column `j`, adding the content
of the columns `j, j + 1, …` of `T` to the row lengths of `λ` gives a weakly decreasing sequence,
the row lengths of a Young diagram. -/
def IsYamanouchi (lam : YoungDiagram) (T : SemistandardYoungTableau μ) : Prop :=
  ∀ j k, lam.rowLen (k + 1) + T.contentFromCol j (k + 1) ≤ lam.rowLen k + T.contentFromCol j k

theorem isYamanouchi_iff :
    T.IsYamanouchi lam ↔
      ∀ j k, lam.rowLen (k + 1) + T.contentFromCol j (k + 1) ≤
        lam.rowLen k + T.contentFromCol j k :=
  Iff.rfl

/-- For a `λ`-Yamanouchi tableau, `λ + c(T)` is weakly decreasing from each row to the next. -/
theorem IsYamanouchi.rowLen_add_content_succ_le (h : T.IsYamanouchi lam) (k : ℕ) :
    lam.rowLen (k + 1) + T.content (k + 1) ≤ lam.rowLen k + T.content k := by
  simpa using h 0 k

/-- **For a `λ`-Yamanouchi tableau, `λ + c(T)` is the sequence of row lengths of a Young
diagram**: it is weakly decreasing. -/
theorem IsYamanouchi.antitone (h : T.IsYamanouchi lam) :
    Antitone fun k => lam.rowLen k + T.content k :=
  antitone_nat_of_succ_le h.rowLen_add_content_succ_le

/-! ### The column and the row where a tableau fails to be Yamanouchi -/

/-- Column `j` witnesses the failure of `λ + c(T_{≥j})` to be weakly decreasing. -/
private def IsBadCol (lam : YoungDiagram) (T : SemistandardYoungTableau μ) (j : ℕ) : Prop :=
  ∃ k, lam.rowLen k + T.contentFromCol j k < lam.rowLen (k + 1) + T.contentFromCol j (k + 1)

private theorem not_isYamanouchi_iff : ¬ T.IsYamanouchi lam ↔ ∃ j, IsBadCol lam T j := by
  simp [IsYamanouchi, IsBadCol]

/-- Only a column of the shape can witness the failure. -/
private theorem lt_rowLen_of_isBadCol {j : ℕ} (h : IsBadCol lam T j) : j < μ.rowLen 0 := by
  by_contra hj
  obtain ⟨k, hk⟩ := h
  rw [T.contentFromCol_eq_zero_of_rowLen_le (not_lt.mp hj),
    T.contentFromCol_eq_zero_of_rowLen_le (not_lt.mp hj)] at hk
  have := lam.rowLen_anti k (k + 1) (Nat.le_succ k)
  omega

open scoped Classical in
/-- The rightmost column witnessing the failure of `T` to be `λ`-Yamanouchi. -/
private noncomputable def badCol (lam : YoungDiagram) (T : SemistandardYoungTableau μ) : ℕ :=
  Nat.findGreatest (IsBadCol lam T) (μ.rowLen 0)

open scoped Classical in
/-- The first row in which a sequence `λ + f` fails to be weakly decreasing, if any. -/
private noncomputable def firstBadRow (lam : YoungDiagram) (f : ℕ → ℕ) : ℕ :=
  if h : ∃ k, lam.rowLen k + f k < lam.rowLen (k + 1) + f (k + 1) then Nat.find h else 0

private theorem firstBadRow_spec {f : ℕ → ℕ}
    (h : ∃ k, lam.rowLen k + f k < lam.rowLen (k + 1) + f (k + 1)) :
    lam.rowLen (firstBadRow lam f) + f (firstBadRow lam f) <
      lam.rowLen (firstBadRow lam f + 1) + f (firstBadRow lam f + 1) := by
  classical
  rw [firstBadRow, dite_eq_left h]
  exact Nat.find_spec h

/-- The row in which the rightmost bad column of `T` fails. -/
private noncomputable def badRow (lam : YoungDiagram) (T : SemistandardYoungTableau μ) : ℕ :=
  firstBadRow lam (T.contentFromCol (badCol lam T))

private theorem badRow_def :
    badRow lam T = firstBadRow lam (T.contentFromCol (badCol lam T)) :=
  (rfl)

private theorem isBadCol_badCol (h : ¬ T.IsYamanouchi lam) : IsBadCol lam T (badCol lam T) := by
  classical
  obtain ⟨j, hj⟩ := not_isYamanouchi_iff.mp h
  exact Nat.findGreatest_spec (lt_rowLen_of_isBadCol hj).le hj

private theorem not_isBadCol_of_badCol_lt {j : ℕ} (hj : badCol lam T < j) :
    ¬ IsBadCol lam T j := by
  classical
  intro hbad
  exact Nat.findGreatest_is_greatest hj (lt_rowLen_of_isBadCol hbad).le hbad

/-- **The local picture at the bad column**: column `badCol` contains `badRow + 1` but not
`badRow`, and `λ + c(T_{≥ badCol})` exceeds by exactly one at `badRow + 1`. -/
private theorem badCol_spec (h : ¬ T.IsYamanouchi lam) :
    lam.rowLen (badRow lam T) + T.contentFromCol (badCol lam T) (badRow lam T) + 1 =
        lam.rowLen (badRow lam T + 1) + T.contentFromCol (badCol lam T) (badRow lam T + 1) ∧
      colCount T (badCol lam T) (badRow lam T + 1) = 1 ∧
      colCount T (badCol lam T) (badRow lam T) = 0 := by
  have hbad : lam.rowLen (badRow lam T) + T.contentFromCol (badCol lam T) (badRow lam T) <
      lam.rowLen (badRow lam T + 1) + T.contentFromCol (badCol lam T) (badRow lam T + 1) :=
    firstBadRow_spec (isBadCol_badCol h)
  have hnext : ¬ IsBadCol lam T (badCol lam T + 1) :=
    not_isBadCol_of_badCol_lt (Nat.lt_succ_self _)
  simp only [IsBadCol, not_exists, not_lt] at hnext
  have hle := hnext (badRow lam T)
  have h₁ := T.contentFromCol_eq_colCount_add (badCol lam T) (badRow lam T)
  have h₂ := T.contentFromCol_eq_colCount_add (badCol lam T) (badRow lam T + 1)
  have h₃ := colCount_le_one T (badCol lam T) (badRow lam T)
  have h₄ := colCount_le_one T (badCol lam T) (badRow lam T + 1)
  omega

/-- Column `badCol` contains no entry `badRow`. -/
private theorem ne_badRow_of_mem (h : ¬ T.IsYamanouchi lam) {r : ℕ}
    (hr : (r, badCol lam T) ∈ μ) : T r (badCol lam T) ≠ badRow lam T := by
  intro hT
  have h0 := (badCol_spec h).2.2
  rw [colCount, card_eq_zero, filter_eq_empty_iff] at h0
  exact h0 ((YoungDiagram.mem_cells _).mpr hr) ⟨rfl, hT⟩

/-- The letter `badRow + 1` occurs in column `badCol`. -/
private theorem exists_eq_badRow_succ (h : ¬ T.IsYamanouchi lam) :
    ∃ r, (r, badCol lam T) ∈ μ ∧ T r (badCol lam T) = badRow lam T + 1 := by
  have h1 := (badCol_spec h).2.1
  rw [colCount, card_eq_one] at h1
  obtain ⟨c, hc⟩ := h1
  have hmem : c ∈ {c ∈ μ.cells | c.2 = badCol lam T ∧ T c.1 c.2 = badRow lam T + 1} := by
    rw [hc]; exact mem_singleton_self c
  simp only [mem_filter, YoungDiagram.mem_cells] at hmem
  obtain ⟨hcμ, hcj, hck⟩ := hmem
  exact ⟨c.1, hcj ▸ hcμ, hcj ▸ hck⟩

/-! ### The Bender–Knuth involution on the columns left of a given one -/

/-- Raise the entries in the columns `j, j + 1, …` by `s`, so that for `s` large they leave the
range of a Bender–Knuth involution. -/
private def shiftFrom (T : SemistandardYoungTableau μ) (j s : ℕ) : SemistandardYoungTableau μ where
  entry r c := T r c + if j ≤ c ∧ (r, c) ∈ μ then s else 0
  row_weak' {r c₁ c₂} hc hmem := by
    have hmem₁ : (r, c₁) ∈ μ := μ.up_left_mem le_rfl hc.le hmem
    have := T.row_weak hc hmem
    simp only [hmem, hmem₁, and_true]
    split_ifs <;> omega
  col_strict' {r₁ r₂ c} hr hmem := by
    have hmem₁ : (r₁, c) ∈ μ := μ.up_left_mem hr.le le_rfl hmem
    have := T.col_strict hr hmem
    simp only [hmem, hmem₁, and_true]
    split_ifs <;> omega
  zeros' {r c} hmem := by
    simp [T.zeros hmem, hmem]

private theorem shiftFrom_apply (T : SemistandardYoungTableau μ) (j s r c : ℕ) :
    shiftFrom T j s r c = T r c + if j ≤ c ∧ (r, c) ∈ μ then s else 0 :=
  (rfl)

/-- A cell of a raised column is outside the Bender–Knuth block at `k`. -/
private theorem not_inBlock_shiftFrom {j k r c : ℕ} (hc : j ≤ c) :
    ¬ (shiftFrom T j (k + 2)).InBlock k r c := by
  intro h
  obtain ⟨hmem, -, hle⟩ := (inBlock_def _ _ _ _).mp h
  rw [shiftFrom_apply, ite_eq_left ⟨hc, hmem⟩] at hle
  omega

/-- The Bender–Knuth involution at `k`, applied to the columns of `T` left of `j`. -/
private def leftBK (T : SemistandardYoungTableau μ) (j k : ℕ)
    (hT : ∀ r, (r, j) ∈ μ → T r j ≠ k) : SemistandardYoungTableau μ where
  entry r c := if c < j then (shiftFrom T j (k + 2)).benderKnuth k r c else T r c
  row_weak' {r c₁ c₂} hc hmem := by
    have hmem₁ : (r, c₁) ∈ μ := μ.up_left_mem le_rfl hc.le hmem
    by_cases h₂ : c₂ < j
    · rw [ite_eq_left (hc.trans h₂), ite_eq_left h₂]
      exact SemistandardYoungTableau.row_weak _ hc hmem
    rw [ite_eq_right h₂]
    by_cases h₁ : c₁ < j
    · rw [ite_eq_left h₁]
      have hj : (r, j) ∈ μ := μ.up_left_mem le_rfl (not_lt.mp h₂) hmem
      have hTj := T.row_weak_of_le (not_lt.mp h₂) hmem
      have hT₁ := T.row_weak h₁ hj
      have hne := hT r hj
      have hshift : shiftFrom T j (k + 2) r c₁ = T r c₁ := by
        rw [shiftFrom_apply, ite_eq_right fun h => absurd h.1 (not_le.mpr h₁), add_zero]
      by_cases hblock : (shiftFrom T j (k + 2)).InBlock k r c₁
      · obtain ⟨-, -, hb⟩ :=
          (inBlock_def _ _ _ _).mp ((inBlock_benderKnuth_iff _ k r c₁).mpr hblock)
        obtain ⟨-, hb', -⟩ := (inBlock_def _ _ _ _).mp hblock
        rw [hshift] at hb'
        omega
      · rw [benderKnuth_apply_of_not_inBlock _ k hblock, hshift]
        exact hT₁.trans hTj
    · rw [ite_eq_right h₁]
      exact T.row_weak hc hmem
  col_strict' {r₁ r₂ c} hr hmem := by
    by_cases hc : c < j
    · rw [ite_eq_left hc, ite_eq_left hc]
      exact SemistandardYoungTableau.col_strict _ hr hmem
    · rw [ite_eq_right hc, ite_eq_right hc]
      exact T.col_strict hr hmem
  zeros' {r c} hmem := by
    split_ifs
    · exact SemistandardYoungTableau.zeros _ hmem
    · exact T.zeros hmem

private theorem leftBK_apply (T : SemistandardYoungTableau μ) (j k : ℕ)
    (hT : ∀ r, (r, j) ∈ μ → T r j ≠ k) (r c : ℕ) :
    leftBK T j k hT r c =
      if c < j then (shiftFrom T j (k + 2)).benderKnuth k r c else T r c :=
  (rfl)

variable {j k : ℕ} {hT : ∀ r, (r, j) ∈ μ → T r j ≠ k}

private theorem leftBK_apply_of_le {r c : ℕ} (hc : j ≤ c) : leftBK T j k hT r c = T r c := by
  rw [leftBK_apply, ite_eq_right (not_lt.mpr hc)]

/-- Inside the columns left of `j`, a cell carries a letter of the block exactly when it did
before, and the other cells are untouched. -/
private theorem leftBK_apply_of_lt {r c : ℕ} (hc : c < j) :
    (k ≤ leftBK T j k hT r c ∧ leftBK T j k hT r c ≤ k + 1 ↔ k ≤ T r c ∧ T r c ≤ k + 1) ∧
      (¬ (k ≤ T r c ∧ T r c ≤ k + 1) → leftBK T j k hT r c = T r c) := by
  have hshift : shiftFrom T j (k + 2) r c = T r c := by
    rw [shiftFrom_apply, ite_eq_right fun h => absurd h.1 (not_le.mpr hc), add_zero]
  rw [leftBK_apply, ite_eq_left hc]
  by_cases hmem : (r, c) ∈ μ
  · have hiff := inBlock_benderKnuth_iff (shiftFrom T j (k + 2)) k r c
    rw [inBlock_def, inBlock_def, hshift] at hiff
    simp only [hmem, true_and] at hiff
    refine ⟨hiff, fun hnot => ?_⟩
    rw [benderKnuth_apply_of_not_inBlock _ k
      fun h => hnot (hshift ▸ ((inBlock_def _ _ _ _).mp h).2), hshift]
  · rw [SemistandardYoungTableau.zeros _ hmem, T.zeros hmem]
    exact ⟨Iff.rfl, fun _ => rfl⟩

/-- The involution writes no letter other than the ones already there and `k`, `k + 1`. -/
private theorem leftBK_apply_eq_or (r c : ℕ) :
    leftBK T j k hT r c = T r c ∨ leftBK T j k hT r c = k ∨ leftBK T j k hT r c = k + 1 := by
  by_cases hc : c < j
  · have h := leftBK_apply_of_lt (T := T) (hT := hT) (r := r) hc
    by_cases hb : k ≤ T r c ∧ T r c ≤ k + 1
    · have := h.1.mpr hb
      omega
    · exact Or.inl (h.2 hb)
  · exact Or.inl (leftBK_apply_of_le (not_lt.mp hc))

/-- The construction does not change the columns from `j` on, so it can be applied again. -/
private theorem leftBK_ne (r : ℕ) (hr : (r, j) ∈ μ) : leftBK T j k hT r j ≠ k := by
  rw [leftBK_apply_of_le le_rfl]
  exact hT r hr

/-- Raising the columns from `j` on commutes with the construction. -/
private theorem shiftFrom_leftBK :
    shiftFrom (leftBK T j k hT) j (k + 2) = (shiftFrom T j (k + 2)).benderKnuth k := by
  ext r c
  rw [shiftFrom_apply, leftBK_apply]
  by_cases hc : c < j
  · rw [ite_eq_left hc, ite_eq_right fun h => absurd h.1 (not_le.mpr hc), add_zero]
  · rw [ite_eq_right hc,
      benderKnuth_apply_of_not_inBlock _ k (not_inBlock_shiftFrom (not_lt.mp hc)),
      shiftFrom_apply]

/-- **The construction is an involution.** -/
private theorem leftBK_leftBK : leftBK (leftBK T j k hT) j k leftBK_ne = T := by
  ext r c
  rw [leftBK_apply]
  by_cases hc : c < j
  · rw [ite_eq_left hc, shiftFrom_leftBK, benderKnuth_benderKnuth, shiftFrom_apply,
      ite_eq_right fun h => absurd h.1 (not_le.mpr hc), add_zero]
  · rw [ite_eq_right hc, leftBK_apply_of_le (not_lt.mp hc)]

/-- The columns from `j` on keep their content. -/
private theorem contentFromCol_leftBK {j' : ℕ} (hj : j ≤ j') (x : ℕ) :
    (leftBK T j k hT).contentFromCol j' x = T.contentFromCol j' x := by
  simp only [contentFromCol]
  congr 1
  refine filter_congr fun c _ => ?_
  constructor
  · rintro ⟨hc, hx⟩
    exact ⟨hc, leftBK_apply_of_le (hj.trans hc) ▸ hx⟩
  · rintro ⟨hc, hx⟩
    exact ⟨hc, (leftBK_apply_of_le (hj.trans hc)).trans hx⟩

/-- The content of the columns left of `j`. -/
private def contentBeforeCol (T : SemistandardYoungTableau μ) (j x : ℕ) : ℕ :=
  #{c ∈ μ.cells | c.2 < j ∧ T c.1 c.2 = x}

private theorem content_eq_contentBeforeCol_add (T : SemistandardYoungTableau μ) (j x : ℕ) :
    T.content x = contentBeforeCol T j x + T.contentFromCol j x := by
  rw [content_apply, contentBeforeCol, contentFromCol, ← card_union_of_disjoint]
  · congr 1
    ext c
    simp only [mem_filter, mem_union]
    grind
  · refine disjoint_filter.mpr fun c _ h h' => ?_
    omega

/-- **The construction exchanges the content of the columns left of `j` at `k` and `k + 1`.** -/
private theorem contentBeforeCol_leftBK (x : ℕ) :
    contentBeforeCol (leftBK T j k hT) j x = contentBeforeCol T j (Equiv.swap k (k + 1) x) := by
  set S := shiftFrom T j (k + 2)
  -- Below the cut, `S` agrees with `T`; from the cut on, `S` and its Bender–Knuth image carry
  -- only letters at least `k + 2`.
  have hS : ∀ c ∈ μ.cells, c.2 < j → S c.1 c.2 = T c.1 c.2 := fun c _ hc => by
    rw [shiftFrom_apply, ite_eq_right fun h => absurd h.1 (not_le.mpr hc), add_zero]
  have hbig : ∀ c ∈ μ.cells, j ≤ c.2 → k + 2 ≤ S c.1 c.2 := fun c hc hj => by
    rw [shiftFrom_apply, ite_eq_left ⟨hj, (YoungDiagram.mem_cells _).mp hc⟩]
    omega
  have hbig' : ∀ c ∈ μ.cells, j ≤ c.2 → S.benderKnuth k c.1 c.2 = S c.1 c.2 := fun c _ hj =>
    benderKnuth_apply_of_not_inBlock _ k (not_inBlock_shiftFrom hj)
  -- For a letter of the block, both sides count the cells of the whole shape.
  have hblock : ∀ (U : SemistandardYoungTableau μ) (y : ℕ), y ≤ k + 1 →
      (∀ c ∈ μ.cells, j ≤ c.2 → k + 2 ≤ U c.1 c.2) →
      #{c ∈ μ.cells | c.2 < j ∧ U c.1 c.2 = y} = U.content y := by
    intro U y hy hU
    rw [content_apply]
    congr 1
    refine filter_congr fun c hc => ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    by_contra hcj
    have := hU c hc (not_lt.mp hcj)
    omega
  by_cases hx : x = k ∨ x = k + 1
  · have hσ : Equiv.swap k (k + 1) x ≤ k + 1 := by
      rcases hx with rfl | rfl <;> simp
    have hx' : x ≤ k + 1 := by omega
    have hleft : contentBeforeCol (leftBK T j k hT) j x =
        #{c ∈ μ.cells | c.2 < j ∧ S.benderKnuth k c.1 c.2 = x} := by
      rw [contentBeforeCol]
      congr 1
      refine filter_congr fun c _ => and_congr_right fun hc => ?_
      rw [leftBK_apply, ite_eq_left hc]
    have hright : contentBeforeCol T j (Equiv.swap k (k + 1) x) =
        #{c ∈ μ.cells | c.2 < j ∧ S c.1 c.2 = Equiv.swap k (k + 1) x} := by
      rw [contentBeforeCol]
      congr 1
      exact filter_congr fun c hc => and_congr_right fun hcj => by rw [hS c hc hcj]
    rw [hleft, hright, hblock _ x hx' fun c hc hj => (hbig' c hc hj).symm ▸ hbig c hc hj,
      hblock _ _ hσ hbig, content_benderKnuth]
  · have hσ : Equiv.swap k (k + 1) x = x := Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
    rw [hσ, contentBeforeCol, contentBeforeCol]
    congr 1
    refine filter_congr fun c _ => and_congr_right fun hc => ?_
    have h := leftBK_apply_of_lt (T := T) (hT := hT) (r := c.1) hc
    by_cases hb : k ≤ T c.1 c.2 ∧ T c.1 c.2 ≤ k + 1
    · have := h.1.mpr hb
      constructor <;> intro h' <;> omega
    · rw [h.2 hb]

/-! ### Stembridge's involution -/

open scoped Classical in
/-- **Stembridge's involution.** On a tableau that is not `λ`-Yamanouchi, apply the
Bender–Knuth involution at the first failing row `k` of the rightmost failing column `j` to the
columns left of `j`; on a `λ`-Yamanouchi tableau, do nothing. -/
noncomputable def stembridgeInvolution (lam : YoungDiagram) (T : SemistandardYoungTableau μ) :
    SemistandardYoungTableau μ :=
  if h : T.IsYamanouchi lam then T
  else leftBK T (badCol lam T) (badRow lam T) fun _ hr => ne_badRow_of_mem h hr

@[simp]
theorem stembridgeInvolution_of_isYamanouchi (h : T.IsYamanouchi lam) :
    T.stembridgeInvolution lam = T := by
  rw [stembridgeInvolution, dite_eq_left h]

private theorem stembridgeInvolution_of_not_isYamanouchi (h : ¬ T.IsYamanouchi lam) :
    T.stembridgeInvolution lam =
      leftBK T (badCol lam T) (badRow lam T) fun _ hr => ne_badRow_of_mem h hr := by
  rw [stembridgeInvolution, dite_eq_right h]

/-- The construction keeps the bad column of a tableau that is not Yamanouchi, and its bad row. -/
private theorem badCol_leftBK (h : ¬ T.IsYamanouchi lam) {hT} :
    badCol lam (leftBK T (badCol lam T) (badRow lam T) hT) = badCol lam T ∧
      badRow lam (leftBK T (badCol lam T) (badRow lam T) hT) = badRow lam T := by
  classical
  have hcol : ∀ {j'}, badCol lam T ≤ j' →
      (IsBadCol lam (leftBK T (badCol lam T) (badRow lam T) hT) j' ↔ IsBadCol lam T j') :=
    fun hj => by simp only [IsBadCol, contentFromCol_leftBK hj]
  have hj : badCol lam (leftBK T (badCol lam T) (badRow lam T) hT) = badCol lam T := by
    rw [badCol, Nat.findGreatest_eq_iff]
    refine ⟨Nat.findGreatest_le _, fun _ => (hcol le_rfl).mpr (isBadCol_badCol h),
      fun j' hj' hj'n hbad => not_isBadCol_of_badCol_lt hj' ((hcol hj'.le).mp hbad)⟩
  refine ⟨hj, ?_⟩
  rw [badRow_def (T := leftBK T (badCol lam T) (badRow lam T) hT), hj]
  exact congrArg (firstBadRow lam) (funext fun x => contentFromCol_leftBK le_rfl x)

/-- **Stembridge's involution preserves being `λ`-Yamanouchi.** -/
@[simp]
theorem isYamanouchi_stembridgeInvolution_iff :
    (T.stembridgeInvolution lam).IsYamanouchi lam ↔ T.IsYamanouchi lam := by
  by_cases h : T.IsYamanouchi lam
  · rw [stembridgeInvolution_of_isYamanouchi h]
  · rw [stembridgeInvolution_of_not_isYamanouchi h]
    refine iff_of_false ?_ h
    rw [not_isYamanouchi_iff]
    refine ⟨badCol lam T, ?_⟩
    simpa only [IsBadCol, contentFromCol_leftBK le_rfl] using isBadCol_badCol h

/-- **Stembridge's involution is an involution.** -/
@[simp]
theorem stembridgeInvolution_stembridgeInvolution :
    (T.stembridgeInvolution lam).stembridgeInvolution lam = T := by
  by_cases h : T.IsYamanouchi lam
  · rw [stembridgeInvolution_of_isYamanouchi h, stembridgeInvolution_of_isYamanouchi h]
  have h' : ¬ (T.stembridgeInvolution lam).IsYamanouchi lam :=
    fun h' => h (isYamanouchi_stembridgeInvolution_iff.mp h')
  rw [stembridgeInvolution_of_not_isYamanouchi h']
  ext r c
  rw [leftBK_apply, stembridgeInvolution_of_not_isYamanouchi h]
  obtain ⟨hj, hk⟩ := badCol_leftBK (hT := fun _ hr => ne_badRow_of_mem h hr) h
  rw [hj, hk, ← leftBK_apply _ _ _ leftBK_ne, leftBK_leftBK]

theorem stembridgeInvolution_involutive (lam μ : YoungDiagram) :
    Function.Involutive fun T : SemistandardYoungTableau μ => T.stembridgeInvolution lam :=
  fun _ => stembridgeInvolution_stembridgeInvolution

/-- **Stembridge's involution transposes the shifted content at two adjacent letters.** Off the
`λ`-Yamanouchi tableaux there is a letter `k` such that `k + 1` occurs in `T`, the involution
writes no letter other than those of `T` and `k`, `k + 1`, and the shifted content
`e_x = λ_x + c_x(T) - x` of the image is `e ∘ (k k+1)`. -/
theorem exists_intCast_rowLen_add_content_stembridgeInvolution (h : ¬ T.IsYamanouchi lam) :
    ∃ k, (∃ r c, (r, c) ∈ μ ∧ T r c = k + 1) ∧
      (∀ r c, T.stembridgeInvolution lam r c = T r c ∨ T.stembridgeInvolution lam r c = k ∨
        T.stembridgeInvolution lam r c = k + 1) ∧
      ∀ x, ((lam.rowLen x + (T.stembridgeInvolution lam).content x : ℕ) : ℤ) - x =
        ((lam.rowLen (Equiv.swap k (k + 1) x) + T.content (Equiv.swap k (k + 1) x) : ℕ) : ℤ) -
          (Equiv.swap k (k + 1) x : ℕ) := by
  obtain ⟨hspec, -, -⟩ := badCol_spec h
  obtain ⟨r, hr, hrk⟩ := exists_eq_badRow_succ h
  refine ⟨badRow lam T, ⟨r, _, hr, hrk⟩, fun r c => ?_, fun x => ?_⟩
  · rw [stembridgeInvolution_of_not_isYamanouchi h]
    exact leftBK_apply_eq_or r c
  rw [stembridgeInvolution_of_not_isYamanouchi h, content_eq_contentBeforeCol_add _ (badCol lam T),
    contentBeforeCol_leftBK, contentFromCol_leftBK le_rfl,
    content_eq_contentBeforeCol_add T (badCol lam T)]
  rcases eq_or_ne x (badRow lam T) with rfl | hxk
  · rw [Equiv.swap_apply_left]
    push_cast
    omega
  rcases eq_or_ne x (badRow lam T + 1) with rfl | hxk'
  · rw [Equiv.swap_apply_right]
    push_cast
    omega
  · rw [Equiv.swap_apply_of_ne_of_ne hxk hxk']

end SemistandardYoungTableau

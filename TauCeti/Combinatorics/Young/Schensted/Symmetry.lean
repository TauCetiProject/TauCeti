/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.RSK

/-!
# The symmetry of the Robinson--Schensted correspondence

Schützenberger's symmetry theorem: the Robinson--Schensted correspondence of the inverse
permutation `σ⁻¹` is that of `σ` with the insertion and recording tableaux exchanged,
`Equiv.Perm.rsk_inv`.

The proof is Fomin's growth-diagram argument. For a word `w` of distinct letters, consider the
insertion tableaux `G(i, k)` of the subwords formed by those of the first `i` letters whose value
is below `k`. Passing from `G(i, k)` to `G(i + 1, k)` adds at most one cell, in the row where the
`i`-th letter is inserted; passing from `G(i, k)` to `G(i, k + 1)` adds at most one cell, the cell
of the letter `k`. Label each edge of the `(i, k)` grid by the row of the added cell, if any.
The comparison `TauCeti.rowInsert_appendToRow` of inserting a letter into a tableau with and
without a strictly larger letter at the end of one of its rows shows that the labels of the top
and right edges of each unit square are given by Fomin's local rule from the labels of its bottom
and left edges, and this rule is symmetric under exchanging the two. Exchanging positions and
values transposes the grid, so the recording word of `σ⁻¹`, read off the top edge of the
transposed grid, lists the rows of the labels of the insertion tableau of `σ`, read off the right
edge of the original grid.

## Main results

* `Equiv.Perm.findIdx?_robinsonSchensted_ofFn_eq_some`: the label `k` lies in row `r` of the
  insertion tableau of `σ`, where `r` is the `k`-th letter of the recording word of `σ⁻¹`.
* `Equiv.Perm.rowWord_snd_fst_rsk_apply`: the row word of the insertion tableau of `σ` is the
  recording word of `σ⁻¹`.
* `Equiv.Perm.rsk_inv`: `rsk n σ⁻¹` exchanges the two tableaux of `rsk n σ`.

## References

* M.-P. Schützenberger, *Quelques remarques sur une construction de Schensted*, Math. Scand. 12
  (1963), 117--128.
* S. Fomin, *Schensted algorithms for dual graded graphs*, J. Algebraic Combin. 4 (1995), 5--45.
* R. P. Stanley, *Enumerative Combinatorics, Volume 2*, Cambridge University Press (1999),
  Section 7.13.
-/

public section

namespace TauCeti

open List

/-! ### The growth diagram of a word of distinct letters -/

section GrowthDiagram

variable {n : ℕ}

/-- The insertion tableau of the letters with value below `k` among the first `i` letters of
`w`. -/
private def growth (w : List (Fin n)) (i k : ℕ) : List (List (Fin n)) :=
  (robinsonSchensted ((w.take i).filter fun x : Fin n => (x : ℕ) < k)).1

/-- The horizontal edge label of the growth diagram: the row of the cell that the `i`-th letter
adds to `growth w i k`, if that letter has value below `k`. -/
private def hLabel (w : List (Fin n)) (i k : ℕ) : Option ℕ :=
  (w[i]?.filter fun x : Fin n => (x : ℕ) < k).map fun x => rowInsertIndex x (growth w i k)

/-- The vertical edge label of the growth diagram: the row of `growth w i (k + 1)` containing
the letter `k`, if any. -/
private def vLabel (w : List (Fin n)) (i : ℕ) (k : Fin n) : Option ℕ :=
  (growth w i (k + 1)).findIdx? fun row => k ∈ row

/-- Fomin's local rule, sending the bottom and left edge labels of a unit square of the growth
diagram to its top and right edge labels. The flag records whether the square carries a point
of the permutation. -/
private def growthRule (b : Bool) (bot left : Option ℕ) : Option ℕ × Option ℕ :=
  if b then (some 0, some 0) else
    match bot, left with
    | some r, some s => if r = s then (some (r + 1), some (r + 1)) else (some r, some s)
    | bot, left => (bot, left)

private theorem growthRule_swap (b : Bool) (bot left : Option ℕ) :
    growthRule b left bot = (growthRule b bot left).swap := by
  unfold growthRule
  cases b
  · rcases bot with _ | r <;> rcases left with _ | s <;> simp [eq_comm]
    split_ifs <;> simp_all
  · simp

private theorem mem_flatten_growth_iff {w : List (Fin n)} {i k : ℕ} {x : Fin n} :
    x ∈ (growth w i k).flatten ↔ x ∈ w.take i ∧ (x : ℕ) < k := by
  rw [growth, (flatten_robinsonSchensted_fst_perm _).mem_iff, mem_filter, decide_eq_true_iff]

private theorem growth_zero_left (w : List (Fin n)) (k : ℕ) : growth w 0 k = [] := by
  simp [growth]

/-- At the full threshold `n`, the growth diagram is the insertion tableau of a prefix. -/
private theorem growth_n (w : List (Fin n)) (i : ℕ) :
    growth w i n = (robinsonSchensted (w.take i)).1 := by
  rw [growth, filter_eq_self.mpr fun x _ => by simp]

/-- Adding the `i`-th letter inserts it, if its value is below the threshold. -/
private theorem growth_succ_left (w : List (Fin n)) {i : ℕ} (hi : i < w.length) (k : ℕ) :
    growth w (i + 1) k =
      if (w[i] : ℕ) < k then rowInsert w[i] (growth w i k) else growth w i k := by
  have htake : w.take (i + 1) = w.take i ++ [w[i]] := by simp
  rw [growth, growth, htake, filter_append]
  split_ifs with h <;> simp [h]

/-- Adding a letter past the end of the word changes nothing. -/
private theorem growth_succ_left_of_le (w : List (Fin n)) {i : ℕ} (hi : w.length ≤ i) (k : ℕ) :
    growth w (i + 1) k = growth w i k := by
  rw [growth, growth, take_of_length_le (by omega), take_of_length_le hi]

private theorem forall_mem_flatten_growth_lt (w : List (Fin n)) (i : ℕ) (k : Fin n) :
    ∀ z ∈ (growth w i k).flatten, z < k := fun _ hz =>
  Fin.lt_def.mpr (mem_flatten_growth_iff.mp hz).2

/-- The bound needed to append `k` after an insertion past it. -/
private theorem le_length_rowInsert {α : Type*} [LinearOrder α] (x : α) {s : ℕ}
    {rows : List (List α)} (hs : s ≤ rows.length) :
    (if rowInsertIndex x rows = s then s + 1 else s) ≤ (rowInsert x rows).length := by
  have hle := rowInsertIndex_le_length x rows
  rw [length_rowInsert]
  split_ifs <;> omega

/-- Raising the threshold from `k` to `k + 1` adds the letter `k` at the end of some row, when
the letter `k` occurs. -/
private theorem growth_succ (w : List (Fin n)) (hw : w.Nodup) (i : ℕ) (k : Fin n) :
    (k ∉ w.take i → growth w i (k + 1) = growth w i k) ∧
      (k ∈ w.take i → ∃ s ≤ (growth w i k).length,
        growth w i (k + 1) = appendToRow k s (growth w i k)) := by
  induction i with
  | zero => simp [growth_zero_left]
  | succ i ih =>
    by_cases hi : i < w.length
    · have htake : w.take (i + 1) = w.take i ++ [w[i]] := by simp
      have hnot : w[i] ∉ w.take i := fun h =>
        disjoint_take_drop hw le_rfl h (mem_drop_iff_getElem.mpr ⟨0, by simpa, by simp⟩)
      have hA := forall_mem_flatten_growth_lt w i k
      rw [growth_succ_left w hi, growth_succ_left w hi, htake]
      simp only [mem_append, mem_singleton]
      rcases lt_trichotomy (w[i] : ℕ) k with hlt | heq | hgt
      · have hne : k ≠ w[i] := fun h => by simp [h] at hlt
        simp only [hlt, show (w[i] : ℕ) < k + 1 by omega, ↓reduceIte, hne, or_false]
        refine ⟨fun hk => by rw [ih.1 hk], fun hk => ?_⟩
        obtain ⟨s, hs, heq⟩ := ih.2 hk
        refine ⟨if rowInsertIndex w[i] (growth w i k) = s then s + 1 else s, ?_, ?_⟩
        · exact le_length_rowInsert _ hs
        · rw [heq]
          exact rowInsert_appendToRow (Fin.lt_def.mpr hlt) hA hs
      · have hk : w[i] = k := Fin.ext heq
        simp only [heq, lt_irrefl, show (k : ℕ) < k + 1 by omega, ↓reduceIte]
        rw [hk] at hnot ⊢
        simp only [or_true, not_true_eq_false, IsEmpty.forall_iff, forall_const, true_and]
        refine ⟨0, Nat.zero_le _, ?_⟩
        rw [ih.1 hnot]
        exact rowInsert_of_forall_le fun z hz => (hA z hz).le
      · have hne : k ≠ w[i] := fun h => by simp [h] at hgt
        simp only [show ¬ (w[i] : ℕ) < k by omega, show ¬ (w[i] : ℕ) < k + 1 by omega,
          ↓reduceIte, hne, or_false]
        exact ih
    · have htake : w.take (i + 1) = w.take i := by
        rw [take_of_length_le (by omega), take_of_length_le (by omega)]
      rw [growth_succ_left_of_le w (by omega), growth_succ_left_of_le w (by omega), htake]
      exact ih

private theorem hLabel_eq (w : List (Fin n)) {i : ℕ} (hi : i < w.length) (k : ℕ) :
    hLabel w i k = if (w[i] : ℕ) < k then some (rowInsertIndex w[i] (growth w i k)) else none := by
  unfold hLabel
  rw [getElem?_eq_getElem hi]
  by_cases h : (w[i] : ℕ) < k <;> simp [Option.filter, h]

private theorem hLabel_zero (w : List (Fin n)) (i : ℕ) : hLabel w i 0 = none := by
  unfold hLabel
  cases w[i]? <;> simp [Option.filter]

private theorem vLabel_zero (w : List (Fin n)) (k : Fin n) : vLabel w 0 k = none := by
  simp [vLabel, growth_zero_left]

private theorem vLabel_eq_none {w : List (Fin n)} {i : ℕ} {k : Fin n} (hk : k ∉ w.take i) :
    vLabel w i k = none := by
  rw [vLabel, findIdx?_eq_none_iff]
  intro row hrow
  simpa using fun hkrow => hk (mem_flatten_growth_iff.mp (mem_flatten_of_mem hrow hkrow)).1

private theorem vLabel_eq_some {w : List (Fin n)} {i s : ℕ} {k : Fin n}
    (hs : s ≤ (growth w i k).length) (h : growth w i (k + 1) = appendToRow k s (growth w i k)) :
    vLabel w i k = some s := by
  rw [vLabel, h]
  refine findIdx?_mem_appendToRow_self (fun row hrow hk => ?_) hs
  exact lt_irrefl k (forall_mem_flatten_growth_lt w i k k (mem_flatten_of_mem hrow hk))

/-- The top edge of the growth diagram is the recording word. -/
private theorem hLabel_n (w : List (Fin n)) {i : ℕ} (hi : i < w.length) :
    hLabel w i n = some ((robinsonSchensted w).2[i]'(by simpa using hi)) := by
  simp only [hLabel_eq w hi, w[i].isLt, ↓reduceIte, growth_n, getElem_robinsonSchensted_snd]

/-- Raising the threshold past `k` does not move the letter `k`. -/
private theorem findIdx?_growth_eq_vLabel (w : List (Fin n)) (hw : w.Nodup) (i : ℕ) (k : Fin n)
    (d : ℕ) (hd : k + 1 + d ≤ n) :
    (growth w i (k + 1 + d)).findIdx? (fun row => k ∈ row) = vLabel w i k := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have hm : k + 1 + d < n := by omega
    have hne : k ≠ (⟨k + 1 + d, hm⟩ : Fin n) := fun h => by
      have := congrArg Fin.val h
      simp only at this
      omega
    obtain ⟨h₁, h₂⟩ := growth_succ w hw i ⟨k + 1 + d, hm⟩
    rw [← ih (by omega), ← add_assoc]
    by_cases hmem : (⟨k + 1 + d, hm⟩ : Fin n) ∈ w.take i
    · obtain ⟨s, -, hs⟩ := h₂ hmem
      exact hs ▸ findIdx?_mem_appendToRow_of_ne hne _ _
    · exact congrArg _ (h₁ hmem)

/-- The right edge of the growth diagram lists the rows of the insertion tableau containing each
letter. -/
private theorem vLabel_length (w : List (Fin n)) (hw : w.Nodup) (k : Fin n) :
    vLabel w w.length k = (robinsonSchensted w).1.findIdx? (fun row => k ∈ row) := by
  rw [← findIdx?_growth_eq_vLabel w hw w.length k (n - (k + 1)) (by omega),
    show (k : ℕ) + 1 + (n - (k + 1)) = n by omega, growth_n, take_length]

/-- **Fomin's local rule** holds in the growth diagram of a word of distinct letters. -/
private theorem growthRule_hLabel_vLabel (w : List (Fin n)) (hw : w.Nodup) {i : ℕ}
    (hi : i < w.length) (k : Fin n) :
    (hLabel w i (k + 1), vLabel w (i + 1) k) =
      growthRule (w[i] = k) (hLabel w i k) (vLabel w i k) := by
  have hnot : w[i] ∉ w.take i := fun h =>
    disjoint_take_drop hw le_rfl h (mem_drop_iff_getElem.mpr ⟨0, by simpa, by simp⟩)
  have hA := forall_mem_flatten_growth_lt w i k
  have htake : w.take (i + 1) = w.take i ++ [w[i]] := by simp
  obtain ⟨G₁, G₂⟩ := growth_succ w hw i k
  rw [hLabel_eq w hi, hLabel_eq w hi]
  rcases lt_trichotomy (w[i] : ℕ) k with hlt | heq | hgt
  · have hne : w[i] ≠ k := fun h => by simp [h] at hlt
    have hk' : k ∈ w.take (i + 1) ↔ k ∈ w.take i := by
      rw [htake, mem_append, mem_singleton]
      exact or_iff_left (Ne.symm hne)
    have hlt' : (w[i] : ℕ) < k + 1 := by omega
    simp only [hlt, hlt', ↓reduceIte]
    rw [decide_eq_false hne]
    by_cases hk : k ∈ w.take i
    · obtain ⟨s, hs, hB⟩ := G₂ hk
      have hB' : growth w (i + 1) (k + 1) =
          appendToRow k (if rowInsertIndex w[i] (growth w i k) = s then s + 1 else s)
            (growth w (i + 1) k) := by
        simp only [growth_succ_left w hi, hlt, hlt', ↓reduceIte, hB]
        exact rowInsert_appendToRow (Fin.lt_def.mpr hlt) hA hs
      rw [vLabel_eq_some hs hB, vLabel_eq_some (by
          simp only [growth_succ_left w hi, hlt, ↓reduceIte]
          exact le_length_rowInsert _ hs) hB', hB,
        rowInsertIndex_appendToRow (Fin.lt_def.mpr hlt) hA hs]
      simp only [growthRule, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> simp_all
    · rw [vLabel_eq_none hk, vLabel_eq_none (by rwa [hk']), G₁ hk]
      simp [growthRule]
  · have hk : w[i] = k := Fin.ext heq
    rw [hk] at hnot
    have hB' : growth w (i + 1) (k + 1) = appendToRow k 0 (growth w (i + 1) k) := by
      simp only [growth_succ_left w hi, hk, lt_irrefl, show (k : ℕ) < k + 1 by omega,
        ↓reduceIte, G₁ hnot]
      exact rowInsert_of_forall_le fun z hz => (hA z hz).le
    rw [vLabel_eq_some (Nat.zero_le _) hB', vLabel_eq_none hnot, G₁ hnot, hk,
      rowInsertIndex_of_forall_le fun z hz => (hA z hz).le]
    simp [growthRule]
  · have hne : w[i] ≠ k := fun h => by simp [h] at hgt
    have hB' : growth w (i + 1) (k + 1) = growth w i (k + 1) := by
      simp only [growth_succ_left w hi, show ¬ (w[i] : ℕ) < k + 1 by omega, ↓reduceIte]
    simp only [show ¬ (w[i] : ℕ) < k by omega, show ¬ (w[i] : ℕ) < k + 1 by omega, ↓reduceIte,
      hne, decide_false, vLabel, hB']
    simp [growthRule]

/-- One column of the transposed growth diagram: if the horizontal labels at threshold `k` of
`w` are the vertical labels at position `k` of `w'`, then so are the vertical labels of `w` at
value `k` and the horizontal labels of `w'` at position `k`. -/
private theorem vLabel_eq_hLabel_of_forall {w w' : List (Fin n)} (hw : w.Nodup)
    (hw' : w'.Nodup) (hl : w.length = n) (hl' : w'.length = n)
    (hww' : ∀ i k : Fin n, w[(i : ℕ)]'(by omega) = k ↔ w'[(k : ℕ)]'(by omega) = i) (k : Fin n)
    (H : ∀ i : Fin n, hLabel w i k = vLabel w' k i) (i : ℕ) (hi : i ≤ n) :
    vLabel w i k = hLabel w' k i := by
  induction i with
  | zero => rw [vLabel_zero, hLabel_zero]
  | succ i ih =>
    have hi' : i < n := by omega
    have he : decide (w[i]'(by omega) = k) = decide (w'[(k : ℕ)]'(by omega) = ⟨i, hi'⟩) :=
      decide_eq_decide.mpr (hww' ⟨i, hi'⟩ k)
    calc vLabel w (i + 1) k
        = (growthRule (w[i]'(by omega) = k) (hLabel w i k) (vLabel w i k)).2 :=
          congrArg Prod.snd (growthRule_hLabel_vLabel w hw (by omega) k)
      _ = (growthRule (w[i]'(by omega) = k) (hLabel w' k i) (vLabel w' k ⟨i, hi'⟩)).1 := by
          rw [H ⟨i, hi'⟩, ih (by omega), growthRule_swap, Prod.snd_swap]
      _ = hLabel w' k (i + 1) := by
          rw [he]
          exact (congrArg Prod.fst (growthRule_hLabel_vLabel w' hw' (by omega) ⟨i, hi'⟩)).symm

/-- **Transposing the growth diagram.** If exchanging positions and values takes `w` to `w'`,
the horizontal labels of the growth diagram of `w` are the vertical labels of that of `w'`. -/
private theorem hLabel_eq_vLabel_of_forall {w w' : List (Fin n)} (hw : w.Nodup)
    (hw' : w'.Nodup) (hl : w.length = n) (hl' : w'.length = n)
    (hww' : ∀ i k : Fin n, w[(i : ℕ)]'(by omega) = k ↔ w'[(k : ℕ)]'(by omega) = i) (k : ℕ)
    (hk : k ≤ n) (i : Fin n) : hLabel w i k = vLabel w' k i := by
  induction k generalizing i with
  | zero => rw [hLabel_zero, vLabel_zero]
  | succ k ih =>
    have hk' : k < n := by omega
    have H := ih (by omega)
    have he : decide (w[(i : ℕ)]'(by omega) = ⟨k, hk'⟩) =
        decide (w'[k]'(by omega) = i) :=
      decide_eq_decide.mpr (hww' i ⟨k, hk'⟩)
    calc hLabel w i (k + 1)
        = (growthRule (w[(i : ℕ)]'(by omega) = ⟨k, hk'⟩) (hLabel w i k)
            (vLabel w i ⟨k, hk'⟩)).1 :=
          congrArg Prod.fst (growthRule_hLabel_vLabel w hw (by omega) ⟨k, hk'⟩)
      _ = (growthRule (w[(i : ℕ)]'(by omega) = ⟨k, hk'⟩) (hLabel w' k i) (vLabel w' k i)).2 := by
          rw [H i, vLabel_eq_hLabel_of_forall hw hw' hl hl' hww' ⟨k, hk'⟩ H i (by omega),
            growthRule_swap, Prod.fst_swap]
      _ = vLabel w' (k + 1) i := by
          rw [he]
          exact (congrArg Prod.snd (growthRule_hLabel_vLabel w' hw' (by omega) i)).symm

end GrowthDiagram

end TauCeti

namespace Equiv.Perm

open List TauCeti

variable {n : ℕ}

/-- **The symmetry of the Robinson--Schensted correspondence**, at the level of words: the label
`k` lies in the row of the insertion tableau of `σ` given by the `k`-th letter of the recording
word of `σ⁻¹`. -/
theorem findIdx?_robinsonSchensted_ofFn_eq_some (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    (robinsonSchensted (ofFn σ)).1.findIdx? (fun row => k ∈ row) =
      some ((robinsonSchensted (ofFn ⇑σ⁻¹)).2[(k : ℕ)]'(by simp)) := by
  have hw : (ofFn σ).Nodup := nodup_ofFn.mpr σ.injective
  have hw' : (ofFn ⇑σ⁻¹).Nodup := nodup_ofFn.mpr σ⁻¹.injective
  have hww' (i k : Fin n) :
      (ofFn σ)[(i : ℕ)]'(by simp) = k ↔ (ofFn ⇑σ⁻¹)[(k : ℕ)]'(by simp) = i := by
    simp only [List.getElem_ofFn, Equiv.Perm.inv_eq_iff_eq]
    exact eq_comm
  rw [← vLabel_length _ hw, length_ofFn,
    vLabel_eq_hLabel_of_forall hw hw' length_ofFn length_ofFn hww' k
      (fun i => hLabel_eq_vLabel_of_forall hw hw' length_ofFn length_ofFn hww' k k.isLt.le i)
      n le_rfl,
    hLabel_n _ (by simp)]

/-- The insertion tableau of `σ` has the recording word of `σ⁻¹` as its row word. -/
theorem rowWord_snd_fst_rsk_apply (σ : Equiv.Perm (Fin n)) :
    (rsk n σ).2.1.rowWord = (robinsonSchensted (ofFn ⇑σ⁻¹)).2 := by
  have hcard : (YoungDiagram.ofPartition (rsk n σ).1).card = n :=
    YoungDiagram.card_ofPartition _
  -- Membership of a label in a row does not see the bound on the labels.
  have hval {m : ℕ} (rows : List (List (Fin m))) (l : Fin m) :
      rows.findIdx? (fun row => l ∈ row) =
        (rows.map (map Fin.val)).findIdx? (fun row => (l : ℕ) ∈ row) := by
    rw [findIdx?_map]
    congr 1
    funext row
    simp [Fin.val_inj]
  refine ext_getElem (by simp [hcard]) fun k hk hk' => ?_
  have hkn : k < n := by simpa using hk'
  apply Option.some.inj
  rw [StandardYoungTableau.getElem_rowWord, ← StandardYoungTableau.findIdx?_mem_toRows, hval,
    map_val_toRows_rsk_apply σ]
  have := findIdx?_robinsonSchensted_ofFn_eq_some σ ⟨k, hkn⟩
  rw [hval] at this
  exact this

/-- **Schützenberger's symmetry theorem.** The Robinson--Schensted correspondence of the
inverse permutation exchanges the insertion and recording tableaux. -/
theorem rsk_inv (σ : Equiv.Perm (Fin n)) :
    rsk n σ⁻¹ = ⟨(rsk n σ).1, (rsk n σ).2.2, (rsk n σ).2.1⟩ := by
  have h₁ : (rsk n σ).2.1.rowWord = (rsk n σ⁻¹).2.2.rowWord := by
    rw [rowWord_snd_fst_rsk_apply, rowWord_rsk_apply]
  have h₂ : (rsk n σ⁻¹).2.1.rowWord = (rsk n σ).2.2.rowWord := by
    rw [rowWord_snd_fst_rsk_apply, inv_inv, rowWord_rsk_apply]
  generalize rsk n σ⁻¹ = x at h₁ h₂ ⊢
  generalize rsk n σ = y at h₁ h₂ ⊢
  obtain ⟨μ, P, Q⟩ := x
  obtain ⟨ν, R, S⟩ := y
  dsimp only at h₁ h₂ ⊢
  obtain rfl : μ = ν := by
    apply YoungDiagram.ofPartition_injective
    ext ⟨i, j⟩
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
      YoungDiagram.mem_iff_lt_rowLen, ← StandardYoungTableau.count_rowWord Q,
      ← StandardYoungTableau.count_rowWord R, h₁]
  rw [StandardYoungTableau.rowWord_injective h₁, StandardYoungTableau.rowWord_injective h₂]

end Equiv.Perm

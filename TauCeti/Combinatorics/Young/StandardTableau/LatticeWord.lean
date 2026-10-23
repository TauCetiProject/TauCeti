/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.RobinsonSchensted
import TauCeti.Combinatorics.Young.StandardTableau.Order
public import TauCeti.Combinatorics.Young.StandardTableau.Corner
import TauCeti.Combinatorics.Young.StandardTableau.Reading

/-!
# Standard tableaux and lattice recording words

The row word of a standard Young tableau records the row containing each label, in increasing
order of labels. It is a lattice word: every prefix contains at least as many entries in row `i`
as in row `i + 1`. Conversely, a lattice word with `μ.rowLen i` occurrences of each letter `i`
determines a unique standard tableau of shape `μ`.

This identifies the recording words of Robinson–Schensted insertion with standard recording
tableaux. The bijection uses the existing corner restriction and extension of standard tableaux:
the final letter specifies the corner occupied by the largest label.

## References

* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), Section 4.1.
* B. E. Sagan, *The Symmetric Group*, second edition, Springer GTM 203 (2001), Section 3.1.
-/

public section

namespace TauCeti.StandardYoungTableau

open List YoungTableau

variable {μ : YoungDiagram} {c : ℕ × ℕ}

/-- The rows containing the labels `0, …, μ.card - 1`, in that order. -/
def rowWord (T : StandardYoungTableau μ) : List ℕ :=
  List.ofFn (rowIndex T.toTableau)

/-- The row word lists the row index of each label. -/
theorem rowWord_def (T : StandardYoungTableau μ) :
    T.rowWord = List.ofFn (rowIndex T.toTableau) := (rfl)

/-- A row word has one letter per cell. -/
@[simp]
theorem length_rowWord (T : StandardYoungTableau μ) : T.rowWord.length = μ.card := by
  simp [rowWord]

/-- The letter at a label's position is the row containing that label. -/
@[simp]
theorem getElem_rowWord (T : StandardYoungTableau μ) (k : ℕ) (hk : k < T.rowWord.length) :
    T.rowWord[k] = rowIndex T.toTableau ⟨k, by simpa using hk⟩ := by
  simp [rowWord]

/-- Standard tableaux are determined by their row words. -/
theorem rowWord_injective : Function.Injective (rowWord (μ := μ)) := by
  intro T U h
  exact rowIndex_injective μ (List.ofFn_injective h)

private theorem rowIndex_extend_of_lt (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) (k : Fin (YoungDiagram.erase μ c).card) :
    rowIndex (extend hc T).toTableau ⟨k.val, by have := hc.card_erase; omega⟩ =
      rowIndex T.toTableau k := by
  let d := T.toTableau.symm k
  have hd : d.1 ≠ c := (hc.mem_erase_iff.mp d.2).2
  have he : (extend hc T).toTableau ⟨d.1, (hc.mem_erase_iff.mp d.2).1⟩ =
      ⟨k.val, by have := hc.card_erase; omega⟩ := by
    apply Fin.ext
    rw [toTableau_apply, extend_apply_val_of_ne hc T _ hd]
    exact congrArg Fin.val (T.toTableau.apply_symm_apply k)
  rw [← he, rowIndex_apply]
  exact (rowIndex_def T.toTableau k).symm

/-- Restoring a corner appends its row to the row word. -/
@[simp]
theorem rowWord_extend (hc : YoungDiagram.IsCorner μ c)
    (T : StandardYoungTableau (YoungDiagram.erase μ c)) :
    (extend hc T).rowWord = T.rowWord ++ [c.1] := by
  rw [rowWord_def, List.ofFn_congr hc.card_erase.symm, List.ofFn_succ']
  simp only [List.concat_eq_append]
  apply congrArg₂ (· ++ ·)
  · exact (congrArg List.ofFn (funext fun k => rowIndex_extend_of_lt hc T k)).trans
      T.rowWord_def.symm
  · congr 1
    have he : (extend hc T).toTableau ⟨c, hc.mem⟩ =
        Fin.cast hc.card_erase (Fin.last (YoungDiagram.erase μ c).card) := by
      apply Fin.ext
      have := extend_apply_self hc T
      have := hc.card_erase
      simp only [toTableau_apply, Fin.val_cast, Fin.val_last]
      omega
    rw [← he, rowIndex_apply]

/-- The number of occurrences of a row in the row word is its length. -/
@[simp]
theorem count_rowWord (T : StandardYoungTableau μ) (i : ℕ) : T.rowWord.count i = μ.rowLen i := by
  simpa only [rowWord_def, ← Multiset.coe_count, ← Fin.univ_val_map, Multiset.count_map,
    ← Finset.filter_val, ← Finset.card_def, eq_comm] using
    card_filter_rowIndex_eq T.toTableau i

/-- Every standard tableau has a lattice row word. -/
theorem isLatticeWord_rowWord (T : StandardYoungTableau μ) : T.rowWord.IsLatticeWord := by
  induction hn : μ.card using Nat.strong_induction_on generalizing μ with
  | h n ih =>
    by_cases hμ : 0 < μ.card
    · let c := T.maxCell hμ
      have hc : YoungDiagram.IsCorner μ c := T.isCorner_maxCell hμ
      let U := restrict hc T (T.apply_maxCell hμ)
      have hU := ih (YoungDiagram.erase μ c).card (by have := hc.card_erase; omega) U rfl
      rw [← extend_restrict hc T (T.apply_maxCell hμ), rowWord_extend,
        isLatticeWord_append_singleton]
      refine ⟨hU, fun i hi => ?_⟩
      rw [count_rowWord, count_rowWord, hc.rowLen_erase,
        hc.rowLen_erase]
      have := hc.rowLen_eq_snd_add_one
      rw [hi] at this
      have hmono := μ.rowLen_anti i (i + 1) (by omega)
      simp only [hi, Nat.add_one_ne_self, ↓reduceIte]
      omega
    · have hzero : T.rowWord = [] := length_eq_zero_iff.mp (by rw [length_rowWord]; omega)
      simp [hzero]

/-- Lattice words with the prescribed row counts are exactly the row words of standard
tableaux of that shape. -/
theorem exists_rowWord_eq_iff (r : List ℕ) :
    (∃ T : StandardYoungTableau μ, T.rowWord = r) ↔
      r.IsLatticeWord ∧ ∀ i, r.count i = μ.rowLen i := by
  refine ⟨?_, ?_⟩
  · rintro ⟨T, rfl⟩
    exact ⟨T.isLatticeWord_rowWord, T.count_rowWord⟩
  · rintro ⟨hr, hshape⟩
    induction r using reverseRecOn generalizing μ with
    | nil =>
      let T := rowSuperstandard μ
      have hp : T.rowWord.Perm [] := List.perm_iff_count.mpr fun i => by
        rw [count_rowWord, ← hshape i]
      exact ⟨T, List.perm_nil.mp hp⟩
    | append_singleton r k ih =>
      have hr' := (isLatticeWord_append_singleton.mp hr).1
      have hk : μ.rowLen k = r.count k + 1 := by simpa using (hshape k).symm
      have hnext : μ.rowLen (k + 1) ≤ r.count k := by
        have := hr'.count_succ_le k
        have := hshape (k + 1)
        simp only [count_append, count_singleton, beq_iff_eq] at this
        split_ifs at this <;> omega
      have hc : YoungDiagram.IsCorner μ (k, r.count k) := by
        refine (YoungDiagram.isCorner_def _ _).mpr ⟨?_, ?_, ?_⟩
        · exact YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
        · simp only [YoungDiagram.mem_iff_lt_rowLen]
          omega
        · simp only [YoungDiagram.mem_iff_lt_rowLen]
          omega
      have hshape' (i : ℕ) : r.count i = (YoungDiagram.erase μ (k, r.count k)).rowLen i := by
        rw [hc.rowLen_erase]
        have := hshape i
        simp only [count_append, count_singleton, beq_iff_eq] at this
        split_ifs <;> split_ifs at this <;> omega
      obtain ⟨T, hT⟩ := ih hr' hshape'
      exact ⟨extend hc T, by rw [rowWord_extend, hT]⟩

/-- Standard tableaux of shape `μ` correspond to lattice words containing each row index
exactly as many times as that row has cells. -/
noncomputable def latticeWordEquiv (μ : YoungDiagram) :
    StandardYoungTableau μ ≃ {r : List ℕ // r.IsLatticeWord ∧ ∀ i, r.count i = μ.rowLen i} :=
  Equiv.ofBijective (fun T => ⟨T.rowWord, T.isLatticeWord_rowWord, T.count_rowWord⟩)
    ⟨fun _ _ h => rowWord_injective (congrArg Subtype.val h),
      fun r => (exists_rowWord_eq_iff r.val).mpr r.property |>.imp fun _ h => Subtype.ext h⟩

/-- The lattice-word correspondence sends a tableau to its row word. -/
@[simp]
theorem latticeWordEquiv_apply_val (T : StandardYoungTableau μ) :
    (latticeWordEquiv μ T).val = T.rowWord := (rfl)

/-- Decoding a lattice word recovers a tableau having exactly that row word. -/
@[simp]
theorem rowWord_latticeWordEquiv_symm (r : {r : List ℕ //
    r.IsLatticeWord ∧ ∀ i, r.count i = μ.rowLen i}) :
    ((latticeWordEquiv μ).symm r).rowWord = r.val :=
  congrArg Subtype.val ((latticeWordEquiv μ).apply_symm_apply r)

end TauCeti.StandardYoungTableau

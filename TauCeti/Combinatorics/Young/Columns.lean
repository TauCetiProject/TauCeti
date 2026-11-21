/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import TauCeti.Combinatorics.Young.Kostka
public import TauCeti.Combinatorics.Young.OfRowLens

/-!
# Columns of bounded semistandard Young tableaux and flag chains

A bounded semistandard Young tableau `T : BoundedSSYT n μ` of shape `μ` with entries in
`{0, …, n - 1}` has strictly increasing columns, so its `m`-th column determines an order
embedding `T.colOrderEmb m : Fin (μ.colLen m) ↪o Fin n` and a finite subset
`T.colFinset m : Finset (Fin n)`. Counting the columns that contain a given letter `r : Fin n`
recovers the tableau content `T.val.content r`
(`TauCeti.BoundedSSYT.sum_ite_mem_colFinset_eq_content`).

Two column sets `I` and `J` can appear as left-to-right columns of a semistandard tableau when
`#J ≤ #I` and the sorted entries satisfy `i_p ≤ j_p` for every `p < #J`
(`TauCeti.FlagTableauLe I J`). Conversely, any `FlagTableauLe`-chain `I : Fin k → Finset (Fin n)`
of nonempty subsets is the sequence of nonempty columns of a reconstructed bounded semistandard
tableau `TauCeti.boundedSSYTOfFlagChain` of shape `TauCeti.shapeOfFlagChain I hanti`
(`TauCeti.exists_boundedSSYT_colFinset_eq`).

## Main definitions

* `TauCeti.BoundedSSYT.colOrderEmb` and `TauCeti.BoundedSSYT.colFinset`: the sorted entries and row
  subset of column `m` of a bounded semistandard tableau.
* `TauCeti.FlagTableauLe`: the column-standardness order `#J ≤ #I` and `i_p ≤ j_p` for `p < #J`,
  with a decidable instance.
* `TauCeti.shapeOfFlagChain` and `TauCeti.boundedSSYTOfFlagChain`: reconstruction of a Young
  diagram and bounded semistandard tableau from a `FlagTableauLe`-chain.

## Main results

* `TauCeti.BoundedSSYT.sum_ite_mem_colFinset_eq_content`: the number of columns containing `r` is
  `T.val.content r`.
* `TauCeti.BoundedSSYT.flagTableauLe_colFinset`: columns of a bounded tableau form a
  `FlagTableauLe`-chain.
* `TauCeti.flagTableauLe_of_adjacent` and `TauCeti.exists_boundedSSYT_colFinset_eq`: an adjacent
  `FlagTableauLe`-chain of nonempty subsets is the column sequence of a bounded tableau of width
  `k` with at most `n` rows.
-/

public section

namespace TauCeti

open Finset

variable {n : ℕ} {μ : YoungDiagram}

/-! ### Columns of a bounded semistandard Young tableau -/

namespace BoundedSSYT

/-- The `m`-th column of a bounded semistandard Young tableau `T`, read as an order embedding
`Fin (μ.colLen m) ↪o Fin n`: entries increase strictly down each column of `μ` and lie below `n`. -/
def colOrderEmb (T : BoundedSSYT n μ) (m : ℕ) : Fin (μ.colLen m) ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ ⟨T.val i m, T.entry_lt (YoungDiagram.mem_iff_lt_colLen.mpr i.isLt)⟩)
    fun _ _ h ↦
      Fin.lt_def.mpr (T.val.col_strict h (YoungDiagram.mem_iff_lt_colLen.mpr ‹Fin _›.isLt))

@[simp]
theorem coe_colOrderEmb_apply (T : BoundedSSYT n μ) (m : ℕ) (i : Fin (μ.colLen m)) :
    (T.colOrderEmb m i : ℕ) = T.val i m :=
  (rfl)

/-- The set of row indices appearing in column `m` of a bounded semistandard Young tableau `T`. -/
def colFinset (T : BoundedSSYT n μ) (m : ℕ) : Finset (Fin n) :=
  univ.map (T.colOrderEmb m).toEmbedding

theorem colFinset_def (T : BoundedSSYT n μ) (m : ℕ) :
    T.colFinset m = univ.map (T.colOrderEmb m).toEmbedding :=
  (rfl)

@[simp]
theorem card_colFinset (T : BoundedSSYT n μ) (m : ℕ) : #(T.colFinset m) = μ.colLen m := by
  simp [colFinset_def]

/-- A row index `r : Fin n` belongs to `T.colFinset m` if and only if it appears at some cell
`(i, m)` of column `m` of `μ`. -/
theorem mem_colFinset_iff (T : BoundedSSYT n μ) {m : ℕ} {r : Fin n} :
    r ∈ T.colFinset m ↔ ∃ i < μ.colLen m, T.val i m = r := by
  rw [colFinset_def, mem_map]
  refine ⟨fun ⟨i, _, hi⟩ ↦ ⟨i, i.isLt, by simpa [Fin.ext_iff] using hi⟩, ?_⟩
  rintro ⟨i, hi, hir⟩
  exact ⟨⟨i, hi⟩, mem_univ _, Fin.ext hir⟩

/-- Columns past `μ.rowLen 0` are empty. -/
@[simp]
theorem colFinset_eq_empty_of_rowLen_zero_le (T : BoundedSSYT n μ) {m : ℕ}
    (hm : μ.rowLen 0 ≤ m) : T.colFinset m = ∅ := by
  rw [← card_eq_zero, card_colFinset]
  by_contra h
  exact (YoungDiagram.mem_iff_lt_rowLen.mp
    (YoungDiagram.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero h))).not_ge hm

/-- Columns strictly before `μ.rowLen 0` are nonempty. -/
theorem colFinset_nonempty_of_lt_rowLen_zero (T : BoundedSSYT n μ) {m : ℕ}
    (hm : m < μ.rowLen 0) : (T.colFinset m).Nonempty := by
  rw [← card_pos, card_colFinset]
  exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hm)

/-- Sorting `T.colFinset m` recovers the column order embedding `T.colOrderEmb m`. -/
theorem orderEmbOfFin_colFinset (T : BoundedSSYT n μ) (m : ℕ) :
    (T.colFinset m).orderEmbOfFin (T.card_colFinset m) = T.colOrderEmb m :=
  (orderEmbOfFin_unique' (T.card_colFinset m) fun i ↦ by
    rw [colFinset_def]
    exact mem_map_of_mem _ (mem_univ i)).symm

@[simp]
theorem coe_orderEmbOfFin_colFinset_apply (T : BoundedSSYT n μ) (m : ℕ) {k : ℕ}
    (hk : #(T.colFinset m) = k) (i : Fin k) :
    ((T.colFinset m).orderEmbOfFin hk i : ℕ) = T.val i m := by
  obtain rfl : k = μ.colLen m := hk.symm.trans (T.card_colFinset m)
  rw [T.orderEmbOfFin_colFinset m, coe_colOrderEmb_apply]

/-- Counting the columns of `T` containing a letter `r : Fin n` recovers the tableau content
`T.val.content r`. -/
theorem sum_ite_mem_colFinset_eq_content (T : BoundedSSYT n μ) (r : Fin n) :
    (∑ m ∈ range (μ.rowLen 0), if r ∈ T.colFinset m then 1 else 0) = T.val.content r := by
  rw [SemistandardYoungTableau.content_apply, sum_boole]
  -- Map each column `m` containing `r` at `(i, m)` to that unique cell of `μ`.
  refine Finset.card_bij
    (fun m hm ↦
      let hex := (T.mem_colFinset_iff.mp (mem_filter.mp hm).right)
      (Classical.choose hex, m))
    (fun m hm ↦ ?_) (fun _ _ _ _ h ↦ congrArg Prod.snd h) fun c hc ↦ ?_
  · obtain ⟨_, hmem⟩ := mem_filter.mp hm
    have hspec := Classical.choose_spec (T.mem_colFinset_iff.mp hmem)
    exact mem_filter.mpr ⟨(μ.mem_cells _).mpr
      (YoungDiagram.mem_iff_lt_colLen.mpr hspec.left), hspec.right⟩
  · obtain ⟨hcμ, hcr⟩ := mem_filter.mp hc
    have hcμ' := (μ.mem_cells _).mp hcμ
    have hm0 : c.snd < μ.rowLen 0 :=
      (YoungDiagram.mem_iff_lt_rowLen.mp hcμ').trans_le (μ.rowLen_anti 0 c.fst (Nat.zero_le _))
    have hrm : r ∈ T.colFinset c.snd :=
      T.mem_colFinset_iff.mpr ⟨c.fst, YoungDiagram.mem_iff_lt_colLen.mp hcμ', hcr⟩
    refine ⟨c.snd, mem_filter.mpr ⟨mem_range.mpr hm0, hrm⟩, ?_⟩
    have hspec := Classical.choose_spec (T.mem_colFinset_iff.mp hrm)
    refine Prod.ext ?_ rfl
    -- Column strictness makes the row index `i` with `T i c.2 = r` unique.
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (T.val.col_strict hlt hcμ').ne (hspec.right.trans hcr.symm)
    · exact (T.val.col_strict hgt (YoungDiagram.mem_iff_lt_colLen.mpr hspec.left)).ne
        (hcr.trans hspec.right.symm)

end BoundedSSYT

/-! ### The column-standardness order and tableau reconstruction -/

/-- **Column-standardness order** on subsets of `Fin n`: `FlagTableauLe I J` holds when `#J ≤ #I`
and the `p`-th smallest element of `I` is at most the `p`-th smallest element of `J` for every
`p < #J`, i.e., `I` and `J` can appear as adjacent columns of a semistandard Young tableau. -/
def FlagTableauLe (I J : Finset (Fin n)) : Prop :=
  ∃ h : #J ≤ #I, ∀ p : Fin #J, I.orderEmbOfFin rfl (Fin.castLE h p) ≤ J.orderEmbOfFin rfl p

theorem flagTableauLe_def {I J : Finset (Fin n)} :
    FlagTableauLe I J ↔
      ∃ h : #J ≤ #I, ∀ p : Fin #J, I.orderEmbOfFin rfl (Fin.castLE h p) ≤ J.orderEmbOfFin rfl p :=
  Iff.rfl

/-- Column standardness between two subsets of `Fin n` is computable. -/
instance (n : ℕ) : DecidableRel (FlagTableauLe (n := n)) := fun I J ↦
  if h : #J ≤ #I then
    if h' : ∀ p : Fin #J, I.orderEmbOfFin rfl (Fin.castLE h p) ≤ J.orderEmbOfFin rfl p then
      isTrue (flagTableauLe_def.mpr ⟨h, h'⟩)
    else isFalse fun hle ↦ h' (flagTableauLe_def.mp hle).2
  else isFalse fun hle ↦ h (flagTableauLe_def.mp hle).1

theorem FlagTableauLe.card_le {I J : Finset (Fin n)} (h : FlagTableauLe I J) : #J ≤ #I := h.1

@[refl]
theorem FlagTableauLe.refl (I : Finset (Fin n)) : FlagTableauLe I I := ⟨le_rfl, fun _ ↦ le_rfl⟩

theorem FlagTableauLe.trans {I J K : Finset (Fin n)} (hIJ : FlagTableauLe I J)
    (hJK : FlagTableauLe J K) : FlagTableauLe I K :=
  ⟨hJK.1.trans hIJ.1, fun p ↦ (hIJ.2 (Fin.castLE hJK.1 p)).trans (hJK.2 p)⟩

/-- Columns of a bounded semistandard tableau satisfy `FlagTableauLe` from left to right. -/
theorem BoundedSSYT.flagTableauLe_colFinset (T : BoundedSSYT n μ)
    {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) : FlagTableauLe (T.colFinset m₁) (T.colFinset m₂) := by
  refine ⟨by rw [T.card_colFinset, T.card_colFinset]; exact μ.colLen_anti m₁ m₂ hm,
    fun p ↦ Fin.le_iff_val_le_val.mpr ?_⟩
  rw [T.coe_orderEmbOfFin_colFinset_apply m₁ rfl, T.coe_orderEmbOfFin_colFinset_apply m₂ rfl]
  exact T.val.row_weak_of_le hm
    (YoungDiagram.mem_iff_lt_colLen.mpr (p.isLt.trans_eq (T.card_colFinset _)))

/-- If every adjacent pair in `I : Fin k → Finset (Fin n)` satisfies `FlagTableauLe`, then the
whole tuple is a `FlagTableauLe`-chain. -/
theorem flagTableauLe_of_adjacent {k : ℕ} {I : Fin k → Finset (Fin n)}
    (hadj : ∀ (j : ℕ) (hj : j + 1 < k), FlagTableauLe (I ⟨j, Nat.lt_of_succ_lt hj⟩) (I ⟨j + 1, hj⟩))
    {m₁ m₂ : Fin k} (hm : m₁ ≤ m₂) : FlagTableauLe (I m₁) (I m₂) := by
  obtain ⟨a, ha⟩ := m₁; obtain ⟨b, hb⟩ := m₂
  have hab : a ≤ b := Fin.le_def.mp hm; clear hm
  induction b, hab using Nat.le_induction with
  | base => exact FlagTableauLe.refl _
  | succ d _ ih => exact (ih (Nat.lt_of_succ_lt hb)).trans (hadj d hb)

/-- The Young diagram with columns of lengths `#(I m)` associated to a tuple of column sizes. -/
def shapeOfFlagChain {k : ℕ} (I : Fin k → Finset (Fin n))
    (hanti : Antitone fun m : Fin k ↦ #(I m)) : YoungDiagram :=
  (YoungDiagram.ofRowLensFin (fun m : Fin k ↦ #(I m)) hanti).transpose

theorem mem_shapeOfFlagChain_iff {k : ℕ} {I : Fin k → Finset (Fin n)}
    {hanti : Antitone fun m : Fin k ↦ #(I m)} {i m : ℕ} :
    (i, m) ∈ shapeOfFlagChain I hanti ↔ ∃ hm : m < k, i < #(I ⟨m, hm⟩) := by
  rw [shapeOfFlagChain, YoungDiagram.mem_transpose, Prod.swap_prod_mk,
    YoungDiagram.mem_iff_lt_rowLen]
  by_cases hm : m < k
  · simp [hm, YoungDiagram.rowLen_ofRowLensFin _ _ ⟨m, hm⟩]
  · simp [hm, YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le _ _ (not_lt.mp hm)]

@[simp]
theorem colLen_shapeOfFlagChain {k : ℕ} (I : Fin k → Finset (Fin n))
    (hanti : Antitone fun m : Fin k ↦ #(I m)) (m : Fin k) :
    (shapeOfFlagChain I hanti).colLen m = #(I m) := by
  simp [shapeOfFlagChain, YoungDiagram.colLen_transpose]

theorem colLen_zero_shapeOfFlagChain_le {k : ℕ} (I : Fin k → Finset (Fin n))
    (hanti : Antitone fun m : Fin k ↦ #(I m)) :
    (shapeOfFlagChain I hanti).colLen 0 ≤ n := by
  dsimp only [shapeOfFlagChain]
  rw [YoungDiagram.colLen_transpose]
  by_cases hk : 0 < k
  · simpa using (YoungDiagram.rowLen_ofRowLensFin _ hanti ⟨0, hk⟩).le.trans
      (card_finset_fin_le _)
  · rw [YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le _ _ (by omega)]
    exact Nat.zero_le n

theorem rowLen_zero_shapeOfFlagChain {k : ℕ} (I : Fin k → Finset (Fin n))
    (hanti : Antitone fun m : Fin k ↦ #(I m)) (hne : ∀ m, (I m).Nonempty) :
    (shapeOfFlagChain I hanti).rowLen 0 = k :=
  le_antisymm
    (not_lt.mp fun hk ↦ by
      obtain ⟨hm, _⟩ := mem_shapeOfFlagChain_iff.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hk)
      omega)
    (not_lt.mp fun hk ↦ (YoungDiagram.mem_iff_lt_rowLen.mp
      (mem_shapeOfFlagChain_iff.mpr ⟨hk, (hne _).card_pos⟩)).false)

/-- Construct the `BoundedSSYT` whose columns are a given `FlagTableauLe`-chain `I`. -/
def boundedSSYTOfFlagChain {k : ℕ} (I : Fin k → Finset (Fin n))
    (hchain : ∀ m₁ m₂, m₁ ≤ m₂ → FlagTableauLe (I m₁) (I m₂))
    (hanti : Antitone fun m : Fin k ↦ #(I m)) :
    BoundedSSYT n (shapeOfFlagChain I hanti) :=
  ⟨{ entry := fun i m ↦
       if h : ∃ hm : m < k, i < #(I ⟨m, hm⟩) then
         ((I ⟨m, h.1⟩).orderEmbOfFin rfl ⟨i, h.2⟩ : ℕ)
       else 0
     row_weak' := fun {i m₁ m₂} hm hcell ↦ by
       have h₂ := mem_shapeOfFlagChain_iff.mp hcell
       have h₁ := mem_shapeOfFlagChain_iff.mp
         ((shapeOfFlagChain I hanti).up_left_mem le_rfl hm.le hcell)
       simp only [h₁, h₂, ↓reduceDIte]
       exact Fin.le_iff_val_le_val.mp
         ((hchain ⟨m₁, h₁.1⟩ ⟨m₂, h₂.1⟩ (Fin.le_def.mpr hm.le)).2 ⟨i, h₂.2⟩)
     col_strict' := fun {i₁ i₂ m} hi hcell ↦ by
       have h₂ := mem_shapeOfFlagChain_iff.mp hcell
       have h₁ := mem_shapeOfFlagChain_iff.mp
         ((shapeOfFlagChain I hanti).up_left_mem hi.le le_rfl hcell)
       simp only [h₁, h₂, ↓reduceDIte]
       exact Fin.lt_def.mp (((I ⟨m, h₂.1⟩).orderEmbOfFin rfl).strictMono hi)
     zeros' := fun h ↦ dite_eq_right (h ∘ mem_shapeOfFlagChain_iff.mpr) },
   fun i m hcell ↦ by
     have h := mem_shapeOfFlagChain_iff.mp hcell
     rw [← SemistandardYoungTableau.to_fun_eq_coe]
     simp only [h, ↓reduceDIte]
     exact ((I ⟨m, h.1⟩).orderEmbOfFin rfl ⟨i, h.2⟩).isLt⟩

theorem boundedSSYTOfFlagChain_apply {k : ℕ} (I : Fin k → Finset (Fin n))
    (hchain : ∀ m₁ m₂, m₁ ≤ m₂ → FlagTableauLe (I m₁) (I m₂))
    (hanti : Antitone fun m : Fin k ↦ #(I m)) {i : ℕ} (m : Fin k) (hi : i < #(I m)) :
    (boundedSSYTOfFlagChain I hchain hanti).val i m =
      ((I m).orderEmbOfFin rfl ⟨i, hi⟩ : ℕ) := by
  dsimp only [boundedSSYTOfFlagChain]
  rw [← SemistandardYoungTableau.to_fun_eq_coe]
  have hmem : ∃ hm : (m : ℕ) < k, i < #(I ⟨m, hm⟩) := ⟨m.isLt, hi⟩
  simp only [hmem, ↓reduceDIte]

@[simp]
theorem colFinset_boundedSSYTOfFlagChain {k : ℕ} (I : Fin k → Finset (Fin n))
    (hchain : ∀ m₁ m₂, m₁ ≤ m₂ → FlagTableauLe (I m₁) (I m₂))
    (hanti : Antitone fun m : Fin k ↦ #(I m)) (m : Fin k) :
    (boundedSSYTOfFlagChain I hchain hanti).colFinset m = I m := by
  ext r
  rw [BoundedSSYT.mem_colFinset_iff, colLen_shapeOfFlagChain]
  refine ⟨fun ⟨i, hi, hir⟩ ↦ ?_, fun hr ↦ ?_⟩
  · rw [boundedSSYTOfFlagChain_apply I hchain hanti m hi] at hir
    exact Fin.ext hir ▸ (I m).orderEmbOfFin_mem rfl _
  · obtain ⟨i, rfl⟩ := (Finset.range_orderEmbOfFin (I m) rfl).symm.subset hr
    exact ⟨i, i.isLt, boundedSSYTOfFlagChain_apply I hchain hanti m i.isLt⟩

/-- Every `FlagTableauLe`-chain of nonempty subsets of `Fin n` is the sequence of nonempty columns
of a bounded semistandard Young tableau of width `k` and shape with at most `n` rows. -/
theorem exists_boundedSSYT_colFinset_eq {k : ℕ} (I : Fin k → Finset (Fin n))
    (hne : ∀ m, (I m).Nonempty)
    (hchain : ∀ m₁ m₂, m₁ ≤ m₂ → FlagTableauLe (I m₁) (I m₂)) :
    ∃ (μ : {μ : YoungDiagram // μ.colLen 0 ≤ n}) (T : BoundedSSYT n μ.val),
      μ.val.rowLen 0 = k ∧ ∀ m : Fin k, T.colFinset m = I m := by
  have hanti : Antitone (fun m : Fin k ↦ #(I m)) := fun _ _ h ↦ (hchain _ _ h).card_le
  exact ⟨⟨shapeOfFlagChain I hanti, colLen_zero_shapeOfFlagChain_le I hanti⟩,
    boundedSSYTOfFlagChain I hchain hanti,
    rowLen_zero_shapeOfFlagChain I hanti hne,
    colFinset_boundedSSYTOfFlagChain I hchain hanti⟩

end TauCeti

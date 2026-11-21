/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Partitions
public import TauCeti.Combinatorics.Young.StandardTableau.Reading
public import TauCeti.RepresentationTheory.Symmetric.RowColumnSubgroup
public import TauCeti.RepresentationTheory.Symmetric.YoungSubgroup.Basic

/-!
# Tableau row groups and Young subgroups

The row group of a tableau depends on its labeling, whereas the Young subgroup attached to its
shape uses consecutive blocks. This file constructs the permutation sending the consecutive-block
labeling to a given tableau, proves that it conjugates the corresponding Young subgroup onto
the tableau's row group, and records its normalization on the row-superstandard tableau
`StandardYoungTableau.rowSuperstandard μ` (where the conjugator is `1` and the row group is
`youngSubgroup (shapePartition μ)` on the nose).

## References

* [G. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 3.
-/

public section

namespace TauCeti

namespace YoungTableau

private abbrev rowBlocks (l : List ℕ) : Type :=
  Σ i : Fin l.length, Fin (l.get i)

private noncomputable def rowCellsEquiv (μ : YoungDiagram) :
    rowBlocks μ.rowLens ≃ ↥μ.cells where
  toFun x := ⟨(x.1, x.2), by
    rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, ← YoungDiagram.get_rowLens]
    exact x.2.isLt⟩
  invFun c :=
    ⟨⟨c.val.1, by
      rw [YoungDiagram.length_rowLens]
      exact (_root_.YoungDiagram.mem_iff_lt_colLen.mp c.property).trans_le
        (μ.colLen_anti 0 c.val.2 c.val.2.zero_le)⟩,
      ⟨c.val.2, by
        have hj := _root_.YoungDiagram.mem_iff_lt_rowLen.mp c.property
        rw [← YoungDiagram.get_rowLens] at hj
        exact hj⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def sortedBlocksEquivRows (μ : YoungDiagram) :
    rowBlocks ((shapePartition μ).parts.sort (· ≥ ·)) ≃ rowBlocks μ.rowLens :=
  Equiv.cast (congrArg rowBlocks (shapePartition_parts_sort μ))

private theorem cast_rowBlocks_fst {l₁ l₂ : List ℕ} (h : l₁ = l₂)
    (x : rowBlocks l₁) :
    ((Equiv.cast (congrArg rowBlocks h) x).1 : ℕ) = x.1 := by
  subst l₂
  rfl

private theorem cast_rowBlocks_snd {l₁ l₂ : List ℕ} (h : l₁ = l₂)
    (x : rowBlocks l₁) :
    ((Equiv.cast (congrArg rowBlocks h) x).2 : ℕ) = x.2 := by
  subst l₂
  rfl

private theorem sortedBlocksEquivRows_fst (μ : YoungDiagram)
    (x : rowBlocks ((shapePartition μ).parts.sort (· ≥ ·))) :
    ((sortedBlocksEquivRows μ x).1 : ℕ) = x.1 :=
  cast_rowBlocks_fst (shapePartition_parts_sort μ) x

private theorem sortedBlocksEquivRows_snd (μ : YoungDiagram)
    (x : rowBlocks ((shapePartition μ).parts.sort (· ≥ ·))) :
    ((sortedBlocksEquivRows μ x).2 : ℕ) = x.2 :=
  cast_rowBlocks_snd (shapePartition_parts_sort μ) x

/-- The permutation carrying the consecutive-block labeling of a Young diagram to the labeling
of `t`. It sends each block of the shape partition to the correspondingly numbered row of `t`. -/
noncomputable def rowYoungConjugator {μ : YoungDiagram} (t : YoungTableau μ) :
    Equiv.Perm (Fin μ.card) :=
  (youngBlocksEquiv (shapePartition μ)).symm |>.trans <|
    (sortedBlocksEquivRows μ).trans ((rowCellsEquiv μ).trans t)

/-- The row of a label after applying `rowYoungConjugator t` is its consecutive-block number. -/
@[simp]
theorem rowIndex_rowYoungConjugator {μ : YoungDiagram} (t : YoungTableau μ)
    (k : Fin μ.card) :
    rowIndex t (rowYoungConjugator t k) =
      youngBlock (shapePartition μ) k := by
  let x := (youngBlocksEquiv (shapePartition μ)).symm k
  have hk : youngBlocksEquiv (shapePartition μ) x = k :=
    Equiv.apply_symm_apply _ k
  rw [← hk, youngBlock_youngBlocksEquiv]
  simp only [rowYoungConjugator, Equiv.trans_apply, rowIndex_apply, rowCellsEquiv,
    Equiv.symm_apply_apply, x]
  exact sortedBlocksEquivRows_fst μ x

-- Not `@[simp]`: with `shapePartition_parts` and `Multiset.coe_sort` in the default simp set,
-- the left-hand side is no longer in simp normal form (the sorted parts reduce to `μ.rowLens`),
-- so the tag would be a `simpNF` violation. The lemma is for explicit `rw`/`exact` use.
/-- On consecutive-block coordinates, `rowYoungConjugator t` sends position `j` in block `i`
to the label in position `j` of row `i` of `t`. -/
theorem rowYoungConjugator_youngBlocksEquiv {μ : YoungDiagram} (t : YoungTableau μ)
    (x : Σ i : Fin
        ((shapePartition μ).parts.sort (· ≥ ·)).length,
      Fin (((shapePartition μ).parts.sort (· ≥ ·)).get i)) :
    rowYoungConjugator t
        (youngBlocksEquiv (shapePartition μ) x) =
      t ⟨(x.1, x.2), by
        rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
        let y := sortedBlocksEquivRows μ x
        calc
          (x.2 : ℕ) = y.2 := (sortedBlocksEquivRows_snd μ x).symm
          _ < μ.rowLens.get y.1 := y.2.isLt
          _ = μ.rowLen y.1 := YoungDiagram.get_rowLens
          _ = μ.rowLen x.1 := congrArg μ.rowLen (sortedBlocksEquivRows_fst μ x)⟩ := by
  simp only [rowYoungConjugator, Equiv.trans_apply, Equiv.symm_apply_apply]
  apply congrArg t
  apply Subtype.ext
  apply Prod.ext
  · exact sortedBlocksEquivRows_fst μ x
  · exact sortedBlocksEquivRows_snd μ x

/-- Relabeling a tableau translates its conjugator on the left: the consecutive-block labeling is
carried to the relabeled tableau by first carrying it to `t` and then applying `σ`. -/
@[simp]
theorem rowYoungConjugator_relabel {μ : YoungDiagram} (σ : Equiv.Perm (Fin μ.card))
    (t : YoungTableau μ) :
    rowYoungConjugator (relabel σ t) = σ * rowYoungConjugator t := by
  have h : relabel σ t = t.trans σ := Equiv.ext fun c => relabel_apply σ t c
  simp only [rowYoungConjugator, Equiv.Perm.mul_def, Equiv.trans_assoc, h]

/-- `rowYoungConjugator` determines the tableau: two `μ`-tableaux with the same conjugator are
equal. -/
theorem rowYoungConjugator_injective {μ : YoungDiagram} :
    Function.Injective (rowYoungConjugator (μ := μ)) := by
  intro t u h
  obtain ⟨σ, rfl⟩ := exists_relabel_eq t u
  have hσ : σ = 1 := mul_right_cancel
    ((rowYoungConjugator_relabel σ t).symm.trans (h.symm.trans (one_mul _).symm))
  rw [hσ, relabel_one]

/-- Conjugation by `rowYoungConjugator t` carries the Young subgroup of the shape partition
onto the row group of `t`. -/
theorem youngSubgroup_map_conj_eq_rowSubgroup {μ : YoungDiagram} (t : YoungTableau μ) :
    (youngSubgroup (shapePartition μ)).map
        (MulAut.conj (rowYoungConjugator t)).toMonoidHom = rowSubgroup t := by
  rw [youngSubgroup_eq_fiberSubgroup, rowSubgroup_def]
  apply fiberSubgroup_map_conj
  intro a b
  simp only [rowIndex_rowYoungConjugator]
  exact Fin.ext_iff

/-- Conjugation by `rowYoungConjugator t` as a multiplicative equivalence from the Young
subgroup of the shape partition to the row group of `t`. -/
noncomputable def youngSubgroupConjMulEquiv {μ : YoungDiagram} (t : YoungTableau μ) :
    youngSubgroup (shapePartition μ) ≃*
      rowSubgroup t :=
  ((MulAut.conj (rowYoungConjugator t)).subgroupMap
      (youngSubgroup (shapePartition μ))).trans
    (MulEquiv.subgroupCongr (youngSubgroup_map_conj_eq_rowSubgroup t))

/-- The subgroup equivalence acts by conjugation with `rowYoungConjugator t`. -/
@[simp]
theorem youngSubgroupConjMulEquiv_apply_coe {μ : YoungDiagram} (t : YoungTableau μ)
    (σ : youngSubgroup (shapePartition μ)) :
    ((youngSubgroupConjMulEquiv t σ : rowSubgroup t) : Equiv.Perm (Fin μ.card)) =
      rowYoungConjugator t * σ * (rowYoungConjugator t)⁻¹ :=
  by
    simp [youngSubgroupConjMulEquiv]
    rfl

/-- The inverse subgroup equivalence acts by conjugation with the inverse of
`rowYoungConjugator t`. -/
@[simp]
theorem youngSubgroupConjMulEquiv_symm_apply_coe {μ : YoungDiagram} (t : YoungTableau μ)
    (τ : rowSubgroup t) :
    (((youngSubgroupConjMulEquiv t).symm τ :
        youngSubgroup (shapePartition μ)) :
      Equiv.Perm (Fin μ.card)) =
      (rowYoungConjugator t)⁻¹ * τ * rowYoungConjugator t := by
  simp [youngSubgroupConjMulEquiv]
  rfl

/-! ### Normalization on the row-superstandard tableau -/

/-- **The row-superstandard tableau has trivial Young conjugator:** reading order agrees on the nose
with the consecutive-block enumeration of `shapePartition μ`. -/
@[simp]
theorem rowYoungConjugator_rowSuperstandard (μ : YoungDiagram) :
    rowYoungConjugator (StandardYoungTableau.rowSuperstandard μ).toTableau = 1 := by
  ext k
  obtain ⟨x, rfl⟩ := (youngBlocksEquiv (shapePartition μ)).surjective k
  rw [rowYoungConjugator_youngBlocksEquiv, StandardYoungTableau.toTableau_apply,
    StandardYoungTableau.rowSuperstandard_apply_val, Equiv.Perm.one_apply,
    YoungDiagram.readingIndex_def, youngBlocksEquiv_apply]
  congr 1
  have hpart : ∀ j : Fin ((shapePartition μ).parts.sort (· ≥ ·)).length,
      ((shapePartition μ).parts.sort (· ≥ ·)).get j = μ.rowLen j.val := fun j => by
    rw [List.get_eq_getElem, ← List.getD_eq_getElem _ 0 j.isLt, ← YoungDiagram.rowLen_ofPartition,
      ofPartition_shapePartition]
  calc
    ∑ i ∈ Finset.range x.1, μ.rowLen i
        = ∑ i : Fin x.1, μ.rowLen (i : ℕ) := (Fin.sum_univ_eq_sum_range μ.rowLen x.1).symm
    _ = ∑ i : Fin x.1,
          ((shapePartition μ).parts.sort (· ≥ ·)).get (Fin.castLE x.1.isLt.le i) :=
        Finset.sum_congr rfl fun i _ => (hpart (Fin.castLE x.1.isLt.le i)).symm

/-- Every `μ`-tableau is obtained from the row-superstandard tableau by relabeling with its
`rowYoungConjugator`. -/
@[simp]
theorem relabel_rowYoungConjugator_rowSuperstandard {μ : YoungDiagram} (t : YoungTableau μ) :
    relabel (rowYoungConjugator t) (StandardYoungTableau.rowSuperstandard μ).toTableau = t :=
  rowYoungConjugator_injective <| by
    rw [rowYoungConjugator_relabel, rowYoungConjugator_rowSuperstandard, mul_one]

/-- In the row-superstandard tableau, the row index of each label is its consecutive-block index in
`shapePartition μ`. -/
@[simp]
theorem rowIndex_rowSuperstandard (μ : YoungDiagram) (k : Fin μ.card) :
    rowIndex (StandardYoungTableau.rowSuperstandard μ).toTableau k =
      youngBlock (shapePartition μ) k := by
  have h := rowIndex_rowYoungConjugator (StandardYoungTableau.rowSuperstandard μ).toTableau k
  rwa [rowYoungConjugator_rowSuperstandard, Equiv.Perm.one_apply] at h

/-- **The row group of the row-superstandard tableau is `youngSubgroup (shapePartition μ)`.** -/
@[simp]
theorem rowSubgroup_rowSuperstandard (μ : YoungDiagram) :
    rowSubgroup (StandardYoungTableau.rowSuperstandard μ).toTableau =
      youngSubgroup (shapePartition μ) := by
  ext σ
  simp [← youngSubgroup_map_conj_eq_rowSubgroup]

end YoungTableau

end TauCeti

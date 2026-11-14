/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.RowStandardTableau
public import TauCeti.RepresentationTheory.Symmetric.Specht.Module
public import TauCeti.RepresentationTheory.Symmetric.YoungSubgroup.Parabolic

/-!
# Row-standard tableaux, minimal coset representatives, and tabloids

Every `μ`-tableau `t` determines its conjugator `TauCeti.YoungTableau.rowYoungConjugator t`, the
permutation of `Fin μ.card` carrying the consecutive-block labeling of `shapePartition μ` to `t`.
This file proves that:

1. on the row-superstandard tableau `StandardYoungTableau.rowSuperstandard μ`, the conjugator is `1`
   and the row group is `youngSubgroup (shapePartition μ)` on the nose;
2. `rowYoungConjugator` identifies row-standard `μ`-tableaux bijectively with the minimal
   left-coset representatives of `(permCoxeterSystem μ.card).parabolic
   (youngParabolicSet (shapePartition μ))` (`TauCeti.RowStandardTableau.minimalCosetRepEquiv`);
3. `YoungTableau.tabloid` identifies row-standard `μ`-tableaux
   `Equiv.Perm (Fin μ.card)`-equivariantly with the left cosets
   `Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ)`
   (`TauCeti.RowStandardTableau.tabloidEquiv`);
4. for a row-standard tableau `t` and a simple reflection `s_i`, `s_i * rowYoungConjugator t` is
   minimal in its left coset if and only if `i` and `i + 1` lie in distinct rows of `t`, and `i` is
   a left descent of `rowYoungConjugator t` if and only if `i + 1` lies in a strictly higher
   (smaller-numbered) row of `t` than `i`.

Together with `TauCeti.TypeAHeckeAlgebra.permutationModuleBasis`, these equivalences and descent
criteria translate the parabolic Hecke basis and generator formulas directly into the combinatorial
row-standard-tableau basis of Dipper–James and Mathas.

## Main definitions

* `TauCeti.RowStandardTableau.ofIsMinimalCosetRep`: the row-standard tableau obtained by relabeling
  the row-superstandard tableau by a minimal left-coset representative.
* `TauCeti.RowStandardTableau.minimalCosetRepEquiv`: the equivalence between `RowStandardTableau μ`
  and minimal left-coset representatives of `youngParabolicSet (shapePartition μ)`.
* `TauCeti.RowStandardTableau.tabloidEquiv`: the `S_n`-equivariant equivalence between
  `RowStandardTableau μ` and `Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ)`.

## Main results

* `TauCeti.YoungTableau.rowYoungConjugator_rowSuperstandard` and
  `TauCeti.YoungTableau.rowSubgroup_rowSuperstandard`: normalization on the row-superstandard
  tableau.
* `TauCeti.RowStandardTableau.rowYoungConjugator_smul`: `rowYoungConjugator` intertwines the
  `S_n`-action on `RowStandardTableau μ` with `CoxeterSystem.minimalCosetRep`.
* `TauCeti.RowStandardTableau.isMinimalCosetRep_transposition_mul_rowYoungConjugator_iff` and
  `TauCeti.RowStandardTableau.isLeftDescent_rowYoungConjugator_iff`: the combinatorial criteria for
  minimal left multiplication and left descents on row-standard tableaux.

## References

* R. Dipper and G. James, *Representations of Hecke algebras of general linear groups*,
  Proc. London Math. Soc. (3) 52 (1986), 20–52, Section 3.
* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999), Lemma 3.3 and Lemma 3.4.
-/

public section

namespace TauCeti

open BraidGroup

namespace YoungTableau

/-- `rowYoungConjugator` determines the tableau: two `μ`-tableaux with the same conjugator are
equal. -/
theorem rowYoungConjugator_injective {μ : YoungDiagram} :
    Function.Injective (rowYoungConjugator (μ := μ)) := by
  intro t u h
  obtain ⟨σ, rfl⟩ := exists_relabel_eq t u
  have hσ : σ = 1 := mul_right_cancel
    ((rowYoungConjugator_relabel σ t).symm.trans (h.symm.trans (one_mul _).symm))
  rw [hσ, relabel_one]

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
      ((shapePartition μ).parts.sort (· ≥ ·)).get j = μ.rowLen j.1 := fun j => by
    rw [List.get_eq_getElem, ← List.getD_eq_getElem _ 0 j.2, ← YoungDiagram.rowLen_ofPartition,
      ofPartition_shapePartition]
  calc
    ∑ i ∈ Finset.range x.1, μ.rowLen i
        = ∑ i : Fin x.1, μ.rowLen (i : ℕ) := (Fin.sum_univ_eq_sum_range μ.rowLen x.1).symm
    _ = ∑ i : Fin x.1,
          ((shapePartition μ).parts.sort (· ≥ ·)).get (Fin.castLE x.1.2.le i) :=
        Finset.sum_congr rfl fun i _ => (hpart (Fin.castLE x.1.2.le i)).symm

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

/-- The tabloid of the row-superstandard tableau is the identity coset of
`youngSubgroup (shapePartition μ)`. -/
@[simp]
theorem tabloid_rowSuperstandard (μ : YoungDiagram) :
    tabloid (StandardYoungTableau.rowSuperstandard μ).toTableau = QuotientGroup.mk 1 := by
  rw [tabloid_def, rowYoungConjugator_rowSuperstandard]

end YoungTableau

namespace RowStandardTableau

variable {μ : YoungDiagram}

/-! ### Equivalence with minimal left-coset representatives -/

/-- The Young conjugator of a row-standard tableau is a minimal left-coset representative for
`youngParabolicSet (shapePartition μ)`. -/
theorem isMinimalCosetRep_rowYoungConjugator (t : RowStandardTableau μ) :
    (permCoxeterSystem μ.card).IsMinimalCosetRep
      (youngParabolicSet (shapePartition μ))
      (YoungTableau.rowYoungConjugator t.toTableau) := by
  rw [isMinimalCosetRep_youngParabolicSet_iff]
  intro a b hblk hab
  obtain ⟨⟨i, j₁⟩, rfl⟩ := (youngBlocksEquiv (shapePartition μ)).surjective a
  obtain ⟨⟨i', j₂⟩, rfl⟩ := (youngBlocksEquiv (shapePartition μ)).surjective b
  rw [youngBlock_youngBlocksEquiv, youngBlock_youngBlocksEquiv] at hblk
  dsimp only at hblk
  subst i'
  rcases (youngBlocksEquiv_lt_youngBlocksEquiv_iff (shapePartition μ)).mp hab with hlt | ⟨-, hj⟩
  · exact absurd hlt (lt_irrefl _)
  · rw [YoungTableau.rowYoungConjugator_youngBlocksEquiv,
      YoungTableau.rowYoungConjugator_youngBlocksEquiv, toTableau_apply, toTableau_apply]
    exact t.row_strict hj _

/-- Relabeling the row-superstandard tableau by a minimal left-coset representative `d` for
`youngParabolicSet (shapePartition μ)` produces a row-standard tableau directly, without sorting. -/
noncomputable def ofIsMinimalCosetRep {d : Equiv.Perm (Fin μ.card)}
    (hd : (permCoxeterSystem μ.card).IsMinimalCosetRep
      (youngParabolicSet (shapePartition μ)) d) :
    RowStandardTableau μ where
  toTableau := YoungTableau.relabel d (StandardYoungTableau.rowSuperstandard μ).toTableau
  row_strict' {i j₁ j₂} hlt hcell := by
    simp only [YoungTableau.relabel_apply]
    set s := StandardYoungTableau.rowSuperstandard μ
    set c₁ : ↥μ.cells := ⟨(i, j₁), μ.up_left_mem le_rfl hlt.le hcell⟩
    set c₂ : ↥μ.cells := ⟨(i, j₂), hcell⟩
    have hblk : youngBlock (shapePartition μ) (s.toTableau c₁) =
        youngBlock (shapePartition μ) (s.toTableau c₂) := by
      apply Fin.ext
      rw [← YoungTableau.rowIndex_rowSuperstandard, ← YoungTableau.rowIndex_rowSuperstandard,
        YoungTableau.rowIndex_apply, YoungTableau.rowIndex_apply]
    exact (isMinimalCosetRep_youngParabolicSet_iff (shapePartition μ) d).mp hd hblk
      (s.row_strict hlt hcell)

/-- The underlying tableau of `ofIsMinimalCosetRep hd` is `relabel d` applied to the
row-superstandard tableau. -/
@[simp]
theorem toTableau_ofIsMinimalCosetRep {d : Equiv.Perm (Fin μ.card)}
    (hd : (permCoxeterSystem μ.card).IsMinimalCosetRep
      (youngParabolicSet (shapePartition μ)) d) :
    (ofIsMinimalCosetRep hd).toTableau =
      YoungTableau.relabel d (StandardYoungTableau.rowSuperstandard μ).toTableau :=
  (rfl)

/-- **Bijection between row-standard `μ`-tableaux and minimal left-coset representatives of
`youngParabolicSet (shapePartition μ)`.** -/
noncomputable def minimalCosetRepEquiv (μ : YoungDiagram) :
    RowStandardTableau μ ≃
      {d : Equiv.Perm (Fin μ.card) //
        (permCoxeterSystem μ.card).IsMinimalCosetRep
          (youngParabolicSet (shapePartition μ)) d} where
  toFun t := ⟨YoungTableau.rowYoungConjugator t.toTableau, t.isMinimalCosetRep_rowYoungConjugator⟩
  invFun d := ofIsMinimalCosetRep d.2
  left_inv t := by
    refine ext fun c => ?_
    rw [← toTableau_apply, toTableau_ofIsMinimalCosetRep,
      YoungTableau.relabel_rowYoungConjugator_rowSuperstandard, toTableau_apply]
  right_inv _ := Subtype.ext (by simp)

/-- `minimalCosetRepEquiv` sends a row-standard tableau to its Young conjugator. -/
@[simp]
theorem minimalCosetRepEquiv_apply_coe (t : RowStandardTableau μ) :
    (minimalCosetRepEquiv μ t : Equiv.Perm (Fin μ.card)) =
      YoungTableau.rowYoungConjugator t.toTableau :=
  (rfl)

/-- The inverse of `minimalCosetRepEquiv` constructs `ofIsMinimalCosetRep`. -/
@[simp]
theorem minimalCosetRepEquiv_symm_apply
    (d : {d : Equiv.Perm (Fin μ.card) //
      (permCoxeterSystem μ.card).IsMinimalCosetRep
        (youngParabolicSet (shapePartition μ)) d}) :
    (minimalCosetRepEquiv μ).symm d = ofIsMinimalCosetRep d.2 :=
  (rfl)

/-- `minimalCosetRepEquiv` sends the row-superstandard tableau to `1`. -/
@[simp]
theorem minimalCosetRepEquiv_rowSuperstandard (μ : YoungDiagram) :
    minimalCosetRepEquiv μ (rowSuperstandard μ) =
      ⟨1, (permCoxeterSystem μ.card).isMinimalCosetRep_one _⟩ := by
  apply Subtype.ext
  rw [minimalCosetRepEquiv_apply_coe, rowSuperstandard_toTableau,
    YoungTableau.rowYoungConjugator_rowSuperstandard]

/-- **Acting on a row-standard tableau sends its Young conjugator to the minimal coset
representative of the translated conjugator.** -/
theorem rowYoungConjugator_smul (σ : Equiv.Perm (Fin μ.card)) (t : RowStandardTableau μ) :
    YoungTableau.rowYoungConjugator (σ • t).toTableau =
      (permCoxeterSystem μ.card).minimalCosetRep
        (youngParabolicSet (shapePartition μ))
        (σ * YoungTableau.rowYoungConjugator t.toTableau) := by
  rw [(permCoxeterSystem μ.card).eq_minimalCosetRep_iff]
  refine ⟨(σ • t).isMinimalCosetRep_rowYoungConjugator, ?_⟩
  rw [parabolic_youngParabolicSet_eq_youngSubgroup,
    ← YoungTableau.rowYoungConjugator_relabel σ t.toTableau,
    ← QuotientGroup.eq, ← YoungTableau.tabloid_def, ← YoungTableau.tabloid_def,
    YoungTableau.tabloid_eq_iff_rowIndex_eq, smul_def, YoungTableau.rowIndex_rowStandardize]

/-! ### Equivariant equivalence with tabloids -/

/-- **Bijection between row-standard `μ`-tableaux and `μ`-tabloids.** -/
noncomputable def tabloidEquiv (μ : YoungDiagram) :
    RowStandardTableau μ ≃ Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ) :=
  Equiv.ofBijective (fun t => YoungTableau.tabloid t.toTableau)
    ⟨fun t u h => by
      rwa [YoungTableau.tabloid_eq_iff_rowIndex_eq, rowIndex_eq_iff] at h,
    fun q => by
      obtain ⟨t₀, rfl⟩ := YoungTableau.tabloid_surjective q
      refine ⟨YoungTableau.rowStandardize t₀, ?_⟩
      rw [YoungTableau.tabloid_eq_iff_rowIndex_eq, YoungTableau.rowIndex_rowStandardize]⟩

/-- `tabloidEquiv` evaluates `YoungTableau.tabloid` on the underlying tableau. -/
@[simp]
theorem tabloidEquiv_apply (t : RowStandardTableau μ) :
    tabloidEquiv μ t = YoungTableau.tabloid t.toTableau :=
  (rfl)

/-- Acting on a row-standard tableau acts by left translation on its tabloid. -/
@[simp]
theorem tabloid_smul (σ : Equiv.Perm (Fin μ.card)) (t : RowStandardTableau μ) :
    YoungTableau.tabloid (σ • t).toTableau = σ • YoungTableau.tabloid t.toTableau := by
  rw [← YoungTableau.tabloid_relabel, YoungTableau.tabloid_eq_iff_rowIndex_eq, smul_def,
    YoungTableau.rowIndex_rowStandardize]

/-- `tabloidEquiv` is `Equiv.Perm (Fin μ.card)`-equivariant. -/
theorem tabloidEquiv_smul (σ : Equiv.Perm (Fin μ.card)) (t : RowStandardTableau μ) :
    tabloidEquiv μ (σ • t) = σ • tabloidEquiv μ t := by
  simp

/-- The number of row-standard `μ`-tableaux is the multinomial index `|μ|! / ∏ i, μ_i!`. -/
theorem card_rowStandardTableau (μ : YoungDiagram) :
    Fintype.card (RowStandardTableau μ) =
      μ.card.factorial / ((shapePartition μ).parts.map Nat.factorial).prod := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (tabloidEquiv μ),
    ← Subgroup.index_eq_card, youngSubgroup_index]

/-! ### Simple reflections and left descents on row-standard tableaux -/

/-- When `i` and `i + 1` lie in distinct rows of `t`, left multiplication by `s_i` agrees with
acting by `s_i` on `t` without row re-sorting. -/
theorem transposition_mul_rowYoungConjugator_of_rowIndex_ne {t : RowStandardTableau μ}
    {i : Fin (μ.card - 1)}
    (h : YoungTableau.rowIndex t.toTableau (strand i) ≠
      YoungTableau.rowIndex t.toTableau (strandSucc i)) :
    transposition i * YoungTableau.rowYoungConjugator t.toTableau =
      YoungTableau.rowYoungConjugator (transposition i • t).toTableau := by
  rw [← YoungTableau.rowYoungConjugator_relabel, transposition_eq_swap,
    ← toTableau_swap_smul_of_rowIndex_ne (by simp) h]

/-- **Minimality of `s_i * rowYoungConjugator t`:** left multiplication by `s_i` stays minimal in
its Young coset if and only if strands `i` and `i + 1` occupy distinct rows of `t`. -/
theorem isMinimalCosetRep_transposition_mul_rowYoungConjugator_iff
    (t : RowStandardTableau μ) (i : Fin (μ.card - 1)) :
    (permCoxeterSystem μ.card).IsMinimalCosetRep
      (youngParabolicSet (shapePartition μ))
      (transposition i * YoungTableau.rowYoungConjugator t.toTableau) ↔
        YoungTableau.rowIndex t.toTableau (strand i) ≠
          YoungTableau.rowIndex t.toTableau (strandSucc i) := by
  refine ⟨fun hmin hrow => ?_, fun hne => ?_⟩
  · have hfix : transposition i • t = t := by
      rw [transposition_eq_swap]
      exact swap_smul_eq_self_of_rowIndex_eq hrow
    have heq := rowYoungConjugator_smul (transposition i) t
    rw [hfix, hmin.minimalCosetRep_eq (permCoxeterSystem μ.card)] at heq
    have htr : transposition i = 1 := mul_right_cancel (heq.symm.trans (one_mul _).symm)
    have hst := Equiv.Perm.congr_fun htr (strand i)
    rw [transposition_apply_strand, Equiv.Perm.one_apply] at hst
    exact strand_ne_strandSucc i hst.symm
  · rw [transposition_mul_rowYoungConjugator_of_rowIndex_ne hne]
    exact (transposition i • t).isMinimalCosetRep_rowYoungConjugator

/-- **Left descents of `rowYoungConjugator t`:** `i` is a left descent of `rowYoungConjugator t` if
and only if `strandSucc i` (`i + 1`) lies in a strictly smaller-numbered (higher) row of `t` than
`strand i` (`i`). -/
theorem isLeftDescent_rowYoungConjugator_iff
    (t : RowStandardTableau μ) (i : Fin (μ.card - 1)) :
    (permCoxeterSystem μ.card).IsLeftDescent
      (YoungTableau.rowYoungConjugator t.toTableau) i ↔
        YoungTableau.rowIndex t.toTableau (strandSucc i) <
          YoungTableau.rowIndex t.toTableau (strand i) := by
  set d := YoungTableau.rowYoungConjugator t.toTableau
  rw [isLeftDescent_permCoxeterSystem_iff]
  have hx : YoungTableau.rowIndex t.toTableau (strandSucc i) =
      youngBlock (shapePartition μ) (d⁻¹ (strandSucc i)) := by
    have h := YoungTableau.rowIndex_rowYoungConjugator t.toTableau (d⁻¹ (strandSucc i))
    simpa only [d, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h
  have hy : YoungTableau.rowIndex t.toTableau (strand i) =
      youngBlock (shapePartition μ) (d⁻¹ (strand i)) := by
    have h := YoungTableau.rowIndex_rowYoungConjugator t.toTableau (d⁻¹ (strand i))
    simpa only [d, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h
  rw [hx, hy, ← Fin.lt_def]
  refine ⟨fun hlt => ?_, fun hlt => ?_⟩
  · refine lt_of_le_of_ne (youngBlock_mono (shapePartition μ) hlt.le) fun hblk => ?_
    have hdlt := (isMinimalCosetRep_youngParabolicSet_iff (shapePartition μ) d).mp
      t.isMinimalCosetRep_rowYoungConjugator hblk hlt
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hdlt
    exact lt_asymm hdlt (Fin.lt_def.mpr (by simp))
  · by_contra hle
    exact not_le_of_gt hlt (youngBlock_mono (shapePartition μ) (not_lt.mp hle))

end RowStandardTableau

end TauCeti

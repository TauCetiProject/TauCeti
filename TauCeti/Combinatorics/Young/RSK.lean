/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Partitions
public import TauCeti.Combinatorics.Young.Schensted.Shape
public import TauCeti.Combinatorics.Young.StandardTableau.LatticeWord
public import TauCeti.Combinatorics.Young.StandardTableau.Rows
public import TauCeti.GroupTheory.Perm.List

/-!
# The Robinson--Schensted correspondence for permutations

The Robinson--Schensted correspondence sends a permutation of `Fin n`, written in one-line
notation, to its insertion and recording tableaux. Both tableaux are standard, have the same
shape, and every pair of standard tableaux of the same shape arises uniquely in this way.

This file packages the word-level correspondence `TauCeti.robinsonSchenstedEquiv` as the
classical equivalence between permutations and pairs of standard Young tableaux. The insertion
tableau is decoded from its rows using `StandardYoungTableau.rowsEquiv`; the recording tableau is
decoded from the recording lattice word using `StandardYoungTableau.latticeWordEquiv`.

## References

* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), Section 4.1.
* B. E. Sagan, *The Symmetric Group*, second edition, Springer GTM 203 (2001), Section 3.1.
-/

public section

namespace TauCeti

open List

private def castRows {m n : ℕ} (h : m = n) (rows : List (List (Fin n))) :
    List (List (Fin m)) := by
  subst n
  exact rows

private theorem isTableauRows_castRows {m n : ℕ} (h : m = n)
    {rows : List (List (Fin n))} (hrows : rows.IsTableauRows) :
    (castRows h rows).IsTableauRows := by
  subst n
  exact hrows

private theorem map_length_castRows {m n : ℕ} (h : m = n)
    (rows : List (List (Fin n))) :
    (castRows h rows).map length = rows.map length := by
  subst n
  rfl

private theorem flatten_castRows_perm {m n : ℕ} (h : m = n)
    {rows : List (List (Fin n))} (hperm : rows.flatten.Perm (finRange n)) :
    (castRows h rows).flatten.Perm (finRange m) := by
  subst n
  exact hperm

private theorem map_val_castRows {m n : ℕ} (h : m = n) (rows : List (List (Fin n))) :
    (castRows h rows).map (map Fin.val) = rows.map (map Fin.val) := by
  subst n
  rfl

private def castStandardYoungTableau {μ ν : YoungDiagram} (h : μ = ν)
    (T : StandardYoungTableau μ) : StandardYoungTableau ν := by
  subst ν
  exact T

private theorem toRows_castStandardYoungTableau {μ ν : YoungDiagram} (h : μ = ν)
    (T : StandardYoungTableau μ) :
    (castStandardYoungTableau h T).toRows =
      castRows (congrArg YoungDiagram.card h).symm T.toRows := by
  subst ν
  rfl

private theorem rowWord_castStandardYoungTableau {μ ν : YoungDiagram} (h : μ = ν)
    (T : StandardYoungTableau μ) :
    (castStandardYoungTableau h T).rowWord = T.rowWord := by
  subst ν
  rfl

private noncomputable def rskMap {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Σ μ : n.Partition,
      StandardYoungTableau (YoungDiagram.ofPartition μ) ×
        StandardYoungTableau (YoungDiagram.ofPartition μ) := by
  let w := List.ofFn σ
  let p := robinsonSchensted w
  have hp : p.1.IsTableauRows := isTableauRows_robinsonSchensted_fst w
  let ν := tableauShape p.1 hp
  have hcard : ν.card = n := by
    rw [card_tableauShape]
    exact (flatten_robinsonSchensted_fst_perm w).length_eq.trans (by simp [w])
  let μ := ν.toPartition hcard
  let rows := castRows hcard p.1
  have hrows : rows.IsTableauRows := isTableauRows_castRows hcard hp
  have hshape : rows.map length = ν.rowLens := by
    rw [map_length_castRows]
    exact (rowLens_tableauShape p.1 hp).symm
  have hw : w.Perm (finRange n) := by
    simpa [w, List.ofFn_eq_map] using σ.map_finRange_perm
  let P : StandardYoungTableau ν := (StandardYoungTableau.rowsEquiv ν).symm
    ⟨rows, hrows, hshape,
      flatten_castRows_perm hcard ((flatten_robinsonSchensted_fst_perm w).trans hw)⟩
  let Q : StandardYoungTableau ν := (StandardYoungTableau.latticeWordEquiv ν).symm
    ⟨p.2, isLatticeWord_robinsonSchensted_snd w, fun i => by
      rw [← length_getD_robinsonSchensted_fst w]
      rw [← YoungDiagram.getD_rowLens, ← hshape, map_length_castRows]
      exact (getD_map p.1 [] (n := i) length).symm⟩
  have hμ : YoungDiagram.ofPartition μ = ν := YoungDiagram.ofPartition_toPartition hcard
  exact ⟨μ, castStandardYoungTableau hμ.symm P, castStandardYoungTableau hμ.symm Q⟩

private def rskData {n : ℕ}
    (x : Σ μ : n.Partition,
      StandardYoungTableau (YoungDiagram.ofPartition μ) ×
        StandardYoungTableau (YoungDiagram.ofPartition μ)) :
    List (List ℕ) × List ℕ :=
  (x.2.1.toRows.map (map Fin.val), x.2.2.rowWord)

private theorem rskData_rskMap {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    rskData (rskMap σ) =
      ((robinsonSchensted (List.ofFn σ)).1.map (map Fin.val),
        (robinsonSchensted (List.ofFn σ)).2) := by
  simp [rskData, rskMap, toRows_castStandardYoungTableau,
    rowWord_castStandardYoungTableau, StandardYoungTableau.toRows_rowsEquiv_symm,
    StandardYoungTableau.rowWord_latticeWordEquiv_symm, map_val_castRows]

private theorem rskData_injective {n : ℕ} : Function.Injective
    (rskData : (Σ μ : n.Partition,
      StandardYoungTableau (YoungDiagram.ofPartition μ) ×
        StandardYoungTableau (YoungDiagram.ofPartition μ)) → List (List ℕ) × List ℕ) := by
  rintro ⟨μ, P, Q⟩ ⟨ν, R, S⟩ h
  have hrowLens : (YoungDiagram.ofPartition μ).rowLens =
      (YoungDiagram.ofPartition ν).rowLens := by
    have := congrArg (map length) (congrArg Prod.fst h)
    simpa [rskData, List.map_map, Function.comp_def] using this
  have hdiagram : YoungDiagram.ofPartition μ = YoungDiagram.ofPartition ν := by
    apply YoungDiagram.equivListRowLens.injective
    exact Subtype.ext hrowLens
  have hμ : μ = ν := YoungDiagram.ofPartition_injective hdiagram
  subst ν
  have hP : P = R := by
    apply StandardYoungTableau.toRows_injective
    apply (List.map_injective_iff.mpr
      (List.map_injective_iff.mpr Fin.val_injective))
    exact congrArg Prod.fst h
  have hQ : Q = S := by
    apply StandardYoungTableau.rowWord_injective
    exact congrArg Prod.snd h
  subst R
  subst S
  rfl

private theorem rskMap_injective {n : ℕ} : Function.Injective (rskMap (n := n)) := by
  intro σ τ h
  have hdata := congrArg rskData h
  rw [rskData_rskMap, rskData_rskMap] at hdata
  have hins : (robinsonSchensted (List.ofFn σ)).1 =
      (robinsonSchensted (List.ofFn τ)).1 := by
    apply (List.map_injective_iff.mpr
      (List.map_injective_iff.mpr Fin.val_injective))
    exact congrArg Prod.fst hdata
  have hrec : (robinsonSchensted (List.ofFn σ)).2 =
      (robinsonSchensted (List.ofFn τ)).2 := by
    exact congrArg (fun z : List (List ℕ) × List ℕ => z.2) hdata
  have hword : List.ofFn σ = List.ofFn τ :=
    robinsonSchensted_injective (Prod.ext hins hrec)
  exact Equiv.ext fun i => congrFun (List.ofFn_injective hword) i

private theorem rskMap_surjective {n : ℕ} : Function.Surjective (rskMap (n := n)) := by
  rintro ⟨μ, P, Q⟩
  let rows := castRows (YoungDiagram.card_ofPartition μ).symm P.toRows
  have hrows : rows.IsTableauRows :=
    isTableauRows_castRows (YoungDiagram.card_ofPartition μ).symm P.isTableauRows_toRows
  have hcontent : rows.flatten.Perm (finRange n) :=
    flatten_castRows_perm (YoungDiagram.card_ofPartition μ).symm P.flatten_toRows_perm
  have hshape (i : ℕ) : (rows.getD i []).length = Q.rowWord.count i := by
    rw [Q.count_rowWord, ← YoungDiagram.getD_rowLens,
      ← P.map_length_toRows, ← map_length_castRows]
    exact (getD_map rows [] (n := i) length).symm
  obtain ⟨w, hwRS⟩ := (exists_robinsonSchensted_eq_iff (p := (rows, Q.rowWord))).mpr
    ⟨hrows, Q.isLatticeWord_rowWord, hshape⟩
  have hw : w.Perm (finRange n) := by
    have hletters := flatten_robinsonSchensted_fst_perm w
    rw [hwRS] at hletters
    exact hletters.symm.trans hcontent
  obtain ⟨σ, hσ⟩ := (permutationWordEquiv n).surjective ⟨w, hw⟩
  refine ⟨σ, rskData_injective ?_⟩
  have hword : List.ofFn σ = w := by
    have := congrArg Subtype.val hσ
    simpa only [permutationWordEquiv_apply_coe] using this
  rw [rskData_rskMap, hword, hwRS]
  simp [rskData, rows, map_val_castRows]

/-- The **Robinson--Schensted correspondence for permutations**: permutations of `Fin n`
correspond to pairs of standard Young tableaux of the same shape, where the shape ranges over
the partitions of `n`. -/
noncomputable def rsk (n : ℕ) :
    Equiv.Perm (Fin n) ≃ Σ μ : n.Partition,
      StandardYoungTableau (YoungDiagram.ofPartition μ) ×
        StandardYoungTableau (YoungDiagram.ofPartition μ) :=
  Equiv.ofBijective rskMap ⟨rskMap_injective, rskMap_surjective⟩

/-- The entries in the rows of the insertion tableau are the entries produced by word-level
Robinson--Schensted insertion. The `Fin` labels are compared through their natural-number values
because the tableau labels are indexed by the cardinality of its inferred shape. -/
@[simp]
theorem map_val_toRows_rsk_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((rsk n σ).2.1.toRows.map (map Fin.val)) =
      (robinsonSchensted (List.ofFn σ)).1.map (map Fin.val) := by
  exact congrArg Prod.fst (rskData_rskMap σ)

/-- The recording tableau of a permutation has the recording word produced by word-level
Robinson--Schensted insertion. -/
@[simp]
theorem rowWord_rsk_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (rsk n σ).2.2.rowWord = (robinsonSchensted (List.ofFn σ)).2 := by
  exact congrArg Prod.snd (rskData_rskMap σ)

/-- The shape of the tableaux in `rsk n σ` is the row-length shape of the insertion tableau. -/
theorem rowLens_ofPartition_rsk_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (YoungDiagram.ofPartition (rsk n σ).1).rowLens =
      (robinsonSchensted (List.ofFn σ)).1.map length := by
  calc
    _ = (rsk n σ).2.1.toRows.map length :=
      ((rsk n σ).2.1.map_length_toRows).symm
    _ = _ := by
      have h := congrArg (map length) (map_val_toRows_rsk_apply σ)
      simpa only [List.map_map, Function.comp_def, List.length_map] using h

end TauCeti

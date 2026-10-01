/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.Partition.Conjugate
public import TauCeti.Combinatorics.Young.Diagram
public import TauCeti.Combinatorics.Young.Tableau

/-!
# The dominance lemma for tableaux

Two tableaux of different shapes can be compared by asking how the rows of one meet the columns
of the other.  The **dominance lemma** says that if the labels of each row of a `μ`-tableau `s`
land in pairwise distinct columns of a `ν`-tableau `t`, then `ν` dominates `μ`.

The proof is a double count.  Write the labels of the first `k` rows of `s` as a set `X`; it has
`μ₁ + ⋯ + μ_k` elements.  Inside a fixed column of `t` each of those `k` rows contributes at most
one label, so `X` meets that column in at most `k` labels, and of course in at most as many
labels as the column is long.  Summing over the columns of `t`, the cells of `ν` in its first `k`
rows -- of which there are exactly `min k (colLen j)` in column `j` -- already accommodate `X`,
so `μ₁ + ⋯ + μ_k ≤ ν₁ + ⋯ + ν_k`.

The counting itself is `YoungDiagram.card_filter_le_sum_take_rowLens`, stated for an
arbitrary finite index type carrying a row function and an injection into the cells: this is what
the tableau statement, where the index type is the set of labels, unfolds to, and it keeps the
counting free of any tableau bookkeeping.  The lemma is the combinatorial engine behind the
triangularity of the Specht modules in the dominance order: a homomorphism from the Specht module
`S^ν` into the permutation module `M^μ` is nonzero only when `ν` dominates `μ`, because the
column antisymmetrizer of a `ν`-tableau kills every `μ`-tabloid unless the row/column condition
below holds.

## Main results

* `TauCeti.YoungTableau.sum_take_rowLens_le_of_injective`: the dominance lemma for two tableaux.
* `TauCeti.dominates_of_rowIndex_colIndex_injective`: the dominance lemma for partitions.
* `TauCeti.exists_ne_rowIndex_eq_colIndex_eq_of_not_dominates`: its contrapositive, producing two
  distinct labels sharing a row of `s` and a column of `t` when dominance fails.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Lemma 3.15.
* B. E. Sagan, *The Symmetric Group*, 2nd edition (2001), Lemma 2.2.4.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "Distinctness and completeness".
-/

public section

namespace TauCeti

namespace YoungTableau

variable {lam m : YoungDiagram}

/-- **The dominance lemma.** Let `s` be an `m`-tableau and `t` a `lam`-tableau whose labels are
identified by `σ`.  If the labels of each row of `s` occupy pairwise distinct columns of `t`,
then every partial sum of the row lengths of `m` is at most the corresponding partial sum for
`lam`.

The hypothesis says that no row of `s` meets a column of `t` in two distinct labels, once the
labels are matched up by `σ`. -/
theorem sum_take_rowLens_le_of_injective (t : YoungTableau lam) (s : YoungTableau m)
    (σ : Fin m.card ≃ Fin lam.card)
    (h : ∀ x y, rowIndex s x = rowIndex s y → colIndex t (σ x) = colIndex t (σ y) → x = y)
    (k : ℕ) : (m.rowLens.take k).sum ≤ (lam.rowLens.take k).sum := by
  classical
  rw [← card_filter_rowIndex_lt s k]
  refine YoungDiagram.card_filter_le_sum_take_rowLens lam (rowIndex s)
    (fun x => ((t.symm (σ x) : ↥lam.cells) : ℕ × ℕ)) (fun x => (t.symm (σ x)).2)
    (fun x y hxy => σ.injective (t.symm.injective (Subtype.ext hxy))) (fun x y hr hc => ?_) k
  exact h x y hr (by simpa only [colIndex_def] using hc)

end YoungTableau

open YoungTableau in
/-- **The dominance lemma for partitions.** If the labels of each row of a `μ`-tableau `s` land
in pairwise distinct columns of a `ν`-tableau `t`, along an identification `σ` of their labels,
then `ν` dominates `μ`. -/
theorem dominates_of_rowIndex_colIndex_injective {n : ℕ} {μ ν : n.Partition}
    (t : YoungTableau (diagramOf ν)) (s : YoungTableau (diagramOf μ))
    (σ : Fin (diagramOf μ).card ≃ Fin (diagramOf ν).card)
    (h : ∀ x y, rowIndex s x = rowIndex s y → colIndex t (σ x) = colIndex t (σ y) → x = y) :
    Dominates ν μ := by
  refine dominates_iff.mpr fun k => ?_
  simpa only [rowLens_diagramOf] using sum_take_rowLens_le_of_injective t s σ h k

open YoungTableau in
/-- **The contrapositive of the dominance lemma.** When `ν` fails to dominate `μ`, every
`ν`-tableau has a column meeting a row of every `μ`-tableau in two distinct labels. -/
theorem exists_ne_rowIndex_eq_colIndex_eq_of_not_dominates {n : ℕ} {μ ν : n.Partition}
    (t : YoungTableau (diagramOf ν)) (s : YoungTableau (diagramOf μ))
    (σ : Fin (diagramOf μ).card ≃ Fin (diagramOf ν).card) (h : ¬Dominates ν μ) :
    ∃ x y, x ≠ y ∧ rowIndex s x = rowIndex s y ∧ colIndex t (σ x) = colIndex t (σ y) := by
  by_contra hcon
  refine h (dominates_of_rowIndex_colIndex_injective t s σ fun x y hr hc => ?_)
  by_contra hxy
  exact hcon ⟨x, y, hxy, hr, hc⟩

end TauCeti

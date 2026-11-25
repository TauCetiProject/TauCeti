/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Addable
public import TauCeti.Combinatorics.Young.Partitions
public import TauCeti.Combinatorics.Young.StandardTableau.Basic
import TauCeti.Combinatorics.Young.StandardTableau.Order

/-!
# Separation of standard tableaux by transformed contents

A function on integer contents which separates the addable cells of every smaller Young
diagram also separates standard tableaux, including tableaux of different shapes. This gives a
combinatorial criterion for distinguishing simultaneous tableau eigenvalues.

## References

* A. Okounkov and A. Vershik, *A new approach to representation theory of symmetric groups*,
  Selecta Math. (N.S.) 2 (1996), 581–605, §5, DOI: 10.1007/BF02433451, for reconstruction
  from ordinary contents along the Young graph. The criterion here allows transformed contents.
-/

public section

namespace TauCeti.StandardYoungTableau

open YoungTableau

variable {n : ℕ}

/-- Transformed label contents determine a standard tableau and its partition shape whenever
the transformation separates the addable cells of every diagram of smaller cardinality. -/
theorem sigma_comp_labelContent_injective_of_injOn_addables {A : Type*} (f : ℤ → A)
    (hf : ∀ μ : YoungDiagram, μ.card < n →
      Set.InjOn (fun c ↦ f (YoungDiagram.cellContent c)) {c | YoungDiagram.IsAddable μ c}) :
    Function.Injective (fun T : (Σ μ : n.Partition,
        StandardYoungTableau (YoungDiagram.ofPartition μ)) => fun i : Fin n =>
      f (labelContent T.2.toTableau (Fin.cast (YoungDiagram.card_ofPartition T.1).symm i))) := by
  rintro ⟨p, T⟩ ⟨q, U⟩ hTU
  let cell (r : n.Partition) (V : StandardYoungTableau (YoungDiagram.ofPartition r))
      (i : Fin n) :=
    let j := Fin.cast (YoungDiagram.card_ofPartition r).symm i
    (rowIndex V.toTableau j, colIndex V.toTableau j)
  have hprefix_mem {r : n.Partition} (V : StandardYoungTableau (YoungDiagram.ofPartition r))
      (i : Fin n) (c : ℕ × ℕ) :
      c ∈ V.initialDiagram (Fin.cast (YoungDiagram.card_ofPartition r).symm i) ↔
        ∃ j < i, cell r V j = c := by
    rw [mem_initialDiagram]
    constructor
    · rintro ⟨j, hj, h⟩
      exact ⟨Fin.cast (YoungDiagram.card_ofPartition r) j, hj, by
        simpa only [cell, Fin.cast_cast, Fin.cast_refl, id_eq] using h⟩
    · rintro ⟨j, hj, h⟩
      exact ⟨Fin.cast (YoungDiagram.card_ofPartition r).symm j, hj, h⟩
  have hcell (i : Fin n) : cell p T i = cell q U i := by
    induction i using WellFoundedLT.induction with
    | _ i ih =>
      have hprefix : T.initialDiagram (Fin.cast (YoungDiagram.card_ofPartition p).symm i) =
          U.initialDiagram (Fin.cast (YoungDiagram.card_ofPartition q).symm i) := by
        apply SetLike.ext
        intro c
        rw [hprefix_mem, hprefix_mem]
        exact exists_congr fun j => and_congr_right fun hj => by rw [ih j hj]
      exact hf _ (by simpa only [card_initialDiagram, Fin.val_cast] using i.isLt)
        (T.isAddable_initialDiagram _) (hprefix ▸ U.isAddable_initialDiagram _)
        (by simpa only [cell, YoungDiagram.cellContent_mk, labelContent_eq_colIndex_sub_rowIndex]
          using congrFun hTU i)
  have hmem {r : n.Partition} (V : StandardYoungTableau (YoungDiagram.ofPartition r))
      (c : ℕ × ℕ) : c ∈ YoungDiagram.ofPartition r ↔ ∃ i, cell r V i = c := by
    constructor
    · rcases c with ⟨a, b⟩
      intro hc
      obtain ⟨i, ha, hb⟩ := exists_rowIndex_colIndex V.toTableau hc
      exact ⟨Fin.cast (YoungDiagram.card_ofPartition r) i, by
        simpa only [cell, Fin.cast_cast, Fin.cast_refl, id_eq] using Prod.ext ha hb⟩
    · rintro ⟨i, rfl⟩
      exact rowIndex_colIndex_mem V.toTableau _
  have hpq : p = q := YoungDiagram.ofPartition_injective (SetLike.ext fun c => by
    simp only [hmem T c, hmem U c, hcell])
  subst q
  congr 1
  apply toTableau_injective
  apply Equiv.symm_bijective.injective
  apply Equiv.ext
  intro i
  apply Subtype.ext
  simpa only [cell, Fin.cast_cast, Fin.cast_refl, id_eq, rowIndex_def, colIndex_def, Prod.mk.eta]
    using hcell (Fin.cast (YoungDiagram.card_ofPartition p) i)

end TauCeti.StandardYoungTableau

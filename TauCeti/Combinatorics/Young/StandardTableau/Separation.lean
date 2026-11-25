/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Addable
public import TauCeti.Combinatorics.Young.Partitions
public import TauCeti.Combinatorics.Young.StandardTableau.Basic
import Mathlib.Order.Interval.Finset.Fin
import TauCeti.Combinatorics.Young.StandardTableau.Order

/-!
# Separation of standard tableaux by transformed contents

A function on integer contents which separates the addable cells of every smaller Young
diagram also separates standard tableaux, including tableaux of different shapes. This gives a
combinatorial criterion for distinguishing simultaneous tableau eigenvalues.
-/

public section

namespace TauCeti.StandardYoungTableau

variable {n : ℕ} {μ ν : YoungDiagram}

private def labelCell (hμ : μ.card = n) (T : StandardYoungTableau μ) (i : Fin n) : ℕ × ℕ :=
  T.toTableau.symm (Fin.cast hμ.symm i)

private theorem labelCell_injective (hμ : μ.card = n) (T : StandardYoungTableau μ) :
    Function.Injective (labelCell hμ T) := by
  intro i j hij
  exact (Fin.cast_injective hμ.symm) (T.toTableau.symm.injective (Subtype.ext hij))

private theorem labelCell_mem (hμ : μ.card = n) (T : StandardYoungTableau μ) (i : Fin n) :
    labelCell hμ T i ∈ μ :=
  (T.toTableau.symm (Fin.cast hμ.symm i)).property

private theorem exists_labelCell_eq_of_le (hμ : μ.card = n) (T : StandardYoungTableau μ)
    (i : Fin n) {c : ℕ × ℕ} (hci : c ≤ labelCell hμ T i) :
    ∃ j ≤ i, labelCell hμ T j = c := by
  have hc : c ∈ μ := μ.isLowerSet hci (labelCell_mem hμ T i)
  let j : Fin n := Fin.cast hμ (T ⟨c, hc⟩)
  have hj : labelCell hμ T j = c := by
    simp only [labelCell, j, Fin.cast_cast, Fin.cast_refl, ← toTableau_apply,
      id_eq, Equiv.symm_apply_apply]
  refine ⟨j, ?_, hj⟩
  by_cases h : c = labelCell hμ T i
  · exact (le_of_eq (labelCell_injective hμ T (hj.trans h)))
  · have hlt := T.apply_lt_apply_of_le (c := ⟨c, hc⟩)
      (d := T.toTableau.symm (Fin.cast hμ.symm i)) hci.1 hci.2
      (fun he => h (congrArg Subtype.val he))
    rw [← toTableau_apply T, ← toTableau_apply T, Equiv.apply_symm_apply] at hlt
    simpa only [j, Fin.le_def, Fin.val_cast, toTableau_apply] using hlt.le

private def initialDiagram (hμ : μ.card = n) (T : StandardYoungTableau μ) (i : Fin n) :
    YoungDiagram where
  cells := (Finset.Iio i).image (labelCell hμ T)
  isLowerSet := by
    intro c d hcd hd
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨k, hkj, hk⟩ := exists_labelCell_eq_of_le hμ T j hcd
    exact Finset.mem_image.mpr ⟨k, Finset.mem_Iio.mpr (hkj.trans_lt
      (Finset.mem_Iio.mp hj)), hk⟩

private theorem initialDiagram_card (hμ : μ.card = n) (T : StandardYoungTableau μ)
    (i : Fin n) : (initialDiagram hμ T i).card = i.val := by
  simp [YoungDiagram.card, initialDiagram, Finset.card_image_of_injective,
    labelCell_injective hμ T]

private theorem isAddable_initialDiagram (hμ : μ.card = n) (T : StandardYoungTableau μ)
    (i : Fin n) : YoungDiagram.IsAddable (initialDiagram hμ T i) (labelCell hμ T i) := by
  rw [YoungDiagram.isAddable_def]
  refine ⟨?_, ?_⟩
  · intro hi
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_Iio.mp hj).ne (labelCell_injective hμ T hji)
  · intro c hci
    obtain ⟨j, hji, hj⟩ := exists_labelCell_eq_of_le hμ T i hci.le
    have hne : j ≠ i := fun h => hci.ne (hj.symm.trans (congrArg (labelCell hμ T) h))
    exact Finset.mem_image.mpr ⟨j, Finset.mem_Iio.mpr (lt_of_le_of_ne hji hne), hj⟩

private theorem labelCell_eq_of_transformedContent_eq {A : Type*} (f : ℤ → A)
    (hf : ∀ ρ : YoungDiagram, ρ.card < n →
      Set.InjOn (fun c ↦ f (YoungDiagram.cellContent c)) {c | YoungDiagram.IsAddable ρ c})
    (hμ : μ.card = n) (hν : ν.card = n) (T : StandardYoungTableau μ)
    (U : StandardYoungTableau ν)
    (hTU : ∀ i, f (YoungDiagram.cellContent (labelCell hμ T i)) =
      f (YoungDiagram.cellContent (labelCell hν U i))) :
    ∀ i, labelCell hμ T i = labelCell hν U i := by
  intro i
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    have hprefix : initialDiagram hμ T i = initialDiagram hν U i := by
      apply YoungDiagram.ext
      exact Finset.image_congr fun j hj => ih j (Finset.mem_Iio.mp hj)
    exact hf _ (by rw [initialDiagram_card]; exact i.isLt)
      (isAddable_initialDiagram hμ T i)
      (hprefix ▸ isAddable_initialDiagram hν U i) (hTU i)

private theorem mem_iff_exists_labelCell (hμ : μ.card = n) (T : StandardYoungTableau μ)
    (c : ℕ × ℕ) : c ∈ μ ↔ ∃ i, labelCell hμ T i = c := by
  refine ⟨fun hc => ⟨Fin.cast hμ (T ⟨c, hc⟩), ?_⟩, ?_⟩
  · simp only [labelCell, Fin.cast_cast, Fin.cast_refl, ← toTableau_apply,
      id_eq, Equiv.symm_apply_apply]
  · rintro ⟨i, rfl⟩
    exact labelCell_mem hμ T i

/-- Transformed label contents determine a standard tableau and its partition shape whenever
the transformation separates the addable cells of every diagram of smaller cardinality. -/
theorem injective_labelContent_of_injOn_addables {A : Type*} (f : ℤ → A)
    (hf : ∀ μ : YoungDiagram, μ.card < n →
      Set.InjOn (fun c ↦ f (YoungDiagram.cellContent c)) {c | YoungDiagram.IsAddable μ c}) :
    Function.Injective (fun T : (Σ μ : n.Partition,
        StandardYoungTableau (YoungDiagram.ofPartition μ)) => fun i : Fin n =>
      f (YoungTableau.labelContent T.2.toTableau
        (Fin.cast (YoungDiagram.card_ofPartition T.1).symm i))) := by
  rintro ⟨p, T⟩ ⟨q, U⟩ hTU
  have hcell := labelCell_eq_of_transformedContent_eq f hf
    (YoungDiagram.card_ofPartition p) (YoungDiagram.card_ofPartition q) T U
    (fun i => by simpa only [YoungTableau.labelContent_def, labelCell] using congrFun hTU i)
  have hshape : YoungDiagram.ofPartition p = YoungDiagram.ofPartition q := by
    apply SetLike.ext
    intro c
    simp_rw [mem_iff_exists_labelCell (YoungDiagram.card_ofPartition p) T,
      mem_iff_exists_labelCell (YoungDiagram.card_ofPartition q) U, hcell]
  have hpq := YoungDiagram.ofPartition_injective hshape
  subst q
  congr 1
  apply toTableau_injective
  apply Equiv.symm_bijective.injective
  apply Equiv.ext
  intro i
  apply Subtype.ext
  simpa [labelCell] using hcell (Fin.cast (YoungDiagram.card_ofPartition p) i)

end TauCeti.StandardYoungTableau

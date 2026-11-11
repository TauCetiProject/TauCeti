/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Copying a CW complex with new characteristic maps

The axioms of a CW complex see a characteristic map `map n i` only through its values on the
closed unit ball and the values of its inverse on the open cell. So the characteristic maps can be
replaced by any partial equivalences with source the open unit ball which agree with them on the
closed unit ball: the inverses then agree on the open cells as well. `Topology.CWComplex.copy`
makes this replacement, keeping the cells (`Topology.CWComplex.copyCellEquiv`), and allows the
carrier to be replaced by an equal set at the same time.

This adjusts the data of a CW structure off its closed cells without changing anything visible on
them. For instance, the characteristic maps can be normalized to depend only on their values, so
that CW structures built independently on different subsets agree on a common cell.
-/

public section

noncomputable section

open Metric Set Topology.RelCWComplex

namespace Topology.CWComplex

variable {X : Type*} [TopologicalSpace X] {C : Set X} [CWComplex C] (C' : Set X) (hC : C' = C)
  (φ : ∀ n, cell C n → PartialEquiv (Fin n → ℝ) X) (hsource : ∀ n i, (φ n i).source = ball 0 1)
  (hφ : ∀ n i, EqOn (φ n i) (map n i) (closedBall 0 1))

/-- **A copy of a CW complex.** The CW structure on `C' = C` with the cells of `C` and
characteristic maps `φ n i`, which have source the open unit ball and agree with those of `C` on
the closed unit ball. -/
@[instance_reducible]
def copy : CWComplex C' :=
  have himg (n : ℕ) (i : cell C n) : φ n i '' closedBall 0 1 = map n i '' closedBall 0 1 :=
    (hφ n i).image_eq
  have hball (n : ℕ) (i : cell C n) : φ n i '' ball 0 1 = map n i '' ball 0 1 :=
    ((hφ n i).mono ball_subset_closedBall).image_eq
  { cell := cell C
    map := φ
    source_eq := hsource
    continuousOn n i := (RelCWComplex.continuousOn n i).congr (hφ n i)
    continuousOn_symm n i := by
      have ht : (φ n i).target = (map n i).target := by
        rw [← (φ n i).image_source_eq_target, ← (map n i).image_source_eq_target, hsource,
          source_eq, hball]
      rw [ht]
      -- On the open cell both inverses invert the same injective map on the open ball.
      refine (RelCWComplex.continuousOn_symm n i).congr fun y hy ↦ ?_
      have hy' : y ∈ (φ n i).target := ht ▸ hy
      have hx : (φ n i).symm y ∈ ball 0 1 := hsource n i ▸ (φ n i).map_target hy'
      calc (φ n i).symm y = (map n i).symm (map n i ((φ n i).symm y)) := by
            rw [(map n i).left_inv (by rwa [source_eq])]
        _ = (map n i).symm y := by
            rw [← hφ n i (ball_subset_closedBall hx), (φ n i).right_inv hy']
    pairwiseDisjoint' := by
      simpa only [openCell, hball] using RelCWComplex.pairwiseDisjoint (C := C)
    mapsTo' n i := by
      obtain ⟨S, hS⟩ := CWComplex.mapsTo (C := C) n i
      refine ⟨S, ?_⟩
      simpa only [closedCell, himg] using hS.congr ((hφ n i).mono sphere_subset_closedBall).symm
    closed' A hAC hA :=
      RelCWComplex.closed' (C := C) A (hC ▸ hAC) ⟨fun n i ↦ himg n i ▸ hA n i, by simp⟩
    union' := by
      simpa only [closedCell, himg, hC] using CWComplex.union (C := C) }

/-- The cells of a copy of a CW complex are its cells. -/
def copyCellEquiv (n : ℕ) :
    @cell X _ C' ∅ (@instRelCWComplex X _ C' (copy C' hC φ hsource hφ)) n ≃ cell C n :=
  Equiv.refl _

/-- The characteristic maps of a copy of a CW complex are the new maps `φ`. -/
@[simp]
theorem map_copy (n : ℕ)
    (i : @cell X _ C' ∅ (@instRelCWComplex X _ C' (copy C' hC φ hsource hφ)) n) :
    @map X _ C' ∅ (@instRelCWComplex X _ C' (copy C' hC φ hsource hφ)) n i =
      φ n (copyCellEquiv C' hC φ hsource hφ n i) :=
  (rfl)

end Topology.CWComplex

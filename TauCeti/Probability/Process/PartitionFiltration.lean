/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Process.PartitionFiltration
public import TauCeti.MeasureTheory.MeasurableSpace.Finpartition

/-!
# Square filtrations from finite measurable partitions

The canonical finite partitions of a countably generated measurable space give a filtration on
its square by recording the partition part of each coordinate. These square σ-algebras increase
to the full product σ-algebra. This is the filtration naturally used by block-average
approximations of measurable kernels.

## Main results

* `TauCeti.MeasureTheory.countableSquareFiltration` is the filtration by equal-level
  product partitions.
* `TauCeti.MeasureTheory.iSup_countableSquareFiltration` says that it generates the
  product σ-algebra.
* `TauCeti.MeasureTheory.countableSquareFiltration_eq_comap` identifies each level with
  the information carried by the pair of finite-partition indices.
-/

public section

noncomputable section

open MeasurableSpace ProbabilityTheory

namespace TauCeti.MeasureTheory

variable {Ω : Type*} [m : MeasurableSpace Ω] [CountablyGenerated Ω]

/-- The filtration on `Ω × Ω` whose level `n` is the product of the level-`n` canonical finite
σ-algebra on each coordinate. -/
def countableSquareFiltration (Ω : Type*) [m : MeasurableSpace Ω]
    [CountablyGenerated Ω] : MeasureTheory.Filtration ℕ (m.prod m) where
  seq n := (countableFiltration Ω n).prod (countableFiltration Ω n)
  mono' _ _ h := by
    -- `rw` does not unfold the measurable-space products behind the filtration coercions.
    change
      (countableFiltration Ω _).comap Prod.fst ⊔
          (countableFiltration Ω _).comap Prod.snd ≤
        (countableFiltration Ω _).comap Prod.fst ⊔
          (countableFiltration Ω _).comap Prod.snd
    exact sup_le_sup
      (MeasurableSpace.comap_mono ((countableFiltration Ω).mono h))
      (MeasurableSpace.comap_mono ((countableFiltration Ω).mono h))
  le' n := by
    -- `rw` does not unfold the measurable-space product behind the filtration coercion.
    change
      (countableFiltration Ω n).comap Prod.fst ⊔
          (countableFiltration Ω n).comap Prod.snd ≤
        m.comap Prod.fst ⊔ m.comap Prod.snd
    exact sup_le_sup (MeasurableSpace.comap_mono ((countableFiltration Ω).le n))
      (MeasurableSpace.comap_mono ((countableFiltration Ω).le n))

/-- A level of the square filtration is the product of the corresponding canonical finite
σ-algebra with itself. -/
@[simp]
theorem countableSquareFiltration_apply (n : ℕ) :
    countableSquareFiltration Ω n =
      (countableFiltration Ω n).prod (countableFiltration Ω n) :=
  (rfl)

/-- The equal-level square filtration generates the full product σ-algebra. -/
theorem iSup_countableSquareFiltration :
    ⨆ n, countableSquareFiltration Ω n = m.prod m := by
  apply le_antisymm
  · exact iSup_le fun n => (countableSquareFiltration Ω).le n
  -- Unfolding the products separates the two coordinate generators of the full product space.
  · change m.comap Prod.fst ⊔ m.comap Prod.snd ≤
      ⨆ n, (countableFiltration Ω n).comap Prod.fst ⊔
        (countableFiltration Ω n).comap Prod.snd
    apply sup_le
    · have h := congrArg
          (fun m' : MeasurableSpace Ω => m'.comap (Prod.fst : Ω × Ω → Ω))
          (iSup_countableFiltration Ω)
      rw [← h, MeasurableSpace.comap_iSup]
      refine iSup_le fun n => le_iSup_of_le n ?_
      exact le_sup_left
    · have h := congrArg
          (fun m' : MeasurableSpace Ω => m'.comap (Prod.snd : Ω × Ω → Ω))
          (iSup_countableFiltration Ω)
      rw [← h, MeasurableSpace.comap_iSup]
      refine iSup_le fun n => le_iSup_of_le n ?_
      exact le_sup_right

/-- The product of the discrete σ-algebras on two countable types is discrete. -/
theorem prod_top_eq_top_of_countable (α β : Type*) [Countable α] [Countable β] :
    (⊤ : MeasurableSpace α).prod (⊤ : MeasurableSpace β) = ⊤ := by
  apply top_unique
  let _ : MeasurableSpace α := ⊤
  let _ : MeasurableSpace β := ⊤
  intro s _
  exact MeasurableSet.of_discrete

/-- A level of the square filtration is precisely the information carried by the two canonical
finite-partition indices. -/
theorem countableSquareFiltration_eq_comap (n : ℕ) :
    countableSquareFiltration Ω n =
      MeasurableSpace.comap
        (Prod.map (Finpartition.countablePartition Ω n).indexedPartition.index
          (Finpartition.countablePartition Ω n).indexedPartition.index) ⊤ := by
  -- Expose the filtration level so `comap_prodMap` can rewrite the pair of index maps.
  change (countableFiltration Ω n).prod (countableFiltration Ω n) = _
  rw [← prod_top_eq_top_of_countable,
    MeasurableSpace.comap_prodMap,
    Finpartition.comap_countablePartition_index_top]
  rfl

end TauCeti.MeasureTheory

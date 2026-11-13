/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import TauCeti.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Almost-everywhere equality of random measures from set evaluations

Two random measures that agree almost surely on each fixed measurable set need not agree almost
surely as measures when the ground σ-algebra is uncountably generated or when realizations take
infinite mass on every generating family. On a countably generated measurable space, however, a
countable measurable cover on which one of the random measures is almost surely finite reduces
equality of measures to countably many intersections with a countable generating π-system.

Unlike `MeasureTheory.Measure.map_eq_iff_forall_finset_map_eval_eq`, which identifies laws on the
Giry space, the criterion here upgrades individual setwise almost-everywhere equalities to a single
event of full measure on which the two realizations coincide on all measurable sets simultaneously.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- Two measures that agree on the intersections of a generating π-system (containing `univ`) with
each piece of a countable measurable cover on which the first measure is finite are equal. Total
mass may be infinite. -/
theorem ext_of_generate_of_cover {X : Type*} [mX : MeasurableSpace X] {μ ν : Measure X}
    {C : Set (Set X)} (hgen : mX = MeasurableSpace.generateFrom C) (hpi : IsPiSystem C)
    (huniv : univ ∈ C) {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n))
    (hcover : ⋃ n, s n = univ) (hfin : ∀ n, μ (s n) ≠ ∞)
    (heq : ∀ n, ∀ A ∈ C, μ (A ∩ s n) = ν (A ∩ s n)) : μ = ν := by
  have hC : ∀ A ∈ C, MeasurableSet A :=
    fun A hA ↦ hgen ▸ MeasurableSpace.measurableSet_generateFrom hA
  have hpiece (n : ℕ) : μ.restrict (s n) = ν.restrict (s n) := by
    have : IsFiniteMeasure (μ.restrict (s n)) := isFiniteMeasure_restrict.mpr (hfin n)
    refine ext_of_generate_finite C hgen hpi (fun A hA ↦ ?_) ?_
    · simp_rw [restrict_apply (hC A hA), heq n A hA]
    · simpa only [restrict_apply MeasurableSet.univ] using heq n univ huniv
  have hdisj (n : ℕ) : μ.restrict (disjointed s n) = ν.restrict (disjointed s n) := by
    rw [← restrict_restrict_of_subset (disjointed_le s n), hpiece n,
      restrict_restrict_of_subset (disjointed_le s n)]
  calc
    μ = Measure.sum (fun n ↦ μ.restrict (disjointed s n)) := by
      rw [← restrict_iUnion (disjoint_disjointed s) (MeasurableSet.disjointed hs),
        iUnion_disjointed, hcover, restrict_univ]
    _ = Measure.sum (fun n ↦ ν.restrict (disjointed s n)) := by simp_rw [hdisj]
    _ = ν := by
      rw [← restrict_iUnion (disjoint_disjointed s) (MeasurableSet.disjointed hs),
        iUnion_disjointed, hcover, restrict_univ]

/-- On a countably generated measurable space, setwise almost-everywhere equality of two random
measures upgrades to almost-everywhere equality of measures whenever one of them is almost surely
finite on each piece of a countable measurable cover. Neither measurability of the random measures
nor finite total mass is required. -/
theorem ae_eq_of_forall_ae_eq_of_cover {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X] {P : Measure Ω} {M₁ M₂ : Ω → Measure X}
    {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    (hfin : ∀ n, ∀ᵐ ω ∂P, M₁ ω (s n) ≠ ∞)
    (heq : ∀ A, MeasurableSet A → ∀ᵐ ω ∂P, M₁ ω A = M₂ ω A) : M₁ =ᵐ[P] M₂ := by
  obtain ⟨C, hcount, hpi, huniv, hgen⟩ :=
    MeasurableSpace.exists_countable_isPiSystem_generateFrom (α := X)
  have hC : ∀ A ∈ C, MeasurableSet A :=
    fun A hA ↦ hgen ▸ MeasurableSpace.measurableSet_generateFrom hA
  have hcounts : ∀ᵐ ω ∂P, ∀ n, ∀ A ∈ C, M₁ ω (A ∩ s n) = M₂ ω (A ∩ s n) :=
    ae_all_iff.2 fun n ↦ (ae_ball_iff hcount).2 fun A hA ↦ heq _ ((hC A hA).inter (hs n))
  filter_upwards [ae_all_iff.2 hfin, hcounts] with ω hωfin hωeq
  exact ext_of_generate_of_cover hgen hpi huniv hs hcover hωfin hωeq

end MeasureTheory.Measure

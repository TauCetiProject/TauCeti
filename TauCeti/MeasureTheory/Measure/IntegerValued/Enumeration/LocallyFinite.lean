/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.IntegerValued.Enumeration.Basic
public import TauCeti.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Measurable enumeration beyond finite measures

A measurable family of integer-valued measures admits a measurable occurrence enumeration
when there is a common countable measurable cover of finite mass. In particular, this applies
to measures finite on compact sets on a sigma-compact standard Borel space. Locations are
repeated according to their multiplicity, and summing the optional Dirac occurrences recovers
the measure exactly, even when its total mass is infinite.

The construction enumerates the finite restrictions to the disjoint pieces of the cover and
interleaves their enumerations. Consequently `none` can occur between actual occurrences;
it is not a signal that the enumeration has ended. This representation supplies the locations
for attaching independent marks to an infinite locally finite configuration.

For a fixed countable measurable cover, the locus of integer-valued measures finite on every
cover piece is itself measurable in `Measure X` on any countably generated space, so on a
standard Borel space there is a total measurable occurrence enumeration
`Measure X → ℕ → Option X` reconstructing every measure in that locus and returning `none`
outside it.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapters 5–6 (marking and measurable enumeration).
-/

public section

open MeasureTheory Set
open scoped ENNReal

/-- A measurable family of integer-valued measures with a common countable finite-mass
cover has a measurable enumeration of all its occurrences. The cover need not be increasing
or disjoint. Missing entries may be interspersed with actual occurrences. -/
theorem Measurable.exists_occurrence_enumeration_of_cover
    {α X : Type*} [MeasurableSpace α] [MeasurableSpace X] [StandardBorelSpace X]
    {μ : α → Measure X} (hm : Measurable μ)
    (hint : ∀ a, (μ a).IsIntegerValued) (s : ℕ → Set X)
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    (hfinite : ∀ a n, μ a (s n) ≠ ∞) :
    ∃ e : α → ℕ → Option X, Measurable e ∧
      ∀ a, μ a = Measure.sum (fun n => (e a n).elim 0 Measure.dirac) := by
  have hpiece (n : ℕ) : Measurable fun a => (μ a).restrict (disjointed s n) :=
    (ProbabilityTheory.Kernel.restrict ⟨μ, hm⟩ (MeasurableSet.disjointed hs n)).measurable
  have hfin (a : α) (n : ℕ) : IsFiniteMeasure ((μ a).restrict (disjointed s n)) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top (hfinite a n)
      (measure_mono (disjointed_le s n)))
  choose e he _ heq using fun n => (hpiece n).exists_finite_occurrence_enumeration
    (fun a => hfin a n) (fun a => (hint a).restrict)
  refine ⟨fun a k => e k.unpair.1 a k.unpair.2,
    measurable_pi_iff.2 (fun k => (measurable_pi_apply k.unpair.2).comp (he k.unpair.1)),
    fun a => ?_⟩
  calc
    μ a = Measure.sum (fun n => (μ a).restrict (disjointed s n)) := by
      rw [← Measure.restrict_iUnion (disjoint_disjointed s) (MeasurableSet.disjointed hs),
        iUnion_disjointed, hcover, Measure.restrict_univ]
    _ = Measure.sum (fun n => Measure.sum (fun k => (e n a k).elim 0 Measure.dirac)) := by
      simp_rw [heq]
    _ = Measure.sum (fun k : ℕ => (e k.unpair.1 a k.unpair.2).elim 0 Measure.dirac) := by
      rw [Measure.sum_sum]
      exact (Measure.sum_comp_equiv Nat.pairEquiv.symm _).symm

/-- A measurable family of integer-valued measures finite on compact sets on a sigma-compact
Hausdorff standard Borel space can be enumerated measurably, with multiplicities retained and no
finite-total-mass assumption. Missing entries may be interspersed with actual occurrences. -/
theorem Measurable.exists_occurrence_enumeration_of_isFiniteMeasureOnCompacts
    {α X : Type*} [MeasurableSpace α] [TopologicalSpace X] [T2Space X]
    [SigmaCompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [StandardBorelSpace X]
    {μ : α → Measure X} (hm : Measurable μ)
    (hfinite : ∀ a, IsFiniteMeasureOnCompacts (μ a))
    (hint : ∀ a, (μ a).IsIntegerValued) :
    ∃ e : α → ℕ → Option X, Measurable e ∧
      ∀ a, μ a = Measure.sum (fun n => (e a n).elim 0 Measure.dirac) :=
  hm.exists_occurrence_enumeration_of_cover hint (compactCovering X)
    (fun n => (isCompact_compactCovering X n).measurableSet) (iUnion_compactCovering X)
    (fun a n => by
      have := hfinite a
      exact (isCompact_compactCovering X n).measure_ne_top)

/-- An almost-everywhere measurable family of measures that are almost surely integer-valued and
almost surely finite on each set of a countable measurable cover admits a measurable occurrence
enumeration that recovers the family almost everywhere. -/
theorem AEMeasurable.exists_ae_occurrence_enumeration_of_cover
    {α X : Type*} [MeasurableSpace α] [MeasurableSpace X] [StandardBorelSpace X]
    {P : Measure α} {μ : α → Measure X} (hm : AEMeasurable μ P)
    (hint : ∀ᵐ a ∂P, (μ a).IsIntegerValued) (s : ℕ → Set X)
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    (hfinite : ∀ n, ∀ᵐ a ∂P, μ a (s n) ≠ ∞) :
    ∃ e : α → ℕ → Option X, Measurable e ∧
      ∀ᵐ a ∂P, μ a = Measure.sum (fun n => (e a n).elim 0 Measure.dirac) := by
  obtain ⟨μ', hμ', hrange, hae⟩ := hm.exists_ae_eq_range_subset
    (t := {ν : Measure X | ν.IsIntegerValued ∧ ∀ n, ν (s n) ≠ ∞})
    (hint.and (ae_all_iff.2 hfinite)) ⟨0, by simp⟩
  obtain ⟨e, he, heq⟩ := hμ'.exists_occurrence_enumeration_of_cover
    (fun a => (hrange (mem_range_self a)).1) s hs hcover
    (fun a n => (hrange (mem_range_self a)).2 n)
  exact ⟨e, he, hae.mono fun a ha => ha.trans (heq a)⟩

namespace MeasureTheory.Measure

/-- On a countably generated measurable space, the set of integer-valued measures giving finite
mass to every set in a countable measurable cover is measurable for the Giry σ-algebra. -/
theorem measurableSet_isIntegerValued_and_forall_ne_top
    {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
    {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ) :
    MeasurableSet {μ : Measure X | μ.IsIntegerValued ∧ ∀ n, μ (s n) ≠ ∞} := by
  classical
  obtain ⟨C, hcount, hpi, huniv, hgen⟩ :=
    MeasurableSpace.exists_countable_isPiSystem_generateFrom (α := X)
  have hCm : ∀ A ∈ C, MeasurableSet A :=
    fun _ hA => hgen ▸ MeasurableSpace.measurableSet_generateFrom hA
  have heq : {μ : Measure X | μ.IsIntegerValued ∧ ∀ n, μ (s n) ≠ ∞} =
      ⋂ n : ℕ, ⋂ A ∈ C, ⋃ k : ℕ, {μ : Measure X | μ (A ∩ s n) = k} := by
    ext μ
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · rintro ⟨hint, hfin⟩ n A hA
      exact hint.exists_eq_natCast ((hCm A hA).inter (hs n))
        ((measure_mono inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr (hfin n)))
    · intro h
      refine ⟨isIntegerValued_of_restrict hcover fun n => ?_, fun n => ?_⟩
      · refine isIntegerValued_of_isPiSystem hgen hpi (fun A hA => ?_) ?_
        · simpa only [Measure.restrict_apply (hCm A hA)] using h n A hA
        · simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using h n univ huniv
      · obtain ⟨k, hk⟩ := h n univ huniv
        rw [univ_inter] at hk
        simp [hk]
  rw [heq]
  refine MeasurableSet.iInter fun n => MeasurableSet.biInter hcount fun A hA =>
    MeasurableSet.iUnion fun k => ?_
  exact measurableSet_eq_fun (Measure.measurable_coe ((hCm A hA).inter (hs n))) measurable_const

/-- On a standard Borel space, every countable measurable cover admits a total measurable
occurrence enumeration of `Measure X` that reconstructs every integer-valued measure finite on
the cover and returns `none` at every index outside that locus. -/
theorem exists_occurrence_enumeration_of_cover
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ) :
    ∃ e : Measure X → ℕ → Option X, Measurable e ∧
      (∀ μ : Measure X, μ.IsIntegerValued → (∀ n, μ (s n) ≠ ∞) →
        μ = Measure.sum fun n => (e μ n).elim 0 Measure.dirac) ∧
      (∀ μ : Measure X, ¬ (μ.IsIntegerValued ∧ ∀ n, μ (s n) ≠ ∞) →
        ∀ n, e μ n = none) := by
  classical
  let S : Set (Measure X) := {μ : Measure X | μ.IsIntegerValued ∧ ∀ n, μ (s n) ≠ ∞}
  have hS : MeasurableSet S := measurableSet_isIntegerValued_and_forall_ne_top hs hcover
  let clean : Measure X → Measure X := fun μ => if μ ∈ S then μ else 0
  have hclean_meas : Measurable clean := Measurable.ite hS measurable_id measurable_const
  have hclean_int : ∀ μ, (clean μ).IsIntegerValued := fun μ => by
    dsimp [clean]
    split_ifs with h
    · exact h.1
    · exact isIntegerValued_zero
  have hclean_fin : ∀ μ n, clean μ (s n) ≠ ∞ := fun μ n => by
    dsimp [clean]
    split_ifs with h
    · exact h.2 n
    · simp
  obtain ⟨e, he, hrec⟩ :=
    hclean_meas.exists_occurrence_enumeration_of_cover hclean_int s hs hcover hclean_fin
  refine ⟨e, he, fun μ hμ hfin => ?_, fun μ hnot n => ?_⟩
  · have hmem : μ ∈ S := ⟨hμ, hfin⟩
    simpa only [clean, ite_eq_left hmem] using hrec μ
  · have hnmem : μ ∉ S := by simpa only [S, mem_ofPred_eq] using hnot
    have hzero : (0 : Measure X) = Measure.sum fun k => (e μ k).elim 0 Measure.dirac := by
      simpa only [clean, ite_eq_right hnmem] using hrec μ
    have hsum := Measure.sum_eq_zero.mp hzero.symm n
    cases h : e μ n with
    | none => rfl
    | some a => simp [h, Measure.dirac_ne_zero] at hsum

end MeasureTheory.Measure

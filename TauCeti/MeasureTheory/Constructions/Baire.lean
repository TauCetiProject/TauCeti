/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.UrysohnsLemma

/-!
# Baire sets and compact hulls

The Baire σ-algebra is the smallest σ-algebra making every continuous real-valued function
measurable. It is contained in the Borel σ-algebra, but the two need not coincide without
countability assumptions. This notion is different from having the Baire property (agreement
with an open set modulo a meagre set).

For an outer regular measure on a locally compact Hausdorff space, every compact set of
finite measure has a compact Baire-measurable superset of the same measure, inside any
prescribed open neighbourhood. The hull is a countable intersection of level sets of compactly
supported continuous functions. This supplies compact Baire approximations for comparing Borel
and Baire measure theory, in particular for Haar measures on groups without second countability.
It does not assert that every Borel set belongs to the completion of the Baire σ-algebra.

## References

* D. H. Fremlin, *Measure Theory*, §443, for the Baire and Borel comparison for Haar measures.
-/

public section

open Set MeasureTheory Filter Topology

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The Baire σ-algebra: the smallest σ-algebra making continuous real-valued functions
measurable. This is not the σ-algebra of sets with the Baire property. -/
@[instance_reducible]
def baire (X : Type*) [TopologicalSpace X] : MeasurableSpace X :=
  ⨆ f : C(X, ℝ), MeasurableSpace.comap f (borel ℝ)

/-- The defining universal property of the Baire σ-algebra. -/
theorem baire_le_iff {m : MeasurableSpace X} :
    baire X ≤ m ↔ ∀ f : C(X, ℝ), Measurable[m] f := by
  simp only [baire, iSup_le_iff, measurable_iff_comap_le, BorelSpace.measurable_eq]

/-- Every Baire set is Borel. -/
theorem baire_le_borel : baire X ≤ borel X :=
  baire_le_iff.2 fun f => f.continuous.borel_measurable

/-- A continuous real-valued function is measurable for the Baire σ-algebra. -/
theorem _root_.ContinuousMap.measurable_baire (f : C(X, ℝ)) :
    Measurable[TauCeti.baire X] f :=
  measurable_iff_comap_le.2 (le_iSup (fun f : C(X, ℝ) =>
    MeasurableSpace.comap f (borel ℝ)) f)

/-- Continuous maps are measurable between Baire σ-algebras. -/
theorem _root_.Continuous.measurable_baire {f : X → Y} (hf : Continuous f) :
    @Measurable X Y (TauCeti.baire X) (TauCeti.baire Y) f := by
  rw [measurable_iff_le_map, baire_le_iff]
  intro g
  exact (g.comp ⟨f, hf⟩).measurable_baire

/-- A compact set admits a compact Baire-measurable hull inside any open neighbourhood,
with null excess for any outer regular measure for which the compact set has finite measure.
No σ-finiteness or countability assumption on the space is needed. -/
theorem _root_.IsCompact.exists_baire_hull [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [μ.OuterRegular]
    {K U : Set X} (hK : IsCompact K) (hμK : μ K ≠ ⊤) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ B : Set X, K ⊆ B ∧ B ⊆ U ∧ IsCompact B ∧ MeasurableSet[baire X] B ∧
      μ (B \ K) = 0 := by
  -- Approximate from outside at errors tending to zero, then insert continuous cutoffs.
  have hopen (n : ℕ) := hK.measurableSet.exists_isOpen_sdiff_lt
    (μ := μ) hμK
    (ε := ENNReal.ofReal (1 / ((n : ℝ) + 1))) (by positivity)
  choose V hKV hV hVfin hVerr using hopen
  have hcut (n : ℕ) := exists_continuous_one_zero_of_isCompact hK
    ((hV n).inter hU).isClosed_compl
    (disjoint_compl_right_iff_subset.2 (subset_inter (hKV n) hKU))
  choose f hfK hfzero hfsupp hfrange using hcut
  let B : Set X := ⋂ n, (f n) ⁻¹' {1}
  have hKB : K ⊆ B := fun x hx => mem_iInter.2 fun n => hfK n hx
  have hBV (n : ℕ) : B ⊆ V n ∩ U := by
    intro x hx
    by_contra h
    have h1 : f n x = 1 := mem_iInter.1 hx n
    have h0 : f n x = 0 := hfzero n h
    exact zero_ne_one (h0.symm.trans h1)
  have hBclosed : IsClosed B := isClosed_iInter fun n =>
    isClosed_singleton.preimage (f n).continuous
  have hBcompact : IsCompact B := (hfsupp 0).of_isClosed_subset hBclosed fun x hx => by
    apply subset_tsupport (f 0)
    have hx1 : f 0 x = 1 := mem_iInter.1 hx 0
    simp [hx1]
  refine ⟨B, hKB, (hBV 0).trans inter_subset_right, hBcompact,
    MeasurableSet.iInter fun n => (f n).measurable_baire (measurableSet_singleton 1), ?_⟩
  have hbound (n : ℕ) : μ (B \ K) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    (measure_mono (sdiff_subset_sdiff_left ((hBV n).trans inter_subset_left))).trans
      (hVerr n).le
  apply le_zero_iff.1
  simpa only [ENNReal.ofReal_zero] using ge_of_tendsto'
    (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat) hbound

end TauCeti

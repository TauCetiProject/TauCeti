/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Measure on an orbit space from a fundamental domain

For a countable group acting measurably and preserving a measure `μ`, a fundamental domain
induces a measure on the orbit space. We use Mathlib's `QuotientMeasureEqMeasurePreimage` to
characterize this measure. Its total mass is the covolume, and a measurable set downstairs
is null exactly when its entire preimage upstairs is null, not just its part in the domain.
-/

public noncomputable section

open MulAction Set
open scoped Pointwise

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- The pushforward of `μ` restricted to a fundamental domain, on the orbit space.
For a countable measure-preserving action this measure is independent of the domain; see
`instQuotientMeasureEqMeasurePreimageOrbitQuotientMeasure`. -/
def orbitQuotientMeasure (G : Type*) [Group G] [MulAction G α] (μ : Measure α)
    [h : HasFundamentalDomain G α μ] : Measure (orbitRel.Quotient G α) :=
  (μ.restrict h.ExistsIsFundamentalDomain.choose).map (Quotient.mk (orbitRel G α))

variable {G : Type*} [Group G] [MulAction G α] {μ : Measure α} [HasFundamentalDomain G α μ]

/-- The total mass of the orbit measure is the covolume. -/
@[simp]
theorem orbitQuotientMeasure_univ : orbitQuotientMeasure G μ univ = covolume G α μ := by
  rw [orbitQuotientMeasure, measure_map_restrict_apply μ _ MeasurableSet.univ,
    preimage_univ, univ_inter, covolume, dite_eq_left ‹HasFundamentalDomain G α μ›]

variable [Countable G] [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]

/-- The orbit measure agrees with the pushforward from every fundamental domain. -/
instance instQuotientMeasureEqMeasurePreimageOrbitQuotientMeasure :
    QuotientMeasureEqMeasurePreimage μ (orbitQuotientMeasure G μ) :=
  let h := (HasFundamentalDomain.ExistsIsFundamentalDomain (G := G) (ν := μ)).choose_spec
  h.quotientMeasureEqMeasurePreimage_quotientMeasure

/-- A set in the orbit space is null if and only if its saturated preimage is null. -/
theorem orbitQuotientMeasure_apply_eq_zero_iff (s : Set (orbitRel.Quotient G α)) :
    orbitQuotientMeasure G μ s = 0 ↔ μ (Quotient.mk (orbitRel G α) ⁻¹' s) = 0 := by
  let p := Quotient.mk (orbitRel G α)
  obtain ⟨F, hF⟩ := HasFundamentalDomain.ExistsIsFundamentalDomain (G := G) (ν := μ)
  constructor
  · intro h
    obtain ⟨t, hst, ht, ht₀⟩ := exists_measurable_superset_of_null h
    rw [hF.projection_respects_measure_apply (orbitQuotientMeasure G μ) ht] at ht₀
    apply measure_mono_null (preimage_mono hst)
    refine hF.measure_zero_of_invariant (p ⁻¹' t) (fun g ↦ ?_) ht₀
    ext x
    simp [p, mem_smul_set_iff_inv_smul_mem, orbitRel.Quotient.quotient_smul_eq]
  · intro h
    obtain ⟨t, hst, ht, ht₀⟩ := exists_measurable_superset_of_null h
    have hsat : p ⁻¹' (p '' t) = ⋃ g : G, g • t :=
      MulAction.quotient_preimage_image_eq_union_mul t
    have hmeas : MeasurableSet (p '' t) := measurableSet_quotient.mpr <| by
      rw [hsat]
      exact .iUnion fun g ↦ ht.const_smul g
    have hsub : s ⊆ p '' t := (image_preimage_eq s Quotient.mk_surjective) ▸ image_mono hst
    apply measure_mono_null hsub
    rw [hF.projection_respects_measure_apply (orbitQuotientMeasure G μ) hmeas, hsat]
    exact measure_inter_null_of_null_left _ (measure_iUnion_null fun g ↦ measure_smul_null ht₀ g)

end MeasureTheory

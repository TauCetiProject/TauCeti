/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.WithDensity
-- Proof-only: change of variables in set integrals along a measurable embedding.
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Measures and the group operations

This file records measure formulas for finite families of disjoint additive translates.  In
lattice-point counting, the formula turns disjoint translates of a fundamental-domain cell into
measure bounds that can be compared with the number of cells. Conversely, a set with infinitely
many disjoint translates inside a set of finite measure is null; this shows that coordinate
hyperplanes of `ι → M` are null for Haar-type measures, without a real vector space structure
on `M`. It also records that inverting or negating a probability measure gives a probability
measure, so that the law of `X⁻¹` or `-X` can be used wherever a probability law is expected, and
that restricting an inversion-invariant measure to a symmetric set, or weighting it by an even
density, keeps it inversion-invariant.

## Main results

* `Measure.measure_biUnion_sub_mem`: a finite disjoint union of translates has measure
  equal to the number of translates times the measure of the original set.
* `Measure.measure_eq_zero_of_pairwiseDisjoint_vadd`: a measurable set with infinitely many
  pairwise disjoint translates whose union has finite measure is null.
* `Measure.measure_hyperplane`: a coordinate hyperplane `{a | a i = x}` of `ι → M` is null for a
  left-invariant measure finite on compact sets, for `M` non-discrete, locally compact and
  σ-compact.
* `Measure.isProbabilityMeasure_inv`, `Measure.isProbabilityMeasure_neg`: the inverse and the
  negation of a probability measure are probability measures.
* `Measure.map_inv_comp`, `Measure.map_neg_comp`: composing a pushforward from the inverted or
  negated measure with inversion or negation recovers the original pushforward.
* `Measure.ae_inv_mem_preimage`, `Measure.ae_neg_mem_preimage`: a full-mass set reflects to a
  full-mass set for the inverted or negated measure.
* `Measure.isInvInvariant_restrict`, `Measure.isNegInvariant_restrict`,
  `Measure.isInvInvariant_withDensity`, `Measure.isNegInvariant_withDensity`: restriction to a
  symmetric set and an even density preserve inversion or negation invariance.
-/

public section

open MeasureTheory Set
open scoped ENNReal Pointwise Topology

namespace TauCeti

variable {E : Type*} [AddGroup E] [MeasurableSpace E] [MeasurableAdd E]

/-- The union of finitely many pairwise disjoint translates of a measurable set has measure equal
to the number of translates times the measure of the set. -/
theorem _root_.MeasureTheory.Measure.measure_biUnion_sub_mem
    (mu : Measure E) [mu.IsAddRightInvariant]
    {G F : Set E} (hFm : MeasurableSet F)
    (hdisj : ∀ w₁ ∈ G, ∀ w₂ ∈ G, w₁ ≠ w₂ →
      Disjoint {y : E | y - w₁ ∈ F} {y : E | y - w₂ ∈ F})
    {T : Finset E} (hT : ↑T ⊆ G) :
    mu (⋃ w ∈ T, {y : E | y - w ∈ F}) = T.card * mu F := by
  rw [measure_biUnion_finset (fun w₁ h₁ w₂ h₂ h ↦ hdisj w₁ (hT h₁) w₂ (hT h₂) h)
    fun w _ ↦ by
      have h : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
        ext y
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, sub_eq_add_neg]
      rw [h]
      exact measurableSet_preimage (measurable_id.add_const (-w)) hFm]
  have htranslate (w : E) : mu {y : E | y - w ∈ F} = mu F := by
    have h : {y : E | y - w ∈ F} = (fun y : E ↦ y + -w) ⁻¹' F := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, sub_eq_add_neg]
    rw [h, measure_preimage_add_right]
  simp_rw [htranslate]
  simp

end TauCeti

namespace MeasureTheory.Measure

/-- The inverse of a probability measure is a probability measure. -/
@[to_additive /-- The negation of a probability measure is a probability measure. -/]
instance isProbabilityMeasure_inv {G : Type*} [MeasurableSpace G] [Inv G] (μ : Measure G)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure μ.inv := by
  rw [inv_def]
  infer_instance

/-- Pushing an inverted measure forward along `f` after inversion gives the pushforward of the
original measure along `f`. -/
@[to_additive /-- Pushing a negated measure forward along `f` after negation gives the pushforward
of the original measure along `f`. -/]
theorem map_inv_comp {G H : Type*} [MeasurableSpace G] [MeasurableSpace H] [InvolutiveInv G]
    [MeasurableInv G] (μ : Measure G) {f : G → H} (hf : AEMeasurable (f ∘ Inv.inv) μ.inv) :
    μ.inv.map (f ∘ Inv.inv) = μ.map f := by
  rw [inv_def] at hf ⊢
  rw [AEMeasurable.map_map_of_aemeasurable hf measurable_inv.aemeasurable]
  congr 1
  ext x
  simp

/-- A set of full measure reflects to a set of full measure for the inverted measure. -/
@[to_additive /-- A set of full measure reflects to a set of full measure for the negated
measure. -/]
theorem ae_inv_mem_preimage {G : Type*} [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G]
    (μ : Measure G) {s : Set G} (hs : MeasurableSet s) (hμs : ∀ᵐ x ∂μ, x ∈ s) :
    ∀ᵐ x ∂μ.inv, x ∈ Inv.inv ⁻¹' s := by
  simp only [Set.mem_preimage]
  rw [inv_def, ae_map_iff measurable_inv.aemeasurable (measurable_inv hs)]
  simpa only [inv_inv] using hμs

section Translates

variable {E : Type*} [AddGroup E] [MeasurableSpace E] [MeasurableAdd E]

/-- A measurable set with infinitely many pairwise disjoint translates, whose union has finite
measure, is null for every left-invariant measure: all the translates have the same measure, so
infinitely many of them can fit into a set of finite measure only if that measure is zero. -/
theorem measure_eq_zero_of_pairwiseDisjoint_vadd (μ : Measure E) [μ.IsAddLeftInvariant]
    {s T : Set E} (hs : MeasurableSet s) (hT : T.Infinite)
    (hdisj : T.PairwiseDisjoint (· +ᵥ s)) (hfin : μ (T + s) ≠ ∞) : μ s = 0 := by
  by_contra h
  let f := hT.natEmbedding
  have hle : ∑' k, μ ((f k : E) +ᵥ s) ≤ μ (T + s) :=
    (tsum_meas_le_meas_iUnion_of_disjoint μ (fun k ↦ hs.const_vadd _)
      fun k l hkl ↦ hdisj (f k).2 (f l).2 fun h ↦ hkl (f.injective (Subtype.ext h))).trans
      (measure_mono (Set.iUnion_subset fun k ↦ Set.vadd_set_subset_add (f k).2))
  simp only [measure_vadd, ENNReal.tsum_const_eq_top_of_ne_zero h, top_le_iff] at hle
  exact hfin hle

variable {ι M : Type*} [Finite ι] [AddGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [T2Space M] [WeaklyLocallyCompactSpace M] [SigmaCompactSpace M] [(𝓝[≠] (0 : M)).NeBot]
  [MeasurableSpace (ι → M)] [BorelSpace (ι → M)]

/-- A coordinate hyperplane `{a | a i = x}` of `ι → M` is null for every left-invariant measure
that is finite on compact sets, when `M` is a non-discrete, locally compact, σ-compact additive
group. This is the analogue of `MeasureTheory.Measure.addHaar_submodule` without a real vector
space structure, and of `MeasureTheory.Measure.pi_hyperplane` without a product structure on the
measure. -/
theorem measure_hyperplane (μ : Measure (ι → M)) [μ.IsAddLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] (i : ι) (x : M) : μ {a | a i = x} = 0 := by
  classical
  obtain ⟨T, hTc, hT0⟩ := exists_compact_mem_nhds (0 : M)
  have hZ : IsClosed {a : ι → M | a i = x} := isClosed_eq (continuous_apply i) continuous_const
  -- On each compact piece, the translates by `Pi.single i t` for `t ∈ T` are disjoint, since
  -- their `i`-th coordinates are `t + x`, and they all lie in a fixed compact set.
  have key (C : Set (ι → M)) (hC : IsCompact C) : μ ({a | a i = x} ∩ C) = 0 := by
    refine measure_eq_zero_of_pairwiseDisjoint_vadd μ (hZ.measurableSet.inter hC.measurableSet)
      ((infinite_of_mem_nhds 0 hT0).image (Pi.single_injective i).injOn) ?_
      ((hTc.image (continuous_single (A := fun _ ↦ M) i)).add (hC.inter_left hZ)).measure_lt_top.ne
    rintro _ ⟨u, -, rfl⟩ _ ⟨v, -, rfl⟩ hne
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ⟨ha, -⟩, rfl⟩ ⟨b, ⟨hb, -⟩, hab⟩
    have h := congrFun hab i
    simp only [Set.mem_ofPred_eq] at ha hb
    simp only [vadd_eq_add, Pi.add_apply, Pi.single_eq_same, ha, hb] at h
    exact hne (by rw [add_right_cancel h])
  rw [← Set.inter_univ {a : ι → M | a i = x}, ← iUnion_compactCovering, Set.inter_iUnion]
  exact measure_iUnion_null fun k ↦ key _ (isCompact_compactCovering _ k)

end Translates

section InvolutiveInv

variable {G : Type*} [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G] {μ : Measure G}

/-- The restriction of an inversion-invariant measure to a set closed under inversion is
inversion-invariant. -/
@[to_additive /-- The restriction of a negation-invariant measure to a set closed under negation
is negation-invariant. -/]
theorem isInvInvariant_restrict [μ.IsInvInvariant] {s : Set G} (hs : s⁻¹ = s) :
    (μ.restrict s).IsInvInvariant := by
  refine ⟨Measure.ext fun t ht ↦ ?_⟩
  rw [inv_apply, restrict_apply ht.inv, restrict_apply ht, ← measure_inv μ, Set.inter_inv,
    inv_inv, hs]

/-- An inversion-invariant measure weighted by a density invariant under inversion is
inversion-invariant. -/
@[to_additive /-- A negation-invariant measure weighted by an even density is
negation-invariant. -/]
theorem isInvInvariant_withDensity [μ.IsInvInvariant] {f : G → ℝ≥0∞} (hf : ∀ x, f x⁻¹ = f x) :
    (μ.withDensity f).IsInvInvariant := by
  refine ⟨Measure.ext fun t ht ↦ ?_⟩
  rw [inv_apply, withDensity_apply _ ht.inv, withDensity_apply _ ht, ← Set.inv_preimage]
  simpa only [hf] using (measurePreserving_inv μ).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.inv G).measurableEmbedding f t

end InvolutiveInv

end MeasureTheory.Measure

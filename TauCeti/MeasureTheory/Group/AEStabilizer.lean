/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.AEStabilizer
public import Mathlib.MeasureTheory.Measure.ContinuousPreimage
public import TauCeti.MeasureTheory.Measure.Restrict

/-!
# The a.e. stabilizer of a set is closed

For a continuous measure-preserving action of a topological group `G` on a space `X` with a
σ-finite locally finite measure `μ` that is inner regular on sets of finite measure, the a.e.
stabilizer `MulAction.aestabilizer G μ s` of a null measurable set `s`, made of the elements `g`
with `g • s =ᵐ[μ] s`, is a closed subgroup of `G`, whatever the measure of `s`.

Mathlib's `isClosed_setOfPred_preimage_ae_eq` (Yury Kudryashov) gives this when `μ s` is finite.
Here `s` is instead tested against sets `E` of finite measure: moving the translation onto `E`
gives `μ (g • s ∩ E) = μ (s ∩ (g • ·) ⁻¹' E)`, and `g ↦ (g • ·) ⁻¹' E` is continuous in measure
(`tendsto_measure_symmDiff_preimage_nhds_zero`). So `g • s` and `s` meet every set of finite
measure in the same measure when `g` lies in the closure of the a.e. stabilizer, and σ-finiteness
then makes them a.e. equal (`TauCeti.ae_eq_of_forall_measure_inter_eq`).

## Main results

* `TauCeti.measure_smul_inter_eq_of_mem_closure_aestabilizer`: an element of the closure of the
  a.e. stabilizer of `s` moves `s` without changing its intersections with sets of finite measure.
* `TauCeti.isClosed_aestabilizer`, `TauCeti.isClosed_addAestabilizer`: the a.e. stabilizer of a
  null measurable set is closed.
-/

public section

open Filter Set MeasureTheory Measure Topology
open scoped Pointwise ENNReal symmDiff

namespace TauCeti

variable {G X : Type*} [Group G] [TopologicalSpace G]
  [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
  [MulAction G X] [ContinuousSMul G X]
  {μ : Measure X} [SMulInvariantMeasure G X μ] [μ.InnerRegularCompactLTTop]
  [IsLocallyFiniteMeasure μ]

/-- If `g` lies in the closure of the a.e. stabilizer of `s`, then `g • s` and `s` meet every
set of finite measure in the same measure. This holds even when `s` has infinite measure. -/
@[to_additive /-- If `g` lies in the closure of the additive a.e. stabilizer of `s`, then
`g +ᵥ s` and `s` meet every set of finite measure in the same measure. This holds even when `s`
has infinite measure. -/]
theorem measure_smul_inter_eq_of_mem_closure_aestabilizer {s E : Set X} {g : G}
    (hg : g ∈ closure (MulAction.aestabilizer G μ s : Set G)) (hE : NullMeasurableSet E μ)
    (hμE : μ E ≠ ∞) : μ (g • s ∩ E) = μ (s ∩ E) := by
  -- Move the translation from `s` onto the finite-measure set `E`.
  have key (h : G) : μ (h • s ∩ E) = μ (s ∩ (h • ·) ⁻¹' E) := by
    rw [preimage_smul]
    exact (measure_inter_inv_smul μ h s E).symm
  -- Moving `E` changes the measure of `s ∩ E` by at most that of the symmetric difference.
  have le_add (A B : Set X) : μ (s ∩ A) ≤ μ (s ∩ B) + μ (A ∆ B) := by
    refine (measure_mono (show s ∩ A ⊆ s ∩ B ∪ A ∆ B from fun x ⟨hxs, hxA⟩ ↦ ?_)).trans
      (measure_union_le _ _)
    by_cases hxB : x ∈ B
    · exact Or.inl ⟨hxs, hxB⟩
    · exact Or.inr (mem_symmDiff.2 (Or.inl ⟨hxA, hxB⟩))
  -- The preimages of `E` under the translations depend continuously on the translation.
  let F : C(G, C(X, X)) := (⟨fun p : G × X ↦ p.1 • p.2, continuous_smul⟩ : C(G × X, X)).curry
  have hF : Tendsto (fun h ↦ μ (((h • ·) ⁻¹' E) ∆ ((g • ·) ⁻¹' E))) (𝓝 g) (𝓝 0) :=
    tendsto_measure_symmDiff_preimage_nhds_zero (f := F) (F.continuous.tendsto g)
      (.of_forall fun h ↦ measurePreserving_smul h μ) (measurePreserving_smul g μ) hE hμE
  -- For every `ε > 0` there is an element of the a.e. stabilizer moving `E` by less than `ε`.
  have approx (ε : ℝ≥0∞) (hε : 0 < ε) : ∃ h ∈ MulAction.aestabilizer G μ s,
      μ (((h • ·) ⁻¹' E) ∆ ((g • ·) ⁻¹' E)) < ε :=
    ((mem_closure_iff_frequently.1 hg).and_eventually (hF.eventually (gt_mem_nhds hε))).exists
  -- On the a.e. stabilizer the translated measure is `μ (s ∩ E)`.
  have hstab {h : G} (hh : h ∈ MulAction.aestabilizer G μ s) :
      μ (s ∩ (h • ·) ⁻¹' E) = μ (s ∩ E) := by
    rw [← key]
    exact measure_congr ((MulAction.mem_aestabilizer.1 hh).inter (.refl _ _ : E =ᵐ[μ] E))
  rw [key]
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_)
    (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_)
  · obtain ⟨h, hh, hlt⟩ := approx ε (by exact_mod_cast hε)
    calc μ (s ∩ (g • ·) ⁻¹' E)
        ≤ μ (s ∩ (h • ·) ⁻¹' E) + μ (((g • ·) ⁻¹' E) ∆ ((h • ·) ⁻¹' E)) := le_add _ _
      _ ≤ μ (s ∩ E) + ε := by
        rw [hstab hh, symmDiff_comm]
        gcongr
  · obtain ⟨h, hh, hlt⟩ := approx ε (by exact_mod_cast hε)
    calc μ (s ∩ E) = μ (s ∩ (h • ·) ⁻¹' E) := (hstab hh).symm
      _ ≤ μ (s ∩ (g • ·) ⁻¹' E) + μ (((h • ·) ⁻¹' E) ∆ ((g • ·) ⁻¹' E)) := le_add _ _
      _ ≤ μ (s ∩ (g • ·) ⁻¹' E) + ε := by gcongr

/-- **The a.e. stabilizer of a set is closed.** For a continuous measure-preserving action of a
topological group on an R₁ space with a σ-finite locally finite measure that is inner regular on
sets of finite measure, the elements `g` with `g • s =ᵐ[μ] s` form a closed subgroup. The set `s`
may have infinite measure; compare `isClosed_setOfPred_preimage_ae_eq`, which needs `μ s ≠ ∞`. -/
@[to_additive isClosed_addAestabilizer /-- **The additive a.e. stabilizer of a set is closed.**
For a continuous measure-preserving additive action of a topological additive group on an R₁ space
with a σ-finite locally finite measure that is inner regular on sets of finite measure, the
elements `g` with `g +ᵥ s =ᵐ[μ] s` form a closed subgroup, whatever the measure of `s`. -/]
theorem isClosed_aestabilizer [SigmaFinite μ] {s : Set X} (hs : NullMeasurableSet s μ) :
    IsClosed (MulAction.aestabilizer G μ s : Set G) := by
  refine closure_subset_iff_isClosed.1 fun g hg ↦ ?_
  exact ae_eq_of_forall_measure_inter_eq (hs.smul g) hs fun E hE hμE ↦
    measure_smul_inter_eq_of_mem_closure_aestabilizer hg hE hμE

end TauCeti

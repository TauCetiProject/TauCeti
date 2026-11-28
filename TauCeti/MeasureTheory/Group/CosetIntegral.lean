/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti Contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.L1

/-!
# Coset Decomposition of Integrals on Groups with Left-Invariant Measures

Let `μ` be a left-invariant measure on a measurable group `H`, let `L` be a measurable subgroup,
and let `r : ι → H` be a countable family of representatives meeting every left coset `g L`
uniquely. Then the Bochner integral of an integrable function `Φ : H → F` decomposes as the
summable series of set integrals `∫ g in L, Φ (r i * g) ∂μ`, and the Lebesgue integral of any
`f : H → ENNReal` decomposes as `∑' i, ∫⁻ g in L, f (r i * g) ∂μ`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/Lib/SiegelWeil/RallisInner/VacuumSummability.lean`
(`New.hasSum_setIntegral_mul_of_existsUnique`).
-/

@[expose] public section

namespace TauCeti

open MeasureTheory

/-- Cutting a Bochner integral over a group into left cosets of a measurable subgroup: if `μ` is
left-invariant on `H`, `L` is a measurable subgroup, and `r : ι → H` is a countable system of
left-coset representatives, then the integrals `∫ g in L, Φ (r i * g) ∂μ` sum to `∫ g, Φ g ∂μ`. -/
theorem hasSum_setIntegral_mul_of_existsUnique {H ι F : Type*} [Group H] [MeasurableSpace H]
    [MeasurableMul H] {μ : Measure H} [μ.IsMulLeftInvariant] {L : Subgroup H} [Countable ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hL : MeasurableSet (L : Set H)) {r : ι → H}
    (hr : ∀ g : H, ∃! i, (r i)⁻¹ * g ∈ L) {Φ : H → F} (hΦ : Integrable Φ μ) :
    HasSum (fun i ↦ ∫ g in (L : Set H), Φ (r i * g) ∂μ) (∫ g, Φ g ∂μ) := by
  let coset (i : ι) : Set H := (fun g ↦ (r i)⁻¹ * g) ⁻¹' (L : Set H)
  have h_disjoint : Pairwise (Function.onFun Disjoint coset) := fun i j h_ne ↦
    Set.disjoint_left.mpr fun g hi hj ↦ h_ne ((hr g).unique hi hj)
  have h_cover : ⋃ i, coset i = Set.univ :=
    Set.eq_univ_of_forall fun g ↦ Set.mem_iUnion.mpr (hr g).exists
  have h_coset (i : ι) : ∫ g in coset i, Φ g ∂μ = ∫ g in (L : Set H), Φ (r i * g) ∂μ := by
    simpa using (measurePreserving_mul_left μ (r i)⁻¹).setIntegral_preimage_emb
      (measurableEmbedding_mulLeft _) (fun g ↦ Φ (r i * g)) (L : Set H)
  simpa only [h_coset, h_cover, Measure.restrict_univ] using
    hasSum_integral_iUnion (s := coset) (fun i ↦ measurable_const_mul _ hL) h_disjoint hΦ.restrict

/-- The `tsum` form of `hasSum_setIntegral_mul_of_existsUnique`. -/
theorem integral_eq_tsum_setIntegral_mul_of_existsUnique {H ι F : Type*} [Group H]
    [MeasurableSpace H] [MeasurableMul H] {μ : Measure H} [μ.IsMulLeftInvariant] {L : Subgroup H}
    [Countable ι] [NormedAddCommGroup F] [NormedSpace ℝ F] (hL : MeasurableSet (L : Set H))
    {r : ι → H} (hr : ∀ g : H, ∃! i, (r i)⁻¹ * g ∈ L) {Φ : H → F} (hΦ : Integrable Φ μ) :
    ∫ g, Φ g ∂μ = ∑' i, ∫ g in (L : Set H), Φ (r i * g) ∂μ :=
  (hasSum_setIntegral_mul_of_existsUnique hL hr hΦ).tsum_eq.symm

/-- Cutting a Lebesgue integral over a group into left cosets of a measurable subgroup: if `μ` is
left-invariant on `H`, `L` is a measurable subgroup, and `r : ι → H` is a countable system of
left-coset representatives, then `∫⁻ g, f g ∂μ = ∑' i, ∫⁻ g in L, f (r i * g) ∂μ`. -/
theorem lintegral_eq_tsum_setLIntegral_mul_of_existsUnique {H ι : Type*} [Group H]
    [MeasurableSpace H] [MeasurableMul H] {μ : Measure H} [μ.IsMulLeftInvariant] {L : Subgroup H}
    [Countable ι] (hL : MeasurableSet (L : Set H)) {r : ι → H}
    (hr : ∀ g : H, ∃! i, (r i)⁻¹ * g ∈ L) (f : H → ENNReal) :
    ∫⁻ g, f g ∂μ = ∑' i, ∫⁻ g in (L : Set H), f (r i * g) ∂μ := by
  let coset (i : ι) : Set H := (fun g ↦ (r i)⁻¹ * g) ⁻¹' (L : Set H)
  have h_disjoint : Pairwise (Function.onFun Disjoint coset) := fun i j h_ne ↦
    Set.disjoint_left.mpr fun g hi hj ↦ h_ne ((hr g).unique hi hj)
  have h_cover : ⋃ i, coset i = Set.univ :=
    Set.eq_univ_of_forall fun g ↦ Set.mem_iUnion.mpr (hr g).exists
  have h_coset (i : ι) : ∫⁻ g in coset i, f g ∂μ = ∫⁻ g in (L : Set H), f (r i * g) ∂μ := by
    simpa using (measurePreserving_mul_left μ (r i)⁻¹).setLIntegral_comp_preimage_emb
      (measurableEmbedding_mulLeft _) (fun g ↦ f (r i * g)) (L : Set H)
  have h_union := lintegral_iUnion (μ := μ) (s := coset)
    (fun i ↦ measurable_const_mul _ hL) h_disjoint f
  simpa only [h_coset, h_cover, Measure.restrict_univ] using h_union

end TauCeti

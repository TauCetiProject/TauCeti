/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Basic.Complex.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Integrals and character orthogonality over additive subgroups

This file proves translation invariance of set integrals over an additive subgroup under a
left-invariant measure, orthogonality of multiplicative characters of an additive group over a
measurable subgroup, and reduction of the integral of a locally constant function over a compact
additive subgroup to a finite coset sum.

## Main results

* `TauCeti.setIntegral_add_left_eq_self_of_mem`: translating the integrand by `m ∈ M` preserves
  `∫ x in M, F x ∂ν`.
* `TauCeti.setIntegral_addChar_eq_ite`: for a left-invariant measure `ν`, a measurable subgroup `M`,
  and `χ : V → ℂ` with `χ (x + y) = χ x * χ y`, `∫ x in M, χ x ∂ν` equals `(ν.real M : ℂ)` if
  `χ = 1` on `M` and `0` otherwise.
* `TauCeti.setIntegral_compact_addSubgroup_eq_finsum`: for a compact subgroup `M` and open subgroup
  `L`, if `F` is constant on cosets of `L ∩ M` in `M`, then
  `∫ x in M, F x ∂ν = ν.real (L ∩ M) • ∑ᶠ q : M ⧸ L.addSubgroupOf M, F q.out`.

## Provenance

Generalized from `New.setIntegral_add_left_eq_self_of_mem`, `New.setIntegral_char`, and
`New.setIntegral_eq_finsum` in `src/Lib/General/Measure/HaarNormalisation.lean` of
[grh-lean](https://github.com/lsernau/grh-lean) at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open MeasureTheory AddSubgroup Set

namespace TauCeti

variable {V X : Type*} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd₂ V]
  {ν : Measure V} [ν.IsAddLeftInvariant] {M L : AddSubgroup V}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- For a left-invariant measure `ν` and an additive subgroup `M`, the set integral over `M` is
unchanged by translating the integrand by an element of `M`. -/
theorem setIntegral_add_left_eq_self_of_mem (F : V → X) {m : V} (hm : m ∈ M) :
    ∫ x : V in M, F (m + x) ∂ν = ∫ x : V in M, F x ∂ν := by
  have h_preimage : (m + ·) ⁻¹' (M : Set V) = M := Set.ext fun x ↦ M.add_mem_cancel_left hm
  simpa [h_preimage] using (measurePreserving_add_left ν m).setIntegral_preimage_emb
    (measurableEmbedding_addLeft m) F M

/-- Character orthogonality over a measurable additive subgroup: for a left-invariant measure `ν`,
a measurable subgroup `M`, and `χ : V → ℂ` satisfying `χ (x + y) = χ x * χ y`, the integral of `χ`
over `M` is `(ν.real M : ℂ)` when `χ = 1` on `M`, and `0` otherwise. -/
theorem setIntegral_addChar_eq_ite {χ : V → ℂ} [Decidable (∀ x ∈ M, χ x = 1)]
    (hM : MeasurableSet (M : Set V)) (h_add : ∀ x y : V, χ (x + y) = χ x * χ y) :
    ∫ x : V in M, χ x ∂ν = if ∀ x ∈ M, χ x = 1 then (ν.real M : ℂ) else 0 := by
  split_ifs with h_triv
  · simp [setIntegral_congr_fun hM h_triv]
  · obtain ⟨m, hm, hm_ne⟩ : ∃ m ∈ M, χ m ≠ 1 := by simpa using h_triv
    have h_mul : χ m * ∫ x : V in M, χ x ∂ν = ∫ x : V in M, χ x ∂ν := by
      simp only [← integral_const_mul, ← h_add, setIntegral_add_left_eq_self_of_mem χ hm]
    exact eq_zero_of_mul_eq_self_left hm_ne h_mul

/-- Let `M` be a compact and `L` an open additive subgroup of `V`, and let `ν` be a left-invariant
Borel measure that is finite on compact sets. If `F` is constant on the cosets of `L ∩ M` in `M`,
then its integral over `M` is `ν.real (L ∩ M)` times the finite sum of its values on these cosets.
-/
theorem setIntegral_compact_addSubgroup_eq_finsum [TopologicalSpace V] [IsTopologicalAddGroup V]
    [BorelSpace V] [T2Space V] [IsFiniteMeasureOnCompacts ν] [CompleteSpace X]
    (hM : IsCompact (M : Set V)) (hL : IsOpen (L : Set V)) {F : V → X}
    (hF : ∀ x y : M, -(x : V) + y ∈ L → F y = F x) :
    ∫ x : V in M, F x ∂ν = ν.real ((L : Set V) ∩ M) • ∑ᶠ q : M ⧸ L.addSubgroupOf M, F q.out := by
  classical
  have h_fin : Finite (M ⧸ L.addSubgroupOf M) := by
    have h_cov : (M : Set V) ⊆ ⋃ x : M, (fun y ↦ -(x : V) + y) ⁻¹' (L : Set V) := fun x hx ↦
      Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by simp⟩
    obtain ⟨t, ht⟩ := hM.elim_finite_subcover (fun x : M ↦ (fun y ↦ -(x : V) + y) ⁻¹' (L : Set V))
      (fun x ↦ hL.preimage (continuous_const.add continuous_id)) h_cov
    refine Finite.of_surjective
      (f := fun x : t ↦ (QuotientAddGroup.mk x.val : M ⧸ L.addSubgroupOf M)) fun q ↦ ?_
    obtain ⟨x, hx_t, hx_mem⟩ := Set.mem_iUnion₂.mp (ht q.out.property)
    refine ⟨⟨x, hx_t⟩, ?_⟩
    rw [← q.out_eq', QuotientAddGroup.eq, mem_addSubgroupOf]
    exact hx_mem
  let : Fintype (M ⧸ L.addSubgroupOf M) := Fintype.ofFinite _
  let G (q : M ⧸ L.addSubgroupOf M) (x : V) : X := indicator L (fun _ ↦ F q.out) (-q.out + x)
  have h_sum : EqOn F (fun x : V ↦ ∑ q : M ⧸ L.addSubgroupOf M, G q x) M := by
    intro x hx
    let q₀ : M ⧸ L.addSubgroupOf M := QuotientAddGroup.mk ⟨x, hx⟩
    have h_coset (q : M ⧸ L.addSubgroupOf M) : -(q.out : V) + x ∈ L ↔ q = q₀ := by
      rw [← q.out_eq', QuotientAddGroup.eq]; simp [mem_addSubgroupOf]
    simp [G, indicator, h_coset, hF q₀.out ⟨x, hx⟩ ((h_coset q₀).mpr rfl)]
  have h_int (q : M ⧸ L.addSubgroupOf M) : IntegrableOn (G q) M ν :=
    (integrableOn_const hM.measure_ne_top).indicator (measurable_const_add _ hL.measurableSet)
  have h_integral (q : M ⧸ L.addSubgroupOf M) :
      ∫ x : V in M, G q x ∂ν = ν.real ((L : Set V) ∩ M) • F q.out := by
    rw [setIntegral_add_left_eq_self_of_mem (indicator L fun _ ↦ F q.out)
      (M.neg_mem q.out.property)]
    simp [hL.measurableSet]
  rw [setIntegral_congr_fun hM.measurableSet h_sum, integral_finsetSum _ fun q _ ↦ h_int q]
  simp [h_integral, finsum_eq_sum_of_fintype, Finset.smul_sum]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.CompactSupport
public import TauCeti.Analysis.Sobolev.W1p.Restriction

/-!
# Local approximation of first-order Sobolev functions

This file combines restriction with compact-support density.  On a relatively compact subdomain,
every Sobolev function is locally a Sobolev-norm limit of test functions on the larger domain.
This is the local approximation step used in the Meyers--Serrin density theorem.

## Main declaration

* `TauCeti.W1p.restrictL_mem_closure_range_ofTestFunctionₗ`: local approximation by restrictions
  of test functions on the larger domain.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Gradient

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-- **Local smooth approximation.**  Let `U` be relatively compact in `Ω`.  For
`1 ≤ p < ∞`, the restriction to `U` of every `u ∈ W^{1,p}(Ω)` lies in the closure of the
restrictions of test functions on `Ω`.

The approximants are smooth on all of `Ω`, not merely on `U`.  This is the local approximation
step in Meyers--Serrin density: a smooth cutoff equal to one on `closure U` first localizes `u`
away from `∂Ω`, after which density of test functions in `W^{1,p}_0(Ω)` applies. -/
theorem W1p.restrictL_mem_closure_range_ofTestFunctionₗ (hp : p ≠ ∞)
    (hcompact : IsCompact (closure (U : Set E)))
    (hclosure : closure (U : Set E) ⊆ (Omega : Set E)) (u : W1p mu Omega p) :
    W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hclosure)) u ∈
      closure (Set.range (fun (phi : 𝓓(Omega, ℝ)) =>
        W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hclosure))
          (W1p.ofTestFunctionₗ mu Omega p phi))) := by
  let hU : U ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hclosure)
  -- The statement spells out the inclusion witness, while the proof reuses `hU`; normalize
  -- these proof-irrelevant arguments before constructing the approximation.
  change W1p.restrictL hU u ∈ closure (Set.range (fun (phi : 𝓓(Omega, ℝ)) =>
    W1p.restrictL hU (W1p.ofTestFunctionₗ mu Omega p phi)))
  obtain ⟨chi, M, hchi, -, hchi_one_nhds, hchi_cpt, hchi_ts, hM0, hchiM_all,
    hchigradM_all⟩ :=
    hcompact.exists_contDiff_cutoff_with_bounds Omega.isOpen hclosure
  have hchiM : ∀ x ∈ (Omega : Set E), |chi x| ≤ M := fun x _ => hchiM_all x
  have hchigradM : ∀ x ∈ (Omega : Set E), ‖∇ chi x‖ ≤ M := fun x _ => hchigradM_all x
  let v := W1p.contDiffSMul chi hchi hM0 hchiM hchigradM u
  have hv_zero : v ∈ w1p0Submodule mu Omega p :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport hp hchi hM0 hchiM hchigradM
      hchi_cpt hchi_ts u
  have hv_closure : v ∈ closure (Set.range (W1p.ofTestFunctionₗ mu Omega p)) := by
    rw [← coe_w1p0Submodule]
    exact hv_zero
  have hrestrict : W1p.restrictL hU v = W1p.restrictL hU u := by
    apply W1p.ext_value
    apply Lp.ext
    have hv_value := (W1p.value_contDiffSMul_ae hchi hM0 hchiM hchigradM u).filter_mono
      (MeasureTheory.ae_mono (Measure.restrict_mono_set mu
        (SetLike.coe_subset_coe.mpr hU)))
    filter_upwards [W1p.value_restrictL_ae hU v, W1p.value_restrictL_ae hU u,
      hv_value, ae_restrict_mem U.isOpen.measurableSet] with x hv hu hmul hxU
    rw [hv, hu, hmul]
    have hxpre : x ∈ chi ⁻¹' ({1} : Set ℝ) :=
      interior_subset (hchi_one_nhds (subset_closure hxU))
    have hx_one : chi x = 1 := by simpa only [mem_preimage, mem_singleton_iff] using hxpre
    rw [hx_one, one_smul]
  rw [← hrestrict]
  refine map_mem_closure (W1p.restrictL hU).continuous hv_closure ?_
  rintro _ ⟨phi, rfl⟩
  exact ⟨phi, rfl⟩

end TauCeti

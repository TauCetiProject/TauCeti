/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# The scalar action on the completion of a topological module

Let `R` be a topological ring and `M` a topological `R`-module whose uniformity is that of its
additive group, with each `m ↦ a • m` uniformly continuous. Mathlib extends the action to the
separated completion `M̂` (`UniformSpace.Completion.instModule`), with each `x ↦ a • x` uniformly
continuous. This file shows that the action `R × M̂ → M̂` is jointly continuous, so that `M̂` is
again a topological `R`-module. The completed tensor product of topological modules uses it to make
its completion a topological module, the target of the maps induced on completions.

The proof checks the three neighbourhood conditions of `ContinuousSMul.of_nhds_zero`. Closures of
neighbourhoods of `0` in `M` are neighbourhoods of `0` in `M̂`, and `a • ·` carries such a closure
into the closure of the image, which gives continuity at `(0, 0)`. Continuity of `a ↦ a • x` at
`0` for a fixed `x ∈ M̂` follows by approximating `x` by an element of `M`.

## Main results

* `UniformSpace.Completion.continuousSMul`: the completion of a topological module is a
  topological module.
-/

public section

open Filter Topology

namespace UniformSpace.Completion

variable {R M : Type*} [Ring R] [TopologicalSpace R] [AddCommGroup M]
  [Module R M] [UniformSpace M] [IsUniformAddGroup M] [ContinuousSMul R M]
  [UniformContinuousConstSMul R M]

/-- The action of `R` on `M̂` is continuous at `(0, 0)`. -/
private theorem tendsto_smul_zero :
    Tendsto (fun p : R × Completion M ↦ p.1 • p.2) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0) := by
  intro U hU
  obtain ⟨C, ⟨hC, hCc⟩, hCU⟩ := (closed_nhds_basis (0 : Completion M)).mem_iff.mp hU
  have hC' : ((↑) : M → Completion M) ⁻¹' C ∈ 𝓝 (0 : M) :=
    (continuous_coe M).continuousAt (by simpa using hC)
  -- the action of `R` on `M` is continuous at `(0, 0)`
  have hsmul : Tendsto (fun p : R × M ↦ p.1 • p.2) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0) := by
    simpa [← nhds_prod_eq] using (continuous_smul (M := R) (X := M)).tendsto ((0 : R), (0 : M))
  obtain ⟨N, hN, V, hV, hNV⟩ := mem_prod_iff.mp (hsmul hC')
  have hV' : closure (((↑) : M → Completion M) '' V) ∈ 𝓝 (0 : Completion M) := by
    simpa using (isDenseInducing_coe (α := M)).closure_image_mem_nhds hV
  refine mem_map.mpr (mem_of_superset (prod_mem_prod hN hV') ?_)
  rintro ⟨a, x⟩ ⟨ha, hx⟩
  -- `{x | a • x ∈ C}` is closed and contains the image of `V`, hence its closure
  have hsub : closure (((↑) : M → Completion M) '' V) ⊆ (fun x ↦ a • x) ⁻¹' C := by
    refine closure_minimal ?_ (hCc.preimage (continuous_const_smul a))
    rintro _ ⟨v, hv, rfl⟩
    simpa [← coe_smul] using hNV (Set.mk_mem_prod ha hv)
  exact hCU (hsub hx)

/-- **The completion of a topological module is a topological module**: the action of `R` on the
separated completion `M̂` is jointly continuous. -/
instance continuousSMul [IsTopologicalRing R] : ContinuousSMul R (Completion M) := by
  refine .of_nhds_zero tendsto_smul_zero (fun x ↦ ?_) fun a ↦ ?_
  · intro U hU
    obtain ⟨U', hU', hU'U⟩ := exists_nhds_zero_half hU
    obtain ⟨N, hN, O, hO, hNO⟩ := mem_prod_iff.mp (tendsto_smul_zero (R := R) (M := M) hU')
    -- approximate `x` by some `m ∈ M` with `x - m ∈ O`
    have hx : (fun y ↦ x - y) ⁻¹' O ∈ 𝓝 x :=
      (continuous_const.sub continuous_id : Continuous fun y : Completion M ↦ x - y).continuousAt
        (by simpa using hO)
    obtain ⟨m, hm⟩ := (denseRange_coe (α := M)).mem_nhds hx
    have hm' : Tendsto (fun a : R ↦ ((a • m : M) : Completion M)) (𝓝 0) (𝓝 0) := by
      simpa [Function.comp_def] using
        ((continuous_coe M).comp (continuous_id.smul (continuous_const (y := m)))).tendsto (0 : R)
    refine mem_map.mpr ?_
    filter_upwards [hN, hm'.eventually_mem hU'] with a haN ham
    have h : a • x = ((a • m : M) : Completion M) + a • (x - m) := by
      rw [coe_smul, ← smul_add, add_sub_cancel]
    rw [Set.mem_preimage, h]
    exact hU'U _ ham _ (hNO (Set.mk_mem_prod haN hm))
  · simpa using (continuous_const_smul a).tendsto (0 : Completion M)

end UniformSpace.Completion

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Fibrewise scalar multiplication on a topological vector bundle

Scalar multiplication in the fibres of a topological vector bundle `E → B` is jointly continuous as
a map `𝕜 × TotalSpace F E → TotalSpace F E`: in a linear trivialization it becomes scalar
multiplication in the model fibre `F`. Consequently a continuous map into the total space,
rescaled fibrewise by a continuous scalar function, is again continuous. This is the topological
counterpart of `ContMDiff.smul_totalSpace`, needing no charts on the base, and it supplies, for
instance, the straight-line homotopy `t • s` from the zero section to a section `s` over an
arbitrary topological space.
-/

public section

open Bundle Topology Filter

variable {𝕜 B F X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] [TopologicalSpace X]

namespace VectorBundle

variable (𝕜 F E) in
/-- Fibrewise scalar multiplication on the total space of a topological vector bundle is jointly
continuous. -/
theorem continuous_smul :
    Continuous fun p : 𝕜 × TotalSpace F E ↦ TotalSpace.mk' F p.2.proj (p.1 • p.2.2) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨((FiberBundle.continuous_proj F E).comp continuous_snd).continuousAt, ?_⟩
  set e := trivializationAt F E p₀.2.proj
  have hsrc : e.source ∈ 𝓝 p₀.2 :=
    e.open_source.mem_nhds (FiberBundle.mem_trivializationAt_proj_source)
  -- Near `p₀` the point lies over the base set of `e`, where `e` is linear on the fibre.
  have hcoord : ContinuousAt (fun p : 𝕜 × TotalSpace F E ↦ p.1 • (e p.2).2) p₀ :=
    continuousAt_fst.smul
      ((continuous_snd.continuousAt.comp (e.continuousOn.continuousAt hsrc)).comp continuousAt_snd)
  refine hcoord.congr ?_
  filter_upwards [continuousAt_snd.preimage_mem_nhds hsrc] with p hp
  have hb : p.2.proj ∈ e.baseSet := e.mem_source.1 hp
  simp only [TotalSpace.mk', e.apply_eq_prod_continuousLinearEquivAt 𝕜 _ hb, map_smul]

end VectorBundle

/-- A continuous map into the total space of a vector bundle, rescaled fibrewise by a continuous
scalar function, is continuous. -/
theorem Continuous.smul_totalSpace {c : X → 𝕜} {φ : X → TotalSpace F E} (hc : Continuous c)
    (hφ : Continuous φ) : Continuous fun x ↦ TotalSpace.mk' F (φ x).proj (c x • (φ x).2) :=
  (VectorBundle.continuous_smul 𝕜 F E).comp (hc.prodMk hφ)

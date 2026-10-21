/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Locally uniform convergence of flow orbits

Convergence of initial points gives locally uniform convergence of their parametrized orbits.
This upgrades pointwise compactness arguments to convergence of trajectories, without local
compactness assumptions on the time or phase space.
-/

public section

open Filter Topology Uniformity

namespace Flow

variable {τ α ι : Type*} [TopologicalSpace τ] [AddZero τ] [UniformSpace α]

/-- Convergent initial points have locally uniformly convergent flow orbits. -/
theorem tendstoLocallyUniformly_orbit (φ : Flow τ α) {u : ι → α} {y : α}
    {l : Filter ι} (hu : Tendsto u l (𝓝 y)) :
    TendstoLocallyUniformly (fun i t => φ t (u i)) (fun t => φ t y) l := by
  refine tendstoLocallyUniformly_iff_forall_tendsto.mpr fun t => ?_
  have htime : Tendsto (fun p : ι × τ => p.2) (l ×ˢ 𝓝 t) (𝓝 t) := tendsto_snd
  have hinit : Tendsto (fun p : ι × τ => u p.1) (l ×ˢ 𝓝 t) (𝓝 y) :=
    hu.comp tendsto_fst
  have hlimit := (φ.cont'.tendsto (t, y)).comp (htime.prodMk_nhds tendsto_const_nhds)
  have horbit := (φ.cont'.tendsto (t, y)).comp (htime.prodMk_nhds hinit)
  exact (hlimit.prodMk_nhds horbit).mono_right (nhds_le_uniformity _)

end Flow

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Pointwise convergence of equicontinuous families is uniform on compact sets

Mathlib's `EquicontinuousOn.tendsto_uniformOnFun_iff_pi'` identifies, for families equicontinuous
on compact sets, uniform convergence on those sets with pointwise convergence on their union.
`EquicontinuousOn.tendstoUniformlyOn_of_tendsto` states the direction used in practice for a
single compact set, in terms of `TendstoUniformlyOn`. Combined with
`LipschitzWith.uniformEquicontinuous`, it shows that equi-Lipschitz functions converging pointwise
converge uniformly on compact sets.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- A family equicontinuous on a compact set `K` and converging pointwise on `K` converges
uniformly on `K`. -/
theorem _root_.EquicontinuousOn.tendstoUniformlyOn_of_tendsto {ι X α : Type*}
    [TopologicalSpace X] [UniformSpace α] {F : ι → X → α} {K : Set X}
    (hF : EquicontinuousOn F K) (hK : IsCompact K) {L : Filter ι} {f : X → α}
    (hFf : ∀ x ∈ K, Tendsto (fun i => F i x) L (𝓝 (f x))) : TendstoUniformlyOn F f L K := by
  have h := (EquicontinuousOn.tendsto_uniformOnFun_iff_pi' (𝔖 := {K}) (by simpa using hK)
    (by simpa using hF) L f).2 <| by
      rw [sUnion_singleton]
      exact tendsto_pi_nhds.2 fun x => hFf x x.2
  exact UniformOnFun.tendsto_iff_tendstoUniformlyOn.1 h K rfl

end TauCeti

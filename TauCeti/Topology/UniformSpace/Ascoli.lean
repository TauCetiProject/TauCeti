/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Pointwise convergence and total boundedness for equicontinuous families

Mathlib's `EquicontinuousOn.tendsto_uniformOnFun_iff_pi'` identifies, for families equicontinuous
on compact sets, uniform convergence on those sets with pointwise convergence on their union.
`EquicontinuousOn.tendstoUniformlyOn_of_tendsto` states the direction used in practice for a
single compact set, in terms of `TendstoUniformlyOn`. Combined with
`LipschitzWith.uniformEquicontinuous`, it shows that equi-Lipschitz functions converging pointwise
converge uniformly on compact sets.

`EquicontinuousWithinAt.totallyBounded_range_eval` spreads total boundedness of the values of a
family from a set of points `D` to any point of the closure of `D` at which the family is
equicontinuous within `D`. It is the pointwise step of the Arzelà–Ascoli theorem with a dense set
of points.
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

/-- Equicontinuity within `D` at a point `x` of the closure of `D` spreads total boundedness of
the values from the points of `D` to `x`. -/
theorem _root_.EquicontinuousWithinAt.totallyBounded_range_eval {ι X Y : Type*}
    [TopologicalSpace X] [UniformSpace Y] {F : ι → X → Y} {D : Set X} {x : X}
    (hF : EquicontinuousWithinAt F D x) (hx : x ∈ closure D)
    (hFD : ∀ x ∈ D, TotallyBounded (range fun i ↦ F i x)) :
    TotallyBounded (range fun i ↦ F i x) := by
  intro U hU
  obtain ⟨V, hV, hVU⟩ := comp_mem_uniformity_sets hU
  have := mem_closure_iff_nhdsWithin_neBot.mp hx
  obtain ⟨x', hx', hx'D⟩ := ((hF V hV).and self_mem_nhdsWithin).exists
  obtain ⟨t, ht, hcover⟩ := hFD x' hx'D V hV
  refine ⟨t, ht, ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨y, hy, hiy⟩ := mem_iUnion₂.mp (hcover ⟨i, rfl⟩)
  exact mem_iUnion₂.mpr ⟨y, hy, hVU ⟨F i x', hx' i, hiy⟩⟩

end TauCeti

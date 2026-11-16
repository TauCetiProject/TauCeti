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

Conversely, the scalar function is recovered continuously from the two maps: if one map into the
total space is a scalar multiple of another, nonzero at a point, and both are continuous there,
then so is the scalar (`TauCeti.VectorBundle.continuousAt_of_eventually_eq_smul`). This is how a
reparametrization factor between two vector fields along a curve is shown to be continuous.
-/

public section

open Bundle Topology Filter

variable {𝕜 B F X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] [TopologicalSpace X]

namespace TauCeti.VectorBundle

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

/-- **Continuity of a fibrewise scalar factor.** Let `φ` and `ψ` be maps into the total space of a
vector bundle, continuous at `x₀`, with `ψ x = c x • φ x` in the fibre over `(φ x).proj` near `x₀`.
If `φ x₀` is a nonzero vector, then the scalar function `c` is continuous at `x₀`. -/
theorem continuousAt_of_eventually_eq_smul {c : X → 𝕜}
    {φ ψ : X → TotalSpace F E} {x₀ : X} (hφ : ContinuousAt φ x₀) (hψ : ContinuousAt ψ x₀)
    (hψφ : ∀ᶠ x in 𝓝 x₀, ψ x = TotalSpace.mk' F (φ x).proj (c x • (φ x).2))
    (h0 : (φ x₀).2 ≠ 0) : ContinuousAt c x₀ := by
  set e := trivializationAt F E (φ x₀).proj
  have hψx₀ : ψ x₀ = TotalSpace.mk' F (φ x₀).proj (c x₀ • (φ x₀).2) := hψφ.self_of_nhds
  -- In the trivialization the two maps become `F`-valued maps `u` and `w`, continuous at `x₀`.
  obtain ⟨hp, hu⟩ : ContinuousAt (fun x ↦ (φ x).proj) x₀ ∧ ContinuousAt (fun x ↦ (e (φ x)).2) x₀ :=
    (FiberBundle.continuousAt_totalSpace F φ).1 hφ
  have hw : ContinuousAt (fun x ↦ (e (ψ x)).2) x₀ := by
    simpa only [hψx₀] using ((FiberBundle.continuousAt_totalSpace F ψ).1 hψ).2
  have hb₀ : (φ x₀).proj ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  have hu₀ : (e (φ x₀)).2 ≠ 0 := by
    rw [e.apply_eq_prod_continuousLinearEquivAt 𝕜 _ hb₀ (φ x₀).2]
    exact (map_ne_zero_iff _ (e.continuousLinearEquivAt 𝕜 _ hb₀).injective).2 h0
  -- Over the base set the trivialization is linear on the fibre, so `w = c • u` near `x₀`.
  have hwu : ∀ᶠ x in 𝓝 x₀, (e (ψ x)).2 = c x • (e (φ x)).2 := by
    filter_upwards [hψφ, hp.preimage_mem_nhds (e.open_baseSet.mem_nhds hb₀)] with x hx hxb
    rw [hx, e.apply_eq_prod_continuousLinearEquivAt 𝕜 _ hxb,
      e.apply_eq_prod_continuousLinearEquivAt 𝕜 _ hxb, map_smul]
  -- Hence `‖c x - c x₀‖ = ‖w x - c x₀ • u x‖ / ‖u x‖`, which tends to `0 / ‖u x₀‖ = 0`.
  have hlim : Tendsto (fun x ↦ ‖(e (ψ x)).2 - c x₀ • (e (φ x)).2‖ / ‖(e (φ x)).2‖) (𝓝 x₀)
      (𝓝 0) := by
    simpa [hwu.self_of_nhds, Pi.div_def] using
      ((hw.tendsto.sub (hu.tendsto.const_smul (c x₀))).norm.div hu.tendsto.norm
        (norm_ne_zero_iff.2 hu₀))
  refine tendsto_iff_norm_sub_tendsto_zero.2 (hlim.congr' ?_)
  filter_upwards [hwu, hu.eventually_ne hu₀] with x hx hux
  rw [hx, ← sub_smul, norm_smul, mul_div_cancel_right₀ _ (norm_ne_zero_iff.2 hux)]

end TauCeti.VectorBundle

/-- A continuous map into the total space of a vector bundle, rescaled fibrewise by a continuous
scalar function, is continuous. -/
theorem Continuous.smul_totalSpace {c : X → 𝕜} {φ : X → TotalSpace F E} (hc : Continuous c)
    (hφ : Continuous φ) : Continuous fun x ↦ TotalSpace.mk' F (φ x).proj (c x • (φ x).2) :=
  (TauCeti.VectorBundle.continuous_smul 𝕜 F E).comp (hc.prodMk hφ)

/-- **A bounded fibrewise rescaling is continuous.** Let `φ` be a continuous map into the total
space of a vector bundle and `c` a bounded scalar function which is continuous at every point
where `φ` takes a nonzero value. Then `φ` rescaled fibrewise by `c` is continuous. No continuity of
`c` is needed at the zeros of `φ`: there the rescaled vector tends to zero because `c` is bounded.
This covers radial retractions, whose scalar factor jumps where the vector vanishes. -/
theorem Continuous.smul_totalSpace_of_norm_le {c : X → 𝕜} {φ : X → TotalSpace F E} {C : ℝ}
    (hφ : Continuous φ) (hcC : ∀ x, ‖c x‖ ≤ C) (hc : ∀ x, (φ x).2 ≠ 0 → ContinuousAt c x) :
    Continuous fun x ↦ TotalSpace.mk' F (φ x).proj (c x • (φ x).2) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  by_cases h0 : (φ x₀).2 = 0
  swap
  · exact (TauCeti.VectorBundle.continuous_smul 𝕜 F E).continuousAt.comp
      (f := fun x ↦ (c x, φ x)) ((hc x₀ h0).prodMk hφ.continuousAt)
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨((FiberBundle.continuous_proj F E).comp hφ).continuousAt, ?_⟩
  set e := trivializationAt F E (φ x₀).proj
  have hsrc : e.source ∈ 𝓝 (φ x₀) :=
    e.open_source.mem_nhds FiberBundle.mem_trivializationAt_proj_source
  have hb₀ : (φ x₀).proj ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  -- In the trivialization at `φ x₀` the rescaled vector is `c x • (e (φ x)).2`, and
  -- `(e (φ x)).2` tends to `(e (φ x₀)).2 = 0`.
  have hu : Tendsto (fun x ↦ (e (φ x)).2) (𝓝 x₀) (𝓝 0) := by
    have h : ContinuousAt (fun x ↦ (e (φ x)).2) x₀ :=
      continuous_snd.continuousAt.comp ((e.continuousOn.continuousAt hsrc).comp hφ.continuousAt)
    have hv : (e (φ x₀)).2 = 0 := by
      rw [e.apply_eq_prod_continuousLinearEquivAt 𝕜 _ hb₀ (φ x₀).2, h0, map_zero]
    rw [ContinuousAt, hv] at h
    exact h
  have hlim : Tendsto (fun x ↦ c x • (e (φ x)).2) (𝓝 x₀) (𝓝 0) :=
    IsBoundedUnder.smul_tendsto_zero ⟨C, eventually_map.2 (Eventually.of_forall hcC)⟩ hu
  have hval : (e (TotalSpace.mk' F (φ x₀).proj (c x₀ • (φ x₀).2))).2 = 0 := by
    rw [TotalSpace.mk', e.apply_eq_prod_continuousLinearEquivAt 𝕜 _ hb₀, h0, smul_zero, map_zero]
  rw [ContinuousAt, hval]
  refine hlim.congr' ?_
  filter_upwards [hφ.continuousAt.preimage_mem_nhds hsrc] with x hx
  have hxb : (φ x).proj ∈ e.baseSet := e.mem_source.1 hx
  rw [TotalSpace.mk', e.apply_eq_prod_continuousLinearEquivAt 𝕜 _ hxb (c x • (φ x).2), map_smul,
    e.apply_eq_prod_continuousLinearEquivAt 𝕜 _ hxb (φ x).2]

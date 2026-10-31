/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
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
theorem continuousAt_of_eventually_eq_smul [SeparatingDual 𝕜 F] {c : X → 𝕜}
    {φ ψ : X → TotalSpace F E} {x₀ : X} (hφ : ContinuousAt φ x₀) (hψ : ContinuousAt ψ x₀)
    (hψφ : ∀ᶠ x in 𝓝 x₀, ψ x = TotalSpace.mk' F (φ x).proj (c x • (φ x).2))
    (h0 : (φ x₀).2 ≠ 0) : ContinuousAt c x₀ := by
  set e := trivializationAt F E (φ x₀).proj
  have hsrc : e.source ∈ 𝓝 (φ x₀) :=
    e.open_source.mem_nhds FiberBundle.mem_trivializationAt_proj_source
  have hb : ∀ᶠ x in 𝓝 x₀, (φ x).proj ∈ e.baseSet :=
    Filter.mem_of_superset (hφ.preimage_mem_nhds hsrc) fun x hx ↦ e.mem_source.1 hx
  -- In the trivialization the two maps become `F`-valued maps `u` and `w = c • u`.
  have hu : ContinuousAt (fun x ↦ (e (φ x)).2) x₀ :=
    continuous_snd.continuousAt.comp ((e.continuousOn.continuousAt hsrc).comp hφ)
  have hψx₀ : ψ x₀ = TotalSpace.mk' F (φ x₀).proj (c x₀ • (φ x₀).2) := hψφ.self_of_nhds
  have hsrc' : e.source ∈ 𝓝 (ψ x₀) := e.open_source.mem_nhds (by
    rw [e.mem_source, hψx₀]
    exact FiberBundle.mem_baseSet_trivializationAt' _)
  have hw : ContinuousAt (fun x ↦ (e (ψ x)).2) x₀ :=
    continuous_snd.continuousAt.comp ((e.continuousOn.continuousAt hsrc').comp hψ)
  have hb₀ : (φ x₀).proj ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  have hu₀ : (e (φ x₀)).2 ≠ 0 := by
    rw [e.apply_eq_prod_continuousLinearEquivAt 𝕜 _ hb₀ (φ x₀).2]
    exact (map_ne_zero_iff _ (e.continuousLinearEquivAt 𝕜 _ hb₀).injective).2 h0
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_ne_zero (R := 𝕜) hu₀
  -- Reading off the scalar with a functional that does not vanish on `u x₀`.
  have hc : ContinuousAt (fun x ↦ ℓ (e (ψ x)).2 / ℓ (e (φ x)).2) x₀ :=
    (ℓ.continuous.continuousAt.comp hw).div (ℓ.continuous.continuousAt.comp hu) hℓ
  refine hc.congr ?_
  filter_upwards [hψφ, hb, (ℓ.continuous.continuousAt.comp hu).eventually_ne hℓ] with x hx hxb hℓx
  -- Over the base set the trivialization is linear on the fibre, so `ℓ (w x) = c x * ℓ (u x)`.
  have hφx : e (φ x) = ((φ x).proj, e.continuousLinearEquivAt 𝕜 _ hxb (φ x).2) :=
    e.apply_eq_prod_continuousLinearEquivAt 𝕜 _ hxb (φ x).2
  have hψx : e (ψ x) = ((φ x).proj, c x • e.continuousLinearEquivAt 𝕜 _ hxb (φ x).2) := by
    rw [hx, ← map_smul]
    exact e.apply_eq_prod_continuousLinearEquivAt 𝕜 _ hxb _
  simp only [Function.comp_apply, hφx] at hℓx
  rw [hφx, hψx, map_smul, smul_eq_mul]
  exact mul_div_cancel_right₀ _ hℓx

end TauCeti.VectorBundle

/-- A continuous map into the total space of a vector bundle, rescaled fibrewise by a continuous
scalar function, is continuous. -/
theorem Continuous.smul_totalSpace {c : X → 𝕜} {φ : X → TotalSpace F E} (hc : Continuous c)
    (hφ : Continuous φ) : Continuous fun x ↦ TotalSpace.mk' F (φ x).proj (c x • (φ x).2) :=
  (TauCeti.VectorBundle.continuous_smul 𝕜 F E).comp (hc.prodMk hφ)

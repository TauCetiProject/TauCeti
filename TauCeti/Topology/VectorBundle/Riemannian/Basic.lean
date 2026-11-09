/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Compactness of norm-bounded parts of a Riemannian vector bundle

In a vector bundle whose fibers carry inner products depending continuously on the base point,
the fiber norm is a continuous function on the total space.  When the model fiber is
finite-dimensional, this file proves that the vectors of norm at most `r` lying over a compact
subset of the base form a compact subset of the total space.  The compactness statement holds more
generally for fiber norms that are continuous on the total space and for which each
trivialization is locally bounded, as for the operator norm on covectors.

This is the properness statement that turns a bound on the speed of a curve in the base together
with relative compactness of its image into relative compactness of its velocity lift.  The
part of the bundle lying over a compact set need not be compact on its own: the fibers of a
bundle with a positive-dimensional model fiber are noncompact, so the norm bound is what makes
the statement true.  The proof is local: near each point of the base, the fiber norm bounds the
model norm of the coordinates in the trivialization at that point (in the Riemannian case by
`eventually_norm_trivializationAt_lt`), so the coordinates of a convergent ultrafilter of bounded
vectors converge too.

## Main results

* `Continuous.norm_bundle`: the fiber norm of a continuous map into the fibers of a continuous
  Riemannian bundle is continuous, with `TauCeti.continuous_norm_bundle` its tautological case.
* `IsCompact.norm_le_bundle`: the vectors of norm at most `r` over a compact set form a compact
  subset of the total space.
* `IsCompact.norm_le_bundle_of_continuous`: the same for a continuous fiber norm with locally
  bounded trivializations.
-/

public section

open Bundle Filter Set
open scoped Topology

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]

section Norm

variable [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]

variable {X : Type*} [TopologicalSpace X] {b : X → B} {v : ∀ x, E (b x)}

/-- Given a continuous map into the fibers of a continuous Riemannian bundle, its fiber norm is
a continuous function. -/
theorem Continuous.norm_bundle (hv : Continuous fun x ↦ (v x : TotalSpace F E)) :
    Continuous fun x ↦ ‖v x‖ := by
  simp only [norm_eq_sqrt_real_inner]
  exact (hv.inner_bundle hv).sqrt

namespace TauCeti

variable (F E) in
/-- In a continuous Riemannian bundle, the fiber norm is a continuous function on the total
space. -/
theorem continuous_norm_bundle : Continuous fun z : TotalSpace F E ↦ ‖z.2‖ :=
  Continuous.norm_bundle (b := TotalSpace.proj) (v := fun z ↦ z.2)
    (continuous_id.congr fun z ↦ (TotalSpace.eta z).symm)

end TauCeti

end Norm

section Compact

variable [FiniteDimensional ℝ F]

section General

variable [∀ x, NormedSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- **The norm-bounded part of a normed vector bundle over a compact set is compact.** Let the
fibers of a vector bundle with finite-dimensional model fiber carry norms, such that the fiber
norm is continuous on the total space and each trivialization is bounded in norm near its base
point. Then the vectors of norm at most `r` lying over a compact subset of the base form a compact
subset of the total space. -/
theorem IsCompact.norm_le_bundle_of_continuous
    (hnorm : Continuous fun z : TotalSpace F E ↦ ‖z.2‖)
    (hloc : ∀ x, ∃ C, ∀ᶠ y in 𝓝 x, ∀ w : E y,
      ‖(trivializationAt F E x).continuousLinearMapAt ℝ y w‖ ≤ C * ‖w‖)
    {K : Set B} (hK : IsCompact K) (r : ℝ) :
    IsCompact {z : TotalSpace F E | z.proj ∈ K ∧ ‖z.2‖ ≤ r} := by
  refine isCompact_iff_ultrafilter_le_nhds'.2 fun 𝒰 hS ↦ ?_
  -- The base points converge to some `x ∈ K`.
  obtain ⟨x, hxK, hx⟩ := hK.ultrafilter_le_nhds' (𝒰.map TotalSpace.proj)
    (Ultrafilter.mem_map.2 (mem_of_superset hS fun _ hz ↦ hz.1))
  replace hx : Tendsto (TotalSpace.proj : TotalSpace F E → B) 𝒰 (𝓝 x) := hx
  set e := trivializationAt F E x
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  obtain ⟨C, hC⟩ := hloc x
  have hU : {z : TotalSpace F E | z.proj ∈ e.baseSet ∧
      ∀ w, ‖e.continuousLinearMapAt ℝ z.proj w‖ ≤ C * ‖w‖} ∈ 𝒰 :=
    hx (inter_mem (e.open_baseSet.mem_nhds hxe) hC)
  -- The fiber coordinates in `e` are bounded, so they converge to some `v`.
  obtain ⟨v, -, hv⟩ := (isCompact_closedBall (0 : F) (|C| * r)).ultrafilter_le_nhds'
    (𝒰.map fun z ↦ (e z).2) <| Ultrafilter.mem_map.2 <| mem_of_superset (inter_mem hS hU)
      fun z ⟨⟨_, hzr⟩, hzb, hzC⟩ ↦ by
        have h := hzC z.2
        rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hzb] at h
        exact mem_closedBall_zero_iff.2 <| h.trans <|
          (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)).trans
            (mul_le_mul_of_nonneg_left hzr (abs_nonneg C))
  replace hv : Tendsto (fun z ↦ (e z).2) (𝒰 : Filter (TotalSpace F E)) (𝓝 v) := hv
  -- So the vectors converge to the vector with coordinates `(x, v)`.
  have hsource : e.source ∈ 𝒰 := mem_of_superset hU fun z hz ↦ e.mem_source.2 hz.1
  have he : Tendsto e 𝒰 (𝓝 (x, v)) :=
    (hx.prodMk_nhds hv).congr' (mem_of_superset hsource fun z hz ↦
      show (z.proj, (e z).2) = e z from Prod.ext (e.coe_fst hz).symm rfl)
  have hlim : (𝒰 : Filter (TotalSpace F E)) ≤ 𝓝 (e.toOpenPartialHomeomorph.symm (x, v)) :=
    tendsto_id'.1 <| ((e.continuousAt_symm (e.mem_target.2 hxe)).tendsto.comp he).congr'
      (mem_of_superset hsource fun z hz ↦ e.left_inv hz)
  refine ⟨_, ⟨?_, ?_⟩, hlim⟩
  · rwa [e.proj_symm_apply' hxe]
  · exact (isClosed_le hnorm continuous_const).mem_of_tendsto hlim
      (mem_of_superset hS fun _ hz ↦ hz.2)

end General

variable [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsContinuousRiemannianBundle F E]

/-- **The norm-bounded part of a Riemannian bundle over a compact set is compact.** In a
continuous Riemannian vector bundle with finite-dimensional model fiber, the vectors of norm at
most `r` lying over a compact subset of the base form a compact subset of the total space. -/
theorem IsCompact.norm_le_bundle {K : Set B} (hK : IsCompact K) (r : ℝ) :
    IsCompact {z : TotalSpace F E | z.proj ∈ K ∧ ‖z.2‖ ≤ r} :=
  hK.norm_le_bundle_of_continuous (TauCeti.continuous_norm_bundle F E)
    (fun x ↦ (eventually_norm_trivializationAt_lt F E x).imp fun _ h ↦
      h.2.mono fun _ hy ↦ (ContinuousLinearMap.le_of_opNorm_le _ hy.le)) r

end Compact

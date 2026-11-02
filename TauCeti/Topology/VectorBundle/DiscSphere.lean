/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Riemannian.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Closed fibre discs and the frontier of their images

In a continuous Riemannian vector bundle, a positive continuous radius gives the closed
fibre discs as the closure of the open fibre discs. Over a compact base with finite-dimensional
model fibre, the closed discs are compact. Consequently a partial homeomorphism defined on
these closed discs takes the sphere bundle precisely onto the frontier of the open disc image.
This gives the topological boundary calculation for closed tubular neighbourhoods.

## References

* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3 (disc tubular neighbourhoods).
-/

public section

open Bundle Set Metric

variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContinuousRiemannianBundle F V]

namespace TauCeti

/-- The closure of the open fibre discs of positive continuous radius is the closed
fibre disc bundle. No rank, compactness or separation assumption is needed. -/
theorem closure_setOf_norm_lt_bundle {r : B → ℝ} (hr : Continuous r) (hpos : ∀ b, 0 < r b) :
    closure {p : TotalSpace F V | ‖p.2‖ < r p.proj} =
      {p : TotalSpace F V | ‖p.2‖ ≤ r p.proj} := by
  refine subset_antisymm (closure_minimal (fun p (hp : ‖p.2‖ < r p.proj) => le_of_lt hp)
    (isClosed_le (TauCeti.continuous_norm_bundle F V)
      (hr.comp (FiberBundle.continuous_proj F V)))) ?_
  rintro ⟨b, v⟩ hv
  have hv' : v ∈ closure (ball (0 : V b) (r b)) := by
    rw [closure_ball _ (hpos b).ne']
    exact mem_closedBall_zero_iff.mpr hv
  have hsub : TotalSpace.mk b '' ball (0 : V b) (r b) ⊆
      {p : TotalSpace F V | ‖p.2‖ < r p.proj} := by
    rintro _ ⟨w, hw, rfl⟩
    exact mem_ball_zero_iff.mp hw
  have hc := (FiberBundle.totalSpaceMk_isEmbedding (F := F) (E := V) b).continuous
  exact closure_mono hsub (mem_closure_image hc.continuousAt hv')

/-- Closed fibre discs of continuous radius are compact over a compact base when the model
fibre is finite-dimensional. The radius may vary and need not be positive. -/
theorem isCompact_setOf_norm_le_bundle [CompactSpace B] [FiniteDimensional ℝ F]
    {r : B → ℝ} (hr : Continuous r) :
    IsCompact {p : TotalSpace F V | ‖p.2‖ ≤ r p.proj} := by
  obtain ⟨R, hR⟩ := (isCompact_range hr).bddAbove
  apply (isCompact_univ.norm_le_bundle (F := F) (E := V) R).of_isClosed_subset
    (isClosed_le (TauCeti.continuous_norm_bundle F V)
      (hr.comp (FiberBundle.continuous_proj F V)))
  exact fun p hp => ⟨mem_univ _, hp.trans (hR (mem_range_self p.proj))⟩

end TauCeti

namespace OpenPartialHomeomorph

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- A partial homeomorphism defined on compact closed fibre discs takes them onto the
closure of the open disc image. -/
theorem closure_image_norm_lt_bundle [CompactSpace B] [FiniteDimensional ℝ F]
    (e : OpenPartialHomeomorph (TotalSpace F V) X) {r : B → ℝ}
    (hr : Continuous r) (hpos : ∀ b, 0 < r b)
    (hsource : {p : TotalSpace F V | ‖p.2‖ ≤ r p.proj} ⊆ e.source) :
    closure (e '' {p : TotalSpace F V | ‖p.2‖ < r p.proj}) =
      e '' {p : TotalSpace F V | ‖p.2‖ ≤ r p.proj} := by
  let D := {p : TotalSpace F V | ‖p.2‖ ≤ r p.proj}
  let U := {p : TotalSpace F V | ‖p.2‖ < r p.proj}
  have hUD : U ⊆ D := fun p (hp : ‖p.2‖ < r p.proj) => le_of_lt hp
  have hclosed : IsClosed (e '' D) :=
    ((TauCeti.isCompact_setOf_norm_le_bundle hr).image_of_continuousOn
      (e.continuousOn.mono hsource)).isClosed
  refine subset_antisymm (closure_minimal (image_mono hUD) hclosed) ?_
  intro y hy
  obtain ⟨p, hp, rfl⟩ := hy
  have hpcl : p ∈ closure U := by
    dsimp only [U]
    rw [TauCeti.closure_setOf_norm_lt_bundle hr hpos]
    exact hp
  exact mem_closure_image (e.continuousAt (hsource hp)) hpcl

/-- A partial homeomorphism defined on compact closed fibre discs takes their bounding
sphere bundle onto the frontier of the open disc image. -/
theorem frontier_image_norm_lt_bundle [CompactSpace B] [FiniteDimensional ℝ F]
    (e : OpenPartialHomeomorph (TotalSpace F V) X) {r : B → ℝ}
    (hr : Continuous r) (hpos : ∀ b, 0 < r b)
    (hsource : {p : TotalSpace F V | ‖p.2‖ ≤ r p.proj} ⊆ e.source) :
    frontier (e '' {p : TotalSpace F V | ‖p.2‖ < r p.proj}) =
      e '' {p : TotalSpace F V | ‖p.2‖ = r p.proj} := by
  let D := {p : TotalSpace F V | ‖p.2‖ ≤ r p.proj}
  let U := {p : TotalSpace F V | ‖p.2‖ < r p.proj}
  have hUD : U ⊆ D := fun p (hp : ‖p.2‖ < r p.proj) => le_of_lt hp
  have hcl := e.closure_image_norm_lt_bundle hr hpos hsource
  have hopen : IsOpen (e '' U) :=
    e.isOpen_image_of_subset_source
      (isOpen_lt (TauCeti.continuous_norm_bundle F V)
        (hr.comp (FiberBundle.continuous_proj F V))) (hUD.trans hsource)
  have hdiff : D \ U = {p : TotalSpace F V | ‖p.2‖ = r p.proj} := by
    ext p
    simp only [D, U, mem_sdiff, mem_ofPred_eq, not_lt]
    exact le_antisymm_iff.symm
  rw [frontier, hcl, hopen.interior_eq,
    ← (e.injOn.mono hsource).image_sdiff_subset hUD, hdiff]

end OpenPartialHomeomorph

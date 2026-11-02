/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Small fibre discs near the zero section

An open neighbourhood of the zero section in a continuous real Riemannian vector bundle
contains discs of a fixed positive radius over a neighbourhood of each base point. The
radius is measured in the fibre metric, rather than in a chosen trivialization. This local
uniformity permits continuous or smooth selection of a radius on the whole base, even when
the bundle is nontrivial and the base is noncompact.

The proof uses Sébastien Gouëzel's `eventually_norm_trivializationAt_lt` to compare the
fibre norm with coordinates in a bundle chart. No finite-dimensionality is required.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24,
the shrinking step in the tubular neighbourhood theorem.
-/

public section

open Bundle Filter Set Topology

namespace IsOpen

variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ b, NormedAddCommGroup (V b)]
  [∀ b, InnerProductSpace ℝ (V b)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContinuousRiemannianBundle F V]

/-- Near each point of the base, a neighbourhood of the zero section contains all fibre
vectors of sufficiently small norm, with one positive bound valid throughout that neighbourhood.
No compactness or finite-dimensionality is required. -/
theorem exists_pos_forall_norm_le_subset_bundle {U : Set (TotalSpace F V)} (hU : IsOpen U)
    {b : B} (hzero : zeroSection F V b ∈ U) :
    ∃ r > 0, ∀ᶠ y in 𝓝 b, ∀ v : V y, ‖v‖ ≤ r → (⟨y, v⟩ : TotalSpace F V) ∈ U := by
  let e := trivializationAt F V b
  have hb : b ∈ e.baseSet := mem_baseSet_trivializationAt F V b
  have hchart : IsOpen (e '' (e.source ∩ U)) :=
    e.toOpenPartialHomeomorph.isOpen_image_source_inter hU
  have hzerochart : (b, (0 : F)) ∈ e '' (e.source ∩ U) := by
    rw [← e.zeroSection ℝ hb]
    exact mem_image_of_mem e ⟨e.mem_source.mpr hb, hzero⟩
  obtain ⟨A, hA, D, hD, hAD⟩ := mem_nhds_prod_iff.mp (hchart.mem_nhds hzerochart)
  obtain ⟨δ, hδ, hδD⟩ := Metric.mem_nhds_iff.mp hD
  obtain ⟨C, hC, hbound⟩ := eventually_norm_trivializationAt_lt F V b
  refine ⟨δ / (2 * C), by positivity, ?_⟩
  filter_upwards [hA, e.open_baseSet.mem_nhds hb, hbound] with y hy hybase hybound
  intro v hv
  have hcoord : ‖(e ⟨y, v⟩).2‖ < δ := by
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hybase]
    calc
      ‖e.continuousLinearMapAt ℝ y v‖ ≤ ‖e.continuousLinearMapAt ℝ y‖ * ‖v‖ :=
        (e.continuousLinearMapAt ℝ y).le_opNorm v
      _ ≤ C * (δ / (2 * C)) :=
        mul_le_mul hybound.le hv (norm_nonneg _) hC.le
      _ = δ / 2 := by field_simp
      _ < δ := half_lt_self hδ
  have himage : e ⟨y, v⟩ ∈ e '' (e.source ∩ U) := by
    rw [e.apply_eq_prod_continuousLinearEquivAt ℝ y hybase v]
    exact hAD ⟨hy, hδD (mem_ball_zero_iff.mpr hcoord)⟩
  obtain ⟨p, ⟨hpsource, hpU⟩, hp⟩ := himage
  exact e.injOn hpsource (e.mem_source.mpr hybase) hp ▸ hpU

end IsOpen

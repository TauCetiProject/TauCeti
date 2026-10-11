/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
public import TauCeti.Topology.Compactification.OnePoint.Nhds

/-!
# The closed upper half-plane in the Riemann sphere

The closure of the open upper half-plane in `OnePoint ℂ` consists of the finite closed
upper half-plane together with infinity. Its approach filter at infinity is the usual
cobounded filter restricted to the upper half-plane. These descriptions allow analytic
boundary limits in the plane to be assembled into continuous sphere-valued extensions.
-/

public section

open Bornology Complex Filter Metric Set Topology UpperHalfPlane
open scoped OnePoint

namespace TauCeti

/-- Approaching infinity from the upper half-plane in the sphere is equivalent to escaping
bounded subsets of the plane within the upper half-plane. -/
theorem nhdsWithin_infty_coe_image_upperHalfPlaneSet :
    𝓝[((↑) : ℂ → OnePoint ℂ) '' upperHalfPlaneSet] (∞ : OnePoint ℂ) =
      map (↑) (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) := by
  rw [nhdsWithin_infty_coe_image, coclosedCompact_eq_cocompact,
    ← Metric.cobounded_eq_cocompact]

/-- The closure of the upper half-plane in the sphere is its finite closed half-plane
with the point at infinity added. -/
theorem closure_coe_image_upperHalfPlaneSet :
    closure (((↑) : ℂ → OnePoint ℂ) '' upperHalfPlaneSet) =
      insert ∞ (((↑) : ℂ → OnePoint ℂ) '' {z : ℂ | 0 ≤ z.im}) := by
  ext x
  induction x using OnePoint.rec with
  | infty =>
    have hcl : (∞ : OnePoint ℂ) ∈
        closure (((↑) : ℂ → OnePoint ℂ) '' upperHalfPlaneSet) := by
      rw [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_infty_coe_image_upperHalfPlaneSet]
      infer_instance
    simp [hcl]
  | coe z =>
    have hcl : z ∈ closure upperHalfPlaneSet ↔
        (z : OnePoint ℂ) ∈ closure (((↑) : ℂ → OnePoint ℂ) '' upperHalfPlaneSet) := by
      rw [OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image]
      rfl
    rw [← hcl, Complex.closure_setOfPred_lt_im]
    simp

/-- Every real point lies in the closure of the upper half-plane in the sphere. -/
theorem ofReal_mem_closure_coe_image_upperHalfPlaneSet (p : ℝ) :
    ((p : ℂ) : OnePoint ℂ) ∈
      closure (((↑) : ℂ → OnePoint ℂ) '' upperHalfPlaneSet) := by
  rw [closure_coe_image_upperHalfPlaneSet]
  exact mem_insert_of_mem _ ⟨(p : ℂ), by simp, rfl⟩

end TauCeti

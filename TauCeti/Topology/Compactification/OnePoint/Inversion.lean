/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Sphere inversion on a one-point compactification

Inversion in a sphere of nonzero radius extends to a homeomorphism of the one-point
compactification. It exchanges the centre and infinity and is its own inverse. On the Euclidean
chart away from the centre it is Mathlib's `EuclideanGeometry.inversion`. Unlike the total
Euclidean function, the extended inversion does not fix the centre.
-/

public noncomputable section

open Filter Topology

namespace OnePoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Classical in
/-- Inversion of the compactification, with the centre and infinity exchanged. -/
private def inversionFun (c : E) (R : ℝ) (p : OnePoint E) : OnePoint E :=
  p.elim (c : OnePoint E) fun x ↦ if x = c then ∞ else ↑(EuclideanGeometry.inversion c R x)

@[simp]
private theorem inversionFun_infty (c : E) (R : ℝ) : inversionFun c R ∞ = c := by
  simp [inversionFun]

@[simp]
private theorem inversionFun_center (c : E) (R : ℝ) : inversionFun c R c = ∞ := by
  simp [inversionFun]

private theorem inversionFun_coe (c : E) (R : ℝ) {x : E} (hx : x ≠ c) :
    inversionFun c R x = ↑(EuclideanGeometry.inversion c R x) := by
  simp [inversionFun, hx]

private theorem involutive_inversionFun (c : E) {R : ℝ} (hR : R ≠ 0) :
    Function.Involutive (inversionFun c R) := by
  intro p
  induction p using OnePoint.rec with
  | infty => simp
  | coe x =>
    rcases eq_or_ne x c with rfl | hx
    · simp
    · rw [inversionFun_coe c R hx,
        inversionFun_coe c R (by simpa [hR] using hx), EuclideanGeometry.inversion_inversion c hR]

private theorem continuous_inversionFun [ProperSpace E] (c : E) {R : ℝ} (hR : R ≠ 0) :
    Continuous (inversionFun c R) := by
  rw [continuous_iff_continuousAt]
  intro p
  induction p using OnePoint.rec with
  | infty =>
    -- The distance of an inverted point from `c` decays as the original distance tends to infinity.
    rw [continuousAt_infty', inversionFun_infty, coclosedCompact_eq_cocompact]
    have hlim : Tendsto (EuclideanGeometry.inversion c R) (cocompact E) (𝓝 c) := by
      refine tendsto_iff_dist_tendsto_zero.2 ?_
      have hd := (tendsto_dist_right_cocompact_atTop c).inv_tendsto_atTop.const_mul (R ^ 2)
      simpa only [EuclideanGeometry.dist_inversion_center, div_eq_mul_inv, mul_zero,
        Pi.inv_apply] using hd
    refine (continuous_coe.continuousAt.tendsto.comp hlim).congr' ?_
    filter_upwards [(isCompact_singleton (x := c)).compl_mem_cocompact] with x hx
    exact (inversionFun_coe c R (by simpa using hx)).symm
  | coe x =>
    rw [continuousAt_coe]
    simp only [ContinuousAt, Function.comp_apply]
    rcases eq_or_ne x c with rfl | hx
    · -- The punctured neighbourhood of the centre maps to the filter at infinity.
      rw [inversionFun_center, ← nhdsNE_sup_pure x, tendsto_sup]
      refine ⟨?_, by
        rw [tendsto_pure_left]
        intro s hs
        simpa using mem_of_mem_nhds hs⟩
      have hlim := EuclideanGeometry.tendsto_inversion_nhdsNE_center_cobounded (c := x) hR
      rw [Metric.cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact] at hlim
      refine (tendsto_coe_infty.comp hlim).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (inversionFun_coe x R (by simpa using hy)).symm
    · rw [inversionFun_coe c R hx]
      have hinv := continuousAt_const.inversion (c := fun _ : E ↦ c)
        (R := fun _ ↦ R) (x := id) continuousAt_const continuousAt_id hx
      refine (continuous_coe.continuousAt.tendsto.comp hinv).congr' ?_
      have hxc : x ∈ ({c} : Set E)ᶜ := hx
      filter_upwards [isOpen_compl_singleton.mem_nhds hxc] with y hy
      exact (inversionFun_coe c R (by simpa using hy)).symm

/-- Inversion in the sphere of centre `c` and nonzero radius `R`, as a self-homeomorphism of the
one-point compactification. In particular this works on each finite-dimensional Euclidean space. -/
def inversion [ProperSpace E] (c : E) (R : ℝ) (hR : R ≠ 0) : OnePoint E ≃ₜ OnePoint E where
  toFun := inversionFun c R
  invFun := inversionFun c R
  left_inv := involutive_inversionFun c hR
  right_inv := involutive_inversionFun c hR
  continuous_toFun := continuous_inversionFun c hR
  continuous_invFun := continuous_inversionFun c hR

variable [ProperSpace E] (c : E) (R : ℝ) (hR : R ≠ 0)

/-- Inversion sends infinity to its centre. -/
@[simp] theorem inversion_infty : inversion c R hR ∞ = (c : OnePoint E) :=
  inversionFun_infty c R

/-- Inversion sends its centre to infinity. -/
@[simp] theorem inversion_center : inversion c R hR (c : OnePoint E) = ∞ :=
  inversionFun_center c R

/-- At a finite point other than the centre, compactified inversion is Euclidean inversion. -/
@[simp] theorem inversion_coe {x : E} (hx : x ≠ c) :
    inversion c R hR (x : OnePoint E) = ↑(EuclideanGeometry.inversion c R x) :=
  inversionFun_coe c R hx

/-- Compactified inversion is its own inverse. -/
@[simp] theorem inversion_symm : (inversion c R hR).symm = inversion c R hR :=
  (rfl)

/-- Applying the same compactified inversion twice is the identity. -/
@[simp] theorem inversion_inversion (p : OnePoint E) :
    inversion c R hR (inversion c R hR p) = p := by
  simpa only [inversion_symm] using (inversion c R hR).symm_apply_apply p

end OnePoint

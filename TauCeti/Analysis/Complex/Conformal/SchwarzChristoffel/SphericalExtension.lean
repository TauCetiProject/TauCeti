/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.LogarithmicEnd.Basic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Power
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Compactification
public import TauCeti.Analysis.Complex.UpperHalfPlane.Compactification
import TauCeti.Algebra.BigOperators.Finset.Fiber

/-!
# Sphere-valued Schwarz--Christoffel boundary extension

Schwarz--Christoffel primitives with integrable finite vertices and logarithmic ends extend
continuously to the closed upper half-plane in the Riemann sphere. This includes the parameter
at infinity, whether its image is finite or infinite. Restricting this extension to the real
projective line gives a continuous boundary parametrization for data with several ends.

Finite prevertices of total exponent greater than `-1` retain their ordinary boundary values;
those of exponent `-1` map to infinity. The parameter at infinity has a finite image in the
decaying range of the total exponent, and maps to infinity otherwise. No global injectivity or
boundary simplicity is assumed. In particular, several parameters can map to infinity, so
continuity does not assert that this parametrization is a Jordan curve.

The construction uses Mathlib's `extendFrom` into `OnePoint ℂ` to assemble the finite-vertex,
logarithmic-end and infinity limits of the primitive.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Bornology Complex Filter Metric Set Topology UpperHalfPlane
open scoped OnePoint

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The canonical sphere-valued extension of the Schwarz--Christoffel primitive from the
upper half-plane. Its values on the compactified closed upper half-plane are genuine limits
when every finite prevertex has total exponent at least `-1`. -/
def schwarzChristoffelSphereExtension (a e : ι → ℝ) (z₀ : UpperHalfPlane) :
    OnePoint ℂ → OnePoint ℂ :=
  extendFrom (((↑) : ℂ → OnePoint ℂ) '' upperHalfPlaneSet)
    (OnePoint.map (schwarzChristoffelPrimitive a e z₀))

/-- The sphere-valued Schwarz--Christoffel boundary on the real projective line, including
finite parameters representing logarithmic ends. -/
def schwarzChristoffelSphereBoundary (a e : ι → ℝ) (z₀ : UpperHalfPlane) :
    OnePoint ℝ → OnePoint ℂ :=
  schwarzChristoffelSphereExtension a e z₀ ∘ OnePoint.map Complex.ofReal

/-- The sphere boundary evaluates the sphere extension on the compactified real axis. -/
theorem schwarzChristoffelSphereBoundary_apply (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (x : OnePoint ℝ) :
    schwarzChristoffelSphereBoundary a e z₀ x =
      schwarzChristoffelSphereExtension a e z₀ (OnePoint.map Complex.ofReal x) :=
  (rfl)

/-- On the open upper half-plane, the sphere extension agrees with the primitive. -/
@[simp]
theorem schwarzChristoffelSphereExtension_coe_of_im_pos (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {z : ℂ} (hz : 0 < z.im) :
    schwarzChristoffelSphereExtension a e z₀ (z : OnePoint ℂ) =
      (schwarzChristoffelPrimitive a e z₀ z : OnePoint ℂ) := by
  apply extendFrom_eq (A := ((↑) : ℂ → OnePoint ℂ) '' upperHalfPlaneSet)
    (subset_closure ⟨z, hz, rfl⟩)
  rw [OnePoint.nhdsWithin_coe_image, tendsto_map'_iff]
  exact OnePoint.continuous_coe.continuousAt.tendsto.comp
    ((hasDerivAt_schwarzChristoffelPrimitive a e z₀ hz).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds)

/-- At an integrable real parameter, the sphere extension retains the finite boundary value. -/
@[simp]
theorem schwarzChristoffelSphereExtension_coe_of_exponent_sum_gt_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (p : ℝ)
    (he : -1 < ∑ i with a i = p, e i) :
    schwarzChristoffelSphereExtension a e z₀ ((p : ℂ) : OnePoint ℂ) =
      (schwarzChristoffelBoundary a e z₀ p : OnePoint ℂ) := by
  apply extendFrom_eq
  · exact image_closure_subset_closure_image OnePoint.continuous_coe
      ⟨(p : ℂ), by rw [Complex.closure_setOfPred_lt_im]; simp, rfl⟩
  · rw [OnePoint.nhdsWithin_coe_image, tendsto_map'_iff]
    exact OnePoint.continuous_coe.continuousAt.tendsto.comp
      (tendsto_schwarzChristoffelPrimitive_boundary a e z₀ p he)

/-- A logarithmic real prevertex maps to infinity in the sphere extension. -/
@[simp]
theorem schwarzChristoffelSphereExtension_coe_of_exponent_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (p : ℝ)
    (he : ∑ i with a i = p, e i = -1) :
    schwarzChristoffelSphereExtension a e z₀ ((p : ℂ) : OnePoint ℂ) = ∞ := by
  apply extendFrom_eq
  · exact image_closure_subset_closure_image OnePoint.continuous_coe
      ⟨(p : ℂ), by rw [Complex.closure_setOfPred_lt_im]; simp, rfl⟩
  · rw [OnePoint.nhdsWithin_coe_image, tendsto_map'_iff]
    have h := tendsto_schwarzChristoffelPrimitive_cobounded_of_prevertex_sum_eq_neg_one
      a e z₀ p he
    rw [Metric.cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact] at h
    exact OnePoint.tendsto_coe_infty.comp h

/-- At parameter infinity, the sphere-valued primitive approaches the finite vertex in the
decaying range and infinity otherwise. This needs no assumptions on finite prevertices. -/
theorem tendsto_onePoint_map_schwarzChristoffelPrimitive_infty
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) :
    Tendsto (OnePoint.map (schwarzChristoffelPrimitive a e z₀))
      (𝓝[((↑) : ℂ → OnePoint ℂ) '' upperHalfPlaneSet] (∞ : OnePoint ℂ))
      (𝓝 (if ∑ i, e i < -1 then
        (schwarzChristoffelVertexAtInfinity a e z₀ : OnePoint ℂ) else ∞)) := by
  rw [nhdsWithin_infty_coe_image_upperHalfPlaneSet, tendsto_map'_iff]
  split_ifs with hsum
  · exact OnePoint.continuous_coe.continuousAt.tendsto.comp
      (tendsto_schwarzChristoffelPrimitive_atInfinity a e z₀ hsum)
  · have h := tendsto_schwarzChristoffelPrimitive_atInfinity_cobounded_of_neg_one_le_sum
      a e z₀ (le_of_not_gt hsum)
    rw [Metric.cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact] at h
    simpa only [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact,
      Function.comp_def, OnePoint.map_some] using OnePoint.tendsto_coe_infty.comp h

/-- At parameter infinity, the sphere extension has the finite vertex in the decaying range
and the point at infinity otherwise. This needs no assumptions on finite prevertices. -/
@[simp]
theorem schwarzChristoffelSphereExtension_infty (a e : ι → ℝ) (z₀ : UpperHalfPlane) :
    schwarzChristoffelSphereExtension a e z₀ ∞ =
      if ∑ i, e i < -1 then (schwarzChristoffelVertexAtInfinity a e z₀ : OnePoint ℂ)
      else ∞ := by
  apply extendFrom_eq _ (tendsto_onePoint_map_schwarzChristoffelPrimitive_infty a e z₀)
  rw [closure_coe_image_upperHalfPlaneSet]
  exact mem_insert _ _

/-- At an integrable real parameter, the sphere boundary retains the finite boundary value. -/
@[simp]
theorem schwarzChristoffelSphereBoundary_coe_of_exponent_sum_gt_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (p : ℝ)
    (he : -1 < ∑ i with a i = p, e i) :
    schwarzChristoffelSphereBoundary a e z₀ (p : OnePoint ℝ) =
      (schwarzChristoffelBoundary a e z₀ p : OnePoint ℂ) := by
  simpa only [schwarzChristoffelSphereBoundary_apply, OnePoint.map_some] using
    schwarzChristoffelSphereExtension_coe_of_exponent_sum_gt_neg_one a e z₀ p he

/-- A logarithmic real prevertex maps to infinity in the sphere boundary. -/
@[simp]
theorem schwarzChristoffelSphereBoundary_coe_of_exponent_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (p : ℝ)
    (he : ∑ i with a i = p, e i = -1) :
    schwarzChristoffelSphereBoundary a e z₀ (p : OnePoint ℝ) = ∞ := by
  simpa only [schwarzChristoffelSphereBoundary_apply, OnePoint.map_some] using
    schwarzChristoffelSphereExtension_coe_of_exponent_sum_eq_neg_one a e z₀ p he

/-- The value of the sphere boundary at the compactifying parameter. -/
@[simp]
theorem schwarzChristoffelSphereBoundary_infty (a e : ι → ℝ) (z₀ : UpperHalfPlane) :
    schwarzChristoffelSphereBoundary a e z₀ ∞ =
      if ∑ i, e i < -1 then (schwarzChristoffelVertexAtInfinity a e z₀ : OnePoint ℂ)
      else ∞ := by
  simp [schwarzChristoffelSphereBoundary_apply]

/-- When all finite prevertices are integrable and the vertex at infinity is finite, the
sphere boundary is the complex-valued compactified boundary embedded in the sphere. -/
theorem schwarzChristoffelSphereBoundary_eq_coe_compactifiedBoundary
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1) :
    schwarzChristoffelSphereBoundary a e z₀ =
      ((↑) : ℂ → OnePoint ℂ) ∘ schwarzChristoffelCompactifiedBoundary a e z₀ := by
  classical
  ext x
  induction x using OnePoint.rec with
  | infty => simp [hinfty]
  | coe p =>
    simp [schwarzChristoffelSphereBoundary_coe_of_exponent_sum_gt_neg_one a e z₀ p
      (lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite p)]

/-- The primitive approaches the sphere boundary from the whole upper half-plane, including
at logarithmic ends. -/
theorem tendsto_schwarzChristoffelPrimitive_sphereBoundary (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (p : ℝ) (he : -1 ≤ ∑ i with a i = p, e i) :
    Tendsto (fun z => (schwarzChristoffelPrimitive a e z₀ z : OnePoint ℂ))
      (𝓝[upperHalfPlaneSet] (p : ℂ))
      (𝓝 (schwarzChristoffelSphereBoundary a e z₀ (p : OnePoint ℝ))) := by
  rcases he.eq_or_lt with he | he
  · rw [schwarzChristoffelSphereBoundary_coe_of_exponent_sum_eq_neg_one a e z₀ p he.symm]
    have h := tendsto_schwarzChristoffelPrimitive_cobounded_of_prevertex_sum_eq_neg_one
      a e z₀ p he.symm
    rw [Metric.cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact] at h
    exact OnePoint.tendsto_coe_infty.comp h
  · rw [schwarzChristoffelSphereBoundary_coe_of_exponent_sum_gt_neg_one a e z₀ p he]
    exact OnePoint.continuous_coe.continuousAt.tendsto.comp
      (tendsto_schwarzChristoffelPrimitive_boundary a e z₀ p he)

/-- **Continuous spherical extension with multiple logarithmic ends.** If every finite
prevertex has total exponent at least `-1`, the sphere extension is continuous on the
compactified closed upper half-plane. Neither ordering nor global univalence is required. -/
theorem continuousOn_schwarzChristoffelSphereExtension (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i) :
    ContinuousOn (schwarzChristoffelSphereExtension a e z₀)
      (closure (((↑) : ℂ → OnePoint ℂ) '' upperHalfPlaneSet)) := by
  apply continuousOn_extendFrom subset_rfl
  intro x hx
  induction x using OnePoint.rec with
  | infty => exact ⟨_, tendsto_onePoint_map_schwarzChristoffelPrimitive_infty a e z₀⟩
  | coe z =>
    simp only [OnePoint.nhdsWithin_coe_image, tendsto_map'_iff]
    have hzcl : z ∈ closure upperHalfPlaneSet := by
      rw [OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image]
      exact hx
    rw [Complex.closure_setOfPred_lt_im] at hzcl
    simp only [mem_ofPred_eq] at hzcl
    rcases lt_or_eq_of_le hzcl with hz | hz
    · exact ⟨(schwarzChristoffelPrimitive a e z₀ z : OnePoint ℂ),
        OnePoint.continuous_coe.continuousAt.tendsto.comp
          ((hasDerivAt_schwarzChristoffelPrimitive a e z₀ hz).continuousAt.tendsto.mono_left
            nhdsWithin_le_nhds)⟩
    · have hzreal : (z.re : ℂ) = z := by
        apply Complex.ext <;> simp [← hz]
      rw [← hzreal]
      have he : -1 ≤ ∑ i with a i = z.re, e i := by
        classical
        by_cases hp : z.re ∈ range a
        · obtain ⟨j, hj⟩ := hp
          rw [← hj]
          exact hfinite j
        · rw [Finset.sum_eq_zero fun i hi => (hp ⟨i, (Finset.mem_filter.mp hi).2⟩).elim]
          norm_num
      exact ⟨_, tendsto_schwarzChristoffelPrimitive_sphereBoundary a e z₀ z.re he⟩

/-- **Continuous sphere boundary for several ends.** Integrable finite vertices and any
number of logarithmic prevertices assemble into a continuous map on the real projective line.
The total exponent is unrestricted, so its compactifying parameter may have finite or
infinite image. -/
theorem continuous_schwarzChristoffelSphereBoundary (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i) :
    Continuous (schwarzChristoffelSphereBoundary a e z₀) := by
  have hproper : Tendsto Complex.ofReal (coclosedCompact ℝ) (coclosedCompact ℂ) := by
    simpa only [coclosedCompact_eq_cocompact] using
      Complex.isUniformEmbedding_ofReal.isClosedEmbedding.tendsto_cocompact
  have hcont := OnePoint.continuous_map Complex.continuous_ofReal hproper
  rw [schwarzChristoffelSphereBoundary, ← continuousOn_univ]
  apply (continuousOn_schwarzChristoffelSphereExtension a e z₀ hfinite).comp
    hcont.continuousOn
  intro x _
  rw [closure_coe_image_upperHalfPlaneSet]
  induction x using OnePoint.rec with
  | infty => simp
  | coe p => exact mem_insert_of_mem _ ⟨(p : ℂ), by simp, by simp⟩

end TauCeti

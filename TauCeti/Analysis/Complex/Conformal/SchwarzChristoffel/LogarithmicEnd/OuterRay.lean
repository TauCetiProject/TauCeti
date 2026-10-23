/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.LogarithmicEnd.Ray
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.UnboundedEdge

/-!
# Outer boundary rays at logarithmic Schwarz--Christoffel prevertices

Suppose the total exponent is less than `-1`, so the parameter at infinity has a finite
Schwarz--Christoffel boundary value. If the leftmost or rightmost prevertex is logarithmic,
the outer real interval between that prevertex and parameter infinity traces an open affine
ray from this finite value. Adding the value at parameter infinity closes the ray.

These formulas complement the rays between finite prevertices and the bounded outer edges.
Together they describe every boundary edge needed to assemble polygonal traces with several
logarithmic ends.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Bornology Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **A right outer edge issuing from a logarithmic prevertex is an open ray.**
If every nonzero prevertex lies at or to the left of `p`, the boundary values for parameters
strictly larger than `p` form the horizontal ray extending left from the finite value at
parameter infinity. The latter endpoint is not attained at a finite parameter. -/
theorem schwarzChristoffelBoundary_image_Ioi_of_prevertex_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p : ℝ}
    (hp : ∑ i with a i = p, e i = -1)
    (ha : ∀ i, e i ≠ 0 → a i ≤ p) (hS : ∑ i, e i < -1) :
    schwarzChristoffelBoundary a e z₀ '' Ioi p =
      (fun t : ℝ => schwarzChristoffelVertexAtInfinity a e z₀ - (t : ℂ)) '' Ioi 0 := by
  classical
  let B : ℝ → ℂ := schwarzChristoffelBoundary a e z₀
  let V : ℂ := schwarzChristoffelVertexAtInfinity a e z₀
  let d : ℝ → ℝ := fun x => ‖V - B x‖
  have hsum {x : ℝ} (hx : p < x) : ∑ i with a i = x, e i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hax := (Finset.mem_filter.mp hi).2
    by_contra hei
    exact (not_le_of_gt hx) (hax ▸ ha i hei)
  have hfinite {x : ℝ} (hx : p < x) : -1 < ∑ i with a i = x, e i := by
    rw [hsum hx]
    norm_num
  have hBtop : Tendsto B atTop (𝓝 V) := by
    apply tendsto_schwarzChristoffelBoundaryValue_atInfinity a e z₀ hS
      tendsto_abs_atTop_atTop
    filter_upwards [eventually_gt_atTop p] with x hx
    exact tendsto_schwarzChristoffelPrimitive_boundary a e z₀ x (hfinite hx)
  have hdtop : Tendsto d atTop (𝓝 0) := by
    have hV : Tendsto (fun _ : ℝ => V) atTop (𝓝 V) := tendsto_const_nhds
    simpa [d] using (hV.sub hBtop).norm
  have hdp : Tendsto d (𝓝[>] p) atTop := by
    rw [tendsto_norm_atTop_iff_cobounded]
    exact (tendsto_const_sub_cobounded V).comp
      ((tendsto_schwarzChristoffelBoundary_cobounded_of_prevertex_sum_eq_neg_one
        a e z₀ p hp).mono_left (nhdsGT_le_nhdsNE p))
  have hcont : ContinuousOn d (Ioi p) := by
    exact (continuousOn_const.sub
      (continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one
        a e z₀ fun x hx => hfinite hx)).norm
  have hdpos {x : ℝ} (hx : x ∈ Ioi p) : 0 < d x := by
    rw [norm_pos_iff, sub_ne_zero]
    exact (schwarzChristoffelBoundary_ne_vertexAtInfinity_of_forall_le
      a e z₀ (hfinite hx) (fun i hi => (ha i hi).trans (le_of_lt hx)) hS).symm
  have hdimage : d '' Ioi p = Ioi 0 := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hdpos hx
    · exact isPreconnected_Ioi.intermediate_value_Ioi
        (le_principal_iff.mpr (Ioi_mem_atTop p))
        (le_principal_iff.mpr self_mem_nhdsWithin) hcont hdtop hdp
  have hangle {x : ℝ} (hx : p < x) : schwarzChristoffelEdgeAngle a e x = 0 := by
    rw [schwarzChristoffelEdgeAngle_eq_sum_filter, Finset.sum_eq_zero, mul_zero]
    intro i hi
    by_cases hei : e i = 0
    · exact hei
    · exact False.elim (hx.asymm ((Finset.mem_filter.mp hi).2.trans_le (ha i hei)))
  have hdir {x : ℝ} (hx : x ∈ Ioi p) : V - B x = (d x : ℂ) := by
    have h := schwarzChristoffelVertexAtInfinity_sub_boundary_eq_norm_mul
      a e z₀ (hfinite hx) (fun i hi => (ha i hi).trans (le_of_lt hx)) hS
    simpa only [B, V, d, hangle hx, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      mul_one] using h
  calc
    B '' Ioi p = (fun t : ℝ => V - (t : ℂ)) '' (d '' Ioi p) := by
      rw [← image_comp]
      apply image_congr
      intro x hx
      dsimp only [Function.comp_apply]
      linear_combination -(hdir hx)
    _ = (fun t : ℝ => V - (t : ℂ)) '' Ioi 0 := by rw [hdimage]

/-- **A left outer edge ending at a logarithmic prevertex is an open ray.**
If every nonzero prevertex lies at or to the right of `p`, the boundary values for parameters
strictly smaller than `p` form the ray from the finite value at parameter infinity in direction
`exp (π * (∑ i, e i) * I)`. The finite endpoint at parameter infinity is not attained. -/
theorem schwarzChristoffelBoundary_image_Iio_of_prevertex_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p : ℝ}
    (hp : ∑ i with a i = p, e i = -1)
    (ha : ∀ i, e i ≠ 0 → p ≤ a i) (hS : ∑ i, e i < -1) :
    schwarzChristoffelBoundary a e z₀ '' Iio p =
      (fun t : ℝ => schwarzChristoffelVertexAtInfinity a e z₀ +
        (t : ℂ) * exp ((Real.pi * ∑ i, e i) * Complex.I)) '' Ioi 0 := by
  classical
  let B : ℝ → ℂ := schwarzChristoffelBoundary a e z₀
  let V : ℂ := schwarzChristoffelVertexAtInfinity a e z₀
  let u : ℂ := exp ((Real.pi * ∑ i, e i) * Complex.I)
  let d : ℝ → ℝ := fun x => ‖B x - V‖
  have hsum {x : ℝ} (hx : x < p) : ∑ i with a i = x, e i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hax := (Finset.mem_filter.mp hi).2
    by_contra hei
    exact (not_le_of_gt hx) (hax ▸ ha i hei)
  have hfinite {x : ℝ} (hx : x < p) : -1 < ∑ i with a i = x, e i := by
    rw [hsum hx]
    norm_num
  have hBbot : Tendsto B atBot (𝓝 V) := by
    apply tendsto_schwarzChristoffelBoundaryValue_atInfinity a e z₀ hS
      tendsto_abs_atBot_atTop
    filter_upwards [eventually_lt_atBot p] with x hx
    exact tendsto_schwarzChristoffelPrimitive_boundary a e z₀ x (hfinite hx)
  have hdbot : Tendsto d atBot (𝓝 0) := by
    have hV : Tendsto (fun _ : ℝ => V) atBot (𝓝 V) := tendsto_const_nhds
    simpa [d] using (hBbot.sub hV).norm
  have hdp : Tendsto d (𝓝[<] p) atTop := by
    rw [tendsto_norm_atTop_iff_cobounded]
    exact (tendsto_sub_const_cobounded V).comp
      ((tendsto_schwarzChristoffelBoundary_cobounded_of_prevertex_sum_eq_neg_one
        a e z₀ p hp).mono_left (nhdsLT_le_nhdsNE p))
  have hcont : ContinuousOn d (Iio p) := by
    exact ((continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one
      a e z₀ fun x hx => hfinite hx).sub continuousOn_const).norm
  have hdpos {x : ℝ} (hx : x ∈ Iio p) : 0 < d x := by
    rw [norm_pos_iff, sub_ne_zero]
    exact schwarzChristoffelBoundary_ne_vertexAtInfinity_of_forall_ge
      a e z₀ (hfinite hx) (fun i hi => (le_of_lt hx).trans (ha i hi)) hS
  have hdimage : d '' Iio p = Ioi 0 := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hdpos hx
    · exact isPreconnected_Iio.intermediate_value_Ioi
        (le_principal_iff.mpr (Iio_mem_atBot p))
        (le_principal_iff.mpr self_mem_nhdsWithin) hcont hdbot hdp
  have hdir {x : ℝ} (hx : x ∈ Iio p) : B x - V = (d x : ℂ) * u := by
    simpa only [B, V, d, u] using
      schwarzChristoffelBoundary_sub_vertexAtInfinity_eq_norm_mul
        a e z₀ (hfinite hx) (fun i hi => (le_of_lt hx).trans (ha i hi)) hS
  calc
    B '' Iio p = (fun t : ℝ => V + (t : ℂ) * u) '' (d '' Iio p) := by
      rw [← image_comp]
      apply image_congr
      intro x hx
      dsimp only [Function.comp_apply]
      linear_combination hdir hx
    _ = (fun t : ℝ => V + (t : ℂ) * u) '' Ioi 0 := by rw [hdimage]

end TauCeti

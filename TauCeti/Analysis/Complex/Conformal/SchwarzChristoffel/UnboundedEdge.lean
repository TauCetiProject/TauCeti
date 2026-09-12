/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.ClosedEdge
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity
public import TauCeti.Analysis.Convex.Segment
public import TauCeti.Topology.Order.Interval

/-!
# The unbounded Schwarz--Christoffel boundary edges

Assume that all nonzero prevertices lie at or to the left of a real point `p`.  The canonical
boundary map then follows one straight edge on `Ici p`.  If the total exponent is less than `-1`,
the edge has a finite endpoint at `schwarzChristoffelVertexAtInfinity`; its image is the segment
from the value at `p` to that endpoint, with the endpoint at infinity omitted from the image.

This result supplies the boundary-edge description used when assembling the boundary of an
unbounded Schwarz--Christoffel polygon.  The endpoint at infinity is identified with the common
limit of the boundary map along the two unbounded real rays; the theorem records that this endpoint
is approached but not reached at a finite parameter.

## Main results

* `TauCeti.schwarzChristoffelBoundary_image_Ici` -- the right-hand unbounded boundary edge is the
  half-open segment from its finite endpoint to the vertex at infinity.
* `TauCeti.schwarzChristoffelBoundary_injOn_Ici` -- the right-hand unbounded boundary map is
  injective on its finite parameters.
* `TauCeti.schwarzChristoffelBoundary_image_Ici_prevertex` -- the same edge description with its
  finite endpoint expressed as a Schwarz--Christoffel vertex.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **The Schwarz--Christoffel boundary map is injective on a right-hand unbounded edge.**
Under the integrability hypothesis at `p` and the assumption that every nonzero prevertex lies at or
to the left of `p`, distinct finite parameters in `Ici p` have distinct boundary values. -/
theorem schwarzChristoffelBoundary_injOn_Ici (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p : ℝ}
    (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → a i ≤ p) :
    InjOn (schwarzChristoffelBoundary a e z₀) (Ici p) := by
  obtain ⟨hfree, hsum⟩ := interval_filter_sum_properties_of_forall_ne_zero_le a e hp ha
  intro x hx y hy hxy
  rcases lt_trichotomy x y with h | h | h
  · exact schwarzChristoffelBoundary_injOn_Icc a e z₀ (hfree hy) hp (hsum hy)
      ⟨hx, h.le⟩ ⟨hy, le_rfl⟩ hxy
  · exact h
  · exact (schwarzChristoffelBoundary_injOn_Icc a e z₀ (hfree hx) hp (hsum hx)
      ⟨hy, h.le⟩ ⟨hx, le_rfl⟩ hxy.symm).symm

/-- The image of the right-hand unbounded boundary edge is the segment from its finite endpoint to
the vertex at infinity, with the latter not attained at a finite boundary parameter. -/
theorem schwarzChristoffelBoundary_image_Ici (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p : ℝ}
    (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → a i ≤ p) (hS : ∑ i, e i < -1) :
    schwarzChristoffelBoundary a e z₀ '' Ici p =
      segment ℝ (schwarzChristoffelBoundary a e z₀ p)
        (schwarzChristoffelVertexAtInfinity a e z₀) \
          {schwarzChristoffelVertexAtInfinity a e z₀} := by
  let B : ℝ → ℂ := schwarzChristoffelBoundary a e z₀
  let V : ℂ := schwarzChristoffelVertexAtInfinity a e z₀
  let u : ℂ := Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I)
  let d : ℝ → ℝ := fun x => ‖B x - B p‖
  let D : ℝ := ‖V - B p‖
  -- To use the finite-edge lemmas on `[p, q]`, no nonzero prevertex may lie in its interior.
  obtain ⟨hfree, hsum⟩ := interval_filter_sum_properties_of_forall_ne_zero_le a e hp ha
  -- The endpoint `p` is integrable, and every later point is free of prevertices by `hfree`.
  have hcont : ContinuousOn B (Ici p) := by
    apply continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one
    intro x hx
    exact hsum hx
  have hformula : ∀ {x : ℝ}, x ∈ Ici p →
      B x - B p = ((d x : ℝ) : ℂ) * u := by
    intro x hx
    have h := schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀ (hfree hx) hp (hsum hx)
      (x := x) (y := p) ⟨hx, le_rfl⟩ ⟨le_rfl, hx⟩ hx
    simpa [B, d, u] using h
  have hBtop : Tendsto B atTop (𝓝 V) := by
    apply tendsto_schwarzChristoffelBoundaryValue_atInfinity a e z₀ hS
      tendsto_abs_atTop_atTop
    filter_upwards [eventually_ge_atTop p] with x hx
    exact tendsto_schwarzChristoffelPrimitive_boundary a e z₀ x (hsum hx)
  have hdl : Tendsto d atTop (𝓝 D) := by
    simpa [d, D] using (hBtop.sub tendsto_const_nhds).norm
  have hdcont : ContinuousOn d (Ici p) := by
    exact (hcont.sub continuousOn_const).norm
  have hdmono : StrictMonoOn d (Ici p) := by
    intro x hx y hy hxy
    have hsumxy := norm_schwarzChristoffelBoundary_sub_add a e z₀ (hfree hy) hp (hsum hy)
      (x := p) (y := x) (z := y) ⟨le_rfl, hy⟩ ⟨hx, hxy.le⟩ ⟨hy, le_rfl⟩ hx hxy.le
    have hinj := schwarzChristoffelBoundary_injOn_Ici a e z₀ hp ha
    have hne : B y ≠ B x := by
      intro h
      have : y = x := hinj hy hx h
      exact hxy.ne this.symm
    have hpos : 0 < ‖B y - B x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hsumxy' : d y = d x + ‖B y - B x‖ := by simpa [d, B] using hsumxy
    rw [hsumxy']
    exact lt_add_of_pos_right _ hpos
  -- Strict monotonicity and the limit at infinity identify the distance parameter's image.
  have hdimage : d '' Ici p = Ico 0 D := by
    simpa [d] using image_Ici_of_continuousOn_of_strictMonoOn_of_tendsto hdcont hdmono hdl
  have hDpos : 0 < D := by
    have hp1 : p + 1 ∈ Ici p := by
      exact mem_Ici.mpr (le_add_of_nonneg_right (by norm_num))
    have hpp1 : p < p + 1 := by linarith
    have hstrict := hdmono self_mem_Ici hp1
      hpp1
    have hle : d (p + 1) ≤ D := by
      apply ge_of_tendsto hdl
      filter_upwards [eventually_ge_atTop (p + 1)] with y hxy
      have hy : y ∈ Ici p := hp1.trans hxy
      exact hdmono.monotoneOn hp1 hy hxy
    simpa [d, D] using hstrict.trans_le hle
  -- The boundary displacement has the same limiting direction and length as the distance ray.
  have hVdir : V - B p = ((D : ℝ) : ℂ) * u := by
    have hright : Tendsto (fun x => ((d x : ℝ) : ℂ) * u) atTop
        (𝓝 (((D : ℝ) : ℂ) * u)) := by
      exact ((Complex.continuous_ofReal.tendsto D).comp hdl).mul_const u
    apply tendsto_nhds_unique (hBtop.sub tendsto_const_nhds)
    exact hright.congr' ((eventually_ge_atTop p).mono fun x hx => (hformula hx).symm)
  -- Convert the half-open scalar interval into the geometric segment with its terminal point
  -- removed.
  have hscalar : (fun t : ℝ => B p + (t : ℂ) * u) '' Ico 0 D =
      segment ℝ (B p) V \ {V} := by
    simpa only [Complex.real_smul] using image_add_smul_Ico hDpos
      (Complex.exp_ne_zero (schwarzChristoffelEdgeAngle a e p * Complex.I)) hVdir
  have hBimage : B '' Ici p = (fun t : ℝ => B p + (t : ℂ) * u) '' (d '' Ici p) := by
    apply Set.Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      have h : B p + ((d x : ℝ) : ℂ) * u = B x := by
        calc
          B p + ((d x : ℝ) : ℂ) * u = B p + (B x - B p) := by rw [hformula hx]
          _ = B x := by abel
      exact ⟨d x, mem_image_of_mem d hx, h⟩
    · rintro z ⟨t, ⟨x, hx, rfl⟩, rfl⟩
      have h : B x = B p + ((d x : ℝ) : ℂ) * u := by
        calc
          B x = B p + (B x - B p) := by abel
          _ = B p + ((d x : ℝ) : ℂ) * u := by rw [hformula hx]
      exact ⟨x, hx, h⟩
  rw [hBimage, hdimage, hscalar]

/-- The right-hand unbounded edge based at a prevertex starts at its corresponding
Schwarz--Christoffel vertex. -/
theorem schwarzChristoffelBoundary_image_Ici_prevertex (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (j : ι) (hj : -1 < ∑ i with a i = a j, e i)
    (ha : ∀ i, e i ≠ 0 → a i ≤ a j) (hS : ∑ i, e i < -1) :
    schwarzChristoffelBoundary a e z₀ '' Ici (a j) =
      segment ℝ (schwarzChristoffelVertex a e z₀ j)
        (schwarzChristoffelVertexAtInfinity a e z₀) \
          {schwarzChristoffelVertexAtInfinity a e z₀} := by
  rw [schwarzChristoffelBoundary_image_Ici a e z₀ hj ha hS,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ j hj]

end TauCeti

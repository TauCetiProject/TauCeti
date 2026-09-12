/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.ClosedEdge
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity

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

private theorem image_Ici_of_continuousOn_strictMonoOn_tendsto {d : ℝ → ℝ} {p D : ℝ}
    (hdp : d p = 0) (hdcont : ContinuousOn d (Ici p))
    (hdmono : StrictMonoOn d (Ici p)) (hdl : Tendsto d atTop (𝓝 D)) :
    d '' Ici p = Ico 0 D := by
  have hle : ∀ x ∈ Ici p, d x ≤ D := by
    intro x hx
    apply ge_of_tendsto hdl
    filter_upwards [eventually_ge_atTop x] with y hxy
    have hy : y ∈ Ici p := hx.trans hxy
    exact hdmono.monotoneOn hx hy hxy
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hxp : p ≤ x := hx
    have hx1 : x + 1 ∈ Ici p := by
      exact le_trans hxp (by linarith)
    have hlt : d x < D := lt_of_lt_of_le
      (hdmono hx hx1 (by linarith)) (hle (x + 1) hx1)
    exact ⟨by rw [← hdp]; exact hdmono.monotoneOn self_mem_Ici hx hxp, hlt⟩
  · rw [← hdp]
    exact isPreconnected_Ici.intermediate_value_Ico self_mem_Ici
      (le_principal_iff.mpr (Ici_mem_atTop p)) hdcont hdl

private theorem image_add_real_smul_Ico {x y u : ℂ} {D : ℝ} (hDpos : 0 < D) (hu : u ≠ 0)
    (hdir : y - x = ((D : ℝ) : ℂ) * u) :
    (fun t : ℝ => x + (t : ℂ) * u) '' Ico 0 D = segment ℝ x y \ {y} := by
  rw [segment_eq_image' ℝ]
  apply Subset.antisymm
  · rintro z ⟨t, ⟨ht0, htD⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · refine ⟨t / D, ⟨div_nonneg ht0 hDpos.le, (div_lt_one hDpos).2 htD |>.le⟩, ?_⟩
      rw [hdir]
      simp only [Complex.real_smul]
      push_cast
      field_simp [hDpos.ne']
    · intro h
      apply htD.ne
      have hEq : x + ((t : ℂ) * u) = y := by simpa using h
      have hmul : (t : ℂ) * u = (D : ℂ) * u := by
        calc
          (t : ℂ) * u = x + (t : ℂ) * u - x := by abel
          _ = y - x := by rw [hEq]
          _ = (D : ℂ) * u := hdir
      exact_mod_cast (mul_right_cancel₀ hu hmul)
  · intro z hz
    rcases hz with ⟨hzseg, hzYnot⟩
    rcases hzseg with ⟨t, ht, rfl⟩
    have htD : t < 1 := by
      by_contra hnot
      have hteq : t = 1 := le_antisymm ht.2 (le_of_not_gt hnot)
      apply hzYnot
      simp only [Set.mem_singleton_iff]
      rw [hteq]
      simp only [Complex.real_smul, ofReal_one, one_mul]
      abel
    refine ⟨t * D, ⟨mul_nonneg ht.1 hDpos.le, ?_⟩, ?_⟩
    · nlinarith [ht.2, hDpos]
    · simp only [Complex.real_smul]
      rw [hdir]
      push_cast
      ring

/-- **The Schwarz--Christoffel boundary map is injective on a right-hand unbounded edge.**
Under the same integrability and prevertex hypotheses as the image theorem, distinct finite
parameters in `Ici p` have distinct boundary values. -/
theorem schwarzChristoffelBoundary_injOn_Ici (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p : ℝ}
    (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → a i ≤ p) :
    InjOn (schwarzChristoffelBoundary a e z₀) (Ici p) := by
  have hfree : ∀ {q : ℝ}, q ∈ Ici p → ∀ i, e i ≠ 0 → a i ∉ Ioo p q := by
    intro q hq i hei hi
    exact (not_lt_of_ge (ha i hei)) hi.1
  have hsum : ∀ {q : ℝ}, q ∈ Ici p → -1 < ∑ i with a i = q, e i := by
    intro q hq
    have hq' : p ≤ q := hq
    rcases eq_or_lt_of_le hq' with hqp | hpq
    · subst q
      exact hp
    · have hz : ∀ i, i ∈ Finset.univ.filter (fun i => a i = q) → e i = 0 := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        by_contra hei
        have hai := ha i hei
        have hiq : p < a i := hi ▸ hpq
        linarith
      rw [Finset.sum_eq_zero hz]
      norm_num
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
  have hfree : ∀ {q : ℝ}, q ∈ Ici p → ∀ i, e i ≠ 0 → a i ∉ Ioo p q := by
    intro q hq i hei hi
    exact (not_lt_of_ge (ha i hei)) hi.1
  have hsum : ∀ {q : ℝ}, q ∈ Ici p → -1 < ∑ i with a i = q, e i := by
    intro q hq
    have hq' : p ≤ q := hq
    rcases eq_or_lt_of_le hq' with hqp | hpq
    · subst q
      exact hp
    · have hz : ∀ i, i ∈ Finset.univ.filter (fun i => a i = q) → e i = 0 := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        by_contra hei
        have hai := ha i hei
        have hiq : p < a i := hi ▸ hpq
        linarith
      rw [Finset.sum_eq_zero hz]
      norm_num
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
  have hdimage : d '' Ici p = Ico 0 D := image_Ici_of_continuousOn_strictMonoOn_tendsto
    (by simp [d]) hdcont hdmono hdl
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
      segment ℝ (B p) V \ {V} := image_add_real_smul_Ico hDpos
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

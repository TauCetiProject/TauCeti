/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.ClosedEdge
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity
public import TauCeti.Analysis.Convex.Segment
public import TauCeti.Algebra.Order.BigOperators.Sum.Filter
public import TauCeti.Topology.Order.Interval

/-!
# The unbounded Schwarz--Christoffel boundary edges

Assume that all prevertices having nonzero exponent lie on one side of a real point `p`, and that
the sum of the exponents at `p` is greater than `-1`.  The canonical boundary map then follows one
straight edge on the corresponding half-line.  If the total exponent is less than `-1`, the edge
has a finite endpoint at `schwarzChristoffelVertexAtInfinity`; together with the local exponent-sum
hypothesis, its image is the segment from the value at `p` to that endpoint, with the endpoint at
infinity omitted from the image.

This result supplies the boundary-edge description used when assembling the boundary of an
unbounded Schwarz--Christoffel polygon.  The endpoint at infinity is identified with the common
limit of the boundary map along the two unbounded real rays; the theorem records that this endpoint
is approached but not reached at a finite parameter.

## Main results

* `TauCeti.schwarzChristoffelBoundary_image_Ici` and
  `TauCeti.schwarzChristoffelBoundary_image_Iic` -- the right- and left-hand unbounded boundary
  edges are half-open segments from their finite endpoints to the vertex at infinity.
* `TauCeti.schwarzChristoffelBoundary_injOn_Ici` and
  `TauCeti.schwarzChristoffelBoundary_injOn_Iic` -- the two unbounded boundary maps are injective
  on their finite parameters.
* `TauCeti.schwarzChristoffelVertexAtInfinity_sub_boundary_eq_norm_mul` and
  `TauCeti.schwarzChristoffelBoundary_sub_vertexAtInfinity_eq_norm_mul` -- the endpoint vectors
  of the two unbounded sides have the expected directions.
* `TauCeti.schwarzChristoffelBoundary_image_Ici_prevertex` and
  `TauCeti.schwarzChristoffelBoundary_image_Iic_prevertex` -- the same edge descriptions with the
  finite endpoints expressed as Schwarz--Christoffel vertices.
* `TauCeti.schwarzChristoffelBoundary_ne_vertexAtInfinity_of_forall_le` and
  `TauCeti.schwarzChristoffelBoundary_ne_vertexAtInfinity_of_forall_ge` -- the finite endpoint of
  either unbounded edge differs from its endpoint at infinity.

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
Under `-1 < ∑ i with a i = p, e i` and `∀ i, e i ≠ 0 → a i ≤ p`, distinct finite parameters in
`Ici p` have distinct boundary values. -/
theorem schwarzChristoffelBoundary_injOn_Ici (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p : ℝ}
    (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → a i ≤ p) :
    InjOn (schwarzChristoffelBoundary a e z₀) (Ici p) := by
  have hfree : ∀ {q : ℝ}, q ∈ Ici p → ∀ i, e i ≠ 0 → a i ∉ Ioo p q :=
    fun _ i hei hi => (not_lt_of_ge (ha i hei)) hi.1
  have hsum : ∀ {q : ℝ}, q ∈ Ici p → -1 < ∑ i with a i = q, e i :=
    fun {q} hq => by
      simpa using
        (Finset.lt_sum_filter_of_lt_zero_of_forall_ne_zero_le (β := ℝ) (a := a) (e := e)
          (p := p) (c := -1) Finset.univ (by norm_num) (by simpa using hp) (by simpa using ha) hq)
  intro x hx y hy hxy
  rcases lt_trichotomy x y with h | h | h
  · exact schwarzChristoffelBoundary_injOn_Icc a e z₀ (hfree hy) hp (hsum hy)
      ⟨hx, h.le⟩ ⟨hy, le_rfl⟩ hxy
  · exact h
  · exact (schwarzChristoffelBoundary_injOn_Icc a e z₀ (hfree hx) hp (hsum hx)
      ⟨hy, h.le⟩ ⟨hx, le_rfl⟩ hxy.symm).symm

/-- The vector from the finite endpoint of a right-hand unbounded Schwarz--Christoffel edge to
its vertex at infinity has the direction of that edge. -/
theorem schwarzChristoffelVertexAtInfinity_sub_boundary_eq_norm_mul
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p : ℝ}
    (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → a i ≤ p) (hS : ∑ i, e i < -1) :
    schwarzChristoffelVertexAtInfinity a e z₀ - schwarzChristoffelBoundary a e z₀ p =
      (‖schwarzChristoffelVertexAtInfinity a e z₀ -
        schwarzChristoffelBoundary a e z₀ p‖ : ℂ) *
        Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) := by
  let B : ℝ → ℂ := schwarzChristoffelBoundary a e z₀
  let V : ℂ := schwarzChristoffelVertexAtInfinity a e z₀
  let u : ℂ := Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I)
  have hfree : ∀ {q : ℝ}, q ∈ Ici p → ∀ i, e i ≠ 0 → a i ∉ Ioo p q :=
    fun _ i hei hi ↦ (not_lt_of_ge (ha i hei)) hi.1
  have hsum : ∀ {q : ℝ}, q ∈ Ici p → -1 < ∑ i with a i = q, e i :=
    fun {q} hq ↦ by
      simpa using
        (Finset.lt_sum_filter_of_lt_zero_of_forall_ne_zero_le (β := ℝ) (a := a) (e := e)
          (p := p) (c := -1) Finset.univ (by norm_num) (by simpa using hp) (by simpa using ha) hq)
  have hformula : ∀ {x : ℝ}, x ∈ Ici p →
      B x - B p = ((‖B x - B p‖ : ℝ) : ℂ) * u := by
    intro x hx
    simpa [B, u] using
      schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀ (hfree hx) hp (hsum hx)
        (x := x) (y := p) ⟨hx, le_rfl⟩ ⟨le_rfl, hx⟩ hx
  have hBtop : Tendsto B atTop (𝓝 V) := by
    apply tendsto_schwarzChristoffelBoundaryValue_atInfinity a e z₀ hS
      tendsto_abs_atTop_atTop
    filter_upwards [eventually_ge_atTop p] with x hx
    exact tendsto_schwarzChristoffelPrimitive_boundary a e z₀ x (hsum hx)
  have hnorm : Tendsto (fun x ↦ ‖B x - B p‖) atTop (𝓝 ‖V - B p‖) :=
    (hBtop.sub tendsto_const_nhds).norm
  have hright : Tendsto (fun x ↦ ((‖B x - B p‖ : ℝ) : ℂ) * u) atTop
      (𝓝 (((‖V - B p‖ : ℝ) : ℂ) * u)) :=
    ((Complex.continuous_ofReal.tendsto _).comp hnorm).mul_const u
  apply tendsto_nhds_unique (hBtop.sub tendsto_const_nhds)
  exact hright.congr' ((eventually_ge_atTop p).mono fun _ hx ↦ (hformula hx).symm)

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
  have hfree : ∀ {q : ℝ}, q ∈ Ici p → ∀ i, e i ≠ 0 → a i ∉ Ioo p q :=
    fun _ i hei hi => (not_lt_of_ge (ha i hei)) hi.1
  have hsum : ∀ {q : ℝ}, q ∈ Ici p → -1 < ∑ i with a i = q, e i :=
    fun {q} hq => by
      simpa using
        (Finset.lt_sum_filter_of_lt_zero_of_forall_ne_zero_le (β := ℝ) (a := a) (e := e)
          (p := p) (c := -1) Finset.univ (by norm_num) (by simpa using hp) (by simpa using ha) hq)
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
    simpa [d] using hdcont.image_Ici_of_strictMonoOn_of_tendsto hdmono hdl
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
  have hVdir : V - B p = ((D : ℝ) : ℂ) * u := by
    simpa [B, V, D, u] using
      schwarzChristoffelVertexAtInfinity_sub_boundary_eq_norm_mul a e z₀ hp ha hS
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

/-- The finite endpoint of a right-hand unbounded Schwarz--Christoffel edge differs from its
endpoint at infinity.  Thus the segment traced by the edge is nondegenerate. -/
theorem schwarzChristoffelBoundary_ne_vertexAtInfinity_of_forall_le (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p : ℝ} (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → a i ≤ p) (hS : ∑ i, e i < -1) :
    schwarzChristoffelBoundary a e z₀ p ≠ schwarzChristoffelVertexAtInfinity a e z₀ := by
  intro h
  have hpimage : schwarzChristoffelBoundary a e z₀ p ∈
      schwarzChristoffelBoundary a e z₀ '' Ici p := ⟨p, self_mem_Ici, rfl⟩
  rw [schwarzChristoffelBoundary_image_Ici a e z₀ hp ha hS, h] at hpimage
  exact hpimage.2 rfl

/-! ### The left-hand edge -/

/-- **The Schwarz--Christoffel boundary map is injective on a left-hand unbounded edge.**
Under `-1 < ∑ i with a i = p, e i` and `∀ i, e i ≠ 0 → p ≤ a i`, distinct finite
parameters in `Iic p` have distinct boundary values. -/
theorem schwarzChristoffelBoundary_injOn_Iic (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p : ℝ}
    (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → p ≤ a i) :
    InjOn (schwarzChristoffelBoundary a e z₀) (Iic p) := by
  have hfree : ∀ {q : ℝ}, q ∈ Iic p → ∀ i, e i ≠ 0 → a i ∉ Ioo q p :=
    fun _ i hei hi => (not_lt_of_ge (ha i hei)) hi.2
  have hsum : ∀ {q : ℝ}, q ∈ Iic p → -1 < ∑ i with a i = q, e i :=
    fun {_} hq =>
      Finset.lt_sum_filter_of_lt_zero_of_forall_ne_zero_le (γ := OrderDual ℝ)
        Finset.univ (by norm_num) hp (by intro i _ hei; exact ha i hei) hq
  intro x hx y hy hxy
  rcases lt_trichotomy x y with h | h | h
  · exact schwarzChristoffelBoundary_injOn_Icc a e z₀ (hfree hx) (hsum hx) hp
      ⟨le_rfl, hx⟩ ⟨h.le, hy⟩ hxy
  · exact h
  · exact (schwarzChristoffelBoundary_injOn_Icc a e z₀ (hfree hy) (hsum hy) hp
      ⟨le_rfl, hy⟩ ⟨h.le, hx⟩ hxy.symm).symm

/-- The vector from the vertex at infinity of a left-hand unbounded Schwarz--Christoffel edge to
its finite endpoint has the direction of that edge. -/
theorem schwarzChristoffelBoundary_sub_vertexAtInfinity_eq_norm_mul
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p : ℝ}
    (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → p ≤ a i) (hS : ∑ i, e i < -1) :
    schwarzChristoffelBoundary a e z₀ p - schwarzChristoffelVertexAtInfinity a e z₀ =
      (‖schwarzChristoffelBoundary a e z₀ p -
        schwarzChristoffelVertexAtInfinity a e z₀‖ : ℂ) *
        Complex.exp ((Real.pi * ∑ i, e i) * Complex.I) := by
  let B : ℝ → ℂ := schwarzChristoffelBoundary a e z₀
  let V : ℂ := schwarzChristoffelVertexAtInfinity a e z₀
  let u : ℂ := Complex.exp ((Real.pi * ∑ i, e i) * Complex.I)
  have hfree : ∀ {q : ℝ}, q ∈ Iic p → ∀ i, e i ≠ 0 → a i ∉ Ioo q p :=
    fun _ i hei hi ↦ (not_lt_of_ge (ha i hei)) hi.2
  have hsum : ∀ {q : ℝ}, q ∈ Iic p → -1 < ∑ i with a i = q, e i :=
    fun {_} hq ↦
      Finset.lt_sum_filter_of_lt_zero_of_forall_ne_zero_le (γ := OrderDual ℝ)
        Finset.univ (by norm_num) hp (by intro i _ hei; exact ha i hei) hq
  have hangle : ∀ {x : ℝ}, x < p →
      schwarzChristoffelEdgeAngle a e x = Real.pi * ∑ i, e i := by
    intro x hx
    rw [schwarzChristoffelEdgeAngle_eq_sum_filter, Finset.sum_filter]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rcases eq_or_ne (e i) 0 with hei | hei
    · simp [hei]
    · simp [hx.trans_le (ha i hei)]
  have hformula : ∀ {x : ℝ}, x ∈ Iic p →
      B p - B x = ((‖B p - B x‖ : ℝ) : ℂ) * u := by
    intro x hx
    rcases eq_or_lt_of_le (mem_Iic.mp hx) with rfl | hxp
    · simp
    · simpa [B, u, hangle hxp] using
        schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀ (hfree hx) (hsum hx) hp
          (x := p) (y := x) ⟨hx, le_rfl⟩ ⟨le_rfl, hx⟩ hx
  have hBbot : Tendsto B atBot (𝓝 V) := by
    apply tendsto_schwarzChristoffelBoundaryValue_atInfinity a e z₀ hS
      tendsto_abs_atBot_atTop
    filter_upwards [eventually_le_atBot p] with x hx
    exact tendsto_schwarzChristoffelPrimitive_boundary a e z₀ x (hsum hx)
  have hnorm : Tendsto (fun x ↦ ‖B p - B x‖) atBot (𝓝 ‖B p - V‖) :=
    (tendsto_const_nhds.sub hBbot).norm
  have hright : Tendsto (fun x ↦ ((‖B p - B x‖ : ℝ) : ℂ) * u) atBot
      (𝓝 (((‖B p - V‖ : ℝ) : ℂ) * u)) :=
    ((Complex.continuous_ofReal.tendsto _).comp hnorm).mul_const u
  apply tendsto_nhds_unique (tendsto_const_nhds.sub hBbot)
  exact hright.congr' ((eventually_le_atBot p).mono fun _ hx ↦ (hformula hx).symm)

/-- The image of the left-hand unbounded boundary edge is the segment from its finite endpoint to
the vertex at infinity, with the latter not attained at a finite boundary parameter. -/
theorem schwarzChristoffelBoundary_image_Iic (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p : ℝ}
    (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → p ≤ a i) (hS : ∑ i, e i < -1) :
    schwarzChristoffelBoundary a e z₀ '' Iic p =
      segment ℝ (schwarzChristoffelBoundary a e z₀ p)
        (schwarzChristoffelVertexAtInfinity a e z₀) \
          {schwarzChristoffelVertexAtInfinity a e z₀} := by
  let B : ℝ → ℂ := schwarzChristoffelBoundary a e z₀
  let V : ℂ := schwarzChristoffelVertexAtInfinity a e z₀
  let u : ℂ := Complex.exp ((Real.pi * ∑ i, e i) * Complex.I)
  let d : ℝ → ℝ := fun x => ‖B p - B x‖
  let D : ℝ := ‖B p - V‖
  -- To use the finite-edge lemmas on `[q, p]`, no nonzero prevertex may lie in its interior.
  have hfree : ∀ {q : ℝ}, q ∈ Iic p → ∀ i, e i ≠ 0 → a i ∉ Ioo q p :=
    fun _ i hei hi => (not_lt_of_ge (ha i hei)) hi.2
  have hsum : ∀ {q : ℝ}, q ∈ Iic p → -1 < ∑ i with a i = q, e i :=
    fun {_} hq =>
      Finset.lt_sum_filter_of_lt_zero_of_forall_ne_zero_le (γ := OrderDual ℝ)
        Finset.univ (by norm_num) hp (by intro i _ hei; exact ha i hei) hq
  have hangle : ∀ {x : ℝ}, x < p →
      schwarzChristoffelEdgeAngle a e x = Real.pi * ∑ i, e i := by
    intro x hx
    rw [schwarzChristoffelEdgeAngle_eq_sum_filter, Finset.sum_filter]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rcases eq_or_ne (e i) 0 with hei | hei
    · simp [hei]
    · simp [hx.trans_le (ha i hei)]
  have hcont : ContinuousOn B (Iic p) := by
    apply continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one
    intro x hx
    exact hsum hx
  have hformula : ∀ {x : ℝ}, x ∈ Iic p →
      B p - B x = ((d x : ℝ) : ℂ) * u := by
    intro x hx
    rcases eq_or_lt_of_le (mem_Iic.mp hx) with rfl | hxp
    · simp [d]
    · have h := schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀ (hfree hx) (hsum hx) hp
        (x := p) (y := x) ⟨hx, le_rfl⟩ ⟨le_rfl, hx⟩ hx
      simpa [B, d, u, hangle hxp] using h
  have hBbot : Tendsto B atBot (nhds V) := by
    apply tendsto_schwarzChristoffelBoundaryValue_atInfinity a e z₀ hS
      tendsto_abs_atBot_atTop
    filter_upwards [eventually_le_atBot p] with x hx
    exact tendsto_schwarzChristoffelPrimitive_boundary a e z₀ x (hsum hx)
  have hdl : Tendsto d atBot (nhds D) := by
    simpa [d, D] using (tendsto_const_nhds.sub hBbot).norm
  have hdcont : ContinuousOn d (Iic p) := by
    exact (continuousOn_const.sub hcont).norm
  have hdanti : StrictAntiOn d (Iic p) := by
    intro x hx y hy hxy
    have hsumxy := norm_schwarzChristoffelBoundary_sub_add a e z₀ (hfree hx) (hsum hx) hp
      (x := x) (y := y) (z := p) ⟨le_rfl, hx⟩ ⟨hxy.le, hy⟩ ⟨hx, le_rfl⟩ hxy.le hy
    have hinj := schwarzChristoffelBoundary_injOn_Iic a e z₀ hp ha
    have hne : B y ≠ B x := by
      intro h
      have : y = x := hinj hy hx h
      exact hxy.ne this.symm
    have hpos : 0 < ‖B y - B x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hsumxy' : d x = ‖B y - B x‖ + d y := by simpa [d, B] using hsumxy
    rw [hsumxy']
    exact lt_add_of_pos_left _ hpos
  -- Strict antitonicity and the limit at infinity identify the distance parameter's image.
  have hdimage : d '' Iic p = Ico 0 D := by
    have himage : d '' Iic p = Ico (d p) D := by
      exact ContinuousOn.image_Ici_of_strictMonoOn_of_tendsto (α := OrderDual ℝ)
        hdcont (fun x hx y hy hxy => hdanti hy hx hxy) hdl
    simpa [d] using himage
  have hDpos : 0 < D := by
    have hp1 : p - 1 ∈ Iic p := by
      exact mem_Iic.mpr (sub_le_self p (by norm_num))
    have hp1p : p - 1 < p := by linarith
    have hstrict := hdanti hp1 self_mem_Iic hp1p
    have hle : d (p - 1) ≤ D := by
      apply ge_of_tendsto hdl
      filter_upwards [eventually_le_atBot (p - 1)] with y hxy
      have hy : y ∈ Iic p := hxy.trans hp1
      exact hdanti.antitoneOn hy hp1 hxy
    simpa [d, D] using hstrict.trans_le hle
  have hVdir : V - B p = ((D : ℝ) : ℂ) * (-u) := by
    have hleft : B p - V = ((D : ℝ) : ℂ) * u := by
      simpa [B, V, D, u] using
        schwarzChristoffelBoundary_sub_vertexAtInfinity_eq_norm_mul a e z₀ hp ha hS
    calc
      V - B p = -(B p - V) := by abel
      _ = -(((D : ℝ) : ℂ) * u) := congrArg Neg.neg hleft
      _ = ((D : ℝ) : ℂ) * (-u) := by ring
  have hscalar : (fun t : ℝ => B p + (t : ℂ) * (-u)) '' Ico 0 D =
      segment ℝ (B p) V \ {V} := by
    simpa only [Complex.real_smul] using image_add_smul_Ico hDpos
      (neg_ne_zero.mpr (Complex.exp_ne_zero ((Real.pi * ∑ i, e i) * Complex.I))) hVdir
  have hBimage : B '' Iic p = (fun t : ℝ => B p + (t : ℂ) * (-u)) '' (d '' Iic p) := by
    apply Set.Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      have h : B p + ((d x : ℝ) : ℂ) * (-u) = B x := by
        calc
          B p + ((d x : ℝ) : ℂ) * (-u) = B p - ((d x : ℝ) : ℂ) * u := by ring
          _ = B x := by rw [← hformula hx]; abel
      exact ⟨d x, mem_image_of_mem d hx, h⟩
    · rintro z ⟨t, ⟨x, hx, rfl⟩, rfl⟩
      have h : B x = B p + ((d x : ℝ) : ℂ) * (-u) := by
        calc
          B x = B p - (B p - B x) := by abel
          _ = B p - ((d x : ℝ) : ℂ) * u := by rw [hformula hx]
          _ = B p + ((d x : ℝ) : ℂ) * (-u) := by ring
      exact ⟨x, hx, h⟩
  rw [hBimage, hdimage, hscalar]

/-- The left-hand unbounded edge based at a prevertex starts at its corresponding
Schwarz--Christoffel vertex. -/
theorem schwarzChristoffelBoundary_image_Iic_prevertex (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (j : ι) (hj : -1 < ∑ i with a i = a j, e i)
    (ha : ∀ i, e i ≠ 0 → a j ≤ a i) (hS : ∑ i, e i < -1) :
    schwarzChristoffelBoundary a e z₀ '' Iic (a j) =
      segment ℝ (schwarzChristoffelVertex a e z₀ j)
        (schwarzChristoffelVertexAtInfinity a e z₀) \
          {schwarzChristoffelVertexAtInfinity a e z₀} := by
  rw [schwarzChristoffelBoundary_image_Iic a e z₀ hj ha hS,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ j hj]

/-- The finite endpoint of a left-hand unbounded Schwarz--Christoffel edge differs from its
endpoint at infinity.  Thus the segment traced by the edge is nondegenerate. -/
theorem schwarzChristoffelBoundary_ne_vertexAtInfinity_of_forall_ge (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p : ℝ} (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → p ≤ a i) (hS : ∑ i, e i < -1) :
    schwarzChristoffelBoundary a e z₀ p ≠ schwarzChristoffelVertexAtInfinity a e z₀ := by
  intro h
  have hpimage : schwarzChristoffelBoundary a e z₀ p ∈
      schwarzChristoffelBoundary a e z₀ '' Iic p := ⟨p, self_mem_Iic, rfl⟩
  rw [schwarzChristoffelBoundary_image_Iic a e z₀ hp ha hS, h] at hpimage
  exact hpimage.2 rfl

end TauCeti

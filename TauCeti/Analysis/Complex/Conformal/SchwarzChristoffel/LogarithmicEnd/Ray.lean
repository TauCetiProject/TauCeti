/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.LogarithmicEnd.Basic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.ClosedEdge

/-!
# Boundary rays and lines at logarithmic prevertices

A prevertex of total exponent `-1` represents infinity. The ordinary boundary values escape
to infinity on both sides of this parameter. An edge joining an integrable parameter to such
a prevertex therefore traces a complete closed ray, with direction determined by the usual
Schwarz--Christoffel edge angle. The finite endpoint is attained and the logarithmic parameter
is excluded. An edge between two logarithmic endpoints traces a complete affine line.

These formulas describe the unbounded sides of polygonal boundaries with several logarithmic
ends. They require no conditions on other edges, the total exponent, or global injectivity.
Coincident prevertices are allowed: only the total exponent at either endpoint matters.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Bornology Complex Filter Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The ordinary boundary values escape to infinity on both sides of a logarithmic
prevertex. No assumptions on the exponents at other prevertices are needed. -/
theorem tendsto_schwarzChristoffelBoundary_cobounded_of_prevertex_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (p : ℝ)
    (he : ∑ i with a i = p, e i = -1) :
    Tendsto (schwarzChristoffelBoundary a e z₀) (𝓝[≠] p) (cobounded ℂ) := by
  classical
  have hregular : ∀ᶠ x in 𝓝[≠] p, ∀ i, a i ≠ x := by
    rw [eventually_all]
    intro i
    by_cases hi : a i = p
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa [hi, eq_comm] using hx
    · exact (eventually_ne_nhdsWithin (Ne.symm hi)).mono fun _ hx => Ne.symm hx
  have hF := tendsto_norm_atTop_iff_cobounded.mpr
    (tendsto_schwarzChristoffelPrimitive_cobounded_of_prevertex_sum_eq_neg_one a e z₀ p he)
  rw [← tendsto_norm_atTop_iff_cobounded, Filter.tendsto_atTop]
  intro R
  obtain ⟨r, hr, hFr⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp
    (hF.eventually (eventually_ge_atTop (R + 1)))
  have hball : ∀ᶠ x : ℝ in 𝓝[≠] p, (x : ℂ) ∈ ball (p : ℂ) r :=
    (continuous_ofReal.tendsto p).mono_left nhdsWithin_le_nhds |>.eventually
      (ball_mem_nhds _ hr)
  filter_upwards [hregular, hball] with x hx hxr
  have hsum : ∑ i with a i = x, e i = 0 := by
    simp [Finset.filter_eq_empty_iff.mpr (fun i _ => hx i)]
  have hB := (tendsto_schwarzChristoffelPrimitive_boundary a e z₀ x
    (by rw [hsum]; norm_num)).norm
  have := Real.nhdsWithin_upperHalfPlaneSet_neBot x
  have hbound : R + 1 ≤ ‖schwarzChristoffelBoundary a e z₀ x‖ := by
    apply ge_of_tendsto hB
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hxr)] with z hz hzr
    exact hFr ⟨hzr, hz⟩
  linarith

/-- An edge whose right endpoint is logarithmic traces the entire closed ray starting at
its integrable left endpoint, in the positive edge direction. -/
theorem schwarzChristoffelBoundary_image_Ico_eq_ray_of_right_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p q : ℝ} (hpq : p < q)
    (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : ∑ i with a i = q, e i = -1) :
    schwarzChristoffelBoundary a e z₀ '' Ico p q =
      (fun t : ℝ => schwarzChristoffelBoundary a e z₀ p +
        (t : ℂ) * exp (schwarzChristoffelEdgeAngle a e p * Complex.I)) '' Ici 0 := by
  classical
  let B := schwarzChristoffelBoundary a e z₀
  let d : ℝ → ℝ := fun x => ‖B x - B p‖
  have hsum {x : ℝ} (hx : x ∈ Ico p q) : -1 < ∑ i with a i = x, e i := by
    rcases hx.1.eq_or_lt with rfl | hpx
    · exact hp
    have hzero : ∑ i with a i = x, e i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      by_contra hei
      exact ha i hei (hi' ▸ ⟨hpx, hx.2⟩)
    rw [hzero]
    norm_num
  have hcont : ContinuousOn B (Ico p q) :=
    continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one a e z₀
      (fun _ hx => hsum hx)
  have hdir {x : ℝ} (hx : x ∈ Ico p q) :
      B x = B p + (d x : ℂ) * exp (schwarzChristoffelEdgeAngle a e p * Complex.I) := by
    have h := schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀
      (fun i hi hmem => ha i hi ⟨hmem.1, hmem.2.trans hx.2⟩) hp (hsum hx)
      (x := x) (y := p) ⟨hx.1, le_rfl⟩ ⟨le_rfl, hx.1⟩ hx.1
    exact sub_eq_iff_eq_add'.mp h
  have hdt : Tendsto d (𝓝[<] q) atTop := by
    rw [tendsto_norm_atTop_iff_cobounded]
    exact (tendsto_sub_const_cobounded (B p)).comp
      ((tendsto_schwarzChristoffelBoundary_cobounded_of_prevertex_sum_eq_neg_one
        a e z₀ q hq).mono_left (nhdsLT_le_nhdsNE q))
  have hdimage : d '' Ico p q = Ici 0 := by
    apply subset_antisymm
    · rintro _ ⟨x, _, rfl⟩
      exact norm_nonneg _
    · have h := isPreconnected_Ico.intermediate_value_Ici
        (a := p) (l := 𝓝[<] q) ⟨le_rfl, hpq⟩
        (le_principal_iff.mpr (Ico_mem_nhdsLT hpq))
        (hcont.sub continuousOn_const).norm hdt
      simpa only [Pi.sub_apply, B, d, sub_self, norm_zero] using h
  calc
    B '' Ico p q = (fun t : ℝ => B p +
        (t : ℂ) * exp (schwarzChristoffelEdgeAngle a e p * Complex.I)) '' (d '' Ico p q) := by
      rw [← image_comp]
      exact image_congr fun x hx => hdir hx
    _ = _ := by rw [hdimage]

/-- An edge whose left endpoint is logarithmic traces the entire closed ray starting at
its integrable right endpoint, in the negative edge direction. -/
theorem schwarzChristoffelBoundary_image_Ioc_eq_ray_of_left_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p q : ℝ} (hpq : p < q)
    (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : ∑ i with a i = p, e i = -1) (hq : -1 < ∑ i with a i = q, e i) :
    schwarzChristoffelBoundary a e z₀ '' Ioc p q =
      (fun t : ℝ => schwarzChristoffelBoundary a e z₀ q -
        (t : ℂ) * exp (schwarzChristoffelEdgeAngle a e p * Complex.I)) '' Ici 0 := by
  classical
  let B := schwarzChristoffelBoundary a e z₀
  let d : ℝ → ℝ := fun x => ‖B q - B x‖
  have hzero {x : ℝ} (hx : x ∈ Ioo p q) : ∑ i with a i = x, e i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    by_contra hei
    exact ha i hei (hi' ▸ hx)
  have hsum {x : ℝ} (hx : x ∈ Ioc p q) : -1 < ∑ i with a i = x, e i := by
    rcases hx.2.eq_or_lt with rfl | hxq
    · exact hq
    · rw [hzero ⟨hx.1, hxq⟩]
      norm_num
  have hcont : ContinuousOn B (Ioc p q) :=
    continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one a e z₀
      (fun _ hx => hsum hx)
  have hdir {x : ℝ} (hx : x ∈ Ioc p q) :
      B x = B q - (d x : ℂ) * exp (schwarzChristoffelEdgeAngle a e p * Complex.I) := by
    rcases hx.2.eq_or_lt with rfl | hxq
    · simp [d]
    have hangle : schwarzChristoffelEdgeAngle a e x = schwarzChristoffelEdgeAngle a e p := by
      have h := schwarzChristoffelEdgeAngle_sub_eq_pi_mul_exponent_sum_of_adjacent a e hx.1
        (fun i hi hmem => ha i hi ⟨hmem.1, hmem.2.trans hxq⟩)
      rw [hzero ⟨hx.1, hxq⟩, mul_zero] at h
      exact (sub_eq_zero.mp h).symm
    have h := schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀
      (fun i hi hmem => ha i hi ⟨hx.1.trans hmem.1, hmem.2⟩) (hsum hx) hq
      (x := q) (y := x) ⟨hx.2, le_rfl⟩ ⟨le_rfl, hx.2⟩ hx.2
    rw [hangle] at h
    linear_combination -h
  have hdt : Tendsto d (𝓝[>] p) atTop := by
    rw [tendsto_norm_atTop_iff_cobounded]
    exact (tendsto_const_sub_cobounded (B q)).comp
      ((tendsto_schwarzChristoffelBoundary_cobounded_of_prevertex_sum_eq_neg_one
        a e z₀ p hp).mono_left (nhdsGT_le_nhdsNE p))
  have hdimage : d '' Ioc p q = Ici 0 := by
    apply subset_antisymm
    · rintro _ ⟨x, _, rfl⟩
      exact norm_nonneg _
    · have h := isPreconnected_Ioc.intermediate_value_Ici
        (a := q) (l := 𝓝[>] p) ⟨hpq, le_rfl⟩
        (le_principal_iff.mpr (Ioc_mem_nhdsGT hpq))
        (continuousOn_const.sub hcont).norm hdt
      simpa only [Pi.sub_apply, B, d, sub_self, norm_zero] using h
  calc
    B '' Ioc p q = (fun t : ℝ => B q -
        (t : ℂ) * exp (schwarzChristoffelEdgeAngle a e p * Complex.I)) '' (d '' Ioc p q) := by
      rw [← image_comp]
      exact image_congr fun x hx => hdir hx
    _ = _ := by rw [hdimage]

/-- An edge between two logarithmic prevertices traces a complete affine line. Any interior
parameter can be used as its origin; the increasing direction is the edge direction. -/
theorem schwarzChristoffelBoundary_image_Ioo_eq_range_of_endpoint_sums_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p q c : ℝ} (hc : c ∈ Ioo p q)
    (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : ∑ i with a i = p, e i = -1) (hq : ∑ i with a i = q, e i = -1) :
    schwarzChristoffelBoundary a e z₀ '' Ioo p q =
      range (fun t : ℝ => schwarzChristoffelBoundary a e z₀ c +
        (t : ℂ) * exp (schwarzChristoffelEdgeAngle a e c * Complex.I)) := by
  classical
  have hzero : ∑ i with a i = c, e i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    by_contra hei
    exact ha i hei (hi' ▸ hc)
  have hcsum : -1 < ∑ i with a i = c, e i := by rw [hzero]; norm_num
  have hleftfree : ∀ i, e i ≠ 0 → a i ∉ Ioo p c :=
    fun i hi hmem => ha i hi ⟨hmem.1, hmem.2.trans hc.2⟩
  have hrightfree : ∀ i, e i ≠ 0 → a i ∉ Ioo c q :=
    fun i hi hmem => ha i hi ⟨hc.1.trans hmem.1, hmem.2⟩
  have hangle : schwarzChristoffelEdgeAngle a e p = schwarzChristoffelEdgeAngle a e c := by
    have h := schwarzChristoffelEdgeAngle_sub_eq_pi_mul_exponent_sum_of_adjacent
      a e hc.1 hleftfree
    rw [hzero, mul_zero] at h
    exact sub_eq_zero.mp h
  have hsplit : Ioo p q = Ioc p c ∪ Ico c q := by
    ext x
    simp only [mem_union, mem_Ioo, mem_Ioc, mem_Ico]
    grind
  rw [hsplit, image_union,
    schwarzChristoffelBoundary_image_Ioc_eq_ray_of_left_sum_eq_neg_one
      a e z₀ hc.1 hleftfree hp hcsum,
    schwarzChristoffelBoundary_image_Ico_eq_ray_of_right_sum_eq_neg_one
      a e z₀ hc.2 hrightfree hcsum hq, hangle]
  -- The two opposite rays have the same origin and together exhaust the affine line.
  ext w
  constructor
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨-t, by simp [sub_eq_add_neg]⟩
    · exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    rcases le_total 0 t with ht | ht
    · exact Or.inr ⟨t, ht, rfl⟩
    · exact Or.inl ⟨-t, neg_nonneg.mpr ht, by simp⟩

end TauCeti

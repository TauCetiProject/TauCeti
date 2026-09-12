/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Module.Ray
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Boundary

/-!
# The closed edges of the Schwarz--Christoffel map are segments

The boundary values of the Schwarz--Christoffel map along a real interval free of prevertices with
nonzero exponent are collinear and injective on the open interval.  This file pins down the whole
closed arc: the image of a closed prevertex-free interval is exactly the *segment* joining the two
boundary values at its endpoints, and the image of the open interval is the corresponding open
segment.  When the endpoints are prevertices, the two boundary values are the Schwarz--Christoffel
vertices, so each closed boundary interval is carried injectively onto the straight polygon side
joining two consecutive vertices; that side is nondegenerate as soon as the two prevertices
themselves are distinct.

All the results below share the same hypotheses on the interval `[p, q]`: no prevertex of nonzero
exponent lies in `Ioo p q`, and each of `p` and `q` carries total exponent greater than `-1`, which
is what makes the boundary map continuous up to that endpoint.  Under those hypotheses every
increment of the boundary map in the increasing direction is a nonnegative real multiple of the one
unimodular direction `exp (i * schwarzChristoffelEdgeAngle a e p)`, so the distance from the left
endpoint is an arclength parameter on the arc:
`TauCeti.schwarzChristoffelBoundary_sub_eq_norm_mul` records the direction and
`TauCeti.norm_schwarzChristoffelBoundary_sub_add` records that the distances add.  That is the form
in which the length of an edge and the direction in which it leaves a vertex are read off.

These results describe the bounded part of the boundary of the Schwarz--Christoffel image edge by
edge: over the prevertices ordered along the real line the boundary values run through a chain of
straight sides joining consecutive vertices.  The two unbounded boundary intervals are not covered
here.  About those, `TauCeti.tendsto_schwarzChristoffelBoundaryValue_atInfinity` says only that the
boundary values converge to a common vertex at infinity in both directions; identifying the image
of either unbounded interval as a segment or a ray remains open.

## Main results

* `TauCeti.schwarzChristoffelBoundary_sub_eq_norm_mul` -- along a closed prevertex-free interval an
  increment of the boundary map is its own length times the unimodular edge direction.
* `TauCeti.norm_schwarzChristoffelBoundary_sub_add` -- those lengths add.
* `TauCeti.schwarzChristoffelBoundary_injOn_Icc` -- the boundary map is injective on the closed
  interval, endpoints included.
* `TauCeti.schwarzChristoffelBoundary_image_Icc` and
  `TauCeti.schwarzChristoffelBoundary_image_Ioo` -- the closed and the open boundary arcs are the
  segment and the open segment joining the two endpoint values.
* `TauCeti.schwarzChristoffelBoundary_image_Icc_prevertex` and
  `TauCeti.schwarzChristoffelBoundary_image_Ioo_prevertex` -- between two prevertices the closed
  and open boundary arcs are the straight side joining the corresponding Schwarz--Christoffel
  vertices and its interior.
* `TauCeti.schwarzChristoffelVertex_ne` -- that side is nondegenerate when the two prevertices
  are distinct.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- On a real interval free of prevertices with nonzero exponent, an increment of the
Schwarz--Christoffel boundary map in the increasing direction is a nonnegative real multiple of the
unimodular edge direction with argument `schwarzChristoffelEdgeAngle a e p`. -/
private theorem exists_nonneg_schwarzChristoffelBoundary_sub_eq_Ioo (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    {x y : ℝ} (hx : x ∈ Ioo p q) (hy : y ∈ Ioo p q) (hyx : y ≤ x) :
    ∃ c : ℝ, 0 ≤ c ∧
      schwarzChristoffelBoundary a e z₀ x - schwarzChristoffelBoundary a e z₀ y =
        (c : ℂ) * Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) :=
  -- the multiple is the integral of the density `∏ i, |t - a i| ^ e i`, which is nonnegative
  ⟨∫ t in y..x, ∏ i, |t - a i| ^ e i,
    intervalIntegral.integral_nonneg_of_forall hyx fun _ =>
      Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _,
    schwarzChristoffelBoundary_sub_eq a e z₀ ha hx hy⟩

/-- The same statement on the *closed* interval, both of whose endpoints are assumed to carry total
exponent greater than `-1`. -/
private theorem exists_nonneg_schwarzChristoffelBoundary_sub_eq (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i)
    {x y : ℝ} (hx : x ∈ Icc p q) (hy : y ∈ Icc p q) (hyx : y ≤ x) :
    ∃ c : ℝ, 0 ≤ c ∧
      schwarzChristoffelBoundary a e z₀ x - schwarzChristoffelBoundary a e z₀ y =
        (c : ℂ) * Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) := by
  -- the nonnegative real multiples of `u` are the image of `Ici 0` under scalar multiplication by
  -- `u`, hence form a closed set, so the statement propagates from the open interval to its
  -- endpoints along the continuous boundary map
  set u : ℂ := Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I)
  have hTclosed : IsClosed {z : ℂ | ∃ c : ℝ, 0 ≤ c ∧ z = (c : ℂ) * u} := by
    have hTeq : {z : ℂ | ∃ c : ℝ, 0 ≤ c ∧ z = (c : ℂ) * u} = (fun c : ℝ => c • u) '' Ici 0 := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_Ici, Complex.real_smul]
      exact ⟨fun ⟨c, hc, hz⟩ => ⟨c, hc, hz.symm⟩, fun ⟨c, hc, hz⟩ => ⟨c, hc, hz.symm⟩⟩
    rw [hTeq]
    exact isClosedMap_smul_left u _ isClosed_Ici
  have hcont : ContinuousOn (schwarzChristoffelBoundary a e z₀) (Icc p q) :=
    continuousOn_schwarzChristoffelBoundary_Icc a e z₀ ha hp hq
  have step₁ : ∀ y ∈ Ioo p q, ∀ x ∈ Icc y q,
      schwarzChristoffelBoundary a e z₀ x - schwarzChristoffelBoundary a e z₀ y ∈
        {z : ℂ | ∃ c : ℝ, 0 ≤ c ∧ z = (c : ℂ) * u} := by
    intro y hy x hx
    have hsub : Icc y q ⊆ Icc p q := Icc_subset_Icc hy.1.le le_rfl
    have hmaps : MapsTo (fun t => schwarzChristoffelBoundary a e z₀ t -
        schwarzChristoffelBoundary a e z₀ y) (Ico y q)
        {z : ℂ | ∃ c : ℝ, 0 ≤ c ∧ z = (c : ℂ) * u} := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with rfl | hlt
      · exact ⟨0, le_rfl, by simp⟩
      · exact exists_nonneg_schwarzChristoffelBoundary_sub_eq_Ioo a e z₀ ha
          ⟨hy.1.trans hlt, ht.2⟩ hy hlt.le
    have hclos : closure (Ico y q) = Icc y q := closure_Ico hy.2.ne
    have hmap := hmaps.closure_of_continuousOn
      (by rw [hclos]; exact (hcont.mono hsub).sub continuousOn_const)
    rw [hclos, hTclosed.closure_eq] at hmap
    exact hmap hx
  have step₂ : ∀ x ∈ Icc p q, p < x →
      schwarzChristoffelBoundary a e z₀ x - schwarzChristoffelBoundary a e z₀ p ∈
        {z : ℂ | ∃ c : ℝ, 0 ≤ c ∧ z = (c : ℂ) * u} := by
    intro x hx hpx
    have hsub : Icc p x ⊆ Icc p q := Icc_subset_Icc le_rfl hx.2
    have hmaps : MapsTo (fun t => schwarzChristoffelBoundary a e z₀ x -
        schwarzChristoffelBoundary a e z₀ t) (Ioo p x)
        {z : ℂ | ∃ c : ℝ, 0 ≤ c ∧ z = (c : ℂ) * u} :=
      fun t ht => step₁ t ⟨ht.1, ht.2.trans_le hx.2⟩ x ⟨ht.2.le, hx.2⟩
    have hclos : closure (Ioo p x) = Icc p x := closure_Ioo hpx.ne
    have hmap := hmaps.closure_of_continuousOn
      (by rw [hclos]; exact continuousOn_const.sub (hcont.mono hsub))
    rw [hclos, hTclosed.closure_eq] at hmap
    exact hmap ⟨le_rfl, hpx.le⟩
  rcases eq_or_lt_of_le hyx with rfl | hlt
  · exact ⟨0, le_rfl, by simp⟩
  rcases eq_or_lt_of_le hy.1 with rfl | hpy
  · exact step₂ x hx hlt
  · exact step₁ y ⟨hpy, hlt.trans_le hx.2⟩ x ⟨hyx, hx.2⟩

/-- **An increment of the Schwarz--Christoffel boundary map along a closed edge is its own length
times the edge direction.**  On a real interval free of prevertices with nonzero exponent, and with
both endpoints carrying total exponent greater than `-1`, the boundary map moves in the increasing
direction by exactly `‖B x - B y‖` along the unimodular direction with argument
`schwarzChristoffelEdgeAngle a e p`. -/
theorem schwarzChristoffelBoundary_sub_eq_norm_mul (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i)
    {x y : ℝ} (hx : x ∈ Icc p q) (hy : y ∈ Icc p q) (hyx : y ≤ x) :
    schwarzChristoffelBoundary a e z₀ x - schwarzChristoffelBoundary a e z₀ y =
      (‖schwarzChristoffelBoundary a e z₀ x - schwarzChristoffelBoundary a e z₀ y‖ : ℂ) *
        Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) := by
  obtain ⟨c, hc0, hc⟩ :=
    exists_nonneg_schwarzChristoffelBoundary_sub_eq a e z₀ ha hp hq hx hy hyx
  have hnorm : ‖schwarzChristoffelBoundary a e z₀ x -
      schwarzChristoffelBoundary a e z₀ y‖ = c := by
    rw [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [hnorm]
  exact hc

/-- **Lengths add along a closed Schwarz--Christoffel edge.**  For three points in increasing order
in a closed interval free of prevertices with nonzero exponent, and with both endpoints carrying
total exponent greater than `-1`, the distance between the two outer boundary values is the sum of
the two distances cut out by the middle one. -/
theorem norm_schwarzChristoffelBoundary_sub_add (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i)
    {x y z : ℝ} (hx : x ∈ Icc p q) (hy : y ∈ Icc p q) (hz : z ∈ Icc p q)
    (hxy : x ≤ y) (hyz : y ≤ z) :
    ‖schwarzChristoffelBoundary a e z₀ z - schwarzChristoffelBoundary a e z₀ x‖ =
      ‖schwarzChristoffelBoundary a e z₀ y - schwarzChristoffelBoundary a e z₀ x‖ +
        ‖schwarzChristoffelBoundary a e z₀ z - schwarzChristoffelBoundary a e z₀ y‖ := by
  -- the two increments are nonnegative real multiples of one and the same unimodular direction,
  -- hence lie on a common ray, along which the triangle inequality is an equality
  obtain ⟨c₁, hc₁, h₁⟩ := exists_nonneg_schwarzChristoffelBoundary_sub_eq a e z₀ ha hp hq hy hx hxy
  obtain ⟨c₂, hc₂, h₂⟩ := exists_nonneg_schwarzChristoffelBoundary_sub_eq a e z₀ ha hp hq hz hy hyz
  have hray : SameRay ℝ (schwarzChristoffelBoundary a e z₀ y - schwarzChristoffelBoundary a e z₀ x)
      (schwarzChristoffelBoundary a e z₀ z - schwarzChristoffelBoundary a e z₀ y) := by
    rw [h₁, h₂, ← Complex.real_smul, ← Complex.real_smul]
    exact (SameRay.sameRay_nonneg_smul_left _ hc₁).nonneg_smul_right hc₂
  calc ‖schwarzChristoffelBoundary a e z₀ z - schwarzChristoffelBoundary a e z₀ x‖
      = ‖(schwarzChristoffelBoundary a e z₀ y - schwarzChristoffelBoundary a e z₀ x) +
          (schwarzChristoffelBoundary a e z₀ z - schwarzChristoffelBoundary a e z₀ y)‖ := by
        rw [sub_add_sub_cancel']
    _ = ‖schwarzChristoffelBoundary a e z₀ y - schwarzChristoffelBoundary a e z₀ x‖ +
          ‖schwarzChristoffelBoundary a e z₀ z - schwarzChristoffelBoundary a e z₀ y‖ :=
        hray.norm_add

/-- Distinct points of a closed interval free of prevertices with nonzero exponent, both of whose
endpoints carry total exponent greater than `-1`, have distinct boundary values. -/
private theorem schwarzChristoffelBoundary_ne_of_lt (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i)
    {x y : ℝ} (hx : x ∈ Icc p q) (hy : y ∈ Icc p q) (hyx : y < x) :
    schwarzChristoffelBoundary a e z₀ x ≠ schwarzChristoffelBoundary a e z₀ y := by
  -- squeeze two interior points between `y` and `x` and add lengths: the total is at least the
  -- length of the interior step, which is positive by injectivity on the open interval
  obtain ⟨m₁, hym₁, hm₁x⟩ := exists_between hyx
  obtain ⟨m₂, hm₁m₂, hm₂x⟩ := exists_between hm₁x
  have hm₁I : m₁ ∈ Icc p q := ⟨hy.1.trans hym₁.le, hm₁x.le.trans hx.2⟩
  have hm₂I : m₂ ∈ Icc p q := ⟨hm₁I.1.trans hm₁m₂.le, hm₂x.le.trans hx.2⟩
  have hm₁O : m₁ ∈ Ioo p q := ⟨hy.1.trans_lt hym₁, hm₁x.trans_le hx.2⟩
  have hm₂O : m₂ ∈ Ioo p q := ⟨hm₁O.1.trans hm₁m₂, hm₂x.trans_le hx.2⟩
  have hpos : 0 < ‖schwarzChristoffelBoundary a e z₀ m₂ -
      schwarzChristoffelBoundary a e z₀ m₁‖ :=
    norm_sub_pos_iff.mpr fun h =>
      hm₁m₂.ne' (schwarzChristoffelBoundary_injOn a e z₀ ha hm₂O hm₁O h)
  have e₁ := norm_schwarzChristoffelBoundary_sub_add a e z₀ ha hp hq hy hm₁I hx hym₁.le hm₁x.le
  have e₂ := norm_schwarzChristoffelBoundary_sub_add a e z₀ ha hp hq hm₁I hm₂I hx hm₁m₂.le hm₂x.le
  intro h
  have hzero : ‖schwarzChristoffelBoundary a e z₀ x -
      schwarzChristoffelBoundary a e z₀ y‖ = 0 := by rw [h]; simp
  have hnn₁ := norm_nonneg (schwarzChristoffelBoundary a e z₀ m₁ -
    schwarzChristoffelBoundary a e z₀ y)
  have hnn₂ := norm_nonneg (schwarzChristoffelBoundary a e z₀ x -
    schwarzChristoffelBoundary a e z₀ m₂)
  linarith

/-- **The Schwarz--Christoffel boundary map is injective on a closed prevertex-free interval.**
On a real interval free of prevertices with nonzero exponent, both of whose endpoints carry total
exponent greater than `-1`, distinct points have distinct boundary values; this is
`TauCeti.schwarzChristoffelBoundary_injOn` with the two endpoints included, so a closed boundary
arc between two prevertices is an embedded straight side. -/
theorem schwarzChristoffelBoundary_injOn_Icc (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i) :
    InjOn (schwarzChristoffelBoundary a e z₀) (Icc p q) := by
  intro x hx y hy hxy
  rcases lt_trichotomy x y with h | h | h
  · exact absurd hxy.symm (schwarzChristoffelBoundary_ne_of_lt a e z₀ ha hp hq hy hx h)
  · exact h
  · exact absurd hxy (schwarzChristoffelBoundary_ne_of_lt a e z₀ ha hp hq hx hy h)

/-- The arclength reparametrisation of a closed Schwarz--Christoffel edge: the distance `d` from
the left endpoint is continuous and strictly increasing on the interval, vanishes at the left
endpoint, and presents the boundary map as the affine parametrisation of the edge by `d`, at unit
speed along the unimodular edge direction. -/
private theorem exists_strictMonoOn_schwarzChristoffelBoundary_eq (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i) :
    ∃ d : ℝ → ℝ, d p = 0 ∧ StrictMonoOn d (Icc p q) ∧ ContinuousOn d (Icc p q) ∧
      EqOn (schwarzChristoffelBoundary a e z₀)
        (⇑(AffineMap.lineMap (schwarzChristoffelBoundary a e z₀ p)
          (schwarzChristoffelBoundary a e z₀ p +
            Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I))) ∘ d) (Icc p q) := by
  refine ⟨fun x => ‖schwarzChristoffelBoundary a e z₀ x - schwarzChristoffelBoundary a e z₀ p‖,
    by simp, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hpI : p ∈ Icc p q := ⟨le_rfl, hx.1.trans hx.2⟩
    have hadd := norm_schwarzChristoffelBoundary_sub_add a e z₀ ha hp hq hpI hx hy hx.1 hxy.le
    have hpos : 0 < ‖schwarzChristoffelBoundary a e z₀ y -
        schwarzChristoffelBoundary a e z₀ x‖ :=
      norm_sub_pos_iff.mpr (schwarzChristoffelBoundary_ne_of_lt a e z₀ ha hp hq hy hx hxy)
    simp only
    linarith
  · exact ((continuousOn_schwarzChristoffelBoundary_Icc a e z₀ ha hp hq).sub
      continuousOn_const).norm
  · intro x hx
    have hpI : p ∈ Icc p q := ⟨le_rfl, hx.1.trans hx.2⟩
    have hstep := schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀ ha hp hq hx hpI hx.1
    simp only [Function.comp_apply, AffineMap.lineMap_apply_module, Complex.real_smul]
    push_cast
    linear_combination hstep

/-- **A closed Schwarz--Christoffel boundary arc is a segment.**  Over a real interval free of
prevertices with nonzero exponent, both of whose endpoints carry total exponent greater than `-1`,
the image of the boundary map is exactly the segment joining its two endpoint values. -/
theorem schwarzChristoffelBoundary_image_Icc (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p q : ℝ} (hpq : p ≤ q) (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i) :
    schwarzChristoffelBoundary a e z₀ '' Icc p q =
      segment ℝ (schwarzChristoffelBoundary a e z₀ p) (schwarzChristoffelBoundary a e z₀ q) := by
  obtain ⟨d, hd0, hdmono, hdcont, hrep⟩ :=
    exists_strictMonoOn_schwarzChristoffelBoundary_eq a e z₀ ha hp hq
  have hpI : p ∈ Icc p q := ⟨le_rfl, hpq⟩
  have hqI : q ∈ Icc p q := ⟨hpq, le_rfl⟩
  have hdq : 0 ≤ d q := by rw [← hd0]; exact hdmono.monotoneOn hpI hqI hpq
  set L : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap (schwarzChristoffelBoundary a e z₀ p)
    (schwarzChristoffelBoundary a e z₀ p +
      Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I)) with hL
  -- the arclength parameter is continuous and monotone, so it sweeps out `Icc (d p) (d q)`
  have hd : d '' Icc p q = segment ℝ 0 (d q) := by
    rw [hdcont.image_Icc_of_monotoneOn hpq hdmono.monotoneOn, hd0, segment_eq_Icc hdq]
  have hBq : L (d q) = schwarzChristoffelBoundary a e z₀ q := (hrep hqI).symm
  calc schwarzChristoffelBoundary a e z₀ '' Icc p q
      = ⇑L '' (d '' Icc p q) := by rw [hrep.image_eq, image_comp]
    _ = ⇑L '' segment ℝ 0 (d q) := by rw [hd]
    _ = segment ℝ (L 0) (L (d q)) := by rw [image_segment]
    _ = segment ℝ (schwarzChristoffelBoundary a e z₀ p) (schwarzChristoffelBoundary a e z₀ q) := by
        rw [hBq, hL, AffineMap.lineMap_apply_zero]

/-- **An open Schwarz--Christoffel boundary arc is an open segment.**  The companion of
`TauCeti.schwarzChristoffelBoundary_image_Icc` that omits the two endpoint values. -/
theorem schwarzChristoffelBoundary_image_Ioo (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p q : ℝ} (hpq : p < q) (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i) :
    schwarzChristoffelBoundary a e z₀ '' Ioo p q =
      openSegment ℝ (schwarzChristoffelBoundary a e z₀ p)
        (schwarzChristoffelBoundary a e z₀ q) := by
  -- the open arc is the closed arc with its two endpoint values removed, and those two values are
  -- distinct by injectivity, so what is left of the segment is exactly the open segment
  have hpI : p ∈ Icc p q := ⟨le_rfl, hpq.le⟩
  have hqI : q ∈ Icc p q := ⟨hpq.le, le_rfl⟩
  have hinj := schwarzChristoffelBoundary_injOn_Icc a e z₀ ha hp hq
  have hne : schwarzChristoffelBoundary a e z₀ p ≠ schwarzChristoffelBoundary a e z₀ q :=
    fun h => hpq.ne (hinj hpI hqI h)
  have hsub : ({p, q} : Set ℝ) ⊆ Icc p q := by
    simp [Set.insert_subset_iff, hpI, hqI]
  rw [← Icc_sdiff_both, hinj.image_sdiff_subset hsub,
    schwarzChristoffelBoundary_image_Icc a e z₀ hpq.le ha hp hq, Set.image_pair]
  refine Set.Subset.antisymm (fun z hz => ?_) fun z hz => ⟨openSegment_subset_segment _ _ _ hz, ?_⟩
  · simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
    exact mem_openSegment_of_ne_left_right (Ne.symm hz.2.1) (Ne.symm hz.2.2) hz.1
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hne (left_mem_openSegment_iff.mp (h ▸ hz)),
      fun h => hne (right_mem_openSegment_iff.mp (h ▸ hz))⟩

/-- **The straight sides of the Schwarz--Christoffel polygon.**  Between two prevertices with no
prevertex of nonzero exponent strictly between them, and with both total exponents greater than
`-1`, the closed boundary arc is exactly the segment joining the two Schwarz--Christoffel
vertices. -/
theorem schwarzChristoffelBoundary_image_Icc_prevertex (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {j k : ι} (hjk : a j ≤ a k) (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo (a j) (a k))
    (hj : -1 < ∑ i with a i = a j, e i) (hk : -1 < ∑ i with a i = a k, e i) :
    schwarzChristoffelBoundary a e z₀ '' Icc (a j) (a k) =
      segment ℝ (schwarzChristoffelVertex a e z₀ j) (schwarzChristoffelVertex a e z₀ k) := by
  rw [schwarzChristoffelBoundary_image_Icc a e z₀ hjk ha hj hk,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ j hj,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ k hk]

/-- **The interiors of the straight sides of the Schwarz--Christoffel polygon.**  Between two
prevertices with no prevertex of nonzero exponent strictly between them, and with both total
exponents greater than `-1`, the open boundary arc is exactly the open segment joining the two
Schwarz--Christoffel vertices. -/
theorem schwarzChristoffelBoundary_image_Ioo_prevertex (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {j k : ι} (hjk : a j < a k) (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo (a j) (a k))
    (hj : -1 < ∑ i with a i = a j, e i) (hk : -1 < ∑ i with a i = a k, e i) :
    schwarzChristoffelBoundary a e z₀ '' Ioo (a j) (a k) =
      openSegment ℝ (schwarzChristoffelVertex a e z₀ j) (schwarzChristoffelVertex a e z₀ k) := by
  rw [schwarzChristoffelBoundary_image_Ioo a e z₀ hjk ha hj hk,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ j hj,
    schwarzChristoffelBoundary_apply_prevertex a e z₀ k hk]

/-- **A Schwarz--Christoffel side is nondegenerate.**  Two prevertices with no prevertex of nonzero
exponent strictly between them, and with both total exponents greater than `-1`, carry distinct
vertices. -/
theorem schwarzChristoffelVertex_ne (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {j k : ι} (hjk : a j < a k) (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo (a j) (a k))
    (hj : -1 < ∑ i with a i = a j, e i) (hk : -1 < ∑ i with a i = a k, e i) :
    schwarzChristoffelVertex a e z₀ j ≠ schwarzChristoffelVertex a e z₀ k := by
  rw [← schwarzChristoffelBoundary_apply_prevertex a e z₀ j hj,
    ← schwarzChristoffelBoundary_apply_prevertex a e z₀ k hk]
  exact fun h => hjk.ne (schwarzChristoffelBoundary_injOn_Icc a e z₀ ha hj hk
    ⟨le_rfl, hjk.le⟩ ⟨hjk.le, le_rfl⟩ h)

end TauCeti

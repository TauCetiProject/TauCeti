/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Segment
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Boundary

/-!
# The closed edges of the Schwarz--Christoffel map are segments

The boundary values of the Schwarz--Christoffel map along a real interval free of prevertices with
nonzero exponent are collinear and injective, and the closed boundary arc over such an interval is
the closure of the open one.  This file pins that closure down: the image of a closed
prevertex-free interval is exactly the *segment* joining the two boundary values at its endpoints,
and the image of the open interval is the corresponding open segment.  When the endpoints are
prevertices, the two boundary values are the Schwarz--Christoffel vertices, so each closed boundary
interval is carried homeomorphically onto the straight polygon side joining two consecutive
vertices, and that side is nondegenerate.

The mechanism is an arclength parameter.  Write `B` for the boundary map,
`u = exp (i · schwarzChristoffelEdgeAngle a e p)` for the fixed unimodular edge direction, and
`d x = ‖B x - B p‖`.  On the *open* interval, `B x - B y` is the integral of the positive real
density `∏ i, |t - a i| ^ e i` between `y` and `x` times `u`, hence a *nonnegative* real multiple of
`u` whenever `y ≤ x`.  The set of nonnegative real multiples of `u` is closed --- it is cut out by
`(u* · z).im = 0` and `0 ≤ (u* · z).re` --- so continuity of `B` on the closed interval propagates
that statement to the endpoints.  Comparing norms turns it into `B x - B y = ‖B x - B y‖ · u`, from
which lengths add along the interval and `d` is a continuous strictly monotone reparametrisation
with `B x = B p + d x · u`.  Strictness comes from squeezing two interior points between `y` and `x`
and quoting the already known injectivity on the open interval.  The image statements are then the
intermediate value theorem applied to `d`.

Together with `TauCeti.tendsto_schwarzChristoffelBoundaryValue_atInfinity`, which closes the two
unbounded boundary intervals up at a single point, this is the edgewise half of the identification
of the Schwarz--Christoffel image with a polygon; the global statement --- that the map is injective
on the upper half-plane and onto the region the edge chain bounds --- is left to later work.

## Main results

* `TauCeti.schwarzChristoffelBoundary_sub_eq_norm_mul` -- along a closed prevertex-free interval an
  increment of the boundary map is its own length times the unimodular edge direction.
* `TauCeti.norm_schwarzChristoffelBoundary_sub_add` -- consequently those lengths add.
* `TauCeti.schwarzChristoffelBoundary_injOn_Icc` -- the boundary map is injective on the closed
  interval, endpoints included.
* `TauCeti.schwarzChristoffelBoundary_image_Icc` and
  `TauCeti.schwarzChristoffelBoundary_image_Ioo` -- the closed and the open boundary arcs are the
  segment and the open segment joining the two endpoint values.
* `TauCeti.schwarzChristoffelBoundary_image_Icc_prevertex` -- between two prevertices the closed
  boundary arc is the straight side joining the corresponding Schwarz--Christoffel vertices.
* `TauCeti.schwarzChristoffelVertex_ne` -- that side is nondegenerate.

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
unimodular edge direction: the density `∏ i, |t - a i| ^ e i` integrated against it is
nonnegative. -/
private theorem exists_nonneg_schwarzChristoffelBoundary_sub_eq_Ioo (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    {x y : ℝ} (hx : x ∈ Ioo p q) (hy : y ∈ Ioo p q) (hyx : y ≤ x) :
    ∃ c : ℝ, 0 ≤ c ∧
      schwarzChristoffelBoundary a e z₀ x - schwarzChristoffelBoundary a e z₀ y =
        (c : ℂ) * Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) :=
  ⟨∫ t in y..x, ∏ i, |t - a i| ^ e i,
    intervalIntegral.integral_nonneg_of_forall hyx fun _ =>
      Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _,
    schwarzChristoffelBoundary_sub_eq a e z₀ ha hx hy⟩

/-- The same statement on the *closed* interval.  The nonnegative real multiples of a unimodular
`u` form a closed set, so the property propagates from the open interval to its endpoints along the
continuous boundary map. -/
private theorem exists_nonneg_schwarzChristoffelBoundary_sub_eq (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i)
    {x y : ℝ} (hx : x ∈ Icc p q) (hy : y ∈ Icc p q) (hyx : y ≤ x) :
    ∃ c : ℝ, 0 ≤ c ∧
      schwarzChristoffelBoundary a e z₀ x - schwarzChristoffelBoundary a e z₀ y =
        (c : ℂ) * Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) := by
  set u : ℂ := Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) with hu
  have huc : (starRingEnd ℂ) u * u = 1 := by
    rw [hu, ← Complex.exp_conj, ← Complex.exp_add]
    have hzero : (starRingEnd ℂ) ((schwarzChristoffelEdgeAngle a e p : ℂ) * Complex.I) +
        (schwarzChristoffelEdgeAngle a e p : ℂ) * Complex.I = 0 := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    rw [hzero, Complex.exp_zero]
  have hTclosed : IsClosed {z : ℂ | ∃ c : ℝ, 0 ≤ c ∧ z = (c : ℂ) * u} := by
    have hTeq : {z : ℂ | ∃ c : ℝ, 0 ≤ c ∧ z = (c : ℂ) * u} =
        {z : ℂ | ((starRingEnd ℂ) u * z).im = 0} ∩
          {z : ℂ | 0 ≤ ((starRingEnd ℂ) u * z).re} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨c, hc, rfl⟩
        have hcz : (starRingEnd ℂ) u * ((c : ℂ) * u) = (c : ℂ) := by
          linear_combination (c : ℂ) * huc
        rw [hcz]
        exact ⟨Complex.ofReal_im c, by simpa using hc⟩
      · rintro ⟨him, hre⟩
        refine ⟨((starRingEnd ℂ) u * z).re, hre, ?_⟩
        have hz : ((((starRingEnd ℂ) u * z).re : ℝ) : ℂ) = (starRingEnd ℂ) u * z :=
          Complex.ext (by simp) (by simp [him])
        rw [hz]
        linear_combination (-z) * huc
    rw [hTeq]
    exact (isClosed_eq (Complex.continuous_im.comp (continuous_const.mul continuous_id))
        continuous_const).inter
      (isClosed_le continuous_const
        (Complex.continuous_re.comp (continuous_const.mul continuous_id)))
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

/-- **Lengths add along a closed Schwarz--Christoffel edge.**  Since all increments point in one
and the same direction, the distance travelled between the ends of a prevertex-free closed interval
is the sum of the distances travelled over the two halves cut out by any intermediate point. -/
theorem norm_schwarzChristoffelBoundary_sub_add (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i)
    {x y z : ℝ} (hx : x ∈ Icc p q) (hy : y ∈ Icc p q) (hz : z ∈ Icc p q)
    (hxy : x ≤ y) (hyz : y ≤ z) :
    ‖schwarzChristoffelBoundary a e z₀ z - schwarzChristoffelBoundary a e z₀ x‖ =
      ‖schwarzChristoffelBoundary a e z₀ y - schwarzChristoffelBoundary a e z₀ x‖ +
        ‖schwarzChristoffelBoundary a e z₀ z - schwarzChristoffelBoundary a e z₀ y‖ := by
  have h₁ := schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀ ha hp hq hy hx hxy
  have h₂ := schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀ ha hp hq hz hy hyz
  have h₃ := schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀ ha hp hq hz hx (hxy.trans hyz)
  have key : ((‖schwarzChristoffelBoundary a e z₀ z -
        schwarzChristoffelBoundary a e z₀ x‖ : ℝ) : ℂ) *
      Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) =
      ((‖schwarzChristoffelBoundary a e z₀ y - schwarzChristoffelBoundary a e z₀ x‖ +
        ‖schwarzChristoffelBoundary a e z₀ z - schwarzChristoffelBoundary a e z₀ y‖ : ℝ) : ℂ) *
        Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) := by
    push_cast
    linear_combination -h₃ + h₁ + h₂
  exact_mod_cast mul_right_cancel₀ (Complex.exp_ne_zero _) key

/-- Distinct points of a closed prevertex-free interval have distinct boundary values: squeezing
two interior points between them and adding lengths, the total is at least the length of the
interior step, which is positive by injectivity on the open interval. -/
private theorem schwarzChristoffelBoundary_ne_of_lt (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i)
    {x y : ℝ} (hx : x ∈ Icc p q) (hy : y ∈ Icc p q) (hyx : y < x) :
    schwarzChristoffelBoundary a e z₀ x ≠ schwarzChristoffelBoundary a e z₀ y := by
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
This extends `TauCeti.schwarzChristoffelBoundary_injOn` to the two endpoints, so a closed boundary
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

/-- The arclength reparametrisation of a closed Schwarz--Christoffel edge: the distance from the
left endpoint is continuous and strictly increasing, and it linearizes the boundary map along the
fixed edge direction. -/
private theorem exists_strictMonoOn_schwarzChristoffelBoundary_eq (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i) :
    ∃ d : ℝ → ℝ, d p = 0 ∧ (∀ x ∈ Icc p q, 0 ≤ d x) ∧ StrictMonoOn d (Icc p q) ∧
      ContinuousOn d (Icc p q) ∧ ∀ x ∈ Icc p q, schwarzChristoffelBoundary a e z₀ x =
        schwarzChristoffelBoundary a e z₀ p + (d x : ℂ) *
          Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) := by
  refine ⟨fun x => ‖schwarzChristoffelBoundary a e z₀ x - schwarzChristoffelBoundary a e z₀ p‖,
    by simp, fun _ _ => norm_nonneg _, ?_, ?_, ?_⟩
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
    have := schwarzChristoffelBoundary_sub_eq_norm_mul a e z₀ ha hp hq hx hpI hx.1
    linear_combination this

/-- **A closed Schwarz--Christoffel boundary arc is a segment.**  Over a real interval free of
prevertices with nonzero exponent, both of whose endpoints carry total exponent greater than `-1`,
the image of the boundary map is exactly the segment joining its two endpoint values. -/
theorem schwarzChristoffelBoundary_image_Icc (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p q : ℝ} (hpq : p ≤ q) (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i) :
    schwarzChristoffelBoundary a e z₀ '' Icc p q =
      segment ℝ (schwarzChristoffelBoundary a e z₀ p) (schwarzChristoffelBoundary a e z₀ q) := by
  obtain ⟨d, hd0, hdnn, hdmono, hdcont, hrep⟩ :=
    exists_strictMonoOn_schwarzChristoffelBoundary_eq a e z₀ ha hp hq
  have hpI : p ∈ Icc p q := ⟨le_rfl, hpq⟩
  have hqI : q ∈ Icc p q := ⟨hpq, le_rfl⟩
  have hdq : 0 ≤ d q := hdnn q hqI
  apply Set.Subset.antisymm
  · rintro - ⟨x, hx, rfl⟩
    rw [segment_eq_image']
    rcases eq_or_lt_of_le hdq with h0 | h0
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      have hdx : d x = 0 :=
        le_antisymm (h0 ▸ hdmono.monotoneOn hx hqI hx.2) (hdnn x hx)
      simp only [hrep x hx, hdx]
      simp
    · refine ⟨d x / d q, ⟨div_nonneg (hdnn x hx) h0.le,
        (div_le_one h0).mpr (hdmono.monotoneOn hx hqI hx.2)⟩, ?_⟩
      have hq0 : (d q : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
      simp only [hrep x hx, hrep q hqI, Complex.real_smul]
      push_cast
      field_simp
      ring
  · rw [segment_eq_image']
    rintro - ⟨t, ht, rfl⟩
    have hmem : t * d q ∈ Icc (d p) (d q) := by
      rw [hd0]
      exact ⟨mul_nonneg ht.1 hdq, mul_le_of_le_one_left hdq ht.2⟩
    obtain ⟨x, hx, hdx⟩ := intermediate_value_Icc hpq hdcont hmem
    refine ⟨x, hx, ?_⟩
    simp only [hrep x hx, hrep q hqI, Complex.real_smul, hdx]
    push_cast
    ring

/-- **An open Schwarz--Christoffel boundary arc is an open segment.**  The companion of
`TauCeti.schwarzChristoffelBoundary_image_Icc` that omits the two endpoint values. -/
theorem schwarzChristoffelBoundary_image_Ioo (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {p q : ℝ} (hpq : p < q) (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q)
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i) :
    schwarzChristoffelBoundary a e z₀ '' Ioo p q =
      openSegment ℝ (schwarzChristoffelBoundary a e z₀ p)
        (schwarzChristoffelBoundary a e z₀ q) := by
  obtain ⟨d, hd0, hdnn, hdmono, hdcont, hrep⟩ :=
    exists_strictMonoOn_schwarzChristoffelBoundary_eq a e z₀ ha hp hq
  have hpI : p ∈ Icc p q := ⟨le_rfl, hpq.le⟩
  have hqI : q ∈ Icc p q := ⟨hpq.le, le_rfl⟩
  have hdq : 0 < d q := hd0 ▸ hdmono hpI hqI hpq
  have hq0 : (d q : ℂ) ≠ 0 := by exact_mod_cast hdq.ne'
  apply Set.Subset.antisymm
  · rintro - ⟨x, hx, rfl⟩
    rw [openSegment_eq_image']
    have hxI : x ∈ Icc p q := Ioo_subset_Icc_self hx
    have h₁ : 0 < d x := hd0 ▸ hdmono hpI hxI hx.1
    have h₂ : d x < d q := hdmono hxI hqI hx.2
    refine ⟨d x / d q, ⟨div_pos h₁ hdq, (div_lt_one hdq).mpr h₂⟩, ?_⟩
    simp only [hrep x hxI, hrep q hqI, Complex.real_smul]
    push_cast
    field_simp
    ring
  · rw [openSegment_eq_image']
    rintro - ⟨t, ht, rfl⟩
    have hmem : t * d q ∈ Icc (d p) (d q) := by
      rw [hd0]
      exact ⟨mul_nonneg ht.1.le hdq.le, mul_le_of_le_one_left hdq.le ht.2.le⟩
    obtain ⟨x, hxI, hdx⟩ := intermediate_value_Icc hpq.le hdcont hmem
    have hx : x ∈ Ioo p q := by
      refine ⟨?_, ?_⟩
      · rcases eq_or_lt_of_le hxI.1 with h | h
        · rw [← h, hd0] at hdx
          exact absurd hdx.symm (mul_pos ht.1 hdq).ne'
        · exact h
      · rcases eq_or_lt_of_le hxI.2 with h | h
        · rw [h] at hdx
          nlinarith [ht.2, hdq]
        · exact h
    refine ⟨x, hx, ?_⟩
    simp only [hrep x hxI, hrep q hqI, Complex.real_smul, hdx]
    push_cast
    ring

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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Logarithmic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.EdgeIntersection

/-!
# Separation of logarithmic Schwarz--Christoffel ends

When the total turning exponent is `-1`, assume the left and right finite endpoints bound
every prevertex with nonzero exponent from below and above, respectively, and that the
exponent sum at each endpoint is greater than `-1` (endpoint integrability). Then the two
outer sides of the normalized Schwarz--Christoffel boundary are parallel horizontal rays
pointing to the right. Their heights are exactly `im c` and `im c + π`, where `c` is the
logarithmic constant at infinity.
Thus their supporting lines are distinct, with separation `π`.

The exact heights identify the two levels of a parallel-sided polygonal end. In particular,
the outer boundary images are automatically disjoint under these hypotheses. The
boundary-simplicity criterion therefore only needs to check intersections among bounded sides
and between bounded sides and the outer rays. No simplicity of the bounded chain or interior
univalence is inferred from the logarithmic asymptotic alone.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The right outer side in the logarithmic case lies exactly at the height of the
logarithmic constant at infinity. Only integrability at its finite endpoint is needed. -/
theorem im_schwarzChristoffelBoundary_of_forall_le_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p : ℝ}
    (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → a i ≤ p) (hsum : ∑ i, e i = -1) :
    (schwarzChristoffelBoundary a e z₀ p).im =
      (schwarzChristoffelLogConstantAtInfinity a e z₀).im := by
  have hheight : ∀ x ∈ Ici p,
      (schwarzChristoffelBoundary a e z₀ x).im =
        (schwarzChristoffelBoundary a e z₀ p).im := by
    intro x hx
    have hmem := mem_image_of_mem (schwarzChristoffelBoundary a e z₀) hx
    rw [schwarzChristoffelBoundary_image_Ici_eq_ray a e z₀ hp ha hsum.ge] at hmem
    obtain ⟨t, _, ht⟩ := hmem
    simpa using (congrArg Complex.im ht).symm
  -- A constant height agrees with its limit in the logarithmic asymptotic.
  have hlimit := (Complex.continuous_im.tendsto _).comp
    (tendsto_schwarzChristoffelBoundary_sub_log_atTop_of_sum_eq_neg_one a e z₀ hsum)
  apply tendsto_nhds_unique (l := atTop)
    (f := fun _ : ℝ => (schwarzChristoffelBoundary a e z₀ p).im) tendsto_const_nhds
  refine hlimit.congr' ?_
  filter_upwards [eventually_ge_atTop p] with x hx
  simpa using hheight x hx

/-- The left outer side in the logarithmic case lies exactly `π` above the height of the
logarithmic constant at infinity. Only integrability at its finite endpoint is needed. -/
theorem im_schwarzChristoffelBoundary_of_forall_ge_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p : ℝ}
    (hp : -1 < ∑ i with a i = p, e i)
    (ha : ∀ i, e i ≠ 0 → p ≤ a i) (hsum : ∑ i, e i = -1) :
    (schwarzChristoffelBoundary a e z₀ p).im =
      (schwarzChristoffelLogConstantAtInfinity a e z₀).im + Real.pi := by
  have hheight : ∀ x ∈ Iic p,
      (schwarzChristoffelBoundary a e z₀ x).im =
        (schwarzChristoffelBoundary a e z₀ p).im := by
    intro x hx
    have hmem := mem_image_of_mem (schwarzChristoffelBoundary a e z₀) hx
    rw [schwarzChristoffelBoundary_image_Iic_eq_ray a e z₀ hp ha hsum.ge] at hmem
    obtain ⟨t, _, ht⟩ := hmem
    simpa [hsum, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I] using
      (congrArg Complex.im ht).symm
  -- The upper boundary value of the logarithm contributes the height difference `π`.
  have hlimit := (Complex.continuous_im.tendsto _).comp
    (tendsto_schwarzChristoffelBoundary_sub_log_neg_atBot_of_sum_eq_neg_one a e z₀ hsum)
  have hconst := tendsto_nhds_unique
    (f := fun _ : ℝ => (schwarzChristoffelBoundary a e z₀ p).im) tendsto_const_nhds
    (hlimit.congr' (by
      filter_upwards [eventually_le_atBot p] with x hx
      simpa using hheight x hx))
  simpa using hconst

/-- The outer boundary images are disjoint when the total exponent is `-1`: they lie
on horizontal lines separated by `π`. The finite prevertices need not be ordered or distinct. -/
theorem disjoint_schwarzChristoffelBoundary_outer_images_of_sum_eq_neg_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {p q : ℝ}
    (hp : -1 < ∑ i with a i = p, e i) (hq : -1 < ∑ i with a i = q, e i)
    (hleft : ∀ i, e i ≠ 0 → p ≤ a i) (hright : ∀ i, e i ≠ 0 → a i ≤ q)
    (hsum : ∑ i, e i = -1) :
    Disjoint (schwarzChristoffelBoundary a e z₀ '' Iic p)
      (schwarzChristoffelBoundary a e z₀ '' Ici q) := by
  rw [disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  have hxsum : -1 < ∑ i with a i = x, e i :=
    Finset.lt_sum_filter_of_lt_zero_of_forall_ne_zero_le (γ := OrderDual ℝ)
      Finset.univ (by norm_num) hp (fun i _ hi => hleft i hi) hx
  have hysum : -1 < ∑ i with a i = y, e i :=
    Finset.lt_sum_filter_of_lt_zero_of_forall_ne_zero_le
      Finset.univ (by norm_num) hq (fun i _ hi => hright i hi) hy
  have hxheight := im_schwarzChristoffelBoundary_of_forall_ge_of_sum_eq_neg_one a e z₀
    hxsum (fun i hi => hx.trans (hleft i hi)) hsum
  have hyheight := im_schwarzChristoffelBoundary_of_forall_le_of_sum_eq_neg_one a e z₀
    hysum (fun i hi => (hright i hi).trans hy) hsum
  have heq := congrArg Complex.im hxy
  rw [hxheight, hyheight] at heq
  linarith [Real.pi_pos]

/-- In the logarithmic case, a Schwarz--Christoffel boundary is simple if bounded sides
meet only at consecutive vertices and each outer ray meets the bounded sides only at its
finite endpoint. No additional intersection condition between the outer rays is needed. -/
theorem schwarzChristoffelBoundary_injective_of_edge_intersections_of_sum_eq_neg_one
    {n : ℕ} (a e : Fin (n + 2) → ℝ) (z₀ : UpperHalfPlane) (ha : Monotone a)
    (hfinite : ∀ k, -1 < ∑ l with a l = a k, e l) (hsum : ∑ k, e k = -1)
    (hinter : ∀ (i j : Fin (n + 1)), i < j →
      ∀ z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc,
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc.castSucc →
          j.val = i.val + 1 ∧ z = schwarzChristoffelVertex a e z₀ i.succ)
    (hleft : ∀ (i : Fin (n + 1)) (z : ℂ),
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
      z ∈ (fun t : ℝ => schwarzChristoffelVertex a e z₀ 0 + (t : ℂ)) '' Ici 0 →
        z = schwarzChristoffelVertex a e z₀ 0)
    (hright : ∀ (i : Fin (n + 1)) (z : ℂ),
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
      z ∈ (fun t : ℝ => schwarzChristoffelVertex a e z₀ (Fin.last (n + 1)) + (t : ℂ)) ''
        Ici 0 → z = schwarzChristoffelVertex a e z₀ (Fin.last (n + 1))) :
    Function.Injective (schwarzChristoffelBoundary a e z₀) := by
  have hfirst : ∀ k, e k ≠ 0 → a 0 ≤ a k := fun k _ => ha k.zero_le
  have hlast : ∀ k, e k ≠ 0 → a k ≤ a (Fin.last (n + 1)) := fun k _ => ha k.le_last
  have houter := disjoint_schwarzChristoffelBoundary_outer_images_of_sum_eq_neg_one a e z₀
    (hfinite 0) (hfinite _) hfirst hlast hsum
  rw [schwarzChristoffelBoundary_image_Iic_eq_ray_prevertex a e z₀ 0
      (hfinite 0) hfirst hsum.ge,
    schwarzChristoffelBoundary_image_Ici_eq_ray_prevertex a e z₀ (Fin.last (n + 1))
      (hfinite _) hlast hsum.ge] at houter
  apply schwarzChristoffelBoundary_injective_of_edge_intersections a e z₀ ha hfinite
    hsum.ge hinter (hright := hright) (houter := houter)
  simpa [hsum, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I] using hleft

end TauCeti

end

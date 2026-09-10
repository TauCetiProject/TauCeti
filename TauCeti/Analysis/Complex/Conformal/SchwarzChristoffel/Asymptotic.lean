/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Edge

/-!
# The Schwarz--Christoffel integrand at a prevertex

Near a real prevertex `p`, all factors of the Schwarz--Christoffel integrand based away from
`p` tend to nonzero limits.  The factors based at `p` combine into the single power
`(z - p) ^ t`, where `t` is the sum of their exponents.  This file identifies the remaining
nonzero coefficient and proves the corresponding normalized limit from the upper half-plane.

The coefficient includes the unimodular phase of the boundary edge immediately to the right of
`p`.  Its remaining factor is a positive real product of the distances from `p` to the other
prevertices.  Consequently the coefficient never vanishes.  This is the local analytic input for
integrating the leading term and obtaining the power-law corner asymptotic of the
Schwarz--Christoffel primitive.

## Main definitions

* `TauCeti.schwarzChristoffelPrevertexCoefficient` -- the nonzero coefficient of the leading
  power of the integrand at a real point.

## Main results

* `TauCeti.schwarzChristoffelPrevertexCoefficient_ne_zero` -- the coefficient is nonzero.
* `TauCeti.norm_schwarzChristoffelPrevertexCoefficient` -- its norm is the positive product of
  distances to the other prevertices.
* `TauCeti.tendsto_schwarzChristoffelIntegrand_div_cpow` -- after division by the total power at
  a prevertex, the integrand tends to its leading coefficient.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The regular part of the continued Schwarz--Christoffel integrand at a real point `p`.
Factors whose prevertex equals `p` are omitted; every remaining factor has positive real base at
`p`, after reflecting the factors whose prevertices lie to its right. -/
private def schwarzChristoffelRegularFactor (a e : ι → ℝ) (p : ℝ) (z : ℂ) : ℂ :=
  ∏ i with a i ≠ p,
    (if a i ≤ p then z - (a i : ℂ) else (a i : ℂ) - z) ^ (e i : ℂ)

/-- The regular part of the continued Schwarz--Christoffel integrand is continuous at its
reference point. -/
private theorem continuousAt_schwarzChristoffelRegularFactor (a e : ι → ℝ) (p : ℝ) :
    ContinuousAt (schwarzChristoffelRegularFactor a e p) (p : ℂ) := by
  classical
  refine tendsto_finsetProd _ fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  by_cases hip : a i ≤ p
  · have hpos : 0 < p - a i := sub_pos.mpr (lt_of_le_of_ne hip hi)
    simp only [ite_eq_left hip]
    refine (continuousAt_cpow_const ?_).comp
      (continuousAt_id.sub continuousAt_const)
    rw [← Complex.ofReal_sub]
    exact Complex.ofReal_mem_slitPlane.mpr hpos
  · have hpos : 0 < a i - p := sub_pos.mpr (lt_of_not_ge hip)
    simp only [ite_eq_right hip]
    refine (continuousAt_cpow_const ?_).comp
      (continuousAt_const.sub continuousAt_id)
    rw [← Complex.ofReal_sub]
    exact Complex.ofReal_mem_slitPlane.mpr hpos

/-- At its reference point, the regular part is the positive real product of the distances to
all other prevertices. -/
private theorem schwarzChristoffelRegularFactor_ofReal (a e : ι → ℝ) (p : ℝ) :
    schwarzChristoffelRegularFactor a e p (p : ℂ) =
      ((∏ i with a i ≠ p, |p - a i| ^ e i : ℝ) : ℂ) := by
  classical
  rw [schwarzChristoffelRegularFactor, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  by_cases hip : a i ≤ p
  · have hpos : 0 < p - a i := sub_pos.mpr (lt_of_le_of_ne hip hi)
    have hcast : (p : ℂ) - (a i : ℂ) = ((p - a i : ℝ) : ℂ) := by push_cast; ring
    rw [ite_eq_left hip, hcast, ← Complex.ofReal_cpow hpos.le, abs_of_pos hpos]
  · have hpos : 0 < a i - p := sub_pos.mpr (lt_of_not_ge hip)
    have hcast : (a i : ℂ) - (p : ℂ) = ((a i - p : ℝ) : ℂ) := by push_cast; ring
    rw [ite_eq_right hip, hcast, ← Complex.ofReal_cpow hpos.le, abs_sub_comm,
      abs_of_pos hpos]

/-- The real product defining the size of the leading coefficient is positive. -/
private theorem prod_rpow_dist_prevertex_pos (a e : ι → ℝ) (p : ℝ) :
    0 < ∏ i with a i ≠ p, |p - a i| ^ e i := by
  classical
  refine Finset.prod_pos fun i hi => ?_
  exact Real.rpow_pos_of_pos
    (abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hi).2.symm)) _

/-- The **leading coefficient of the Schwarz--Christoffel integrand at a real point** `p`.

The exponential records the direction of the boundary edge immediately to the right of `p`.
The positive real product is the contribution at `p` of every factor based at a different
prevertex.  If `p` is not itself a prevertex, this is simply the boundary value of the integrand
there. -/
def schwarzChristoffelPrevertexCoefficient (a e : ι → ℝ) (p : ℝ) : ℂ :=
  Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) *
    ((∏ i with a i ≠ p, |p - a i| ^ e i : ℝ) : ℂ)

/-- The leading coefficient is its boundary direction times the positive product of distances to
the other prevertices. -/
theorem schwarzChristoffelPrevertexCoefficient_def (a e : ι → ℝ) (p : ℝ) :
    schwarzChristoffelPrevertexCoefficient a e p =
      Complex.exp (schwarzChristoffelEdgeAngle a e p * Complex.I) *
        ((∏ i with a i ≠ p, |p - a i| ^ e i : ℝ) : ℂ) :=
  (rfl)

/-- The norm of the leading coefficient is the positive real product of the powered distances
from `p` to the other prevertices. -/
theorem norm_schwarzChristoffelPrevertexCoefficient (a e : ι → ℝ) (p : ℝ) :
    ‖schwarzChristoffelPrevertexCoefficient a e p‖ =
      ∏ i with a i ≠ p, |p - a i| ^ e i := by
  have hpos := prod_rpow_dist_prevertex_pos a e p
  have hre : (schwarzChristoffelEdgeAngle a e p * Complex.I : ℂ).re = 0 := by simp
  rw [schwarzChristoffelPrevertexCoefficient_def, norm_mul, Complex.norm_exp, hre,
    Real.exp_zero, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]

/-- The leading coefficient of the Schwarz--Christoffel integrand at a real point is nonzero. -/
theorem schwarzChristoffelPrevertexCoefficient_ne_zero (a e : ι → ℝ) (p : ℝ) :
    schwarzChristoffelPrevertexCoefficient a e p ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_schwarzChristoffelPrevertexCoefficient]
  exact ne_of_gt (prod_rpow_dist_prevertex_pos a e p)

/-- The continued Schwarz--Christoffel integrand splits into its power singularity at `p` and a
factor continuous and nonzero there. -/
private theorem schwarzChristoffelContinuedIntegrand_eq_cpow_mul_regularFactor
    (a e : ι → ℝ) (p : ℝ) {z : ℂ} (hz : z ≠ (p : ℂ)) :
    schwarzChristoffelContinuedIntegrand a e p z =
      (z - (p : ℂ)) ^ ((∑ i with a i = p, e i : ℝ) : ℂ) *
        schwarzChristoffelRegularFactor a e p z := by
  classical
  rw [schwarzChristoffelContinuedIntegrand_def, schwarzChristoffelRegularFactor,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => a i = p)]
  congr 1
  calc
    (∏ i with a i = p,
        (if a i ≤ p then z - (a i : ℂ) else (a i : ℂ) - z) ^ (e i : ℂ)) =
        ∏ i with a i = p, (z - (p : ℂ)) ^ (e i : ℂ) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have haip : a i = p := (Finset.mem_filter.mp hi).2
          rw [haip, ite_eq_left le_rfl]
    _ = (z - (p : ℂ)) ^ ((∑ i with a i = p, e i : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      induction Finset.univ.filter (fun i => a i = p) using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          rw [Finset.prod_insert hi, Finset.sum_insert hi, ih,
            ← Complex.cpow_add _ _ (sub_ne_zero.mpr hz)]

/-- **Leading asymptotic of the Schwarz--Christoffel integrand at a prevertex.**  Dividing the
integrand by `(z - p)` raised to the total exponent carried by `p` leaves a function tending to the
nonzero prevertex coefficient as `z` approaches `p` from the upper half-plane.  Coincident
prevertices are handled by summing all of their exponents. -/
theorem tendsto_schwarzChristoffelIntegrand_div_cpow (a e : ι → ℝ) (p : ℝ) :
    Tendsto
      (fun z => schwarzChristoffelIntegrand a e z /
        (z - (p : ℂ)) ^ ((∑ i with a i = p, e i : ℝ) : ℂ))
      (𝓝[upperHalfPlaneSet] (p : ℂ))
      (𝓝 (schwarzChristoffelPrevertexCoefficient a e p)) := by
  have hregular := (continuousAt_schwarzChristoffelRegularFactor a e p).tendsto
  rw [schwarzChristoffelPrevertexCoefficient_def,
    ← schwarzChristoffelRegularFactor_ofReal]
  refine Tendsto.congr' ?_
    (tendsto_const_nhds.mul (hregular.mono_left nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzp : z ≠ (p : ℂ) := by
    intro h
    rw [h] at hz
    simp at hz
  rw [schwarzChristoffelIntegrand_eq_exp_mul_continued a e p hz,
    schwarzChristoffelContinuedIntegrand_eq_cpow_mul_regularFactor a e p hzp]
  field_simp [Complex.cpow_ne_zero_iff.mpr (Or.inl (sub_ne_zero.mpr hzp))]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Integrand
public import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Slope
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.Complex.AtInfinity

/-!
# Complex asymptotics of the Schwarz--Christoffel integrand at infinity

Writing `S = ∑ i, e i`, the integrand has the expansion

`schwarzChristoffelIntegrand a e z / z ^ S = 1 - (∑ i, e i * a i) / z + o(1 / z)`

as `z` tends to infinity through the whole upper half-plane. In particular, the normalized
integrand tends to one, with error `O(1 / z)`. These estimates retain the complex phase, even
for approaches arbitrarily close to the negative real axis. They provide derivative estimates
for the power-law growth of the primitive and for properness of unbounded polygonal maps.

The normalization equals `∏ i, (1 - a i / z) ^ e i` on the upper half-plane. This product is
holomorphic as a function of `1 / z` near zero; its value and derivative there give the two
terms. No ordering, distinctness, integrability, or sign conditions on the data are needed.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Asymptotics Bornology Complex Filter Finset Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- Dividing the Schwarz--Christoffel integrand by its total power gives a product in the
reciprocal coordinate. This identity uses the principal branches on the upper half-plane. -/
theorem schwarzChristoffelIntegrand_div_cpow_eq_prod (a e : ι → ℝ) {z : ℂ}
    (hz : z ∈ upperHalfPlaneSet) :
    schwarzChristoffelIntegrand a e z / z ^ ((∑ i, e i : ℝ) : ℂ) =
      ∏ i, (1 - (a i : ℂ) * z⁻¹) ^ (e i : ℂ) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  rw [schwarzChristoffelIntegrand_def, ofReal_sum, cpow_sum hz0,
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have him : 0 < (z - (a i : ℂ)).im := by simpa using hz
  rw [← div_cpow_of_im_pos him hz]
  congr 1
  field_simp

/-- **First correction at infinity.** The coefficient of `1 / z` in the normalized
Schwarz--Christoffel integrand is the negative weighted sum of the real prevertices. The limit
holds uniformly over all directions in the upper half-plane. -/
theorem tendsto_mul_schwarzChristoffelIntegrand_div_cpow_sub_one_atInfinity (a e : ι → ℝ) :
    Tendsto (fun z : ℂ => z *
      (schwarzChristoffelIntegrand a e z / z ^ ((∑ i, e i : ℝ) : ℂ) - 1))
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 (-∑ i, (e i : ℂ) * (a i : ℂ))) := by
  classical
  -- Every reciprocal-coordinate factor has base one at zero, away from the branch cut.
  have hfactor (i : ι) : HasDerivAt
      (fun w : ℂ => (1 - (a i : ℂ) * w) ^ (e i : ℂ))
      (-(e i : ℂ) * (a i : ℂ)) 0 := by
    have h := (((hasDerivAt_id (0 : ℂ)).const_mul (a i : ℂ)).const_sub 1).cpow_const
      (c := (e i : ℂ)) (by simp [Complex.slitPlane])
    simpa using h
  have hprod : HasDerivAt (fun w : ℂ => ∏ i, (1 - (a i : ℂ) * w) ^ (e i : ℂ))
      (-∑ i, (e i : ℂ) * (a i : ℂ)) 0 := by
    simpa [Finset.sum_neg_distrib] using HasDerivAt.fun_finsetProd
      (u := Finset.univ) (fun i _ => hfactor i)
  have h := hprod.tendsto_slope_zero.comp
    (tendsto_inv₀_cobounded'.mono_left
      (inf_le_left : cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet ≤ cobounded ℂ))
  simp only [zero_add, mul_zero, sub_zero, one_cpow, prod_const_one, smul_eq_mul] at h
  refine h.congr' ?_
  filter_upwards [mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hz
  rw [schwarzChristoffelIntegrand_div_cpow_eq_prod a e hz]
  simp only [Function.comp_apply, inv_inv]

/-- **Complex leading term at infinity.** The Schwarz--Christoffel integrand divided by
`z ^ (∑ i, e i)` tends to one through the entire upper half-plane. -/
theorem tendsto_schwarzChristoffelIntegrand_div_cpow_atInfinity (a e : ι → ℝ) :
    Tendsto (fun z : ℂ => schwarzChristoffelIntegrand a e z / z ^ ((∑ i, e i : ℝ) : ℂ))
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 1) := by
  have h := tendsto_zero_of_tendsto_mul_cobounded inf_le_left
    (tendsto_mul_schwarzChristoffelIntegrand_div_cpow_sub_one_atInfinity a e)
  simpa only [sub_add_cancel, zero_add] using h.add (tendsto_const_nhds (x := (1 : ℂ)))

/-- The relative error of the leading power of the Schwarz--Christoffel integrand is
`O(1 / z)` throughout the upper half-plane at infinity. -/
theorem isBigO_schwarzChristoffelIntegrand_div_cpow_sub_one_atInfinity (a e : ι → ℝ) :
    (fun z : ℂ => schwarzChristoffelIntegrand a e z / z ^ ((∑ i, e i : ℝ) : ℂ) - 1)
      =O[cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet] (fun z : ℂ => z⁻¹) := by
  refine isBigO_of_div_tendsto_nhds ?_ (-∑ i, (e i : ℂ) * (a i : ℂ)) ?_
  · filter_upwards [mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hz
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz
    exact fun h => (inv_ne_zero hz0 h).elim
  · convert tendsto_mul_schwarzChristoffelIntegrand_div_cpow_sub_one_atInfinity a e using 1
    ext z
    simp [div_inv_eq_mul, mul_comm]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Asymptotic
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# The second correction to the Schwarz--Christoffel integrand at infinity

Write `S = ∑ i, e i`, `M = ∑ i, e i * a i`, and
`C = (M ^ 2 - ∑ i, e i * a i ^ 2) / 2`. The normalized integrand has expansion

`integrand(z) / z ^ S = 1 - M / z + C / z ^ 2 + o(1 / z ^ 2)`.

The limit holds through the whole upper half-plane, including tangential approaches to the
real axis. No ordering, distinctness, integrability, or sign conditions on the finite data
are required.

At total exponent `S = 1`, this gives
`integrand(z) = z - M + C / z + o(1 / z)`. The coefficient `C` is therefore the
logarithmic coefficient when the primitive's quadratic and linear leading terms are removed.
This is the analytic input for separating the parallel outer sides of a polygonal end of
opening `2π`; the leading quadratic term alone does not distinguish their supporting lines.
No asymptotic for the primitive or boundary separation is claimed here.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

open Bornology Complex Filter Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **Second correction at infinity.** The quadratic coefficient of the normalized
Schwarz--Christoffel integrand is half the difference between the square of the first weighted
moment and the second weighted moment of the prevertices. The limit is uniform in direction
within the upper half-plane. -/
theorem tendsto_sq_mul_schwarzChristoffelIntegrand_div_cpow_sub_linear_atInfinity
    (a e : ι → ℝ) :
    Tendsto (fun z : ℂ => z ^ 2 *
      (schwarzChristoffelIntegrand a e z / z ^ ((∑ i, e i : ℝ) : ℂ) - 1 +
        (∑ i, (e i : ℂ) * (a i : ℂ)) / z))
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet)
      (𝓝 (((∑ i, (e i : ℂ) * (a i : ℂ)) ^ 2 -
        ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2)) := by
  have h := (tendsto_prod_one_sub_mul_cpow_sub_linear_div_sq
    (fun i => (a i : ℂ)) (fun i => (e i : ℂ))).comp
      (tendsto_inv₀_cobounded'.mono_left
        (inf_le_left : cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet ≤ cobounded ℂ))
  refine h.congr' ?_
  filter_upwards [mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hz
  rw [schwarzChristoffelIntegrand_div_cpow_eq_prod a e hz]
  simp [div_eq_mul_inv, inv_pow, mul_comm]

/-- **The integrand at an end of opening `2π`.** At total exponent one, subtracting the
linear and constant terms leaves a `1 / z` term with the explicit real coefficient displayed
in the conclusion. This coefficient becomes a logarithmic term after integration. -/
theorem tendsto_mul_schwarzChristoffelIntegrand_sub_linear_atInfinity_of_sum_eq_one
    (a e : ι → ℝ) (hsum : ∑ i, e i = 1) :
    Tendsto (fun z : ℂ => z *
      (schwarzChristoffelIntegrand a e z - z + ∑ i, (e i : ℂ) * (a i : ℂ)))
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet)
      (𝓝 (((∑ i, (e i : ℂ) * (a i : ℂ)) ^ 2 -
        ∑ i, (e i : ℂ) * (a i : ℂ) ^ 2) / 2)) := by
  refine (tendsto_sq_mul_schwarzChristoffelIntegrand_div_cpow_sub_linear_atInfinity a e).congr' ?_
  filter_upwards [mem_inf_of_right (mem_principal_self upperHalfPlaneSet)] with z hz
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  simp only [hsum, ofReal_one, cpow_one]
  field_simp

end TauCeti

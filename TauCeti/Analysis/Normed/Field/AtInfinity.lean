/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Bornology.BoundedOperation

/-!
# Limits at infinity in normed rings and fields

Limits along `Bornology.cobounded`, the filter at infinity of a normed ring.

In a normed ring with multiplicative norm, if `z * ψ z` has a finite limit along a filter
approaching infinity, then `ψ z` tends to zero. In a normed division ring, if `ζ` tends to infinity
then so does the normalized coordinate `(ζ - c) / b`, for `b ≠ 0`; in particular so does
`(q + g⁻¹ - c) / b` when `g` tends to `0` without vanishing. In a normed field, a finite product of
powers of `1 - z * w⁻¹` tends to one as `w` tends to infinity; together with
`Finset.prod_sub_pow_eq_pow_sum_mul_prod_one_sub_mul_inv_pow`, this says that a product of powers
of `w - z` behaves like `w` to the total exponent at infinity.

## Main results

* `TauCeti.tendsto_zero_of_tendsto_mul_cobounded`: `z * ψ z → c` at infinity forces `ψ z → 0`.
* `TauCeti.tendsto_sub_div_of_tendsto_cobounded`: `(ζ - c) / b` tends to infinity with `ζ`.
* `TauCeti.tendsto_cobounded_div_of_tendsto_nhdsNE_zero`: `(q + g⁻¹ - c) / b` tends to infinity
  as `g` tends to `0` without vanishing.
* `Finset.tendsto_prod_one_sub_mul_inv_pow`: `∏ z ∈ s, (1 - z * w⁻¹) ^ n z → 1` at infinity.
-/

public section

open Bornology Filter Topology

namespace TauCeti

/-- If `z * ψ z` has a finite limit along a filter approaching infinity in a normed ring with
multiplicative norm, then `ψ z` tends to zero. -/
theorem tendsto_zero_of_tendsto_mul_cobounded {𝕜 : Type*} [NormedRing 𝕜] [NormMulClass 𝕜]
    {l : Filter 𝕜} (hl : l ≤ cobounded 𝕜) {ψ : 𝕜 → 𝕜} {c : 𝕜}
    (h : Tendsto (fun z => z * ψ z) l (𝓝 c)) :
    Tendsto ψ l (𝓝 0) := by
  nontriviality 𝕜
  have := NoZeroDivisors.to_isDomain 𝕜
  exact tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded (f := id)
    (by simpa only [id, smul_eq_mul] using h.norm.isBoundedUnder_le) hl

section NormedDivisionRing

variable {𝕜 : Type*} [NormedDivisionRing 𝕜]

/-- If `ζ` tends to infinity, then so does the normalized coordinate `(ζ - c) / b`, for `b ≠ 0`. -/
theorem tendsto_sub_div_of_tendsto_cobounded {α : Type*} {l : Filter α} {ζ : α → 𝕜} {c b : 𝕜}
    (hb : b ≠ 0) (hζ : Tendsto ζ l (cobounded 𝕜)) :
    Tendsto (fun a => (ζ a - c) / b) l (cobounded 𝕜) := by
  simpa [div_eq_mul_inv, Function.comp_def] using
    (tendsto_mul_right_cobounded (inv_ne_zero hb)).comp ((tendsto_sub_const_cobounded c).comp hζ)

/-- If `g` tends to `0` without vanishing, the normalized coordinate `(q + g⁻¹ - c) / b` of the
inverted point `q + g⁻¹` tends to infinity, for `b ≠ 0`. -/
theorem tendsto_cobounded_div_of_tendsto_nhdsNE_zero {α : Type*} {l : Filter α} {g : α → 𝕜}
    {q c b : 𝕜} (hb : b ≠ 0) (hg : Tendsto g l (𝓝[≠] 0)) :
    Tendsto (fun a => (q + (g a)⁻¹ - c) / b) l (cobounded 𝕜) :=
  tendsto_sub_div_of_tendsto_cobounded hb
    ((tendsto_const_add_cobounded q).comp (tendsto_inv₀_nhdsNE_zero.comp hg))

end NormedDivisionRing

end TauCeti

namespace Finset

/-- A product of powers of `1 - z * w⁻¹` tends to one as `w` tends to infinity. -/
theorem tendsto_prod_one_sub_mul_inv_pow {𝕜 : Type*} [NormedField 𝕜] (s : Finset 𝕜)
    (n : 𝕜 → ℕ) :
    Tendsto (fun w ↦ ∏ z ∈ s, (1 - z * w⁻¹) ^ n z) (cobounded 𝕜) (𝓝 1) := by
  have := tendsto_finsetProd s fun z _ ↦
    (tendsto_const_nhds (x := (1 : 𝕜)).sub (tendsto_inv₀_cobounded.const_mul z)).pow (n z)
  simpa only [mul_zero, sub_zero, one_pow, prod_const_one] using this

end Finset

end

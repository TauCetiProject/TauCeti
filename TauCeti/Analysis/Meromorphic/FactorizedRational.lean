/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.FactorizedRational
public import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Evaluation, logarithmic derivative and splitting of factorized rational functions

For a finitely supported exponent `d : 𝕜 → ℤ`, Mathlib's `Function.FactorizedRational` studies
the function `∏ᶠ u, (· - u) ^ d u`. This file adds three facts about it:

* `Function.FactorizedRational.finprod_apply_eq_prod`: its value at a point is the finite product
  `∏ u ∈ support d, (y - u) ^ d u`;
* `Function.FactorizedRational.logDeriv_eq_finsum`: at a point `z` with `d z = 0` its logarithmic
  derivative is `∑ᶠ u, d u / (z - u)`;
* `Function.FactorizedRational.finprod_eq_finprod_mul_finprod_sub`: if `d'` vanishes wherever `d`
  does, it is the product of the factorized rational functions with exponents `d'` and `d - d'`.
-/

public section

namespace Function.FactorizedRational

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {d : 𝕜 → ℤ}

/-- The value at `y` of the finitely supported product `∏ᶠ u, (· - u) ^ d u`, as a finite
product over the support of `d`. -/
theorem finprod_apply_eq_prod (hd : d.support.Finite) (y : 𝕜) :
    (∏ᶠ u, (· - u) ^ d u) y = ∏ u ∈ hd.toFinset, (y - u) ^ d u :=
  (congrFun (finprod_eq_fun hd) y).trans <|
    finprod_eq_prod_of_mulSupport_subset _ fun u hu ↦
      hd.mem_toFinset.2 fun h ↦ hu (by simp [h])

/-- **Logarithmic derivative of a factorized rational function.** If `d` has finite support,
then at a point `z` with `d z = 0` the logarithmic derivative of `∏ᶠ u, (· - u) ^ d u` is
`∑ᶠ u, d u / (z - u)`. -/
theorem logDeriv_eq_finsum (hd : d.support.Finite) {z : 𝕜} (hz : d z = 0) :
    logDeriv (∏ᶠ u, (· - u) ^ d u) z = ∑ᶠ u, (d u : 𝕜) / (z - u) := by
  classical
  have hzu (u : 𝕜) (hu : u ∈ hd.toFinset) : z - u ≠ 0 :=
    sub_ne_zero.2 fun h ↦ hd.mem_toFinset.1 hu (h ▸ hz)
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hd.toFinset)
      (by rw [mulSupport d, hd.coe_toFinset])]
  simp only [Pi.pow_def]
  rw [logDeriv_prod (f := fun u w ↦ (w - u) ^ d u) (fun u hu ↦ zpow_ne_zero _ (hzu u hu))
      fun u hu ↦ (differentiableAt_id.sub_const u).zpow (.inl (hzu u hu)),
    finsum_eq_sum_of_support_subset (s := hd.toFinset)]
  · refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [logDeriv_fun_zpow (f := fun w ↦ w - u) (by fun_prop)]
    simp [logDeriv_apply, div_eq_mul_inv]
  · exact fun u hu ↦ hd.mem_toFinset.2 fun h ↦ hu (by simp [h])

/-- **Splitting a factorized rational function.** If `d` has finite support and `d'` vanishes
wherever `d` does, then `∏ᶠ u, (· - u) ^ d u` is the product of the factorized rational functions
with exponents `d'` and `d - d'`. -/
theorem finprod_eq_finprod_mul_finprod_sub {d' : 𝕜 → ℤ} (hd : d.support.Finite)
    (h : d'.support ⊆ d.support) :
    (∏ᶠ u, (· - u) ^ d u) = (∏ᶠ u, (· - u) ^ d' u) * ∏ᶠ u, (· - u) ^ (d u - d' u) := by
  have hfin {e : 𝕜 → ℤ} (he : e.support.Finite) :
      (fun u ↦ (· - u) ^ e u : 𝕜 → 𝕜 → 𝕜).HasFiniteMulSupport := by
    rw [Function.HasFiniteMulSupport, mulSupport]
    exact he
  -- `d'` vanishes wherever `d` does.
  have h' {u : 𝕜} (hdu : d u = 0) : d' u = 0 := notMem_support.1 fun hu ↦ h hu hdu
  have hsub : (fun u ↦ d u - d' u).support.Finite := hd.subset fun u hu hdu ↦
    hu <| by simp [hdu, h' hdu]
  rw [← finprod_mul_distrib (hfin (hd.subset h)) (hfin hsub)]
  refine finprod_congr fun u ↦ funext fun x ↦ ?_
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [← zpow_add']
  · simp
  · by_cases hdu : d u = 0
    · exact .inr (.inr ⟨h' hdu, by simp [hdu, h' hdu]⟩)
    · exact .inr (.inl (by simpa using hdu))

end Function.FactorizedRational

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measure-preserving subgroup shear and product integrability

Let `R` be a subgroup of a measurable group `G`, equipped with an s-finite measure `ν` on `R` and
an s-finite left-invariant measure `μ` on `G`. For any `g : G`, the subgroup shear map
`(s, x) ↦ (s, g * (s : G)⁻¹ * x)` preserves the product measure `ν.prod μ`
(`TauCeti.measurePreserving_subgroup_shear`). Consequently, for any `ν`-integrable scalar function
`a : R → 𝕜` and `μ`-integrable function `e : G → E`, the sheared product
`(s, x) ↦ a s • e (g * (s : G)⁻¹ * x)` is `ν.prod μ`-integrable
(`MeasureTheory.Integrable.smul_comp_inv_mul`) and its product integral factors as
`(∫ s, a s ∂ν) • (∫ x, e x ∂μ)` (`TauCeti.integral_prod_smul_comp_inv_mul`).

## Main results

* `TauCeti.measurePreserving_subgroup_shear`: the shear `(s, x) ↦ (s, g * s⁻¹ * x)` preserves
  `ν.prod μ`.
* `MeasureTheory.Integrable.smul_comp_inv_mul`: integrability of
  `(s, x) ↦ a s • e (g * s⁻¹ * x)`.
* `TauCeti.integral_prod_smul_comp_inv_mul`: product integral evaluation via the shear.

## Provenance

Adapted from `New.integrable_mul_comp_inv_mul` in `grh-lean`
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
file `src/Lib/Adelic/QuotientMeasure/MovingTheQuotient.lean`).
-/

public section

open MeasureTheory Measure

section

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {R : Subgroup G} {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant]
  {ν : Measure R} [SFinite ν]

/-- The subgroup shear `(s, x) ↦ (s, g * (s : G)⁻¹ * x)` preserves the product measure `ν.prod μ`
whenever `μ` is left-invariant on `G`. -/
theorem TauCeti.measurePreserving_subgroup_shear (g : G) :
    MeasurePreserving (fun p : R × G ↦ (p.fst, g * (p.fst : G)⁻¹ * p.snd))
      (ν.prod μ) (ν.prod μ) :=
  (MeasurePreserving.id ν).skew_product
    (g := fun (s : R) (x : G) ↦ g * (s : G)⁻¹ * x)
    (by fun_prop)
    (.of_forall fun s ↦ map_mul_left_eq_self μ (g * (s : G)⁻¹))

/-- If `a : R → 𝕜` is `ν`-integrable and `e : G → E` is `μ`-integrable for a left-invariant
measure `μ`, then `(s, x) ↦ a s • e (g * (s : G)⁻¹ * x)` is integrable on `R × G`. -/
theorem MeasureTheory.Integrable.smul_comp_inv_mul {𝕜 E : Type*} [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    {a : R → 𝕜} (ha : Integrable a ν) {e : G → E} (he : Integrable e μ) (g : G) :
    Integrable (fun p : R × G ↦ a p.fst • e (g * (p.fst : G)⁻¹ * p.snd)) (ν.prod μ) :=
  (TauCeti.measurePreserving_subgroup_shear (R := R) (μ := μ) (ν := ν) g)
    |>.integrable_comp_of_integrable (ha.smul_prod he)

/-- The product integral of `(s, x) ↦ a s • e (g * (s : G)⁻¹ * x)` over `ν.prod μ` factors as
`(∫ s, a s ∂ν) • (∫ x, e x ∂μ)`. -/
theorem TauCeti.integral_prod_smul_comp_inv_mul {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    (a : R → 𝕜) (e : G → E) (g : G) :
    ∫ p : R × G, a p.fst • e (g * (p.fst : G)⁻¹ * p.snd) ∂(ν.prod μ) =
      (∫ s : R, a s ∂ν) • ∫ x : G, e x ∂μ := by
  let φ : R × G ≃ᵐ R × G :=
    { toFun := fun p ↦ (p.fst, g * (p.fst : G)⁻¹ * p.snd)
      invFun := fun p ↦ (p.fst, (p.fst : G) * g⁻¹ * p.snd)
      left_inv := fun p ↦ by simp [mul_assoc]
      right_inv := fun p ↦ by simp [mul_assoc]
      measurable_toFun :=
        measurable_fst.prodMk
          ((measurable_const.mul measurable_fst.subtypeVal.inv).mul measurable_snd)
      measurable_invFun :=
        measurable_fst.prodMk
          ((measurable_fst.subtypeVal.mul measurable_const).mul measurable_snd) }
  have hmp : MeasurePreserving φ (ν.prod μ) (ν.prod μ) :=
    TauCeti.measurePreserving_subgroup_shear (R := R) (μ := μ) (ν := ν) g
  exact (hmp.integral_comp' (g := fun p : R × G ↦ a p.fst • e p.snd)).trans (integral_prod_smul a e)

end

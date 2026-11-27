/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import TauCeti.MeasureTheory.Measure.Haar.ArchimedeanMultHaar
import TauCeti.MeasureTheory.Measure.PiWithDensity

/-!
# The archimedean factor `d^×x_∞` of the idele measure

For a number field `K`, the archimedean factor `d^×x_∞` of the normalized Haar measure on the
ideles is the product over the infinite places of `dx / |x|` at the real places and of
`2 dx dy / (x² + y²)` at the complex places (`TauCeti.realMultHaar`, `TauCeti.complexMultHaar`).
This file defines it on the mixed space `ℝ^{r₁} × ℂ^{r₂}` of `K` (`TauCeti.mixedMultHaar`) and
proves:

* `TauCeti.mixedMultHaar_eq_withDensity`: the defining equation of the roadmap. `d^×x_∞` is the
  additive measure `μ_∞` (`dx` at real places, `2 dx dy` at complex places, that is `2 ^ r₂` times
  `volume`) with density `N(x)⁻¹`, the inverse of the product of the normalized absolute values
  `mixedEmbedding.norm x`, which is squared at complex places. In particular `d^×x_∞` does not
  charge the non-units `N(x) = 0` (`TauCeti.mixedMultHaar_setOf_norm_eq_zero`).
* `TauCeti.map_mixedMultHaar_mul_left`: `d^×x_∞` is invariant under multiplication by every unit
  `c` of the mixed space, `N(c) ≠ 0`.
* `TauCeti.mixedMultHaar_prod_pi`: the mass of a box is the product of the archimedean masses of
  its sides.
* `TauCeti.mixedMultHaar_box_one_exp_one`: the box with `[1, e]` at every real place and the
  annulus `1 ≤ |z| ≤ e` at every complex place has mass `(4π) ^ r₂`. Over `ℚ` this is the
  archimedean factor `[1, e]` of mass `1`, and at the complex place of an imaginary quadratic
  field it is the annulus of mass `4π`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, §2.3.
-/

public section

open MeasureTheory Measure Set NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped ENNReal Real

namespace TauCeti

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- The archimedean factor `d^×x_∞` of the normalized Haar measure on the ideles of a number field
`K`, as a measure on the mixed space `ℝ^{r₁} × ℂ^{r₂}`: the product of `dx / |x|` over the real
places and of `2 dx dy / (x² + y²)` over the complex places. It does not charge the non-units
(`TauCeti.mixedMultHaar_setOf_norm_eq_zero`). -/
noncomputable def mixedMultHaar : Measure (mixedSpace K) :=
  (Measure.pi fun _ : {w : InfinitePlace K // IsReal w} ↦ realMultHaar).prod
    (Measure.pi fun _ : {w : InfinitePlace K // IsComplex w} ↦ complexMultHaar)

open scoped Classical in
/-- The defining formula of `d^×x_∞`, as a product measure over the infinite places. -/
theorem mixedMultHaar_def : mixedMultHaar K =
    (Measure.pi fun _ : {w : InfinitePlace K // IsReal w} ↦ realMultHaar).prod
      (Measure.pi fun _ : {w : InfinitePlace K // IsComplex w} ↦ complexMultHaar) := (rfl)

open scoped Classical in
instance : SigmaFinite (mixedMultHaar K) := by
  rw [mixedMultHaar_def]
  infer_instance

variable {K}

open scoped Classical in
/-- **The box formula.** `d^×x_∞` gives a box the product of the archimedean masses of its sides:
`dx / |x|` at the real places and `2 dx dy / (x² + y²)` at the complex places. -/
theorem mixedMultHaar_prod_pi (s : {w : InfinitePlace K // IsReal w} → Set ℝ)
    (t : {w : InfinitePlace K // IsComplex w} → Set ℂ) :
    mixedMultHaar K (univ.pi s ×ˢ univ.pi t) =
      (∏ w, realMultHaar (s w)) * ∏ w, complexMultHaar (t w) := by
  rw [mixedMultHaar_def, prod_prod, pi_pi, pi_pi]

open scoped Classical in
/-- **Invariance.** `d^×x_∞` is invariant under multiplication by a unit of the mixed space, that
is by every `c` with `N(c) ≠ 0`. -/
theorem map_mixedMultHaar_mul_left {c : mixedSpace K} (hc : mixedEmbedding.norm c ≠ 0) :
    (mixedMultHaar K).map (c * ·) = mixedMultHaar K := by
  have hc' := (mixedEmbedding.norm_ne_zero_iff).mp hc
  have h1 (w : {w : InfinitePlace K // IsReal w}) : c.1 w ≠ 0 := by
    simpa [normAtPlace_apply_of_isReal w.prop] using hc' w.val
  have h2 (w : {w : InfinitePlace K // IsComplex w}) : c.2 w ≠ 0 := by
    simpa [normAtPlace_apply_of_isComplex w.prop] using hc' w.val
  have : ∀ w, SigmaFinite (realMultHaar.map (c.1 w * ·)) := fun w ↦ by
    rw [map_realMultHaar_mul_left (h1 w)]
    infer_instance
  have : ∀ w, SigmaFinite (complexMultHaar.map (c.2 w * ·)) := fun w ↦ by
    rw [map_complexMultHaar_mul_left (h2 w)]
    infer_instance
  have hmul : (c * · : mixedSpace K → mixedSpace K) =
      Prod.map (fun x w ↦ c.1 w * x w) (fun x w ↦ c.2 w * x w) := rfl
  rw [hmul, mixedMultHaar_def, ← map_prod_map _ _ (by fun_prop) (by fun_prop),
    pi_map_pi fun w ↦ (measurable_const_mul (c.1 w)).aemeasurable,
    pi_map_pi fun w ↦ (measurable_const_mul (c.2 w)).aemeasurable]
  simp_rw [map_realMultHaar_mul_left (h1 _), map_complexMultHaar_mul_left (h2 _)]

open scoped Classical in
/-- The norm `N(x)` of a point of the mixed space is the product of the absolute values of its
real coordinates and of the squared absolute values of its complex coordinates. -/
theorem mixedEmbedding_norm_eq_prod_mul_prod (x : mixedSpace K) :
    mixedEmbedding.norm x = (∏ w, ‖x.1 w‖) * ∏ w, ‖x.2 w‖ ^ 2 := by
  classical
  rw [mixedEmbedding.norm_apply, prod_eq_prod_mul_prod]
  congr 1
  · exact Finset.prod_congr rfl fun w _ ↦ by
      rw [normAtPlace_apply_of_isReal w.prop, mult_isReal w, pow_one]
  · exact Finset.prod_congr rfl fun w _ ↦ by
      rw [normAtPlace_apply_of_isComplex w.prop, mult_isComplex w]

open scoped Classical in
/-- **The defining equation of `d^×x_∞`.** It is the additive measure `μ_∞ = 2 ^ r₂ • volume`
(`dx` at the real places, `2 dx dy` at the complex places) with density `N(x)⁻¹`, the inverse of
the product of the normalized absolute values. -/
theorem mixedMultHaar_eq_withDensity :
    mixedMultHaar K = volume.withDensity fun x ↦
      ENNReal.ofReal (2 ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹) := by
  rw [mixedMultHaar_def, realMultHaar_def, complexMultHaar_def,
    pi_withDensity _ fun _ ↦ (by fun_prop), pi_withDensity _ fun _ ↦ (by fun_prop),
    ← volume_pi, ← volume_pi, prod_withDensity (by fun_prop) (by fun_prop), ← volume_eq_prod]
  refine withDensity_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  rw [← ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ by positivity,
    ← ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ by positivity, ← ENNReal.ofReal_mul (by positivity),
    mixedEmbedding_norm_eq_prod_mul_prod, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]
  congr 1
  simp only [Real.norm_eq_abs, Finset.prod_inv_distrib, mul_inv]
  ring

open scoped Classical in
/-- `d^×x_∞` does not charge the non-units of the mixed space, the points with `N(x) = 0`. -/
theorem mixedMultHaar_setOf_norm_eq_zero :
    mixedMultHaar K {x | mixedEmbedding.norm x = 0} = 0 := by
  rw [mixedMultHaar_eq_withDensity, withDensity_apply_eq_zero' (by fun_prop)]
  refine measure_mono_null (fun x hx ↦ ?_) (measure_empty (μ := volume))
  simp only [mem_inter_iff, mem_ofPred_eq] at hx
  simp [hx.2] at hx

open scoped Classical in
/-- **The box Check.** The box with `[1, e]` at every real place and the annulus `1 ≤ |z| ≤ e` at
every complex place has `d^×x_∞` mass `(4π) ^ r₂`: each real side has mass `log e = 1` and each
complex side has mass `2 · 2π · log e = 4π`. Over `ℚ` the box is `[1, e]` of mass `1`; at the
complex place of an imaginary quadratic field it is the annulus of mass `4π`. -/
theorem mixedMultHaar_box_one_exp_one :
    mixedMultHaar K (univ.pi (fun _ ↦ Icc 1 (Real.exp 1)) ×ˢ
      univ.pi fun _ ↦ {z : ℂ | ‖z‖ ∈ Icc 1 (Real.exp 1)}) =
      ENNReal.ofReal (4 * π) ^ nrComplexPlaces K := by
  rw [mixedMultHaar_prod_pi, realMultHaar_Icc_one_exp_one,
    complexMultHaar_setOf_norm_mem_Icc_one_exp_one, Finset.prod_const_one, one_mul,
    Finset.prod_const, Finset.card_univ]

end TauCeti

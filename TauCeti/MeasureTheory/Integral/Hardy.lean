/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.MultHaar
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Hardy's inequalities

For `θ > 0` and `1 ≤ q ≤ ∞`, the averaging operators on `(0, ∞)` with respect to the
multiplicative Haar measure `dt / t` (`TauCeti.multHaar`) satisfy the weighted Hardy inequalities

`‖t ↦ t ^ (-θ) ∫₀ᵗ f(s) ds / s‖_{L^q(dt / t)} ≤ θ⁻¹ ‖t ↦ t ^ (-θ) f(t)‖_{L^q(dt / t)}`,
`‖t ↦ t ^ θ ∫_t^∞ f(s) ds / s‖_{L^q(dt / t)} ≤ θ⁻¹ ‖t ↦ t ^ θ f(t)‖_{L^q(dt / t)}`,

with the sharp constant `θ⁻¹` (`TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Iic_multHaar_le` and
`TauCeti.eLpNorm_rpow_mul_setLIntegral_Ici_multHaar_le`). Rewriting `ds / s` in terms of Lebesgue
measure yields the standard weighted forms for Lebesgue integrals over `(0, t]` and `(t, ∞)`
(`TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_multHaar_le`,
`TauCeti.eLpNorm_rpow_mul_setLIntegral_Ioi_multHaar_le`), and specializing to `q = p` via
`TauCeti.eLpNorm_ofReal_rpow_inv_mul_multHaar` gives the classical Hardy inequalities on `(0, ∞)`

`‖t ↦ t⁻¹ ∫₀ᵗ f‖_{L^p(0, ∞)} ≤ (1 - 1 / p)⁻¹ ‖f‖_{L^p(0, ∞)}` (`1 < p ≤ ∞`),
`‖t ↦ ∫_t^∞ s⁻¹ f(s) ds‖_{L^p(0, ∞)} ≤ p ‖f‖_{L^p(0, ∞)}` (`1 ≤ p < ∞`)

(`TauCeti.eLpNorm_inv_mul_setLIntegral_Ioc_le`, `TauCeti.eLpNorm_setLIntegral_Ioi_inv_mul_le`).

## Proof method

The forward inequality on `dt / t` is Schur's test (`TauCeti.eLpNorm_lintegral_mul_le`) for the
homogeneous kernel `k(t, s) = 1_{(0, t]}(s) (s / t) ^ θ` on `(multHaar, multHaar)`. By dilation
invariance (`TauCeti.map_multHaar_mul_left`) and the exponential change of variable
(`TauCeti.map_volume_exp`), every row integral and every column integral of `k` equals `θ⁻¹`, so
Schur's test gives the constant `(θ⁻¹) ^ (1 - 1 / q) (θ⁻¹) ^ (1 / q) = θ⁻¹` uniformly across
`1 ≤ q ≤ ∞`. The backward inequality follows by inversion invariance (`TauCeti.map_multHaar_inv`).

No measurability hypothesis on `f` is required: when the right-hand integrand is not almost
everywhere strongly measurable its `L^q` seminorm is `∞` by convention, and the bound holds
trivially.

## Main declarations

* `TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Iic_multHaar_le`: forward weighted Hardy inequality
  on `dt / t`.
* `TauCeti.eLpNorm_rpow_mul_setLIntegral_Ici_multHaar_le`: backward weighted Hardy inequality on
  `dt / t`.
* `TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_multHaar_le`: forward weighted Hardy inequality
  for Lebesgue integrals over `(0, t]` in `L^q(dt / t)`.
* `TauCeti.eLpNorm_rpow_mul_setLIntegral_Ioi_multHaar_le`: backward weighted Hardy inequality for
  Lebesgue integrals over `(t, ∞)` in `L^q(dt / t)`.
* `TauCeti.eLpNorm_inv_mul_setLIntegral_Ioc_le`: classical Hardy's inequality on `(0, ∞)` for
  `1 < p ≤ ∞`.
* `TauCeti.eLpNorm_setLIntegral_Ioi_inv_mul_le`: classical dual Hardy's inequality on `(0, ∞)` for
  `1 ≤ p < ∞`.

## References

* G. H. Hardy, *Note on a theorem of Hilbert*, Math. Z. **6** (1920), 314–317.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §1.3 and §5.2.
* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Chapter V,
  §3 (Lemma 3.14).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- The homogeneous Hardy kernel `k(t, s) = 1_{(0, t]}(s) (s / t) ^ θ`. -/
private noncomputable def hardyKernel (θ t s : ℝ) : ℝ≥0∞ :=
  (Ioc 0 t).indicator (fun s ↦ ENNReal.ofReal ((s / t) ^ θ)) s

private theorem measurable_hardyKernel (θ : ℝ) :
    Measurable (Function.uncurry (hardyKernel θ)) := by
  have hset : MeasurableSet {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hfun : Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal ((p.2 / p.1) ^ θ) := by fun_prop
  exact hfun.indicator hset

/-- Every row integral of `hardyKernel θ` against `dt / t` for `t > 0` equals `θ⁻¹`. -/
private theorem lintegral_hardyKernel_right {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t) :
    ∫⁻ s, hardyKernel θ t s ∂multHaar = ENNReal.ofReal θ⁻¹ := by
  have hmp : MeasurePreserving (t * ·) multHaar multHaar :=
    ⟨measurable_const_mul t, map_multHaar_mul_left ht⟩
  have hmeas : Measurable (hardyKernel θ t) :=
    (measurable_hardyKernel θ).comp measurable_prodMk_left
  rw [← hmp.lintegral_comp hmeas, ← map_volume_exp,
    lintegral_map (f := fun u ↦ hardyKernel θ t (t * u))
      (hmeas.comp (measurable_const_mul t)) Real.measurable_exp,
    ← lintegral_Iic_ofReal_exp_mul hθ, ← lintegral_indicator measurableSet_Iic]
  refine lintegral_congr fun x ↦ ?_
  have hexp : 0 < Real.exp x := Real.exp_pos x
  have hmem : t * Real.exp x ∈ Ioc 0 t ↔ x ∈ Iic 0 := by
    simp only [mem_Ioc, mem_Iic, mul_pos_iff_of_pos_left ht, hexp, true_and,
      mul_le_iff_le_one_right ht, Real.exp_le_one_iff]
  by_cases hx : x ∈ Iic (0 : ℝ)
  · simp only [hardyKernel, indicator_of_mem (hmem.2 hx), indicator_of_mem hx,
      mul_div_cancel_left₀ _ ht.ne', ← Real.exp_mul, mul_comm]
  · simp only [hardyKernel, indicator_of_notMem (mt hmem.1 hx), indicator_of_notMem hx]

/-- Every column integral of `hardyKernel θ` against `dt / t` for `s > 0` equals `θ⁻¹`. -/
private theorem lintegral_hardyKernel_left {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s) :
    ∫⁻ t, hardyKernel θ t s ∂multHaar = ENNReal.ofReal θ⁻¹ := by
  have hmp : MeasurePreserving (s * ·) multHaar multHaar :=
    ⟨measurable_const_mul s, map_multHaar_mul_left hs⟩
  have hmeas : Measurable fun t ↦ hardyKernel θ t s :=
    (measurable_hardyKernel θ).comp measurable_prodMk_right
  rw [← hmp.lintegral_comp hmeas, ← map_volume_exp,
    lintegral_map (f := fun v ↦ hardyKernel θ (s * v) s)
      (hmeas.comp (measurable_const_mul s)) Real.measurable_exp,
    ← lintegral_Ioi_ofReal_exp_neg_mul hθ, Measure.restrict_congr_set Ioi_ae_eq_Ici,
    ← lintegral_indicator measurableSet_Ici]
  refine lintegral_congr fun x ↦ ?_
  have hmem : s ∈ Ioc 0 (s * Real.exp x) ↔ x ∈ Ici 0 := by
    simp only [mem_Ioc, mem_Ici, hs, true_and, le_mul_iff_one_le_right hs, Real.one_le_exp_iff]
  by_cases hx : x ∈ Ici (0 : ℝ)
  · simp only [hardyKernel, indicator_of_mem (hmem.2 hx), indicator_of_mem hx,
      div_mul_cancel_left₀ hs.ne', ← Real.exp_neg, ← Real.exp_mul]
    ring_nf
  · simp only [hardyKernel, indicator_of_notMem (mt hmem.1 hx), indicator_of_notMem hx]

/-- For `t > 0`, the weighted average `t ^ (-θ) ∫₀ᵗ f(s) ds / s` is the integral operator with
kernel `hardyKernel θ` applied to `s ↦ s ^ (-θ) f(s)`. -/
private theorem ofReal_rpow_neg_mul_setLIntegral_Iic_eq_hardyKernel (f : ℝ → ℝ≥0∞) (θ : ℝ)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Iic t, f s ∂multHaar =
      ∫⁻ s, hardyKernel θ t s * (ENNReal.ofReal (s ^ (-θ)) * f s) ∂multHaar := by
  have hset : Iic t =ᵐ[multHaar] Ioc 0 t := by
    filter_upwards [ae_pos_multHaar] with s hs
    simp [hs]
  rw [Measure.restrict_congr_set hset, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator measurableSet_Ioc]
  refine lintegral_congr fun s ↦ ?_
  by_cases hs : s ∈ Ioc 0 t
  · simp only [indicator_of_mem hs, hardyKernel]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (div_nonneg hs.1.le ht.le) _)]
    congr 2
    symm
    calc (s / t) ^ θ * s ^ (-θ)
        = (s ^ θ * s ^ (-θ)) * t ^ (-θ) := by
          rw [Real.div_rpow hs.1.le ht.le, div_eq_mul_inv, Real.rpow_neg ht.le]
          ring
      _ = t ^ (-θ) := by rw [← Real.rpow_add hs.1, add_neg_cancel, Real.rpow_zero, one_mul]
  · simp [hardyKernel, indicator_of_notMem hs]

/-- **Forward weighted Hardy inequality on `dt / t`.** For `θ > 0` and `1 ≤ q ≤ ∞`,
`‖t ↦ t ^ (-θ) ∫₀ᵗ f(s) ds / s‖_{L^q(dt / t)} ≤ θ⁻¹ ‖t ↦ t ^ (-θ) f(t)‖_{L^q(dt / t)}`. -/
theorem eLpNorm_rpow_neg_mul_setLIntegral_Iic_multHaar_le {f : ℝ → ℝ≥0∞} {θ : ℝ} (hθ : 0 < θ)
    {q : ℝ≥0∞} (hq : 1 ≤ q) :
    eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Iic t, f s ∂multHaar) q multHaar ≤
      ENNReal.ofReal θ⁻¹ *
        eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * f t) q multHaar := by
  set g : ℝ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (s ^ (-θ)) * f s
  by_cases hg : AEStronglyMeasurable g multHaar
  · have hcongr :
        (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Iic t, f s ∂multHaar) =ᵐ[multHaar]
          fun t : ℝ ↦ ∫⁻ s, hardyKernel θ t s * g s ∂multHaar :=
      ae_pos_multHaar.mono fun t ht ↦ ofReal_rpow_neg_mul_setLIntegral_Iic_eq_hardyKernel f θ ht
    have hrow : ∀ᵐ t ∂multHaar, ∫⁻ s, hardyKernel θ t s ∂multHaar ≤ ENNReal.ofReal θ⁻¹ :=
      ae_pos_multHaar.mono fun t ht ↦ (lintegral_hardyKernel_right hθ ht).le
    have hcol : ∀ᵐ s ∂multHaar, ∫⁻ t, hardyKernel θ t s ∂multHaar ≤ ENNReal.ofReal θ⁻¹ :=
      ae_pos_multHaar.mono fun s hs ↦ (lintegral_hardyKernel_left hθ hs).le
    calc eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Iic t, f s ∂multHaar) q multHaar
        = eLpNorm (fun t : ℝ ↦ ∫⁻ s, hardyKernel θ t s * g s ∂multHaar) q multHaar :=
          eLpNorm_congr_ae hcongr
      _ ≤ ENNReal.ofReal θ⁻¹ ^ (1 - q.toReal⁻¹) * ENNReal.ofReal θ⁻¹ ^ q.toReal⁻¹ *
            eLpNorm g q multHaar :=
          eLpNorm_lintegral_mul_le (measurable_hardyKernel θ).aemeasurable hg.aemeasurable hq
            hrow hcol
      _ = ENNReal.ofReal θ⁻¹ * eLpNorm g q multHaar := by
          rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.2 (inv_pos.2 hθ)).ne'
            ENNReal.ofReal_ne_top, sub_add_cancel, ENNReal.rpow_one]
  · rw [eLpNorm_of_not_aestronglyMeasurable hg,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 (inv_pos.2 hθ)).ne']
    exact le_top

/-- Inversion preserves `L^q(dt / t)` seminorms without measurability hypotheses. -/
private theorem eLpNorm_comp_inv_multHaar (g : ℝ → ℝ≥0∞) (q : ℝ≥0∞) :
    eLpNorm (g ∘ Inv.inv) q multHaar = eLpNorm g q multHaar := by
  have hmp : MeasurePreserving Inv.inv multHaar multHaar := ⟨measurable_inv, map_multHaar_inv⟩
  by_cases hg : AEStronglyMeasurable g multHaar
  · exact eLpNorm_comp_measurePreserving hg hmp
  · have hgi : ¬ AEStronglyMeasurable (g ∘ Inv.inv) multHaar := fun h ↦ hg <| by
      exact (h.comp_measurePreserving hmp).congr (ae_of_all _ fun t ↦ by simp [Function.comp_apply])
    rw [eLpNorm_of_not_aestronglyMeasurable hgi, eLpNorm_of_not_aestronglyMeasurable hg]

/-- Inversion exchanges `dt / t`-integrals over `(-∞, t]` and `[t⁻¹, ∞)` for `t > 0`. -/
private theorem setLIntegral_Iic_comp_inv_multHaar (f : ℝ → ℝ≥0∞) {t : ℝ} (ht : 0 < t) :
    ∫⁻ s in Iic t, f s⁻¹ ∂multHaar = ∫⁻ s in Ici t⁻¹, f s ∂multHaar := by
  have hmp : MeasurePreserving Inv.inv multHaar multHaar := ⟨measurable_inv, map_multHaar_inv⟩
  have hemb : MeasurableEmbedding (Inv.inv : ℝ → ℝ) :=
    ⟨inv_injective, measurable_inv, fun _ hs ↦ by
      rw [Set.image_eq_preimage_of_inverse inv_inv inv_inv]
      exact measurable_inv hs⟩
  rw [← lintegral_indicator measurableSet_Iic, ← lintegral_indicator measurableSet_Ici,
    ← hmp.lintegral_comp_emb hemb]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_pos_multHaar] with s hs
  have hmem : s⁻¹ ∈ Iic t ↔ s ∈ Ici t⁻¹ := by
    simp only [mem_Iic, mem_Ici, inv_le_comm₀ hs ht]
  by_cases hst : s⁻¹ ∈ Iic t
  · simp only [indicator_of_mem hst, indicator_of_mem (hmem.1 hst), inv_inv]
  · simp only [indicator_of_notMem hst, indicator_of_notMem (mt hmem.2 hst)]

/-- **Backward weighted Hardy inequality on `dt / t`.** For `θ > 0` and `1 ≤ q ≤ ∞`,
`‖t ↦ t ^ θ ∫_t^∞ f(s) ds / s‖_{L^q(dt / t)} ≤ θ⁻¹ ‖t ↦ t ^ θ f(t)‖_{L^q(dt / t)}`. -/
theorem eLpNorm_rpow_mul_setLIntegral_Ici_multHaar_le {f : ℝ → ℝ≥0∞} {θ : ℝ} (hθ : 0 < θ)
    {q : ℝ≥0∞} (hq : 1 ≤ q) :
    eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ici t, f s ∂multHaar) q multHaar ≤
      ENNReal.ofReal θ⁻¹ *
        eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * f t) q multHaar := by
  have hL : (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Iic t, f s⁻¹ ∂multHaar) =ᵐ[multHaar]
      (fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ici t, f s ∂multHaar) ∘ Inv.inv := by
    filter_upwards [ae_pos_multHaar] with t ht
    simp only [Function.comp_apply, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
    rw [setLIntegral_Iic_comp_inv_multHaar f ht]
  have hR : (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * f t⁻¹) =ᵐ[multHaar]
      (fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * f t) ∘ Inv.inv := by
    filter_upwards [ae_pos_multHaar] with t ht
    simp [Function.comp_apply, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le]
  calc eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ici t, f s ∂multHaar) q multHaar
      = eLpNorm ((fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ici t, f s ∂multHaar) ∘ Inv.inv)
          q multHaar := (eLpNorm_comp_inv_multHaar _ q).symm
    _ = eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Iic t, f s⁻¹ ∂multHaar)
          q multHaar := (eLpNorm_congr_ae hL).symm
    _ ≤ ENNReal.ofReal θ⁻¹ *
          eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * f t⁻¹) q multHaar :=
        eLpNorm_rpow_neg_mul_setLIntegral_Iic_multHaar_le hθ hq
    _ = ENNReal.ofReal θ⁻¹ *
          eLpNorm ((fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * f t) ∘ Inv.inv) q multHaar := by
        rw [eLpNorm_congr_ae hR]
    _ = ENNReal.ofReal θ⁻¹ * eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * f t) q multHaar := by
        rw [eLpNorm_comp_inv_multHaar]

/-- **Forward weighted Hardy inequality for Lebesgue integrals in `L^q(dt / t)`.** For `θ > 0` and
`1 ≤ q ≤ ∞`, `‖t ↦ t ^ (-θ) ∫₀ᵗ f(s) ds‖_{L^q(dt / t)} ≤ θ⁻¹ ‖t ↦ t ^ (1 - θ) f(t)‖_{L^q(dt / t)}`.
-/
theorem eLpNorm_rpow_neg_mul_setLIntegral_Ioc_multHaar_le {f : ℝ → ℝ≥0∞} {θ : ℝ} (hθ : 0 < θ)
    {q : ℝ≥0∞} (hq : 1 ≤ q) :
    eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, f s) q multHaar ≤
      ENNReal.ofReal θ⁻¹ *
        eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 - θ)) * f t) q multHaar := by
  have hL : (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, f s) =ᵐ[multHaar]
      fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) *
        ∫⁻ s in Iic t, (ENNReal.ofReal s * f s) ∂multHaar := by
    filter_upwards [ae_pos_multHaar] with t _
    congr 1
    rw [setLIntegral_multHaar_eq_setLIntegral _ measurableSet_Iic, inter_comm, Ioi_inter_Iic]
    refine (setLIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_).symm
    rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hs.1.le), inv_mul_cancel₀ hs.1.ne',
      ENNReal.ofReal_one, one_mul]
  have hR : (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * (ENNReal.ofReal t * f t)) =ᵐ[multHaar]
      fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 - θ)) * f t := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
      ← Real.rpow_add_one ht.ne', neg_add_eq_sub]
  rw [eLpNorm_congr_ae hL, ← eLpNorm_congr_ae hR]
  exact eLpNorm_rpow_neg_mul_setLIntegral_Iic_multHaar_le hθ hq

/-- **Backward weighted Hardy inequality for Lebesgue integrals in `L^q(dt / t)`.** For `θ > 0` and
`1 ≤ q ≤ ∞`,
`‖t ↦ t ^ θ ∫_t^∞ f(s) ds‖_{L^q(dt / t)} ≤ θ⁻¹ ‖t ↦ t ^ (1 + θ) f(t)‖_{L^q(dt / t)}`. -/
theorem eLpNorm_rpow_mul_setLIntegral_Ioi_multHaar_le {f : ℝ → ℝ≥0∞} {θ : ℝ} (hθ : 0 < θ)
    {q : ℝ≥0∞} (hq : 1 ≤ q) :
    eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ioi t, f s) q multHaar ≤
      ENNReal.ofReal θ⁻¹ *
        eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 + θ)) * f t) q multHaar := by
  have hL : (fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ioi t, f s) =ᵐ[multHaar]
      fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) *
        ∫⁻ s in Ici t, (ENNReal.ofReal s * f s) ∂multHaar := by
    filter_upwards [ae_pos_multHaar] with t ht
    congr 1
    rw [setLIntegral_multHaar_eq_setLIntegral _ measurableSet_Ici,
      inter_eq_left.2 (Ici_subset_Ioi.2 ht), Measure.restrict_congr_set Ioi_ae_eq_Ici]
    refine (setLIntegral_congr_fun measurableSet_Ici fun s hs ↦ ?_).symm
    have hs0 : 0 < s := ht.trans_le hs
    rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hs0.le), inv_mul_cancel₀ hs0.ne',
      ENNReal.ofReal_one, one_mul]
  have hR : (fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * (ENNReal.ofReal t * f t)) =ᵐ[multHaar]
      fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 + θ)) * f t := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
      ← Real.rpow_add_one ht.ne', add_comm]
  rw [eLpNorm_congr_ae hL, ← eLpNorm_congr_ae hR]
  exact eLpNorm_rpow_mul_setLIntegral_Ici_multHaar_le hθ hq

/-- **Hardy's inequality on `(0, ∞)`.** For `1 < p ≤ ∞`,
`‖t ↦ t⁻¹ ∫₀ᵗ f‖_{L^p(0, ∞)} ≤ (1 - 1 / p)⁻¹ ‖f‖_{L^p(0, ∞)}`. For finite `p`, the constant is
the sharp constant `p / (p - 1)`; for `p = ∞`, it is `1`. -/
theorem eLpNorm_inv_mul_setLIntegral_Ioc_le {f : ℝ → ℝ≥0∞} {p : ℝ≥0∞} (hp : 1 < p) :
    eLpNorm (fun t : ℝ ↦ ENNReal.ofReal t⁻¹ * ∫⁻ s in Ioc 0 t, f s) p (volume.restrict (Ioi 0)) ≤
      ENNReal.ofReal (1 - p.toReal⁻¹)⁻¹ * eLpNorm f p (volume.restrict (Ioi 0)) := by
  have hθ : 0 < 1 - p.toReal⁻¹ := by
    rcases eq_or_ne p ∞ with rfl | hp_top
    · simp
    · have h1p : (1 : ℝ) < p.toReal := by
        simpa using ENNReal.toReal_strict_mono hp_top hp
      exact sub_pos.2 (inv_lt_one_of_one_lt₀ h1p)
  rw [← eLpNorm_ofReal_rpow_inv_mul_multHaar _ p, ← eLpNorm_ofReal_rpow_inv_mul_multHaar f p]
  have hL : (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) *
        (ENNReal.ofReal t⁻¹ * ∫⁻ s in Ioc 0 t, f s)) =ᵐ[multHaar]
      fun t : ℝ ↦ ENNReal.ofReal (t ^ (-(1 - p.toReal⁻¹))) * ∫⁻ s in Ioc 0 t, f s := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
      ← Real.rpow_neg_one t, ← Real.rpow_add ht, neg_sub, sub_eq_add_neg]
  rw [eLpNorm_congr_ae hL]
  simpa only [sub_sub_cancel] using
    eLpNorm_rpow_neg_mul_setLIntegral_Ioc_multHaar_le (f := f) hθ hp.le

/-- **Dual Hardy's inequality on `(0, ∞)`.** For `1 ≤ p < ∞`,
`‖t ↦ ∫_t^∞ s⁻¹ f(s) ds‖_{L^p(0, ∞)} ≤ p ‖f‖_{L^p(0, ∞)}`. -/
theorem eLpNorm_setLIntegral_Ioi_inv_mul_le {f : ℝ → ℝ≥0∞} {p : ℝ≥0∞} (hp₁ : 1 ≤ p)
    (hp_top : p ≠ ∞) :
    eLpNorm (fun t : ℝ ↦ ∫⁻ s in Ioi t, ENNReal.ofReal s⁻¹ * f s) p (volume.restrict (Ioi 0)) ≤
      p * eLpNorm f p (volume.restrict (Ioi 0)) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp₁).ne'
  have hθ : 0 < p.toReal⁻¹ := inv_pos.2 (ENNReal.toReal_pos hp0 hp_top)
  rw [← eLpNorm_ofReal_rpow_inv_mul_multHaar _ p, ← eLpNorm_ofReal_rpow_inv_mul_multHaar f p]
  have hR : (fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 + p.toReal⁻¹)) *
        (ENNReal.ofReal t⁻¹ * f t)) =ᵐ[multHaar]
      fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * f t := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
      Real.rpow_add ht, Real.rpow_one, mul_right_comm, mul_inv_cancel₀ ht.ne', one_mul]
  simpa only [inv_inv, ENNReal.ofReal_toReal hp_top, eLpNorm_congr_ae hR] using
    eLpNorm_rpow_mul_setLIntegral_Ioi_multHaar_le (f := fun s ↦ ENNReal.ofReal s⁻¹ * f s) hθ hp₁

end TauCeti

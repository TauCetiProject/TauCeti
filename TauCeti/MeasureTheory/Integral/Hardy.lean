/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import TauCeti.MeasureTheory.Measure.Haar.MultHaar
-- `Mathlib.MeasureTheory.Function.SpecialFunctions.Basic` is imported privately: it supplies Borel
-- measurability of real powers and products in `ℝ≥0∞`.
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
-- `TauCeti.Analysis.SpecialFunctions.Pow.Integral` is imported privately: it supplies the half-line
-- power integrals bounding the row and column integrals of the Hardy kernel.
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
-- `TauCeti.MeasureTheory.Integral.SchurTest` is imported privately: it supplies Schur's test in
-- `L^q` form, from which all forms of Hardy's inequality below are deduced.
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Hardy's inequalities on the positive half-line

For `θ > 0` and `1 ≤ q ≤ ∞`, the two averaging operators on `(0, ∞)` with respect to the
multiplicative Haar measure `dt / t` (`TauCeti.multHaar`) satisfy the weighted Hardy inequalities

* `‖t ↦ t ^ (-θ) ∫_{0 < s ≤ t} g(s) ds / s‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ (-θ) g(s)‖_{L^q(ds / s)}`
  (`TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_multHaar_le`),
* `‖t ↦ t ^ θ ∫_{s > t} g(s) ds / s‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ θ g(s)‖_{L^q(ds / s)}`
  (`TauCeti.eLpNorm_rpow_mul_setLIntegral_Ioi_multHaar_le`).

Absorbing the Jacobian `s` between Lebesgue measure and `ds / s` gives the forms for Lebesgue
lower integrals over `(0, t]` and `(t, ∞)`:

* `‖t ↦ t ^ (-θ) ∫₀ᵗ g‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ (1 - θ) g(s)‖_{L^q(ds / s)}`
  (`TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le`),
* `‖t ↦ t ^ θ ∫_t^∞ g‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ (1 + θ) g(s)‖_{L^q(ds / s)}`
  (`TauCeti.eLpNorm_rpow_mul_setLIntegral_Ioi_le`).

The first of these bounds the `K`-method norm of `(L¹, L^∞)` by the Lorentz seminorm when
`g = ‖f‖*`; specializing to `θ = 1 - 1 / p` and `q = p` yields Hardy's classical `L^p(0, ∞)`
inequality with the constant `(1 - 1 / p)⁻¹ = p / (p - 1)` for `1 < p ≤ ∞`
(`TauCeti.eLpNorm_setLIntegral_Ioc_div_le`).

All statements are formulated for arbitrary `g : ℝ → ℝ≥0∞` without measurability hypotheses: when
the weighted integrand on the right fails to be almost everywhere strongly measurable, its `eLpNorm`
is `∞` and `θ⁻¹ * ∞ = ∞`. When it is measurable, the inequalities reduce to Schur's test
(`TauCeti.eLpNorm_lintegral_mul_le`) for the homogeneous kernel `k(t, s) = [0 < s < t] (s / t) ^ θ`
and its transpose on `dt / t`, whose row and column integrals both equal `θ⁻¹`.

## References

* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, 2nd ed., Cambridge University Press,
  1952, §9.8–9.9 (Theorems 327 and 330).
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §3.4 (Lemma 3.4.3) and §5.2 (Theorem 5.2.1).
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

/-- The homogeneous kernel `[0 < s < t] * (s / t) ^ θ` used to deduce Hardy's inequalities from
Schur's test on `dt / t`. -/
private noncomputable def hardyKernel (θ : ℝ) (t s : ℝ) : ℝ≥0∞ :=
  {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}.indicator
    (fun p ↦ ENNReal.ofReal ((p.2 / p.1) ^ θ)) (t, s)

private theorem measurable_uncurry_hardyKernel (θ : ℝ) :
    Measurable (Function.uncurry (hardyKernel θ)) :=
  (ENNReal.measurable_ofReal.comp ((measurable_snd.div measurable_fst).pow_const θ)).indicator
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst))

private theorem hardyKernel_eq_indicator_Ioo (θ : ℝ) (t s : ℝ) :
    hardyKernel θ t s = (Ioo 0 t).indicator (fun u ↦ ENNReal.ofReal ((u / t) ^ θ)) s := by
  simp [hardyKernel, indicator_apply]

private theorem hardyKernel_swap_eq_indicator_Ioi (θ : ℝ) {t : ℝ} (ht : 0 < t) (s : ℝ) :
    hardyKernel θ s t = (Ioi t).indicator (fun u ↦ ENNReal.ofReal ((t / u) ^ θ)) s := by
  simp [hardyKernel, indicator_apply, ht]

/-- Each row integral `∫_{0 < s < t} (s / t) ^ θ ds / s` of `hardyKernel θ` equals `θ⁻¹`. -/
private theorem lintegral_hardyKernel_right {θ : ℝ} (hθ : 0 < θ) {t : ℝ} (ht : 0 < t) :
    ∫⁻ s, hardyKernel θ t s ∂multHaar = ENNReal.ofReal θ⁻¹ := by
  simp_rw [hardyKernel_eq_indicator_Ioo]
  rw [lintegral_multHaar]
  have hind : ∀ s, ENNReal.ofReal s⁻¹ *
      (Ioo 0 t).indicator (fun u ↦ ENNReal.ofReal ((u / t) ^ θ)) s =
        (Ioo 0 t).indicator (fun u ↦ ENNReal.ofReal u⁻¹ * ENNReal.ofReal ((u / t) ^ θ)) s := by
    intro s
    by_cases hs : s ∈ Ioo 0 t <;> simp [hs]
  have hcongr : ∀ s ∈ Ioo 0 t,
      ENNReal.ofReal s⁻¹ * ENNReal.ofReal ((s / t) ^ θ) =
        ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal (s ^ (θ - 1)) := fun s ⟨hs, _⟩ ↦ by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      Real.div_rpow hs.le ht.le, Real.rpow_neg ht.le, Real.rpow_sub hs, Real.rpow_one]
    field_simp
  simp_rw [hind]
  rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_self_of_subset_left Ioo_subset_Ioi_self,
    setLIntegral_congr_fun measurableSet_Ioo hcongr,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_ofReal_rpow_Ioo (by linarith) ht.le, sub_add_cancel,
    ← ENNReal.ofReal_mul (by positivity), div_eq_mul_inv, ← mul_assoc,
    ← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero, one_mul]

/-- Each column integral `∫_{t > s} (s / t) ^ θ dt / t` of `hardyKernel θ` equals `θ⁻¹`. -/
private theorem lintegral_hardyKernel_left {θ : ℝ} (hθ : 0 < θ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ t, hardyKernel θ t s ∂multHaar = ENNReal.ofReal θ⁻¹ := by
  simp_rw [hardyKernel_swap_eq_indicator_Ioi θ hs]
  rw [lintegral_multHaar]
  have hind : ∀ t, ENNReal.ofReal t⁻¹ *
      (Ioi s).indicator (fun u ↦ ENNReal.ofReal ((s / u) ^ θ)) t =
        (Ioi s).indicator (fun u ↦ ENNReal.ofReal u⁻¹ * ENNReal.ofReal ((s / u) ^ θ)) t := by
    intro t
    by_cases ht : t ∈ Ioi s <;> simp [ht]
  have hcongr : ∀ t ∈ Ioi s,
      ENNReal.ofReal t⁻¹ * ENNReal.ofReal ((s / t) ^ θ) =
        ENNReal.ofReal (s ^ θ) * ENNReal.ofReal (t ^ (-θ - 1)) := fun t (ht : s < t) ↦ by
    have ht0 : 0 < t := hs.trans ht
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      Real.div_rpow hs.le ht0.le, sub_eq_add_neg, Real.rpow_add ht0, Real.rpow_neg ht0.le,
      Real.rpow_neg_one]
    field_simp
  simp_rw [hind]
  rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_self_of_subset_left (Ioi_subset_Ioi hs.le),
    setLIntegral_congr_fun measurableSet_Ioi hcongr,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_ofReal_rpow_Ioi_of_lt (by linarith) hs, sub_add_cancel,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [neg_div_neg_eq, div_eq_mul_inv, ← mul_assoc, ← Real.rpow_add hs, add_neg_cancel,
    Real.rpow_zero, one_mul]

/-- The Schur constant `A ^ (1 - 1 / q) * A ^ (1 / q)` simplifies to `A` when `1 ≤ q`. -/
private theorem schur_const_self {q : ℝ≥0∞} (hq : 1 ≤ q) (A : ℝ≥0∞) :
    A ^ (1 - q.toReal⁻¹) * A ^ q.toReal⁻¹ = A := by
  have h0 : 0 ≤ 1 - q.toReal⁻¹ := by
    rcases eq_or_ne q ∞ with rfl | hq_top
    · simp
    · exact sub_nonneg.2 (inv_le_one_of_one_le₀ (by simpa using ENNReal.toReal_mono hq_top hq))
  rw [← ENNReal.rpow_add_of_nonneg _ _ h0 (inv_nonneg.2 ENNReal.toReal_nonneg), sub_add_cancel,
    ENNReal.rpow_one]

/-- **Weighted Hardy inequality** on `dt / t` near `0`: for `θ > 0` and `1 ≤ q ≤ ∞`,
`‖t ↦ t ^ (-θ) ∫_{0 < s ≤ t} g(s) ds / s‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ (-θ) g(s)‖_{L^q(ds / s)}`. -/
theorem eLpNorm_rpow_neg_mul_setLIntegral_Ioc_multHaar_le {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (g : ℝ → ℝ≥0∞) :
    eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s ∂multHaar) q multHaar ≤
      ENNReal.ofReal θ⁻¹ * eLpNorm (fun s : ℝ ↦ ENNReal.ofReal (s ^ (-θ)) * g s) q multHaar := by
  set G : ℝ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (s ^ (-θ)) * g s
  by_cases hG : AEStronglyMeasurable G multHaar
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hG,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 (inv_pos.2 hθ)).ne']
    exact le_top
  have hae : (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s ∂multHaar) =ᵐ[multHaar]
      fun t ↦ ∫⁻ s, hardyKernel θ t s * G s ∂multHaar := by
    filter_upwards [ae_pos_multHaar] with t ht
    have hIoo : multHaar.restrict (Ioo 0 t) = multHaar.restrict (Ioc 0 t) :=
      Measure.restrict_congr_set (ae_multHaar ▸ ae_restrict_of_ae Ioo_ae_eq_Ioc)
    simp_rw [hardyKernel_eq_indicator_Ioo]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hIoo,
      ← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun s ↦ ?_
    by_cases hs : s ∈ Ioo 0 t
    · have hst : 0 ≤ (s / t) ^ θ := Real.rpow_nonneg (div_nonneg hs.1.le ht.le) θ
      rw [indicator_of_mem hs, indicator_of_mem hs, ← mul_assoc,
        ← ENNReal.ofReal_mul hst, Real.div_rpow hs.1.le ht.le, Real.rpow_neg hs.1.le,
        div_mul_eq_mul_div, mul_inv_cancel₀ (Real.rpow_pos_of_pos hs.1 θ).ne', one_div,
        ← Real.rpow_neg ht.le]
    · simp [hs]
  rw [eLpNorm_congr_ae hae, ← schur_const_self hq (ENNReal.ofReal θ⁻¹)]
  exact eLpNorm_lintegral_mul_le (measurable_uncurry_hardyKernel θ).aemeasurable hG.aemeasurable hq
    (ae_pos_multHaar.mono fun _ ht ↦ (lintegral_hardyKernel_right hθ ht).le)
    (ae_pos_multHaar.mono fun _ hs ↦ (lintegral_hardyKernel_left hθ hs).le)

/-- **Weighted Hardy inequality** near `0` for Lebesgue lower integrals: for `θ > 0` and
`1 ≤ q ≤ ∞`,
`‖t ↦ t ^ (-θ) ∫₀ᵗ g‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ (1 - θ) g(s)‖_{L^q(ds / s)}`. -/
theorem eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (g : ℝ → ℝ≥0∞) :
    eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s) q multHaar ≤
      ENNReal.ofReal θ⁻¹ *
        eLpNorm (fun s : ℝ ↦ ENNReal.ofReal (s ^ (1 - θ)) * g s) q multHaar := by
  have h := eLpNorm_rpow_neg_mul_setLIntegral_Ioc_multHaar_le hθ hq fun s ↦ ENNReal.ofReal s * g s
  simp_rw [← setLIntegral_eq_setLIntegral_multHaar g Ioc_subset_Ioi_self] at h
  have hR : (fun s : ℝ ↦ ENNReal.ofReal (s ^ (-θ)) * (ENNReal.ofReal s * g s)) =ᵐ[multHaar]
      fun s ↦ ENNReal.ofReal (s ^ (1 - θ)) * g s := by
    filter_upwards [ae_pos_multHaar] with s hs
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add_one hs.ne',
      show -θ + 1 = 1 - θ by ring]
  rwa [eLpNorm_congr_ae hR] at h

/-- **Weighted Hardy inequality** on `dt / t` at `∞`: for `θ > 0` and `1 ≤ q ≤ ∞`,
`‖t ↦ t ^ θ ∫_{s > t} g(s) ds / s‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ θ g(s)‖_{L^q(ds / s)}`. -/
theorem eLpNorm_rpow_mul_setLIntegral_Ioi_multHaar_le {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (g : ℝ → ℝ≥0∞) :
    eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ioi t, g s ∂multHaar) q multHaar ≤
      ENNReal.ofReal θ⁻¹ * eLpNorm (fun s : ℝ ↦ ENNReal.ofReal (s ^ θ) * g s) q multHaar := by
  set G : ℝ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (s ^ θ) * g s
  by_cases hG : AEStronglyMeasurable G multHaar
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hG,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 (inv_pos.2 hθ)).ne']
    exact le_top
  have hae : (fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ioi t, g s ∂multHaar) =ᵐ[multHaar]
      fun t ↦ ∫⁻ s, hardyKernel θ s t * G s ∂multHaar := by
    filter_upwards [ae_pos_multHaar] with t ht
    simp_rw [hardyKernel_swap_eq_indicator_Ioi θ ht]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun s ↦ ?_
    by_cases hs : s ∈ Ioi t
    · have hs0 : 0 < s := ht.trans hs
      have hts : 0 ≤ (t / s) ^ θ := Real.rpow_nonneg (div_nonneg ht.le hs0.le) θ
      rw [indicator_of_mem hs, indicator_of_mem hs, ← mul_assoc,
        ← ENNReal.ofReal_mul hts, Real.div_rpow ht.le hs0.le,
        div_mul_cancel₀ _ (Real.rpow_pos_of_pos hs0 θ).ne']
    · simp [hs]
  have hk : Measurable (Function.uncurry fun t s ↦ hardyKernel θ s t) :=
    (measurable_uncurry_hardyKernel θ).comp measurable_swap
  rw [eLpNorm_congr_ae hae, ← schur_const_self hq (ENNReal.ofReal θ⁻¹)]
  exact eLpNorm_lintegral_mul_le hk.aemeasurable hG.aemeasurable hq
    (ae_pos_multHaar.mono fun _ ht ↦ (lintegral_hardyKernel_left hθ ht).le)
    (ae_pos_multHaar.mono fun _ hs ↦ (lintegral_hardyKernel_right hθ hs).le)

/-- **Weighted Hardy inequality** at `∞` for Lebesgue lower integrals: for `θ > 0` and
`1 ≤ q ≤ ∞`,
`‖t ↦ t ^ θ ∫_t^∞ g‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ (1 + θ) g(s)‖_{L^q(ds / s)}`. -/
theorem eLpNorm_rpow_mul_setLIntegral_Ioi_le {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0∞}
    (hq : 1 ≤ q) (g : ℝ → ℝ≥0∞) :
    eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ioi t, g s) q multHaar ≤
      ENNReal.ofReal θ⁻¹ *
        eLpNorm (fun s : ℝ ↦ ENNReal.ofReal (s ^ (1 + θ)) * g s) q multHaar := by
  have h := eLpNorm_rpow_mul_setLIntegral_Ioi_multHaar_le hθ hq fun s ↦ ENNReal.ofReal s * g s
  have hL : (fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ioi t, g s) =ᵐ[multHaar]
      fun t ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ioi t, ENNReal.ofReal s * g s ∂multHaar := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [setLIntegral_eq_setLIntegral_multHaar g (Ioi_subset_Ioi ht.le)]
  have hR : (fun s : ℝ ↦ ENNReal.ofReal (s ^ θ) * (ENNReal.ofReal s * g s)) =ᵐ[multHaar]
      fun s ↦ ENNReal.ofReal (s ^ (1 + θ)) * g s := by
    filter_upwards [ae_pos_multHaar] with s hs
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add_one hs.ne', add_comm]
  rwa [← eLpNorm_congr_ae hL, eLpNorm_congr_ae hR] at h

/-- Relates the `L^p(0, ∞)` seminorm of `g` to the `L^p(dt / t)` seminorm of `t ^ (1 / p) * g t`,
for `p ≠ 0`, without measurability assumptions on `g`. -/
private theorem eLpNorm_volume_restrict_Ioi_eq_eLpNorm_multHaar {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (g : ℝ → ℝ≥0∞) :
    eLpNorm g p (volume.restrict (Ioi 0)) =
      eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * g t) p multHaar := by
  have hiff : AEStronglyMeasurable g (volume.restrict (Ioi 0)) ↔
      AEStronglyMeasurable (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * g t) multHaar := by
    rw [aestronglyMeasurable_multHaar_iff, aestronglyMeasurable_iff_aemeasurable,
      aestronglyMeasurable_iff_aemeasurable]
    refine ⟨fun hg ↦ (by fun_prop : Measurable fun t : ℝ ↦
        ENNReal.ofReal (t ^ p.toReal⁻¹)).aemeasurable.mul hg, fun hg ↦ ?_⟩
    have hcongr : g =ᵐ[volume.restrict (Ioi 0)] fun t : ℝ ↦
        ENNReal.ofReal (t ^ (-p.toReal⁻¹)) * (ENNReal.ofReal (t ^ p.toReal⁻¹) * g t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add ht, neg_add_cancel,
        Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    exact (((by fun_prop : Measurable fun t : ℝ ↦
      ENNReal.ofReal (t ^ (-p.toReal⁻¹))).aemeasurable.mul hg).congr hcongr.symm)
  by_cases hg : AEStronglyMeasurable g (volume.restrict (Ioi 0))
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hg, eLpNorm_of_not_aestronglyMeasurable (mt hiff.2 hg)]
  have hg' := hiff.1 hg
  rcases eq_or_ne p ∞ with rfl | hp
  · simp only [ENNReal.toReal_top, inv_zero, Real.rpow_zero, ENNReal.ofReal_one, one_mul] at hg' ⊢
    rw [eLpNorm_exponent_top hg, eLpNorm_exponent_top hg']
    simp [eLpNormEssSup_eq_essSup_eNorm]
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hg,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hg', setLIntegral_Ioi_eq_lintegral_multHaar]
  refine congrArg (· ^ (1 / p.toReal)) (lintegral_congr_ae ?_)
  filter_upwards [ae_pos_multHaar] with t ht
  simp only [eNorm_eq_self]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le,
    ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos ht _), ← Real.rpow_mul ht.le,
    inv_mul_cancel₀ hr.ne', Real.rpow_one]

/-- **Hardy's inequality** on `(0, ∞)`: for `1 < p ≤ ∞` and any `g : ℝ → ℝ≥0∞`,
`‖t ↦ (∫₀ᵗ g) / t‖_{L^p(0, ∞)} ≤ (1 - 1 / p)⁻¹ ‖g‖_{L^p(0, ∞)}`. For finite `p` the constant is
`p / (p - 1)`, and for `p = ∞` it is `1`. -/
theorem eLpNorm_setLIntegral_Ioc_div_le {p : ℝ≥0∞} (hp : 1 < p) (g : ℝ → ℝ≥0∞) :
    eLpNorm (fun t : ℝ ↦ (∫⁻ s in Ioc 0 t, g s) / ENNReal.ofReal t) p (volume.restrict (Ioi 0)) ≤
      ENNReal.ofReal (1 - p.toReal⁻¹)⁻¹ * eLpNorm g p (volume.restrict (Ioi 0)) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hθ : 0 < 1 - p.toReal⁻¹ := by
    rcases eq_or_ne p ∞ with rfl | hptop
    · simp
    · exact sub_pos.2 (inv_lt_one_of_one_lt₀ (by simpa using ENNReal.toReal_strict_mono hptop hp))
  rw [eLpNorm_volume_restrict_Ioi_eq_eLpNorm_multHaar hp0,
    eLpNorm_volume_restrict_Ioi_eq_eLpNorm_multHaar hp0 g]
  have hL : (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) *
        ((∫⁻ s in Ioc 0 t, g s) / ENNReal.ofReal t)) =ᵐ[multHaar]
      fun t ↦ ENNReal.ofReal (t ^ (-(1 - p.toReal⁻¹))) * ∫⁻ s in Ioc 0 t, g s := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [div_eq_mul_inv, mul_comm _ (ENNReal.ofReal t)⁻¹, ← mul_assoc,
      ← ENNReal.ofReal_inv_of_pos ht, ← ENNReal.ofReal_mul (by positivity),
      ← div_eq_mul_inv, ← Real.rpow_sub_one ht.ne', show p.toReal⁻¹ - 1 = -(1 - p.toReal⁻¹) by ring]
  have hR : (fun s : ℝ ↦ ENNReal.ofReal (s ^ (1 - (1 - p.toReal⁻¹))) * g s) =
      fun s ↦ ENNReal.ofReal (s ^ p.toReal⁻¹) * g s := by
    ext s
    rw [sub_sub_cancel]
  rw [eLpNorm_congr_ae hL, ← hR]
  exact eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le hθ hp.le g

end TauCeti

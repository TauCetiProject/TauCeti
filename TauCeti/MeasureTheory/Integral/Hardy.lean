/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import TauCeti.MeasureTheory.Measure.Haar.MultHaar
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Hardy's inequalities on `(0, ∞)`

This file proves the weighted Hardy inequalities on `(0, ∞)` with respect to the multiplicative
Haar measure `dt / t` (`TauCeti.multHaar`), together with the classical `Lᵖ(0, ∞)` bound for the
Cesàro averaging operator and the reverse inequality for antitone functions.

For `θ > 0`, `1 ≤ q ≤ ∞`, and `g : ℝ → ℝ≥0∞`:
* **Near `0`** (`TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le`):
  `‖t ↦ t ^ (-θ) ∫₀ᵗ g‖_{L^q(dt / t)} ≤ θ⁻¹ ‖t ↦ t ^ (1 - θ) g(t)‖_{L^q(dt / t)}`,
  with equality at `q = 1` (`TauCeti.lintegral_rpow_neg_mul_setLIntegral_Ioc`).
* **At `∞`** (`TauCeti.eLpNorm_rpow_mul_setLIntegral_Ioi_le`):
  `‖t ↦ t ^ θ ∫_t^∞ g‖_{L^q(dt / t)} ≤ θ⁻¹ ‖t ↦ t ^ (1 + θ) g(t)‖_{L^q(dt / t)}`,
  with equality at `q = 1` (`TauCeti.lintegral_rpow_mul_setLIntegral_Ioi`).
* **Classical Hardy inequality** (`TauCeti.eLpNorm_inv_mul_setLIntegral_Ioc_le`): for `1 < p ≤ ∞`,
  `‖t ↦ t⁻¹ ∫₀ᵗ g‖_{Lᵖ(0, ∞)} ≤ (1 - 1 / p)⁻¹ ‖g‖_{Lᵖ(0, ∞)}` (so `p / (p - 1)` for finite `p`
  and `1` at `p = ∞`).
* **Reverse bound for antitone functions**
  (`TauCeti.eLpNorm_rpow_one_sub_mul_le_of_antitoneOn`): if `g` is antitone on `(0, ∞)`, then
  `t ^ (1 - θ) g(t) ≤ t ^ (-θ) ∫₀ᵗ g` for every `t > 0`, so the reverse `L^q(dt / t)` bound holds
  with constant `1` for all `θ ∈ ℝ` and `q ∈ [0, ∞]`.

Both `dt / t` bounds are deduced uniformly across `1 ≤ q ≤ ∞` (including `q = ∞`) by applying
Schur's test (`TauCeti.eLpNorm_lintegral_mul_le`) to the dilation-invariant kernel
`k_θ(t, s) = 1_{0 < s ≤ t} (s / t) ^ θ`, whose row and column integrals against `dt / t` are both
equal to `θ⁻¹`. Because `eLpNorm` is `∞` on functions that are not a.e. strongly measurable, no
measurability hypothesis on `g` is needed in the `L^q` inequalities.

## Main declarations

* `TauCeti.lintegral_rpow_neg_mul_setLIntegral_Ioc`: exact `L¹(dt / t)` identity for
  `t ^ (-θ) ∫₀ᵗ g`.
* `TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le`: weighted Hardy inequality near `0`.
* `TauCeti.lintegral_rpow_mul_setLIntegral_Ioi`: exact `L¹(dt / t)` identity for
  `t ^ θ ∫_t^∞ g`.
* `TauCeti.eLpNorm_rpow_mul_setLIntegral_Ioi_le`: weighted Hardy inequality at `∞`.
* `TauCeti.eLpNorm_inv_mul_setLIntegral_Ioc_le`: classical `Lᵖ(0, ∞)` Hardy inequality for
  `1 < p ≤ ∞`.
* `TauCeti.rpow_one_sub_mul_le_rpow_neg_mul_setLIntegral_Ioc`,
  `TauCeti.eLpNorm_rpow_one_sub_mul_le_of_antitoneOn`: reverse inequality for antitone functions.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.3 (Lemma 5.3.1).
* G. H. Hardy, J. E. Littlewood, and G. Pólya, *Inequalities*, 2nd ed., Cambridge University
  Press, 1952, Theorem 327 and Theorem 330.
-/

public section

open MeasureTheory Measure Set
open scoped ENNReal

namespace TauCeti

/-- The dilation-invariant kernel `1_{0 < s ≤ t} (s / t) ^ θ` of Hardy's operator on `dt / t`. -/
private noncomputable def hardyKernel (θ t s : ℝ) : ℝ≥0∞ :=
  (Ioc 0 t).indicator (fun s ↦ ENNReal.ofReal ((s / t) ^ θ)) s

private theorem measurable_uncurry_hardyKernel (θ : ℝ) :
    Measurable (Function.uncurry (hardyKernel θ)) := by
  have hS : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Ioc 0 p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have h_eq : Function.uncurry (hardyKernel θ) =
      {p : ℝ × ℝ | p.2 ∈ Ioc 0 p.1}.indicator
        (fun p : ℝ × ℝ ↦ ENNReal.ofReal ((p.2 / p.1) ^ θ)) := by
    ext ⟨t, s⟩
    simp [hardyKernel, indicator_apply]
  rw [h_eq]
  exact (((measurable_snd.div measurable_fst).pow_const θ).ennreal_ofReal).indicator hS

/-- For `θ > 0` and `t > 0`, the row integral of `hardyKernel θ` against `dt / t` is `θ⁻¹`. -/
private theorem lintegral_hardyKernel_right {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t) :
    ∫⁻ s, hardyKernel θ t s ∂multHaar = ENNReal.ofReal θ⁻¹ := by
  have h_eq : hardyKernel θ t =
      (Ioc 0 t).indicator fun s ↦ ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal (s ^ θ) := by
    ext s
    by_cases hs : s ∈ Ioc 0 t
    · rw [hardyKernel, indicator_of_mem hs, indicator_of_mem hs,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), Real.div_rpow hs.1.le ht.le,
        Real.rpow_neg ht.le, div_eq_inv_mul]
    · simp [hardyKernel, hs]
  rw [h_eq, lintegral_indicator measurableSet_Ioc,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    setLIntegral_Ioc_rpow_multHaar hθ ht, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
    mul_left_comm, ← Real.rpow_add ht, neg_add_cancel, Real.rpow_zero, mul_one]

/-- For `θ > 0` and `s > 0`, the column integral of `hardyKernel θ` against `dt / t` is `θ⁻¹`. -/
private theorem lintegral_hardyKernel_left {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s) :
    ∫⁻ t, hardyKernel θ t s ∂multHaar = ENNReal.ofReal θ⁻¹ := by
  have hs_null : multHaar {s} = 0 := by
    rw [← Icc_self, multHaar_Icc hs le_rfl, sub_self, ENNReal.ofReal_zero]
  have hae_ne : ∀ᵐ t ∂multHaar, t ≠ s := ae_iff.2 (by simpa using hs_null)
  have hae : (fun t ↦ hardyKernel θ t s) =ᵐ[multHaar]
      (Ioi s).indicator fun t ↦ ENNReal.ofReal (s ^ θ) * ENNReal.ofReal (t ^ (-θ)) := by
    filter_upwards [hae_ne] with t ht_ne
    by_cases hst : s < t
    · rw [hardyKernel, indicator_of_mem (mem_Ioc.2 ⟨hs, hst.le⟩), indicator_of_mem (mem_Ioi.2 hst),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _), Real.div_rpow hs.le (hs.trans hst).le,
        Real.rpow_neg (hs.trans hst).le, div_eq_mul_inv]
    · have hnot : s ∉ Ioc 0 t := fun h ↦ hst (lt_of_le_of_ne (mem_Ioc.1 h).2 ht_ne.symm)
      rw [hardyKernel, indicator_of_notMem hnot, indicator_of_notMem (by simpa using hst)]
  rw [lintegral_congr_ae hae, lintegral_indicator measurableSet_Ioi,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    setLIntegral_Ioi_rpow_neg_multHaar hθ hs, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),
    mul_left_comm, ← Real.rpow_add hs, add_neg_cancel, Real.rpow_zero, mul_one]

/-- Integrating `hardyKernel θ t s` against `s ^ (1 - θ) g(s) ds / s` recovers
`t ^ (-θ) ∫₀ᵗ g(s) ds`, with no measurability hypothesis on `g`. -/
private theorem lintegral_hardyKernel_mul_Ioc (θ : ℝ) {t : ℝ} (ht : 0 < t) (g : ℝ → ℝ≥0∞) :
    ∫⁻ s, hardyKernel θ t s * (ENNReal.ofReal (s ^ (1 - θ)) * g s) ∂multHaar =
      ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s := by
  have hcongr : EqOn
      (fun s ↦ ENNReal.ofReal s⁻¹ *
        (hardyKernel θ t s * (ENNReal.ofReal (s ^ (1 - θ)) * g s)))
      ((Ioc 0 t).indicator fun s ↦ ENNReal.ofReal (t ^ (-θ)) * g s) (Ioi 0) := by
    intro s (hs : 0 < s)
    dsimp only [hardyKernel]
    by_cases hst : s ≤ t
    · have hmem : s ∈ Ioc 0 t := ⟨hs, hst⟩
      rw [indicator_of_mem hmem, indicator_of_mem hmem]
      calc ENNReal.ofReal s⁻¹ * (ENNReal.ofReal ((s / t) ^ θ) *
            (ENNReal.ofReal (s ^ (1 - θ)) * g s))
          = ENNReal.ofReal (s⁻¹ * ((s / t) ^ θ * s ^ (1 - θ))) * g s := by
            rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hs.le),
              ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hs.le)
                (Real.rpow_nonneg (div_nonneg hs.le ht.le) _)), mul_assoc]
        _ = ENNReal.ofReal (t ^ (-θ)) * g s := by
            congr 2
            rw [Real.div_rpow hs.le ht.le, div_eq_mul_inv, mul_right_comm (s ^ θ),
              ← Real.rpow_add hs, add_sub_cancel, Real.rpow_one, ← mul_assoc,
              inv_mul_cancel₀ hs.ne', one_mul, ← Real.rpow_neg ht.le]
    · have hnot : s ∉ Ioc 0 t := fun h ↦ hst h.2
      simp [indicator_of_notMem hnot]
  rw [lintegral_multHaar_eq_setLIntegral, setLIntegral_congr_fun measurableSet_Ioi hcongr,
    setLIntegral_indicator measurableSet_Ioc, inter_eq_left.2 Ioc_subset_Ioi_self,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Integrating the transposed kernel `hardyKernel θ s t` against `s ^ (1 + θ) g(s) ds / s`
recovers `t ^ θ ∫_t^∞ g(s) ds`, with no measurability hypothesis on `g`. -/
private theorem lintegral_hardyKernel_swap_mul_Ioi (θ : ℝ) {t : ℝ} (ht : 0 < t) (g : ℝ → ℝ≥0∞) :
    ∫⁻ s, hardyKernel θ s t * (ENNReal.ofReal (s ^ (1 + θ)) * g s) ∂multHaar =
      ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ioi t, g s := by
  have hcongr : EqOn
      (fun s ↦ ENNReal.ofReal s⁻¹ *
        (hardyKernel θ s t * (ENNReal.ofReal (s ^ (1 + θ)) * g s)))
      ((Ici t).indicator fun s ↦ ENNReal.ofReal (t ^ θ) * g s) (Ioi 0) := by
    intro s (hs : 0 < s)
    dsimp only [hardyKernel]
    by_cases hts : t ≤ s
    · have hmem : t ∈ Ioc 0 s := ⟨ht, hts⟩
      rw [indicator_of_mem hmem, indicator_of_mem (mem_Ici.2 hts)]
      calc ENNReal.ofReal s⁻¹ * (ENNReal.ofReal ((t / s) ^ θ) *
            (ENNReal.ofReal (s ^ (1 + θ)) * g s))
          = ENNReal.ofReal (s⁻¹ * ((t / s) ^ θ * s ^ (1 + θ))) * g s := by
            rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hs.le),
              ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hs.le)
                (Real.rpow_nonneg (div_nonneg ht.le hs.le) _)), mul_assoc]
        _ = ENNReal.ofReal (t ^ θ) * g s := by
            congr 2
            have hs_ne : s ≠ 0 := hs.ne'
            have hsθ_ne : s ^ θ ≠ 0 := (Real.rpow_pos_of_pos hs θ).ne'
            rw [Real.div_rpow ht.le hs.le, Real.rpow_add hs, Real.rpow_one]
            field_simp
    · have hnot : t ∉ Ioc 0 s := fun h ↦ hts h.2
      rw [indicator_of_notMem hnot, indicator_of_notMem (by simpa using hts)]
      simp
  rw [lintegral_multHaar_eq_setLIntegral, setLIntegral_congr_fun measurableSet_Ioi hcongr,
    setLIntegral_indicator measurableSet_Ici, inter_eq_left.2 (Ici_subset_Ioi.2 ht),
    ← restrict_congr_set Ioi_ae_eq_Ici, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- `A ^ (1 - 1 / q) * A ^ (1 / q) = A` for `1 ≤ q`. -/
private theorem rpow_one_sub_inv_mul_rpow_inv {q : ℝ≥0∞} (hq : 1 ≤ q) (A : ℝ≥0∞) :
    A ^ (1 - q.toReal⁻¹) * A ^ q.toReal⁻¹ = A := by
  have h0 : 0 ≤ 1 - q.toReal⁻¹ := by
    rcases eq_or_ne q ∞ with rfl | hq_top
    · simp
    · exact sub_nonneg.2 (inv_le_one_of_one_le₀ (by simpa using ENNReal.toReal_mono hq_top hq))
  rw [← ENNReal.rpow_add_of_nonneg _ _ h0 (by positivity), sub_add_cancel, ENNReal.rpow_one]

/-- **Exact `L¹(dt / t)` Hardy identity near `0`.** For `θ > 0` and `g` a.e. measurable on
`(0, ∞)`, `∫ t ^ (-θ) (∫₀ᵗ g) dt / t = θ⁻¹ ∫ t ^ (1 - θ) g(t) dt / t`. -/
theorem lintegral_rpow_neg_mul_setLIntegral_Ioc {θ : ℝ} (hθ : 0 < θ) {g : ℝ → ℝ≥0∞}
    (hg : AEMeasurable g (volume.restrict (Ioi 0))) :
    ∫⁻ t, ENNReal.ofReal (t ^ (-θ)) * (∫⁻ s in Ioc 0 t, g s) ∂multHaar =
      ENNReal.ofReal θ⁻¹ * ∫⁻ t, ENNReal.ofReal (t ^ (1 - θ)) * g t ∂multHaar := by
  set G : ℝ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (s ^ (1 - θ)) * g s
  have hG : AEMeasurable G multHaar :=
    ((measurable_id.pow_const (1 - θ)).ennreal_ofReal).aemeasurable.mul
      (aemeasurable_multHaar_iff.2 hg)
  have hjoint : AEMeasurable (Function.uncurry fun t s ↦ hardyKernel θ t s * G s)
      (multHaar.prod multHaar) :=
    (measurable_uncurry_hardyKernel θ).aemeasurable.mul hG.comp_snd
  have hlhs : ∫⁻ t, ENNReal.ofReal (t ^ (-θ)) * (∫⁻ s in Ioc 0 t, g s) ∂multHaar =
      ∫⁻ t, ∫⁻ s, hardyKernel θ t s * G s ∂multHaar ∂multHaar := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_pos_multHaar] with t ht
    exact (lintegral_hardyKernel_mul_Ioc θ ht g).symm
  rw [hlhs, lintegral_lintegral_swap hjoint, ← lintegral_const_mul'' _ hG]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_pos_multHaar] with s hs
  have hm : Measurable (fun t ↦ hardyKernel θ t s) :=
    (measurable_uncurry_hardyKernel θ).comp measurable_prodMk_right
  rw [lintegral_mul_const _ hm, lintegral_hardyKernel_left hθ hs]

/-- **Weighted Hardy inequality near `0`.** For `θ > 0`, `1 ≤ q ≤ ∞`, and any `g : ℝ → ℝ≥0∞`,
`‖t ↦ t ^ (-θ) ∫₀ᵗ g‖_{L^q(dt / t)} ≤ θ⁻¹ ‖t ↦ t ^ (1 - θ) g(t)‖_{L^q(dt / t)}`. -/
theorem eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (g : ℝ → ℝ≥0∞) :
    eLpNorm (fun t ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s) q multHaar ≤
      ENNReal.ofReal θ⁻¹ *
        eLpNorm (fun t ↦ ENNReal.ofReal (t ^ (1 - θ)) * g t) q multHaar := by
  set G : ℝ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (s ^ (1 - θ)) * g s
  by_cases hG : AEStronglyMeasurable G multHaar
  · have hcongr : (fun t ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s) =ᵐ[multHaar]
        fun t ↦ ∫⁻ s, hardyKernel θ t s * G s ∂multHaar := by
      filter_upwards [ae_pos_multHaar] with t ht
      exact (lintegral_hardyKernel_mul_Ioc θ ht g).symm
    rw [eLpNorm_congr_ae hcongr]
    set A := ENNReal.ofReal θ⁻¹
    have hrow : ∀ᵐ t ∂multHaar, ∫⁻ s, hardyKernel θ t s ∂multHaar ≤ A := by
      filter_upwards [ae_pos_multHaar] with t ht using (lintegral_hardyKernel_right hθ ht).le
    have hcol : ∀ᵐ s ∂multHaar, ∫⁻ t, hardyKernel θ t s ∂multHaar ≤ A := by
      filter_upwards [ae_pos_multHaar] with s hs using (lintegral_hardyKernel_left hθ hs).le
    have hschur := eLpNorm_lintegral_mul_le
      (measurable_uncurry_hardyKernel θ).aemeasurable hG.aemeasurable hq hrow hcol
    rwa [rpow_one_sub_inv_mul_rpow_inv hq A] at hschur
  · have hθ_ne : ENNReal.ofReal θ⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hθ)).ne'
    rw [eLpNorm_of_not_aestronglyMeasurable hG, ENNReal.mul_top hθ_ne]
    exact le_top

/-- **Exact `L¹(dt / t)` Hardy identity at `∞`.** For `θ > 0` and `g` a.e. measurable on
`(0, ∞)`, `∫ t ^ θ (∫_t^∞ g) dt / t = θ⁻¹ ∫ t ^ (1 + θ) g(t) dt / t`. -/
theorem lintegral_rpow_mul_setLIntegral_Ioi {θ : ℝ} (hθ : 0 < θ) {g : ℝ → ℝ≥0∞}
    (hg : AEMeasurable g (volume.restrict (Ioi 0))) :
    ∫⁻ t, ENNReal.ofReal (t ^ θ) * (∫⁻ s in Ioi t, g s) ∂multHaar =
      ENNReal.ofReal θ⁻¹ * ∫⁻ t, ENNReal.ofReal (t ^ (1 + θ)) * g t ∂multHaar := by
  set G : ℝ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (s ^ (1 + θ)) * g s
  have hG : AEMeasurable G multHaar :=
    ((measurable_id.pow_const (1 + θ)).ennreal_ofReal).aemeasurable.mul
      (aemeasurable_multHaar_iff.2 hg)
  have hk_swap : Measurable (Function.uncurry fun t s ↦ hardyKernel θ s t) :=
    (measurable_uncurry_hardyKernel θ).comp measurable_swap
  have hjoint : AEMeasurable (Function.uncurry fun t s ↦ hardyKernel θ s t * G s)
      (multHaar.prod multHaar) :=
    hk_swap.aemeasurable.mul hG.comp_snd
  have hlhs : ∫⁻ t, ENNReal.ofReal (t ^ θ) * (∫⁻ s in Ioi t, g s) ∂multHaar =
      ∫⁻ t, ∫⁻ s, hardyKernel θ s t * G s ∂multHaar ∂multHaar := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_pos_multHaar] with t ht
    exact (lintegral_hardyKernel_swap_mul_Ioi θ ht g).symm
  rw [hlhs, lintegral_lintegral_swap hjoint, ← lintegral_const_mul'' _ hG]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_pos_multHaar] with s hs
  have hm : Measurable (hardyKernel θ s) :=
    (measurable_uncurry_hardyKernel θ).comp measurable_prodMk_left
  rw [lintegral_mul_const _ hm, lintegral_hardyKernel_right hθ hs]

/-- **Weighted Hardy inequality at `∞`.** For `θ > 0`, `1 ≤ q ≤ ∞`, and any `g : ℝ → ℝ≥0∞`,
`‖t ↦ t ^ θ ∫_t^∞ g‖_{L^q(dt / t)} ≤ θ⁻¹ ‖t ↦ t ^ (1 + θ) g(t)‖_{L^q(dt / t)}`. -/
theorem eLpNorm_rpow_mul_setLIntegral_Ioi_le {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (g : ℝ → ℝ≥0∞) :
    eLpNorm (fun t ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ioi t, g s) q multHaar ≤
      ENNReal.ofReal θ⁻¹ *
        eLpNorm (fun t ↦ ENNReal.ofReal (t ^ (1 + θ)) * g t) q multHaar := by
  set G : ℝ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (s ^ (1 + θ)) * g s
  by_cases hG : AEStronglyMeasurable G multHaar
  · have hcongr : (fun t ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ioi t, g s) =ᵐ[multHaar]
        fun t ↦ ∫⁻ s, hardyKernel θ s t * G s ∂multHaar := by
      filter_upwards [ae_pos_multHaar] with t ht
      exact (lintegral_hardyKernel_swap_mul_Ioi θ ht g).symm
    rw [eLpNorm_congr_ae hcongr]
    set A := ENNReal.ofReal θ⁻¹
    have hk_swap : Measurable (Function.uncurry fun t s ↦ hardyKernel θ s t) :=
      (measurable_uncurry_hardyKernel θ).comp measurable_swap
    have hrow : ∀ᵐ t ∂multHaar, ∫⁻ s, hardyKernel θ s t ∂multHaar ≤ A := by
      filter_upwards [ae_pos_multHaar] with t ht using (lintegral_hardyKernel_left hθ ht).le
    have hcol : ∀ᵐ s ∂multHaar, ∫⁻ t, hardyKernel θ s t ∂multHaar ≤ A := by
      filter_upwards [ae_pos_multHaar] with s hs using (lintegral_hardyKernel_right hθ hs).le
    have hschur := eLpNorm_lintegral_mul_le
      hk_swap.aemeasurable hG.aemeasurable hq hrow hcol
    rwa [rpow_one_sub_inv_mul_rpow_inv hq A] at hschur
  · have hθ_ne : ENNReal.ofReal θ⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hθ)).ne'
    rw [eLpNorm_of_not_aestronglyMeasurable hG, ENNReal.mul_top hθ_ne]
    exact le_top

/-- **Classical Hardy inequality on `(0, ∞)`.** For `1 < p ≤ ∞` and any `g : ℝ → ℝ≥0∞`, the
Cesàro average `t ↦ t⁻¹ ∫₀ᵗ g` satisfies
`‖t ↦ t⁻¹ ∫₀ᵗ g‖_{Lᵖ(0, ∞)} ≤ (1 - 1 / p)⁻¹ ‖g‖_{Lᵖ(0, ∞)}`.
For finite `p`, `(1 - 1 / p)⁻¹ = p / (p - 1)`; for `p = ∞` the constant is `1`. -/
theorem eLpNorm_inv_mul_setLIntegral_Ioc_le {p : ℝ≥0∞} (hp : 1 < p) (g : ℝ → ℝ≥0∞) :
    eLpNorm (fun t ↦ ENNReal.ofReal t⁻¹ * ∫⁻ s in Ioc 0 t, g s) p (volume.restrict (Ioi 0)) ≤
      ENNReal.ofReal (1 - p.toReal⁻¹)⁻¹ * eLpNorm g p (volume.restrict (Ioi 0)) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  set θ := 1 - p.toReal⁻¹
  have hθ : 0 < θ := by
    rcases eq_or_ne p ∞ with rfl | hptop
    · simp [θ]
    · have hp_gt : 1 < p.toReal := by
        simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop).2 hp
      exact sub_pos.2 (inv_lt_one_of_one_lt₀ hp_gt)
  rw [← eLpNorm_rpow_toReal_inv_mul_multHaar hp0,
    ← eLpNorm_rpow_toReal_inv_mul_multHaar hp0 g]
  have hlhs : (fun t ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) *
        (ENNReal.ofReal t⁻¹ * ∫⁻ s in Ioc 0 t, g s)) =ᵐ[multHaar]
      fun t ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_neg_one t,
      ← Real.rpow_add ht]
    congr 3
    dsimp [θ]
    ring
  have hrhs : (fun t ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * g t) =
      fun t ↦ ENNReal.ofReal (t ^ (1 - θ)) * g t := by
    ext t
    have hsub : p.toReal⁻¹ = 1 - θ := by dsimp [θ]; ring
    rw [hsub]
  rw [eLpNorm_congr_ae hlhs, hrhs]
  exact eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le hθ hp.le g

/-- If `g` is antitone on `(0, ∞)`, then `t ^ (1 - θ) g(t) ≤ t ^ (-θ) ∫₀ᵗ g` for every `t > 0`
and `θ ∈ ℝ`. -/
theorem rpow_one_sub_mul_le_rpow_neg_mul_setLIntegral_Ioc (θ : ℝ) {g : ℝ → ℝ≥0∞}
    (hg : AntitoneOn g (Ioi 0)) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (1 - θ)) * g t ≤
      ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s := by
  have hint : ENNReal.ofReal t * g t ≤ ∫⁻ s in Ioc 0 t, g s := by
    calc ENNReal.ofReal t * g t
        = ∫⁻ _ in Ioc 0 t, g t := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
      _ ≤ ∫⁻ s in Ioc 0 t, g s :=
          setLIntegral_mono' measurableSet_Ioc fun s hs ↦ hg hs.1 ht hs.2
  calc ENNReal.ofReal (t ^ (1 - θ)) * g t
      = ENNReal.ofReal (t ^ (-θ)) * (ENNReal.ofReal t * g t) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
          ← Real.rpow_add_one ht.ne']
        ring_nf
    _ ≤ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s := by gcongr

/-- **Reverse Hardy bound for antitone functions.** If `g` is antitone on `(0, ∞)`, then for every
`θ ∈ ℝ` and `q ∈ [0, ∞]`,
`‖t ↦ t ^ (1 - θ) g(t)‖_{L^q(dt / t)} ≤ ‖t ↦ t ^ (-θ) ∫₀ᵗ g‖_{L^q(dt / t)}`. -/
theorem eLpNorm_rpow_one_sub_mul_le_of_antitoneOn (θ : ℝ) (q : ℝ≥0∞) {g : ℝ → ℝ≥0∞}
    (hg : AntitoneOn g (Ioi 0)) :
    eLpNorm (fun t ↦ ENNReal.ofReal (t ^ (1 - θ)) * g t) q multHaar ≤
      eLpNorm (fun t ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s) q multHaar := by
  have hg_mh : AEMeasurable g multHaar :=
    aemeasurable_multHaar_iff.2 (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi hg)
  have hmeas : AEStronglyMeasurable
      (fun t ↦ ENNReal.ofReal (t ^ (1 - θ)) * g t) multHaar :=
    (((measurable_id.pow_const (1 - θ)).ennreal_ofReal).aemeasurable.mul
      hg_mh).aestronglyMeasurable
  refine eLpNorm_mono_eNorm_ae hmeas ?_
  filter_upwards [ae_pos_multHaar] with t ht
  simp only [eNorm_eq_self]
  exact rpow_one_sub_mul_le_rpow_neg_mul_setLIntegral_Ioc θ hg ht

end TauCeti

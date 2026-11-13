/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.MultHaar
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Weighted Hardy inequalities on `(0, ∞)`

For `θ > 0` and `1 ≤ q ≤ ∞`, the prefix and tail integration operators satisfy the sharp bounds
with respect to the multiplicative Haar measure `dt / t` (`TauCeti.multHaar`):

* `‖t ↦ t ^ (-θ) ∫₀ᵗ ψ(s) ds / s‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ (-θ) ψ(s)‖_{L^q(ds / s)}`,
* `‖t ↦ t ^ θ ∫_t^∞ ψ(s) ds / s‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ θ ψ(s)‖_{L^q(ds / s)}`.

Substituting `ψ(s) = s φ(s)` turns the inner integrals into Lebesgue integrals on `(0, t]` and
`[t, ∞)`:

* `‖t ↦ t ^ (-θ) ∫₀ᵗ φ(s) ds‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ (1 - θ) φ(s)‖_{L^q(ds / s)}`,
* `‖t ↦ t ^ θ ∫_t^∞ φ(s) ds‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ (1 + θ) φ(s)‖_{L^q(ds / s)}`.

Both pairs follow uniformly across `1 ≤ q ≤ ∞` from Schur's test
(`TauCeti.eLpNorm_lintegral_mul_le`) applied to `k(t, s) = 1_{0 < s ≤ t} (s / t) ^ θ` and its
transpose on `multHaar`, whose row and column integrals against `dt / t` both equal `θ⁻¹`. In real
interpolation, the prefix inequality bounds the `K`-method norm of `(L¹, L^∞)` by `‖·‖_{p, q}`
(`1 / p = 1 - θ`), while both inequalities together underlie Holmstedt's reiteration estimates.

## Main declarations

* `TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_multHaar_le`: prefix Hardy inequality (`dt / t`).
* `TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le`: prefix Hardy inequality (`∫₀ᵗ φ(s) ds`).
* `TauCeti.eLpNorm_rpow_mul_setLIntegral_Ici_multHaar_le`: tail Hardy inequality (`dt / t`).
* `TauCeti.eLpNorm_rpow_mul_setLIntegral_Ici_le`: tail Hardy inequality (`∫_t^∞ φ(s) ds`).

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, Lemma 5.3.1.
* G. H. Hardy, J. E. Littlewood, and G. Pólya, *Inequalities*, 2nd ed., Cambridge University
  Press, 1952, Theorem 330.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- The homogeneous Schur kernel `1_{0 < s ≤ t} (s / t) ^ θ` on `(0, ∞) × (0, ∞)`. Its transpose
`(t, s) ↦ hardyKernel θ s t` is the kernel of the tail Hardy operator. -/
private noncomputable def hardyKernel (θ t s : ℝ) : ℝ≥0∞ :=
  if 0 < t ∧ 0 < s ∧ s ≤ t then ENNReal.ofReal ((s / t) ^ θ) else 0

private theorem measurable_uncurry_hardyKernel (θ : ℝ) :
    Measurable (Function.uncurry (hardyKernel θ)) :=
  Measurable.ite
    ((measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst)))
    (((measurable_snd.div measurable_fst).pow_const θ).ennreal_ofReal) measurable_const

private theorem measurable_uncurry_hardyKernel_swap (θ : ℝ) :
    Measurable (Function.uncurry fun t s ↦ hardyKernel θ s t) :=
  (measurable_uncurry_hardyKernel θ).comp measurable_swap

private theorem lintegral_hardyKernel_row {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t) :
    ∫⁻ s, hardyKernel θ t s ∂multHaar = ENNReal.ofReal θ⁻¹ := by
  have hcongr : hardyKernel θ t = (Ioc 0 t).indicator fun s ↦ ENNReal.ofReal ((s / t) ^ θ) := by
    ext s; simp [hardyKernel, ht, indicator_apply]
  rw [hcongr, lintegral_indicator measurableSet_Ioc,
    setLIntegral_multHaar_eq_setLIntegral measurableSet_Ioc,
    inter_eq_self_of_subset_left Ioc_subset_Ioi_self, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have hpt : ∀ s ∈ Ioo 0 t, ENNReal.ofReal s⁻¹ * ENNReal.ofReal ((s / t) ^ θ) =
      ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal (s ^ (θ - 1)) := fun s hs ↦ by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hs.1.le),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
    congr 1
    rw [Real.div_rpow hs.1.le ht.le, Real.rpow_neg ht.le, Real.rpow_sub hs.1, Real.rpow_one]
    simp only [div_eq_mul_inv]; ring
  rw [setLIntegral_congr_fun measurableSet_Ioo hpt, lintegral_const_mul _ (by fun_prop),
    lintegral_ofReal_rpow_Ioo (by linarith) ht.le, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  congr 1
  have htθ : t ^ θ ≠ 0 := (Real.rpow_pos_of_pos ht θ).ne'
  rw [sub_add_cancel, Real.rpow_neg ht.le]; field_simp

private theorem lintegral_hardyKernel_col {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s) :
    ∫⁻ t, hardyKernel θ t s ∂multHaar = ENNReal.ofReal θ⁻¹ := by
  have hcongr : (fun t ↦ hardyKernel θ t s) =
      (Ici s).indicator fun t ↦ ENNReal.ofReal ((s / t) ^ θ) := by
    ext t; by_cases hst : s ≤ t
    · simp [hardyKernel, hs, hst, hs.trans_le hst]
    · simp [hardyKernel, hst]
  rw [hcongr, lintegral_indicator measurableSet_Ici,
    setLIntegral_multHaar_eq_setLIntegral measurableSet_Ici,
    inter_eq_self_of_subset_left (Ici_subset_Ioi.2 hs), ← Measure.restrict_congr_set Ioi_ae_eq_Ici]
  have hpt : ∀ t ∈ Ioi s, ENNReal.ofReal t⁻¹ * ENNReal.ofReal ((s / t) ^ θ) =
      ENNReal.ofReal (s ^ θ) * ENNReal.ofReal (t ^ (-θ - 1)) := fun t ht ↦ by
    have ht0 : 0 < t := hs.trans ht
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 ht0.le),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
    congr 1
    rw [Real.div_rpow hs.le ht0.le, show -θ - 1 = -(θ + 1) by ring, Real.rpow_neg ht0.le,
      Real.rpow_add ht0, Real.rpow_one]
    simp only [div_eq_mul_inv, mul_inv]; ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_const_mul _ (by fun_prop),
    lintegral_ofReal_rpow_Ioi_of_lt (by linarith) hs,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
  congr 1
  have hsθ : s ^ θ ≠ 0 := (Real.rpow_pos_of_pos hs θ).ne'
  rw [show -θ - 1 + 1 = -θ by ring, neg_div_neg_eq, Real.rpow_neg hs.le]; field_simp

private theorem schur_const_eq_self (A : ℝ≥0∞) {q : ℝ≥0∞} (hq : 1 ≤ q) :
    A ^ (1 - q.toReal⁻¹) * A ^ q.toReal⁻¹ = A := by
  have h₀ : 0 ≤ 1 - q.toReal⁻¹ := by
    rcases eq_or_ne q ∞ with rfl | hq_top
    · simp
    · exact sub_nonneg.2 (inv_le_one_of_one_le₀ (by simpa using ENNReal.toReal_mono hq_top hq))
  rw [← ENNReal.rpow_add_of_nonneg _ _ h₀ (by positivity), sub_add_cancel, ENNReal.rpow_one]

private theorem setLIntegral_eq_multHaar {S : Set ℝ} (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0)
    (φ : ℝ → ℝ≥0∞) :
    ∫⁻ s in S, φ s = ∫⁻ s in S, ENNReal.ofReal s * φ s ∂multHaar := by
  rw [setLIntegral_multHaar_eq_setLIntegral hS, inter_eq_self_of_subset_left hS0]
  refine setLIntegral_congr_fun hS fun s hs ↦ ?_
  have hs0 : 0 < s := hS0 hs
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hs0.le), inv_mul_cancel₀ hs0.ne',
    ENNReal.ofReal_one, one_mul]

/-- **Prefix Hardy inequality** in multiplicative Haar form: for `θ > 0` and `1 ≤ q ≤ ∞`,
`‖t ↦ t ^ (-θ) ∫₀ᵗ ψ(s) ds / s‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ (-θ) ψ(s)‖_{L^q(ds / s)}`. -/
theorem eLpNorm_rpow_neg_mul_setLIntegral_Ioc_multHaar_le {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {ψ : ℝ → ℝ≥0∞} (hψ : AEMeasurable ψ multHaar) :
    eLpNorm (fun t ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, ψ s ∂multHaar) q multHaar ≤
      ENNReal.ofReal θ⁻¹ * eLpNorm (fun s ↦ ENNReal.ofReal (s ^ (-θ)) * ψ s) q multHaar := by
  set g : ℝ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (s ^ (-θ)) * ψ s
  have hg : AEMeasurable g multHaar :=
    ((measurable_id.pow_const (-θ)).ennreal_ofReal).aemeasurable.mul hψ
  have hae : (fun t ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, ψ s ∂multHaar) =ᵐ[multHaar]
      fun t ↦ ∫⁻ s, hardyKernel θ t s * g s ∂multHaar := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [← lintegral_const_mul'' _ hψ.restrict, ← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun s ↦ ?_
    by_cases hs : s ∈ Ioc 0 t
    · have hpow : (s / t) ^ θ * s ^ (-θ) = t ^ (-θ) := by
        rw [Real.div_rpow hs.1.le ht.le, Real.rpow_neg hs.1.le, Real.rpow_neg ht.le,
          div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ (Real.rpow_pos_of_pos hs.1 θ).ne',
          one_mul]
      simp only [indicator_of_mem hs, hardyKernel, ht, hs.1, hs.2, and_self, ↓reduceIte, g]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (div_nonneg hs.1.le ht.le) θ), hpow]
    · simp [indicator_of_notMem hs, hardyKernel, show ¬(0 < t ∧ 0 < s ∧ s ≤ t) from
        fun h ↦ hs ⟨h.2.1, h.2.2⟩]
  rw [eLpNorm_congr_ae hae]
  exact (eLpNorm_lintegral_mul_le (measurable_uncurry_hardyKernel θ).aemeasurable hg hq
    (ae_pos_multHaar.mono fun t ht ↦ (lintegral_hardyKernel_row hθ ht).le)
    (ae_pos_multHaar.mono fun s hs ↦ (lintegral_hardyKernel_col hθ hs).le)).trans_eq
    (by rw [schur_const_eq_self _ hq])

/-- **Prefix Hardy inequality** for Lebesgue integrals on `(0, t]`: for `θ > 0` and `1 ≤ q ≤ ∞`,
`‖t ↦ t ^ (-θ) ∫₀ᵗ φ(s) ds‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ (1 - θ) φ(s)‖_{L^q(ds / s)}`. -/
theorem eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {φ : ℝ → ℝ≥0∞} (hφ : AEMeasurable φ (volume.restrict (Ioi 0))) :
    eLpNorm (fun t ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, φ s) q multHaar ≤
      ENNReal.ofReal θ⁻¹ * eLpNorm (fun s ↦ ENNReal.ofReal (s ^ (1 - θ)) * φ s) q multHaar := by
  have hφ_mh : AEMeasurable φ multHaar :=
    multHaar_def ▸ hφ.mono_ac (withDensity_absolutelyContinuous _ _)
  simp_rw [setLIntegral_eq_multHaar measurableSet_Ioc Ioc_subset_Ioi_self]
  refine (eLpNorm_rpow_neg_mul_setLIntegral_Ioc_multHaar_le hθ hq
    (measurable_id.ennreal_ofReal.aemeasurable.mul hφ_mh)).trans_eq ?_
  congr 1; refine eLpNorm_congr_ae (ae_pos_multHaar.mono fun s hs ↦ ?_)
  dsimp only [Pi.mul_apply, id_eq]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _), ← Real.rpow_add_one hs.ne',
    show -θ + 1 = 1 - θ by ring]

/-- **Tail Hardy inequality** in multiplicative Haar form: for `θ > 0` and `1 ≤ q ≤ ∞`,
`‖t ↦ t ^ θ ∫_t^∞ ψ(s) ds / s‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ θ ψ(s)‖_{L^q(ds / s)}`. -/
theorem eLpNorm_rpow_mul_setLIntegral_Ici_multHaar_le {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {ψ : ℝ → ℝ≥0∞} (hψ : AEMeasurable ψ multHaar) :
    eLpNorm (fun t ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ici t, ψ s ∂multHaar) q multHaar ≤
      ENNReal.ofReal θ⁻¹ * eLpNorm (fun s ↦ ENNReal.ofReal (s ^ θ) * ψ s) q multHaar := by
  set g : ℝ → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (s ^ θ) * ψ s
  have hg : AEMeasurable g multHaar :=
    ((measurable_id.pow_const θ).ennreal_ofReal).aemeasurable.mul hψ
  have hae : (fun t ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ici t, ψ s ∂multHaar) =ᵐ[multHaar]
      fun t ↦ ∫⁻ s, hardyKernel θ s t * g s ∂multHaar := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [← lintegral_const_mul'' _ hψ.restrict, ← lintegral_indicator measurableSet_Ici]
    refine lintegral_congr fun s ↦ ?_
    by_cases hs : s ∈ Ici t
    · have hs0 : 0 < s := ht.trans_le hs
      have hst : t ≤ s := hs
      have hpow : (t / s) ^ θ * s ^ θ = t ^ θ := by
        rw [Real.div_rpow ht.le hs0.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hs0 θ).ne']
      simp only [indicator_of_mem hs, hardyKernel, hs0, ht, hst, and_self, ↓reduceIte, g]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (div_nonneg ht.le hs0.le) θ), hpow]
    · simp [indicator_of_notMem hs, hardyKernel,
        show ¬(0 < s ∧ 0 < t ∧ t ≤ s) from fun h ↦ hs h.2.2]
  rw [eLpNorm_congr_ae hae]
  exact (eLpNorm_lintegral_mul_le (measurable_uncurry_hardyKernel_swap θ).aemeasurable hg hq
    (ae_pos_multHaar.mono fun t ht ↦ (lintegral_hardyKernel_col hθ ht).le)
    (ae_pos_multHaar.mono fun s hs ↦ (lintegral_hardyKernel_row hθ hs).le)).trans_eq
    (by rw [schur_const_eq_self _ hq])

/-- **Tail Hardy inequality** for Lebesgue integrals on `[t, ∞)`: for `θ > 0` and `1 ≤ q ≤ ∞`,
`‖t ↦ t ^ θ ∫_t^∞ φ(s) ds‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ (1 + θ) φ(s)‖_{L^q(ds / s)}`. -/
theorem eLpNorm_rpow_mul_setLIntegral_Ici_le {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {φ : ℝ → ℝ≥0∞} (hφ : AEMeasurable φ (volume.restrict (Ioi 0))) :
    eLpNorm (fun t ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ici t, φ s) q multHaar ≤
      ENNReal.ofReal θ⁻¹ * eLpNorm (fun s ↦ ENNReal.ofReal (s ^ (1 + θ)) * φ s) q multHaar := by
  have hφ_mh : AEMeasurable φ multHaar :=
    multHaar_def ▸ hφ.mono_ac (withDensity_absolutelyContinuous _ _)
  have hlhs : (fun t ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ici t, φ s) =ᵐ[multHaar]
      fun t ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ici t, ENNReal.ofReal s * φ s ∂multHaar :=
    ae_pos_multHaar.mono fun t ht ↦ by
      dsimp only; rw [setLIntegral_eq_multHaar measurableSet_Ici (Ici_subset_Ioi.2 ht)]
  rw [eLpNorm_congr_ae hlhs]
  refine (eLpNorm_rpow_mul_setLIntegral_Ici_multHaar_le hθ hq
    (measurable_id.ennreal_ofReal.aemeasurable.mul hφ_mh)).trans_eq ?_
  congr 1; refine eLpNorm_congr_ae (ae_pos_multHaar.mono fun s hs ↦ ?_)
  dsimp only [Pi.mul_apply, id_eq]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _), ← Real.rpow_add_one hs.ne',
    add_comm θ 1]

end TauCeti

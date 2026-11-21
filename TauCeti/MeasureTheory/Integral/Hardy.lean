/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Holder
public import TauCeti.MeasureTheory.Measure.Haar.MultHaar
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Weighted Hardy inequalities on `(0, ∞)`

For `θ > 0` and `1 ≤ q ≤ ∞`, the prefix and tail integration operators satisfy the weighted norm
bounds with respect to the multiplicative Haar measure `dt / t` (`TauCeti.multHaar`):

* `‖t ↦ t ^ (-θ) ∫₀ᵗ ψ(s) ds / s‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ (-θ) ψ(s)‖_{L^q(ds / s)}`,
* `‖t ↦ t ^ θ ∫_t^∞ ψ(s) ds / s‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ θ ψ(s)‖_{L^q(ds / s)}`.

Substituting `ψ(s) = s φ(s)` turns the inner integrals into Lebesgue integrals on `(0, t]` and
`[t, ∞)`:

* `‖t ↦ t ^ (-θ) ∫₀ᵗ φ(s) ds‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ (1 - θ) φ(s)‖_{L^q(ds / s)}`,
* `‖t ↦ t ^ θ ∫_t^∞ φ(s) ds‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ (1 + θ) φ(s)‖_{L^q(ds / s)}`.

Both pairs follow uniformly across `1 ≤ q ≤ ∞` from Schur's test
(`TauCeti.eLpNorm_lintegral_mul_le`) applied to `k(t, s) = 1_{0 < s ≤ t} (s / t) ^ θ` and its
transpose on `multHaar`, whose row and column integrals against `dt / t` both equal `θ⁻¹`.
Setting `q = p` and `θ = 1 - 1 / p` recovers Hardy's classical `Lᵖ(0, ∞)` inequality with the sharp
constant `p / (p - 1)` (`TauCeti.eLpNorm_inv_mul_lintegral_Ioc_le`). For antitone functions on
`(0, ∞)` there is an immediate pointwise lower bound giving the reverse inequality with constant
`1` (`TauCeti.eLpNorm_rpow_one_sub_le_eLpNorm_rpow_neg_mul_lintegral_Ioc`).

## Main declarations

* `TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_multHaar_le`: prefix Hardy inequality (`dt / t`).
* `TauCeti.eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le`: prefix Hardy inequality (`∫₀ᵗ φ(s) ds`).
* `TauCeti.eLpNorm_rpow_mul_setLIntegral_Ici_multHaar_le`: tail Hardy inequality (`dt / t`).
* `TauCeti.eLpNorm_rpow_mul_setLIntegral_Ici_le`: tail Hardy inequality (`∫_t^∞ φ(s) ds`).
* `TauCeti.eLpNorm_inv_mul_lintegral_Ioc_le`: Hardy's classical inequality
  `‖t ↦ t⁻¹ ∫₀ᵗ g‖_{Lᵖ(0, ∞)} ≤ q ‖g‖_{Lᵖ(0, ∞)}` for Hölder conjugate `p, q`.
* `TauCeti.eLpNorm_rpow_one_sub_le_eLpNorm_rpow_neg_mul_lintegral_Ioc`: reverse bound for functions
  antitone on `(0, ∞)`.

## References

* G. H. Hardy, *Note on a theorem of Hilbert*, Math. Z. **6** (1920), 314–317.
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
  have hae : hardyKernel θ t =ᵐ[multHaar]
      (Iic t).indicator fun s ↦ ENNReal.ofReal (t ^ (-θ)) * ENNReal.ofReal (s ^ θ) := by
    filter_upwards [ae_pos_multHaar] with s hs
    by_cases hst : s ≤ t
    · simp only [hardyKernel, ht, hs, hst, and_self, ↓reduceIte, indicator_of_mem (mem_Iic.2 hst)]
      rw [Real.div_rpow hs.le ht.le, div_eq_mul_inv, mul_comm, ← Real.rpow_neg ht.le,
        ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
    · simp [hardyKernel, hst]
  rw [lintegral_congr_ae hae, lintegral_indicator measurableSet_Iic,
    lintegral_const_mul _ (by fun_prop), lintegral_Iic_multHaar_rpow hθ ht,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), Real.rpow_neg ht.le, ← mul_assoc,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos ht θ).ne', one_mul]

private theorem lintegral_hardyKernel_col {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s) :
    ∫⁻ t, hardyKernel θ t s ∂multHaar = ENNReal.ofReal θ⁻¹ := by
  have hcongr : (fun t ↦ hardyKernel θ t s) =
      (Ici s).indicator fun t ↦ ENNReal.ofReal (s ^ θ) * ENNReal.ofReal (t ^ (-θ)) := by
    ext t
    by_cases hst : s ≤ t
    · have ht : 0 < t := hs.trans_le hst
      simp only [hardyKernel, ht, hs, hst, and_self, ↓reduceIte, indicator_of_mem (mem_Ici.2 hst)]
      rw [Real.div_rpow hs.le ht.le, div_eq_mul_inv, ← Real.rpow_neg ht.le,
        ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _)]
    · simp [hardyKernel, hst]
  rw [hcongr, lintegral_indicator measurableSet_Ici, lintegral_const_mul _ (by fun_prop),
    lintegral_Ici_multHaar_rpow_neg hθ hs, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),
    Real.rpow_neg hs.le, ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hs θ).ne', one_mul]

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
    · rw [indicator_of_notMem hs, hardyKernel, ite_eq_right fun h ↦ hs ⟨h.2.1, h.2.2⟩, zero_mul]
  rw [eLpNorm_congr_ae hae]
  exact (eLpNorm_lintegral_mul_le (measurable_uncurry_hardyKernel θ).aemeasurable hg hq
    (ae_pos_multHaar.mono fun t ht ↦ (lintegral_hardyKernel_row hθ ht).le)
    (ae_pos_multHaar.mono fun s hs ↦ (lintegral_hardyKernel_col hθ hs).le)).trans_eq <| by
      rw [mul_comm (_ ^ _), ENNReal.rpow_mul_rpow_one_sub _ (by positivity)
        (sub_nonneg.1 (by simpa only [one_div] using ENNReal.one_sub_one_div_toReal_nonneg hq))]

/-- **Prefix Hardy inequality** for Lebesgue integrals on `(0, t]`: for `θ > 0` and `1 ≤ q ≤ ∞`,
`‖t ↦ t ^ (-θ) ∫₀ᵗ φ(s) ds‖_{L^q(dt / t)} ≤ θ⁻¹ ‖s ↦ s ^ (1 - θ) φ(s)‖_{L^q(ds / s)}`. -/
theorem eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {φ : ℝ → ℝ≥0∞} (hφ : AEMeasurable φ (volume.restrict (Ioi 0))) :
    eLpNorm (fun t ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, φ s) q multHaar ≤
      ENNReal.ofReal θ⁻¹ * eLpNorm (fun s ↦ ENNReal.ofReal (s ^ (1 - θ)) * φ s) q multHaar := by
  have hφ_mh : AEMeasurable φ multHaar :=
    multHaar_def ▸ hφ.mono_ac (withDensity_absolutelyContinuous _ _)
  simp_rw [setLIntegral_eq_setLIntegral_multHaar measurableSet_Ioc Ioc_subset_Ioi_self]
  refine (eLpNorm_rpow_neg_mul_setLIntegral_Ioc_multHaar_le hθ hq
    (measurable_id.ennreal_ofReal.aemeasurable.mul hφ_mh)).trans_eq ?_
  congr 1; refine eLpNorm_congr_ae (ae_pos_multHaar.mono fun s hs ↦ ?_)
  dsimp only [Pi.mul_apply, id_eq]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _), ← Real.rpow_add_one hs.ne',
    neg_add_eq_sub]

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
    · rw [indicator_of_notMem hs, hardyKernel, ite_eq_right fun h ↦ hs h.2.2, zero_mul]
  rw [eLpNorm_congr_ae hae]
  exact (eLpNorm_lintegral_mul_le (measurable_uncurry_hardyKernel_swap θ).aemeasurable hg hq
    (ae_pos_multHaar.mono fun t ht ↦ (lintegral_hardyKernel_col hθ ht).le)
    (ae_pos_multHaar.mono fun s hs ↦ (lintegral_hardyKernel_row hθ hs).le)).trans_eq <| by
      rw [mul_comm (_ ^ _), ENNReal.rpow_mul_rpow_one_sub _ (by positivity)
        (sub_nonneg.1 (by simpa only [one_div] using ENNReal.one_sub_one_div_toReal_nonneg hq))]

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
      dsimp only; rw [setLIntegral_eq_setLIntegral_multHaar measurableSet_Ici (Ici_subset_Ioi.2 ht)]
  rw [eLpNorm_congr_ae hlhs]
  refine (eLpNorm_rpow_mul_setLIntegral_Ici_multHaar_le hθ hq
    (measurable_id.ennreal_ofReal.aemeasurable.mul hφ_mh)).trans_eq ?_
  congr 1; refine eLpNorm_congr_ae (ae_pos_multHaar.mono fun s hs ↦ ?_)
  dsimp only [Pi.mul_apply, id_eq]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _), ← Real.rpow_add_one hs.ne',
    add_comm θ 1]

/-! ### Classical Hardy inequality on `(0, ∞)` -/

/-- **Hardy's classical integral inequality on `(0, ∞)`.** For Hölder conjugate exponents `p` and
`q` (so `q = p / (p - 1)` for `1 < p < ∞`, `q = 1` for `p = ∞`, and `q = ∞` for `p = 1`) and any
`g : ℝ → ℝ≥0∞`,
`‖t ↦ t⁻¹ ∫₀ᵗ g(s) ds‖_{Lᵖ(0, ∞)} ≤ q * ‖g‖_{Lᵖ(0, ∞)}`. -/
theorem eLpNorm_inv_mul_lintegral_Ioc_le {p q : ℝ≥0∞} [hpq : ENNReal.HolderConjugate p q]
    (g : ℝ → ℝ≥0∞) :
    eLpNorm (fun t : ℝ ↦ ENNReal.ofReal t⁻¹ * ∫⁻ s in Ioc 0 t, g s) p (volume.restrict (Ioi 0)) ≤
      q * eLpNorm g p (volume.restrict (Ioi 0)) := by
  have hqp : ENNReal.HolderConjugate q p := ENNReal.HolderConjugate.symm
  rcases eq_or_ne p 1 with rfl | hp1
  · rcases eq_or_ne (eLpNorm g 1 (volume.restrict (Ioi 0))) 0 with h0 | hne
    · have hg0 : g =ᵐ[volume.restrict (Ioi 0)] 0 := (eLpNorm_eq_zero_iff one_ne_zero).1 h0
      have hzero : (fun t : ℝ ↦ ENNReal.ofReal t⁻¹ * ∫⁻ s in Ioc 0 t, g s) =ᵐ[volume.restrict
          (Ioi 0)] 0 := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
        have hg' : ∀ᵐ s ∂volume.restrict (Ioc 0 t), g s = 0 :=
          ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self hg0
        simp [lintegral_congr_ae hg']
      rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
      exact zero_le
    · have hqtop : q = ∞ := hqp.eq_top_iff_eq_one.2 rfl
      rw [hqtop, ENNReal.top_mul hne]
      exact le_top
  have hp0 : p ≠ 0 := hpq.ne_zero
  have hq0 : q ≠ 0 := hqp.ne_zero
  by_cases hg_meas : AEStronglyMeasurable g (volume.restrict (Ioi 0))
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hg_meas, ENNReal.mul_top hq0]
    exact le_top
  have hqtop : q ≠ ∞ := mt hqp.eq_top_iff_eq_one.1 hp1
  have hθ : 0 < q.toReal⁻¹ := inv_pos.2 (ENNReal.toReal_pos hq0 hqtop)
  have h1θ : 1 - q.toReal⁻¹ = p.toReal⁻¹ := by
    have hsum : p.toReal⁻¹ + q.toReal⁻¹ = 1 := by
      have hp_inv : p⁻¹ ≠ ∞ := by simpa using hp0
      have hq_inv : q⁻¹ ≠ ∞ := by simpa using hq0
      have htoReal := congrArg ENNReal.toReal hpq.inv_add_inv_eq_one
      rwa [ENNReal.toReal_add hp_inv hq_inv, ENNReal.toReal_inv, ENNReal.toReal_inv,
        ENNReal.toReal_one] at htoReal
    linarith
  have hq_eq : ENNReal.ofReal (q.toReal⁻¹)⁻¹ = q := by
    rw [inv_inv, ENNReal.ofReal_toReal hqtop]
  rw [eLpNorm_volume_Ioi_eq_eLpNorm_multHaar hp0, eLpNorm_volume_Ioi_eq_eLpNorm_multHaar hp0,
    ← h1θ]
  have hcongr : (fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 - q.toReal⁻¹)) *
        (ENNReal.ofReal t⁻¹ * ∫⁻ s in Ioc 0 t, g s)) =ᵐ[multHaar]
      fun t ↦ ENNReal.ofReal (t ^ (-q.toReal⁻¹)) * ∫⁻ s in Ioc 0 t, g s := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_neg_one t,
      ← Real.rpow_add ht]
    ring_nf
  rw [eLpNorm_congr_ae hcongr]
  simpa only [hq_eq] using
    eLpNorm_rpow_neg_mul_setLIntegral_Ioc_le hθ hpq.one_le hg_meas.aemeasurable

/-! ### Reverse bound for antitone functions -/

/-- For a function `g : ℝ → ℝ≥0∞` that is antitone on `(0, ∞)`, `t g(t) ≤ ∫₀ᵗ g(s) ds` for every
`t > 0`, and hence `t ^ (1 - θ) g(t) ≤ t ^ (-θ) ∫₀ᵗ g(s) ds`. -/
theorem rpow_one_sub_mul_le_rpow_neg_mul_lintegral_Ioc {g : ℝ → ℝ≥0∞} (hg : AntitoneOn g (Ioi 0))
    (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (1 - θ)) * g t ≤ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s := by
  calc ENNReal.ofReal (t ^ (1 - θ)) * g t
      = ENNReal.ofReal (t ^ (-θ)) * (ENNReal.ofReal t * g t) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
            ← Real.rpow_add_one ht.ne', neg_add_eq_sub]
    _ = ENNReal.ofReal (t ^ (-θ)) * ∫⁻ _ in Ioc 0 t, g t := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm (g t)]
    _ ≤ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s := by
          gcongr 1
          exact setLIntegral_mono' measurableSet_Ioc fun s hs ↦ hg hs.left ht hs.right

/-- **Reverse weighted Hardy bound for antitone functions.** If `g : ℝ → ℝ≥0∞` is antitone on
`(0, ∞)`, then for every `θ : ℝ` and every `q : ℝ≥0∞`,
`‖t ↦ t ^ (1 - θ) g(t)‖_{L^q(dt / t)} ≤ ‖t ↦ t ^ (-θ) ∫₀ᵗ g(s) ds‖_{L^q(dt / t)}`. -/
theorem eLpNorm_rpow_one_sub_le_eLpNorm_rpow_neg_mul_lintegral_Ioc {g : ℝ → ℝ≥0∞}
    (hg : AntitoneOn g (Ioi 0)) (θ : ℝ) (q : ℝ≥0∞) :
    eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 - θ)) * g t) q multHaar ≤
      eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s) q multHaar := by
  have hg_meas : AEMeasurable g multHaar :=
    multHaar_def ▸ (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi hg).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hlhs_meas : AEStronglyMeasurable
      (fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 - θ)) * g t) multHaar :=
    ((by fun_prop : Measurable fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 - θ))).aemeasurable.mul
      hg_meas).aestronglyMeasurable
  refine eLpNorm_mono_eNorm_ae hlhs_meas ?_
  filter_upwards [ae_pos_multHaar] with t ht
  simpa only [eNorm_eq_self] using rpow_one_sub_mul_le_rpow_neg_mul_lintegral_Ioc hg θ ht

end TauCeti

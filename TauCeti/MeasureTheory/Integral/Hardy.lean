/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Holder
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import TauCeti.MeasureTheory.Measure.Haar.MultHaar
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Hardy's integral inequalities

For `0 < θ`, `1 ≤ q ≤ ∞`, and any `g : ℝ → ℝ≥0∞`, the Hardy averaging operators on `(0, ∞)` satisfy
the weighted `L^q(dt / t)` bounds

`‖t ↦ t ^ (-θ) ∫₀ᵗ g(s) ds‖_{L^q(dt / t)} ≤ θ⁻¹ ‖t ↦ t ^ (1 - θ) g(t)‖_{L^q(dt / t)}`

(`TauCeti.eLpNorm_rpow_neg_mul_lintegral_Ioc_le`) and, for the tail integral,

`‖t ↦ t ^ θ ∫_t^∞ g(s) ds‖_{L^q(dt / t)} ≤ θ⁻¹ ‖t ↦ t ^ (1 + θ) g(t)‖_{L^q(dt / t)}`

(`TauCeti.eLpNorm_rpow_mul_lintegral_Ioi_le`), where `dt / t` is `TauCeti.multHaar`. Both proofs
rewrite the operator as an integral kernel against `dt / t` — with kernel `1_{s ≤ t} (s / t) ^ θ`
for the head integral and its transpose `1_{t < s} (t / s) ^ θ` for the tail integral — whose row
and column integrals against `dt / t` are both equal to `θ⁻¹`, and then apply Schur's test
(`TauCeti.eLpNorm_lintegral_mul_le`).

Setting `q = p` and `θ = 1 - 1 / p` recovers Hardy's classical `Lᵖ(0, ∞)` inequality with the sharp
constant `p / (p - 1)` (written via the Hölder conjugate exponent `q`, so that the endpoints `p = 1`
and `p = ∞` are included uniformly, `TauCeti.eLpNorm_inv_mul_lintegral_Ioc_le`). For antitone
functions on `(0, ∞)` there is an immediate pointwise lower bound giving the reverse inequality with
constant `1` (`TauCeti.eLpNorm_rpow_one_sub_le_eLpNorm_rpow_neg_mul_lintegral_Ioc`).

## Main declarations

* `TauCeti.eLpNorm_rpow_neg_mul_lintegral_Ioc_le`: weighted Hardy inequality for `∫₀ᵗ g` against
  `dt / t` for `0 < θ` and `1 ≤ q ≤ ∞`, with sharp constant `θ⁻¹`.
* `TauCeti.eLpNorm_rpow_mul_lintegral_Ioi_le`: weighted Hardy inequality for `∫_t^∞ g` against
  `dt / t` for `0 < θ` and `1 ≤ q ≤ ∞`, with sharp constant `θ⁻¹`.
* `TauCeti.eLpNorm_inv_mul_lintegral_Ioc_le`: Hardy's classical inequality
  `‖t ↦ t⁻¹ ∫₀ᵗ g‖_{Lᵖ(0, ∞)} ≤ q ‖g‖_{Lᵖ(0, ∞)}` for Hölder conjugate `p, q`.
* `TauCeti.eLpNorm_rpow_one_sub_le_eLpNorm_rpow_neg_mul_lintegral_Ioc`: reverse bound for functions
  antitone on `(0, ∞)`.

## References

* G. H. Hardy, *Note on a theorem of Hilbert*, Math. Z. **6** (1920), 314–317.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §5.3 (Lemma 5.3.1).
* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*,
  Princeton University Press, 1971, Chapter V, §3.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-! ### Weighted Hardy inequalities on `(0, ∞)` with `dt / t` -/

/-- The Hardy kernel `(t, s) ↦ 1_{s ≤ t} (s / t) ^ θ` has row integral `θ⁻¹` against `dt / t`
for every `t > 0`. -/
private theorem lintegral_hardyKernel_right {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t) :
    ∫⁻ s, (if s ≤ t then ENNReal.ofReal ((s / t) ^ θ) else 0) ∂multHaar = ENNReal.ofReal θ⁻¹ := by
  have heq : (fun s : ℝ ↦ if s ≤ t then ENNReal.ofReal ((s / t) ^ θ) else 0) =ᵐ[multHaar]
      fun s ↦ ENNReal.ofReal (t ^ (-θ)) * (Iic t).indicator (fun s ↦ ENNReal.ofReal (s ^ θ)) s := by
    filter_upwards [ae_pos_multHaar] with s hs
    by_cases hst : s ≤ t
    · simp only [hst, ↓reduceIte, indicator_of_mem (mem_Iic.2 hst)]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _),
        Real.div_rpow hs.le ht.le, Real.rpow_neg ht.le, div_eq_mul_inv, mul_comm]
    · simp [hst]
  rw [lintegral_congr_ae heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_indicator measurableSet_Iic, lintegral_Iic_multHaar_rpow hθ ht,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← mul_assoc, ← Real.rpow_add ht,
    neg_add_cancel, Real.rpow_zero, one_mul]

/-- The Hardy kernel `(t, s) ↦ 1_{s ≤ t} (s / t) ^ θ` has column integral `θ⁻¹` against `dt / t`
for every `s > 0`. -/
private theorem lintegral_hardyKernel_left {θ s : ℝ} (hθ : 0 < θ) (hs : 0 < s) :
    ∫⁻ t, (if s ≤ t then ENNReal.ofReal ((s / t) ^ θ) else 0) ∂multHaar = ENNReal.ofReal θ⁻¹ := by
  have heq : (fun t : ℝ ↦ if s ≤ t then ENNReal.ofReal ((s / t) ^ θ) else 0) =ᵐ[multHaar]
      fun t ↦ ENNReal.ofReal (s ^ θ) *
        (Ici s).indicator (fun t ↦ ENNReal.ofReal (t ^ (-θ))) t := by
    filter_upwards [ae_pos_multHaar] with t ht
    by_cases hst : s ≤ t
    · simp only [hst, ↓reduceIte, indicator_of_mem (mem_Ici.2 hst)]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),
        Real.div_rpow hs.le ht.le, Real.rpow_neg ht.le, div_eq_mul_inv]
    · simp [hst]
  rw [lintegral_congr_ae heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_indicator measurableSet_Ici, lintegral_Ici_multHaar_rpow_neg hθ hs,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _), ← mul_assoc, ← Real.rpow_add hs,
    add_neg_cancel, Real.rpow_zero, one_mul]

/-- `A ^ (1 - 1 / q) * A ^ (1 / q) = A` for positive finite `A` and `1 ≤ q ≤ ∞`. -/
private theorem rpow_one_sub_inv_mul_rpow_inv {A : ℝ≥0∞} (hA0 : A ≠ 0) (hA : A ≠ ∞) (q : ℝ≥0∞) :
    A ^ (1 - q.toReal⁻¹) * A ^ q.toReal⁻¹ = A := by
  rw [← ENNReal.rpow_add _ _ hA0 hA, sub_add_cancel, ENNReal.rpow_one]

/-- Rewriting `t ^ (-θ) ∫₀ᵗ g(s) ds` as a kernel integral against `dt / t`. -/
private theorem rpow_neg_mul_lintegral_Ioc_eq {θ t : ℝ} (ht : 0 < t) (g : ℝ → ℝ≥0∞) :
    ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s =
      ∫⁻ s, (if s ≤ t then ENNReal.ofReal ((s / t) ^ θ) else 0) *
        (ENNReal.ofReal (s ^ (1 - θ)) * g s) ∂multHaar := by
  rw [multHaar_def, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    measurable_inv.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← Ioi_inter_Iic, inter_comm, ← setLIntegral_indicator measurableSet_Iic]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_
  dsimp only [Pi.mul_apply]
  by_cases hst : s ≤ t
  · simp only [hst, ↓reduceIte, indicator_of_mem (mem_Iic.2 hst)]
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hs.le),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [Real.div_rpow hs.le ht.le, Real.rpow_sub hs, Real.rpow_one, Real.rpow_neg ht.le]
    have hsθ : s ^ θ ≠ 0 := (Real.rpow_pos_of_pos hs θ).ne'
    have htθ : t ^ θ ≠ 0 := (Real.rpow_pos_of_pos ht θ).ne'
    field_simp [hs.ne', hsθ, htθ]
  · simp [hst]

/-- **Weighted Hardy inequality (head integral).** For `0 < θ`, `1 ≤ q ≤ ∞`, and any
`g : ℝ → ℝ≥0∞`,
`‖t ↦ t ^ (-θ) ∫₀ᵗ g(s) ds‖_{L^q(dt / t)} ≤ θ⁻¹ ‖t ↦ t ^ (1 - θ) g(t)‖_{L^q(dt / t)}`.
No measurability hypothesis on `g` is needed: if the integrand on the right is not a.e. strongly
measurable then the right-hand side is `∞`. -/
theorem eLpNorm_rpow_neg_mul_lintegral_Ioc_le {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (g : ℝ → ℝ≥0∞) :
    eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s) q multHaar ≤
      ENNReal.ofReal θ⁻¹ *
        eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 - θ)) * g t) q multHaar := by
  set h : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (t ^ (1 - θ)) * g t
  by_cases hh : AEStronglyMeasurable h multHaar
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hh,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 (inv_pos.2 hθ)).ne']
    exact le_top
  set k : ℝ → ℝ → ℝ≥0∞ := fun t s ↦ if s ≤ t then ENNReal.ofReal ((s / t) ^ θ) else 0
  have hk : Measurable (Function.uncurry k) :=
    Measurable.ite (measurableSet_le measurable_snd measurable_fst)
      (((measurable_snd.div measurable_fst).pow_const θ).ennreal_ofReal) measurable_const
  have heq : (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s) =ᵐ[multHaar]
      fun t ↦ ∫⁻ s, k t s * h s ∂multHaar := by
    filter_upwards [ae_pos_multHaar] with t ht
    exact rpow_neg_mul_lintegral_Ioc_eq ht g
  rw [eLpNorm_congr_ae heq]
  have hschur := eLpNorm_lintegral_mul_le (μ := multHaar) (ν := multHaar) hk.aemeasurable
    hh.aemeasurable hq
    (ae_pos_multHaar.mono fun t ht ↦ (lintegral_hardyKernel_right hθ ht).le)
    (ae_pos_multHaar.mono fun s hs ↦ (lintegral_hardyKernel_left hθ hs).le)
  rwa [rpow_one_sub_inv_mul_rpow_inv (ENNReal.ofReal_pos.2 (inv_pos.2 hθ)).ne'
    ENNReal.ofReal_ne_top] at hschur

/-- Rewriting `t ^ θ ∫_t^∞ g(s) ds` as a kernel integral against `dt / t`. -/
private theorem rpow_mul_lintegral_Ioi_eq {θ t : ℝ} (ht : 0 < t) (g : ℝ → ℝ≥0∞) :
    ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ioi t, g s =
      ∫⁻ s, (if t < s then ENNReal.ofReal ((t / s) ^ θ) else 0) *
        (ENNReal.ofReal (s ^ (1 + θ)) * g s) ∂multHaar := by
  have hinter : Ioi t = Ioi t ∩ Ioi 0 := by rw [Ioi_inter_Ioi, max_eq_left ht.le]
  rw [multHaar_def, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    measurable_inv.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hinter,
    ← setLIntegral_indicator measurableSet_Ioi]
  refine setLIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_
  dsimp only [Pi.mul_apply]
  by_cases hts : t < s
  · simp only [hts, ↓reduceIte, indicator_of_mem (mem_Ioi.2 hts)]
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hs.le),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [Real.div_rpow ht.le hs.le, Real.rpow_add hs, Real.rpow_one]
    have hsθ : s ^ θ ≠ 0 := (Real.rpow_pos_of_pos hs θ).ne'
    field_simp [hs.ne', hsθ]
  · simp [hts]

/-- **Weighted Hardy inequality (tail integral).** For `0 < θ`, `1 ≤ q ≤ ∞`, and any
`g : ℝ → ℝ≥0∞`,
`‖t ↦ t ^ θ ∫_t^∞ g(s) ds‖_{L^q(dt / t)} ≤ θ⁻¹ ‖t ↦ t ^ (1 + θ) g(t)‖_{L^q(dt / t)}`.
No measurability hypothesis on `g` is needed. -/
theorem eLpNorm_rpow_mul_lintegral_Ioi_le {θ : ℝ} (hθ : 0 < θ) {q : ℝ≥0∞} (hq : 1 ≤ q)
    (g : ℝ → ℝ≥0∞) :
    eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ioi t, g s) q multHaar ≤
      ENNReal.ofReal θ⁻¹ *
        eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 + θ)) * g t) q multHaar := by
  set h : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (t ^ (1 + θ)) * g t
  by_cases hh : AEStronglyMeasurable h multHaar
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hh,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 (inv_pos.2 hθ)).ne']
    exact le_top
  set k : ℝ → ℝ → ℝ≥0∞ := fun t s ↦ if t < s then ENNReal.ofReal ((t / s) ^ θ) else 0
  have hk : Measurable (Function.uncurry k) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      (((measurable_fst.div measurable_snd).pow_const θ).ennreal_ofReal) measurable_const
  have hrow : ∀ t : ℝ, 0 < t → ∫⁻ s, k t s ∂multHaar ≤ ENNReal.ofReal θ⁻¹ := fun t ht ↦ by
    rw [← lintegral_hardyKernel_left hθ ht]
    refine lintegral_mono fun s ↦ ?_
    by_cases hts : t < s
    · simp [k, hts, hts.le]
    · simp [k, hts]
  have hcol : ∀ s : ℝ, 0 < s → ∫⁻ t, k t s ∂multHaar ≤ ENNReal.ofReal θ⁻¹ := fun s hs ↦ by
    rw [← lintegral_hardyKernel_right hθ hs]
    refine lintegral_mono fun t ↦ ?_
    by_cases hts : t < s
    · simp [k, hts, hts.le]
    · simp [k, hts]
  have heq : (fun t : ℝ ↦ ENNReal.ofReal (t ^ θ) * ∫⁻ s in Ioi t, g s) =ᵐ[multHaar]
      fun t ↦ ∫⁻ s, k t s * h s ∂multHaar := by
    filter_upwards [ae_pos_multHaar] with t ht
    exact rpow_mul_lintegral_Ioi_eq ht g
  rw [eLpNorm_congr_ae heq]
  have hschur := eLpNorm_lintegral_mul_le (μ := multHaar) (ν := multHaar) hk.aemeasurable
    hh.aemeasurable hq
    (ae_pos_multHaar.mono hrow) (ae_pos_multHaar.mono hcol)
  rwa [rpow_one_sub_inv_mul_rpow_inv (ENNReal.ofReal_pos.2 (inv_pos.2 hθ)).ne'
    ENNReal.ofReal_ne_top] at hschur

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
  simpa only [hq_eq] using eLpNorm_rpow_neg_mul_lintegral_Ioc_le hθ hpq.one_le g

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
          exact setLIntegral_mono' measurableSet_Ioc fun s hs ↦ hg hs.1 ht hs.2

/-- **Reverse weighted Hardy bound for antitone functions.** If `g : ℝ → ℝ≥0∞` is antitone on
`(0, ∞)`, then for every `θ : ℝ` and every `q : ℝ≥0∞`,
`‖t ↦ t ^ (1 - θ) g(t)‖_{L^q(dt / t)} ≤ ‖t ↦ t ^ (-θ) ∫₀ᵗ g(s) ds‖_{L^q(dt / t)}`. -/
theorem eLpNorm_rpow_one_sub_le_eLpNorm_rpow_neg_mul_lintegral_Ioc {g : ℝ → ℝ≥0∞}
    (hg : AntitoneOn g (Ioi 0)) (θ : ℝ) (q : ℝ≥0∞) :
    eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 - θ)) * g t) q multHaar ≤
      eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-θ)) * ∫⁻ s in Ioc 0 t, g s) q multHaar := by
  -- Extending `g` by `⊤` on `(-∞, 0]` produces a globally antitone, hence measurable, modification.
  set g' : ℝ → ℝ≥0∞ := fun t ↦ if 0 < t then g t else ⊤
  have hg'_anti : Antitone g' := fun a b hab ↦ by
    by_cases ha : 0 < a
    · have hb : 0 < b := ha.trans_le hab
      simpa [g', ha, hb] using hg ha hb hab
    · simp [g', ha]
  have hg_meas : AEMeasurable g multHaar :=
    hg'_anti.measurable.aemeasurable.congr (ae_pos_multHaar.mono fun t ht ↦ by simp [g', ht])
  have hlhs_meas : AEStronglyMeasurable
      (fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 - θ)) * g t) multHaar :=
    ((by fun_prop : Measurable fun t : ℝ ↦ ENNReal.ofReal (t ^ (1 - θ))).aemeasurable.mul
      hg_meas).aestronglyMeasurable
  refine eLpNorm_mono_eNorm_ae hlhs_meas ?_
  filter_upwards [ae_pos_multHaar] with t ht
  simpa only [eNorm_eq_self] using rpow_one_sub_mul_le_rpow_neg_mul_lintegral_Ioc hg θ ht

end TauCeti

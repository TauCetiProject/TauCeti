/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.DeLaValleePoussin
public import TauCeti.Probability.Renewal.Measure
public import TauCeti.Probability.Renewal.StrongLaw
import TauCeti.Probability.Independence.InfinitePi

/-!
# The elementary renewal theorem

Let `T 0, T 1, …` be independent, identically distributed nonnegative increments that are not
almost surely zero, with extended mean `μ = 𝔼[T 0] ∈ (0, ∞]` and rate `r = (μ⁻¹).toReal`, so that
`r = 0` when the mean is infinite. The almost-sure renewal law of large numbers
(`TauCeti.Probability.ae_tendsto_renewalCountNat_div`) says that `N t / t → r` almost surely. This
file upgrades it to convergence in `L¹` and deduces the **elementary renewal theorem**: the renewal
function `m t = 𝔼[N t]` satisfies `m t / t → r` as `t → ∞`, also when the mean is infinite.

The upgrade is Vitali's convergence theorem. The family `N t / t`, `t ≥ 1`, is uniformly
integrable because its second moments are bounded: `𝔼[(N t) ^ 2]` grows at most quadratically in
`t` (`TauCeti.Probability.exists_lintegral_renewalCount_pow_le`), and a family bounded in `L²` is
uniformly integrable by the de la Vallée Poussin criterion. Mathlib's Vitali theorem is stated for
sequences, and the continuous-time limit follows by testing along every sequence of times tending
to infinity.

## Main results

* `TauCeti.Probability.uniformIntegrable_renewalCountNat_div` — the family `N t / t`, `t ≥ 1`, is
  uniformly integrable.
* `TauCeti.Probability.tendsto_eLpNorm_renewalCountNat_div_sub` — `N t / t → r` in `L¹`.
* `TauCeti.Probability.tendsto_integral_renewalCountNat_div` — `𝔼[N t] / t → r`.
* `MeasureTheory.Measure.tendsto_renewalFunction_div` — **the elementary renewal theorem**
  `m t / t → r` for the renewal function of a probability measure on `ℝ≥0` other than the point
  mass at zero.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : ℕ → Ω → ℝ≥0}

/-- The second moments of `N t / t` are bounded uniformly in `t ≥ 1`. -/
private theorem exists_lintegral_renewalCountNat_div_sq_le (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) :
    ∃ C : ℝ≥0, ∀ t : ℝ≥0, 1 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (‖(renewalCountNat T t ω : ℝ) / t‖ ^ 2) ∂P ≤ C := by
  obtain ⟨C, hC⟩ := exists_lintegral_renewalCount_pow_le hT hindep hid hzero 2
  refine ⟨4 * C, fun t ht ↦ ?_⟩
  have ht0 : (t : ℝ≥0∞) ^ 2 ≠ 0 := pow_ne_zero 2 (by simpa using (zero_lt_one.trans_le ht).ne')
  have htop : (t : ℝ≥0∞) ^ 2 ≠ ∞ := by finiteness
  have hpt (ω : Ω) : ENNReal.ofReal (‖(renewalCountNat T t ω : ℝ) / t‖ ^ 2) ≤
      ((t : ℝ≥0∞) ^ 2)⁻¹ * renewalCount T t ω ^ 2 := by
    rw [Real.norm_of_nonneg (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_div_of_pos (by simpa using zero_lt_one.trans_le ht), ENNReal.ofReal_natCast,
      ENNReal.ofReal_coe_nnreal, ENNReal.div_eq_inv_mul, mul_pow, ENNReal.inv_pow]
    gcongr
    exact natCast_renewalCountNat_le T t ω
  have h2t : ((t + 1 : ℝ≥0) : ℝ≥0∞) ≤ 2 * t := by
    have : t + 1 ≤ 2 * t := by
      rw [two_mul]
      gcongr
    exact_mod_cast this
  calc ∫⁻ ω, ENNReal.ofReal (‖(renewalCountNat T t ω : ℝ) / t‖ ^ 2) ∂P
      ≤ ∫⁻ ω, ((t : ℝ≥0∞) ^ 2)⁻¹ * renewalCount T t ω ^ 2 ∂P := lintegral_mono hpt
    _ = ((t : ℝ≥0∞) ^ 2)⁻¹ * ∫⁻ ω, renewalCount T t ω ^ 2 ∂P :=
        lintegral_const_mul _ ((measurable_renewalCount hT t).pow_const 2)
    _ ≤ ((t : ℝ≥0∞) ^ 2)⁻¹ * (C * (2 * t) ^ 2) := by
        gcongr
        exact (hC t).trans (by gcongr)
    _ = ((t : ℝ≥0∞) ^ 2)⁻¹ * (t : ℝ≥0∞) ^ 2 * (4 * C) := by ring
    _ = ↑(4 * C) := by
        rw [ENNReal.inv_mul_cancel ht0 htop, one_mul, ENNReal.coe_mul, ENNReal.coe_ofNat]

/-- **Uniform integrability of the renewal counts per unit time.** For independent, identically
distributed increments that are not almost surely zero, the family `N t / t`, `t ≥ 1`, is
uniformly integrable. No assumption is made on the mean of the increments. -/
theorem uniformIntegrable_renewalCountNat_div (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) :
    UniformIntegrable (fun (t : Ici (1 : ℝ≥0)) ω ↦ (renewalCountNat T t ω : ℝ) / t) 1 P := by
  have := hindep.isProbabilityMeasure
  obtain ⟨C, hC⟩ := exists_lintegral_renewalCountNat_div_sq_le hT hindep hid hzero
  have hm (t : Ici (1 : ℝ≥0)) :
      AEStronglyMeasurable (fun ω ↦ (renewalCountNat T t ω : ℝ) / t) P := by
    have := measurable_renewalCountNat hT t
    fun_prop
  have hΦ : Tendsto (fun x : ℝ ↦ x ^ 2 / x) atTop atTop :=
    tendsto_id.congr fun x ↦ by simp only [id, sq, mul_self_div_self]
  have hu : UnifIntegrable (fun (t : Ici (1 : ℝ≥0)) ω ↦ (renewalCountNat T t ω : ℝ) / t) 1 P :=
    unifIntegrable_of_lintegral_ofReal_le hΦ hm ENNReal.coe_ne_top fun t ↦ hC t t.2
  refine ⟨hu, 1 + C, fun t ↦ ?_⟩
  -- The bound `x ≤ 1 + x ^ 2` turns the second-moment bound into a first-moment bound.
  have hsq (x : ℝ) : x ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  rw [eLpNorm_one_eq_lintegral_enorm (hm t)]
  calc ∫⁻ ω, ‖(renewalCountNat T t ω : ℝ) / t‖ₑ ∂P
      ≤ ∫⁻ ω, 1 + ENNReal.ofReal (‖(renewalCountNat T t ω : ℝ) / t‖ ^ 2) ∂P := by
        refine lintegral_mono fun ω ↦ ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hsq _)
    _ = 1 + ∫⁻ ω, ENNReal.ofReal (‖(renewalCountNat T t ω : ℝ) / t‖ ^ 2) ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 1 + C := by gcongr; exact hC t t.2
    _ = ↑(1 + C) := by rw [ENNReal.coe_add, ENNReal.coe_one]

/-- **The renewal law of large numbers in `L¹`.** For independent, identically distributed
increments that are not almost surely zero, `N t / t` converges in `L¹` to the reciprocal of the
extended mean increment, with rate zero for infinite mean. -/
theorem tendsto_eLpNorm_renewalCountNat_div_sub (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) :
    Tendsto (fun t : ℝ≥0 ↦ eLpNorm (fun ω ↦ (renewalCountNat T t ω : ℝ) / t -
      (∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P)⁻¹.toReal) 1 P) atTop (𝓝 0) := by
  have := hindep.isProbabilityMeasure
  have hui := uniformIntegrable_renewalCountNat_div hT hindep hid hzero
  have hlim := ae_tendsto_renewalCountNat_div (fun _ _ hij ↦ hindep.indepFun hij) hid hzero
  refine tendsto_of_seq_tendsto fun x hx ↦ ?_
  -- Vitali's theorem applies along the times `max (x n) 1 ≥ 1`, which eventually equal `x n`.
  let y (n : ℕ) : Ici (1 : ℝ≥0) := ⟨max (x n) 1, le_max_right _ _⟩
  have hy : Tendsto (fun n ↦ (y n : ℝ≥0)) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ le_max_left _ _) hx
  have hvitali := tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
    (f := fun n ω ↦ (renewalCountNat T (y n) ω : ℝ) / (y n : ℝ≥0))
    (fun n ↦ by have := measurable_renewalCountNat hT (y n : ℝ≥0); fun_prop)
    (memLp_const _) (hui.1.comp y) (hlim.mono fun ω hω ↦ hω.comp hy)
  refine hvitali.congr' ?_
  filter_upwards [hx.eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply, y, max_eq_left hn, Pi.sub_def]

/-- **The elementary renewal theorem**, on any realization of the increments: for independent,
identically distributed increments that are not almost surely zero, the expected count per unit
time converges to the reciprocal of the extended mean increment, with rate zero for infinite
mean. -/
theorem tendsto_integral_renewalCountNat_div (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) :
    Tendsto (fun t : ℝ≥0 ↦ (∫ ω, (renewalCountNat T t ω : ℝ) ∂P) / t) atTop
      (𝓝 (∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P)⁻¹.toReal) := by
  have := hindep.isProbabilityMeasure
  set r := (∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P)⁻¹.toReal
  have hint : ∀ t : ℝ≥0, Integrable (fun ω ↦ (renewalCountNat T t ω : ℝ) / t) P := fun t ↦
    ((integrable_toReal_renewalCount hT hindep hid hzero t).congr <| by
      filter_upwards [ae_natCast_renewalCountNat hT hindep hid hzero] with ω hω
      rw [← hω t, ENNReal.toReal_natCast]).div_const _
  have h := tendsto_integral_of_L1' (fun _ ↦ r) (Eventually.of_forall hint)
    (tendsto_eLpNorm_renewalCountNat_div_sub hT hindep hid hzero)
  simpa only [integral_div, integral_const, probReal_univ, one_smul] using h

end TauCeti.Probability

namespace MeasureTheory.Measure

/-- **The elementary renewal theorem.** For a probability measure `μ` on `ℝ≥0` other than the
point mass at zero, the renewal function satisfies `m t / t → (𝔼 μ)⁻¹` as `t → ∞`, where the
reciprocal of the extended mean is taken before conversion to a real number, so that the limit is
zero for infinite mean. -/
theorem tendsto_renewalFunction_div (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (hμ : μ {0} < 1) :
    Tendsto (fun t : ℝ≥0 ↦ (μ.renewalFunction t).toReal / t) atTop
      (𝓝 (∫⁻ x, (x : ℝ≥0∞) ∂μ)⁻¹.toReal) := by
  -- Realize i.i.d. increments with law `μ` as the coordinates of the product measure.
  set P := Measure.infinitePi fun _ : ℕ ↦ μ
  have hT : ∀ n, Measurable fun w : ℕ → ℝ≥0 ↦ w n := measurable_pi_apply
  have hindep : iIndepFun _ P := TauCeti.Probability.iIndepFun_eval_infinitePi _
  have hid (n : ℕ) : IdentDistrib _ _ P P := μ.identDistrib_eval_infinitePi n 0
  have hmap : ∀ n, P.map (fun w ↦ w n) = μ := fun n ↦ infinitePi_map_eval _ n
  have hzero : P {w | w 0 = 0} < 1 := by
    rwa [← hmap 0, map_apply (hT 0) (measurableSet_singleton 0)] at hμ
  have h := TauCeti.Probability.tendsto_integral_renewalCountNat_div hT hindep hid hzero
  simp_rw [TauCeti.Probability.integral_renewalCountNat hT hindep hid hzero, hmap] at h
  rwa [← lintegral_map (by fun_prop) (hT 0), hmap] at h

end MeasureTheory.Measure

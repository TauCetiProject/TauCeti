/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.Normed.Interpolation.KFunctional
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# The real interpolation method

For a compatible couple `(X₀, X₁)`, `0 < θ < 1` and `1 ≤ q ≤ ∞`, the real interpolation space
`(X₀, X₁)_{θ,q}` of the `K`-method consists of the elements `u` of the sum space `X₀ + X₁` with

`‖u‖_{θ,q} = ‖t ↦ t^(-θ) K(t, u)‖_{L^q((0, ∞), dt / t)} < ∞`,

where `K(t, u) = inf {‖x₀‖ + t ‖x₁‖ | u = x₀ + x₁}` is Peetre's `K`-functional.

We compute the `L^q(dt / t)` norm in the logarithmic variable `t = e^s`, which carries `dt / t`
on `(0, ∞)` to Lebesgue measure on `ℝ`: the norm is the `L^q(ℝ)` norm of
`s ↦ e^(-θ s) K(e^s, u)` (`CompatibleCouple.weightedKFunctional`). For finite `q` this agrees
with the `dt / t` integral (`CompatibleCouple.realInterpENorm_eq_lintegral`), and in this variable
the dilations `t ↦ λ t` used by the interpolation theorem become translations.

## Main declarations

* `TauCeti.CompatibleCouple.realInterpENorm`: the extended norm `‖u‖_{θ,q}` on the sum space.
* `TauCeti.CompatibleCouple.RealInterpSpace`: the space `(X₀, X₁)_{θ,q}`, a normed space for
  `1 ≤ q`.
* `TauCeti.CompatibleCouple.realInterpConst`: the constant `‖t ↦ t^(-θ) min 1 t‖_{L^q(dt/t)}`,
  finite and positive for `0 < θ < 1`. For the couple `(X, X)` the `(θ, q)`-norm is this
  constant times the norm of `X` (`realInterpENorm_refl`).
* `RealInterpSpace.toSumL`, `RealInterpSpace.ofInter`: the continuous inclusions
  `X₀ ∩ X₁ → (X₀, X₁)_{θ,q} → X₀ + X₁`, with norms controlled by `realInterpConst`.
* `RealInterpSpace.completeSpace`: `(X₀, X₁)_{θ,q}` is a Banach space when `X₀` and `X₁` are.
* `realInterpENorm_map_le`, `RealInterpSpace.map`, `RealInterpSpace.norm_map_le`: the
  interpolation theorem. A map of couples whose restrictions to `X₀` and `X₁` have norms at most
  `M₀` and `M₁` induces a map of the real interpolation spaces of norm at most
  `M₀ ^ (1 - θ) * M₁ ^ θ`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §3.1 (Theorem 3.1.2) and Theorem 3.4.2(a).
-/

public noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti

namespace CompatibleCouple

variable {𝕜 X₀ X₁ V : Type*} [NormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousAdd V]
  (C : CompatibleCouple 𝕜 X₀ X₁ V)

/-! ### The weighted `K`-functional -/

/-- The function `s ↦ e^(-θ s) K(e^s, u)`. It is `t ↦ t^(-θ) K(t, u)` in the logarithmic variable
`t = e^s`, which carries the measure `dt / t` on `(0, ∞)` to Lebesgue measure on `ℝ`. -/
def weightedKFunctional (θ : ℝ) (u : C.SumSpace) (s : ℝ) : ℝ :=
  Real.exp (-θ * s) * C.kFunctional (Real.exp s) u

variable {C} {θ : ℝ} {q : ℝ≥0∞}

theorem weightedKFunctional_nonneg (θ : ℝ) (u : C.SumSpace) (s : ℝ) :
    0 ≤ C.weightedKFunctional θ u s :=
  mul_nonneg (Real.exp_pos _).le (kFunctional_nonneg (Real.exp_pos s).le)

theorem measurable_weightedKFunctional (θ : ℝ) (u : C.SumSpace) :
    Measurable (C.weightedKFunctional θ u) := by
  have hK : Monotone fun s => C.kFunctional (Real.exp s) u := fun a b hab =>
    kFunctional_mono (Real.exp_pos a).le (Real.exp_le_exp.2 hab) u
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.mul
    hK.measurable

theorem aestronglyMeasurable_weightedKFunctional (θ : ℝ) (u : C.SumSpace) :
    AEStronglyMeasurable (C.weightedKFunctional θ u) volume :=
  (measurable_weightedKFunctional θ u).aestronglyMeasurable

@[simp]
theorem weightedKFunctional_zero (θ : ℝ) : C.weightedKFunctional θ 0 = 0 := by
  ext s
  simp [weightedKFunctional, kFunctional_zero (Real.exp_pos s).le]

theorem weightedKFunctional_add_le (θ : ℝ) (u v : C.SumSpace) (s : ℝ) :
    C.weightedKFunctional θ (u + v) s ≤
      C.weightedKFunctional θ u s + C.weightedKFunctional θ v s := by
  simp only [weightedKFunctional, ← mul_add]
  exact mul_le_mul_of_nonneg_left (kFunctional_add_le (Real.exp_pos s).le u v)
    (Real.exp_pos _).le

theorem weightedKFunctional_smul (θ : ℝ) (c : 𝕜) (u : C.SumSpace) :
    C.weightedKFunctional θ (c • u) = ‖c‖ • C.weightedKFunctional θ u := by
  ext s
  simp only [weightedKFunctional, kFunctional_smul (Real.exp_pos s).le, Pi.smul_apply,
    smul_eq_mul]
  ring

@[simp]
theorem weightedKFunctional_neg (θ : ℝ) (u : C.SumSpace) :
    C.weightedKFunctional θ (-u) = C.weightedKFunctional θ u := by
  ext s
  simp [weightedKFunctional, kFunctional_neg (Real.exp_pos s).le]

theorem continuous_weightedKFunctional (θ s : ℝ) :
    Continuous fun u : C.SumSpace => C.weightedKFunctional θ u s :=
  continuous_const.mul (continuous_kFunctional (Real.exp_pos s).le)

/-! ### The interpolation constant -/

/-- The constant `‖t ↦ t^(-θ) min 1 t‖_{L^q(dt/t)}`, computed in the variable `t = e^s`. Since
`min 1 t * ‖u‖ ≤ K(t, u)`, with equality for the couple `(X, X)`, it controls the inclusions
`X₀ ∩ X₁ → (X₀, X₁)_{θ,q} → X₀ + X₁`. It is positive for `q ≠ 0` and finite for `0 < θ < 1`. -/
def realInterpConst (θ : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm (fun s : ℝ => Real.exp (-θ * s) * min 1 (Real.exp s)) q volume

private lemma measurable_realInterpWeight (θ : ℝ) :
    Measurable fun s : ℝ => Real.exp (-θ * s) * min 1 (Real.exp s) :=
  ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (continuous_const.min Real.continuous_exp)).measurable

theorem realInterpConst_pos (hq : q ≠ 0) : 0 < realInterpConst θ q := by
  refine pos_iff_ne_zero.2 fun h => ?_
  rw [realInterpConst, eLpNorm_eq_zero_iff hq] at h
  obtain ⟨s, hs⟩ := h.exists
  exact (mul_pos (Real.exp_pos _) (lt_min one_pos (Real.exp_pos s))).ne' hs

private lemma realInterpWeight_le (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (s : ℝ) :
    Real.exp (-θ * s) * min 1 (Real.exp s) ≤ Real.exp (-(min θ (1 - θ) * |s|)) := by
  have h₀ := min_le_left θ (1 - θ)
  have h₁ := min_le_right θ (1 - θ)
  rcases le_total 0 s with hs | hs
  · rw [min_eq_left (Real.one_le_exp hs), mul_one, abs_of_nonneg hs]
    exact Real.exp_le_exp.2 (by nlinarith)
  · rw [min_eq_right (Real.exp_le_one_iff.2 hs), ← Real.exp_add, abs_of_nonpos hs]
    exact Real.exp_le_exp.2 (by nlinarith)

theorem realInterpConst_lt_top (hθ₀ : 0 < θ) (hθ₁ : θ < 1) : realInterpConst θ q < ∞ := by
  refine ((memLp_exp_neg_mul_abs (lt_min hθ₀ (sub_pos.2 hθ₁)) q).of_le
    (measurable_realInterpWeight θ).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)).eLpNorm_lt_top
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (le_min zero_le_one
    (Real.exp_pos s).le)), Real.norm_of_nonneg (Real.exp_pos _).le]
  exact realInterpWeight_le hθ₀ hθ₁ s

theorem realInterpConst_toReal_pos (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hq : q ≠ 0) :
    0 < (realInterpConst θ q).toReal :=
  ENNReal.toReal_pos (realInterpConst_pos hq).ne' (realInterpConst_lt_top hθ₀ hθ₁).ne

/-- At `θ = 1 / 2` and `q = 2` the constant is `√2`: in the variable `t`,
`∫₀^∞ (t^(-1/2) min 1 t)² dt / t = ∫₀¹ dt + ∫₁^∞ t^(-2) dt = 2`. For the couple `(X, X)` the
`(1/2, 2)`-norm is therefore `√2` times the norm of `X` (`realInterpENorm_refl`). -/
theorem realInterpConst_half_two : realInterpConst (1 / 2) 2 = ENNReal.ofReal (Real.sqrt 2) := by
  have hsq (s b : ℝ) (hb : b = 2 * (-(1 / 2) * s + min 0 s)) :
      ‖Real.exp (-(1 / 2) * s) * min 1 (Real.exp s)‖ₑ ^ (2 : ℝ≥0∞).toReal =
        ENNReal.ofReal (Real.exp b) := by
    have hmin : min 1 (Real.exp s) = Real.exp (min 0 s) := by
      rw [Real.exp_monotone.map_min, Real.exp_zero]
    rw [hmin, ← Real.exp_add, ENNReal.toReal_ofNat, Real.enorm_of_nonneg (Real.exp_pos _).le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le zero_le_two, ← Real.exp_mul, hb]
    congr 2
    ring
  have hlint : ∫⁻ s : ℝ, ‖Real.exp (-(1 / 2) * s) * min 1 (Real.exp s)‖ₑ ^ (2 : ℝ≥0∞).toReal =
      2 := by
    rw [← lintegral_add_compl _ (measurableSet_Iic (a := (0 : ℝ))), compl_Iic,
      setLIntegral_congr_fun measurableSet_Iic fun s (hs : s ≤ 0) =>
        hsq s s (by rw [min_eq_right hs]; ring),
      setLIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) =>
        hsq s (-s) (by rw [min_eq_left hs.le]; ring),
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_Iic 0)
        (Eventually.of_forall fun _ => (Real.exp_pos _).le),
      ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
        (Eventually.of_forall fun _ => (Real.exp_pos _).le),
      integral_exp_Iic_zero, integral_exp_neg_Ioi_zero]
    norm_num
  rw [realInterpConst, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    (measurable_realInterpWeight _).aestronglyMeasurable, hlint, ENNReal.toReal_ofNat,
    Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg zero_le_two (by norm_num),
    ENNReal.ofReal_ofNat]

/-! ### The extended `(θ, q)`-norm on the sum space -/

variable (C) in
/-- The extended real interpolation norm `‖u‖_{θ,q} = ‖t ↦ t^(-θ) K(t, u)‖_{L^q(dt/t)}` on the sum
space, computed in the variable `t = e^s` as the `L^q(ℝ)` norm of `weightedKFunctional θ u`. -/
def realInterpENorm (θ : ℝ) (q : ℝ≥0∞) (u : C.SumSpace) : ℝ≥0∞ :=
  eLpNorm (C.weightedKFunctional θ u) q volume

/-- For finite `q ≠ 0`, `‖u‖_{θ,q}^q` is the integral of `(t^(-θ) K(t, u))^q` against
`dt / t` on `(0, ∞)`. -/
theorem realInterpENorm_eq_lintegral (hq₀ : q ≠ 0) (hq : q ≠ ∞) (u : C.SumSpace) :
    C.realInterpENorm θ q u =
      (∫⁻ t in Ioi 0, ENNReal.ofReal ((t ^ (-θ) * C.kFunctional t u) ^ q.toReal / t)) ^
        (1 / q.toReal) := by
  rw [realInterpENorm, eLpNorm_eq_lintegral_rpow_enorm_toReal hq₀ hq
    (aestronglyMeasurable_weightedKFunctional θ u)]
  congr 1
  rw [← Real.range_exp, ← image_univ, lintegral_image_eq_lintegral_abs_deriv_mul
    MeasurableSet.univ (fun s _ => (Real.hasDerivAt_exp s).hasDerivWithinAt)
    Real.exp_injective.injOn, Measure.restrict_univ]
  refine lintegral_congr fun s => ?_
  have hK := kFunctional_nonneg (C := C) (Real.exp_pos s).le (u := u)
  rw [abs_of_pos (Real.exp_pos s), ← ENNReal.ofReal_mul (Real.exp_pos s).le,
    mul_div_cancel₀ _ (Real.exp_pos s).ne', ← Real.exp_mul, mul_comm s,
    Real.enorm_of_nonneg (weightedKFunctional_nonneg θ u s),
    ENNReal.ofReal_rpow_of_nonneg (weightedKFunctional_nonneg θ u s) ENNReal.toReal_nonneg,
    weightedKFunctional]

@[simp]
theorem realInterpENorm_zero (θ : ℝ) (q : ℝ≥0∞) : C.realInterpENorm θ q 0 = 0 := by
  simp [realInterpENorm]

theorem realInterpENorm_add_le (hq : 1 ≤ q) (u v : C.SumSpace) :
    C.realInterpENorm θ q (u + v) ≤ C.realInterpENorm θ q u + C.realInterpENorm θ q v := by
  refine (eLpNorm_mono_real (aestronglyMeasurable_weightedKFunctional θ _) fun s => ?_).trans
    (eLpNorm_add_le hq)
  rw [Real.norm_of_nonneg (weightedKFunctional_nonneg θ _ s), Pi.add_apply]
  exact weightedKFunctional_add_le θ u v s

theorem realInterpENorm_smul (c : 𝕜) (u : C.SumSpace) :
    C.realInterpENorm θ q (c • u) = ‖c‖ₑ * C.realInterpENorm θ q u := by
  rw [realInterpENorm, weightedKFunctional_smul, eLpNorm_const_smul, enorm_norm, realInterpENorm]

@[simp]
theorem realInterpENorm_neg (u : C.SumSpace) :
    C.realInterpENorm θ q (-u) = C.realInterpENorm θ q u := by
  simp [realInterpENorm]

theorem realInterpENorm_sub_comm (u v : C.SumSpace) :
    C.realInterpENorm θ q (u - v) = C.realInterpENorm θ q (v - u) := by
  rw [← neg_sub, realInterpENorm_neg]

theorem realInterpENorm_eq_zero_iff [T1Space V] (hq : q ≠ 0) {u : C.SumSpace} :
    C.realInterpENorm θ q u = 0 ↔ u = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ realInterpENorm_zero θ q⟩
  rw [realInterpENorm, eLpNorm_eq_zero_iff hq] at h
  obtain ⟨s, hs⟩ := h.exists
  rw [Pi.zero_apply, weightedKFunctional, mul_eq_zero, or_iff_right (Real.exp_pos _).ne'] at hs
  exact (kFunctional_eq_zero_iff (Real.exp_pos s)).1 hs

/-- Fatou's lemma for the `(θ, q)`-norm: if `v m → w` in the sum space, then
`‖u - w‖_{θ,q} ≤ liminf ‖u - v m‖_{θ,q}`. -/
theorem realInterpENorm_sub_le_liminf {v : ℕ → C.SumSpace} {w : C.SumSpace}
    (hv : Tendsto v atTop (𝓝 w)) (u : C.SumSpace) :
    C.realInterpENorm θ q (u - w) ≤ atTop.liminf fun m => C.realInterpENorm θ q (u - v m) :=
  Lp.eLpNorm_lim_le_liminf_eLpNorm (fun _ => aestronglyMeasurable_weightedKFunctional θ _) _
    (aestronglyMeasurable_weightedKFunctional θ _) (Eventually.of_forall fun s =>
      ((continuous_weightedKFunctional θ s).tendsto _).comp (tendsto_const_nhds.sub hv))

/-- The sum norm is controlled by the `(θ, q)`-norm: `c_{θ,q} ‖u‖ ≤ ‖u‖_{θ,q}`, where
`c_{θ,q} = realInterpConst θ q`. -/
theorem realInterpConst_mul_enorm_le (u : C.SumSpace) :
    realInterpConst θ q * ‖u‖ₑ ≤ C.realInterpENorm θ q u := by
  rw [mul_comm, ← enorm_norm, realInterpConst, ← eLpNorm_const_smul]
  refine eLpNorm_mono_real ((measurable_realInterpWeight θ).const_smul _).aestronglyMeasurable
    fun s => ?_
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_norm, Real.norm_of_nonneg (mul_nonneg
    (Real.exp_pos _).le (le_min zero_le_one (Real.exp_pos s).le)), weightedKFunctional,
    mul_left_comm, mul_comm ‖u‖]
  exact mul_le_mul_of_nonneg_left (min_one_mul_norm_le_kFunctional (Real.exp_pos s).le u)
    (Real.exp_pos _).le

/-- The `(θ, q)`-norm of an element of the intersection is controlled by its intersection norm:
`‖x‖_{θ,q} ≤ c_{θ,q} ‖x‖`, where `c_{θ,q} = realInterpConst θ q`. -/
theorem realInterpENorm_fstToSum_interFst_le (x : C.inter) :
    C.realInterpENorm θ q (C.fstToSum (C.interFst x)) ≤ realInterpConst θ q * ‖x‖ₑ := by
  rw [mul_comm, ← enorm_norm, realInterpConst, ← eLpNorm_const_smul]
  refine eLpNorm_mono_real (aestronglyMeasurable_weightedKFunctional θ _) fun s => ?_
  rw [Pi.smul_apply, smul_eq_mul, Real.norm_of_nonneg (weightedKFunctional_nonneg θ _ s),
    weightedKFunctional, mul_left_comm, mul_comm ‖x‖]
  exact mul_le_mul_of_nonneg_left (kFunctional_fstToSum_interFst_le (Real.exp_pos s).le x)
    (Real.exp_pos _).le

theorem toReal_realInterpENorm_fstToSum_interFst_le (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (x : C.inter) : (C.realInterpENorm θ q (C.fstToSum (C.interFst x))).toReal ≤
      (realInterpConst θ q).toReal * ‖x‖ := by
  rw [← toReal_enorm x, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (realInterpConst_lt_top hθ₀ hθ₁).ne
    enorm_ne_top) (realInterpENorm_fstToSum_interFst_le x)

section Refl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- For the couple `(X, X)`, the `(θ, q)`-norm is `realInterpConst θ q` times the norm of `X`. -/
theorem realInterpENorm_refl (u : (refl 𝕜 X).SumSpace) :
    (refl 𝕜 X).realInterpENorm θ q u = realInterpConst θ q * ‖u‖ₑ := by
  rw [mul_comm, ← enorm_norm, realInterpConst, ← eLpNorm_const_smul, realInterpENorm]
  congr 1
  ext s
  rw [weightedKFunctional, kFunctional_refl (Real.exp_pos s).le, Pi.smul_apply, smul_eq_mul]
  ring

end Refl

/-! ### The interpolation inequality -/

section Map

variable {Y₀ Y₁ W : Type*} [NormedAddCommGroup Y₀] [NormedSpace 𝕜 Y₀]
  [NormedAddCommGroup Y₁] [NormedSpace 𝕜 Y₁] [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W]
  [ContinuousAdd W] {D : CompatibleCouple 𝕜 Y₀ Y₁ W}
  {T₀ : X₀ → Y₀} {T₁ : X₁ → Y₁} {M₀ M₁ : ℝ}

/-- The interpolation inequality: if a map `T` of the sum spaces restricts to maps
`T₀ : X₀ → Y₀` and `T₁ : X₁ → Y₁` with `‖T₀ x‖ ≤ M₀ ‖x‖` and `‖T₁ x‖ ≤ M₁ ‖x‖`, where
`M₀, M₁ > 0`, then `‖T u‖_{θ,q} ≤ M₀ ^ (1 - θ) M₁ ^ θ ‖u‖_{θ,q}`. -/
theorem realInterpENorm_map_le {F : Type*}
    [FunLike F C.SumSpace D.SumSpace] [AddHomClass F C.SumSpace D.SumSpace] {T : F}
    (h₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
    (h₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x))
    (hT₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (hT₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (u : C.SumSpace) :
    D.realInterpENorm θ q (T u) ≤
      ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * C.realInterpENorm θ q u := by
  -- In the variable `s = log t`, the dilation `t ↦ t M₁ / M₀` is the translation by `a`.
  obtain ⟨a, ha⟩ : ∃ a, Real.exp a = M₁ / M₀ := ⟨_, Real.exp_log (div_pos hM₁ hM₀)⟩
  have hc : 0 ≤ M₀ ^ (1 - θ) * M₁ ^ θ :=
    mul_nonneg (Real.rpow_nonneg hM₀.le _) (Real.rpow_nonneg hM₁.le _)
  have hpt (s : ℝ) : D.weightedKFunctional θ (T u) s ≤
      M₀ ^ (1 - θ) * M₁ ^ θ * C.weightedKFunctional θ u (s + a) := by
    have he : Real.exp s * M₁ / M₀ = Real.exp (s + a) := by
      rw [Real.exp_add, ha, mul_div_assoc]
    have hexp : M₀ ^ (1 - θ) * M₁ ^ θ * Real.exp (-θ * (s + a)) = M₀ * Real.exp (-θ * s) := by
      have h₀ := Real.rpow_pos_of_pos hM₀ θ
      have h₁ := Real.rpow_pos_of_pos hM₁ θ
      rw [mul_add, Real.exp_add, mul_comm (-θ) a, Real.exp_mul a, ha,
        Real.rpow_neg (div_pos hM₁ hM₀).le, Real.div_rpow hM₁.le hM₀.le, inv_div,
        Real.rpow_sub hM₀, Real.rpow_one]
      field_simp
    have h := kFunctional_map_le h₀ h₁ hT₀ hT₁ hM₀ (Real.exp_pos s).le u
    rw [he] at h
    rw [weightedKFunctional, weightedKFunctional, ← mul_assoc, hexp, mul_comm M₀, mul_assoc]
    exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  calc D.realInterpENorm θ q (T u)
      ≤ eLpNorm ((M₀ ^ (1 - θ) * M₁ ^ θ) • (C.weightedKFunctional θ u ∘ (· + a))) q volume :=
        eLpNorm_mono_real (aestronglyMeasurable_weightedKFunctional θ _) fun s => by
          rw [Real.norm_of_nonneg (weightedKFunctional_nonneg θ _ s)]
          exact hpt s
    _ = ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * C.realInterpENorm θ q u := by
        rw [eLpNorm_const_smul, Real.enorm_of_nonneg hc, eLpNorm_comp_measurePreserving
          (aestronglyMeasurable_weightedKFunctional θ u) (measurePreserving_add_right volume a),
          realInterpENorm]

/-- The interpolation inequality `‖T u‖_{θ,q} ≤ M₀ ^ (1 - θ) M₁ ^ θ ‖u‖_{θ,q}` for real norms. -/
theorem toReal_realInterpENorm_map_le {F : Type*}
    [FunLike F C.SumSpace D.SumSpace] [AddHomClass F C.SumSpace D.SumSpace] {T : F}
    (h₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
    (h₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x))
    (hT₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (hT₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    {u : C.SumSpace} (hu : C.realInterpENorm θ q u < ∞) :
    (D.realInterpENorm θ q (T u)).toReal ≤
      M₀ ^ (1 - θ) * M₁ ^ θ * (C.realInterpENorm θ q u).toReal := by
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu.ne)
    (realInterpENorm_map_le h₀ h₁ hT₀ hT₁ hM₀ hM₁ u)).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (mul_nonneg (Real.rpow_nonneg hM₀.le _) (Real.rpow_nonneg hM₁.le _))]

end Map

/-! ### The real interpolation space -/

variable (C) in
/-- The real interpolation space `(X₀, X₁)_{θ,q}` as a submodule of the sum space: the elements
`u` with `‖u‖_{θ,q} < ∞`. -/
def realInterpSubmodule (θ : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)] : Submodule 𝕜 C.SumSpace where
  carrier := {u | C.realInterpENorm θ q u < ∞}
  add_mem' {u v} hu hv :=
    (realInterpENorm_add_le Fact.out u v).trans_lt (ENNReal.add_lt_top.2 ⟨hu, hv⟩)
  zero_mem' := by simp
  smul_mem' c u hu := by
    simpa only [mem_ofPred_eq, realInterpENorm_smul] using ENNReal.mul_lt_top enorm_lt_top hu

theorem mem_realInterpSubmodule_iff [Fact (1 ≤ q)] {u : C.SumSpace} :
    u ∈ C.realInterpSubmodule θ q ↔ C.realInterpENorm θ q u < ∞ :=
  Iff.rfl

variable (C) in
/-- The real interpolation space `(X₀, X₁)_{θ,q}` of the `K`-method: the elements `u` of the sum
space `X₀ + X₁` with `‖u‖_{θ,q} = ‖t ↦ t^(-θ) K(t, u)‖_{L^q(dt/t)} < ∞`, normed by `‖u‖_{θ,q}`.
It is a normed space for `1 ≤ q` when the ambient space is `T₁`, and a Banach space between
`X₀ ∩ X₁` and `X₀ + X₁` when moreover `0 < θ < 1` and `X₀`, `X₁` are Banach spaces.

It is a type of its own, rather than `realInterpSubmodule θ q`, because the submodule carries the
norm of the sum space. -/
@[ext]
structure RealInterpSpace (θ : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)] where
  /-- The underlying element of the sum space. -/
  toSum : C.SumSpace
  toSum_mem : toSum ∈ C.realInterpSubmodule θ q

namespace RealInterpSpace

variable [Fact (1 ≤ q)]

theorem toSum_injective : Function.Injective (toSum : C.RealInterpSpace θ q → C.SumSpace) :=
  fun _ _ => RealInterpSpace.ext

theorem realInterpENorm_toSum_lt_top (u : C.RealInterpSpace θ q) :
    C.realInterpENorm θ q u.toSum < ∞ :=
  u.toSum_mem

instance : Zero (C.RealInterpSpace θ q) :=
  ⟨⟨0, zero_mem _⟩⟩

instance : Add (C.RealInterpSpace θ q) :=
  ⟨fun u v => ⟨u.toSum + v.toSum, add_mem u.toSum_mem v.toSum_mem⟩⟩

instance : Neg (C.RealInterpSpace θ q) :=
  ⟨fun u => ⟨-u.toSum, neg_mem u.toSum_mem⟩⟩

instance : Sub (C.RealInterpSpace θ q) :=
  ⟨fun u v => ⟨u.toSum - v.toSum, sub_mem u.toSum_mem v.toSum_mem⟩⟩

instance {M : Type*} [SMul M 𝕜] [SMul M C.SumSpace] [IsScalarTower M 𝕜 C.SumSpace] :
    SMul M (C.RealInterpSpace θ q) :=
  ⟨fun c u => ⟨c • u.toSum, Submodule.smul_of_tower_mem _ c u.toSum_mem⟩⟩

@[simp]
theorem toSum_zero : (0 : C.RealInterpSpace θ q).toSum = 0 :=
  (rfl)

@[simp]
theorem toSum_add (u v : C.RealInterpSpace θ q) : (u + v).toSum = u.toSum + v.toSum :=
  (rfl)

@[simp]
theorem toSum_neg (u : C.RealInterpSpace θ q) : (-u).toSum = -u.toSum :=
  (rfl)

@[simp]
theorem toSum_sub (u v : C.RealInterpSpace θ q) : (u - v).toSum = u.toSum - v.toSum :=
  (rfl)

@[simp]
theorem toSum_smul {M : Type*} [SMul M 𝕜] [SMul M C.SumSpace] [IsScalarTower M 𝕜 C.SumSpace]
    (c : M) (u : C.RealInterpSpace θ q) : (c • u).toSum = c • u.toSum :=
  (rfl)

instance : AddCommGroup (C.RealInterpSpace θ q) :=
  toSum_injective.addCommGroup _ toSum_zero toSum_add toSum_neg toSum_sub
    (fun _ _ => toSum_smul _ _) (fun _ _ => toSum_smul _ _)

instance : Module 𝕜 (C.RealInterpSpace θ q) :=
  toSum_injective.module 𝕜 ⟨⟨toSum, toSum_zero⟩, toSum_add⟩ toSum_smul

variable (C θ q) in
/-- The inclusion `(X₀, X₁)_{θ,q} → X₀ + X₁` as a linear map; see `toSumL` for its continuity. -/
def toSumₗ : C.RealInterpSpace θ q →ₗ[𝕜] C.SumSpace where
  toFun := toSum
  map_add' := toSum_add
  map_smul' := toSum_smul

@[simp]
theorem toSumₗ_apply (u : C.RealInterpSpace θ q) : toSumₗ C θ q u = u.toSum :=
  (rfl)

/-- The norm of `(X₀, X₁)_{θ,q}`: `‖u‖ = ‖u‖_{θ,q}`, a finite real number. -/
instance : Norm (C.RealInterpSpace θ q) :=
  ⟨fun u => (C.realInterpENorm θ q u.toSum).toReal⟩

theorem norm_def (u : C.RealInterpSpace θ q) : ‖u‖ = (C.realInterpENorm θ q u.toSum).toReal :=
  (rfl)

/-- `RealInterpSpace θ q` satisfies the axioms of a normed space. -/
theorem normedSpaceCore [T1Space V] : NormedSpace.Core 𝕜 (C.RealInterpSpace θ q) where
  norm_nonneg _ := ENNReal.toReal_nonneg
  norm_smul c u := by
    rw [norm_def, norm_def, toSum_smul, realInterpENorm_smul, ENNReal.toReal_mul, toReal_enorm]
  norm_triangle u v := by
    rw [norm_def, norm_def, norm_def, toSum_add, ← ENNReal.toReal_add
      (realInterpENorm_toSum_lt_top u).ne (realInterpENorm_toSum_lt_top v).ne]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨(realInterpENorm_toSum_lt_top u).ne,
      (realInterpENorm_toSum_lt_top v).ne⟩) (realInterpENorm_add_le Fact.out _ _)
  norm_eq_zero_iff u := by
    rw [norm_def, ENNReal.toReal_eq_zero_iff, or_iff_left (realInterpENorm_toSum_lt_top u).ne,
      realInterpENorm_eq_zero_iff (zero_lt_one.trans_le Fact.out).ne']
    exact ⟨fun h => RealInterpSpace.ext h, fun h => h ▸ rfl⟩

instance [T1Space V] : NormedAddCommGroup (C.RealInterpSpace θ q) :=
  .ofCore normedSpaceCore

instance [T1Space V] : NormedSpace 𝕜 (C.RealInterpSpace θ q) :=
  .ofCore normedSpaceCore

variable [T1Space V]

theorem enorm_eq (u : C.RealInterpSpace θ q) : ‖u‖ₑ = C.realInterpENorm θ q u.toSum := by
  rw [← _root_.ofReal_norm, norm_def, ENNReal.ofReal_toReal (realInterpENorm_toSum_lt_top u).ne]

/-! ### The inclusions `X₀ ∩ X₁ → (X₀, X₁)_{θ,q} → X₀ + X₁` -/

theorem norm_toSum_le (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (u : C.RealInterpSpace θ q) :
    ‖u.toSum‖ ≤ (realInterpConst θ q).toReal⁻¹ * ‖u‖ := by
  have hc := realInterpConst_toReal_pos (q := q) hθ₀ hθ₁ (zero_lt_one.trans_le Fact.out).ne'
  rw [le_inv_mul_iff₀ hc, norm_def, ← toReal_enorm, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (realInterpENorm_toSum_lt_top u).ne (realInterpConst_mul_enorm_le _)

variable (C q) in
/-- The continuous inclusion `(X₀, X₁)_{θ,q} → X₀ + X₁`, of norm at most `c_{θ,q}⁻¹`, where
`c_{θ,q} = realInterpConst θ q`. -/
def toSumL (hθ₀ : 0 < θ) (hθ₁ : θ < 1) : C.RealInterpSpace θ q →L[𝕜] C.SumSpace :=
  (toSumₗ C θ q).mkContinuous _ (norm_toSum_le hθ₀ hθ₁)

@[simp]
theorem toSumL_apply (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (u : C.RealInterpSpace θ q) :
    toSumL C q hθ₀ hθ₁ u = u.toSum :=
  (rfl)

variable (C q) in
/-- The continuous inclusion `X₀ ∩ X₁ → (X₀, X₁)_{θ,q}`, of norm at most `c_{θ,q}`, where
`c_{θ,q} = realInterpConst θ q`. -/
def ofInter (hθ₀ : 0 < θ) (hθ₁ : θ < 1) : C.inter →L[𝕜] C.RealInterpSpace θ q :=
  LinearMap.mkContinuous
    { toFun x := ⟨C.fstToSum (C.interFst x), (realInterpENorm_fstToSum_interFst_le x).trans_lt
        (ENNReal.mul_lt_top (realInterpConst_lt_top hθ₀ hθ₁) enorm_lt_top)⟩
      map_add' x y := RealInterpSpace.ext (by simp)
      map_smul' c x := RealInterpSpace.ext (by simp) }
    (realInterpConst θ q).toReal fun x => toReal_realInterpENorm_fstToSum_interFst_le hθ₀ hθ₁ x

@[simp]
theorem toSum_ofInter (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (x : C.inter) :
    (ofInter C q hθ₀ hθ₁ x).toSum = C.fstToSum (C.interFst x) :=
  (rfl)

theorem norm_ofInter_le (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (x : C.inter) :
    ‖ofInter C q hθ₀ hθ₁ x‖ ≤ (realInterpConst θ q).toReal * ‖x‖ :=
  toReal_realInterpENorm_fstToSum_interFst_le hθ₀ hθ₁ x

/-! ### Completeness -/

/-- The real interpolation space of a couple of Banach spaces is a Banach space
(Bergh–Löfström, Theorem 3.4.2(a)). -/
theorem completeSpace [CompleteSpace X₀] [CompleteSpace X₁] (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    CompleteSpace (C.RealInterpSpace θ q) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete
    ((toSumL C q hθ₀ hθ₁).uniformContinuous.comp_cauchySeq hu)
  -- Once `‖u n - u m‖ ≤ ε` for `m, n ≥ N`, Fatou's lemma gives `‖u n - w‖_{θ,q} ≤ ε` for `n ≥ N`.
  have key : ∀ ε > 0, ∃ N, ∀ n ≥ N,
      C.realInterpENorm θ q ((u n).toSum - w) ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu ε hε
    refine ⟨N, fun n hn => (realInterpENorm_sub_le_liminf hw _).trans
      (liminf_le_of_frequently_le' ((eventually_ge_atTop N).mono fun m hm => ?_).frequently)⟩
    rw [Function.comp_apply, toSumL_apply, ← toSum_sub, ← enorm_eq, ← _root_.ofReal_norm,
      ← dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal (hN n hn m hm).le
  obtain ⟨N, hN⟩ := key 1 one_pos
  have hw_mem : w ∈ C.realInterpSubmodule θ q := by
    rw [← sub_sub_cancel (u N).toSum w]
    exact sub_mem (u N).toSum_mem ((hN N le_rfl).trans_lt ENNReal.ofReal_lt_top)
  refine ⟨⟨w, hw_mem⟩, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
  obtain ⟨N', hN'⟩ := key (ε / 2) (half_pos hε)
  refine ⟨N', fun n hn => ?_⟩
  rw [dist_eq_norm, norm_def, toSum_sub]
  exact (ENNReal.toReal_le_of_le_ofReal (half_pos hε).le (hN' n hn)).trans_lt (half_lt_self hε)

/-! ### The interpolation theorem -/

section Map

variable {Y₀ Y₁ W : Type*} [NormedAddCommGroup Y₀] [NormedSpace 𝕜 Y₀]
  [NormedAddCommGroup Y₁] [NormedSpace 𝕜 Y₁] [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W]
  [ContinuousAdd W] {D : CompatibleCouple 𝕜 Y₀ Y₁ W}
  {T₀ : X₀ → Y₀} {T₁ : X₁ → Y₁} {M₀ M₁ : ℝ} [T1Space W]

/-- The interpolation theorem for the real method (Bergh–Löfström, Theorem 3.1.2): a linear map
`T` of the sum spaces restricting to maps `T₀ : X₀ → Y₀` and `T₁ : X₁ → Y₁` with
`‖T₀ x‖ ≤ M₀ ‖x‖` and `‖T₁ x‖ ≤ M₁ ‖x‖`, where `M₀, M₁ > 0`, maps `(X₀, X₁)_{θ,q}` to
`(Y₀, Y₁)_{θ,q}`, with norm at most `M₀ ^ (1 - θ) * M₁ ^ θ` (`norm_map_le`). -/
def map (T : C.SumSpace →ₗ[𝕜] D.SumSpace) (h₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
    (h₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x))
    (hT₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (hT₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (hM₀ : 0 < M₀)
    (hM₁ : 0 < M₁) : C.RealInterpSpace θ q →L[𝕜] D.RealInterpSpace θ q :=
  LinearMap.mkContinuous
    { toFun u := ⟨T u.toSum, (realInterpENorm_map_le h₀ h₁ hT₀ hT₁ hM₀ hM₁ _).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top u.toSum_mem)⟩
      map_add' _ _ := RealInterpSpace.ext (map_add T _ _)
      map_smul' _ _ := RealInterpSpace.ext (map_smul T _ _) }
    (M₀ ^ (1 - θ) * M₁ ^ θ) fun u =>
      toReal_realInterpENorm_map_le h₀ h₁ hT₀ hT₁ hM₀ hM₁ u.toSum_mem

variable (T : C.SumSpace →ₗ[𝕜] D.SumSpace) (h₀ : ∀ x, T (C.fstToSum x) = D.fstToSum (T₀ x))
  (h₁ : ∀ x, T (C.sndToSum x) = D.sndToSum (T₁ x))
  (hT₀ : ∀ x, ‖T₀ x‖ ≤ M₀ * ‖x‖) (hT₁ : ∀ x, ‖T₁ x‖ ≤ M₁ * ‖x‖) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)

@[simp]
theorem toSum_map (u : C.RealInterpSpace θ q) :
    (map T h₀ h₁ hT₀ hT₁ hM₀ hM₁ u).toSum = T u.toSum :=
  (rfl)

theorem norm_map_le (u : C.RealInterpSpace θ q) :
    ‖map T h₀ h₁ hT₀ hT₁ hM₀ hM₁ u‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ * ‖u‖ :=
  toReal_realInterpENorm_map_le h₀ h₁ hT₀ hT₁ hM₀ hM₁ u.toSum_mem

end Map

end RealInterpSpace

end CompatibleCouple

end TauCeti

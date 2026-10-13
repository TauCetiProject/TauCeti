/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Function.Lp.OperatorLocalBound

/-!
# Singular integral operators map bounded functions to functions of bounded mean oscillation

A Calderón–Zygmund operator is bounded on `Lᵖ` for `1 < p < ∞` but not on `L^∞`. The substitute
at the endpoint `p = ∞` is that it maps bounded functions to functions of **bounded mean
oscillation**: there is a constant `C` with

`⨍_Q ‖T f - (T f)_Q‖ ≤ C ‖f‖_∞`, where `(T f)_Q = ⨍_Q T f`,

for every ball `Q`. Such a function need not be bounded, but by the John–Nirenberg inequality
(`TauCeti.volume_lt_norm_sub_setAverage_closedBall_le`) it is exponentially integrable on every
cube of `ℝⁿ`.

Let `T` be a bounded linear operator on `L²`, given away from the support of its argument by a
kernel `K`: if `b ∈ L²` vanishes on a ball, then `T b x = ∫ K x y (b y) dy` for almost every `x`
in that ball. Assume `K` satisfies **Hörmander's condition in the first variable**,

`∫_{dist y x' > 2 dist x x'} ‖K x y - K x' y‖ dy ≤ B` for all `x`, `x'`,

which is the condition `TauCeti.setLIntegral_compl_closedBall_enorm_le_of_hormander` imposes on the
transposed kernel `(x, y) ↦ K y x`. Then for every `f ∈ L²` and every closed ball
`Q = closedBall c r` with `r > 0` and `μ (closedBall c (5 r)) ≤ D μ Q`,

`⨍_Q ‖T f - (T f)_Q‖ ≤ 2 (√D ‖T‖ + B) ‖f‖_∞`

(`ContinuousLinearMap.setLAverage_enorm_sub_setAverage_le_of_hormander_of_measure_closedBall_le`).
In a finite-dimensional normed space with an additive Haar measure, `D = 5ⁿ` works for every
ball, so the same estimate holds on every ball with constant `2 (5^{n/2} ‖T‖ + B) ‖f‖_∞`
(`ContinuousLinearMap.setLAverage_enorm_sub_setAverage_le_of_hormander`). Both estimates are
inequalities in `ℝ≥0∞`, stated for `f ∈ L²`, where `T f` is defined. When `B < ∞` and
`‖f‖_∞ < ∞` the constant is finite, and then `T f` has bounded mean oscillation.

## The proof

Split `f = f₁ + f₂`, where `f₁` is `f` on the enlarged ball `5Q = closedBall c (5 r)` and zero
off it. The local part is controlled by the `L²` bound: by the Cauchy–Schwarz inequality,
`⨍_Q ‖T f₁‖ ≤ (μ Q)^{-1/2} ‖T‖ ‖f₁‖₂ ≤ √D ‖T‖ ‖f‖_∞`. The far part `f₂` vanishes on `5Q`, so on `Q`
it is given by the kernel, and for `x, x' ∈ Q` every point `y` with `f₂ y ≠ 0` satisfies
`dist y x' > 4 r ≥ 2 dist x x'`. Hörmander's condition therefore gives
`‖T f₂ x - T f₂ x'‖ ≤ B ‖f‖_∞` (`TauCeti.enorm_integral_sub_integral_le_of_hormander`): `T f₂` is
nearly constant on `Q`. Comparing `T f` with the constant `T f₂ x'` bounds its mean oscillation,
and replacing the constant by the average costs a factor `2`
(`TauCeti.setLAverage_enorm_sub_setAverage_le`).

## Main declarations

* `TauCeti.enorm_integral_sub_integral_le_of_hormander`: a bounded function vanishing near `x'`
  has kernel integrals at `x` and `x'` that differ by at most `B ‖b‖_∞`.
* `ContinuousLinearMap.setLAverage_enorm_sub_setAverage_le_of_hormander_of_measure_closedBall_le`:
  the mean oscillation of `T f` on a ball, in a metric measure space with a doubling bound for
  that ball.
* `ContinuousLinearMap.setLAverage_enorm_sub_setAverage_le_of_hormander`:
  the mean oscillation of `T f` on every ball of a finite-dimensional normed space with Haar
  measure; when `B < ∞` and `‖f‖_∞ < ∞`, `T f` has bounded mean oscillation.

## References

* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Chapter IV.
* L. Grafakos, *Modern Fourier Analysis*, Chapter 3.
* J. Duoandikoetxea, *Fourier Analysis*, Chapter 6.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal

section Kernel

variable {X E F : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Hörmander's condition in the first variable.** Let `K` be a kernel whose difference at the
points `x`, `x'` satisfies `∫_{dist y x' > 2 dist x x'} ‖K x y - K x' y‖ dy ≤ B`. If `‖b‖ ≤ M`
almost everywhere and `b` vanishes almost everywhere on `closedBall x' (2 dist x x')`, then the
kernel integrals of `b` at `x` and at `x'` differ by at most `B M`. No integrability of
`y ↦ K x y (b y)` is assumed. -/
theorem enorm_integral_sub_integral_le_of_hormander {K : X → X → E →L[ℝ] F} {x x' : X}
    (hKx : AEStronglyMeasurable (K x) μ) (hKx' : AEStronglyMeasurable (K x') μ) {B : ℝ≥0∞}
    (hB : ∫⁻ y in {y | 2 * dist x x' < dist y x'}, ‖K x y - K x' y‖ₑ ∂μ ≤ B)
    {b : X → E} (hb : AEStronglyMeasurable b μ) {M : ℝ≥0∞} (hM : ∀ᵐ y ∂μ, ‖b y‖ₑ ≤ M)
    (hsupp : ∀ᵐ y ∂μ, y ∈ closedBall x' (2 * dist x x') → b y = 0) :
    ‖∫ y, K x y (b y) ∂μ - ∫ y, K x' y (b y) ∂μ‖ₑ ≤ B * M := by
  have hKd : AEStronglyMeasurable (fun y => K x y - K x' y) μ := hKx.sub hKx'
  have hS : MeasurableSet {y | 2 * dist x x' < dist y x'} :=
    (isOpen_lt continuous_const (continuous_id.dist continuous_const)).measurableSet
  -- Since `b` vanishes off the region of Hörmander's condition, the difference of the integrands
  -- has integral at most `B M`.
  have hlint : ∫⁻ y, ‖(K x y - K x' y) (b y)‖ₑ ∂μ ≤ B * M := by
    calc ∫⁻ y, ‖(K x y - K x' y) (b y)‖ₑ ∂μ
        ≤ ∫⁻ y in {y | 2 * dist x x' < dist y x'}, ‖K x y - K x' y‖ₑ * M ∂μ := by
          rw [← lintegral_indicator hS]
          refine lintegral_mono_ae ?_
          filter_upwards [hM, hsupp] with y hy hy'
          by_cases h : 2 * dist x x' < dist y x'
          · rw [indicator_of_mem (show y ∈ {y | 2 * dist x x' < dist y x'} from h)]
            exact (ContinuousLinearMap.le_opENorm _ _).trans (by gcongr)
          · rw [hy' (mem_closedBall.2 (not_lt.1 h))]
            simp
      _ = (∫⁻ y in {y | 2 * dist x x' < dist y x'}, ‖K x y - K x' y‖ₑ ∂μ) * M :=
          lintegral_mul_const'' _ hKd.enorm.restrict
      _ ≤ B * M := by gcongr
  rcases eq_or_ne (B * M) ∞ with hBM | hBM
  · simp [hBM]
  have hint : Integrable (fun y => (K x y - K x' y) (b y)) μ :=
    ⟨(ContinuousLinearMap.apply ℝ F).aestronglyMeasurable_comp₂ hb hKd,
      hlint.trans_lt hBM.lt_top⟩
  by_cases hx' : Integrable (fun y => K x' y (b y)) μ
  · have hx : Integrable (fun y => K x y (b y)) μ :=
      (hint.add hx').congr (.of_forall fun y => by simp)
    rw [← integral_sub hx hx']
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq_of_le ?_ hlint)
    simp
  · have hx : ¬Integrable (fun y => K x y (b y)) μ := fun hx =>
      hx' ((hx.sub hint).congr (.of_forall fun y => by simp))
    simp [integral_undef hx, integral_undef hx']

end Kernel

end TauCeti

namespace ContinuousLinearMap

open MeasureTheory Metric Set TauCeti
open scoped ENNReal

section Doubling

variable {X E F : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- The far part: if `b ∈ L²` is bounded by `M` and vanishes on `closedBall c (5 r)`, then on
`closedBall c r` the function `T b` stays within `B M` of a constant, by Hörmander's condition. -/
private theorem exists_ae_enorm_apply_sub_le_of_hormander (T : Lp E 2 μ →L[ℝ] Lp F 2 μ)
    {K : X → X → E →L[ℝ] F} (hK : ∀ x, AEStronglyMeasurable (K x) μ) {B : ℝ≥0∞}
    (hB : ∀ x x', ∫⁻ y in {y | 2 * dist x x' < dist y x'}, ‖K x y - K x' y‖ₑ ∂μ ≤ B)
    (hrep : ∀ (b : Lp E 2 μ) (y : X) (ρ : ℝ), (∀ᵐ z ∂μ, z ∈ ball y ρ → b z = 0) →
      ∀ᵐ x ∂μ, x ∈ ball y ρ → T b x = ∫ z, K x z (b z) ∂μ)
    {b : Lp E 2 μ} {M : ℝ≥0∞} (hM : ∀ᵐ y ∂μ, ‖b y‖ₑ ≤ M) {c : X} {r : ℝ} (hr : 0 < r)
    (hvan : ∀ᵐ y ∂μ, y ∈ closedBall c (5 * r) → b y = 0) (h0 : μ (closedBall c r) ≠ 0) :
    ∃ a : F, ∀ᵐ x ∂μ.restrict (closedBall c r), ‖T b x - a‖ₑ ≤ B * M := by
  have hQ : MeasurableSet (closedBall c r) := measurableSet_closedBall
  -- On the ball, `T b` is given by the kernel.
  have hQrep : ∀ᵐ x ∂μ.restrict (closedBall c r), T b x = ∫ z, K x z (b z) ∂μ := by
    rw [ae_restrict_iff' hQ]
    filter_upwards [hrep b c (5 * r) (by
      filter_upwards [hvan] with y h hy using h (ball_subset_closedBall hy))] with x hx hxQ
    exact hx (closedBall_subset_ball (by linarith) hxQ)
  obtain ⟨x', hx'Q, hx'⟩ : ∃ x' ∈ closedBall c r, T b x' = ∫ z, K x' z (b z) ∂μ := by
    have : (ae (μ.restrict (closedBall c r))).NeBot := ae_restrict_neBot.2 h0
    exact ((ae_restrict_mem hQ).and hQrep).exists
  refine ⟨T b x', ?_⟩
  filter_upwards [hQrep, ae_restrict_mem hQ] with x hx hxQ
  rw [hx, hx']
  refine enorm_integral_sub_integral_le_of_hormander (hK x) (hK x') (hB x x')
    (Lp.aestronglyMeasurable b) hM ?_
  -- Every `y` with `dist y x' ≤ 2 dist x x'` lies in `closedBall c (5 r)`, where `b` vanishes.
  filter_upwards [hvan] with y hy hyb
  refine hy ?_
  rw [mem_closedBall] at hyb hxQ hx'Q ⊢
  linarith [dist_triangle y x' c, dist_triangle_right x x' c]

/-- **Singular integral operators map `L^∞` to BMO**, on one ball. Let `T` be a bounded linear
operator on `L²(μ)` such that `T b x = ∫ K x y (b y) dy` for almost every `x` in any ball on
which `b` vanishes, where the kernel `K` satisfies Hörmander's condition in the first variable,
`∫_{dist y x' > 2 dist x x'} ‖K x y - K x' y‖ dy ≤ B` for all `x`, `x'`. If
`μ (closedBall c (5 r)) ≤ D μ (closedBall c r)` with `r > 0`, then for every `f ∈ L²` the mean
oscillation of `T f` on `closedBall c r` is at most `2 (√D ‖T‖ + B) ‖f‖_∞`. -/
theorem setLAverage_enorm_sub_setAverage_le_of_hormander_of_measure_closedBall_le
    (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) {K : X → X → E →L[ℝ] F}
    (hK : ∀ x, AEStronglyMeasurable (K x) μ) {B : ℝ≥0∞}
    (hB : ∀ x x', ∫⁻ y in {y | 2 * dist x x' < dist y x'}, ‖K x y - K x' y‖ₑ ∂μ ≤ B)
    (hrep : ∀ (b : Lp E 2 μ) (y : X) (ρ : ℝ), (∀ᵐ z ∂μ, z ∈ ball y ρ → b z = 0) →
      ∀ᵐ x ∂μ, x ∈ ball y ρ → T b x = ∫ z, K x z (b z) ∂μ)
    (f : Lp E 2 μ) {c : X} {r : ℝ} (hr : 0 < r) {D : ℝ≥0∞}
    (hD : μ (closedBall c (5 * r)) ≤ D * μ (closedBall c r)) :
    ⨍⁻ x in closedBall c r, ‖T f x - ⨍ z in closedBall c r, T f z ∂μ‖ₑ ∂μ ≤
      2 * (D ^ (2⁻¹ : ℝ) * ‖T‖ₑ + B) * eLpNorm f ∞ μ := by
  set M := eLpNorm (f : X → E) ∞ μ
  have h5 : MeasurableSet (closedBall c (5 * r)) := measurableSet_closedBall
  -- A ball of measure `0` or `∞` has mean oscillation `0`.
  rcases eq_or_ne (μ (closedBall c r)) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0]
  rcases eq_or_ne (μ (closedBall c r)) ∞ with htop | htop
  · simp [setLAverage_eq, htop]
  -- Split `f = f₁ + f₂`, with `f₁ = f - f₂` supported on the enlarged ball and `f₂` vanishing
  -- there.
  obtain ⟨f₂, hf₂⟩ : ∃ f₂ : Lp E 2 μ, f₂ =ᵐ[μ] (closedBall c (5 * r))ᶜ.indicator f :=
    ⟨_, ((Lp.memLp f).indicator h5.compl.nullMeasurableSet).coeFn_toLp⟩
  have hf₁ : ⇑(f - f₂) =ᵐ[μ] (closedBall c (5 * r)).indicator f := by
    filter_upwards [Lp.coeFn_sub f f₂, hf₂] with x h1 h2
    rw [h1, Pi.sub_apply, h2]
    by_cases hx : x ∈ closedBall c (5 * r) <;> simp [hx]
  have hTf : ⇑(T f) =ᵐ[μ] ⇑(T (f - f₂)) + ⇑(T f₂) := by
    have h := Lp.coeFn_add (T (f - f₂)) (T f₂)
    rwa [← map_add, sub_add_cancel] at h
  have hM₂ : ∀ᵐ y ∂μ, ‖f₂ y‖ₑ ≤ M := by
    have hfM : ∀ᵐ y ∂μ, ‖f y‖ₑ ≤ M := by
      rw [show M = eLpNormEssSup f μ from eLpNorm_exponent_top (Lp.aestronglyMeasurable f)]
      exact ae_le_eLpNormEssSup
    filter_upwards [hf₂, hfM] with y h1 h2
    rw [h1]
    exact (enorm_indicator_le_enorm_self _ _).trans h2
  have hvan : ∀ᵐ y ∂μ, y ∈ closedBall c (5 * r) → f₂ y = 0 := by
    filter_upwards [hf₂] with y h hy
    rw [h, indicator_of_notMem (notMem_compl_iff.2 hy)]
  obtain ⟨a, ha⟩ := exists_ae_enorm_apply_sub_le_of_hormander T hK hB hrep hM₂ hr hvan h0
  -- The local part has `∫_Q ‖T f₁‖ ≤ √D ‖T‖ M μ Q`.
  have hloc : ∫⁻ x in closedBall c r, ‖T (f - f₂) x‖ₑ ∂μ ≤
      D ^ (2⁻¹ : ℝ) * ‖T‖ₑ * M * μ (closedBall c r) := by
    have hsq : μ (closedBall c r) ^ (2⁻¹ : ℝ) * μ (closedBall c r) ^ (2⁻¹ : ℝ) =
        μ (closedBall c r) := by
      rw [← ENNReal.rpow_add _ _ h0 htop]
      norm_num
    calc ∫⁻ x in closedBall c r, ‖T (f - f₂) x‖ₑ ∂μ
        ≤ ‖T‖ₑ * (M * μ (closedBall c (5 * r)) ^ (2⁻¹ : ℝ)) * μ (closedBall c r) ^ (2⁻¹ : ℝ) :=
          (setLIntegral_enorm_apply_le_of_ae_eq_indicator T h5 hf₁ _).trans_eq (by norm_num [M])
      _ ≤ ‖T‖ₑ * (M * (D * μ (closedBall c r)) ^ (2⁻¹ : ℝ)) *
            μ (closedBall c r) ^ (2⁻¹ : ℝ) := by gcongr
      _ = D ^ (2⁻¹ : ℝ) * ‖T‖ₑ * M *
            (μ (closedBall c r) ^ (2⁻¹ : ℝ) * μ (closedBall c r) ^ (2⁻¹ : ℝ)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
          ring
      _ = D ^ (2⁻¹ : ℝ) * ‖T‖ₑ * M * μ (closedBall c r) := by rw [hsq]
  -- Comparing `T f = T f₁ + T f₂` with the constant `a` bounds its mean oscillation.
  have hconst : ⨍⁻ x in closedBall c r, ‖T f x - a‖ₑ ∂μ ≤ (D ^ (2⁻¹ : ℝ) * ‖T‖ₑ + B) * M := by
    rw [setLAverage_eq, ENNReal.div_le_iff h0 htop]
    calc ∫⁻ x in closedBall c r, ‖T f x - a‖ₑ ∂μ
        ≤ ∫⁻ x in closedBall c r, (‖T (f - f₂) x‖ₑ + B * M) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_of_ae hTf, ha] with x h1 h2
          rw [h1, Pi.add_apply, add_sub_assoc]
          exact (enorm_add_le _ _).trans (by gcongr)
      _ = ∫⁻ x in closedBall c r, ‖T (f - f₂) x‖ₑ ∂μ + B * M * μ (closedBall c r) := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
      _ ≤ D ^ (2⁻¹ : ℝ) * ‖T‖ₑ * M * μ (closedBall c r) + B * M * μ (closedBall c r) := by
          gcongr
      _ = (D ^ (2⁻¹ : ℝ) * ‖T‖ₑ + B) * M * μ (closedBall c r) := by ring
  have : IsFiniteMeasure (μ.restrict (closedBall c r)) := isFiniteMeasure_restrict.2 htop
  have hint : IntegrableOn (T f) (closedBall c r) μ :=
    ((Lp.memLp (T f)).restrict _).integrable one_le_two
  calc ⨍⁻ x in closedBall c r, ‖T f x - ⨍ z in closedBall c r, T f z ∂μ‖ₑ ∂μ
      ≤ 2 * ⨍⁻ x in closedBall c r, ‖T f x - a‖ₑ ∂μ :=
        setLAverage_enorm_sub_setAverage_le hint _
    _ ≤ _ := by rw [mul_assoc]; gcongr

end Doubling

section AddHaar

variable {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

/-- **Singular integral operators map `L^∞` to BMO.** Let `T` be a bounded linear operator on
`L²(μ)`, for an additive Haar measure `μ` on a finite-dimensional real normed space `V` of
dimension `n`, such that `T b x = ∫ K x y (b y) dy` for almost every `x` in any ball on which `b`
vanishes, where the kernel `K` satisfies Hörmander's condition in the first variable,
`∫_{dist y x' > 2 dist x x'} ‖K x y - K x' y‖ dy ≤ B` for all `x`, `x'`. Then for every `f ∈ L²`
and every closed ball `Q`,

`⨍_Q ‖T f - (T f)_Q‖ ≤ 2 (5^{n/2} ‖T‖ + B) ‖f‖_∞`

as an inequality in `ℝ≥0∞`. In particular, if `B < ∞` and `‖f‖_∞ < ∞`, then `T f` has bounded
mean oscillation. -/
theorem setLAverage_enorm_sub_setAverage_le_of_hormander
    (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) {K : V → V → E →L[ℝ] F}
    (hK : ∀ x, AEStronglyMeasurable (K x) μ) {B : ℝ≥0∞}
    (hB : ∀ x x', ∫⁻ y in {y | 2 * dist x x' < dist y x'}, ‖K x y - K x' y‖ₑ ∂μ ≤ B)
    (hrep : ∀ (b : Lp E 2 μ) (y : V) (ρ : ℝ), (∀ᵐ z ∂μ, z ∈ ball y ρ → b z = 0) →
      ∀ᵐ x ∂μ, x ∈ ball y ρ → T b x = ∫ z, K x z (b z) ∂μ)
    (f : Lp E 2 μ) (c : V) (r : ℝ) :
    ⨍⁻ x in closedBall c r, ‖T f x - ⨍ z in closedBall c r, T f z ∂μ‖ₑ ∂μ ≤
      2 * ((5 ^ Module.finrank ℝ V : ℝ≥0∞) ^ (2⁻¹ : ℝ) * ‖T‖ₑ + B) * eLpNorm f ∞ μ := by
  have key : ∀ ρ : ℝ, 0 < ρ →
      ⨍⁻ x in closedBall c ρ, ‖T f x - ⨍ z in closedBall c ρ, T f z ∂μ‖ₑ ∂μ ≤
        2 * ((5 ^ Module.finrank ℝ V : ℝ≥0∞) ^ (2⁻¹ : ℝ) * ‖T‖ₑ + B) * eLpNorm f ∞ μ := by
    refine fun ρ hρ =>
      setLAverage_enorm_sub_setAverage_le_of_hormander_of_measure_closedBall_le T hK hB hrep f hρ
        (le_of_eq ?_)
    rw [Measure.addHaar_closedBall_mul μ c (by norm_num : (0 : ℝ) ≤ 5) hρ.le,
      Measure.addHaar_closedBall_center μ c, ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rcases lt_or_ge 0 r with hr | hr
  · exact key r hr
  rcases eq_or_ne (μ (closedBall c r)) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0]
  -- A closed ball of nonpositive radius and positive measure is a point carrying an atom, so the
  -- space is trivial and the ball is also the closed ball of radius `1`.
  have hr0 : r = 0 := by
    refine le_antisymm hr (not_lt.1 fun hr' => h0 ?_)
    rw [closedBall_eq_empty.2 hr', measure_empty]
  subst hr0
  have : Subsingleton V := by
    by_contra hV
    rw [not_subsingleton_iff_nontrivial] at hV
    exact h0 (by rw [closedBall_zero, measure_singleton])
  have hball : closedBall c 0 = closedBall c 1 := by
    ext x
    simp [Subsingleton.elim x c]
  rw [hball]
  exact key 1 one_pos

end AddHaar

end ContinuousLinearMap

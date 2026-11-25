/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.WeakMixing
public import TauCeti.Dynamics.Ergodic.Action.Eigenfunction
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Weak mixing in `L²` and eigenfunctions

Let `ℝ` act jointly measurably on `X`, preserving a probability measure `μ`, and let `U_t` be the
Koopman group on complex `L²(μ)`, `U_t f = f ∘ (t +ᵥ ·)` (`TauCeti.koopmanGroup`).

The action is weakly mixing exactly when, for all `f g ∈ L²(μ)`, the centered correlations
`⟪g, U_t f⟫ - (∫ f) conj (∫ g)` tend to `0` in Cesàro mean in absolute value:
`T⁻¹ ∫₀ᵀ |⟪g, U_t f⟫ - (∫ f) conj (∫ g)| dt → 0`
(`MeasureTheory.Measure.isWeaklyMixing_iff_tendsto_average_norm_inner_koopmanGroup`). For
indicator functions `f = 1_A`, `g = 1_B` the centered correlation is
`μ((t +ᵥ ·)⁻¹' A ∩ B) - μ(A) μ(B)`, which gives one direction. For the other, the set of pairs
`(f, g)` with vanishing Cesàro mean is closed under addition in each variable, since the centered
correlation is additive in each, and closed, since it is Lipschitz in each variable uniformly in
`t`; simple functions are dense in `L²(μ)`.

As a consequence, a measurable eigenfunction of a weakly mixing action is almost everywhere
constant (`MeasureTheory.Measure.IsWeaklyMixing.exists_ae_eq_const_of_eigenfunction`): the action
is ergodic, so for frequency `0` the eigenfunction is almost invariant, hence constant; for a
frequency `a ≠ 0` it is in `L²(μ)`, has integral `0` because `∫ f = exp(2πiat) ∫ f`, and its
centered correlation `⟪f, U_t f⟫ = exp(2πiat) ‖f‖²` has constant absolute value `‖f‖²`, which
must therefore vanish. This is the easy half of the eigenfunction criterion for weak mixing.

## Main results

* `MeasureTheory.Measure.IsWeaklyMixing.tendsto_average_norm_inner_koopmanGroup`: the `L²` form
  of weak mixing;
* `MeasureTheory.Measure.isWeaklyMixing_iff_tendsto_average_norm_inner_koopmanGroup`: weak mixing
  is equivalent to its `L²` form;
* `MeasureTheory.Measure.IsWeaklyMixing.exists_ae_eq_const_of_eigenfunction`: every measurable
  eigenfunction of a weakly mixing action is almost everywhere constant.

## References

* M. Hochman, *Notes on ergodic theory*, 2012, Section 6.1 (for actions of `ℤ`).
-/

public section

noncomputable section

open Filter MeasureTheory Set TauCeti TauCeti.Semigroups
open scoped Topology ENNReal ComplexConjugate InnerProductSpace

namespace MeasureTheory.Measure

/-! ### Cesàro means of continuous functions -/

section Cesaro

/-- If a continuous nonnegative function `φ` is bounded, up to an arbitrarily small additive
constant, by continuous functions whose Cesàro means tend to `0`, its Cesàro means tend to `0`. -/
private theorem tendsto_average_of_forall_le {φ : ℝ → ℝ} (hφ : Continuous φ) (h0 : ∀ t, 0 ≤ φ t)
    (h : ∀ ε > 0, ∃ ψ : ℝ → ℝ, Continuous ψ ∧
      Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ψ t) atTop (𝓝 0) ∧ ∀ t, φ t ≤ ψ t + ε) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, φ t) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨ψ, hψc, hψ, hφψ⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.1 hψ (ε / 2) (half_pos hε)
  refine ⟨max T₀ 1, fun T hTmax => ?_⟩
  have hT : 0 < T := lt_of_lt_of_le one_pos (le_of_max_le_right hTmax)
  have hψT := hT₀ T (le_of_max_le_left hTmax)
  rw [Real.dist_eq, sub_zero] at hψT ⊢
  have hint : ∫ t in (0 : ℝ)..T, φ t ≤ ∫ t in (0 : ℝ)..T, (ψ t + ε / 2) :=
    intervalIntegral.integral_mono_on hT.le (hφ.intervalIntegrable _ _)
      ((hψc.add continuous_const).intervalIntegrable _ _) fun t _ => hφψ t
  rw [intervalIntegral.integral_add (hψc.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hint
  have hnonneg : 0 ≤ T⁻¹ * ∫ t in (0 : ℝ)..T, φ t :=
    mul_nonneg (inv_nonneg.2 hT.le) (intervalIntegral.integral_nonneg hT.le fun t _ => h0 t)
  rw [abs_of_nonneg hnonneg]
  have hle : T⁻¹ * ∫ t in (0 : ℝ)..T, φ t ≤ (T⁻¹ * ∫ t in (0 : ℝ)..T, ψ t) + ε / 2 := by
    calc T⁻¹ * ∫ t in (0 : ℝ)..T, φ t
        ≤ T⁻¹ * ((∫ t in (0 : ℝ)..T, ψ t) + T * (ε / 2)) :=
          mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hT.le)
      _ = (T⁻¹ * ∫ t in (0 : ℝ)..T, ψ t) + ε / 2 := by
          rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hT.ne', one_mul]
  linarith [le_abs_self (T⁻¹ * ∫ t in (0 : ℝ)..T, ψ t)]

/-- The Cesàro means of a sum of two continuous functions are the sums of their Cesàro means. -/
private theorem tendsto_average_add {ψ₁ ψ₂ : ℝ → ℝ} (h₁c : Continuous ψ₁) (h₂c : Continuous ψ₂)
    (h₁ : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ψ₁ t) atTop (𝓝 0))
    (h₂ : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ψ₂ t) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, (ψ₁ t + ψ₂ t)) atTop (𝓝 0) := by
  simpa [intervalIntegral.integral_add (h₁c.intervalIntegrable _ _) (h₂c.intervalIntegrable _ _),
    mul_add] using h₁.add h₂

end Cesaro

/-! ### Centered correlations of a unitary group -/

section Correlation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (U : StronglyContinuousGroup H) (e : H)

/-- The centered correlation `⟪g, U_t f⟫ - ⟪e, f⟫ ⟪g, e⟫` of a group `U` relative to a vector
`e`. For the Koopman group and `e = 1`, it is `⟪g, U_t f⟫ - (∫ f) conj (∫ g)`. -/
private def corr (f g : H) (t : ℝ) : ℂ :=
  ⟪g, U t f⟫_ℂ - ⟪e, f⟫_ℂ * ⟪g, e⟫_ℂ

/-- The Cesàro means of the absolute value of the centered correlation tend to `0`. -/
private def CorrVanishes (f g : H) : Prop :=
  Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ‖corr U e f g t‖) atTop (𝓝 0)

private theorem continuous_corr (f g : H) : Continuous (corr U e f g) :=
  (continuous_const.inner (U.continuous_orbit f)).sub continuous_const

private theorem corr_add_left (f₁ f₂ g : H) (t : ℝ) :
    corr U e (f₁ + f₂) g t = corr U e f₁ g t + corr U e f₂ g t := by
  simp only [corr, map_add, inner_add_right]
  ring

private theorem corr_add_right (f g₁ g₂ : H) (t : ℝ) :
    corr U e f (g₁ + g₂) t = corr U e f g₁ t + corr U e f g₂ t := by
  simp only [corr, inner_add_left]
  ring

variable {U}

private theorem norm_corr_le (hU : U.IsUnitary) (f g : H) (t : ℝ) :
    ‖corr U e f g t‖ ≤ (1 + ‖e‖ ^ 2) * (‖f‖ * ‖g‖) := by
  calc ‖corr U e f g t‖ ≤ ‖⟪g, U t f⟫_ℂ‖ + ‖⟪e, f⟫_ℂ‖ * ‖⟪g, e⟫_ℂ‖ := by
        rw [corr, ← norm_mul]
        exact norm_sub_le _ _
    _ ≤ ‖g‖ * ‖U t f‖ + (‖e‖ * ‖f‖) * (‖g‖ * ‖e‖) := by
        gcongr
        · exact norm_inner_le_norm _ _
        · exact norm_inner_le_norm _ _
        · exact norm_inner_le_norm _ _
    _ = (1 + ‖e‖ ^ 2) * (‖f‖ * ‖g‖) := by
        rw [hU.norm_map]
        ring

private theorem corrVanishes_add_left {f₁ f₂ g : H} (h₁ : CorrVanishes U e f₁ g)
    (h₂ : CorrVanishes U e f₂ g) : CorrVanishes U e (f₁ + f₂) g := by
  refine tendsto_average_of_forall_le (continuous_corr U e _ _).norm (fun _ => norm_nonneg _)
    fun ε hε => ⟨fun t => ‖corr U e f₁ g t‖ + ‖corr U e f₂ g t‖,
      ((continuous_corr U e _ _).norm.add (continuous_corr U e _ _).norm),
      tendsto_average_add (continuous_corr U e _ _).norm (continuous_corr U e _ _).norm h₁ h₂,
      fun t => ?_⟩
  rw [corr_add_left]
  beta_reduce
  linarith [norm_add_le (corr U e f₁ g t) (corr U e f₂ g t)]

private theorem corrVanishes_add_right {f g₁ g₂ : H} (h₁ : CorrVanishes U e f g₁)
    (h₂ : CorrVanishes U e f g₂) : CorrVanishes U e f (g₁ + g₂) := by
  refine tendsto_average_of_forall_le (continuous_corr U e _ _).norm (fun _ => norm_nonneg _)
    fun ε hε => ⟨fun t => ‖corr U e f g₁ t‖ + ‖corr U e f g₂ t‖,
      ((continuous_corr U e _ _).norm.add (continuous_corr U e _ _).norm),
      tendsto_average_add (continuous_corr U e _ _).norm (continuous_corr U e _ _).norm h₁ h₂,
      fun t => ?_⟩
  rw [corr_add_right]
  beta_reduce
  linarith [norm_add_le (corr U e f g₁ t) (corr U e f g₂ t)]

private theorem isClosed_corrVanishes_left (hU : U.IsUnitary) (g : H) :
    IsClosed {f | CorrVanishes U e f g} := by
  refine isClosed_of_closure_subset fun f hf => ?_
  refine tendsto_average_of_forall_le (continuous_corr U e _ _).norm (fun _ => norm_nonneg _)
    fun ε hε => ?_
  have hC : 0 < (1 + ‖e‖ ^ 2) * (‖g‖ + 1) := by positivity
  obtain ⟨f', hf', hff'⟩ := Metric.mem_closure_iff.1 hf (ε / ((1 + ‖e‖ ^ 2) * (‖g‖ + 1)))
    (div_pos hε hC)
  refine ⟨fun t => ‖corr U e f' g t‖, (continuous_corr U e f' g).norm, hf', fun t => ?_⟩
  have hsplit : corr U e f g t = corr U e f' g t + corr U e (f - f') g t := by
    rw [← corr_add_left, add_sub_cancel]
  have hbound := norm_corr_le e hU (f - f') g t
  rw [← dist_eq_norm, dist_comm] at hbound
  have hlt : (1 + ‖e‖ ^ 2) * (dist f' f * ‖g‖) ≤ ε := by
    rw [lt_div_iff₀ hC] at hff'
    calc (1 + ‖e‖ ^ 2) * (dist f' f * ‖g‖) = dist f f' * ((1 + ‖e‖ ^ 2) * ‖g‖) := by
          rw [dist_comm]; ring
      _ ≤ dist f f' * ((1 + ‖e‖ ^ 2) * (‖g‖ + 1)) := by gcongr; linarith
      _ ≤ ε := hff'.le
  rw [hsplit]
  beta_reduce
  linarith [norm_add_le (corr U e f' g t) (corr U e (f - f') g t)]

private theorem isClosed_corrVanishes_right (hU : U.IsUnitary) (f : H) :
    IsClosed {g | CorrVanishes U e f g} := by
  refine isClosed_of_closure_subset fun g hg => ?_
  refine tendsto_average_of_forall_le (continuous_corr U e _ _).norm (fun _ => norm_nonneg _)
    fun ε hε => ?_
  have hC : 0 < (1 + ‖e‖ ^ 2) * (‖f‖ + 1) := by positivity
  obtain ⟨g', hg', hgg'⟩ := Metric.mem_closure_iff.1 hg (ε / ((1 + ‖e‖ ^ 2) * (‖f‖ + 1)))
    (div_pos hε hC)
  refine ⟨fun t => ‖corr U e f g' t‖, (continuous_corr U e f g').norm, hg', fun t => ?_⟩
  have hsplit : corr U e f g t = corr U e f g' t + corr U e f (g - g') t := by
    rw [← corr_add_right, add_sub_cancel]
  have hbound := norm_corr_le e hU f (g - g') t
  rw [← dist_eq_norm, dist_comm] at hbound
  have hlt : (1 + ‖e‖ ^ 2) * (‖f‖ * dist g' g) ≤ ε := by
    rw [lt_div_iff₀ hC] at hgg'
    calc (1 + ‖e‖ ^ 2) * (‖f‖ * dist g' g) = dist g g' * ((1 + ‖e‖ ^ 2) * ‖f‖) := by
          rw [dist_comm]; ring
      _ ≤ dist g g' * ((1 + ‖e‖ ^ 2) * (‖f‖ + 1)) := by gcongr; linarith
      _ ≤ ε := hgg'.le
  rw [hsplit]
  beta_reduce
  linarith [norm_add_le (corr U e f g' t) (corr U e f (g - g') t)]

end Correlation

/-! ### The `L²` form of weak mixing -/

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The constant function `1` in complex `L²(μ)`. -/
private def one : Lp ℂ 2 μ :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) 1

private theorem inner_one_left (f : Lp ℂ 2 μ) : ⟪(one : Lp ℂ 2 μ), f⟫_ℂ = ∫ x, f x ∂μ := by
  rw [one, L2.inner_indicatorConstLp_one, Measure.restrict_univ]

private theorem inner_one_right (g : Lp ℂ 2 μ) :
    ⟪g, (one : Lp ℂ 2 μ)⟫_ℂ = conj (∫ x, g x ∂μ) := by
  rw [← inner_conj_symm, inner_one_left]

variable [AddAction ℝ X] [MeasurableVAdd₂ ℝ X] [VAddInvariantMeasure ℝ X μ]

private theorem corr_koopmanGroup (f g : Lp ℂ 2 μ) (t : ℝ) :
    corr (koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top) one f g t =
      ⟪g, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t f⟫_ℂ -
        (∫ x, f x ∂μ) * conj (∫ x, g x ∂μ) := by
  unfold corr
  rw [inner_one_left, inner_one_right]
  rfl

/-- The Koopman operator at time `t` sends the indicator of `A` to the indicator of
`(t +ᵥ ·)⁻¹' A`. -/
private theorem koopmanGroup_indicatorConstLp {A : Set X} (hA : MeasurableSet A) (c : ℂ) (t : ℝ) :
    koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t (indicatorConstLp 2 hA (measure_ne_top μ A) c) =
      indicatorConstLp 2 (hA.preimage (measurable_const_vadd t)) (measure_ne_top μ _) c :=
  (Eq.congr_left (koopmanGroup_apply μ ℂ 2 ENNReal.ofNat_ne_top t _)).2
    (Lp.indicatorConstLp_compMeasurePreserving hA _ c (measurePreserving_vadd t μ))

/-- The centered correlation of two indicator functions. -/
private theorem corr_indicatorConstLp {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (c d : ℂ) (t : ℝ) :
    corr (koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top) one
        (indicatorConstLp 2 hA (measure_ne_top μ A) c)
        (indicatorConstLp 2 hB (measure_ne_top μ B) d) t =
      (conj d * c) * ((μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ B) - μ.real A * μ.real B : ℝ) : ℂ) := by
  rw [corr_koopmanGroup, koopmanGroup_indicatorConstLp, ← inner_one_left, ← inner_one_right,
    one, L2.inner_indicatorConstLp_indicatorConstLp, L2.inner_indicatorConstLp_indicatorConstLp,
    L2.inner_indicatorConstLp_indicatorConstLp, univ_inter, inter_univ, inter_comm B]
  simp only [RCLike.inner_apply, map_one, one_mul, mul_one, Complex.real_smul]
  push_cast
  ring

private theorem norm_corr_indicatorConstLp {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (c d : ℂ) (t : ℝ) :
    ‖corr (koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top) one
        (indicatorConstLp 2 hA (measure_ne_top μ A) c)
        (indicatorConstLp 2 hB (measure_ne_top μ B) d) t‖ =
      ‖d‖ * ‖c‖ * |μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ B) - μ.real A * μ.real B| := by
  rw [corr_indicatorConstLp, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real,
    Real.norm_eq_abs]

/-- **The `L²` form of weak mixing.** For a weakly mixing jointly measurable action of `ℝ`
preserving a probability measure `μ`, and all `f g` in complex `L²(μ)`, the centered correlations
`⟪g, U_t f⟫ - (∫ f) conj (∫ g)` of the Koopman group tend to `0` in Cesàro mean in absolute
value. -/
theorem IsWeaklyMixing.tendsto_average_norm_inner_koopmanGroup (h : IsWeaklyMixing μ)
    (f g : Lp ℂ 2 μ) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
        ‖⟪g, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t f⟫_ℂ -
          (∫ x, f x ∂μ) * conj (∫ x, g x ∂μ)‖) atTop (𝓝 0) := by
  have hU := koopmanGroup_isUnitary μ ℂ
  suffices hfg : CorrVanishes (koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top) one f g by
    simp only [CorrVanishes, corr_koopmanGroup] at hfg
    exact hfg
  -- Indicator functions.
  have hind : ∀ {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (c d : ℂ),
      CorrVanishes (koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top) one
        (indicatorConstLp 2 hA (measure_ne_top μ A) c)
        (indicatorConstLp 2 hB (measure_ne_top μ B) d) := by
    intro A B hA hB c d
    simp only [CorrVanishes, norm_corr_indicatorConstLp, intervalIntegral.integral_const_mul]
    simpa [mul_left_comm _ (‖d‖ * ‖c‖)] using
      (isWeaklyMixing_def.1 h A B hA hB).const_mul (‖d‖ * ‖c‖)
  -- The first variable.
  have hleft : ∀ {B : Set X} (hB : MeasurableSet B) (d : ℂ) (f : Lp ℂ 2 μ),
      CorrVanishes (koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top) one f
        (indicatorConstLp 2 hB (measure_ne_top μ B) d) := by
    intro B hB d f
    induction f using Lp.induction (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ∞) with
    | indicatorConst c hA _ => exact hind hA hB c d
    | add _ _ _ h₁ h₂ => exact corrVanishes_add_left one h₁ h₂
    | isClosed => exact isClosed_corrVanishes_left one hU _
  induction g using Lp.induction (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ ∞) with
  | indicatorConst d hB _ => exact hleft hB d f
  | add _ _ _ h₁ h₂ => exact corrVanishes_add_right one h₁ h₂
  | isClosed => exact isClosed_corrVanishes_right one hU f

/-- **Weak mixing is equivalent to its `L²` form.** A jointly measurable action of `ℝ` preserving
a probability measure `μ` is weakly mixing exactly when, for all `f g` in complex `L²(μ)`, the
centered correlations `⟪g, U_t f⟫ - (∫ f) conj (∫ g)` of the Koopman group tend to `0` in Cesàro
mean in absolute value. -/
theorem isWeaklyMixing_iff_tendsto_average_norm_inner_koopmanGroup :
    IsWeaklyMixing μ ↔ ∀ f g : Lp ℂ 2 μ,
      Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
        ‖⟪g, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t f⟫_ℂ -
          (∫ x, f x ∂μ) * conj (∫ x, g x ∂μ)‖) atTop (𝓝 0) := by
  refine ⟨fun h => h.tendsto_average_norm_inner_koopmanGroup,
    fun h => isWeaklyMixing_def.2 fun A B hA hB => ?_⟩
  have := h (indicatorConstLp 2 hA (measure_ne_top μ A) 1)
    (indicatorConstLp 2 hB (measure_ne_top μ B) 1)
  simp_rw [← corr_koopmanGroup, norm_corr_indicatorConstLp, norm_one, one_mul] at this
  exact this

/-! ### Eigenfunctions of a weakly mixing action -/

/-- **Eigenfunctions of a weakly mixing action are constant.** For a weakly mixing jointly
measurable action of `ℝ` preserving a probability measure `μ`, every a.e. strongly measurable
`f : X → ℂ` with, for some `a` and every `t`, `f(t +ᵥ x) = exp(2πiat) f(x)` for almost every `x`,
is almost everywhere constant. This is one half of the eigenfunction criterion for weak mixing. -/
theorem IsWeaklyMixing.exists_ae_eq_const_of_eigenfunction (h : IsWeaklyMixing μ) {f : X → ℂ}
    (hf : AEStronglyMeasurable f μ) {a : ℝ}
    (heig : ∀ t : ℝ, (fun x => f (t +ᵥ x)) =ᵐ[μ]
      fun x => Complex.exp (2 * Real.pi * a * t * Complex.I) * f x) :
    ∃ c : ℂ, f =ᵐ[μ] Function.const X c := by
  have := h.ergodicVAdd
  rcases eq_or_ne a 0 with rfl | ha
  · refine ErgodicVAdd.ae_eq_const_of_forall_ae_eq_comp_vadd₀ ℝ hf.aemeasurable.nullMeasurable
      fun t => ?_
    filter_upwards [heig t] with x hx
    simpa using hx
  refine ⟨0, ?_⟩
  have hF := memLp_of_eigenfunction 2 hf heig
  set F := hF.toLp f
  -- The integral of `f` vanishes: it is multiplied by `exp(2πia t) = -1` at `t = 1/(2a)`.
  have hint : ∫ x, f x ∂μ = 0 := by
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    have hcomp := (measurePreserving_vadd (1 / (2 * a)) μ).integral_comp
      (MeasurableEquiv.vadd (1 / (2 * a)) : X ≃ᵐ X).measurableEmbedding f
    rw [integral_congr_ae (heig _), integral_const_mul,
      show 2 * (Real.pi : ℂ) * a * ((1 / (2 * a) : ℝ) : ℂ) * Complex.I = Real.pi * Complex.I by
        push_cast; field_simp] at hcomp
    simp only [Complex.exp_pi_mul_I] at hcomp
    linear_combination -hcomp / 2
  have hFint : ∫ x, F x ∂μ = 0 := by
    rw [integral_congr_ae hF.coeFn_toLp, hint]
  -- The centered correlation of `F` with itself has constant absolute value `‖F‖²`.
  have heigF : ∀ t : ℝ, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t F =
      Complex.exp ((2 * Real.pi * a : ℝ) * t * Complex.I) • F :=
    (Semigroups.StronglyContinuousGroup.mem_eigenspace_iff _ _ _ _).1
      (toLp_mem_eigenspace_koopmanGroup hf heig)
  have hcorr : ∀ t : ℝ, ‖⟪F, koopmanGroup μ ℂ 2 ENNReal.ofNat_ne_top t F⟫_ℂ -
      (∫ x, F x ∂μ) * conj (∫ x, F x ∂μ)‖ = ‖F‖ ^ 2 := by
    intro t
    rw [hFint, zero_mul, sub_zero, heigF t, inner_smul_right, inner_self_eq_norm_sq_to_K,
      norm_mul]
    simp only [show ((2 * Real.pi * a : ℝ) : ℂ) * t * Complex.I = ((2 * Real.pi * a * t : ℝ) : ℂ) *
      Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]
    norm_cast
    exact abs_of_nonneg (by positivity)
  have hlim := h.tendsto_average_norm_inner_koopmanGroup F F
  simp_rw [hcorr, intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hlim
  have hconst : Tendsto (fun T : ℝ => T⁻¹ * (T * ‖F‖ ^ 2)) atTop (𝓝 (‖F‖ ^ 2)) :=
    tendsto_const_nhds.congr' (eventually_gt_atTop 0 |>.mono fun T hT => by field_simp)
  have hF0 : F = 0 := by
    have := tendsto_nhds_unique hconst hlim
    simpa using this
  filter_upwards [hF.coeFn_toLp, (Lp.ext_iff.1 hF0).trans (Lp.coeFn_zero ℂ 2 μ)] with x h₁ h₂
  rw [← h₁, h₂]
  rfl

end MeasureTheory.Measure

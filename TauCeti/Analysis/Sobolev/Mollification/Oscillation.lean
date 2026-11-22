/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.Average
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic

import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Calculus.BumpFunction.Oscillation
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.WeakDeriv
import TauCeti.MeasureTheory.Function.LpSeminorm.Ball

/-!
# Sobolev mollification oscillation bounds

Let `E` be a finite-dimensional real normed space of dimension `n` with an additive Haar measure
`μ`, and let `u : E → F` have weak Fréchet derivative `Du` on an open set `Ω`
(`TauCeti.HasWeakFDerivOn μ Ω u Du`). Combining the normalized-bump oscillation bound
(`ContDiffBump.setLAverage_enorm_sub_normed_convolution_le`) with the Banach-valued
Poincaré–Wirtinger inequality on balls
(`TauCeti.HasWeakFDerivOn.setLAverage_enorm_sub_setAverage_ball_le_mul_rpow`) yields the Sobolev
mollification oscillation bound: for `ball x φ.rOut ⊆ Ω` and `1 ≤ p ≤ ∞`,

`⨍⁻ z in B(x, φ.rOut), ‖u z - (φ.normed μ ⋆ u) x‖ₑ`
`  ≤ (1 + (φ.rOut / φ.rIn) ^ n) * 2 ^ (n + 1) * ω ^ (-1 / p) * φ.rOut ^ (1 - n / p) * ‖Du‖_{Lᵖ(B)}`.

At the borderline exponent `p = n` (in positive dimension `n ≥ 1`), the radius cancels completely;
for any family of bumps with bounded aspect ratio `φᵢ.rOut / φᵢ.rIn ≤ κ` and `φᵢ.rOut → 0`, the
oscillation `⨍⁻ z in B(x, φᵢ.rOut), ‖u z - (φᵢ.normed μ ⋆ u) x‖ₑ` vanishes uniformly over compact
subsets (when extended by zero outside `V ≤ Ω`, via
`ContDiffBump.normed_convolution_indicator_eq_of_ball_subset`) and globally when `Du ∈ Lⁿ(μ)`, by
absolute continuity of the integral. This is the quantitative VMO estimate used to keep
mollifications of `W^{1,n}` maps close to a target submanifold in Schoen–Uhlenbeck approximation.

## Main declarations

* `TauCeti.HasWeakFDerivOn.setLAverage_enorm_sub_normed_convolution_le_mul_rpow` and
  `TauCeti.HasWeakFDerivOn.setLAverage_enorm_sub_normed_convolution_le`: Sobolev
  mollification oscillation bounds for all `1 ≤ p ≤ ∞` and at the scale-invariant exponent `p = n`.
* `TauCeti.HasWeakFDerivOn.tendsto_iSup_setLAverage_enorm_sub_normed_convolution_indicator` and
  `TauCeti.HasWeakFDerivOn.tendsto_iSup_setLAverage_enorm_sub_normed_convolution`: uniform
  vanishing of the mollification oscillation at `p = n` on compact subsets and globally.

## References

* P. Hajłasz, *Sobolev mappings between manifolds and metric spaces*, in *Sobolev Spaces in
  Mathematics I*, Int. Math. Ser. (N.Y.) **8**, Springer (2009), 185–222, inequality (2.1).
* R. Schoen, K. Uhlenbeck, *Boundary regularity and the Dirichlet problem for harmonic maps*,
  J. Differential Geom. **18** (1983), 253–268, §4.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter MeasureTheory Metric Module Set TopologicalSpace
open scoped Convolution ENNReal Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {u : E → F} {Du : E → E →L[ℝ] F}

/-- **Sobolev mollification oscillation bound.** For a weakly differentiable function `u : E → F`
on `Ω`, a normalized bump `φ`, a point `x` with `ball x φ.rOut ⊆ Ω`, and any exponent `1 ≤ p ≤ ∞`,

`⨍⁻ z in B(x, φ.rOut), ‖u z - (φ.normed μ ⋆ u) x‖ₑ`
`  ≤ (1 + (φ.rOut / φ.rIn) ^ n) * 2 ^ (n + 1) * ω ^ (-1 / p) * φ.rOut ^ (1 - n / p) * ‖Du‖_{Lᵖ(B)}`.

No a priori integrability assumption on `u` or `Du` is required. -/
theorem HasWeakFDerivOn.setLAverage_enorm_sub_normed_convolution_le_mul_rpow
    (hu : HasWeakFDerivOn μ Ω u Du) (φ : ContDiffBump (0 : E)) {x : E}
    (hball : ball x φ.rOut ⊆ Ω) {p : ℝ≥0∞} (hp1 : 1 ≤ p) :
    ⨍⁻ z in ball x φ.rOut, ‖u z - (φ.normed μ ⋆[lsmul ℝ ℝ, μ] u) x‖ₑ ∂μ ≤
      ENNReal.ofReal ((1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) * 2 ^ (finrank ℝ E + 1) *
          μ.real (ball 0 1) ^ (-p.toReal⁻¹) * φ.rOut ^ (1 - (finrank ℝ E : ℝ) / p.toReal)) *
        eLpNorm Du p (μ.restrict (ball x φ.rOut)) := by
  have : CompleteSpace F := hu.completeSpace
  have hK1 : 0 < 1 + (φ.rOut / φ.rIn) ^ finrank ℝ E := by
    have : 0 ≤ (φ.rOut / φ.rIn) ^ finrank ℝ E := by positivity [φ.rOut_pos.le, φ.rIn_pos.le]
    linarith
  have hωpos : 0 < μ.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  have hK2 : 0 < 2 ^ (finrank ℝ E + 1) * μ.real (ball (0 : E) 1) ^ (-p.toReal⁻¹) *
      φ.rOut ^ (1 - (finrank ℝ E : ℝ) / p.toReal) :=
    mul_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos hωpos _))
      (Real.rpow_pos_of_pos φ.rOut_pos _)
  by_cases hDu_top : eLpNorm Du p (μ.restrict (ball x φ.rOut)) = ∞
  · have hCpos : 0 < (1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) * 2 ^ (finrank ℝ E + 1) *
        μ.real (ball (0 : E) 1) ^ (-p.toReal⁻¹) * φ.rOut ^ (1 - (finrank ℝ E : ℝ) / p.toReal) := by
      simpa only [mul_assoc] using mul_pos hK1 hK2
    rw [hDu_top, ENNReal.mul_top (ENNReal.ofReal_pos.2 hCpos).ne']
    exact le_top
  · -- Finite `Lᵖ` seminorm of `Du` on the ball forces `u` to be integrable on the ball.
    have : IsFiniteMeasure (μ.restrict (ball x φ.rOut)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have hDup : MemLp Du p (μ.restrict (ball x φ.rOut)) := lt_top_iff_ne_top.2 hDu_top
    have hDu1 : MemLp Du 1 (μ.restrict (ball x φ.rOut)) := hDup.mono_exponent hp1
    let B : Opens E := ⟨ball x φ.rOut, isOpen_ball⟩
    have hB : HasWeakFDerivOn μ B u Du := hu.mono hball
    have hu1 : IntegrableOn u (ball x φ.rOut) μ :=
      memLp_one_iff_integrable.1 <|
        hB.memLp_of_convex (convex_ball x φ.rOut) isBounded_ball le_rfl ENNReal.one_ne_top hDu1
    calc ⨍⁻ z in ball x φ.rOut, ‖u z - (φ.normed μ ⋆[lsmul ℝ ℝ, μ] u) x‖ₑ ∂μ
        ≤ ENNReal.ofReal (1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) *
            ⨍⁻ z in ball x φ.rOut, ‖u z - ⨍ w in ball x φ.rOut, u w ∂μ‖ₑ ∂μ :=
          φ.setLAverage_enorm_sub_normed_convolution_le hu1
      _ ≤ ENNReal.ofReal (1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) *
            (ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * μ.real (ball 0 1) ^ (-p.toReal⁻¹) *
                φ.rOut ^ (1 - (finrank ℝ E : ℝ) / p.toReal)) *
              eLpNorm Du p (μ.restrict (ball x φ.rOut))) :=
          mul_le_mul_right
            (hu.setLAverage_enorm_sub_setAverage_ball_le_mul_rpow φ.rOut_pos hball hp1) _
      _ = ENNReal.ofReal ((1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) * 2 ^ (finrank ℝ E + 1) *
            μ.real (ball 0 1) ^ (-p.toReal⁻¹) * φ.rOut ^ (1 - (finrank ℝ E : ℝ) / p.toReal)) *
          eLpNorm Du p (μ.restrict (ball x φ.rOut)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hK1.le]
          congr 2
          ring

/-- **Scale-invariant Sobolev mollification oscillation bound at the borderline exponent `p = n`.**
In positive dimension `n = finrank ℝ E ≥ 1`, for `ball x φ.rOut ⊆ Ω`,

`⨍⁻ z in B(x, φ.rOut), ‖u z - (φ.normed μ ⋆ u) x‖ₑ`
`  ≤ (1 + (φ.rOut / φ.rIn) ^ n) * 2 ^ (n + 1) * ω ^ (-1 / n) * ‖Du‖_{Lⁿ(B(x, φ.rOut))}`.

The radius cancels completely; only the aspect ratio `φ.rOut / φ.rIn` enters the constant. -/
theorem HasWeakFDerivOn.setLAverage_enorm_sub_normed_convolution_le [Nontrivial E]
    (hu : HasWeakFDerivOn μ Ω u Du) (φ : ContDiffBump (0 : E)) {x : E}
    (hball : ball x φ.rOut ⊆ Ω) :
    ⨍⁻ z in ball x φ.rOut, ‖u z - (φ.normed μ ⋆[lsmul ℝ ℝ, μ] u) x‖ₑ ∂μ ≤
      ENNReal.ofReal ((1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) * 2 ^ (finrank ℝ E + 1) *
          μ.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹)) *
        eLpNorm Du (finrank ℝ E) (μ.restrict (ball x φ.rOut)) := by
  have hn : 1 ≤ (finrank ℝ E : ℝ≥0∞) := by exact_mod_cast finrank_pos
  have hn0 : (finrank ℝ E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 finrank_pos.ne'
  have h := hu.setLAverage_enorm_sub_normed_convolution_le_mul_rpow φ hball hn
  simpa only [ENNReal.toReal_natCast, div_self hn0, sub_self, Real.rpow_zero, mul_one] using h

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The scale-invariant `p = n` oscillation constant for aspect ratio bound `κ`. -/
private def oscillationConst (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) (κ : ℝ) : ℝ :=
  (1 + (max κ 0) ^ finrank ℝ E) * 2 ^ (finrank ℝ E + 1) *
    μ.real (ball (0 : E) 1) ^ (-(finrank ℝ E : ℝ)⁻¹)

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Monotonicity of the scale-invariant `p = n` oscillation constant in the aspect ratio bound. -/
private theorem oscillationConst_le (φ : ContDiffBump (0 : E)) {κ : ℝ}
    (hκ : φ.rOut ≤ κ * φ.rIn) :
    (1 + (φ.rOut / φ.rIn) ^ finrank ℝ E) * 2 ^ (finrank ℝ E + 1) *
        μ.real (ball (0 : E) 1) ^ (-(finrank ℝ E : ℝ)⁻¹) ≤
      oscillationConst E μ κ := by
  have hratio : φ.rOut / φ.rIn ≤ max κ 0 :=
    ((div_le_iff₀ φ.rIn_pos).2 hκ).trans (le_max_left κ 0)
  have hr0 : 0 ≤ φ.rOut / φ.rIn := div_nonneg φ.rOut_pos.le φ.rIn_pos.le
  unfold oscillationConst
  gcongr

/-- **Uniform vanishing of the mollification oscillation on compact subsets at `p = n`.** Let
`u : E → F` have weak Fréchet derivative `Du` on `Ω` in positive dimension `n`, let `K ⊆ V` be a
compact subset of an open set `V ≤ Ω` with `eLpNorm Du n (μ.restrict V) ≠ ∞`, and let `φ i` be
bumps with `(φ i).rOut → 0` and uniformly bounded aspect ratio `(φ i).rOut ≤ κ * (φ i).rIn`. Then
the mean deviation of `u` from its interior mollification `φ i ⋆ V.indicator u` over
`B(x, (φ i).rOut)` tends to `0` uniformly over `x ∈ K`. -/
theorem HasWeakFDerivOn.tendsto_iSup_setLAverage_enorm_sub_normed_convolution_indicator
    [Nontrivial E] (hu : HasWeakFDerivOn μ Ω u Du) {V : Opens E} (hVΩ : V ≤ Ω)
    {K : Set E} (hK : IsCompact K) (hKV : K ⊆ V)
    (hDu : eLpNorm Du (finrank ℝ E) (μ.restrict V) ≠ ∞)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    {κ : ℝ} (hκ : ∀ᶠ i in l, (φ i).rOut ≤ κ * (φ i).rIn) :
    Tendsto (fun i => ⨆ x ∈ K, ⨍⁻ z in ball x (φ i).rOut,
        ‖u z - ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] (V : Set E).indicator u) x‖ₑ ∂μ)
      l (𝓝 0) := by
  have hDext : eLpNorm ((V : Set E).indicator Du) (finrank ℝ E) μ ≠ ∞ := by
    rwa [eLpNorm_indicator_eq_eLpNorm_restrict (f := Du) V.isOpen.measurableSet.nullMeasurableSet]
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open V.isOpen hKV
  refine tendsto_zero_of_eventually_le_mul_iSup_eLpNorm_restrict_ball
    (Nat.cast_ne_zero.2 finrank_pos.ne') (ENNReal.natCast_ne_top _) hDext hφ
    (C := ENNReal.ofReal (oscillationConst E μ κ)) ?_ ENNReal.ofReal_ne_top
  filter_upwards [hφ.eventually (gt_mem_nhds hδ), hκ] with i hi hκi
  refine iSup₂_le fun x hx => ?_
  have hball : ball x (φ i).rOut ⊆ V := fun y hy =>
    hδV (mem_cthickening_of_dist_le y x δ K hx ((mem_ball.1 hy).trans hi).le)
  have hDu_eq : eLpNorm Du (finrank ℝ E) (μ.restrict (ball x (φ i).rOut)) =
      eLpNorm ((V : Set E).indicator Du) (finrank ℝ E) (μ.restrict (ball x (φ i).rOut)) :=
    eLpNorm_congr_ae <| ae_restrict_of_forall_mem isOpen_ball.measurableSet fun y hy =>
      (Set.indicator_of_mem (hball hy) Du).symm
  rw [(φ i).normed_convolution_indicator_eq_of_ball_subset hball]
  refine (hu.setLAverage_enorm_sub_normed_convolution_le (φ i)
    (hball.trans (SetLike.coe_subset_coe.2 hVΩ))).trans ?_
  rw [hDu_eq]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (oscillationConst_le (φ i) hκi))
    (le_iSup (fun c => eLpNorm ((V : Set E).indicator Du) (finrank ℝ E)
      (μ.restrict (ball c (φ i).rOut))) x)

/-- **Global uniform vanishing of the mollification oscillation at `p = n`.** For a globally weakly
differentiable function `u : E → F` in positive dimension `n` with `eLpNorm Du n μ ≠ ∞` and bumps
`φ i` with `(φ i).rOut → 0` and uniformly bounded aspect ratio `(φ i).rOut ≤ κ * (φ i).rIn`, the
mean deviation of `u` from `(φ i).normed μ ⋆ u` over `B(x, (φ i).rOut)` tends to `0` uniformly over
all `x : E`. -/
theorem HasWeakFDerivOn.tendsto_iSup_setLAverage_enorm_sub_normed_convolution
    [Nontrivial E] (hu : HasWeakFDerivOn μ ⊤ u Du) (hDu : eLpNorm Du (finrank ℝ E) μ ≠ ∞)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : E)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    {κ : ℝ} (hκ : ∀ᶠ i in l, (φ i).rOut ≤ κ * (φ i).rIn) :
    Tendsto (fun i => ⨆ x : E, ⨍⁻ z in ball x (φ i).rOut,
        ‖u z - ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] u) x‖ₑ ∂μ)
      l (𝓝 0) := by
  refine tendsto_zero_of_eventually_le_mul_iSup_eLpNorm_restrict_ball
    (Nat.cast_ne_zero.2 finrank_pos.ne') (ENNReal.natCast_ne_top _) hDu hφ
    (C := ENNReal.ofReal (oscillationConst E μ κ)) ?_ ENNReal.ofReal_ne_top
  filter_upwards [hκ] with i hκi
  refine iSup_le fun x => ?_
  refine (hu.setLAverage_enorm_sub_normed_convolution_le (φ i) (subset_univ _)).trans ?_
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (oscillationConst_le (φ i) hκi))
    (le_iSup (fun c => eLpNorm Du (finrank ℝ E) (μ.restrict (ball c (φ i).rOut))) x)

end TauCeti

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.Action.Koopman
public import TauCeti.Dynamics.Ergodic.Action.WeakMixing.Basic
public import TauCeti.MeasureTheory.Group.Action
import TauCeti.Analysis.Semigroups.Group.MeanErgodic
import TauCeti.Analysis.SpecificLimits.Cesaro.Integral
import TauCeti.Dynamics.Ergodic.Action.MeanErgodic
import TauCeti.Analysis.InnerProductSpace.L2.Product
import TauCeti.MeasureTheory.Function.L2Space

/-!
# The multiplier property of weak mixing

Let `ℝ` act jointly measurably on `X` and on `Y`, preserving probability measures `μ` and `ν`, and
let `ℝ` act on `X × Y` diagonally, `t +ᵥ (x, y) = (t +ᵥ x, t +ᵥ y)`. If the action on `X` is weakly
mixing and the action on `Y` is ergodic, then the diagonal action is ergodic for `μ.prod ν`
(`MeasureTheory.Measure.ergodicVAdd_prod_of_isWeaklyMixing`).

The proof goes through the Koopman groups `U_t f = f ∘ (t +ᵥ ·)` on complex `L²`, and uses that
an action preserving a finite measure is ergodic exactly when the only Koopman-fixed vectors are
the almost everywhere constant functions (`TauCeti.ergodicVAdd_of_forall_koopmanGroup_eq`).

* For indicators of rectangles `F₁ = 1_{C × D}`, `F₂ = 1_{A × B}`, the correlation
  `⟪F₁, U_t F₂⟫` is the product `c₁(t) c₂(t)` of `c₁(t) = μ((t +ᵥ ·)⁻¹' A ∩ C)` and
  `c₂(t) = ν((t +ᵥ ·)⁻¹' B ∩ D)`. Weak mixing gives `T⁻¹ ∫₀ᵀ |c₁(t) - μ(A) μ(C)| dt → 0`, and
  ergodicity of `Y` gives `T⁻¹ ∫₀ᵀ c₂(t) dt → ν(B) ν(D)`
  (`TauCeti.tendsto_average_inner_koopmanGroup_of_ergodicVAdd`). As `0 ≤ c₂ ≤ 1`, the averaged
  correlation tends to `μ(A) μ(C) ν(B) ν(D) = ⟪F₁, 1⟫ ⟪1, F₂⟫`
  (`TauCeti.tendsto_average_mul_of_tendsto_average_abs_sub`).
* So the mean ergodic limit `P F₂` of the averages of `U_t F₂` has the same inner products with
  rectangle indicators as `⟪1, F₂⟫ 1`. Indicators of rectangles are total in `L²(μ.prod ν)`
  (`MeasureTheory.Lp.eq_zero_of_forall_inner_indicatorConstLp_prod`), so `P F₂ = ⟪1, F₂⟫ 1`. For a
  vector `F` fixed by the Koopman group, `⟪F, F₂⟫ = ⟪F, U_t F₂⟫` for every `t`, hence
  `⟪F, F₂⟫ = ⟪F, P F₂⟫ = ⟪F, 1⟫ ⟪1, F₂⟫`, and the totality of rectangle indicators again shows
  `F = ⟪1, F⟫ 1`.

## Main results

* `MeasureTheory.Measure.ergodicVAdd_prod_of_isWeaklyMixing`: the multiplier property of weak
  mixing.

## References

* M. Hochman, *Notes on ergodic theory*, 2012, Proposition 6.2.1 (for actions of `ℤ`).
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology ENNReal ComplexConjugate InnerProductSpace

namespace MeasureTheory.Measure

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [AddAction ℝ X] [AddAction ℝ Y]
  [MeasurableVAdd₂ ℝ X] [MeasurableVAdd₂ ℝ Y] {μ : Measure X} {ν : Measure Y}

/-- The indicator of a measurable rectangle in complex `L²(μ.prod ν)`. -/
private abbrev rectL2 [IsFiniteMeasure μ] [IsFiniteMeasure ν] {A : Set X} {B : Set Y}
    (hA : MeasurableSet A) (hB : MeasurableSet B) : Lp ℂ 2 (μ.prod ν) :=
  indicatorConstLp 2 (hA.prod hB) (measure_ne_top _ _) 1

omit [AddAction ℝ X] [AddAction ℝ Y] [MeasurableVAdd₂ ℝ X] [MeasurableVAdd₂ ℝ Y] in
private theorem integral_rectL2 [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {A : Set X}
    {B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫ z, rectL2 (μ := μ) (ν := ν) hA hB z ∂(μ.prod ν) = (μ.real A * ν.real B : ℝ) := by
  simp only [rectL2, integral_indicatorConstLp, measureReal_prod_prod]
  simp

/-- The Koopman correlation of two rectangles is the product of the correlations of the sides. -/
private theorem inner_rectL2_koopmanGroup [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [VAddInvariantMeasure ℝ X μ] [VAddInvariantMeasure ℝ Y ν] {A C : Set X} {B D : Set Y}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (t : ℝ) :
    ⟪rectL2 hC hD, TauCeti.koopmanGroup (μ.prod ν) ℂ 2 ENNReal.ofNat_ne_top t (rectL2 hA hB)⟫_ℂ =
      ((μ.real ((fun x => t +ᵥ x) ⁻¹' A ∩ C) * ν.real ((fun y => t +ᵥ y) ⁻¹' B ∩ D) : ℝ) :
        ℂ) := by
  have hpre : (fun z : X × Y => t +ᵥ z) ⁻¹' A ×ˢ B =
      ((fun x => t +ᵥ x) ⁻¹' A) ×ˢ ((fun y => t +ᵥ y) ⁻¹' B) := rfl
  rw [TauCeti.inner_indicatorConstLp_koopmanGroup (μ.prod ν) (hA.prod hB) (hC.prod hD) t, hpre,
    prod_inter_prod, measureReal_prod_prod]

/-- The averaged Koopman correlations of two rectangles, for `X` weakly mixing and `Y` ergodic,
tend to `μ(A) μ(C) ν(B) ν(D)`. -/
private theorem tendsto_average_inner_rectL2 [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [VAddInvariantMeasure ℝ X μ] [ErgodicVAdd ℝ Y ν] (hμ : IsWeaklyMixing μ) {A C : Set X}
    {B D : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hD : MeasurableSet D) :
    Tendsto (fun T : ℝ => (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, ⟪rectL2 hC hD,
        TauCeti.koopmanGroup (μ.prod ν) ℂ 2 ENNReal.ofNat_ne_top t (rectL2 hA hB)⟫_ℂ) atTop
      (𝓝 (((μ.real A * μ.real C) * (ν.real B * ν.real D) : ℝ) : ℂ)) := by
  -- the second factor, by ergodicity of `ν`
  have h₂ : Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T,
      ν.real ((fun y => t +ᵥ y) ⁻¹' B ∩ D)) atTop (𝓝 (ν.real B * ν.real D)) := by
    have h := TauCeti.tendsto_average_inner_koopmanGroup_of_ergodicVAdd
      (indicatorConstLp 2 hB (measure_ne_top ν B) (1 : ℂ))
      (indicatorConstLp 2 hD (measure_ne_top ν D) (1 : ℂ))
    simp only [TauCeti.inner_indicatorConstLp_koopmanGroup ν hB hD,
      intervalIntegral.integral_ofReal, integral_indicatorConstLp] at h
    have h' := (Complex.continuous_re.tendsto _).comp h
    simpa only [Function.comp_def, ← Complex.ofReal_inv, Complex.real_smul, mul_one,
      Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re] using h'
  have hlim := TauCeti.tendsto_average_mul_of_tendsto_average_abs_sub
    (fun T => (TauCeti.continuous_measureReal_preimage_vadd_inter μ hA hC).intervalIntegrable 0 T)
    (fun T => (TauCeti.continuous_measureReal_preimage_vadd_inter ν hB hD).intervalIntegrable 0 T)
    (C := 1) (fun t => by
      rw [abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one) ((isWeaklyMixing_def.1 hμ) A C hA hC) h₂
  simp_rw [inner_rectL2_koopmanGroup hA hB hC hD, intervalIntegral.integral_ofReal]
  refine ((Complex.continuous_ofReal.tendsto _).comp hlim).congr fun T => ?_
  simp

/-- For `X` weakly mixing and `Y` ergodic, the averaged Koopman correlations of any `F` with a
rectangle `G` tend to `(∫ G) conj (∫ F)`. -/
private theorem tendsto_average_inner_koopmanGroup_rectL2 [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [VAddInvariantMeasure ℝ X μ] [ErgodicVAdd ℝ Y ν]
    (hμ : IsWeaklyMixing μ) {A : Set X} {B : Set Y} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (F : Lp ℂ 2 (μ.prod ν)) :
    Tendsto (fun T : ℝ => (T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T,
        ⟪F, TauCeti.koopmanGroup (μ.prod ν) ℂ 2 ENNReal.ofNat_ne_top t (rectL2 hA hB)⟫_ℂ) atTop
      (𝓝 ((∫ z, rectL2 (μ := μ) (ν := ν) hA hB z ∂(μ.prod ν)) *
        conj (∫ z, F z ∂(μ.prod ν)))) := by
  set U := TauCeti.koopmanGroup (μ.prod ν) ℂ 2 ENNReal.ofNat_ne_top
  have hU : U.IsUnitary := TauCeti.koopmanGroup_isUnitary (μ.prod ν) ℂ
  have := TauCeti.Semigroups.StronglyContinuousGroup.hasOrthogonalProjection_fixedSubmodule U
    hU.isComplexLinear
  set K := U.fixedSubmodule hU.isComplexLinear
  suffices hLc : K.starProjection (rectL2 hA hB) =
      Lp.const 2 (μ.prod ν) (∫ z, rectL2 (μ := μ) (ν := ν) hA hB z ∂(μ.prod ν)) from
    TauCeti.tendsto_average_inner_koopmanGroup_of_sub_const_mem_orthogonal
      (hLc ▸ K.sub_starProjection_mem_orthogonal _) F
  rw [← sub_eq_zero]
  refine Lp.eq_zero_of_forall_inner_indicatorConstLp_prod _ fun C D hC hD => ?_
  have h₁ := tendsto_nhds_unique (hU.tendsto_average_inner (rectL2 hA hB) (rectL2 hC hD))
    (tendsto_average_inner_rectL2 hμ hA hB hC hD)
  rw [inner_sub_right, h₁, L2.inner_const_right, RCLike.inner_apply, integral_rectL2 hA hB,
    integral_rectL2 hC hD, sub_eq_zero, Complex.conj_ofReal]
  push_cast
  ring

/-- **The multiplier property of weak mixing.** Let `ℝ` act jointly measurably on `X` and on `Y`,
preserving probability measures `μ` and `ν`. If the action on `X` is weakly mixing and the action
on `Y` is ergodic, then the diagonal action on `X × Y` is ergodic for `μ.prod ν`. -/
theorem ergodicVAdd_prod_of_isWeaklyMixing [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [VAddInvariantMeasure ℝ X μ] [ErgodicVAdd ℝ Y ν] (hμ : IsWeaklyMixing μ) :
    ErgodicVAdd ℝ (X × Y) (μ.prod ν) := by
  refine TauCeti.ergodicVAdd_of_forall_koopmanGroup_eq fun F hF => ⟨∫ z, F z ∂(μ.prod ν), ?_⟩
  -- `F` minus its integral is orthogonal to every rectangle
  suffices hFc : F = Lp.const 2 (μ.prod ν) (∫ z, F z ∂(μ.prod ν)) by
    generalize ∫ z, F z ∂(μ.prod ν) = c at hFc ⊢
    rw [hFc]
    exact Lp.coeFn_const 2 (μ.prod ν) c
  rw [← sub_eq_zero]
  refine Lp.eq_zero_of_forall_inner_indicatorConstLp_prod _ fun A B hA hB => ?_
  have hconst : ⟪F, rectL2 hA hB⟫_ℂ =
      (∫ z, rectL2 (μ := μ) (ν := ν) hA hB z ∂(μ.prod ν)) * conj (∫ z, F z ∂(μ.prod ν)) :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun T hT =>
      ((TauCeti.koopmanGroup_isUnitary (μ.prod ν) ℂ).average_inner_of_forall_eq hF
        (rectL2 hA hB) hT).symm)) (tendsto_average_inner_koopmanGroup_rectL2 hμ hA hB F)
  -- conjugating, the same identity with the rectangle in the first slot
  have hconst' : ⟪rectL2 hA hB, F⟫_ℂ =
      conj (∫ z, rectL2 (μ := μ) (ν := ν) hA hB z ∂(μ.prod ν)) * ∫ z, F z ∂(μ.prod ν) := by
    rw [← inner_conj_symm, hconst, map_mul, Complex.conj_conj, mul_comm]
  rw [inner_sub_right, hconst', L2.inner_const_right, RCLike.inner_apply]
  exact sub_eq_zero.2 (mul_comm _ _)

end MeasureTheory.Measure

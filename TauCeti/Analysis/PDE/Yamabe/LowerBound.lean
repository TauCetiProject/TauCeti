/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Quotient
import TauCeti.MeasureTheory.Integral.AbsRpow
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support

/-!
# A lower bound for the Yamabe quotient

On a compact Riemannian manifold of dimension `n > 2`, the Yamabe quotient satisfies

`Q_g(u) ≥ -(∫ (Scal_g⁻) ^ (n / 2) dV_g) ^ (2 / n)`

for every `C¹` function `u`. Here `Scal_g⁻ = max (-Scal_g) 0` is the negative part of the
scalar curvature. Hölder's inequality with conjugate exponents `n / 2` and `n / (n - 2)`
controls the negative potential energy by the critical norm of `u`; the Dirichlet term is
nonnegative. In particular, the quotients of nonzero smooth functions are bounded below.

These are bounds for the differentiable-function quotient, not a construction of its weak
domain or a claim that its infimum is attained. Neither orientation nor absence of boundary
is needed for the estimate: it uses no integration by parts.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2
  (boundedness below of the Yamabe functional).
-/

public section

open Bundle MeasureTheory Module TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Yamabe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- Hölder's inequality controls the negative scalar-curvature term by the critical norm. -/
private theorem integral_scalarCurvature_negPart_mul_sq_le (hn : 2 < finrank ℝ E)
    {u : M → ℝ} (hu : Continuous u) :
    ∫ x, ((CovariantDerivative.leviCivitaConnection I M).scalarCurvature x)⁻ * u x ^ 2
        ∂riemannianVolume I M ≤
      (∫ x, ((CovariantDerivative.leviCivitaConnection I M).scalarCurvature x)⁻ ^
        ((finrank ℝ E : ℝ) / 2) ∂riemannianVolume I M) ^ (2 / (finrank ℝ E : ℝ)) *
      (∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M) ^
        (2 / criticalExponent (finrank ℝ E)) := by
  have hn' : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
  have hpq : ((finrank ℝ E : ℝ) / 2).HolderConjugate
      (criticalExponent (finrank ℝ E) / 2) := by
    rw [Real.holderConjugate_iff]
    constructor
    · linarith
    · rw [criticalExponent_def]
      field_simp
      ring
  have hS := (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := riemannianVolume I M) hpq
    (Filter.Eventually.of_forall fun x ↦ negPart_nonneg _)
    (Filter.Eventually.of_forall fun x ↦ sq_nonneg (u x))
    ((hS.neg.sup continuous_const).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((hu.pow 2).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hpow (x : M) : (u x ^ 2) ^ (criticalExponent (finrank ℝ E) / 2) =
      |u x| ^ criticalExponent (finrank ℝ E) := by
    rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  simpa only [hpow, one_div_div] using h

/-- **Lower bound for the Yamabe quotient.** In dimension `n > 2`, every `C¹` function on a
compact Riemannian manifold satisfies `Q_g(u) ≥ -‖Scal_g⁻‖_{L^{n/2}}`. The zero function is
included, using the total definition of the quotient. -/
theorem neg_integral_scalarCurvature_negPart_rpow_le_yamabeQuotient
    (hn : 2 < finrank ℝ E) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 1 u) :
    -(∫ x, ((CovariantDerivative.leviCivitaConnection I M).scalarCurvature x)⁻ ^
        ((finrank ℝ E : ℝ) / 2) ∂riemannianVolume I M) ^ (2 / (finrank ℝ E : ℝ)) ≤
      yamabeQuotient I u := by
  set S := (CovariantDerivative.leviCivitaConnection I M).scalarCurvature
  set μ := riemannianVolume I M
  set C := (∫ x, (S x)⁻ ^ ((finrank ℝ E : ℝ) / 2) ∂μ) ^ (2 / (finrank ℝ E : ℝ))
  have hC : 0 ≤ C := Real.rpow_nonneg (integral_nonneg fun x ↦
    Real.rpow_nonneg (negPart_nonneg _) _) _
  by_cases hu0 : u = 0
  · subst u
    simpa [yamabeQuotient_def, criticalExponent_pos hn |>.ne'] using neg_nonpos.mpr hC
  have hN : 0 < (∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂μ) ^
      (2 / criticalExponent (finrank ℝ E)) :=
    Real.rpow_pos_of_pos (integral_abs_rpow_pos hu.continuous hu0 (criticalExponent_pos hn)) _
  rw [yamabeQuotient_def, le_div_iff₀ hN]
  have hS : Continuous S :=
    (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous
  have hg : Continuous fun x ↦ ‖mgradient I u x‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using continuous_inner_mgradient hu hu
  have hE : Integrable (fun x ↦ conformalCoefficient (finrank ℝ E) *
      ‖mgradient I u x‖ ^ 2 + S x * u x ^ 2) μ :=
    ((continuous_const.mul hg).add (hS.mul (hu.continuous.pow 2))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hneg : Integrable (fun x ↦ (S x)⁻ * u x ^ 2) μ :=
    ((hS.neg.sup continuous_const).mul (hu.continuous.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    -C * (∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂μ) ^
        (2 / criticalExponent (finrank ℝ E))
      ≤ -(∫ x, (S x)⁻ * u x ^ 2 ∂μ) := by
        simpa only [neg_mul] using neg_le_neg
          (integral_scalarCurvature_negPart_mul_sq_le hn hu.continuous)
    _ = ∫ x, -((S x)⁻ * u x ^ 2) ∂μ := (integral_neg _).symm
    _ ≤ _ := by
      apply integral_mono hneg.neg hE
      intro x
      have hScal : -(S x)⁻ ≤ S x := by
        rw [neg_le]
        exact le_sup_left
      have hgrad : 0 ≤ conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 :=
        mul_nonneg (conformalCoefficient_pos hn).le (sq_nonneg _)
      simpa only [Pi.neg_apply, neg_mul] using
        (mul_le_mul_of_nonneg_right hScal (sq_nonneg (u x))).trans
          (le_add_of_nonneg_left hgrad)

/-- On a compact Riemannian manifold of dimension greater than two, the Yamabe quotients of
nonzero `C¹` functions form a set bounded below. In particular this bounds the smooth test
domain. -/
theorem bddBelow_image_yamabeQuotient (hn : 2 < finrank ℝ E) :
    BddBelow (yamabeQuotient I '' {u : M → ℝ | ContMDiff I 𝓘(ℝ) 1 u ∧ u ≠ 0}) := by
  refine ⟨-(∫ x, ((CovariantDerivative.leviCivitaConnection I M).scalarCurvature x)⁻ ^
    ((finrank ℝ E : ℝ) / 2) ∂riemannianVolume I M) ^ (2 / (finrank ℝ E : ℝ)), ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact neg_integral_scalarCurvature_negPart_rpow_le_yamabeQuotient hn hu.1

end TauCeti.Yamabe

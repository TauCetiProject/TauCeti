/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Quantile
-- Proof-only: weighted AM-GM with its equality case, the one-dimensional change of variables,
-- and functions with equal derivatives on an interval.
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Function.JacobianOneDim
import TauCeti.Analysis.MeanInequalities

/-!
# Equality in Brunn–Minkowski for convex sets: matching height quantiles

Let `K` and `L` be bounded Borel convex sets of positive volume in a finite-dimensional Euclidean
space, let `0 < θ < 1`, and let `e` be a unit vector. Write `z_K` and `z_L` for the quantile
functions of the height `⟪e, x⟫` of a point drawn uniformly from `K` and from `L`. This file shows
that if the multiplicative Brunn–Minkowski inequality
`volume K ^ (1 - θ) * volume L ^ θ ≤ volume ((1 - θ) • K + θ • L)` is an equality, then
`z_L - z_K` is constant on the levels `Ioo 0 1`. In other words, along each direction the heights
at which `K` and `L` cut off equal volume fractions differ by a constant, which may depend on the
direction.

This is the analytic core of the Kneser–Süss proof that equality in Brunn–Minkowski forces a
homothety. Put `z = (1 - θ) z_K + θ z_L`. The weighted sum of the hyperplane sections of `K` at
height `z_K τ` and of `L` at height `z_L τ` lies in the section of `(1 - θ) • K + θ • L` at height
`z τ`, so Brunn–Minkowski in the hyperplane bounds the section of the sum from below. The change
of variables `ζ = z τ` then gives
`volume ((1 - θ) • K + θ • L) ≥ ∫ τ in Ioo 0 1, z' τ * volume (section at z τ)`,
and by the derivative of the height quantile and weighted AM-GM the integrand is at least
`volume K ^ (1 - θ) * volume L ^ θ`. It is strictly larger wherever
`volume K / volume (K_{z_K τ}) ≠ volume L / volume (L_{z_L τ})`. These two ratios are `z_K'` and
`z_L'`, so under equality they agree on all of `Ioo 0 1` by continuity, and `z_L - z_K` is constant.

The estimate on sections is
`TauCeti.volume_hyperplaneSection_rpow_mul_volume_hyperplaneSection_rpow_le`.

## Main results

* `Convex.exists_quantile_map_inner_cond_eq_add_of_volume_le`: under equality in the
  multiplicative Brunn–Minkowski inequality, the height quantiles of `K` and `L` along any unit
  vector differ by a constant on `Ioo 0 1`.

## References

* H. Kneser and W. Süss, *Die Volumina in linearen Scharen konvexer Körper*, Mat. Tidsskr. B
  (1932), 19–25.
* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge University
  Press, 2014, Theorem 7.1.1 and its proof.
-/

public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal Pointwise RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable {e : E} {K L : Set E}

/-- **The Kneser–Süss integral inequality.** Along the weighted height quantile
`z = (1 - θ) z_K + θ z_L`, the derivative `z'` times the weighted geometric mean of the section
volumes of `K` at `z_K τ` and of `L` at `z_L τ`, integrated over `Ioo 0 1`, is at most the volume of
`(1 - θ) • K + θ • L`. -/
private theorem setLIntegral_ofReal_le_volume_smul_add_smul (hK : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hKm : MeasurableSet K) (hK0 : volume K ≠ 0)
    (hL : Convex ℝ L) (hLb : Bornology.IsBounded L) (hLm : MeasurableSet L)
    (hL0 : volume L ≠ 0) (he : ‖e‖ = 1) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∫⁻ τ in Ioo 0 1, ENNReal.ofReal
      (((1 - θ) * (volume.real K / volume.real {y : (ℝ ∙ e)ᗮ |
          (y : E) + ((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ K}) +
        θ * (volume.real L / volume.real {y : (ℝ ∙ e)ᗮ |
          (y : E) + ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ L})) *
      (volume.real {y : (ℝ ∙ e)ᗮ |
          (y : E) + ((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ K} ^ (1 - θ) *
        volume.real {y : (ℝ ∙ e)ᗮ |
          (y : E) + ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ L} ^ θ)) ≤
      volume ((1 - θ) • K + θ • L) := by
  set zK := ((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile
  set zL := ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile
  set a : ℝ → ℝ := fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + zK τ • e ∈ K}
  set b : ℝ → ℝ := fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + zL τ • e ∈ L}
  set M := (1 - θ) • K + θ • L
  have ha (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : 0 < a τ :=
    hK.volume_real_hyperplaneSection_quantile_pos hKb hK0 he hτ
  have hb (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : 0 < b τ :=
    hL.volume_real_hyperplaneSection_quantile_pos hLb hL0 he hτ
  -- The weighted quantile `z` is strictly increasing with positive derivative `z'`.
  set z : ℝ → ℝ := fun τ ↦ (1 - θ) * zK τ + θ * zL τ
  set z' : ℝ → ℝ := fun τ ↦ (1 - θ) * (volume.real K / a τ) + θ * (volume.real L / b τ)
  have hz' (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : HasDerivAt z (z' τ) τ :=
    ((hK.hasDerivAt_quantile_map_inner_cond hKb hKm hK0 he hτ).const_mul (1 - θ)).add
      ((hL.hasDerivAt_quantile_map_inner_cond hLb hLm hL0 he hτ).const_mul θ)
  have hzpos (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : 0 < z' τ := by
    have hKr : 0 < volume.real K := ENNReal.toReal_pos hK0 hKb.measure_lt_top.ne
    have hLr : 0 < volume.real L := ENNReal.toReal_pos hL0 hLb.measure_lt_top.ne
    exact add_pos (mul_pos (by linarith) (div_pos hKr (ha τ hτ)))
      (mul_pos hθ₀ (div_pos hLr (hb τ hτ)))
  have hzmono : StrictMonoOn z (Ioo 0 1) := by
    intro s hs t ht hst
    have hK' := strictMonoOn_quantile _ (continuous_cdf_map_inner_cond he hK0
      hKb.measure_lt_top.ne) hs ht hst
    have hL' := strictMonoOn_quantile _ (continuous_cdf_map_inner_cond he hL0
      hLb.measure_lt_top.ne) hs ht hst
    simp only [z]
    nlinarith
  -- Pointwise, the integrand is bounded by the change-of-variables integrand along `z`, by
  -- Brunn–Minkowski in the hyperplane.
  have hpt (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : ENNReal.ofReal (z' τ * (a τ ^ (1 - θ) * b τ ^ θ)) ≤
      ENNReal.ofReal |z' τ| * volume {y : (ℝ ∙ e)ᗮ | (y : E) + z τ • e ∈ M} := by
    rw [abs_of_pos (hzpos τ hτ), ENNReal.ofReal_mul (hzpos τ hτ).le,
      ENNReal.ofReal_mul (Real.rpow_nonneg (ha τ hτ).le _),
      ← ENNReal.ofReal_rpow_of_nonneg (ha τ hτ).le (by linarith),
      ← ENNReal.ofReal_rpow_of_nonneg (hb τ hτ).le hθ₀.le, ofReal_measureReal
        (hKb.volume_hyperplaneSection_lt_top e _).ne, ofReal_measureReal
        (hLb.volume_hyperplaneSection_lt_top e _).ne]
    exact mul_le_mul_right
      (volume_hyperplaneSection_rpow_mul_volume_hyperplaneSection_rpow_le e hKm hLm hθ₀ hθ₁ _ _) _
  -- Change variables along `z`, then apply Cavalieri's formula to the convex set `M`.
  refine (setLIntegral_mono' measurableSet_Ioo hpt).trans ?_
  rw [← lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (fun τ hτ ↦ (hz' τ hτ).hasDerivWithinAt) hzmono.injOn
    (fun ζ ↦ volume {y : (ℝ ∙ e)ᗮ | (y : E) + ζ • e ∈ M})]
  refine (setLIntegral_le_lintegral _ _).trans_eq ?_
  rw [← volume_eq_lintegral_volume_hyperplaneSection e he
    (((hK.smul _).add (hL.smul _)).nullMeasurableSet (μ := volume))]

/-- Under equality in multiplicative Brunn–Minkowski, the derivatives of the two height quantiles,
`volume K / volume (K_{z_K τ})` and `volume L / volume (L_{z_L τ})`, agree at every level. -/
private theorem div_volume_real_hyperplaneSection_quantile_eq (hK : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hKm : MeasurableSet K) (hK0 : volume K ≠ 0)
    (hL : Convex ℝ L) (hLb : Bornology.IsBounded L) (hLm : MeasurableSet L)
    (hL0 : volume L ≠ 0) (he : ‖e‖ = 1) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hvol : volume ((1 - θ) • K + θ • L) ≤ volume K ^ (1 - θ) * volume L ^ θ) {τ : ℝ}
    (hτ : τ ∈ Ioo 0 1) :
    volume.real K / volume.real {y : (ℝ ∙ e)ᗮ |
        (y : E) + ((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ K} =
      volume.real L / volume.real {y : (ℝ ∙ e)ᗮ |
        (y : E) + ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ L} := by
  have hint := setLIntegral_ofReal_le_volume_smul_add_smul hK hKb hKm hK0 hL hLb hLm hL0 he
    hθ₀ hθ₁
  set a : ℝ → ℝ := fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ |
    (y : E) + ((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ K}
  set b : ℝ → ℝ := fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ |
    (y : E) + ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ L}
  set c := volume.real K ^ (1 - θ) * volume.real L ^ θ
  set g : ℝ → ℝ := fun τ ↦ ((1 - θ) * (volume.real K / a τ) + θ * (volume.real L / b τ)) *
    (a τ ^ (1 - θ) * b τ ^ θ)
  have ha (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : 0 < a τ :=
    hK.volume_real_hyperplaneSection_quantile_pos hKb hK0 he hτ
  have hb (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : 0 < b τ :=
    hL.volume_real_hyperplaneSection_quantile_pos hLb hL0 he hτ
  -- By weighted AM-GM, `g` is at least the weighted geometric mean `c` of the volumes.
  have hcg (τ : ℝ) (hτ : τ ∈ Ioo 0 1) : c ≤ g τ :=
    Real.geom_mean_le_arith_mean2_weighted_div_mul measureReal_nonneg measureReal_nonneg (ha τ hτ)
      (hb τ hτ) hθ₀.le hθ₁.le
  have hc : 0 ≤ c := mul_nonneg (Real.rpow_nonneg measureReal_nonneg _)
    (Real.rpow_nonneg measureReal_nonneg _)
  have hvol' : volume ((1 - θ) • K + θ • L) ≤ ENNReal.ofReal c := by
    refine hvol.trans_eq ?_
    rw [← ofReal_measureReal hKb.measure_lt_top.ne, ← ofReal_measureReal hLb.measure_lt_top.ne,
      ENNReal.ofReal_rpow_of_nonneg measureReal_nonneg (by linarith),
      ENNReal.ofReal_rpow_of_nonneg measureReal_nonneg hθ₀.le, ← ENNReal.ofReal_mul
        (Real.rpow_nonneg measureReal_nonneg _)]
  have hgc : ContinuousOn g (Ioo 0 1) := by
    have hac := hK.continuousOn_volume_real_hyperplaneSection_quantile hKb hK0 he
    have hbc := hL.continuousOn_volume_real_hyperplaneSection_quantile hLb hL0 he
    refine (((continuousOn_const.div hac fun τ hτ ↦ (ha τ hτ).ne').const_smul (1 - θ)).add
      ((continuousOn_const.div hbc fun τ hτ ↦ (hb τ hτ).ne').const_smul θ)).mul
      ((hac.rpow_const fun τ hτ ↦ Or.inl (ha τ hτ).ne').mul
        (hbc.rpow_const fun τ hτ ↦ Or.inl (hb τ hτ).ne'))
  -- The integral of `g ≥ c` over `Ioo 0 1` is at most `c`, so the continuous `g` equals `c`.
  have hae : g =ᵐ[volume.restrict (Ioo 0 1)] fun _ ↦ c := by
    have hle : ∫⁻ τ in Ioo 0 1, ENNReal.ofReal (g τ) ≤
        ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal c := by
      rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
      exact hint.trans hvol'
    have h := ae_eq_of_ae_le_of_lintegral_le
      ((ae_restrict_iff' measurableSet_Ioo).2 (ae_of_all _ fun τ hτ ↦
        ENNReal.ofReal_le_ofReal (hcg τ hτ)))
      (by simp) (ENNReal.measurable_ofReal.comp_aemeasurable
        (hgc.aemeasurable measurableSet_Ioo)) hle
    filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with τ hτ hτI
    exact ((ENNReal.ofReal_eq_ofReal_iff hc (hc.trans (hcg τ hτI))).1 hτ).symm
  have hgτ : g τ = c := eqOn_open_of_ae_eq hae isOpen_Ioo hgc continuousOn_const hτ
  -- Equality in weighted AM-GM forces the two ratios to agree.
  by_contra hne
  exact (Real.geom_mean_lt_arith_mean2_weighted_div_mul measureReal_nonneg measureReal_nonneg
    (ha τ hτ) (hb τ hτ) hθ₀ hθ₁ hne).ne' hgτ

/-- **Matching height quantiles under Brunn–Minkowski equality.** Let `K` and `L` be bounded Borel
convex sets of positive volume, `0 < θ < 1`, and `e` a unit vector. If the volume of
`(1 - θ) • K + θ • L` is at most `volume K ^ (1 - θ) * volume L ^ θ`, that is, if the multiplicative
Brunn–Minkowski inequality is an equality, then the quantile functions
of the height `⟪e, x⟫` of a point drawn uniformly from `L` and from `K` differ by a constant on
the levels `Ioo 0 1`. -/
theorem _root_.Convex.exists_quantile_map_inner_cond_eq_add_of_volume_le (hK : Convex ℝ K)
    (hKb : Bornology.IsBounded K) (hKm : MeasurableSet K) (hK0 : volume K ≠ 0)
    (hL : Convex ℝ L) (hLb : Bornology.IsBounded L) (hLm : MeasurableSet L)
    (hL0 : volume L ≠ 0) (he : ‖e‖ = 1) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hvol : volume ((1 - θ) • K + θ • L) ≤ volume K ^ (1 - θ) * volume L ^ θ) :
    ∃ c, EqOn ((volume[|L]).map fun x ↦ ⟪e, x⟫).quantile
      (((volume[|K]).map fun x ↦ ⟪e, x⟫).quantile · + c) (Ioo 0 1) := by
  have hKd (τ : ℝ) (hτ : τ ∈ Ioo 0 1) := hK.hasDerivAt_quantile_map_inner_cond hKb hKm hK0 he hτ
  have hLd (τ : ℝ) (hτ : τ ∈ Ioo 0 1) := hL.hasDerivAt_quantile_map_inner_cond hLb hLm hL0 he hτ
  exact isOpen_Ioo.exists_eq_add_of_deriv_eq isPreconnected_Ioo
    (fun τ hτ ↦ (hLd τ hτ).differentiableAt.differentiableWithinAt)
    (fun τ hτ ↦ (hKd τ hτ).differentiableAt.differentiableWithinAt)
    fun τ hτ ↦ by
      rw [(hLd τ hτ).deriv, (hKd τ hτ).deriv]
      exact (div_volume_real_hyperplaneSection_quantile_eq hK hKb hKm hK0 hL hLb hLm hL0 he
        hθ₀ hθ₁ hvol hτ).symm

end TauCeti

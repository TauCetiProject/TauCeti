/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.VariationMeasure
public import TauCeti.Analysis.Sobolev.W1p.ChainRule
public import TauCeti.MeasureTheory.Function.SchwarzRearrangement
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.BoundedVariation.LevelSet
import TauCeti.Analysis.BoundedVariation.SchwarzRearrangement
import TauCeti.Analysis.BoundedVariation.UniformIntegrable
import TauCeti.Analysis.BoundedVariation.WeakDerivative
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.MeasureTheory.Function.Coarea.Measurability
import TauCeti.MeasureTheory.Function.DeLaValleePoussin
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.SchwarzRearrangement.CriticalValues
import TauCeti.MeasureTheory.Integral.ReciprocalWeight

/-!
# The Pólya–Szegő inequality for Lipschitz and `W^{1,1}` functions

Let `E` be a finite-dimensional real inner product space equipped with Lebesgue `volume`. While the
BV Pólya–Szegő inequality (`TauCeti.totalVariationOn_toReal_schwarzRearrangement_le`) shows that
symmetric decreasing rearrangement does not increase total variation, BV membership alone allows a
Cantor-type singular derivative measure. Exclusion of singular concentration in `W^{1,1}` requires
preserving uniform integrability of gradients across smooth approximations.

This file proves two main results:

1. **Convex-integrand Pólya–Szegő for Lipschitz functions**
   (`LipschitzWith.lintegral_ofReal_map_norm_fderiv_toReal_schwarzRearrangement_le` and
   `LipschitzWith.integral_map_norm_fderiv_toReal_schwarzRearrangement_le`). For every `K`-Lipschitz
   `h : E → ℝ` and every `Φ : ℝ → ℝ` convex on `[0, ∞)` with `Φ 0 ≤ 0`, the real Schwarz
   rearrangement `h*` of the positive part of `h` satisfies
   `∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h* x‖) ≤ ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖)`.
   By the scalar coarea formula on `{Dh ≠ 0}`, both integrals decompose over positive levels `t > 0`
   into `∫_{{w = t} ∩ {Dw ≠ 0}} Φ(‖Dw‖) / ‖Dw‖ dH^{n-1}`. At almost every level `t > 0`:
   * `t` is not a critical value of `h*`, so `‖Dh*‖` is constant and nonzero along `{h* = t}` by
     `TauCeti.norm_eq_of_eq_of_forall_fderiv_ne_zero` and `TauCeti.norm_fderiv_eq_of_norm_eq`;
   * the codimension-one Hausdorff measures of `{h* = t}` and `{h = t}` agree with their superlevel
     perimeters (`LipschitzWith.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage`), which
     satisfy `P({h* > t}) ≤ P({h > t})` by the sharp Euclidean isoperimetric inequality;
   * the reciprocal-gradient level integrals satisfy `m_{h*}(t) = -μ_h'(t) ≥ m_h(t)` by
     the reciprocal-weight coarea identities in
     `TauCeti.MeasureTheory.Function.SchwarzRearrangement.CriticalValues` and
     `TauCeti.MeasureTheory.Function.Coarea.DistributionFunction`;
   * reciprocal-weighted Jensen and perspective monotonicity
     (`ConvexOn.mul_map_div_le_integral_div`) compare the two level integrals.
   Truncating `Φ` at zero, replacing `h` by `max h 0`, and subtracting the infimum of levels of
   finite superlevel measure eliminate monotonicity, sign, and decay hypotheses from the extended
   Lebesgue inequality.

2. **`W^{1,1}` Pólya–Szegő** (`TauCeti.W1p.schwarzRearrangement` and
   `TauCeti.W1p.schwarzRearrangementNorm`). For `u : W1p volume ⊤ 1`, mollifying `(W1p.value u)⁺` by
   shrinking normalized smooth bumps `ρ_j` produces globally Lipschitz functions `u_j` whose
   gradients satisfy `∫ Φ(‖Du_j‖) ≤ ∫ Φ(‖∇u⁺‖)` by convolution Jensen, hence
   `∫ Φ(‖D(u_j*)‖) ≤ ∫ Φ(‖∇u⁺‖)` by the Lipschitz inequality. Choosing `Φ` superlinear via de la
   Vallée Poussin (`MeasureTheory.Integrable.exists_convexOn_superlinear_integrable`) yields uniform
   equi-integrability of `D(u_j*)`, while `Φ = id` bounds their `L¹` norms by `‖∇u⁺‖_{L¹}`. Since
   `u_j* → u*` in `L¹` by `L¹`-contraction of Schwarz rearrangement,
   `MeasureTheory.LocallyIntegrableOn.exists_hasWeakFDerivOn_integrableOn_of_uniformIntegrable`
   shows that `|D(u*)| ≪ volume` and equips `u*` (and similarly `|u|*`) with an `L¹` weak gradient
   satisfying `‖∇(u*)‖_{L¹} ≤ ‖∇u‖_{L¹}`.

## Main declarations

* `LipschitzWith.lintegral_ofReal_map_norm_fderiv_toReal_schwarzRearrangement_le`: extended
  convex-integrand Pólya–Szegő inequality for arbitrary Lipschitz functions.
* `LipschitzWith.integrable_map_norm_fderiv_toReal_schwarzRearrangement` and
  `LipschitzWith.integral_map_norm_fderiv_toReal_schwarzRearrangement_le`: Bochner integrability and
  integral comparison for convex nondecreasing `Φ` with `Φ 0 = 0`.
* `TauCeti.W1p.exists_setLIntegral_enorm_fderiv_toReal_schwarzRearrangement_convolution_le`:
  quantitative equi-integrability `∫_s ‖D((ρ_i ⋆ u)*)‖ₑ ≤ T * volume s + ε` across bump families.
* `TauCeti.W1p.schwarzRearrangement` and `TauCeti.W1p.schwarzRearrangementNorm`: positive-part and
  absolute-value Schwarz rearrangements on `W1p volume ⊤ 1`, together with their value and gradient
  `L¹` norm bounds and variation-measure absolute continuity.

## References

* G. Bianchi, R. J. Gardner, P. Gronchi, M. Kiderlen, *The Pólya–Szegő inequality for smoothing
  rearrangements*, J. Funct. Anal. **287** (2024), Theorem 5.8.
* J. Brothers, W. P. Ziemer, *Minimal rearrangements of Sobolev functions*, J. Reine Angew. Math.
  **384** (1988), 153–179.
* E. H. Lieb, M. Loss, *Analysis*, 2nd ed., AMS, 2001, Theorem 7.17 and Lemma 7.17.
-/

public noncomputable section

open MeasureTheory Set Filter TopologicalSpace Metric Module ContinuousLinearMap
open scoped ENNReal NNReal Topology Convolution Distributions RealInnerProductSpace

/-! ### Convex-integrand Pólya–Szegő inequality for Lipschitz functions -/

namespace LipschitzWith

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Truncating `h - c` at zero does not increase the gradient norm of a continuous function. -/
private theorem norm_fderiv_max_sub_zero_le {h : E → ℝ} (hh : Continuous h) (c : ℝ) (x : E) :
    ‖fderiv ℝ (fun y ↦ max (h y - c) 0) x‖ ≤ ‖fderiv ℝ h x‖ := by
  rcases le_or_gt (h x) c with hxc | hcx
  · have hmin : IsLocalMin (fun y ↦ max (h y - c) 0) x := by
      refine Eventually.of_forall fun y ↦ ?_
      dsimp only
      rw [max_eq_right (sub_nonpos.2 hxc)]
      exact le_max_right _ _
    simp [hmin.fderiv_eq_zero]
  · have hev : (fun y ↦ max (h y - c) 0) =ᶠ[𝓝 x] fun y ↦ h y - c := by
      filter_upwards [hh.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hcx)] with y (hy : c < h y)
      exact max_eq_left (sub_pos.2 hy).le
    rw [hev.fderiv_eq, fderiv_sub_const]

/-- If `Φ` is convex on `[0, ∞)` with `Φ 0 ≤ 0`, then `s ↦ max (Φ s) 0` is nondecreasing on
`[0, ∞)`. -/
private theorem monotoneOn_max_zero_of_convexOn {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ)
    (hΦ0 : Φ 0 ≤ 0) : MonotoneOn (fun s ↦ max (Φ s) 0) (Ici 0) := by
  intro a (ha : 0 ≤ a) b (hb : 0 ≤ b) hab
  refine max_le ?_ (le_max_right _ _)
  rcases eq_or_lt_of_le hb with rfl | hb_pos
  · rw [le_antisymm hab ha]
    exact hΦ0.trans (le_max_right _ _)
  · have hcomb : (1 - a / b) • (0 : ℝ) + (a / b) • b = a := by
      simp [div_mul_cancel₀ _ hb_pos.ne']
    have hconv := hΦ.2 (mem_Ici.2 le_rfl) hb (sub_nonneg.2 (div_le_one_of_le₀ hab hb))
      (div_nonneg ha hb) (sub_add_cancel 1 (a / b))
    rw [hcomb] at hconv
    simp only [smul_eq_mul] at hconv
    have h1 : (1 - a / b) * Φ 0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (div_le_one_of_le₀ hab hb)) hΦ0
    have h2 : (a / b) * Φ b ≤ max (Φ b) 0 := calc
      (a / b) * Φ b ≤ (a / b) * max (Φ b) 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (div_nonneg ha hb)
      _ ≤ 1 * max (Φ b) 0 :=
        mul_le_mul_of_nonneg_right (div_le_one_of_le₀ hab hb) (le_max_right _ _)
      _ = max (Φ b) 0 := one_mul _
    linarith [hconv, h1, h2]

variable [MeasurableSpace E] [BorelSpace E]

/-- Measurability of `x ↦ Φ ‖fderiv ℝ w x‖` when `Φ` is monotone on `[0, ∞)`. -/
private theorem measurable_map_norm_fderiv (w : E → ℝ) {Φ : ℝ → ℝ} (hΦm : MonotoneOn Φ (Ici 0)) :
    Measurable fun x : E ↦ Φ ‖fderiv ℝ w x‖ := by
  have hm : Monotone fun s : ℝ ↦ Φ (max s 0) := fun a b hab ↦
    hΦm (le_max_right _ _) (le_max_right _ _) (max_le_max_right 0 hab)
  have heq : (fun x : E ↦ Φ ‖fderiv ℝ w x‖) = fun x ↦ Φ (max ‖fderiv ℝ w x‖ 0) :=
    funext fun x ↦ by rw [max_eq_left (norm_nonneg _)]
  rw [heq]
  exact hm.measurable.comp (measurable_fderiv ℝ w).norm

/-- Extended-real wrapper around `ConvexOn.mul_map_div_le_integral_div` on the regular level surface
`{x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}`. -/
private theorem ofReal_mul_map_div_le_setLIntegral_fiber {h : E → ℝ}
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    {t P M : ℝ} (hP : 0 ≤ P) (hM0 : 0 ≤ M)
    (hPv : ENNReal.ofReal P ≤ μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}))
    (hPh_fin : μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) < ∞)
    (hmh : ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹
      ∂μHE[finrank ℝ E - 1] ≤ ENNReal.ofReal M)
    (hΦh_fin : ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
      ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ∂μHE[finrank ℝ E - 1] < ∞) :
    ENNReal.ofReal (M * Φ (P / M)) ≤
      ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ∂μHE[finrank ℝ E - 1] := by
  have hSm : MeasurableSet ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) := by
    rw [inter_comm]
    exact TauCeti.measurableSet_preimage_inter_setOf_fderiv_ne_zero (measurableSet_singleton t)
  set S := {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}
  set ν := μHE[finrank ℝ E - 1].restrict S
  have : IsFiniteMeasure ν := ⟨by rw [Measure.restrict_apply_univ]; exact hPh_fin⟩
  have hg : ∀ᵐ x ∂ν, 0 < ‖fderiv ℝ h x‖ :=
    (ae_restrict_mem hSm).mono fun x hx ↦ norm_pos_iff.2 hx.1
  have hinv_eq : ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ h x‖⁻¹ ∂ν = ∫⁻ x, ‖fderiv ℝ h x‖ₑ⁻¹ ∂ν :=
    lintegral_congr_ae (hg.mono fun x hpos ↦ by
      dsimp only
      rw [← ofReal_norm, ENNReal.ofReal_inv_of_pos hpos])
  have hi : Integrable (fun x ↦ ‖fderiv ℝ h x‖⁻¹) ν :=
    (lintegral_ofReal_ne_top_iff_integrable (measurable_fderiv ℝ h).norm.inv.aestronglyMeasurable
      (ae_of_all _ fun x ↦ inv_nonneg.2 (norm_nonneg _))).1
      (hinv_eq.symm ▸ (hmh.trans_lt ENNReal.ofReal_lt_top).ne)
  have hΦ_nonneg (x : E) : 0 ≤ Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖ :=
    div_nonneg (hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hΦi : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ν :=
    (lintegral_ofReal_ne_top_iff_integrable
      ((measurable_map_norm_fderiv h hΦm).div (measurable_fderiv ℝ h).norm).aestronglyMeasurable
      (ae_of_all _ hΦ_nonneg)).1 hΦh_fin.ne
  have hPν : P ≤ ν.real univ := by
    rw [measureReal_def, Measure.restrict_apply_univ, ← ENNReal.toReal_ofReal hP]
    exact ENNReal.toReal_mono hPh_fin.ne hPv
  have hM_int : ∫ x, ‖fderiv ℝ h x‖⁻¹ ∂ν ≤ M := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ inv_nonneg.2 (norm_nonneg _))
      hi.aestronglyMeasurable, hinv_eq, ← ENNReal.toReal_ofReal hM0]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hmh
  rw [← ofReal_integral_eq_lintegral_ofReal hΦi (ae_of_all _ hΦ_nonneg)]
  exact ENNReal.ofReal_le_ofReal
    (hΦ.mul_map_div_le_integral_div hΦm hΦ0 hg hi hΦi hP hPν hM_int)

end NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Single-level comparison between a radially nonincreasing map `v` at a regular level `t` and a
map `h` whose regular level surface has at least the Hausdorff measure of `v ⁻¹' {t}` and no smaller
reciprocal-gradient bound `μ'`. -/
private theorem fiber_le_of_level_bounds {v h : E → ℝ} (hvm : Measurable v)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    {t μ' : ℝ} (hrad : ∀ z w : E, ‖z‖ ≤ ‖w‖ → v w ≤ v z)
    (hreg : ∀ z : E, v z = t → fderiv ℝ v z ≠ 0)
    (hPv : μHE[finrank ℝ E - 1] (v ⁻¹' {t}) ≤
      μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}))
    (hPh_fin : μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) < ∞)
    (hmv : ∫⁻ x in {x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t}, ‖fderiv ℝ v x‖ₑ⁻¹
      ∂μHE[finrank ℝ E - 1] = ENNReal.ofReal μ')
    (hmh : ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹
      ∂μHE[finrank ℝ E - 1] ≤ ENNReal.ofReal μ')
    (hΦh_fin : ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
      ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ∂μHE[finrank ℝ E - 1] < ∞) :
    ∫⁻ x in {x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ v x‖ / ‖fderiv ℝ v x‖) ∂μHE[finrank ℝ E - 1] ≤
      ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ∂μHE[finrank ℝ E - 1] := by
  have hv_inter : {x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t} = v ⁻¹' {t} :=
    inter_eq_right.mpr fun x hx ↦ hreg x hx
  rw [hv_inter] at hmv ⊢
  rcases eq_or_ne (μHE[finrank ℝ E - 1] (v ⁻¹' {t})) 0 with hPv0 | hPv0
  · simp [Measure.restrict_eq_zero.2 hPv0]
  obtain ⟨x₀, hx₀ : v x₀ = t⟩ := nonempty_of_measure_ne_zero hPv0
  have hPv_fin : μHE[finrank ℝ E - 1] (v ⁻¹' {t}) < ∞ := hPv.trans_lt hPh_fin
  have hvt_m : MeasurableSet (v ⁻¹' {t}) := hvm (measurableSet_singleton t)
  have hcst (x : E) (hx : x ∈ v ⁻¹' {t}) : ‖fderiv ℝ v x‖ = ‖fderiv ℝ v x₀‖ :=
    TauCeti.norm_fderiv_eq_of_norm_eq
      (fun z w hzw ↦ le_antisymm (hrad w z hzw.symm.le) (hrad z w hzw.le))
      (TauCeti.norm_eq_of_eq_of_forall_fderiv_ne_zero hrad
        (fun z hz ↦ hreg z (hz.trans hx₀)) (hx₀.trans hx.symm)).symm
  set γ := ‖fderiv ℝ v x₀‖
  have hγ : 0 < γ := norm_pos_iff.2 (hreg x₀ hx₀)
  set P := μHE[finrank ℝ E - 1].real (v ⁻¹' {t})
  have hP : 0 < P := ENNReal.toReal_pos hPv0 hPv_fin.ne
  set M := max μ' 0
  have hM_eq : ENNReal.ofReal M = ENNReal.ofReal μ' := by simp [M]
  have hmv_eval : ENNReal.ofReal γ⁻¹ * μHE[finrank ℝ E - 1] (v ⁻¹' {t}) = ENNReal.ofReal M := by
    rw [hM_eq, ← hmv, ← setLIntegral_const]
    refine setLIntegral_congr_fun hvt_m fun x hx ↦ ?_
    rw [← ofReal_norm, hcst x hx, ENNReal.ofReal_inv_of_pos hγ]
  have hM_val : M = γ⁻¹ * P := by
    have htr := congrArg ENNReal.toReal hmv_eval
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 hγ.le),
      ENNReal.toReal_ofReal (le_max_right _ _), eq_comm] at htr
  have hPM : P / M = γ := by rw [hM_val]; field_simp
  have hP_ofReal : ENNReal.ofReal P = μHE[finrank ℝ E - 1] (v ⁻¹' {t}) := by
    dsimp only [P]
    rw [measureReal_def, ENNReal.ofReal_toReal hPv_fin.ne]
  have hlhs_eval : ∫⁻ x in v ⁻¹' {t}, ENNReal.ofReal (Φ ‖fderiv ℝ v x‖ / ‖fderiv ℝ v x‖)
        ∂μHE[finrank ℝ E - 1] = ENNReal.ofReal (M * Φ (P / M)) := by
    have hΦγ : 0 ≤ Φ γ / γ := div_nonneg (hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) hγ.le hγ.le) hγ.le
    calc ∫⁻ x in v ⁻¹' {t}, ENNReal.ofReal (Φ ‖fderiv ℝ v x‖ / ‖fderiv ℝ v x‖)
            ∂μHE[finrank ℝ E - 1]
        = ENNReal.ofReal (Φ γ / γ) * ENNReal.ofReal P := by
          rw [setLIntegral_congr_fun hvt_m fun x hx ↦ by rw [hcst x hx],
            setLIntegral_const, hP_ofReal]
      _ = ENNReal.ofReal (M * Φ (P / M)) := by
          rw [← ENNReal.ofReal_mul hΦγ, hPM, hM_val]
          congr 1
          ring
  rw [hlhs_eval]
  exact ofReal_mul_map_div_le_setLIntegral_fiber hΦ hΦm hΦ0 hP.le (le_max_right _ _)
    (hP_ofReal.trans_le hPv) hPh_fin (hM_eq ▸ hmh) hΦh_fin

variable [FiniteDimensional ℝ E]

/-- For a nonnegative function `w : E → ℝ` and `Φ : ℝ → ℝ` monotone on `[0, ∞)` with `Φ 0 = 0`, the
gradient integral `∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ w x‖)` equals the coarea level integral over
`t > 0` of `Φ ‖fderiv ℝ w‖ / ‖fderiv ℝ w‖` on `{fderiv ℝ w ≠ 0} ∩ w ⁻¹' {t}`. -/
private theorem lintegral_ofReal_fderiv_eq_coarea {w : E → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    {Φ : ℝ → ℝ} (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ w x‖) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x in {x | fderiv ℝ w x ≠ 0} ∩ w ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ w x‖ / ‖fderiv ℝ w x‖) ∂μHE[finrank ℝ E - 1] := by
  set R := {x | fderiv ℝ w x ≠ 0}
  have hRm : MeasurableSet R := (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ w)
  have hqm : Measurable fun x : E ↦ ENNReal.ofReal (Φ ‖fderiv ℝ w x‖ / ‖fderiv ℝ w x‖) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_map_norm_fderiv w hΦm).div (measurable_fderiv ℝ w).norm)
  have hsurj (x : E) (hx : x ∈ R) : Function.Surjective (fderiv ℝ w x) :=
    surjective_of_ne_zero_of_finrank_eq_one (finrank_self ℝ)
      ((ContinuousLinearMap.coe_injective.ne_iff' ContinuousLinearMap.toLinearMap_zero).2 hx)
  have hR_eq : ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ w x‖) =
      ∫⁻ x in R, ENNReal.ofReal (Φ ‖fderiv ℝ w x‖) := by
    rw [← lintegral_add_compl _ hRm]
    have hc0 : ∫⁻ x in Rᶜ, ENNReal.ofReal (Φ ‖fderiv ℝ w x‖) = 0 := by
      refine (setLIntegral_congr_fun hRm.compl fun x hx ↦ ?_).trans lintegral_zero
      have h0 : fderiv ℝ w x = 0 := by simpa [R] using hx
      simp [h0, hΦ0]
    rw [hc0, add_zero]
  have hco := MeasureTheory.lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
    hRm.nullMeasurableSet (fun _ hx ↦ TauCeti.differentiableAt_of_fderiv_ne_zero hx) hsurj hqm
  rw [finrank_self] at hco
  have hlhs : ∫⁻ x in R, ENNReal.ofReal (fderiv ℝ w x).adjoint.normDet *
        ENNReal.ofReal (Φ ‖fderiv ℝ w x‖ / ‖fderiv ℝ w x‖) =
      ∫⁻ x in R, ENNReal.ofReal (Φ ‖fderiv ℝ w x‖) := by
    refine setLIntegral_congr_fun hRm fun x hx ↦ ?_
    rw [ContinuousLinearMap.normDet_adjoint_eq_norm, ← ENNReal.ofReal_mul (norm_nonneg _),
      mul_div_cancel₀ _ (norm_ne_zero_iff.2 hx)]
  rw [hR_eq, ← hlhs, hco, ← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun t ↦ ?_
  by_cases ht : 0 < t
  · exact (indicator_of_mem (mem_Ioi.2 ht) (fun s ↦
      ∫⁻ x in R ∩ w ⁻¹' {s}, ENNReal.ofReal (Φ ‖fderiv ℝ w x‖ / ‖fderiv ℝ w x‖)
        ∂μHE[finrank ℝ E - 1])).symm
  · rw [indicator_of_notMem (mem_Ioi.not.2 ht)]
    have hempty : R ∩ w ⁻¹' {t} = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      rintro ⟨hxR, hwx⟩
      have hwx0 : w x = 0 := le_antisymm (hwx.trans_le (not_lt.1 ht)) (hw0 x)
      have hmin : IsLocalMin w x := Eventually.of_forall fun y ↦ hwx0.symm ▸ hw0 y
      exact hxR hmin.fderiv_eq_zero
    simp [hempty]

/-- Pointwise finiteness of the extended Schwarz rearrangement of `ENNReal.ofReal ∘ h` when `h` is
Lipschitz and its positive superlevel sets have finite volume. -/
private theorem schwarzRearrangement_ofReal_ne_top_of_lipschitzWith [Nontrivial E] {K : ℝ≥0}
    {h : E → ℝ} (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) (x : E) :
    TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x ≠ ∞ := by
  refine TauCeti.schwarzRearrangement_ne_top volume (K := K) (fun a b ↦ ?_)
    (t := ENNReal.ofReal 1) ENNReal.ofReal_ne_top ?_ x
  · calc ENNReal.ofReal (h a) ≤ ENNReal.ofReal (h b + K * dist a b) :=
          ENNReal.ofReal_le_ofReal (hh.le_add_mul a b)
      _ ≤ ENNReal.ofReal (h b) + K * edist a b := by
        rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
        exact ENNReal.ofReal_add_le
  · convert hfin 1 one_pos using 2
    ext y
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_one

/-- Almost-every-level finiteness and critical-value exclusion needed in the Lipschitz Pólya–Szegő
coarea comparison. -/
private theorem ae_level_conditions_of_lipschitzWith {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) {Φ : ℝ → ℝ} (hΦm : MonotoneOn Φ (Ici 0))
    (hInt : ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
      ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ∂μHE[finrank ℝ E - 1] ≠ ∞) :
    ∀ᵐ t : ℝ, 0 < t →
      ∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ∂μHE[finrank ℝ E - 1] < ∞ ∧
      μHE[finrank ℝ E - 1] (h ⁻¹' {t}) < ∞ ∧
      μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x = 0} ∩ h ⁻¹' {t}) = 0 ∧
      ∀ z : E, (TauCeti.schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) z).toReal = t →
        fderiv ℝ (fun w ↦ (TauCeti.schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) w).toReal) z ≠ 0 := by
  have hRh : MeasurableSet {x | fderiv ℝ h x ≠ 0} :=
    (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ h)
  have hm := MeasureTheory.aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt (F := ℝ) volume
    hRh.nullMeasurableSet
    (fun x hx ↦ (TauCeti.differentiableAt_of_fderiv_ne_zero hx).hasFDerivAt.hasFDerivWithinAt)
    (ENNReal.measurable_ofReal.comp
      ((measurable_map_norm_fderiv h hΦm).div (measurable_fderiv ℝ h).norm))
  rw [finrank_self] at hm
  have hae_Φfin := (ae_restrict_iff' measurableSet_Ioi).1 (ae_lt_top' hm.restrict hInt)
  have hae_Hfin : ∀ᵐ t : ℝ, 0 < t → μHE[finrank ℝ E - 1] (h ⁻¹' {t}) < ∞ := by
    have hk (k : ℕ) : ∀ᵐ t : ℝ,
        μHE[finrank ℝ E - 1] ({x | 1 / ((k : ℝ) + 1) < h x} ∩ h ⁻¹' {t}) < ∞ := by
      have hSk : NullMeasurableSet {x | 1 / ((k : ℝ) + 1) < h x} :=
        (isOpen_lt continuous_const hh.continuous).measurableSet.nullMeasurableSet
      simpa [finrank_self] using
        hh.ae_euclideanHausdorffMeasure_inter_preimage_lt_top_of_integrableOn hSk
          (hh.integrableOn_normDet_adjoint_fderiv (hfin _ (Nat.one_div_pos_of_nat (n := k))))
    filter_upwards [ae_all_iff.2 hk] with t ht htpos
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt htpos
    have heq : {x | 1 / ((k : ℝ) + 1) < h x} ∩ h ⁻¹' {t} = h ⁻¹' {t} :=
      inter_eq_right.mpr fun x (hx : h x = t) ↦ by change 1 / ((k : ℝ) + 1) < h x; rwa [hx]
    rw [← heq]
    exact ht k
  have hae_crit_h : ∀ᵐ t : ℝ, μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x = 0} ∩ h ⁻¹' {t}) = 0 := by
    simpa [finrank_self, ContinuousLinearMap.normDet_adjoint_eq_norm] using
      hh.ae_euclideanHausdorffMeasure_setOf_normDet_adjoint_fderiv_eq_zero_inter_preimage_eq_zero
  have hae_reg_v : ∀ᵐ t : ℝ, ∀ z : E,
      (TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal = t →
        fderiv ℝ (fun w ↦ (TauCeti.schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) w).toReal) z ≠ 0 := by
    rw [eventually_iff, mem_ae_iff]
    refine measure_mono_null (fun t ht ↦ ?_)
      (hh.volume_image_setOf_fderiv_toReal_schwarzRearrangement_eq_zero volume)
    rw [mem_compl_iff, mem_ofPred_eq] at ht
    push Not at ht
    obtain ⟨z, hzt, hfz⟩ := ht
    exact ⟨z, hfz, hzt⟩
  filter_upwards [hae_Φfin, hae_Hfin, hae_crit_h, hae_reg_v] with t h1 h2 h3 h4 htpos
  exact ⟨h1 htpos, h2 htpos, h3, h4⟩

/-- Core Lipschitz Pólya–Szegő inequality on a nontrivial space for nonnegative `h` whose positive
superlevel sets have finite volume, and `Φ` convex and monotone on `[0, ∞)` with `Φ 0 = 0`. -/
private theorem lintegral_ofReal_map_norm_fderiv_le_core [Nontrivial E] {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h) (h0 : ∀ x, 0 ≤ h x) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦
        (TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) := by
  rcases eq_or_ne (∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖)) ∞ with htop | hInt_ne
  · exact htop ▸ le_top
  have hv : LipschitzWith K (fun z ↦
      (TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) :=
    TauCeti.lipschitzWith_toReal_schwarzRearrangement volume hh
  have hne := schwarzRearrangement_ofReal_ne_top_of_lipschitzWith hh hfin
  rw [lintegral_ofReal_fderiv_eq_coarea h0 hΦm hΦ0] at hInt_ne
  rw [lintegral_ofReal_fderiv_eq_coarea (fun _ ↦ ENNReal.toReal_nonneg) hΦm hΦ0,
    lintegral_ofReal_fderiv_eq_coarea h0 hΦm hΦ0]
  have hRh : MeasurableSet {x | fderiv ℝ h x ≠ 0} :=
    (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ h)
  refine setLIntegral_mono_ae' measurableSet_Ioi ?_
  filter_upwards [ae_level_conditions_of_lipschitzWith hh hfin hΦm hInt_ne,
    hh.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage,
    hv.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage,
    hh.ae_setLIntegral_inv_enorm_fderiv_toReal_schwarzRearrangement_eq_ofReal_neg_deriv hfin,
    MeasureTheory.ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv hfin]
    with t hlev hperh hperv hmv hmh (htpos : 0 < t)
  obtain ⟨hΦt, hHt, hcrith, hregv⟩ := hlev htpos
  have hRh_eq : μHE[finrank ℝ E - 1] (h ⁻¹' {t}) =
      μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) := by
    rw [← measure_inter_add_sdiff (h ⁻¹' {t}) hRh, inter_comm (h ⁻¹' {t})]
    have hdiff : h ⁻¹' {t} \ {x | fderiv ℝ h x ≠ 0} = {x | fderiv ℝ h x = 0} ∩ h ⁻¹' {t} := by
      ext x; simp [and_comm]
    rw [hdiff, hcrith, add_zero]
  have hPv_le : μHE[finrank ℝ E - 1] ((fun z ↦ (TauCeti.schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (h y)) z).toReal) ⁻¹' {t}) ≤
      μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) := by
    rw [← hRh_eq, ← hperv, ← hperh]
    have hvset : {x | t < (TauCeti.schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) x).toReal} =
        {x | ENNReal.ofReal t < TauCeti.schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) x} := by
      ext x; exact (ENNReal.ofReal_lt_iff_lt_toReal htpos.le (hne x)).symm
    have hhset : {x | t < h x} = {x | ENNReal.ofReal t < ENNReal.ofReal (h x)} := by
      ext x; exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg htpos.le).symm
    have hnm : NullMeasurableSet {x | ENNReal.ofReal t < ENNReal.ofReal (h x)} := by
      rw [← hhset]
      exact (isOpen_lt continuous_const hh.continuous).measurableSet.nullMeasurableSet
    rw [hvset, hhset]
    exact hnm.perimeter_setOf_lt_schwarzRearrangement_le
  exact fiber_le_of_level_bounds hv.continuous.measurable hΦ hΦm hΦ0
    (fun z w hzw ↦ ENNReal.toReal_mono (hne z)
      (TauCeti.schwarzRearrangement_le_of_norm_le volume _ hzw))
    hregv hPv_le (hRh_eq ▸ hHt) (hmv htpos) (hmh htpos) hΦt

/-- For `S = {s ≥ 0 | volume {h > s} ≠ ∞}` and `c = sInf S`, shifting `h` at `c` commutes with
extended Schwarz rearrangement up to `+ ENNReal.ofReal c`. -/
private theorem schwarzRearrangement_ofReal_eq_add_sInf [Nontrivial E] (h : E → ℝ) (x : E) :
    TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x =
      TauCeti.schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (max (h y - sInf {s : ℝ | 0 ≤ s ∧ volume {x | s < h x} ≠ ∞}) 0))
        x + ENNReal.ofReal (sInf {s : ℝ | 0 ≤ s ∧ volume {x | s < h x} ≠ ∞}) := by
  set S : Set ℝ := {s : ℝ | 0 ≤ s ∧ volume {x | s < h x} ≠ ∞}
  set c := sInf S
  have hSbdd : BddBelow S := ⟨0, fun _ hs ↦ hs.1⟩
  have hc0 : 0 ≤ c := Real.sInf_nonneg fun _ hs ↦ hs.1
  rw [← congrFun (TauCeti.schwarzRearrangement_add_const volume _ _) x]
  refine eq_of_forall_lt_iff fun t ↦ ?_
  rw [TauCeti.lt_schwarzRearrangement_iff, TauCeti.lt_schwarzRearrangement_iff]
  rcases lt_or_ge t (ENNReal.ofReal c) with htc | hct
  · have ht_fin : t ≠ ∞ := (lt_trans htc ENNReal.ofReal_lt_top).ne
    have htr_not : t.toReal ∉ S := notMem_of_lt_csInf (ENNReal.toReal_lt_of_lt_ofReal htc) hSbdd
    have hvol : volume {y | t < ENNReal.ofReal (h y)} = ∞ := by
      have hvol' : volume {y | t.toReal < h y} = ∞ := by
        by_contra hne
        exact htr_not ⟨ENNReal.toReal_nonneg, hne⟩
      convert hvol' using 2
      ext y
      conv_lhs => rw [← ENNReal.ofReal_toReal ht_fin]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg
    have huniv : {y | t < ENNReal.ofReal (max (h y - c) 0) + ENNReal.ofReal c} = univ :=
      eq_univ_of_forall fun _ ↦ htc.trans_le le_add_self
    rw [hvol, huniv, measure_univ_of_isAddLeftInvariant]
  · rcases eq_or_ne t ∞ with rfl | ht_fin
    · simp
    · suffices {y | t < ENNReal.ofReal (h y)} =
          {y | t < ENNReal.ofReal (max (h y - c) 0) + ENNReal.ofReal c} by rw [this]
      ext y
      simp only [mem_ofPred_eq]
      rw [← ENNReal.ofReal_add (le_max_right _ _) hc0, ← ENNReal.ofReal_toReal ht_fin]
      have hcs : c ≤ t.toReal := (ENNReal.ofReal_le_iff_le_toReal ht_fin).1 hct
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg]
      grind

/-- Removing the finite-superlevel-measure hypothesis `hfin` by shifting `h` at the infimum `c` of
levels with finite superlevel volume (or noting `h* = 0` when all superlevel volumes are `∞`). -/
private theorem lintegral_ofReal_map_norm_fderiv_le_of_nonneg [Nontrivial E] {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦
        (TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) := by
  let S : Set ℝ := {s : ℝ | 0 ≤ s ∧ volume {x | s < h x} ≠ ∞}
  rcases S.eq_empty_or_nonempty with hSempty | hSne
  · have htop_all (x : E) :
        TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x = ∞ := by
      by_contra hne
      have hlt : TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x <
          TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x := by
        rw [TauCeti.lt_schwarzRearrangement_iff]
        set r := (TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x).toReal
        have hvol' : volume {y | r < h y} = ∞ := by
          by_contra hfin
          exact (hSempty ▸ notMem_empty r) ⟨ENNReal.toReal_nonneg, hfin⟩
        have hset : {y | TauCeti.schwarzRearrangement volume (fun z ↦ ENNReal.ofReal (h z)) x <
            ENNReal.ofReal (h y)} = {y | r < h y} := by
          ext y
          conv_lhs => rw [← ENNReal.ofReal_toReal hne]
          exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg
        rw [hset, hvol']
        exact measure_ball_lt_top
      exact lt_irrefl _ hlt
    simp [htop_all, hΦ0]
  · set c := sInf S
    have hSbdd : BddBelow S := ⟨0, fun _ hs ↦ hs.1⟩
    have hc0 : 0 ≤ c := Real.sInf_nonneg fun _ hs ↦ hs.1
    let hc_fun : E → ℝ := fun x ↦ max (h x - c) 0
    have hhc_lip : LipschitzWith K hc_fun :=
      (LipschitzWith.of_dist_le_mul fun x y ↦ by
        simpa [dist_sub_right] using hh.dist_le_mul x y).max_const 0
    have hhc_fin (t : ℝ) (ht : 0 < t) : volume {x | t < hc_fun x} ≠ ∞ := by
      obtain ⟨s, hsS, hsc⟩ := (csInf_lt_iff hSbdd hSne).1 (lt_add_of_pos_right c ht)
      refine ne_top_of_le_ne_top hsS.2 (measure_mono fun x (hx : t < max (h x - c) 0) ↦ ?_)
      rcases lt_max_iff.1 hx with hx | hx
      · change s < h x; linarith
      · exact (not_lt_of_gt ht hx).elim
    have hhc_ne := schwarzRearrangement_ofReal_ne_top_of_lipschitzWith hhc_lip hhc_fin
    have hval_eq : (fun z ↦ (TauCeti.schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (h y)) z).toReal) =
        fun z ↦ (TauCeti.schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (hc_fun y)) z).toReal + c := by
      ext z
      rw [schwarzRearrangement_ofReal_eq_add_sInf h z,
        ENNReal.toReal_add (hhc_ne z) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hc0]
    simp_rw [hval_eq, fderiv_add_const]
    exact (lintegral_ofReal_map_norm_fderiv_le_core hhc_lip (fun _ ↦ le_max_right _ _)
      hhc_fin hΦ hΦm hΦ0).trans (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal
      (hΦm (norm_nonneg _) (norm_nonneg _) (norm_fderiv_max_sub_zero_le hh.continuous c x)))

/-- **Convex-integrand Pólya–Szegő inequality for Lipschitz functions.** For any `K`-Lipschitz
function `h : E → ℝ` and any `Φ : ℝ → ℝ` convex on `[0, ∞)` with `Φ 0 ≤ 0`, the real Schwarz
rearrangement of the positive part of `h` satisfies
`∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h* x‖) ≤ ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖)`. -/
theorem lintegral_ofReal_map_norm_fderiv_toReal_schwarzRearrangement_le
    {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦ0 : Φ 0 ≤ 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦
        (TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) := by
  by_cases hE : Nontrivial E
  swap
  · have hsub : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    refine le_of_eq (lintegral_congr fun x ↦ ?_)
    rw [@Subsingleton.elim (E →L[ℝ] ℝ) (by infer_instance) (fderiv ℝ _ x) 0,
      @Subsingleton.elim (E →L[ℝ] ℝ) (by infer_instance) (fderiv ℝ h x) 0]
  let Ψ : ℝ → ℝ := fun s ↦ max (Φ s) 0
  have hΨ_ofReal (r : ℝ) : ENNReal.ofReal (Φ r) = ENNReal.ofReal (Ψ r) := by
    simp [Ψ, ENNReal.ofReal_max]
  have hΨ0 : Ψ 0 = 0 := max_eq_right hΦ0
  have hΨ_conv : ConvexOn ℝ (Ici 0) Ψ := hΦ.sup (convexOn_const 0 (convex_Ici 0))
  have hΨ_mono : MonotoneOn Ψ (Ici 0) := monotoneOn_max_zero_of_convexOn hΦ hΦ0
  let hp : E → ℝ := fun x ↦ max (h x) 0
  have hhp : LipschitzWith K hp := hh.max_const 0
  have hrearr_eq : (fun y ↦ ENNReal.ofReal (h y)) = fun y ↦ ENNReal.ofReal (hp y) :=
    funext fun y ↦ by simp [hp, ENNReal.ofReal_max]
  simp_rw [hΨ_ofReal, hrearr_eq]
  exact (lintegral_ofReal_map_norm_fderiv_le_of_nonneg hhp hΨ_conv hΨ_mono hΨ0).trans
    (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal
      (hΨ_mono (norm_nonneg _) (norm_nonneg _)
        (by simpa [hp] using norm_fderiv_max_sub_zero_le hh.continuous 0 x)))

/-- **Integrability in the Lipschitz convex-integrand Pólya–Szegő inequality.** If `h` is
`K`-Lipschitz and `Φ` is convex and nondecreasing on `[0, ∞)` with `Φ 0 = 0`, integrability of
`x ↦ Φ ‖fderiv ℝ h x‖` implies integrability of `x ↦ Φ ‖fderiv ℝ h* x‖`. -/
theorem integrable_map_norm_fderiv_toReal_schwarzRearrangement
    {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖)) :
    Integrable (fun x ↦ Φ ‖fderiv ℝ (fun z ↦
      (TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) := by
  have hnonneg (w : E → ℝ) (x : E) : 0 ≤ Φ ‖fderiv ℝ w x‖ :=
    hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) (norm_nonneg _) (norm_nonneg _)
  refine (lintegral_ofReal_ne_top_iff_integrable
    (measurable_map_norm_fderiv _ hΦm).aestronglyMeasurable (ae_of_all _ (hnonneg _))).1 ?_
  refine ne_top_of_le_ne_top ((lintegral_ofReal_ne_top_iff_integrable
    hint.aestronglyMeasurable (ae_of_all _ (hnonneg h))).2 hint) ?_
  exact hh.lintegral_ofReal_map_norm_fderiv_toReal_schwarzRearrangement_le hΦ hΦ0.le

/-- **Bochner-integral Pólya–Szegő inequality for Lipschitz functions.** For `K`-Lipschitz `h` and
convex nondecreasing `Φ` on `[0, ∞)` with `Φ 0 = 0`, if `x ↦ Φ ‖fderiv ℝ h x‖` is integrable then
`∫ x, Φ ‖fderiv ℝ h* x‖ ≤ ∫ x, Φ ‖fderiv ℝ h x‖`. -/
theorem integral_map_norm_fderiv_toReal_schwarzRearrangement_le
    {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖)) :
    ∫ x, Φ ‖fderiv ℝ (fun z ↦
        (TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ ≤
      ∫ x, Φ ‖fderiv ℝ h x‖ := by
  have hnonneg (w : E → ℝ) (x : E) : 0 ≤ Φ ‖fderiv ℝ w x‖ :=
    hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) (norm_nonneg _) (norm_nonneg _)
  have hint' := hh.integrable_map_norm_fderiv_toReal_schwarzRearrangement hΦ hΦm hΦ0 hint
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnonneg _)) hint'.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnonneg h)) hint.aestronglyMeasurable]
  exact ENNReal.toReal_mono
    ((lintegral_ofReal_ne_top_iff_integrable hint.aestronglyMeasurable
      (ae_of_all _ (hnonneg h))).2 hint)
    (hh.lintegral_ofReal_map_norm_fderiv_toReal_schwarzRearrangement_le hΦ hΦ0.le)

end LipschitzWith

/-! ### The `W^{1,1}` Pólya–Szegő inequality -/

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `L¹`-contraction of the real Schwarz rearrangement of positive parts, written with extended
norms. -/
private theorem lintegral_enorm_toReal_schwarzRearrangement_sub_le {u v : E → ℝ}
    (hu : AEMeasurable u volume) (hv : AEMeasurable v volume) :
    ∫⁻ x, ‖(schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (u y)) x).toReal -
        (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (v y)) x).toReal‖ₑ ≤
      ∫⁻ x, ‖u x - v x‖ₑ := by
  have htoReal (a b : ℝ≥0∞) : ‖a.toReal - b.toReal‖ₑ ≤ edist a b := by
    rw [ENNReal.edist_eq_max]
    rcases eq_or_ne a ∞ with rfl | ha
    · rcases eq_or_ne b ∞ with rfl | hb
      · simp
      · simp [ENNReal.top_sub hb]
    · rcases eq_or_ne b ∞ with rfl | hb
      · simp [ENNReal.top_sub ha]
      · rcases le_total a b with hab | hba
        · have htr : a.toReal ≤ b.toReal := ENNReal.toReal_mono hb hab
          rw [← ofReal_norm, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 htr),
            ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hb,
            ENNReal.ofReal_toReal ha]
          exact le_max_right _ _
        · have htr : b.toReal ≤ a.toReal := ENNReal.toReal_mono ha hba
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 htr),
            ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha,
            ENNReal.ofReal_toReal hb]
          exact le_max_left _ _
  have hofReal (a b : ℝ) : edist (ENNReal.ofReal a) (ENNReal.ofReal b) ≤ ‖a - b‖ₑ := by
    have hsub (x y : ℝ) : ENNReal.ofReal x - ENNReal.ofReal y ≤ ENNReal.ofReal |x - y| := by
      have hy : ENNReal.ofReal y = ENNReal.ofReal (max y 0) := by simp [ENNReal.ofReal_max]
      rw [hy, ← ENNReal.ofReal_sub x (le_max_right y 0)]
      exact ENNReal.ofReal_le_ofReal (by grind)
    rw [ENNReal.edist_eq_max, ← ofReal_norm, Real.norm_eq_abs]
    exact max_le (hsub a b) (abs_sub_comm a b ▸ hsub b a)
  calc ∫⁻ x, ‖(schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (u y)) x).toReal -
          (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (v y)) x).toReal‖ₑ
      ≤ ∫⁻ x, edist (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (u y)) x)
          (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (v y)) x) :=
        lintegral_mono fun _ ↦ htoReal _ _
    _ ≤ ∫⁻ x, edist (ENNReal.ofReal (u x)) (ENNReal.ofReal (v x)) := by
        simpa using lintegral_edist_rpow_schwarzRearrangement_le volume
          hu.ennreal_ofReal hv.ennreal_ofReal le_rfl
    _ ≤ ∫⁻ x, ‖u x - v x‖ₑ := lintegral_mono fun _ ↦ hofReal _ _

/-- Convolving an integrable scalar function with a smooth compactly supported bump yields a
globally Lipschitz function. -/
private theorem exists_lipschitzWith_normed_convolution (phi : ContDiffBump (0 : E))
    {u : E → ℝ} (hu : Integrable u volume) :
    ∃ K : ℝ≥0, LipschitzWith K ((phi.normed volume) ⋆[lsmul ℝ ℝ, volume] u) := by
  have hrho_cd : ContDiff ℝ 1 (phi.normed volume) := phi.contDiff_normed
  have hrho_cpt : HasCompactSupport (phi.normed volume) := phi.hasCompactSupport_normed
  obtain ⟨C, hC⟩ := (hrho_cpt.fderiv ℝ).exists_bound_of_continuous
    (hrho_cd.continuous_fderiv one_ne_zero)
  let L : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hrho_lip : LipschitzWith L (phi.normed volume) :=
    lipschitzWith_of_nnNorm_fderiv_le (hrho_cd.differentiable one_ne_zero) fun x ↦ by
      rw [← NNReal.coe_le_coe, coe_nnNorm]
      exact (hC x).trans (le_max_left _ _)
  let K : ℝ≥0 :=
    ⟨(L : ℝ) * ∫ z, ‖u z‖, mul_nonneg L.coe_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)⟩
  refine ⟨K, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  have hflip (w : E) : ((phi.normed volume) ⋆[lsmul ℝ ℝ, volume] u) w =
      ∫ z, phi.normed volume (w - z) * u z := by
    rw [← convolution_flip]
    rfl
  have hint (w : E) : Integrable (fun z ↦ phi.normed volume (w - z) * u z) volume := by
    simpa only [flip_apply, lsmul_apply, smul_eq_mul] using
      (hrho_cpt.convolutionExists_right (lsmul ℝ ℝ).flip hu.locallyIntegrable
        hrho_cd.continuous w).integrable
  rw [Real.dist_eq, hflip x, hflip y, ← integral_sub (hint x) (hint y)]
  calc |∫ z, (phi.normed volume (x - z) * u z - phi.normed volume (y - z) * u z)|
      ≤ ∫ z, ‖(phi.normed volume (x - z) - phi.normed volume (y - z)) * u z‖ := by
        simpa [sub_mul] using norm_integral_le_integral_norm
          (fun z ↦ phi.normed volume (x - z) * u z - phi.normed volume (y - z) * u z)
    _ ≤ ∫ z, ((L : ℝ) * dist x y) * ‖u z‖ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _)
          (hu.norm.const_mul _) (ae_of_all _ fun z ↦ ?_)
        dsimp only
        rw [norm_mul, Real.norm_eq_abs, ← Real.dist_eq]
        exact mul_le_mul_of_nonneg_right
          ((hrho_lip.dist_le_mul (x - z) (y - z)).trans_eq (by rw [dist_sub_right]))
          (norm_nonneg _)
    _ = (K : ℝ) * dist x y := by
        have hK : (K : ℝ) = (L : ℝ) * ∫ z, ‖u z‖ := rfl
        rw [integral_const_mul, hK]
        ring

/-- On the whole space, the weak gradient of `u : W1p volume ⊤ 1` is integrable. -/
private theorem W1p.integrable_gradient (u : W1p (E := E) volume ⊤ 1) :
    Integrable (W1p.gradient u : E → E) volume :=
  memLp_one_iff_integrable.1 (by simpa using Lp.memLp (W1p.gradient u))

/-- Combining convolution Jensen with the Lipschitz convex-integrand Pólya–Szegő inequality on any
`u : W1p volume ⊤ 1` and normalized smooth bump `phi`. -/
private theorem lintegral_ofReal_fderiv_schwarzRearrangement_convolution_le
    (u : W1p (E := E) volume ⊤ 1) (phi : ContDiffBump (0 : E))
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦ (schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (((phi.normed volume) ⋆[lsmul ℝ ℝ, volume] ⇑(W1p.value u)) y))
        z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖W1p.gradient u x‖) := by
  have hu_int : Integrable (W1p.value u : E → ℝ) volume :=
    memLp_one_iff_integrable.1 (W1p.memLp_value u)
  have hg_int : Integrable (W1p.gradient u : E → E) volume := W1p.integrable_gradient u
  obtain ⟨K, hK⟩ := exists_lipschitzWith_normed_convolution phi hu_int
  have hflip : (phi.normed volume) ⋆[lsmul ℝ ℝ, volume] ⇑(W1p.value u) =
      ⇑(W1p.value u) ⋆[(lsmul ℝ ℝ).flip, volume] phi.normed volume := by
    rw [← convolution_flip]
  calc ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ (fun z ↦ (schwarzRearrangement volume
          (fun y ↦ ENNReal.ofReal (((phi.normed volume) ⋆[lsmul ℝ ℝ, volume] ⇑(W1p.value u)) y))
          z).toReal) x‖)
      ≤ ∫⁻ x, ENNReal.ofReal
          (Φ ‖fderiv ℝ ((phi.normed volume) ⋆[lsmul ℝ ℝ, volume] ⇑(W1p.value u)) x‖) :=
        hK.lintegral_ofReal_map_norm_fderiv_toReal_schwarzRearrangement_le hΦ hΦ0.le
    _ ≤ ∫⁻ x, ENNReal.ofReal (Φ ‖innerSL ℝ (W1p.gradient u x)‖) := by
        rw [hflip]
        exact (W1p.hasWeakFDerivOn u).lintegral_ofReal_map_norm_fderiv_convolution_le
          hu_int.locallyIntegrable
          ((innerSL ℝ (E := E)).integrable_comp hg_int).locallyIntegrable
          hΦ hΦm phi.contDiff_normed phi.hasCompactSupport_normed
          (ae_of_all _ phi.nonneg_normed) phi.integral_normed
    _ = ∫⁻ x, ENNReal.ofReal (Φ ‖W1p.gradient u x‖) :=
        lintegral_congr fun x ↦ by rw [innerSL_apply_norm]

/-- De la Vallée Poussin superlinear convex function for `W1p.gradient u`, converted to an extended
Lebesgue finiteness bound. -/
private theorem exists_convexOn_superlinear_lintegral_gradient_ne_top
    (u : W1p (E := E) volume ⊤ 1) :
    ∃ Φ : ℝ → ℝ, Φ 0 = 0 ∧ MonotoneOn Φ (Ici 0) ∧ ConvexOn ℝ (Ici 0) Φ ∧
      Tendsto (fun t ↦ Φ t / t) atTop atTop ∧
      ∫⁻ x, ENNReal.ofReal (Φ ‖W1p.gradient u x‖) ≠ ∞ := by
  obtain ⟨Φ, hΦ0, hΦm, hΦc, hΦsup, hΦint⟩ :=
    (W1p.integrable_gradient u).exists_convexOn_superlinear_integrable
  refine ⟨Φ, hΦ0, hΦm.monotoneOn _, hΦc.subset (subset_univ _) (convex_Ici 0), hΦsup, ?_⟩
  exact (lintegral_ofReal_ne_top_iff_integrable hΦint.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by simpa [hΦ0] using hΦm (norm_nonneg _))).2 hΦint

/-- **Quantitative equi-integrability of rearranged mollifications.** For any `u : W1p volume ⊤ 1`,
any family of normalized smooth bumps `phi i`, and any `ε ≠ 0`, there is `T : ℝ≥0` such that
`∫⁻ x in s, ‖fderiv ℝ (((phi i).normed volume ⋆ W1p.value u)*) x‖ₑ ≤ T * volume s + ε` uniformly in
`i` and `s : Set E`. -/
theorem W1p.exists_setLIntegral_enorm_fderiv_toReal_schwarzRearrangement_convolution_le
    (u : W1p (E := E) volume ⊤ 1) {ι : Type*} (phi : ι → ContDiffBump (0 : E)) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) :
    ∃ T : ℝ≥0, ∀ (i : ι) (s : Set E),
      ∫⁻ x in s, ‖fderiv ℝ (fun z ↦ (schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (((phi i).normed volume ⋆[lsmul ℝ ℝ, volume] ⇑(W1p.value u)) y))
        z).toReal) x‖ₑ ≤ T * volume s + ε := by
  obtain ⟨Φ, hΦ0, hΦm, hΦc, hΦsup, hC⟩ := exists_convexOn_superlinear_lintegral_gradient_ne_top u
  exact exists_setLIntegral_enorm_le_mul_add hΦsup hC
    (fun i ↦ lintegral_ofReal_fderiv_schwarzRearrangement_convolution_le u (phi i) hΦc hΦm hΦ0) hε

/-- Transferring `UniformIntegrable` from `volume` to `volume.restrict (⊤ : Opens E)` on plain
function families. -/
private theorem uniformIntegrable_restrict_top {α β : Type*} [NormedAddCommGroup β]
    {f : α → E → β} (hf : UniformIntegrable f 1 (volume : Measure E)) :
    UniformIntegrable f 1 (volume.restrict (⊤ : Opens E)) := by
  rwa [Opens.coe_top, Measure.restrict_univ]

/-- Identifying `eLpNorm` on `volume.restrict (⊤ : Opens E)` with `eLpNorm` on `volume` for plain
functions. -/
private theorem eLpNorm_restrict_top {β : Type*} [NormedAddCommGroup β] (f : E → β) :
    eLpNorm f 1 (volume.restrict (⊤ : Opens E)) = eLpNorm f 1 (volume : Measure E) := by
  rw [Opens.coe_top, Measure.restrict_univ]

/-- Uniform integrability of the Fréchet derivatives of rearranged mollifications for any
`w : W1p volume ⊤ 1` and bump family `phi`. -/
private theorem uniformIntegrable_fderiv_schwarzRearrangement_convolution
    (w : W1p (E := E) volume ⊤ 1) {ι : Type*} (phi : ι → ContDiffBump (0 : E)) :
    UniformIntegrable
      (fun i ↦ fderiv ℝ fun z ↦ (schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (((phi i).normed volume ⋆[lsmul ℝ ℝ, volume] ⇑(W1p.value w)) y))
        z).toReal)
      1 (volume.restrict (⊤ : Opens E)) := by
  obtain ⟨Φ, hΦ0, hΦm, hΦc, hΦsup, hC⟩ := exists_convexOn_superlinear_lintegral_gradient_ne_top w
  refine uniformIntegrable_restrict_top ⟨unifIntegrable_of_lintegral_ofReal_le hΦsup
      (fun i ↦ (measurable_fderiv ℝ _).aestronglyMeasurable) hC fun i ↦
      lintegral_ofReal_fderiv_schwarzRearrangement_convolution_le w (phi i) hΦc hΦm hΦ0, ?_⟩
  refine (iSup_le fun i ↦ ?_).trans_lt (W1p.integrable_gradient w).2
  rw [eLpNorm_one_eq_lintegral_eNorm (measurable_fderiv ℝ _).aestronglyMeasurable]
  simpa [ofReal_norm] using lintegral_ofReal_fderiv_schwarzRearrangement_convolution_le w (phi i)
    (convexOn_id (convex_Ici 0)) monotoneOn_id rfl

/-- Core existence of an `L¹` weak gradient for the real Schwarz rearrangement of the positive part
of `u : W1p volume ⊤ 1`, bounded in `L¹` by the weak gradient of `u⁺`. -/
private theorem exists_hasWeakFDerivOn_of_w1p (u : W1p (E := E) volume ⊤ 1) :
    ∃ g : E → E,
      HasWeakFDerivOn volume ⊤
        (fun x ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (W1p.value u y)) x).toReal)
        (fun x ↦ innerSL ℝ (g x)) ∧
      MemLp g 1 (volume.restrict (⊤ : Opens E)) ∧
      ∫⁻ x, ‖g x‖ₑ ≤ ∫⁻ x, ‖W1p.gradient (W1p.posPart ENNReal.one_ne_top u) x‖ₑ := by
  set w := W1p.posPart ENNReal.one_ne_top u
  let phi : ℕ → ContDiffBump (0 : E) := fun n ↦
    ⟨1 / ((n : ℝ) + 2), 1 / ((n : ℝ) + 1), by positivity, by gcongr; linarith⟩
  have hw_int : Integrable (W1p.value w : E → ℝ) volume :=
    memLp_one_iff_integrable.1 (W1p.memLp_value w)
  let v_n : ℕ → E → ℝ := fun n x ↦ (schwarzRearrangement volume
    (fun y ↦ ENNReal.ofReal (((phi n).normed volume ⋆[lsmul ℝ ℝ, volume] ⇑(W1p.value w)) y))
    x).toReal
  let v₀ : E → ℝ := fun x ↦
    (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (W1p.value w y)) x).toReal
  have hv_weak (n : ℕ) : HasWeakFDerivOn volume ⊤ (v_n n) (fderiv ℝ (v_n n)) := by
    obtain ⟨K, hK⟩ := exists_lipschitzWith_normed_convolution (phi n) hw_int
    exact ((lipschitzWith_toReal_schwarzRearrangement volume hK).locallyLipschitz.locallyLipschitzOn
      (s := (⊤ : Opens E))).hasWeakFDerivOn_fderiv
  have hL1_bound (n : ℕ) : ∫⁻ x, ‖fderiv ℝ (v_n n) x‖ₑ ≤ ∫⁻ x, ‖W1p.gradient w x‖ₑ := by
    simpa [ofReal_norm] using lintegral_ofReal_fderiv_schwarzRearrangement_convolution_le w (phi n)
      (convexOn_id (convex_Ici 0)) monotoneOn_id rfl
  have hconv (K : Set E) (_ : IsCompact K) (_ : K ⊆ (⊤ : Opens E)) :
      Tendsto (fun n ↦ ∫⁻ x in K, ‖v_n n x - v₀ x‖ₑ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_lintegral_enorm_normed_convolution_sub (phi := phi)
        tendsto_one_div_add_atTop_nhds_zero_nat hw_int)
      (fun _ ↦ bot_le) fun n ↦ (setLIntegral_le_lintegral _ _).trans ?_
    obtain ⟨L, hL⟩ := exists_lipschitzWith_normed_convolution (phi n) hw_int
    exact lintegral_enorm_toReal_schwarzRearrangement_sub_le
      hL.continuous.aemeasurable hw_int.aemeasurable
  obtain ⟨g, hg_weak, hg_int, hg_le⟩ :=
    (hw_int.toReal_schwarzRearrangement.locallyIntegrable.locallyIntegrableOn ⊤)
      |>.exists_hasWeakFDerivOn_integrableOn_of_uniformIntegrable hv_weak
        (uniformIntegrable_fderiv_schwarzRearrangement_convolution w phi) hconv
  have hv₀_eq : v₀ = fun x ↦
      (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (W1p.value u y)) x).toReal := by
    ext x; dsimp only [v₀]; congr 1
    refine congrFun (schwarzRearrangement_congr_ae volume ?_) x
    have hae : ⇑(W1p.value w) =ᵐ[volume] fun y ↦ max (W1p.value u y) 0 := by
      simpa [w, W1p.value_posPart] using Lp.coeFn_posPart (W1p.value u)
    filter_upwards [hae] with y hy
    rw [hy, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
  rw [hv₀_eq] at hg_weak
  rw [Opens.coe_top, integrableOn_univ] at hg_int
  rw [Opens.coe_top, Measure.restrict_univ] at hg_le
  exact ⟨g, hg_weak, memLp_one_iff_integrable.2 (by simpa using hg_int),
    hg_le.trans (liminf_le_of_frequently_le' (Eventually.of_forall hL1_bound).frequently)⟩

namespace W1p

/-- `L¹` membership of the real Schwarz rearrangement of `(W1p.value u)⁺` on `⊤`. -/
private theorem memLp_toReal_schwarzRearrangement_value (u : W1p (E := E) volume ⊤ 1) :
    MemLp
      (fun x ↦ (TauCeti.schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (W1p.value u y)) x).toReal)
      1 (volume.restrict (⊤ : Opens E)) := by
  simpa using memLp_one_iff_integrable.2
    (memLp_one_iff_integrable.1 (W1p.memLp_value u)).toReal_schwarzRearrangement

/-- Weak-gradient compatibility between the `Lp` classes used to construct
`W1p.schwarzRearrangement u`. -/
private theorem hasWeakFDerivOn_toLp_schwarzRearrangement (u : W1p (E := E) volume ⊤ 1) :
    HasWeakFDerivOn volume ⊤
      ((memLp_toReal_schwarzRearrangement_value u).toLp _)
      (fun x ↦ innerSL ℝ
        (((Classical.choose_spec (exists_hasWeakFDerivOn_of_w1p u)).2.1.toLp _) x)) := by
  let hg := Classical.choose_spec (exists_hasWeakFDerivOn_of_w1p u)
  refine (hg.1.congr_ae (memLp_toReal_schwarzRearrangement_value u).coeFn_toLp.symm).congr_ae_deriv
    ?_
  filter_upwards [hg.2.1.coeFn_toLp] with x hx
  rw [hx]

/-- **Positive-part Schwarz rearrangement on `W^{1,1}`.** Maps `u : W1p volume ⊤ 1` to the
`W^{1,1}` element whose value is the symmetric decreasing rearrangement of `(W1p.value u)⁺`. -/
def schwarzRearrangement (u : W1p (E := E) volume ⊤ 1) : W1p (E := E) volume ⊤ 1 :=
  W1p.mk
    ((memLp_toReal_schwarzRearrangement_value u).toLp _)
    ((Classical.choose_spec (exists_hasWeakFDerivOn_of_w1p u)).2.1.toLp _)
    (hasWeakFDerivOn_toLp_schwarzRearrangement u)

/-- The value of `W1p.schwarzRearrangement u` agrees almost everywhere with the real Schwarz
rearrangement of `(W1p.value u)⁺`. -/
theorem value_schwarzRearrangement_ae (u : W1p (E := E) volume ⊤ 1) :
    ⇑(W1p.value (W1p.schwarzRearrangement u)) =ᵐ[volume.restrict (⊤ : Opens E)]
      fun x ↦ (TauCeti.schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (W1p.value u y)) x).toReal := by
  rw [schwarzRearrangement, W1p.value_mk]
  exact MemLp.coeFn_toLp _

/-- The canonical everywhere-defined radial rearrangement `u*` has weak gradient
`W1p.gradient (W1p.schwarzRearrangement u)` on the whole space. -/
theorem hasWeakFDerivOn_toReal_schwarzRearrangement (u : W1p (E := E) volume ⊤ 1) :
    HasWeakFDerivOn volume ⊤
      (fun x ↦ (TauCeti.schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (W1p.value u y)) x).toReal)
      (fun x ↦ innerSL ℝ (W1p.gradient (W1p.schwarzRearrangement u) x)) :=
  (W1p.hasWeakFDerivOn (W1p.schwarzRearrangement u)).congr_ae (value_schwarzRearrangement_ae u)

/-- **Exclusion of singular concentration for `u*`.** For `u : W1p volume ⊤ 1`, the BV variation
measure of `u*` is absolutely continuous with respect to `volume`, with density
`‖W1p.gradient (W1p.schwarzRearrangement u) ·‖ₑ`. -/
theorem variationMeasure_toReal_schwarzRearrangement_eq_withDensity (u : W1p (E := E) volume ⊤ 1) :
    variationMeasure volume ⊤
      (fun x ↦ (TauCeti.schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (W1p.value u y)) x).toReal) =
      (volume.comap ((↑) : (⊤ : Opens E) → E)).withDensity
        fun x ↦ ‖W1p.gradient (W1p.schwarzRearrangement u) (x : E)‖ₑ := by
  rw [(hasWeakFDerivOn_toReal_schwarzRearrangement u).variationMeasure_eq_withDensity]
  congr 1 with x
  rw [← ofReal_norm, innerSL_apply_norm, ofReal_norm]

/-- The `L¹` norm of `W1p.value (W1p.schwarzRearrangement u)` equals that of `(W1p.value u)⁺`. -/
theorem norm_value_schwarzRearrangement_eq_posPart (u : W1p (E := E) volume ⊤ 1) :
    ‖W1p.value (W1p.schwarzRearrangement u)‖ = ‖Lp.posPart (W1p.value u)‖ := by
  have hu_int : Integrable (W1p.value u : E → ℝ) volume :=
    memLp_one_iff_integrable.1 (W1p.memLp_value u)
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (value_schwarzRearrangement_ae u),
    eLpNorm_congr_ae (Lp.coeFn_posPart (W1p.value u)),
    eLpNorm_restrict_top, eLpNorm_restrict_top,
    eLpNorm_one_eq_lintegral_eNorm hu_int.toReal_schwarzRearrangement.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_eNorm hu_int.pos_part.aestronglyMeasurable]
  congr 1
  have hlhs : ∫⁻ x, ‖(TauCeti.schwarzRearrangement volume
        (fun y ↦ ENNReal.ofReal (W1p.value u y)) x).toReal‖ₑ =
      ∫⁻ x, TauCeti.schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (W1p.value u y)) x := by
    refine lintegral_congr_ae ?_
    filter_upwards [hu_int.ae_schwarzRearrangement_ofReal_ne_top] with x hx
    rw [Real.eNorm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx]
  rw [hlhs, lintegral_schwarzRearrangement volume hu_int.aemeasurable.ennreal_ofReal]
  refine lintegral_congr fun x ↦ ?_
  rw [Real.eNorm_of_nonneg (le_max_right _ _), ENNReal.ofReal_max, ENNReal.ofReal_zero,
    max_eq_left zero_le]

/-- Positive-part Schwarz rearrangement does not increase the `L¹` value norm. -/
theorem norm_value_schwarzRearrangement_le (u : W1p (E := E) volume ⊤ 1) :
    ‖W1p.value (W1p.schwarzRearrangement u)‖ ≤ ‖W1p.value u‖ := by
  rw [norm_value_schwarzRearrangement_eq_posPart]
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [Lp.coeFn_posPart (W1p.value u)] with x hx
  rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ (0 : ℝ))]
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- For almost-everywhere nonnegative `u : W1p volume ⊤ 1`, Schwarz rearrangement preserves the
`L¹` value norm. -/
theorem norm_value_schwarzRearrangement_of_ae_nonneg {u : W1p (E := E) volume ⊤ 1}
    (hu : ∀ᵐ x ∂volume.restrict (⊤ : Opens E), 0 ≤ W1p.value u x) :
    ‖W1p.value (W1p.schwarzRearrangement u)‖ = ‖W1p.value u‖ := by
  rw [norm_value_schwarzRearrangement_eq_posPart]
  congr 1
  apply Lp.ext
  filter_upwards [Lp.coeFn_posPart (W1p.value u), hu] with x hx hux
  rw [hx, max_eq_left hux]

/-- **Sharp positive-part `W^{1,1}` Pólya–Szegő inequality.** The `L¹` norm of the weak gradient of
`W1p.schwarzRearrangement u` is at most that of `u⁺`. -/
theorem norm_gradient_schwarzRearrangement_le_posPart (u : W1p (E := E) volume ⊤ 1) :
    ‖W1p.gradient (W1p.schwarzRearrangement u)‖ ≤
      ‖W1p.gradient (W1p.posPart ENNReal.one_ne_top u)‖ := by
  let hg := Classical.choose_spec (exists_hasWeakFDerivOn_of_w1p u)
  have hgrad_ae : ⇑(W1p.gradient (W1p.schwarzRearrangement u)) =ᵐ[volume.restrict (⊤ : Opens E)]
      Classical.choose (exists_hasWeakFDerivOn_of_w1p u) := by
    rw [schwarzRearrangement, W1p.gradient_mk]
    exact hg.2.1.coeFn_toLp
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hgrad_ae]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) ?_
  have hm1 : MemLp (Classical.choose (exists_hasWeakFDerivOn_of_w1p u)) 1 volume := by
    simpa using hg.2.1
  have hm2 : MemLp (W1p.gradient (W1p.posPart ENNReal.one_ne_top u) : E → E) 1 volume := by
    simpa using Lp.memLp (W1p.gradient (W1p.posPart ENNReal.one_ne_top u))
  rw [eLpNorm_restrict_top, eLpNorm_restrict_top (W1p.gradient _ : E → E),
    eLpNorm_one_eq_lintegral_eNorm hm1.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_eNorm hm2.aestronglyMeasurable]
  exact hg.2.2

/-- **`W^{1,1}` Pólya–Szegő inequality, `L¹` norm form.** The `L¹` norm of the weak gradient of
`W1p.schwarzRearrangement u` is at most that of `u`. -/
theorem norm_gradient_schwarzRearrangement_le (u : W1p (E := E) volume ⊤ 1) :
    ‖W1p.gradient (W1p.schwarzRearrangement u)‖ ≤ ‖W1p.gradient u‖ := by
  refine (norm_gradient_schwarzRearrangement_le_posPart u).trans (Lp.norm_le_norm_of_ae_le ?_)
  filter_upwards [W1p.gradient_posPart_ae ENNReal.one_ne_top u] with x hx
  rw [hx]
  exact norm_indicator_le_norm_self _ _

/-- On the whole space, the Bochner integral of `‖W1p.gradient v ·‖` equals `‖W1p.gradient v‖`. -/
private theorem integral_norm_gradient_eq_norm (v : W1p (E := E) volume ⊤ 1) :
    ∫ x, ‖W1p.gradient v x‖ = ‖W1p.gradient v‖ := by
  have hm : MemLp (W1p.gradient v : E → E) 1 volume := by simpa using Lp.memLp (W1p.gradient v)
  rw [Lp.norm_def, eLpNorm_restrict_top (W1p.gradient v : E → E),
    eLpNorm_one_eq_lintegral_eNorm hm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ norm_nonneg _)
      hm.aestronglyMeasurable.norm]
  congr 1
  exact lintegral_congr fun _ ↦ by rw [ofReal_norm]

/-- **`W^{1,1}` Pólya–Szegő inequality, Bochner integral form.** -/
theorem integral_norm_gradient_schwarzRearrangement_le (u : W1p (E := E) volume ⊤ 1) :
    ∫ x, ‖W1p.gradient (W1p.schwarzRearrangement u) x‖ ≤ ∫ x, ‖W1p.gradient u x‖ := by
  rw [integral_norm_gradient_eq_norm, integral_norm_gradient_eq_norm]
  exact norm_gradient_schwarzRearrangement_le u

/-- **Absolute-value Schwarz rearrangement on `W^{1,1}`.** Maps `u : W1p volume ⊤ 1` to the
`W^{1,1}` element whose value is the symmetric decreasing rearrangement of `|W1p.value u|`. -/
def schwarzRearrangementNorm (u : W1p (E := E) volume ⊤ 1) : W1p (E := E) volume ⊤ 1 :=
  W1p.schwarzRearrangement (W1p.posPart ENNReal.one_ne_top u + W1p.posPart ENNReal.one_ne_top (-u))

/-- Helper identifying the value of `u⁺ + (-u)⁺` almost everywhere with `|W1p.value u|`. -/
private theorem value_posPart_add_posPart_neg_ae (u : W1p (E := E) volume ⊤ 1) :
    ⇑(W1p.value (W1p.posPart ENNReal.one_ne_top u + W1p.posPart ENNReal.one_ne_top (-u))) =ᵐ[
        volume.restrict (⊤ : Opens E)] fun x ↦ |W1p.value u x| := by
  filter_upwards [W1p.value_add_ae (W1p.posPart ENNReal.one_ne_top u)
      (W1p.posPart ENNReal.one_ne_top (-u)),
    Lp.coeFn_posPart (W1p.value u), Lp.coeFn_posPart (W1p.value (-u)),
    W1p.value_neg_ae u] with x hadd hp1 hp2 hneg
  simp only [W1p.value_posPart, Pi.add_apply, Pi.neg_apply] at hadd hp1 hp2 hneg ⊢
  rw [hadd, hp1, hp2, hneg]
  rcases le_total 0 (W1p.value u x) with h | h
  · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.2 h), add_zero]
  · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (neg_nonneg.2 h), zero_add]

/-- The value of `W1p.schwarzRearrangementNorm u` agrees almost everywhere with the real Schwarz
rearrangement of `‖W1p.value u ·‖ₑ`. -/
theorem value_schwarzRearrangementNorm_ae (u : W1p (E := E) volume ⊤ 1) :
    ⇑(W1p.value (W1p.schwarzRearrangementNorm u)) =ᵐ[volume.restrict (⊤ : Opens E)]
      fun x ↦ (TauCeti.schwarzRearrangement volume (fun y ↦ ‖W1p.value u y‖ₑ) x).toReal := by
  have hae : ⇑(W1p.value (W1p.posPart ENNReal.one_ne_top u +
        W1p.posPart ENNReal.one_ne_top (-u))) =ᵐ[volume] fun x ↦ |W1p.value u x| := by
    simpa using value_posPart_add_posPart_neg_ae u
  have hcongr : TauCeti.schwarzRearrangement volume
      (fun y ↦ ENNReal.ofReal
        (W1p.value (W1p.posPart ENNReal.one_ne_top u + W1p.posPart ENNReal.one_ne_top (-u)) y)) =
      TauCeti.schwarzRearrangement volume (fun y ↦ ‖W1p.value u y‖ₑ) := by
    refine schwarzRearrangement_congr_ae volume ?_
    filter_upwards [hae] with y hy
    rw [hy, ← Real.norm_eq_abs, ofReal_norm]
  filter_upwards [value_schwarzRearrangement_ae
    (W1p.posPart ENNReal.one_ne_top u + W1p.posPart ENNReal.one_ne_top (-u))] with x hx
  rw [schwarzRearrangementNorm, hx, hcongr]

/-- The canonical everywhere-defined radial rearrangement `|u|*` has weak gradient
`W1p.gradient (W1p.schwarzRearrangementNorm u)` on the whole space. -/
theorem hasWeakFDerivOn_toReal_schwarzRearrangementNorm (u : W1p (E := E) volume ⊤ 1) :
    HasWeakFDerivOn volume ⊤
      (fun x ↦ (TauCeti.schwarzRearrangement volume (fun y ↦ ‖W1p.value u y‖ₑ) x).toReal)
      (fun x ↦ innerSL ℝ (W1p.gradient (W1p.schwarzRearrangementNorm u) x)) :=
  (W1p.hasWeakFDerivOn (W1p.schwarzRearrangementNorm u)).congr_ae
    (value_schwarzRearrangementNorm_ae u)

/-- **Exclusion of singular concentration for `|u|*`.** For `u : W1p volume ⊤ 1`, the BV variation
measure of `|u|*` is absolutely continuous with respect to `volume`, with density
`‖W1p.gradient (W1p.schwarzRearrangementNorm u) ·‖ₑ`. -/
theorem variationMeasure_toReal_schwarzRearrangementNorm_eq_withDensity
    (u : W1p (E := E) volume ⊤ 1) :
    variationMeasure volume ⊤
      (fun x ↦ (TauCeti.schwarzRearrangement volume (fun y ↦ ‖W1p.value u y‖ₑ) x).toReal) =
      (volume.comap ((↑) : (⊤ : Opens E) → E)).withDensity
        fun x ↦ ‖W1p.gradient (W1p.schwarzRearrangementNorm u) (x : E)‖ₑ := by
  rw [(hasWeakFDerivOn_toReal_schwarzRearrangementNorm u).variationMeasure_eq_withDensity]
  congr 1 with x
  rw [← ofReal_norm, innerSL_apply_norm, ofReal_norm]

/-- Absolute-value Schwarz rearrangement preserves the `L¹` value norm. -/
@[simp]
theorem norm_value_schwarzRearrangementNorm (u : W1p (E := E) volume ⊤ 1) :
    ‖W1p.value (W1p.schwarzRearrangementNorm u)‖ = ‖W1p.value u‖ := by
  have hae := value_posPart_add_posPart_neg_ae u
  rw [schwarzRearrangementNorm, norm_value_schwarzRearrangement_of_ae_nonneg
    (hae.mono fun _ hx ↦ hx.symm ▸ abs_nonneg _), Lp.norm_def, Lp.norm_def]
  congr 1
  exact eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    (hae.mono fun x hx ↦ by rw [hx, Real.norm_eq_abs, abs_abs, Real.norm_eq_abs])

/-- **Signed `W^{1,1}` Pólya–Szegő inequality, `L¹` norm form.** Rearranging `|u|` does not
increase the `L¹` norm of the weak gradient. -/
theorem norm_gradient_schwarzRearrangementNorm_le (u : W1p (E := E) volume ⊤ 1) :
    ‖W1p.gradient (W1p.schwarzRearrangementNorm u)‖ ≤ ‖W1p.gradient u‖ := by
  refine (norm_gradient_schwarzRearrangement_le _).trans (Lp.norm_le_norm_of_ae_le ?_)
  filter_upwards [Lp.coeFn_add (W1p.gradient (W1p.posPart ENNReal.one_ne_top u))
      (W1p.gradient (W1p.posPart ENNReal.one_ne_top (-u))),
    W1p.gradient_posPart_ae ENNReal.one_ne_top u,
    W1p.gradient_posPart_ae ENNReal.one_ne_top (-u),
    W1p.value_neg_ae u, Lp.coeFn_neg (W1p.gradient u)] with x hadd hp1 hp2 hvneg hgneg
  rw [W1p.gradient_add, hadd, Pi.add_apply, hp1, hp2]
  by_cases hxpos : (0 : ℝ) < W1p.value u x
  · have hxneg : ¬ (0 : ℝ) < W1p.value (-u) x := by
      rw [hvneg, Pi.neg_apply]
      linarith
    rw [indicator_of_mem hxpos, indicator_of_notMem hxneg, add_zero]
  · rw [indicator_of_notMem hxpos, zero_add]
    refine (norm_indicator_le_norm_self _ _).trans_eq ?_
    rw [W1p.gradient_neg, hgneg, Pi.neg_apply, norm_neg]

/-- **Signed `W^{1,1}` Pólya–Szegő inequality, Bochner integral form.** -/
theorem integral_norm_gradient_schwarzRearrangementNorm_le (u : W1p (E := E) volume ⊤ 1) :
    ∫ x, ‖W1p.gradient (W1p.schwarzRearrangementNorm u) x‖ ≤ ∫ x, ‖W1p.gradient u x‖ := by
  rw [integral_norm_gradient_eq_norm, integral_norm_gradient_eq_norm]
  exact norm_gradient_schwarzRearrangementNorm_le u

end W1p

end TauCeti

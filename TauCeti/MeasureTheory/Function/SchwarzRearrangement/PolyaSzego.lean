/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.MeasureTheory.Function.SchwarzRearrangement.Lipschitz
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import TauCeti.Analysis.BoundedVariation.LevelPerimeter
import TauCeti.Analysis.BoundedVariation.SchwarzRearrangement
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Convex.Continuous
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.MeasureTheory.Function.Coarea.DistributionFunction
import TauCeti.MeasureTheory.Function.Coarea.Integral
import TauCeti.MeasureTheory.Function.SchwarzRearrangement.CriticalValues
import TauCeti.MeasureTheory.Integral.ReciprocalWeight

/-!
# The Pólya–Szegő inequality for Lipschitz functions

Let `E` be a nontrivial finite-dimensional real inner product space, and let `Φ : ℝ → ℝ` be convex
and monotone on `[0, ∞)` with `Φ 0 = 0`. For a Lipschitz function `h : E → ℝ` whose positive
superlevel sets `{x | t < h x}` (`t > 0`) have finite Lebesgue volume, the real-valued Schwarz
rearrangement `h* x := (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x).toReal`
is Lipschitz with the same constant and decreases `∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖)`, via
weighted coarea, Euclidean isoperimetry, and the reciprocal-weighted Jensen inequality on fibers.

## References

* J. E. Brothers, W. P. Ziemer, *Minimal rearrangements of Sobolev functions*, J. Reine Angew. Math.
  384 (1988), 153–179.
* G. Bianchi, R. J. Gardner, P. Gronchi, M. Kiderlen, *Rearrangement and polarization inequalities
  for Sobolev functions*, J. Funct. Anal. 287 (2024), Theorem 5.8.
-/

public section

open Filter Function MeasureTheory Metric Module Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_fderiv_eq_of_norm_eq {v : E → ℝ}
    (hrad : ∀ x y, ‖x‖ = ‖y‖ → v x = v y) {x y : E} (hxy : ‖x‖ = ‖y‖) :
    ‖fderiv ℝ v x‖ = ‖fderiv ℝ v y‖ := by
  let R := (ℝ ∙ (x - y))ᗮ.reflection
  have hcomp : v ∘ R = v := funext fun z ↦ hrad (R z) z (R.norm_map z)
  have h := R.norm_iteratedFDeriv_comp_right v x 1
  rwa [hcomp, Submodule.reflection_sub hxy, norm_iteratedFDeriv_one, norm_iteratedFDeriv_one] at h

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_eq_of_notMem_image_fderiv_eq_zero {v : E → ℝ}
    (hanti : ∀ x y, ‖x‖ ≤ ‖y‖ → v y ≤ v x) {t : ℝ}
    (ht : t ∉ v '' {z | fderiv ℝ v z = 0}) {x y : E} (hx : v x = t) (hy : v y = t) :
    ‖x‖ = ‖y‖ := by
  have hnot_lt {a b : E} (ha : v a = t) (hb : v b = t) (hab : ‖a‖ < ‖b‖) : False := by
    have hb0 : 0 < ‖b‖ := (norm_nonneg a).trans_lt hab
    let z₀ : E := ((‖a‖ + ‖b‖) / (2 * ‖b‖)) • b
    have hz₀_norm : ‖z₀‖ = (‖a‖ + ‖b‖) / 2 := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]; field_simp [hb0.ne']
    have hz₀_mem : z₀ ∈ {z : E | ‖a‖ < ‖z‖ ∧ ‖z‖ < ‖b‖} :=
      ⟨hz₀_norm ▸ by linarith, hz₀_norm ▸ by linarith⟩
    have hU : {z : E | ‖a‖ < ‖z‖ ∧ ‖z‖ < ‖b‖} ∈ 𝓝 z₀ := ((isOpen_lt continuous_const
      continuous_norm).inter (isOpen_lt continuous_norm continuous_const)).mem_nhds hz₀_mem
    have hconst : ∀ z ∈ {z : E | ‖a‖ < ‖z‖ ∧ ‖z‖ < ‖b‖}, v z = t := fun z hz ↦
      le_antisymm ((hanti a z hz.1.le).trans_eq ha) (hb.symm.trans_le (hanti z b hz.2.le))
    exact ht ⟨z₀, (EventuallyEq.fderiv_eq (eventually_of_mem hU hconst)).trans
      (fderiv_const_apply t), hconst z₀ hz₀_mem⟩
  exact (lt_trichotomy ‖x‖ ‖y‖).elim (fun h ↦ (hnot_lt hx hy h).elim)
    (Or.elim · id fun h ↦ (hnot_lt hy hx h).elim)

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_fderiv_max_zero_le {h : E → ℝ} (hh : Continuous h) (x : E) :
    ‖fderiv ℝ (fun y ↦ max (h y) 0) x‖ ≤ ‖fderiv ℝ h x‖ := by
  rcases lt_trichotomy (h x) 0 with hlt | heq | hgt
  · have h0 : fderiv ℝ (fun y ↦ max (h y) 0) x = 0 :=
      (EventuallyEq.fderiv_eq (f := fun _ ↦ (0 : ℝ)) ((hh.continuousAt.eventually
        (gt_mem_nhds hlt)).mono fun _ hy ↦ max_eq_right hy.le)).trans (fderiv_const_apply 0)
    simp [h0]
  · simp [show fderiv ℝ (fun y ↦ max (h y) 0) x = 0 from
      IsLocalMin.fderiv_eq_zero (.of_forall fun _ ↦ by simp [heq])]
  · exact le_of_eq (congrArg norm (EventuallyEq.fderiv_eq
      ((hh.continuousAt.eventually (lt_mem_nhds hgt)).mono fun _ hy ↦ max_eq_left hy.le)))

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
private theorem norm_fderiv_norm_le {u : E → ℝ} (hu : Continuous u) (x : E) :
    ‖fderiv ℝ (fun y ↦ ‖u y‖) x‖ ≤ ‖fderiv ℝ u x‖ := by
  rcases lt_trichotomy (u x) 0 with hlt | heq | hgt
  · have hneg : fderiv ℝ (fun y ↦ ‖u y‖) x = -fderiv ℝ u x :=
      (EventuallyEq.fderiv_eq (f := fun y ↦ -u y) ((hu.continuousAt.eventually
        (gt_mem_nhds hlt)).mono fun _ hy ↦ Real.norm_of_nonpos hy.le)).trans fderiv_neg
    rw [hneg, norm_neg]
  · have h0 : fderiv ℝ (fun y ↦ ‖u y‖) x = 0 :=
      IsLocalMin.fderiv_eq_zero (.of_forall fun _ ↦ by simp [heq])
    rw [h0]; simp
  · exact le_of_eq (congrArg norm (EventuallyEq.fderiv_eq
      ((hu.continuousAt.eventually (lt_mem_nhds hgt)).mono fun _ hy ↦ Real.norm_of_nonneg hy.le)))

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem measurable_map_norm_fderiv {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ)
    (hΦm : MonotoneOn Φ (Ici 0)) (u : E → ℝ) :
    Measurable fun x ↦ Φ ‖fderiv ℝ u x‖ := by
  have hcont : Continuous fun s : ℝ ↦ Φ (max s 0) := (hΦ.continuousOn_Ici_of_monotoneOn
    hΦm).comp_continuous (continuous_id.max continuous_const) fun s ↦ le_max_right s 0
  exact (funext fun x ↦ by rw [max_eq_left (norm_nonneg (fderiv ℝ u x))] :
    (fun x ↦ Φ (max ‖fderiv ℝ u x‖ 0)) = _) ▸ hcont.measurable.comp (measurable_fderiv ℝ u).norm

omit [Nontrivial E] in
private theorem lintegral_map_norm_fderiv_eq_setLIntegral_Ioi {Φ : ℝ → ℝ}
    (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    {u : E → ℝ} (hu0 : ∀ x, 0 ≤ u x) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ u x‖) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x in {x | fderiv ℝ u x ≠ 0} ∩ u ⁻¹' {t},
        ENNReal.ofReal (Φ ‖fderiv ℝ u x‖ / ‖fderiv ℝ u x‖) ∂μHE[finrank ℝ E - 1] := by
  set R := {x : E | fderiv ℝ u x ≠ 0}
  have hR : MeasurableSet R := (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ u)
  have hsurj (x : E) (hx : x ∈ R) : Surjective (fderiv ℝ u x) :=
    surjective_of_ne_zero_of_finrank_eq_one (finrank_self ℝ) (f := (fderiv ℝ u x).toLinearMap)
      ((ContinuousLinearMap.coe_injective.ne_iff' ContinuousLinearMap.toLinearMap_zero).2 hx)
  let g : E → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Φ ‖fderiv ℝ u x‖ / ‖fderiv ℝ u x‖)
  have hg : Measurable g := ENNReal.measurable_ofReal.comp
    ((measurable_map_norm_fderiv hΦ hΦm u).div (measurable_fderiv ℝ u).norm)
  have hlhs : ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ u x‖) =
      ∫⁻ x in R, ENNReal.ofReal (fderiv ℝ u x).adjoint.normDet * g x := by
    rw [← lintegral_indicator hR]
    refine lintegral_congr fun x ↦ ?_
    by_cases hx : x ∈ R
    · rw [indicator_of_mem hx, ContinuousLinearMap.normDet_adjoint_eq_norm,
        ← ENNReal.ofReal_mul (norm_nonneg _), mul_div_cancel₀ _ (norm_ne_zero_iff.2 hx)]
    · simp only [R, mem_ofPred_eq, not_not] at hx
      rw [indicator_of_notMem (by simp [R, hx]), hx, norm_zero, hΦ0, ENNReal.ofReal_zero]
  rw [hlhs, lintegral_normDet_adjoint_fderiv_mul_eq_lintegral_setLIntegral_fiber
    hR.nullMeasurableSet (fun _ hx ↦ differentiableAt_of_fderiv_ne_zero hx) hsurj hg, finrank_self,
    ← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun t ↦ ?_
  by_cases ht : 0 < t
  · rw [indicator_of_mem ht]
  · have hemp : R ∩ u ⁻¹' {t} = ∅ := eq_empty_of_forall_notMem fun x ⟨hxR, hxu⟩ ↦ hxR <| by
      have hux0 : u x = 0 := le_antisymm ((mem_preimage.1 hxu).trans_le (not_lt.1 ht)) (hu0 x)
      exact IsLocalMin.fderiv_eq_zero (.of_forall fun y ↦ hux0.symm ▸ hu0 y)
    rw [indicator_of_notMem (s := Ioi (0 : ℝ)) ht]; simp [hemp]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem setLIntegral_fiber_le_of_const_norm_fderiv {Φ : ℝ → ℝ}
    (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    {K : ℝ≥0} {v h : E → ℝ} {S_v S_h : Set E}
    (hSv_m : MeasurableSet S_v) (hSh_m : MeasurableSet S_h)
    (hSv_pos : ∀ x ∈ S_v, 0 < ‖fderiv ℝ v x‖) (hSh_pos : ∀ x ∈ S_h, 0 < ‖fderiv ℝ h x‖)
    (hSh_le : ∀ x ∈ S_h, ‖fderiv ℝ h x‖ ≤ K)
    (hconst : ∀ x ∈ S_v, ∀ y ∈ S_v, ‖fderiv ℝ v x‖ = ‖fderiv ℝ v y‖)
    (hperim : μHE[finrank ℝ E - 1] S_v ≤ μHE[finrank ℝ E - 1] S_h)
    (hinv : (∫⁻ x in S_h, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]) ≤
      ∫⁻ x in S_v, ‖fderiv ℝ v x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1])
    (hinv_fin : (∫⁻ x in S_v, ‖fderiv ℝ v x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]) < ∞)
    (hΦ_fin : (∫⁻ x in S_h, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖)
      ∂μHE[finrank ℝ E - 1]) < ∞) :
    (∫⁻ x in S_v, ENNReal.ofReal (Φ ‖fderiv ℝ v x‖ / ‖fderiv ℝ v x‖) ∂μHE[finrank ℝ E - 1]) ≤
      ∫⁻ x in S_h, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ∂μHE[finrank ℝ E - 1] := by
  set μH : Measure E := μHE[finrank ℝ E - 1]
  have hΦ_nn (s : ℝ) (hs : 0 ≤ s) : 0 ≤ Φ s := hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) hs hs
  have hSh_fin : μH S_h < ∞ :=
    calc μH S_h = ∫⁻ _ in S_h, 1 ∂μH := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in S_h, (K : ℝ≥0∞) * ‖fderiv ℝ h x‖ₑ⁻¹ ∂μH :=
          setLIntegral_mono ((measurable_fderiv ℝ h).eNorm.inv.const_mul _) fun x hx ↦ by
            have hne0 : ‖fderiv ℝ h x‖ₑ ≠ 0 := by
              rw [← ofReal_norm]; exact (ENNReal.ofReal_pos.2 (hSh_pos x hx)).ne'
            rw [← ENNReal.mul_inv_cancel hne0 (by simp [← ofReal_norm])]
            gcongr; rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
            exact ENNReal.ofReal_le_ofReal (hSh_le x hx)
      _ = (K : ℝ≥0∞) * ∫⁻ x in S_h, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μH :=
          lintegral_const_mul _ (measurable_fderiv ℝ h).eNorm.inv
      _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_lt_top (hinv.trans_lt hinv_fin)
  have hSv_fin : μH S_v < ∞ := hperim.trans_lt hSh_fin
  by_cases hSv0 : μH S_v = 0
  · simp [Measure.restrict_eq_zero.2 hSv0]
  obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero hSv0
  set γ := ‖fderiv ℝ v x₀‖; have hγ : 0 < γ := hSv_pos x₀ hx₀
  set ν_h := μH.restrict S_h; have : Fact (μH S_h < ∞) := ⟨hSh_fin⟩
  set P := (μH S_v).toReal; set M := (∫⁻ x in S_v, ‖fderiv ℝ v x‖ₑ⁻¹ ∂μH).toReal
  have hP_pos : 0 < P := ENNReal.toReal_pos hSv0 hSv_fin.ne
  have hM_eq : M = P / γ := by
    have hm : (∫⁻ x in S_v, ‖fderiv ℝ v x‖ₑ⁻¹ ∂μH) = ENNReal.ofReal γ⁻¹ * μH S_v :=
      (setLIntegral_const _ _).symm ▸ setLIntegral_congr_fun hSv_m fun x hx ↦ by
        rw [← ofReal_norm, hconst x hx x₀ hx₀, ENNReal.ofReal_inv_of_pos hγ]
    simp [M, P, hm, ENNReal.toReal_ofReal (inv_nonneg.2 hγ.le), inv_mul_eq_div]
  have hlhs_eq : (∫⁻ x in S_v, ENNReal.ofReal (Φ ‖fderiv ℝ v x‖ / ‖fderiv ℝ v x‖) ∂μH) =
      ENNReal.ofReal (M * Φ (P / M)) := by
    have hc : (∫⁻ x in S_v, ENNReal.ofReal (Φ ‖fderiv ℝ v x‖ / ‖fderiv ℝ v x‖) ∂μH) =
        ENNReal.ofReal (Φ γ / γ) * μH S_v :=
      (setLIntegral_const _ _).symm ▸ setLIntegral_congr_fun hSv_m fun x hx ↦ by
        rw [hconst x hx x₀ hx₀]
    rw [hc, show P / M = γ by rw [hM_eq, div_div_cancel₀ hP_pos.ne'], hM_eq,
      ← ENNReal.ofReal_toReal hSv_fin.ne, ← ENNReal.ofReal_mul (div_nonneg (hΦ_nn γ hγ.le) hγ.le)]
    congr 1; ring
  have hg_pos : ∀ᵐ x ∂ν_h, 0 < ‖fderiv ℝ h x‖ := (ae_restrict_mem hSh_m).mono hSh_pos
  have hinv_int : Integrable (fun x ↦ ‖fderiv ℝ h x‖⁻¹) ν_h :=
    ⟨(measurable_fderiv ℝ h).norm.inv.aestronglyMeasurable,
      (lintegral_congr_ae <| hg_pos.mono fun _ hx ↦ by
        rw [← ofReal_norm, ← ofReal_norm, Real.norm_of_nonneg (inv_nonneg.2 hx.le),
          ENNReal.ofReal_inv_of_pos hx]).trans_lt (hinv.trans_lt hinv_fin)⟩
  have hΦ_int : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖) ν_h :=
    ⟨((measurable_map_norm_fderiv hΦ hΦm h).div (measurable_fderiv ℝ h).norm).aestronglyMeasurable,
      (lintegral_congr_ae <| hg_pos.mono fun _ hx ↦ by
        rw [← ofReal_norm, Real.norm_of_nonneg (div_nonneg (hΦ_nn _ hx.le) hx.le)]).trans_lt hΦ_fin⟩
  have hM_bound : (∫ x, ‖fderiv ℝ h x‖⁻¹ ∂ν_h) ≤ M := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hinv_fin.ne,
      ofReal_integral_eq_lintegral_ofReal hinv_int (hg_pos.mono fun _ hx ↦ inv_nonneg.2 hx.le)]
    exact (setLIntegral_congr_fun hSh_m fun x hx ↦ by
      rw [← ofReal_norm, ENNReal.ofReal_inv_of_pos (hSh_pos x hx)]).le.trans hinv
  have hPν : P ≤ ν_h.real univ := by
    rw [measureReal_def, Measure.restrict_apply_univ]; exact ENNReal.toReal_mono hSh_fin.ne hperim
  rw [hlhs_eq, ← ofReal_integral_eq_lintegral_ofReal hΦ_int
    (hg_pos.mono fun _ hx ↦ div_nonneg (hΦ_nn _ hx.le) hx.le)]
  exact ENNReal.ofReal_le_ofReal
    (hΦ.mul_map_div_le_integral_div hΦm hΦ0 hg_pos hinv_int hΦ_int hP_pos.le hPν hM_bound)

private theorem schwarzRearrangement_ofReal_ne_top {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) (x : E) :
    schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x ≠ ∞ := by
  refine schwarzRearrangement_ne_top volume (K := K) (fun a b ↦ ?_) (t := ENNReal.ofReal 1)
    (by simp) ?_ x
  · refine (ENNReal.ofReal_le_ofReal (hh.le_add_mul a b)).trans ?_
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
    exact ENNReal.ofReal_add_le
  · convert hfin 1 zero_lt_one using 2
    ext y; exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_one

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
private theorem setOf_differentiableAt_and_surjective_eq_setOf_fderiv_ne_zero (w : E → ℝ) :
    {x : E | DifferentiableAt ℝ w x ∧ Surjective (fderiv ℝ w x)} = {x : E | fderiv ℝ w x ≠ 0} := by
  ext x; simp only [mem_ofPred_eq]
  refine ⟨fun ⟨_, hs⟩ h0 ↦ ?_, fun hx ↦ ⟨differentiableAt_of_fderiv_ne_zero hx,
    surjective_of_ne_zero_of_finrank_eq_one (finrank_self ℝ) (f := (fderiv ℝ w x).toLinearMap)
      ((ContinuousLinearMap.coe_injective.ne_iff' ContinuousLinearMap.toLinearMap_zero).2 hx)⟩⟩
  obtain ⟨y, hy⟩ := hs 1; simp [h0] at hy

private theorem ae_fiber_bounds_toReal_schwarzRearrangement
    {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) :
    let v : E → ℝ := fun x ↦
      (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) x).toReal
    ∀ᵐ t : ℝ, 0 < t →
      t ∉ v '' {z | fderiv ℝ v z = 0} ∧
      μHE[finrank ℝ E - 1] ({x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t}) ≤
        μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) ∧
      (∫⁻ x in {x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}, ‖fderiv ℝ h x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]) ≤
        (∫⁻ x in {x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t}, ‖fderiv ℝ v x‖ₑ⁻¹ ∂μHE[finrank ℝ E - 1]) ∧
      (∫⁻ x in {x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t}, ‖fderiv ℝ v x‖ₑ⁻¹
        ∂μHE[finrank ℝ E - 1]) < ∞ := by
  set f : E → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (h y)
  set v : E → ℝ := fun x ↦ (schwarzRearrangement volume f x).toReal
  have hv_lip : LipschitzWith K v := lipschitzWith_toReal_schwarzRearrangement volume hh
  have hv_ne_top := schwarzRearrangement_ofReal_ne_top hh hfin
  have hv_level {t : ℝ} (ht : 0 < t) :
      {x | t < v x} = {x | ENNReal.ofReal t < schwarzRearrangement volume f x} :=
    Set.ext fun x ↦ (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hv_ne_top x)).symm
  have hh_level {t : ℝ} (ht : 0 < t) : {x | ENNReal.ofReal t < f x} = {x | t < h x} :=
    Set.ext fun _ ↦ ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le
  have hcrit := hh.volume_image_setOf_fderiv_toReal_schwarzRearrangement_eq_zero volume
  filter_upwards [compl_mem_ae_iff.2 hcrit, hh.ae_restrict_inter_setOf_regular_preimage_eq univ,
    hv_lip.ae_restrict_inter_setOf_regular_preimage_eq univ,
    hh.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage,
    hv_lip.ae_perimeter_setOf_lt_eq_euclideanHausdorffMeasure_preimage,
    ae_setLIntegral_inv_enorm_fderiv_le_ofReal_neg_deriv hfin,
    hh.ae_setLIntegral_inv_enorm_fderiv_toReal_schwarzRearrangement_eq_ofReal_neg_deriv hfin]
    with t hcritt hregh hregv hperh hperv hdisth hdistv ht
  rw [finrank_self, univ_inter, univ_inter,
    setOf_differentiableAt_and_surjective_eq_setOf_fderiv_ne_zero h] at hregh
  rw [finrank_self, univ_inter, univ_inter,
    setOf_differentiableAt_and_surjective_eq_setOf_fderiv_ne_zero v] at hregv
  refine ⟨hcritt, ?_, hdistv ht ▸ hdisth ht, (hdistv ht) ▸ ENNReal.ofReal_lt_top⟩
  rw [show μHE[finrank ℝ E - 1] ({x | fderiv ℝ v x ≠ 0} ∩ v ⁻¹' {t}) =
      μHE[finrank ℝ E - 1] (v ⁻¹' {t}) by
        simpa using congrArg (fun ν : Measure E ↦ ν univ) hregv.symm,
    show μHE[finrank ℝ E - 1] ({x | fderiv ℝ h x ≠ 0} ∩ h ⁻¹' {t}) =
      μHE[finrank ℝ E - 1] (h ⁻¹' {t}) by
        simpa using congrArg (fun ν : Measure E ↦ ν univ) hregh.symm,
    ← hperv, ← hperh, hv_level ht, ← hh_level ht]
  have hm : MeasurableSet {x | ENNReal.ofReal t < f x} :=
    measurableSet_lt measurable_const hh.continuous.measurable.ennreal_ofReal
  exact hm.nullMeasurableSet.perimeter_setOf_lt_schwarzRearrangement_le

private theorem lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le_of_nonneg
    {K : ℝ≥0} {h : E → ℝ} (hh : LipschitzWith K h) (hh0 : ∀ x, 0 ≤ h x)
    (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) := by
  by_cases htop : ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) = ∞
  · exact htop ▸ le_top
  set f : E → ℝ≥0∞ := fun y ↦ ENNReal.ofReal (h y)
  set v : E → ℝ := fun x ↦ (schwarzRearrangement volume f x).toReal
  have hv_lip : LipschitzWith K v := lipschitzWith_toReal_schwarzRearrangement volume hh
  have hv_ne_top := schwarzRearrangement_ofReal_ne_top hh hfin
  have hco_h := lintegral_map_norm_fderiv_eq_setLIntegral_Ioi hΦ hΦm hΦ0 hh0
  rw [lintegral_map_norm_fderiv_eq_setLIntegral_Ioi hΦ hΦm hΦ0 (fun _ ↦ ENNReal.toReal_nonneg),
    hco_h]
  set R_v := {x : E | fderiv ℝ v x ≠ 0}; set R_h := {x : E | fderiv ℝ h x ≠ 0}
  have hRv_m : MeasurableSet R_v :=
    (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ v)
  have hRh_m : MeasurableSet R_h :=
    (measurableSet_singleton 0).compl.preimage (measurable_fderiv ℝ h)
  have hΦ_ae_fin : ∀ᵐ t : ℝ, t ∈ Ioi (0 : ℝ) →
      (∫⁻ x in R_h ∩ h ⁻¹' {t}, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖ / ‖fderiv ℝ h x‖)
        ∂μHE[finrank ℝ E - 1]) < ∞ := by
    have hmeas := aemeasurable_setLIntegral_fiber_of_hasFDerivWithinAt volume
      hRh_m.nullMeasurableSet
      (fun _ hx ↦ (differentiableAt_of_fderiv_ne_zero hx).hasFDerivAt.hasFDerivWithinAt)
      (ENNReal.measurable_ofReal.comp
        ((measurable_map_norm_fderiv hΦ hΦm h).div (measurable_fderiv ℝ h).norm))
    rw [finrank_self] at hmeas
    exact (ae_restrict_iff' measurableSet_Ioi).1 (ae_lt_top' hmeas.restrict (hco_h ▸ htop))
  have hrad (x y : E) (hxy : ‖x‖ = ‖y‖) : v x = v y :=
    congrArg ENNReal.toReal (schwarzRearrangement_eq_of_norm_eq volume f hxy)
  have hanti (x y : E) (hxy : ‖x‖ ≤ ‖y‖) : v y ≤ v x :=
    ENNReal.toReal_mono (hv_ne_top x) (schwarzRearrangement_le_of_norm_le volume f hxy)
  refine setLIntegral_mono_ae' measurableSet_Ioi ?_
  filter_upwards [hΦ_ae_fin, ae_fiber_bounds_toReal_schwarzRearrangement hh hfin]
    with t hΦt hfib ht
  obtain ⟨hcritt, hperim_le, hinv_le, hinv_fin⟩ := hfib ht
  exact setLIntegral_fiber_le_of_const_norm_fderiv hΦ hΦm hΦ0
    (hRv_m.inter (isClosed_singleton.preimage hv_lip.continuous).measurableSet)
    (hRh_m.inter (isClosed_singleton.preimage hh.continuous).measurableSet)
    (fun _ hx ↦ norm_pos_iff.2 hx.1) (fun _ hx ↦ norm_pos_iff.2 hx.1)
    (fun _ _ ↦ norm_fderiv_le_of_lipschitz ℝ hh)
    (fun _ hx _ hy ↦ norm_fderiv_eq_of_norm_eq hrad
      (norm_eq_of_notMem_image_fderiv_eq_zero hanti hcritt hx.2 hy.2))
    hperim_le hinv_le hinv_fin (hΦt ht)

omit [Nontrivial E] in
private theorem integrable_and_integral_le_of_lintegral_le {v u : E → ℝ} {Φ : ℝ → ℝ}
    (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hle : ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ v x‖) ≤ ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ u x‖))
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ u x‖) volume) :
    Integrable (fun x ↦ Φ ‖fderiv ℝ v x‖) volume ∧
      ∫ x, Φ ‖fderiv ℝ v x‖ ≤ ∫ x, Φ ‖fderiv ℝ u x‖ := by
  have hΦ_nn (s : ℝ) (hs : 0 ≤ s) : 0 ≤ Φ s := hΦ0 ▸ hΦm (mem_Ici.2 le_rfl) hs hs
  have heq (w : E → ℝ) : (∫⁻ x, ‖Φ ‖fderiv ℝ w x‖‖ₑ) =
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ w x‖) :=
    lintegral_congr fun _ ↦ by rw [← ofReal_norm, Real.norm_of_nonneg (hΦ_nn _ (norm_nonneg _))]
  have hint_v : Integrable (fun x ↦ Φ ‖fderiv ℝ v x‖) volume :=
    ⟨(measurable_map_norm_fderiv hΦ hΦm v).aestronglyMeasurable,
      by rw [HasFiniteIntegral, heq v]; exact hle.trans_lt (heq u ▸ hint.hasFiniteIntegral)⟩
  refine ⟨hint_v, ?_⟩
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ ↦ hΦ_nn _ (norm_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal hint_v (.of_forall fun _ ↦ hΦ_nn _ (norm_nonneg _)),
    ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ ↦ hΦ_nn _ (norm_nonneg _))]
  exact hle

section PublicAPI

/-- **The convex-integrand Pólya–Szegő inequality for Lipschitz functions.** -/
theorem lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ h x‖) := by
  let hpos : E → ℝ := fun x ↦ max (h x) 0
  have hhpos_lip : LipschitzWith K hpos := by
    simpa only [max_eq_left (zero_le : 0 ≤ K)] using hh.max (LipschitzWith.const (0 : ℝ))
  have hhpos_fin (t : ℝ) (ht : 0 < t) : volume {x | t < hpos x} ≠ ∞ := by
    convert hfin t ht using 2; ext x; simp [hpos, lt_max_iff, ht.not_gt]
  have hofReal : (fun y ↦ ENNReal.ofReal (h y)) = fun y ↦ ENNReal.ofReal (hpos y) := funext fun y ↦
    (le_total 0 (h y)).elim (fun hy ↦ by simp [hpos, max_eq_left hy])
      (fun hy ↦ by simp [hpos, max_eq_right hy, ENNReal.ofReal_of_nonpos hy])
  rw [hofReal]
  exact (lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le_of_nonneg hhpos_lip
    (fun x ↦ le_max_right (h x) 0) hhpos_fin hΦ hΦm hΦ0).trans (lintegral_mono fun x ↦
      ENNReal.ofReal_le_ofReal
        (hΦm (norm_nonneg _) (norm_nonneg _) (norm_fderiv_max_zero_le hh.continuous x)))

/-- **Signed convex-integrand Pólya–Szegő inequality for Lipschitz functions.** -/
theorem lintegral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le {K : ℝ≥0} {u : E → ℝ}
    (hu : LipschitzWith K u) (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0) :
    ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖) ≤
      ∫⁻ x, ENNReal.ofReal (Φ ‖fderiv ℝ u x‖) := by
  have hu_norm : LipschitzWith K (fun x ↦ ‖u x‖) := by
    simpa only [one_mul, Function.comp_def] using
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).comp hu
  exact (lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le hu_norm hfin hΦ hΦm hΦ0).trans
    (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal
      (hΦm (norm_nonneg _) (norm_nonneg _) (norm_fderiv_norm_le hu.continuous x)))

/-- Integrability of `Φ ‖Dh*‖` when `Φ ‖Dh‖` is integrable. -/
theorem integrable_map_norm_fderiv_toReal_schwarzRearrangement {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖) volume) :
    Integrable (fun x ↦ Φ ‖fderiv ℝ
      (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖)
      volume :=
  (integrable_and_integral_le_of_lintegral_le hΦ hΦm hΦ0
    (lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le hh hfin hΦ hΦm hΦ0) hint).1

/-- **Bochner-integral Pólya–Szegő inequality** for the positive-part Schwarz rearrangement. -/
theorem integral_map_norm_fderiv_toReal_schwarzRearrangement_le {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ h x‖) volume) :
    ∫ x, Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ ≤
      ∫ x, Φ ‖fderiv ℝ h x‖ :=
  (integrable_and_integral_le_of_lintegral_le hΦ hΦm hΦ0
    (lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le hh hfin hΦ hΦm hΦ0) hint).2

/-- Integrability of `Φ ‖D(|u|*)‖` when `Φ ‖Du‖` is integrable. -/
theorem integrable_map_norm_fderiv_toReal_schwarzRearrangement_norm {K : ℝ≥0} {u : E → ℝ}
    (hu : LipschitzWith K u) (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ u x‖) volume) :
    Integrable (fun x ↦ Φ ‖fderiv ℝ
      (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖)
      volume :=
  (integrable_and_integral_le_of_lintegral_le hΦ hΦm hΦ0
    (lintegral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le hu hfin hΦ hΦm hΦ0) hint).1

/-- **Signed Bochner-integral Pólya–Szegő inequality** for `‖u ·‖`. -/
theorem integral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le {K : ℝ≥0} {u : E → ℝ}
    (hu : LipschitzWith K u) (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞)
    {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici 0) Φ) (hΦm : MonotoneOn Φ (Ici 0)) (hΦ0 : Φ 0 = 0)
    (hint : Integrable (fun x ↦ Φ ‖fderiv ℝ u x‖) volume) :
    ∫ x, Φ ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖ ≤
      ∫ x, Φ ‖fderiv ℝ u x‖ :=
  (integrable_and_integral_le_of_lintegral_le hΦ hΦm hΦ0
    (lintegral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le hu hfin hΦ hΦm hΦ0) hint).2

/-- **`Lᵖ` gradient Pólya–Szegő inequality (`1 ≤ p`, `lintegral` form)** for the positive part. -/
theorem lintegral_norm_fderiv_toReal_schwarzRearrangement_rpow_le {K : ℝ≥0} {h : E → ℝ}
    (hh : LipschitzWith K h) (hfin : ∀ t, 0 < t → volume {x | t < h x} ≠ ∞) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal (h y)) z).toReal) x‖ ^ p) ≤
      ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ h x‖ ^ p) :=
  lintegral_map_norm_fderiv_toReal_schwarzRearrangement_le hh hfin (convexOn_rpow hp)
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (zero_le_one.trans hp))
    (Real.zero_rpow (zero_lt_one.trans_le hp).ne')

/-- **Signed `Lᵖ` gradient Pólya–Szegő inequality (`1 ≤ p`, `lintegral` form)**. -/
theorem lintegral_norm_fderiv_toReal_schwarzRearrangement_norm_rpow_le {K : ℝ≥0} {u : E → ℝ}
    (hu : LipschitzWith K u) (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖ ^ p) ≤
      ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ u x‖ ^ p) :=
  lintegral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le hu hfin (convexOn_rpow hp)
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (zero_le_one.trans hp))
    (Real.zero_rpow (zero_lt_one.trans_le hp).ne')

/-- Integrability of `‖D(|u|*)‖ ^ p` (`1 ≤ p`) when `‖Du‖ ^ p` is integrable. -/
theorem integrable_norm_fderiv_toReal_schwarzRearrangement_norm_rpow {K : ℝ≥0} {u : E → ℝ}
    (hu : LipschitzWith K u) (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞) {p : ℝ} (hp : 1 ≤ p)
    (hint : Integrable (fun x ↦ ‖fderiv ℝ u x‖ ^ p) volume) :
    Integrable (fun x ↦ ‖fderiv ℝ
      (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖ ^ p)
      volume :=
  integrable_map_norm_fderiv_toReal_schwarzRearrangement_norm hu hfin (convexOn_rpow hp)
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (zero_le_one.trans hp))
    (Real.zero_rpow (zero_lt_one.trans_le hp).ne') hint

/-- **Signed `Lᵖ` gradient Pólya–Szegő inequality (`1 ≤ p`, Bochner-integral form)**. -/
theorem integral_norm_fderiv_toReal_schwarzRearrangement_norm_rpow_le {K : ℝ≥0} {u : E → ℝ}
    (hu : LipschitzWith K u) (hfin : ∀ t, 0 < t → volume {x | t < ‖u x‖} ≠ ∞) {p : ℝ} (hp : 1 ≤ p)
    (hint : Integrable (fun x ↦ ‖fderiv ℝ u x‖ ^ p) volume) :
    ∫ x, ‖fderiv ℝ
        (fun z ↦ (schwarzRearrangement volume (fun y ↦ ENNReal.ofReal ‖u y‖) z).toReal) x‖ ^ p ≤
      ∫ x, ‖fderiv ℝ u x‖ ^ p :=
  integral_map_norm_fderiv_toReal_schwarzRearrangement_norm_le hu hfin (convexOn_rpow hp)
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (zero_le_one.trans hp))
    (Real.zero_rpow (zero_lt_one.trans_le hp).ne') hint

end PublicAPI

end TauCeti

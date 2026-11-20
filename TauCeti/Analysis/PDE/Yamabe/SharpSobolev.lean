/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Analysis.PDE.Yamabe.Bubble.Basic
public import TauCeti.Analysis.PDE.Yamabe.SphereConstant
public import TauCeti.Analysis.Sobolev.D1p0.Basic
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.PDE.Yamabe.Bubble.Cutoff
import TauCeti.Analysis.PDE.Yamabe.Bubble.Homogeneous
import TauCeti.Analysis.PDE.Yamabe.WeightedSobolev
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.SchwarzRearrangement.PolyaSzego

/-!
# The sharp Euclidean Sobolev inequality

For a finite-dimensional real inner product space `E` of dimension `n > 2` with Lebesgue measure,
let `aₙ = 4 (n - 1) / (n - 2)` (`TauCeti.Yamabe.conformalCoefficient`),
`pₙ = 2 n / (n - 2)` (`TauCeti.Yamabe.criticalExponent`), and
`Y(Sⁿ) = n (n - 1) |Sⁿ| ^ (2 / n)` (`TauCeti.Yamabe.sphereYamabeConstant`).

This file establishes the sharp Euclidean Sobolev inequality
`Y(Sⁿ) (∫ |u| ^ pₙ) ^ (2 / pₙ) ≤ aₙ ∫ ‖du‖²` for:
* compactly supported Lipschitz functions
  (`sphereYamabeConstant_mul_rpow_le_conformalCoefficient_mul_integral_of_lipschitzWith`);
* compactly supported `C¹` functions
  (`sphereYamabeConstant_mul_rpow_le_conformalCoefficient_mul_integral`);
* elements of `D1p0 volume ⊤ 2`, in both norm and integral form, together with sharpness on
  `D1p0 volume ⊤ 2` and `C_c^∞(E)`.

## References

* T. Aubin, *Problèmes isopérimétriques et espaces de Sobolev*, J. Differential Geom. 11 (1976).
* G. Talenti, *Best constant in Sobolev inequality*, Ann. Mat. Pura Appl. 110 (1976), 353–372.
* D. Cordero-Erausquin, B. Nazaret, C. Villani, *A mass-transportation approach to sharp Sobolev and
  Gagliardo–Nirenberg inequalities*, Adv. Math. 182 (2004), 307–332.
-/

public section

noncomputable section

open Filter Function MeasureTheory Metric Module Set TopologicalSpace
open scoped ContDiff Distributions Gradient NNReal Topology

namespace TauCeti.Yamabe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

private theorem volume_real_ball_pos {r : ℝ} (hr : 0 < r) : 0 < volume.real (ball (0 : E) r) :=
  measureReal_def _ _ ▸ ENNReal.toReal_pos
    (isOpen_ball.measure_pos volume (nonempty_ball.2 hr)).ne' measure_ball_lt_top.ne

private theorem mul_integral_bubbleRadialWeight_eq_roundSphereVolume (hn : 2 < finrank ℝ E) :
    (finrank ℝ E : ℝ) * (volume.real (ball (0 : E) 1) *
        ∫ s in Ioi (0 : ℝ), bubbleRadialWeight (finrank ℝ E) s) =
      roundSphereVolume (finrank ℝ E) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have h := integral_bubble_rpow_criticalExponent_eq_roundSphereVolume
    (E := E) (by omega) hn.ne' one_pos 0
  simp_rw [bubble_rpow_criticalExponent hn.ne' one_pos, sub_zero] at h
  rw [integral_fun_norm_addHaar volume (fun s ↦ (2 * 1 / (1 ^ 2 + s ^ 2)) ^ finrank ℝ E),
    setIntegral_congr_fun (g := bubbleRadialWeight (finrank ℝ E)) measurableSet_Ioi fun s _ ↦ by
      simp [bubbleRadialWeight_def, smul_eq_mul]] at h
  simpa only [nsmul_eq_mul, smul_eq_mul, mul_assoc] using h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem deriv_radial_sq_le {v : E → ℝ} (hv_rad : ∀ x y, ‖x‖ = ‖y‖ → v x = v y)
    {e₀ : E} (he₀ : ‖e₀‖ = 1) {r : ℝ} (hr : 0 < r) :
    (deriv (fun s : ℝ ↦ v (s • e₀)) r) ^ 2 ≤ ‖fderiv ℝ v (r • e₀)‖ ^ 2 := by
  set g : ℝ → ℝ := fun s ↦ v (s • e₀)
  by_cases hg : DifferentiableAt ℝ g r
  · have hre₀_ne : r • e₀ ≠ 0 := fun h0 ↦ by
      have := congrArg norm h0; simp [norm_smul, abs_of_pos hr, he₀, hr.ne'] at this
    have hv_eq : v = g ∘ norm := funext fun x ↦ hv_rad x (‖x‖ • e₀) (by simp [norm_smul, he₀])
    have hnorm_r : ‖r • e₀‖ = r := by simp [norm_smul, abs_of_pos hr, he₀]
    have hv_diff : DifferentiableAt ℝ v (r • e₀) :=
      hv_eq ▸ (hnorm_r ▸ hg).comp (r • e₀) (differentiableAt_id.norm ℝ hre₀_ne)
    have hray : HasDerivAt (fun s : ℝ ↦ s • e₀) e₀ r := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id r).smul_const e₀
    have hg_deriv : HasDerivAt g (fderiv ℝ v (r • e₀) e₀) r :=
      hv_diff.hasFDerivAt.comp_hasDerivAt r hray
    rw [hg_deriv.deriv]; refine sq_le_sq.mpr ?_
    rw [abs_of_nonneg (norm_nonneg _), ← Real.norm_eq_abs]
    simpa only [he₀, mul_one] using (fderiv ℝ v (r • e₀)).le_opNorm e₀
  · rw [deriv_zero_of_not_differentiableAt hg]; simp

private theorem integrable_norm_fderiv_sq_of_lipschitzWith {K : ℝ≥0} {u : E → ℝ}
    (hu : LipschitzWith K u) (hsupp : HasCompactSupport u) :
    Integrable (fun x ↦ ‖fderiv ℝ u x‖ ^ 2) volume := by
  refine ((integrableOn_const (C := (K : ℝ) ^ 2) hsupp.measure_lt_top.ne).integrable_indicator
    hsupp.isCompact.isClosed.measurableSet).mono'
    ((measurable_fderiv ℝ u).norm.pow_const 2).aestronglyMeasurable (.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases hx : x ∈ tsupport u
  · rw [indicator_of_mem hx]
    exact sq_le_sq.mpr (by simpa only [abs_of_nonneg (norm_nonneg _), abs_of_nonneg K.coe_nonneg]
      using norm_fderiv_le_of_lipschitz ℝ hu)
  · simp [indicator_of_notMem hx, (notMem_tsupport_iff_eventuallyEq.mp hx).fderiv_eq]

private theorem integral_radial_deriv_sq_le [Nontrivial E] {K : ℝ≥0} {v : E → ℝ}
    (hv_lip : LipschitzWith K v) (hv_supp : HasCompactSupport v)
    (hv_rad : ∀ x y, ‖x‖ = ‖y‖ → v x = v y) {e₀ : E} (he₀ : ‖e₀‖ = 1) (c : ℝ) :
    (finrank ℝ E : ℝ) * (volume.real (ball (0 : E) 1) *
        ∫ r in Ioi (0 : ℝ), r ^ (finrank ℝ E - 1) *
          (deriv (fun r ↦ c * v (max r 0 • e₀)) r) ^ 2) ≤
      c ^ 2 * ∫ x, ‖fderiv ℝ v x‖ ^ 2 := by
  set n := finrank ℝ E with hn_def
  let f : ℝ → ℝ := fun r ↦ c * v (max r 0 • e₀)
  let φ : ℝ → ℝ := fun r ↦ ‖fderiv ℝ v (max r 0 • e₀)‖ ^ 2
  have hv_grad_int := integrable_norm_fderiv_sq_of_lipschitzWith hv_lip hv_supp
  have hv_grad_eq : (fun x : E ↦ ‖fderiv ℝ v x‖ ^ 2) = fun x ↦ φ ‖x‖ := funext fun x ↦ by
    have hnorm : ‖x‖ = ‖‖x‖ • e₀‖ := by rw [norm_smul, Real.norm_eq_abs, abs_norm, he₀, mul_one]
    simp only [φ, max_eq_left (norm_nonneg x), norm_fderiv_eq_of_norm_eq hv_rad hnorm]
  have hφ_int : IntegrableOn (fun r ↦ r ^ (n - 1) * ‖fderiv ℝ v (r • e₀)‖ ^ 2) (Ioi 0) := by
    rw [hv_grad_eq] at hv_grad_int
    exact ((integrable_fun_norm_addHaar volume (f := φ)).mp hv_grad_int).congr_fun
      (fun r (hr : 0 < r) ↦ by simp [φ, max_eq_left hr.le, smul_eq_mul, ← hn_def]) measurableSet_Ioi
  have hpt : ∀ r ∈ Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2 ≤
      c ^ 2 * (r ^ (n - 1) * ‖fderiv ℝ v (r • e₀)‖ ^ 2) := fun r (hr : 0 < r) ↦ by
    have hev : f =ᶠ[𝓝 r] fun s ↦ c * v (s • e₀) :=
      eventually_of_mem (Ioi_mem_nhds hr) fun s hs ↦ by simp [f, max_eq_left hs.le]
    rw [hev.deriv_eq, deriv_const_mul_field, mul_pow, mul_left_comm]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (deriv_radial_sq_le hv_rad he₀ hr) (pow_nonneg hr.le _))
      (sq_nonneg c)
  have hderiv_f_int : IntegrableOn (fun r ↦ r ^ (n - 1) * (deriv f r) ^ 2) (Ioi 0) :=
    (hφ_int.const_mul (c ^ 2)).mono' (((continuous_pow (n - 1)).measurable.mul
      ((measurable_deriv f).pow_const 2)).aestronglyMeasurable.restrict)
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr ↦ by
        rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (mem_Ioi.1 hr).le _) (sq_nonneg _))]
        exact hpt r hr)
  have hrad_le : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2 ≤
      c ^ 2 * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * ‖fderiv ℝ v (r • e₀)‖ ^ 2 := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on hderiv_f_int (hφ_int.const_mul (c ^ 2)) measurableSet_Ioi hpt
  have hgrad_polar : (n : ℝ) * (volume.real (ball (0 : E) 1) *
      ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * ‖fderiv ℝ v (r • e₀)‖ ^ 2) = ∫ x, ‖fderiv ℝ v x‖ ^ 2 := by
    rw [hv_grad_eq, integral_fun_norm_addHaar volume φ]
    simp only [nsmul_eq_mul, smul_eq_mul, ← hn_def]; congr 2
    exact setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ by
      simp [φ, max_eq_left hr.le]
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrad_le measureReal_nonneg)
    (Nat.cast_nonneg n)).trans_eq (by rw [← hgrad_polar]; ring)

private theorem radial_sharp_sobolev (hn : 2 < finrank ℝ E) {K : ℝ≥0} {v : E → ℝ}
    (hv_lip : LipschitzWith K v) (hv_nonneg : ∀ x, 0 ≤ v x)
    (hv_anti : ∀ x y, ‖x‖ ≤ ‖y‖ → v y ≤ v x) {R : ℝ} (hR : 0 < R)
    (hvR : ∀ x, R ≤ ‖x‖ → v x = 0) :
    sphereYamabeConstant (finrank ℝ E) *
        (∫ x, v x ^ criticalExponent (finrank ℝ E)) ^ (2 / criticalExponent (finrank ℝ E)) ≤
      conformalCoefficient (finrank ℝ E) * ∫ x, ‖fderiv ℝ v x‖ ^ 2 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  set n := finrank ℝ E with hn_def
  set pₙ := criticalExponent n
  have hpₙ : 0 < pₙ := criticalExponent_pos hn
  have hv_supp : HasCompactSupport v :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) R) fun x hx ↦
      mem_closedBall_zero_iff.2 (not_lt.1 fun hlt ↦ hx (hvR x hlt.le))
  set M := ∫ x, v x ^ pₙ
  have hM_nn : 0 ≤ M := integral_nonneg fun x ↦ Real.rpow_nonneg (hv_nonneg x) _
  rcases hM_nn.eq_or_lt with hM0 | hM_pos
  · rw [← hM0, Real.zero_rpow (div_pos zero_lt_two hpₙ).ne', mul_zero]
    exact mul_nonneg (conformalCoefficient_pos hn).le (integral_nonneg fun _ ↦ sq_nonneg _)
  -- Stage 1: Construct the normalized radial profile `f` and verify its regularity and support.
  obtain ⟨e₀, he₀⟩ := exists_norm_eq (E := E) zero_le_one
  have hv_rad (x y : E) (h : ‖x‖ = ‖y‖) : v x = v y :=
    le_antisymm (hv_anti y x h.ge) (hv_anti x y h.le)
  have hI₀_val := mul_integral_bubbleRadialWeight_eq_roundSphereVolume (E := E) hn
  set I₀ := ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s
  have hball := volume_real_ball_pos (E := E) one_pos
  set c := (roundSphereVolume n / M) ^ (1 / pₙ)
  have hc0 : 0 ≤ roundSphereVolume n / M := div_nonneg (roundSphereVolume_pos n).le hM_pos.le
  have hc : 0 < c := Real.rpow_pos_of_pos (div_pos (roundSphereVolume_pos n) hM_pos) _
  let f : ℝ → ℝ := fun r ↦ c * v (max r 0 • e₀)
  have hf_lip : LipschitzWith (c.toNNReal * K) f := LipschitzWith.of_dist_le_mul fun r₁ r₂ ↦ by
    simp only [f, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hc, NNReal.coe_mul,
      Real.coe_toNNReal c hc.le, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    have hmax := (LipschitzWith.id.max (LipschitzWith.const 0)).dist_le_mul r₁ r₂
    simp only [id_eq, max_eq_left zero_le_one, NNReal.coe_one, one_mul, Real.dist_eq] at hmax
    exact ((Real.dist_eq _ _).symm.trans_le (hv_lip.dist_le_mul _ _)).trans
      (by rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs, he₀, mul_one]; gcongr)
  have hf_anti : AntitoneOn f (Ici 0) := fun r₁ hr₁ r₂ hr₂ hle ↦
    mul_le_mul_of_nonneg_left (hv_anti _ _ (by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, he₀, mul_one, mul_one,
        max_eq_left hr₁, max_eq_left hr₂, abs_of_nonneg hr₁, abs_of_nonneg hr₂]; exact hle)) hc.le
  have hfR (r : ℝ) (hr : R ≤ r) : f r = 0 := by
    have hge : R ≤ ‖max r 0 • e₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, he₀, mul_one, max_eq_left (hR.le.trans hr),
        abs_of_nonneg (hR.le.trans hr)]; exact hr
    simp [f, hvR _ hge]
  -- Stage 2: Express the critical mass `M` in polar coordinates and verify `f` is normalized.
  have hv_polar : M = (n : ℝ) * (volume.real (ball (0 : E) 1) *
      ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * v (r • e₀) ^ pₙ) := by
    have hv_eq : (fun x : E ↦ v x ^ pₙ) = fun x ↦ (fun r ↦ v (max r 0 • e₀) ^ pₙ) ‖x‖ :=
      funext fun x ↦ by
        dsimp only; rw [max_eq_left (norm_nonneg x), hv_rad x (‖x‖ • e₀) (by simp [norm_smul, he₀])]
    dsimp only [M]; rw [hv_eq, integral_fun_norm_addHaar volume (fun r ↦ v (max r 0 • e₀) ^ pₙ)]
    simp only [nsmul_eq_mul, smul_eq_mul, ← hn_def]; congr 2
    exact setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ by rw [max_eq_left hr.le]
  have hnorm : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * f r ^ pₙ = I₀ := by
    have hcp : c ^ pₙ = roundSphereVolume n / M := by
      rw [← Real.rpow_mul hc0, one_div_mul_cancel hpₙ.ne', Real.rpow_one]
    have hfun : ∀ r ∈ Ioi (0 : ℝ), r ^ (n - 1) * f r ^ pₙ =
        c ^ pₙ * (r ^ (n - 1) * v (r • e₀) ^ pₙ) := fun r (hr : 0 < r) ↦ by
      simp only [f, max_eq_left hr.le, Real.mul_rpow hc.le (hv_nonneg _)]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul, hcp]
    apply mul_left_cancel₀ (by positivity : (n : ℝ) * volume.real (ball (0 : E) 1) ≠ 0)
    calc (n : ℝ) * volume.real (ball (0 : E) 1) *
          (roundSphereVolume n / M * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * v (r • e₀) ^ pₙ)
        = roundSphereVolume n / M * ((n : ℝ) * (volume.real (ball (0 : E) 1) *
            ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * v (r • e₀) ^ pₙ)) := by ring
      _ = roundSphereVolume n := by rw [← hv_polar, div_mul_cancel₀ _ hM_pos.ne']
      _ = (n : ℝ) * volume.real (ball (0 : E) 1) * I₀ := by rw [← hI₀_val, mul_assoc]
  -- Stage 3: Apply the 1D weighted Sobolev inequality to `f` and rescale back to `v`.
  have h1d := mul_integral_bubbleRadialWeight_le_conformalCoefficient_mul_integral hn hf_lip
    (fun r _ ↦ mul_nonneg hc.le (hv_nonneg _)) hf_anti hR hfR hnorm
  have hrad := integral_radial_deriv_sq_le hv_lip hv_supp hv_rad he₀ c
  have hS_pos : 0 < roundSphereVolume n ^ (2 / pₙ) :=
    Real.rpow_pos_of_pos (roundSphereVolume_pos n) _
  have hM_rpow : 0 < M ^ (2 / pₙ) := Real.rpow_pos_of_pos hM_pos _
  have hc2 : c ^ 2 = roundSphereVolume n ^ (2 / pₙ) / M ^ (2 / pₙ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hc0, one_div_mul_eq_div,
      Real.div_rpow (roundSphereVolume_pos n).le hM_pos.le]
  have hcomb : sphereYamabeConstant n * roundSphereVolume n ^ (2 / pₙ) ≤
      (conformalCoefficient n * ∫ x, ‖fderiv ℝ v x‖ ^ 2) *
        (roundSphereVolume n ^ (2 / pₙ) / M ^ (2 / pₙ)) :=
    calc sphereYamabeConstant n * roundSphereVolume n ^ (2 / pₙ)
        = (n : ℝ) * volume.real (ball (0 : E) 1) * ((n : ℝ) * ((n : ℝ) - 1) * I₀) := by
          rw [two_div_criticalExponent, sphereYamabeConstant_mul_roundSphereVolume_rpow, ← hI₀_val]
          ring
      _ ≤ (n : ℝ) * volume.real (ball (0 : E) 1) *
            (conformalCoefficient n * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2) :=
          mul_le_mul_of_nonneg_left h1d (by positivity)
      _ = conformalCoefficient n * ((n : ℝ) * (volume.real (ball (0 : E) 1) *
            ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (deriv f r) ^ 2)) := by ring
      _ ≤ conformalCoefficient n * (c ^ 2 * ∫ x, ‖fderiv ℝ v x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hrad (conformalCoefficient_pos hn).le
      _ = (conformalCoefficient n * ∫ x, ‖fderiv ℝ v x‖ ^ 2) *
            (roundSphereVolume n ^ (2 / pₙ) / M ^ (2 / pₙ)) := by rw [hc2]; ring
  have hcancel : sphereYamabeConstant n * M ^ (2 / pₙ) *
      (roundSphereVolume n ^ (2 / pₙ) / M ^ (2 / pₙ)) =
      sphereYamabeConstant n * roundSphereVolume n ^ (2 / pₙ) := by
    field_simp [hM_rpow.ne']
  refine le_of_mul_le_mul_right ?_ (div_pos hS_pos hM_rpow)
  rwa [hcancel]

private theorem exists_radius_schwarzRearrangement_eq_zero [Nontrivial E] {u : E → ENNReal}
    (hfin0 : volume {y | 0 < u y} ≠ ⊤) :
    ∃ R > 0, ∀ x : E, R ≤ ‖x‖ → schwarzRearrangement volume u x = 0 := by
  have hball1 := volume_real_ball_pos (E := E) one_pos
  set R := max 1 ((volume {y | 0 < u y}).toReal / volume.real (ball (0 : E) 1) + 1)
  refine ⟨R, lt_of_lt_of_le one_pos (le_max_left _ _), fun x hx ↦ ?_⟩
  have hx1 : 1 ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hx2 : (volume {y | 0 < u y}).toReal / volume.real (ball (0 : E) 1) + 1 ≤ ‖x‖ :=
    (le_max_right _ _).trans hx
  have hvol_lt : volume {y | 0 < u y} < volume (ball (0 : E) ‖x‖) := by
    have hpos_r : 0 < ‖x‖ ^ finrank ℝ E := pow_pos (one_pos.trans_le hx1) _
    rw [volume.addHaar_ball_of_pos 0 (one_pos.trans_le hx1),
      ← ENNReal.ofReal_toReal measure_ball_lt_top.ne, ← measureReal_def,
      ← ENNReal.ofReal_mul hpos_r.le, ← ENNReal.ofReal_toReal hfin0,
      ENNReal.ofReal_lt_ofReal_iff (mul_pos hpos_r hball1)]
    have := mul_le_mul_of_nonneg_right hx2 hball1.le
    rw [add_mul, div_mul_cancel₀ _ hball1.ne', one_mul] at this
    exact (by linarith : _ < ‖x‖ * volume.real (ball (0 : E) 1)).trans_le
      (mul_le_mul_of_nonneg_right (le_self_pow₀ hx1 (Module.finrank_pos (R := ℝ)).ne') hball1.le)
  by_contra hne
  exact hvol_lt.not_gt ((lt_schwarzRearrangement_iff volume).mp (pos_iff_ne_zero.mpr hne))

/-- **The sharp Euclidean Sobolev inequality for compactly supported Lipschitz functions.** -/
theorem sphereYamabeConstant_mul_rpow_le_conformalCoefficient_mul_integral_of_lipschitzWith
    (hn : 2 < finrank ℝ E) {K : ℝ≥0} {u : E → ℝ} (hu : LipschitzWith K u)
    (hsupp : HasCompactSupport u) :
    sphereYamabeConstant (finrank ℝ E) *
        (∫ x, |u x| ^ criticalExponent (finrank ℝ E)) ^ (2 / criticalExponent (finrank ℝ E)) ≤
      conformalCoefficient (finrank ℝ E) * ∫ x, ‖fderiv ℝ u x‖ ^ 2 := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  set pₙ := criticalExponent (finrank ℝ E)
  have hpₙ : 0 < pₙ := criticalExponent_pos hn
  -- Stage 1: Form the Schwarz rearrangement `v` and verify its regularity and support.
  let u_enn : E → ENNReal := fun y ↦ ENNReal.ofReal ‖u y‖
  let v_enn : E → ENNReal := schwarzRearrangement volume u_enn
  let v : E → ℝ := fun z ↦ (v_enn z).toReal
  have hu_norm : LipschitzWith K (fun y ↦ ‖u y‖) := by
    simpa only [one_mul, Function.comp_def] using
      (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).comp hu
  have hv_lip : LipschitzWith K v := lipschitzWith_toReal_schwarzRearrangement volume hu_norm
  have hsub_supp : {y | 0 < u_enn y} ⊆ tsupport u := fun y hy ↦
    subset_tsupport u (mem_support.2 fun h0 ↦ by simp [u_enn, h0] at hy)
  have hfin0 : volume {y | 0 < u_enn y} ≠ ⊤ :=
    ((measure_mono hsub_supp).trans_lt hsupp.measure_lt_top).ne
  have hfin : ∀ t, 0 < t → volume {y | t < ‖u y‖} ≠ ⊤ := fun t ht ↦
    ((measure_mono fun _ hy ↦ hsub_supp (ENNReal.ofReal_pos.mpr (ht.trans hy))).trans_lt
      hsupp.measure_lt_top).ne
  have hv_ne_top : ∀ x, v_enn x ≠ ⊤ :=
    schwarzRearrangement_ne_top volume (K := K) (fun x y ↦
      (ENNReal.ofReal_le_ofReal (hu_norm.le_add_mul x y)).trans (by
        rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
        exact ENNReal.ofReal_add_le)) ENNReal.zero_ne_top hfin0
  have hv_anti : ∀ x y, ‖x‖ ≤ ‖y‖ → v y ≤ v x := fun x y hxy ↦
    ENNReal.toReal_mono (hv_ne_top x) (schwarzRearrangement_le_of_norm_le volume u_enn hxy)
  obtain ⟨R, hR, hvR_enn⟩ := exists_radius_schwarzRearrangement_eq_zero hfin0
  have hvR : ∀ x, R ≤ ‖x‖ → v x = 0 := fun x hx ↦ by simp [v, v_enn, hvR_enn x hx]
  have hv_supp : HasCompactSupport v :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) R) fun x hx ↦
      mem_closedBall_zero_iff.2 (not_lt.1 fun hlt ↦ hx (hvR x hlt.le))
  -- Stage 2: Equimeasurability of the critical mass and Pólya–Szegő gradient decay.
  have hmass_eq : (∫ x, v x ^ pₙ) = ∫ x, |u x| ^ pₙ := by
    rw [← ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ Real.rpow_nonneg ENNReal.toReal_nonneg _),
      ← ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)]
    congr 1
    rw [ofReal_integral_eq_lintegral_ofReal ((hv_lip.continuous.rpow_const fun _ ↦ .inr hpₙ.le
        ).integrable_of_hasCompactSupport (hv_supp.rpow_const hpₙ.ne'))
        (.of_forall fun _ ↦ Real.rpow_nonneg ENNReal.toReal_nonneg _),
      ofReal_integral_eq_lintegral_ofReal ((hu.continuous.abs.rpow_const fun _ ↦ .inr hpₙ.le
        ).integrable_of_hasCompactSupport (hsupp.abs.rpow_const hpₙ.ne'))
        (.of_forall fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)]
    refine (lintegral_congr fun x ↦ ?_).trans ((lintegral_rpow_schwarzRearrangement volume
      hu_norm.continuous.aemeasurable.ennreal_ofReal hpₙ).trans (lintegral_congr fun x ↦ ?_))
    · rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hpₙ.le,
        ENNReal.ofReal_toReal (hv_ne_top x)]
    · rw [← Real.norm_eq_abs, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpₙ.le]
  have hps : ∫ x, ‖fderiv ℝ v x‖ ^ 2 ≤ ∫ x, ‖fderiv ℝ u x‖ ^ 2 := by
    simpa only [Real.rpow_two] using
      hu.integral_norm_fderiv_toReal_schwarzRearrangement_norm_rpow_le hfin one_le_two
        (by simpa only [Real.rpow_two] using integrable_norm_fderiv_sq_of_lipschitzWith hu hsupp)
  -- Stage 3: Apply the radial sharp Sobolev inequality to `v`.
  rw [← hmass_eq]
  exact (radial_sharp_sobolev hn hv_lip (fun _ ↦ ENNReal.toReal_nonneg) hv_anti hR hvR).trans
    (mul_le_mul_of_nonneg_left hps (conformalCoefficient_pos hn).le)

/-- **The sharp Euclidean Sobolev inequality for compactly supported `C¹` functions.** -/
theorem sphereYamabeConstant_mul_rpow_le_conformalCoefficient_mul_integral
    (hn : 2 < finrank ℝ E) {u : E → ℝ} (hu : ContDiff ℝ 1 u) (hsupp : HasCompactSupport u) :
    sphereYamabeConstant (finrank ℝ E) *
        (∫ x, |u x| ^ criticalExponent (finrank ℝ E)) ^ (2 / criticalExponent (finrank ℝ E)) ≤
      conformalCoefficient (finrank ℝ E) * ∫ x, ‖fderiv ℝ u x‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := hsupp.exists_bound_iteratedFDeriv_of_contDiff (n := 1) hu
  refine sphereYamabeConstant_mul_rpow_le_conformalCoefficient_mul_integral_of_lipschitzWith hn
    (K := C.toNNReal)
    (lipschitzWith_of_nnNorm_fderiv_le (hu.differentiable one_ne_zero) fun x ↦ ?_) hsupp
  rw [← NNReal.coe_le_coe, coe_nnNorm, Real.coe_toNNReal C hC0, ← norm_iteratedFDeriv_one]
  exact hC 1 le_rfl x

private theorem setIntegral_top_opens (F : E → ℝ) : (∫ x in (⊤ : Opens E), F x) = ∫ x, F x := by
  rw [Opens.coe_top, Measure.restrict_univ]

private theorem norm_lp_criticalExponent_sq
    [Fact (1 ≤ ENNReal.ofReal (criticalExponent (finrank ℝ E)))] (hn : 2 < finrank ℝ E)
    (w : Lp ℝ (ENNReal.ofReal (criticalExponent (finrank ℝ E)))
      ((volume : Measure E).restrict (⊤ : Opens E))) :
    ‖w‖ ^ 2 =
      (∫ x, |w x| ^ criticalExponent (finrank ℝ E)) ^ (2 / criticalExponent (finrank ℝ E)) := by
  have hpₙ : 0 < criticalExponent (finrank ℝ E) := criticalExponent_pos hn
  have hLp := Lp.integral_norm_rpow_eq_norm_rpow
    (ENNReal.ofReal_pos.mpr hpₙ).ne' ENNReal.ofReal_ne_top w
  rw [ENNReal.toReal_ofReal hpₙ.le, setIntegral_top_opens] at hLp
  simp_rw [Real.norm_eq_abs] at hLp
  rw [hLp, ← Real.rpow_mul (norm_nonneg _), mul_div_cancel₀ _ hpₙ.ne', Real.rpow_two]

/-- **The sharp Euclidean Sobolev inequality on `D^{1,2}_0(E)`**, in norm form. -/
theorem sphereYamabeConstant_mul_norm_sobolevEmbeddingL_sq_le_conformalCoefficient_mul_norm_sq
    (hn : 2 < finrank ℝ E) (u : D1p0 volume (⊤ : Opens E) 2) :
    sphereYamabeConstant (finrank ℝ E) *
        ‖D1p0.sobolevEmbeddingL (inv_ofReal_criticalExponent_add_inv_eq_inv hn) u‖ ^ 2 ≤
      conformalCoefficient (finrank ℝ E) * ‖u‖ ^ 2 := by
  set hexp := inv_ofReal_criticalExponent_add_inv_eq_inv hn
  set pₙ := criticalExponent (finrank ℝ E)
  set pstar := ENNReal.ofReal pₙ
  have : Fact (1 ≤ pstar) := ⟨one_le_of_inv_add_eq_inv hexp⟩
  refine (D1p0.denseRange_ofTestFunctionₗ (mu := volume) (Omega := (⊤ : Opens E))
    (p := 2)).induction_on u (isClosed_le
      (continuous_const.mul ((D1p0.sobolevEmbeddingL hexp).continuous.norm.pow 2))
      (continuous_const.mul (continuous_norm.pow 2))) fun φ ↦ ?_
  rw [D1p0.sobolevEmbeddingL_ofTestFunctionₗ ENNReal.ofReal_ne_top hexp φ,
    D1p0.norm_ofTestFunctionₗ, norm_lp_criticalExponent_sq hn]
  have hint_eq : (∫ x, |testFunctionLp (mu := volume) pstar φ x| ^ pₙ) =
      ∫ x, |(φ : E → ℝ) x| ^ pₙ := by
    rw [← setIntegral_top_opens, ← setIntegral_top_opens (fun x ↦ |(φ : E → ℝ) x| ^ pₙ)]
    exact integral_congr_ae ((testFunctionLp_apply_ae (mu := volume) pstar φ).mono fun _ hx ↦
      congrArg (|·| ^ pₙ) hx)
  have hmem : MemLp (fderiv ℝ (φ : E → ℝ)) 2 volume :=
    (φ.contDiff.continuous_fderiv (by simp)).memLp_of_hasCompactSupport
      (φ.hasCompactSupport.fderiv ℝ)
  rw [hint_eq, hmem.eLpNorm_two_eq_ofReal_sqrt_integral,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _)]
  exact sphereYamabeConstant_mul_rpow_le_conformalCoefficient_mul_integral hn
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport

/-- **The sharp Euclidean Sobolev inequality on `D^{1,2}_0(E)`**, in integral form. -/
theorem sphereYamabeConstant_mul_rpow_sobolevEmbeddingL_le_conformalCoefficient_mul_integral
    (hn : 2 < finrank ℝ E) (u : D1p0 volume (⊤ : Opens E) 2) :
    sphereYamabeConstant (finrank ℝ E) *
        (∫ x, |D1p0.sobolevEmbeddingL (inv_ofReal_criticalExponent_add_inv_eq_inv hn) u x| ^
            criticalExponent (finrank ℝ E)) ^ (2 / criticalExponent (finrank ℝ E)) ≤
      conformalCoefficient (finrank ℝ E) * ∫ x, ‖u.val x‖ ^ 2 := by
  set hexp := inv_ofReal_criticalExponent_add_inv_eq_inv hn
  have : Fact (1 ≤ ENNReal.ofReal (criticalExponent (finrank ℝ E))) :=
    ⟨one_le_of_inv_add_eq_inv hexp⟩
  have hsq := Lp.integral_norm_sq_eq_norm_sq u.val
  rw [setIntegral_top_opens, Submodule.norm_coe] at hsq
  rw [← norm_lp_criticalExponent_sq hn, hsq]
  exact sphereYamabeConstant_mul_norm_sobolevEmbeddingL_sq_le_conformalCoefficient_mul_norm_sq hn u

/-- **Sharpness on `D^{1,2}_0(E)`**: `Y(Sⁿ)` is the least value of the Euclidean Sobolev quotient
on nonzero elements of `D1p0 volume ⊤ 2`, attained by the Aubin–Talenti bubbles. -/
theorem isLeast_image_conformalCoefficient_mul_norm_sq_div (hn : 2 < finrank ℝ E) :
    IsLeast
      ((fun u : D1p0 volume (⊤ : Opens E) 2 ↦
          conformalCoefficient (finrank ℝ E) * ‖u‖ ^ 2 /
            ‖D1p0.sobolevEmbeddingL (inv_ofReal_criticalExponent_add_inv_eq_inv hn) u‖ ^ 2) ''
        {u | u ≠ 0})
      (sphereYamabeConstant (finrank ℝ E)) := by
  set hexp := inv_ofReal_criticalExponent_add_inv_eq_inv hn
  set pₙ := criticalExponent (finrank ℝ E)
  have : Fact (1 ≤ ENNReal.ofReal pₙ) := ⟨one_le_of_inv_add_eq_inv hexp⟩
  constructor
  · obtain ⟨u, hu_fun, hu_grad⟩ := exists_sobolevEmbeddingL_ae_eq_bubble volume hn one_pos (0 : E)
    have hu_norm_pow : ‖D1p0.sobolevEmbeddingL hexp u‖ ^ 2 =
        (∫ x, bubble 1 (0 : E) x ^ pₙ) ^ (2 / pₙ) := by
      rw [norm_lp_criticalExponent_sq hn]; congr 1
      exact integral_congr_ae (hu_fun.mono fun x hx ↦ by
        dsimp only; rw [hx, abs_of_pos (bubble_pos one_pos 0 x)])
    have hmass_pos : 0 < (∫ x, bubble 1 (0 : E) x ^ pₙ) ^ (2 / pₙ) := by
      rw [integral_bubble_rpow_criticalExponent_eq_roundSphereVolume (by omega) hn.ne' one_pos 0]
      exact Real.rpow_pos_of_pos (roundSphereVolume_pos _) _
    have hu_ne : u ≠ 0 := by rintro rfl; simp [map_zero] at hu_norm_pow; linarith
    have hu_grad_sq : ‖u‖ ^ 2 = ∫ x, ‖fderiv ℝ (bubble 1 (0 : E)) x‖ ^ 2 := by
      have hsq := Lp.integral_norm_sq_eq_norm_sq u.val
      rw [setIntegral_top_opens, Submodule.norm_coe] at hsq
      exact hsq.symm.trans (integral_congr_ae (hu_grad.mono fun x hx ↦ by
        dsimp only; rw [hx, norm_gradient_eq_norm_fderiv]))
    refine ⟨u, hu_ne, ?_⟩
    dsimp only
    rw [hu_grad_sq, hu_norm_pow,
      conformalCoefficient_mul_integral_norm_fderiv_bubble_sq_eq_sphereYamabeConstant
        hn one_pos (0 : E), mul_div_cancel_right₀ _ hmass_pos.ne']
  · rintro _ ⟨u, hu_ne : u ≠ 0, rfl⟩
    have hemb_ne : D1p0.sobolevEmbeddingL hexp u ≠ 0 := fun h0 ↦
      hu_ne (D1p0.sobolevEmbeddingL_injective ENNReal.ofReal_ne_top hexp
        (h0.trans (map_zero _).symm))
    exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hemb_ne))).2
      (sphereYamabeConstant_mul_norm_sobolevEmbeddingL_sq_le_conformalCoefficient_mul_norm_sq hn u)

/-- **Sharpness on `C_c^∞(E)`**: `Y(Sⁿ)` is the greatest lower bound of the Euclidean Sobolev
quotient on smooth compactly supported functions with positive critical mass. -/
theorem isGLB_image_conformalCoefficient_mul_integral_div (hn : 2 < finrank ℝ E) :
    IsGLB
      ((fun u : E → ℝ ↦
          conformalCoefficient (finrank ℝ E) * (∫ x, ‖fderiv ℝ u x‖ ^ 2) /
            (∫ x, |u x| ^ criticalExponent (finrank ℝ E)) ^
              (2 / criticalExponent (finrank ℝ E))) ''
        {u | ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
          0 < ∫ x, |u x| ^ criticalExponent (finrank ℝ E)})
      (sphereYamabeConstant (finrank ℝ E)) := by
  constructor
  · rintro _ ⟨u, ⟨hu_smooth, hu_supp, hu_pos⟩, rfl⟩
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hu_pos _)).2
      (sphereYamabeConstant_mul_rpow_le_conformalCoefficient_mul_integral hn
        (hu_smooth.of_le (by simp)) hu_supp)
  · intro c hc
    by_contra! hlt
    obtain ⟨u, hu_smooth, hu_supp, _, _, hu_pos, hu_lt⟩ :=
      exists_contDiff_hasCompactSupport_sobolev_quotient_lt (E := E) hn isOpen_univ
        ⟨0, mem_univ 0⟩ (sub_pos.mpr hlt)
    linarith [hc ⟨u, ⟨hu_smooth, hu_supp, hu_pos⟩, rfl⟩]

end TauCeti.Yamabe

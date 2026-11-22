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
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Analysis.Calculus.FDeriv.Integrable
import TauCeti.Analysis.PDE.Yamabe.Bubble.Cutoff
import TauCeti.Analysis.PDE.Yamabe.Bubble.Homogeneous
import TauCeti.Analysis.PDE.Yamabe.WeightedSobolev
import TauCeti.MeasureTheory.Constructions.HaarToSphere
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Function.SchwarzRearrangement.PolyaSzego
import TauCeti.MeasureTheory.Measure.OpenPos

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
  have hI₀_val := mul_integral_bubbleRadialWeight_eq_roundSphereVolume (E := E) (by omega) hn.ne'
  set I₀ := ∫ s in Ioi (0 : ℝ), bubbleRadialWeight n s
  have hball := Metric.measureReal_ball_pos (volume : Measure E) (0 : E) one_pos
  set c := (roundSphereVolume n / M) ^ (1 / pₙ)
  have hc0 : 0 ≤ roundSphereVolume n / M := div_nonneg (roundSphereVolume_pos n).le hM_pos.le
  have hc : 0 < c := Real.rpow_pos_of_pos (div_pos (roundSphereVolume_pos n) hM_pos) _
  let f : ℝ → ℝ := fun r ↦ c * v (max r 0 • e₀)
  have hf_lip : LipschitzWith (‖c‖₊ * K) f := by
    simpa only [f, Function.comp_def, smul_eq_mul, id_eq, LinearIsometry.toSpanSingleton_apply,
      mul_one] using (lipschitzWith_smul c).comp ((hv_lip.comp
        (LinearIsometry.toSpanSingleton ℝ E he₀).isometry.lipschitzWith).comp
          (LipschitzWith.id.max_const (0 : ℝ)))
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
  have hrad := integral_radial_deriv_sq_le volume hv_lip hv_supp hv_rad he₀ c
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
  have hfin0_norm : volume {y | (0 : ℝ) < ‖u y‖} ≠ ⊤ := by
    convert hfin0 using 2
    ext y
    exact ENNReal.ofReal_pos.symm
  have hfin : ∀ t, 0 < t → volume {y | t < ‖u y‖} ≠ ⊤ := fun t ht ↦
    ((measure_mono fun _ hy ↦ hsub_supp (ENNReal.ofReal_pos.mpr (ht.trans hy))).trans_lt
      hsupp.measure_lt_top).ne
  have hv_ne_top : ∀ x, v_enn x ≠ ⊤ :=
    schwarzRearrangement_ofReal_ne_top volume hu_norm le_rfl hfin0_norm
  have hv_anti : ∀ x y, ‖x‖ ≤ ‖y‖ → v y ≤ v x := fun x y hxy ↦
    ENNReal.toReal_mono (hv_ne_top x) (schwarzRearrangement_le_of_norm_le volume u_enn hxy)
  obtain ⟨R, hR, hvR_enn⟩ := exists_radius_schwarzRearrangement_eq_zero volume hfin0
  have hvR : ∀ x, R ≤ ‖x‖ → v x = 0 := fun x hx ↦ by simp [v, v_enn, hvR_enn x hx]
  have hv_supp : HasCompactSupport v :=
    hasCompactSupport_toReal_schwarzRearrangement volume hfin0_norm
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
        (by simpa only [Real.rpow_two] using
          integrable_norm_fderiv_sq_of_lipschitzWith (𝕜 := ℝ) (μ := volume) hu hsupp)
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
  obtain ⟨K, hK⟩ := hu.lipschitzWith_of_hasCompactSupport hsupp one_ne_zero
  exact sphereYamabeConstant_mul_rpow_le_conformalCoefficient_mul_integral_of_lipschitzWith hn
    hK hsupp

private theorem norm_lp_criticalExponent_sq (hn : 2 < finrank ℝ E)
    (w : Lp ℝ (ENNReal.ofReal (criticalExponent (finrank ℝ E)))
      ((volume : Measure E).restrict (⊤ : Opens E))) :
    ‖w‖ ^ 2 =
      (∫ x, |w x| ^ criticalExponent (finrank ℝ E)) ^ (2 / criticalExponent (finrank ℝ E)) := by
  have hpₙ : 0 < criticalExponent (finrank ℝ E) := criticalExponent_pos hn
  have hLp := Lp.integral_norm_rpow_eq_norm_rpow
    (ENNReal.ofReal_pos.mpr hpₙ).ne' ENNReal.ofReal_ne_top w
  simp only [ENNReal.toReal_ofReal hpₙ.le, Opens.coe_top, setIntegral_univ, Real.norm_eq_abs] at hLp
  rw [hLp, ← Real.rpow_mul (Lp.norm_def w ▸ ENNReal.toReal_nonneg),
    mul_div_cancel₀ _ hpₙ.ne', Real.rpow_two]

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
    rw [← setIntegral_univ (f := fun x ↦ |testFunctionLp (mu := volume) pstar φ x| ^ pₙ),
      ← setIntegral_univ (f := fun x ↦ |(φ : E → ℝ) x| ^ pₙ), ← Opens.coe_top]
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
  simp only [Opens.coe_top, setIntegral_univ, Submodule.norm_coe] at hsq
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
      simp only [Opens.coe_top, setIntegral_univ, Submodule.norm_coe] at hsq
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

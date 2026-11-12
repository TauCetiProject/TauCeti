/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.H1
import Mathlib.Analysis.Convex.Continuous
import TauCeti.Geometry.Manifold.Riemannian.Trudinger
import TauCeti.MeasureTheory.Function.Lp.IntegralFunctional

/-!
# Exponential integrability on the completed Sobolev space of a closed surface

Trudinger's inequality extends from smooth functions to the Hilbert space `SobolevH1 I M`:
there are `β > 0` and `C` such that `∫ exp (β w²) dV ≤ C` on its closed unit ball.
Consequently, for every `w ∈ H¹(M)` and every real `t`, `exp (t w)` is integrable.
These statements concern the `L²` value of `w`, so they are independent of its representative.

This makes the exponential potential in the Liouville energy finite on `H¹(M)`, and supplies
bounds on the nonlinear term on bounded sets. The integral of `exp (t w)` is convex and norm
continuous on `H¹(M)`: Trudinger bounds it locally, and local boundedness of a convex
function implies continuity. The extension uses density of smooth functions
and lower semicontinuity of integral functionals on `L²`. No regularity of weak solutions is
assumed.

## References

* N. S. Trudinger, *On imbeddings into Orlicz spaces and some applications*, J. Math. Mech. 17
  (1967), 473–483.
* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), Chapter 2.
-/

public section

open Bundle MeasureTheory Set
open scoped ContDiff Manifold ENNReal NNReal Topology

noncomputable section

namespace TauCeti.Manifold.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private theorem exists_lintegral_exp_normalized_sq_le (hE : Module.finrank ℝ E = 2) :
    ∃ β > 0, ∃ C : ℝ≥0, ∀ w : SobolevH1 I M,
      ∫⁻ x, ENNReal.ofReal (Real.exp (β * ((1 + ‖w‖)⁻¹ * toLp w x) ^ 2))
        ∂riemannianVolume I M ≤ C := by
  obtain ⟨b, hb, C, hC⟩ := exists_lintegral_exp_mul_sq_le_of_finrank_eq_two (I := I) (M := M) hE
  refine ⟨b / 4, by positivity, C, fun w ↦ ?_⟩
  -- Normalize continuously before applying density, so the sublevel set is closed even at zero.
  have hcont : Continuous (fun w : SobolevH1 I M ↦ (1 + ‖w‖)⁻¹ • toLp w) :=
    (continuous_const.add continuous_norm).inv₀
      (fun w ↦ (add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg w)).ne') |>.smul toLp.continuous
  have hlsc := (TauCeti.lowerSemicontinuous_lintegral_ofReal_comp_Lp
    (μ := riemannianVolume I M) (p := 2) Measure.AbsolutelyContinuous.rfl
    (Φ := fun t : ℝ ↦ Real.exp (b / 4 * t ^ 2)) (by fun_prop)).comp hcont
  have heq (w : SobolevH1 I M) :
      (∫⁻ x, ENNReal.ofReal (Real.exp (b / 4 * (((1 + ‖w‖)⁻¹ • toLp w) x) ^ 2))
        ∂riemannianVolume I M) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (b / 4 * ((1 + ‖w‖)⁻¹ * toLp w x) ^ 2))
        ∂riemannianVolume I M := by
    apply lintegral_congr_ae
    filter_upwards [Lp.coeFn_smul (1 + ‖w‖)⁻¹ (toLp w)] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul]
  have hclosed := hlsc.isClosed_preimage (C : ℝ≥0∞)
  simp only [Function.comp_def, heq] at hclosed
  refine induction_on w hclosed fun u ↦ ?_
  let c : ℝ := (2 * (1 + ‖ofSmooth u‖))⁻¹
  let v : C^∞⟮I, M; ℝ⟯ := c • u
  have hc : 0 < c := by dsimp [c]; positivity
  have hv : ‖ofSmooth v‖ ≤ 1 / 2 := by
    rw [map_smul, norm_smul, Real.norm_of_nonneg hc.le]
    dsimp [c]
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith [norm_nonneg (ofSmooth u)]
  have hval : eLpNorm v 2 (riemannianVolume I M) ≤ ENNReal.ofReal ‖ofSmooth v‖ := by
    rw [← eLpNorm_congr_ae (toLp_ofSmooth_ae_eq v), ← Lp.eNorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_toLp_le _)
  have hgrad : eLpNorm (fun x ↦ ‖mgradient I v x‖) 2 (riemannianVolume I M) ≤
      ENNReal.ofReal ‖ofSmooth v‖ := by
    let G : C(M, ℝ) := ⟨_, continuous_norm_mgradient (v.contMDiff.of_le (by simp))⟩
    have heq := eLpNorm_congr_ae (p := 2) (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ)
      (riemannianVolume I M) G)
    simp only [G, ContinuousMap.coe_mk] at heq
    rw [← heq, ← Lp.eNorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_toLp_norm_mgradient_le v)
  have hnorm : eLpNorm (fun x ↦ ‖mgradient I v x‖) 2 (riemannianVolume I M) +
      eLpNorm v 2 (riemannianVolume I M) ≤ 1 := by
    calc _ ≤ ENNReal.ofReal ‖ofSmooth v‖ + ENNReal.ofReal ‖ofSmooth v‖ := add_le_add hgrad hval
      _ = ENNReal.ofReal (‖ofSmooth v‖ + ‖ofSmooth v‖) :=
        (ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)).symm
      _ ≤ 1 := by exact_mod_cast (by linarith : ‖ofSmooth v‖ + ‖ofSmooth v‖ ≤ 1)
  have h := hC v (v.contMDiff.of_le (by simp)) hnorm
  refine (le_of_eq (lintegral_congr_ae ?_)).trans h
  filter_upwards [toLp_ofSmooth_ae_eq u] with x hx
  rw [hx]
  congr 2
  simp only [v, ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul]
  dsimp [c]
  rw [mul_inv_rev]
  ring

/-- **Trudinger's inequality on `H¹`.** On a closed surface with a continuous Riemannian metric,
there are `β > 0` and `C` such that `∫ exp (β w²) dV ≤ C` on the closed unit ball of `H¹(M)`. -/
theorem exists_lintegral_exp_mul_sq_le (hE : Module.finrank ℝ E = 2) :
    ∃ β > 0, ∃ C : ℝ≥0, ∀ w : SobolevH1 I M, ‖w‖ ≤ 1 →
      ∫⁻ x, ENNReal.ofReal (Real.exp (β * toLp w x ^ 2)) ∂riemannianVolume I M ≤ C := by
  obtain ⟨b, hb, C, hC⟩ := exists_lintegral_exp_normalized_sq_le (I := I) (M := M) hE
  refine ⟨b / 4, by positivity, C, fun w hw ↦ (lintegral_mono fun x ↦ ?_).trans (hC w)⟩
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hinv : 1 / 2 ≤ (1 + ‖w‖)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : 0 < 1 + ‖w‖)
      (by linarith : 1 + ‖w‖ ≤ 2)
  calc b / 4 * toLp w x ^ 2 = b * ((1 / 2 : ℝ) ^ 2 * toLp w x ^ 2) := by ring
    _ ≤ b * ((1 + ‖w‖)⁻¹ ^ 2 * toLp w x ^ 2) := by gcongr
    _ = _ := by ring

/-- Exponential moments of `H¹` functions on a closed surface admit a bound depending only on
`t` and the `H¹` norm. In particular the bound is uniform on bounded subsets of `H¹(M)`. -/
theorem exists_lintegral_exp_mul_le (hE : Module.finrank ℝ E = 2) :
    ∃ A > 0, ∃ C : ℝ≥0, ∀ (w : SobolevH1 I M) (t : ℝ),
      ∫⁻ x, ENNReal.ofReal (Real.exp (t * toLp w x)) ∂riemannianVolume I M ≤
        C * ENNReal.ofReal (Real.exp (A * t ^ 2 * (1 + ‖w‖) ^ 2)) := by
  obtain ⟨b, hb, C, hC⟩ := exists_lintegral_exp_normalized_sq_le (I := I) (M := M) hE
  refine ⟨(4 * b)⁻¹, by positivity, C, fun w t ↦ ?_⟩
  have hn : 0 < 1 + ‖w‖ := by positivity
  have hpoint (x : M) : t * toLp w x ≤
      (4 * b)⁻¹ * t ^ 2 * (1 + ‖w‖) ^ 2 + b * ((1 + ‖w‖)⁻¹ * toLp w x) ^ 2 := by
    have hsq := sq_nonneg (2 * b * ((1 + ‖w‖)⁻¹ * toLp w x) - t * (1 + ‖w‖))
    have hcancel : (1 + ‖w‖) * ((1 + ‖w‖)⁻¹ * toLp w x) = toLp w x := by
      rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
    have hdiv : 4 * b * ((4 * b)⁻¹ * t ^ 2 * (1 + ‖w‖) ^ 2) =
        t ^ 2 * (1 + ‖w‖) ^ 2 := by field_simp
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 4 * b)).mp
    rw [mul_add, hdiv]
    calc 4 * b * (t * toLp w x) =
          4 * b * (t * (1 + ‖w‖) * ((1 + ‖w‖)⁻¹ * toLp w x)) := by
            rw [mul_assoc t, hcancel]
      _ ≤ _ := by nlinarith only [hsq]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal
        (Real.exp ((4 * b)⁻¹ * t ^ 2 * (1 + ‖w‖) ^ 2) *
          Real.exp (b * ((1 + ‖w‖)⁻¹ * toLp w x) ^ 2)) ∂riemannianVolume I M := by
      apply lintegral_mono
      intro x
      simp only [← Real.exp_add]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hpoint x))
    _ = ENNReal.ofReal (Real.exp ((4 * b)⁻¹ * t ^ 2 * (1 + ‖w‖) ^ 2)) *
        ∫⁻ x, ENNReal.ofReal (Real.exp (b * ((1 + ‖w‖)⁻¹ * toLp w x) ^ 2))
          ∂riemannianVolume I M := by
      simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by rw [mul_comm (C : ℝ≥0∞)]; gcongr; exact hC w

/-- Every exponential `exp (t w)` of an `H¹` function on a closed surface is integrable. -/
theorem integrable_exp_mul (hE : Module.finrank ℝ E = 2) (w : SobolevH1 I M) (t : ℝ) :
    Integrable (fun x ↦ Real.exp (t * toLp w x)) (riemannianVolume I M) := by
  obtain ⟨A, -, C, hC⟩ := exists_lintegral_exp_mul_le (I := I) (M := M) hE
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le)).mp
  exact ne_top_of_le_ne_top (by finiteness) (hC w t)

/-- The exponential of an `H¹` function on a closed surface belongs to every finite `Lᵖ` space.
This applies in particular to the nonlinear term `exp (2w)` of the curvature equation. -/
theorem memLp_exp_mul (hE : Module.finrank ℝ E = 2) (w : SobolevH1 I M) (t : ℝ)
    {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (fun x ↦ Real.exp (t * toLp w x)) p (riemannianVolume I M) := by
  have hm : AEStronglyMeasurable (fun x ↦ Real.exp (t * toLp w x)) (riemannianVolume I M) :=
    by fun_prop
  by_cases hp0 : p = 0
  · exact hp0 ▸ memLp_zero_iff_aestronglyMeasurable.mpr hm
  apply (integrable_norm_rpow_iff hm hp0 hp).mp
  simpa only [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_mul, mul_assoc,
    mul_comm _ p.toReal] using integrable_exp_mul hE w (p.toReal * t)

/-- The exponential potential is convex on the Sobolev space of a closed surface. -/
theorem convexOn_integral_exp_mul (hE : Module.finrank ℝ E = 2) (t : ℝ) :
    ConvexOn ℝ univ (fun w : SobolevH1 I M ↦
      ∫ x, Real.exp (t * toLp w x) ∂riemannianVolume I M) := by
  refine ⟨convex_univ, fun u _ v _ a b ha hb hab ↦ ?_⟩
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_exp_mul hE u t).const_mul a)
      ((integrable_exp_mul hE v t).const_mul b)]
  refine integral_mono_ae (integrable_exp_mul hE _ t)
    (((integrable_exp_mul hE u t).const_mul a).add
      ((integrable_exp_mul hE v t).const_mul b)) ?_
  simp only [map_add, map_smul]
  filter_upwards [Lp.coeFn_add (a • toLp u) (b • toLp v),
    Lp.coeFn_smul a (toLp u), Lp.coeFn_smul b (toLp v)] with x hx hu hv
  simp only [hx, hu, hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  convert convexOn_exp.2 (mem_univ (t * toLp u x)) (mem_univ (t * toLp v x)) ha hb hab using 1
  congr 1
  ring

/-- The exponential potential is norm continuous on the Sobolev space of a closed surface. -/
theorem continuous_integral_exp_mul (hE : Module.finrank ℝ E = 2) (t : ℝ) :
    Continuous (fun w : SobolevH1 I M ↦
      ∫ x, Real.exp (t * toLp w x) ∂riemannianVolume I M) := by
  obtain ⟨A, hA, C, hC⟩ := exists_lintegral_exp_mul_le (I := I) (M := M) hE
  have hbound : ∀ w : SobolevH1 I M, ‖w‖ < 1 →
      ∫ x, Real.exp (t * toLp w x) ∂riemannianVolume I M ≤
        C * Real.exp (A * t ^ 2 * (1 + 1) ^ 2) := by
    intro w hw
    have h := hC w t
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul hE w t)
      (Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le)] at h
    have h' := ENNReal.toReal_mono (by finiteness) h
    simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal,
      (Real.exp_pos _).le, integral_nonneg (fun _ ↦ (Real.exp_pos _).le)] at h'
    refine h'.trans ?_
    gcongr
  have hc := (convexOn_integral_exp_mul (I := I) (M := M) hE t).continuousOn_tfae
    isOpen_univ univ_nonempty
  apply continuousOn_univ.mp
  apply (hc.out 4 2).mp
  refine ⟨0, mem_univ _, C * Real.exp (A * t ^ 2 * (1 + 1) ^ 2), ?_⟩
  simp only [Filter.eventually_map]
  filter_upwards [Metric.ball_mem_nhds (0 : SobolevH1 I M) zero_lt_one] with w hw
  exact hbound w (by simpa using hw)

end TauCeti.Manifold.SobolevH1

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.LiouvilleEnergy.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Trudinger
import Mathlib.Analysis.InnerProductSpace.Convex
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.LocallyConvex.WeakSpace
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Geometry.Manifold.Riemannian.Poisson
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Minimizing the Liouville energy on a closed surface

The Liouville energy extends to the Hilbert completion `SobolevH1 I M` as
`J(w) = D(w,w)/2 + ⟪K,w⟫L² + (∫ exp(2w) dV)/2`.
On a closed surface Trudinger's inequality makes the exponential term finite and locally
bounded. Its convexity then gives norm continuity. Consequently the energy is continuous,
convex and weakly lower semicontinuous. The smooth coercivity estimate extends by density;
when `∫ K dV < 0`, bounded energy implies bounded `H¹` norm. Weak compactness of Hilbert
balls therefore gives a minimizer on the completed space.

This is a variational existence statement, without a regularity assertion: a smooth solution
of the curvature equation requires the weak Euler–Lagrange equation and elliptic regularity
in addition. The direct-method argument follows the existing formalization of
`TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`.

## References

* M. S. Berger, *Riemannian structures of prescribed Gaussian curvature for compact
  2-manifolds*, J. Differential Geom. 5 (1971), 325–332.
* J. L. Kazdan and F. W. Warner, *Curvature functions for compact 2-manifolds*, Ann. of Math. 99
  (1974), 14–47, §3.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Springer (2011), Corollary 3.9 and Chapter 8.
-/

public section

open Bundle MeasureTheory Set TopologicalSpace
open scoped ContDiff Manifold InnerProductSpace Topology

noncomputable section

namespace TauCeti.Manifold.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The Liouville energy on the completed Sobolev space. On a closed surface the exponential
term is integrable by Trudinger's inequality. -/
def liouvilleEnergy (w : SobolevH1 I M) (K : Lp ℝ 2 (riemannianVolume I M)) : ℝ :=
  dirichletForm w w / 2 + ⟪K, toLp w⟫_ℝ +
    (∫ x, Real.exp (2 * toLp w x) ∂riemannianVolume I M) / 2

/-- The three terms of the Sobolev Liouville energy. -/
theorem liouvilleEnergy_def (w : SobolevH1 I M) (K : Lp ℝ 2 (riemannianVolume I M)) :
    w.liouvilleEnergy K = dirichletForm w w / 2 + ⟪K, toLp w⟫_ℝ +
      (∫ x, Real.exp (2 * toLp w x) ∂riemannianVolume I M) / 2 :=
  (rfl)

/-- The zero function has only the constant exponential contribution to the energy. -/
@[simp]
theorem liouvilleEnergy_zero (K : Lp ℝ 2 (riemannianVolume I M)) :
    (0 : SobolevH1 I M).liouvilleEnergy K = (riemannianVolume I M).real univ / 2 := by
  have hzero : (∫ x, Real.exp (2 * (0 : Lp ℝ 2 (riemannianVolume I M)) x)
      ∂riemannianVolume I M) = (riemannianVolume I M).real univ := by
    rw [integral_congr_ae ((Lp.coeFn_zero ℝ 2 (riemannianVolume I M)).mono
      fun x hx ↦ congrArg (fun t ↦ Real.exp (2 * t)) hx)]
    simp
  simpa only [liouvilleEnergy_def, map_zero, zero_div, zero_add, inner_zero_right] using
    congrArg (· / 2) hzero

/-- On smooth functions the completed Liouville energy agrees with the classical energy. -/
@[simp]
theorem liouvilleEnergy_ofSmooth (u : C^∞⟮I, M; ℝ⟯)
    (K : Lp ℝ 2 (riemannianVolume I M)) :
    (ofSmooth u).liouvilleEnergy K = TauCeti.Manifold.liouvilleEnergy I K u := by
  have hlin : ⟪K, toLp (ofSmooth u)⟫_ℝ =
      ∫ x, K x * u x ∂riemannianVolume I M := by
    rw [toLp_ofSmooth, L2.inner_toLp_continuousMap]
    simp only [ContinuousMap.coe_ofClass, conj_trivial, mul_comm]
  rw [liouvilleEnergy_def, TauCeti.Manifold.liouvilleEnergy_eq_add
    ((Lp.memLp K).integrable one_le_two) (u.contMDiff.of_le (by simp)), hlin,
    dirichletForm_ofSmooth]
  simp only [real_inner_self_eq_norm_sq]
  congr 1
  exact congrArg (· / 2) (integral_congr_ae
    ((toLp_ofSmooth_ae_eq u).mono fun x hx ↦ congrArg (fun t ↦ Real.exp (2 * t)) hx))

variable [I.Boundaryless]

/-- The Sobolev Liouville energy is norm continuous on a closed surface. -/
theorem continuous_liouvilleEnergy (hE : Module.finrank ℝ E = 2)
    (K : Lp ℝ 2 (riemannianVolume I M)) :
    Continuous (fun w : SobolevH1 I M ↦ w.liouvilleEnergy K) := by
  simp only [liouvilleEnergy_def]
  exact ((by fun_prop : Continuous fun w : SobolevH1 I M ↦
    dirichletForm w w / 2 + ⟪K, toLp w⟫_ℝ)).add ((continuous_integral_exp_mul hE 2).div_const 2)

/-- The Sobolev Liouville energy is convex on a closed surface. -/
theorem convexOn_liouvilleEnergy (hE : Module.finrank ℝ E = 2)
    (K : Lp ℝ 2 (riemannianVolume I M)) :
    ConvexOn ℝ univ (fun w : SobolevH1 I M ↦ w.liouvilleEnergy K) := by
  refine ⟨convex_univ, fun u _ v _ a b ha hb hab ↦ ?_⟩
  have hexp := (convexOn_integral_exp_mul hE 2).2 (mem_univ u) (mem_univ v) ha hb hab
  have hD := dirichletForm_self_nonneg (u - v)
  simp only [map_sub, sub_apply] at hD
  rw [dirichletForm_comm v u] at hD
  have hmul := mul_nonneg (mul_nonneg ha hb) hD
  simp only [liouvilleEnergy_def, map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul, inner_add_right, inner_smul_right,
    dirichletForm_comm v u] at *
  have ha' : a * a + a * b = a := by nlinarith [congrArg (a * ·) hab]
  have hb' : b * b + a * b = b := by nlinarith [congrArg (b * ·) hab]
  linear_combination hexp / 2 + hmul / 2 + dirichletForm u u / 2 * ha' +
    dirichletForm v v / 2 * hb'

/-- The Sobolev Liouville energy is lower semicontinuous in the weak topology. -/
theorem lowerSemicontinuous_liouvilleEnergy (hE : Module.finrank ℝ E = 2)
    (K : Lp ℝ 2 (riemannianVolume I M)) :
    LowerSemicontinuous fun w : WeakSpace ℝ (SobolevH1 I M) ↦
      ((toWeakSpace ℝ (SobolevH1 I M)).symm w).liouvilleEnergy K :=
  (convexOn_liouvilleEnergy hE K).quasiconvexOn.lowerSemicontinuous_comp_toWeakSpace_symm
    (continuous_liouvilleEnergy hE K).lowerSemicontinuous

variable [PreconnectedSpace M]

/-- **Coercivity on the completion.** Negative total curvature controls both the Dirichlet
energy and the mean of every `H¹` function by its Liouville energy. -/
theorem exists_le_liouvilleEnergy_add (hE : Module.finrank ℝ E = 2)
    (K : Lp ℝ 2 (riemannianVolume I M)) (hK : ∫ x, K x ∂riemannianVolume I M < 0) :
    ∃ C : ℝ, ∀ w : SobolevH1 I M,
      dirichletForm w w / 4 + (-∫ x, K x ∂riemannianVolume I M) *
        |⨍ x, toLp w x ∂riemannianVolume I M| ≤ w.liouvilleEnergy K + C := by
  obtain ⟨C, hC⟩ := TauCeti.Manifold.exists_le_liouvilleEnergy_add (Lp.memLp K) hK
  have hmean (w : SobolevH1 I M) :
      (⨍ x, toLp w x ∂riemannianVolume I M) =
        ((riemannianVolume I M).real univ)⁻¹ *
          ⟪toLp w, toLp (ofSmooth (1 : C^∞⟮I, M; ℝ⟯))⟫_ℝ := by
    rw [inner_toLp_ofSmooth_right, average_eq]
    simp
  have hmean_cont : Continuous fun w : SobolevH1 I M ↦
      ⨍ x, toLp w x ∂riemannianVolume I M := by
    simp only [hmean]
    fun_prop
  refine ⟨C, fun w ↦ induction_on w (isClosed_le
    ((by fun_prop : Continuous fun w : SobolevH1 I M ↦ dirichletForm w w / 4).add
      (hmean_cont.abs.const_mul _))
    ((continuous_liouvilleEnergy hE K).add_const C)) fun u ↦ ?_⟩
  rw [liouvilleEnergy_ofSmooth, dirichletForm_ofSmooth,
    average_congr (toLp_ofSmooth_ae_eq u)]
  simpa only [real_inner_self_eq_norm_sq] using hC u (u.contMDiff.of_le (by simp))

/-- Sublevel sets of the Liouville energy on a closed surface of negative total curvature
are bounded in the `H¹` norm. -/
theorem exists_norm_le_of_liouvilleEnergy_le (hE : Module.finrank ℝ E = 2)
    (K : Lp ℝ 2 (riemannianVolume I M)) (hK : ∫ x, K x ∂riemannianVolume I M < 0)
    (c : ℝ) :
    ∃ R : ℝ, ∀ w : SobolevH1 I M, w.liouvilleEnergy K ≤ c → ‖w‖ ≤ R := by
  obtain ⟨C, hC⟩ := exists_le_liouvilleEnergy_add hE K hK
  obtain ⟨P, hP0, hP⟩ := exists_norm_toLp_sq_le (I := I) (M := M)
  set B := max (c + C) 0
  set S := -∫ x, K x ∂riemannianVolume I M
  set V := (riemannianVolume I M).real univ
  have hS : 0 < S := neg_pos.mpr hK
  have _ : 0 ≤ B := le_max_right _ _
  refine ⟨Real.sqrt ((P + 1) * (4 * B) + V⁻¹ * (V * (B / S)) ^ 2), fun w hw ↦ ?_⟩
  have hDw := dirichletForm_self_nonneg w
  have htotal := hC w
  have hD : dirichletForm w w ≤ 4 * B := by
    have := mul_nonneg hS.le (abs_nonneg (⨍ x, toLp w x ∂riemannianVolume I M))
    dsimp only [S] at this
    linarith [le_max_left (c + C) 0]
  have hmean : |⨍ x, toLp w x ∂riemannianVolume I M| ≤ B / S := by
    rw [le_div_iff₀ hS]
    linarith [le_max_left (c + C) 0]
  have hint : |∫ x, toLp w x ∂riemannianVolume I M| ≤ V * (B / S) := by
    rw [← measure_smul_average (riemannianVolume I M) (fun x ↦ toLp w x), smul_eq_mul,
      abs_mul, abs_of_nonneg (measureReal_nonneg : 0 ≤ V)]
    exact mul_le_mul_of_nonneg_left hmean measureReal_nonneg
  apply (Real.le_sqrt (norm_nonneg w) (by positivity)).mpr
  rw [norm_sq_eq_dirichletForm_add]
  calc
    _ ≤ (P + 1) * dirichletForm w w + V⁻¹ * (∫ x, toLp w x ∂riemannianVolume I M) ^ 2 := by
      linarith [hP w]
    _ ≤ _ := by
      have hintsq : (∫ x, toLp w x ∂riemannianVolume I M) ^ 2 ≤ (V * (B / S)) ^ 2 := by
        nlinarith [sq_abs (∫ x, toLp w x ∂riemannianVolume I M),
          mul_self_le_mul_self (abs_nonneg (∫ x, toLp w x ∂riemannianVolume I M)) hint]
      exact add_le_add (mul_le_mul_of_nonneg_left hD (by positivity))
        (mul_le_mul_of_nonneg_left hintsq (inv_nonneg.mpr measureReal_nonneg))

/-- **Existence of a Sobolev minimizer.** On a closed connected Riemannian surface, the
Liouville energy for square-integrable `K` with negative integral attains its minimum on `H¹`.
No smoothness or solution of the curvature equation is assumed. -/
theorem exists_forall_liouvilleEnergy_le (hE : Module.finrank ℝ E = 2)
    (K : Lp ℝ 2 (riemannianVolume I M)) (hK : ∫ x, K x ∂riemannianVolume I M < 0) :
    ∃ w : SobolevH1 I M, ∀ v : SobolevH1 I M, w.liouvilleEnergy K ≤ v.liouvilleEnergy K := by
  obtain ⟨R, hR⟩ := exists_norm_le_of_liouvilleEnergy_le hE K hK
    ((0 : SobolevH1 I M).liouvilleEnergy K)
  have hR0 : (0 : SobolevH1 I M) ∈ Metric.closedBall 0 R := by
    rw [mem_closedBall_zero_iff]
    exact hR 0 le_rfl
  have hcompact : IsCompact (toWeakSpace ℝ (SobolevH1 I M) '' Metric.closedBall 0 R) :=
    TauCeti.isCompact_toWeakSpace_closedBall
      surjective_inclusionInDoubleDual_of_uniformConvexSpace 0 R
  obtain ⟨a, -, hmin⟩ := (lowerSemicontinuous_liouvilleEnergy hE K).lowerSemicontinuousOn
    _ |>.exists_isMinOn ⟨_, mem_image_of_mem _ hR0⟩ hcompact
  refine ⟨(toWeakSpace ℝ (SobolevH1 I M)).symm a, fun v ↦ ?_⟩
  by_cases hv : ‖v‖ ≤ R
  · simpa only [LinearEquiv.symm_apply_apply] using
      (isMinOn_iff.mp hmin) _ (mem_image_of_mem _ (mem_closedBall_zero_iff.mpr hv))
  · have h0 := (isMinOn_iff.mp hmin) _ (mem_image_of_mem _ hR0)
    simp only [LinearEquiv.symm_apply_apply] at h0
    exact h0.trans (le_of_lt (not_le.mp fun h ↦ hv (hR v h)))

end TauCeti.Manifold.SobolevH1

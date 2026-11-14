/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.LiouvilleEnergy.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Trudinger
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Convex
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.LocallyConvex.WeakSpace
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Geometry.Manifold.Riemannian.Poisson
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Integral.Exp.AddMul

/-!
# Minimizing the Liouville energy on a closed surface

The Liouville energy extends to the Hilbert completion `SobolevH1 I M` as
`J(w) = D(w,w)/2 + ⟪K,w⟫L² + (∫ exp(2w) dV)/2`.
On a closed surface Trudinger's inequality makes the exponential term finite and locally
bounded. Its convexity then gives norm continuity. Consequently the energy is continuous,
convex and weakly lower semicontinuous. The smooth coercivity estimate extends by density;
when `∫ K dV < 0`, bounded energy implies bounded `H¹` norm. Weak compactness of Hilbert
balls therefore gives a minimizer on the completed space.

Trudinger's inequality also makes `J` differentiable along lines: `t ↦ J(w + t v)` has derivative
`D(w, v) + ⟪K, v⟫_{L²} + ∫ e^(2w) v dV` at `t = 0`. A minimizer `w` is therefore a weak solution
of the curvature equation `Δ⁺w + K + e^(2w) = 0`,

`D(w, v) = -∫ (K + e^(2w)) v dV` for every `v ∈ H¹(M)`,

in the form of the weak Poisson equation of
`TauCeti.Manifold.SobolevH1.existsUnique_dirichletForm_eq` with right-hand side `-(K + e^(2w))`.
Testing a weak solution against the constant `1` gives the area normalization
`∫ e^(2w) dV = -∫ K dV`.

These are variational statements without a regularity assertion: a smooth solution of the
curvature equation requires elliptic regularity in addition. The direct-method argument follows
the existing formalization of `TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`.

## Main results

* `TauCeti.Manifold.SobolevH1.exists_forall_liouvilleEnergy_le`: the Liouville energy attains its
  minimum on `H¹(M)` when `∫ K dV < 0`.
* `TauCeti.Manifold.SobolevH1.hasDerivAt_liouvilleEnergy_add_smul`: the first variation of the
  Liouville energy on `H¹(M)`.
* `TauCeti.Manifold.SobolevH1.dirichletForm_eq_integral_of_forall_liouvilleEnergy_le`: the weak
  Euler–Lagrange equation of a minimizer.
* `TauCeti.Manifold.SobolevH1.integral_exp_two_mul_eq_neg_integral_of_forall_dirichletForm_eq`:
  the area normalization of a weak solution.
* `TauCeti.Manifold.SobolevH1.exists_forall_dirichletForm_eq_integral_neg_add_exp_mul`:
  existence of a weak solution of the curvature equation when `∫ K dV < 0`.

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

/-- **The first variation of the Sobolev Liouville energy.** On a closed surface, for
`K ∈ L²(M)` and `w, v ∈ H¹(M)`, the function `t ↦ J(w + t v)` has derivative
`D(w, v) + ⟪K, v⟫_{L²} + ∫ e^(2w) v dV` at `t = 0`, where `D` is the Dirichlet form. -/
theorem hasDerivAt_liouvilleEnergy_add_smul (hE : Module.finrank ℝ E = 2)
    (K : Lp ℝ 2 (riemannianVolume I M)) (w v : SobolevH1 I M) :
    HasDerivAt (fun t : ℝ ↦ (w + t • v).liouvilleEnergy K)
      (dirichletForm w v + ⟪K, toLp v⟫_ℝ +
        ∫ x, Real.exp (2 * toLp w x) * toLp v x ∂riemannianVolume I M) 0 := by
  -- Along the line, the exponential term is `∫ exp (2w + t (2v)) dV`, which is differentiable
  -- because Trudinger's inequality makes every `exp (2 (w + s v))` integrable.
  have hae (s : ℝ) : (fun x ↦ Real.exp (2 * toLp (w + s • v) x)) =ᵐ[riemannianVolume I M]
      fun x ↦ Real.exp (2 * toLp w x + s * (2 * toLp v x)) := by
    filter_upwards [Lp.coeFn_add (toLp w) (s • toLp v), Lp.coeFn_smul s (toLp v)] with x hx hs
    rw [map_add, map_smul, hx, Pi.add_apply, hs, Pi.smul_apply, smul_eq_mul]
    ring_nf
  have hexp := hasDerivAt_integral_exp_add_mul (μ := riemannianVolume I M) (t₀ := 0)
    (.of_forall fun s ↦ (integrable_exp_mul hE (w + s • v) 2).congr (hae s))
  have hline (t : ℝ) : (w + t • v).liouvilleEnergy K =
      (dirichletForm w w + 2 * t * dirichletForm w v + t ^ 2 * dirichletForm v v) / 2 +
        (⟪K, toLp w⟫_ℝ + t * ⟪K, toLp v⟫_ℝ) +
          (∫ x, Real.exp (2 * toLp w x + t * (2 * toLp v x)) ∂riemannianVolume I M) / 2 := by
    rw [liouvilleEnergy_def, integral_congr_ae (hae t)]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, inner_add_right,
      inner_smul_right, dirichletForm_comm v w]
    ring
  have h := ((((hasDerivAt_id (0 : ℝ)).const_mul (2 * dirichletForm w v)).const_add
      (dirichletForm w w)).add
    ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (dirichletForm v v))).div_const 2 |>.add
    (((hasDerivAt_id (0 : ℝ)).const_mul ⟪K, toLp v⟫_ℝ).const_add ⟪K, toLp w⟫_ℝ)
    |>.add (hexp.div_const 2)
  convert h using 1
  · funext t
    simp only [hline, Pi.add_apply, id]
    ring
  · have hint : ∫ x, 2 * toLp v x * Real.exp (2 * toLp w x + 0 * (2 * toLp v x))
        ∂riemannianVolume I M =
          2 * ∫ x, Real.exp (2 * toLp w x) * toLp v x ∂riemannianVolume I M := by
      rw [← integral_const_mul]
      simp only [zero_mul, add_zero, mul_comm (Real.exp _), mul_assoc]
    rw [hint]
    ring

/-- **The weak Euler–Lagrange equation of the Liouville energy.** On a closed surface, let
`K ∈ L²(M)` and let `w ∈ H¹(M)` minimize the Liouville energy. Then `w` is a weak solution of the
curvature equation `Δ⁺w + K + e^(2w) = 0`: for every `v ∈ H¹(M)`,
`D(w, v) = -∫ (K + e^(2w)) v dV`, where `D` is the Dirichlet form. -/
theorem dirichletForm_eq_integral_of_forall_liouvilleEnergy_le (hE : Module.finrank ℝ E = 2)
    (K : Lp ℝ 2 (riemannianVolume I M)) {w : SobolevH1 I M}
    (hw : ∀ v : SobolevH1 I M, w.liouvilleEnergy K ≤ v.liouvilleEnergy K) (v : SobolevH1 I M) :
    dirichletForm w v =
      ∫ x, -(K x + Real.exp (2 * toLp w x)) * toLp v x ∂riemannianVolume I M := by
  have hmin : IsLocalMin (fun t : ℝ ↦ (w + t • v).liouvilleEnergy K) 0 :=
    Filter.Eventually.of_forall fun t ↦ by simpa only [zero_smul, add_zero] using hw (w + t • v)
  have h0 := hmin.hasDerivAt_eq_zero (hasDerivAt_liouvilleEnergy_add_smul hE K w v)
  have hK : ⟪K, toLp v⟫_ℝ = ∫ x, K x * toLp v x ∂riemannianVolume I M := by
    simp [L2.inner_def, mul_comm]
  have hexp : Integrable (fun x ↦ Real.exp (2 * toLp w x) * toLp v x) (riemannianVolume I M) :=
    (memLp_exp_mul hE w 2 (p := 2) ENNReal.ofNat_ne_top).integrable_mul (Lp.memLp (toLp v))
  simp only [neg_mul, add_mul, integral_neg]
  rw [integral_add (f := fun x ↦ K x * toLp v x)
    ((Lp.memLp K).integrable_mul (Lp.memLp (toLp v))) hexp, ← hK]
  linarith

/-- **Area normalization.** On a closed surface, if `w ∈ H¹(M)` is a weak solution of the
curvature equation `Δ⁺w + K + e^(2w) = 0` for `K ∈ L²(M)`, then `∫ e^(2w) dV = -∫ K dV`. When `K`
is the Gaussian curvature, this says that the conformal metric `e^(2w) g` has area `-∫ K dV`. -/
theorem integral_exp_two_mul_eq_neg_integral_of_forall_dirichletForm_eq
    (hE : Module.finrank ℝ E = 2) (K : Lp ℝ 2 (riemannianVolume I M)) {w : SobolevH1 I M}
    (hw : ∀ v : SobolevH1 I M, dirichletForm w v =
      ∫ x, -(K x + Real.exp (2 * toLp w x)) * toLp v x ∂riemannianVolume I M) :
    ∫ x, Real.exp (2 * toLp w x) ∂riemannianVolume I M =
      -∫ x, K x ∂riemannianVolume I M := by
  have h := hw (ofSmooth 1)
  rw [dirichletForm_ofSmooth_one, integral_congr_ae ((toLp_ofSmooth_ae_eq 1).mono
    fun x hx ↦ congrArg (-(K x + Real.exp (2 * toLp w x)) * ·) hx)] at h
  simp only [ContMDiffMap.coe_one, Pi.one_apply, mul_one, integral_neg] at h
  rw [integral_add ((Lp.memLp K).integrable one_le_two) (integrable_exp_mul hE w 2)] at h
  linarith

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

/-- **Existence of a weak solution of the curvature equation.** On a closed connected Riemannian
surface, for `K ∈ L²(M)` with negative integral, there is `w ∈ H¹(M)` solving
`Δ⁺w + K + e^(2w) = 0` weakly: `D(w, v) = -∫ (K + e^(2w)) v dV` for every `v ∈ H¹(M)`. -/
theorem exists_forall_dirichletForm_eq_integral_neg_add_exp_mul (hE : Module.finrank ℝ E = 2)
    (K : Lp ℝ 2 (riemannianVolume I M)) (hK : ∫ x, K x ∂riemannianVolume I M < 0) :
    ∃ w : SobolevH1 I M, ∀ v : SobolevH1 I M, dirichletForm w v =
      ∫ x, -(K x + Real.exp (2 * toLp w x)) * toLp v x ∂riemannianVolume I M :=
  (exists_forall_liouvilleEnergy_le hE K hK).imp fun _ hw ↦
    dirichletForm_eq_integral_of_forall_liouvilleEnergy_le hE K hw

end TauCeti.Manifold.SobolevH1

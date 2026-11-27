/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Probability.DysonBrownianMotion.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.ODE.Nonautonomous
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Globally Lipschitz chamber truncations of Dyson Brownian motion

Shifting by a continuous additive forcing path `w : ℝ≥0 → Fin n → ℝ` reduces the `ε`-truncated
Dyson integral equation to the globally Lipschitz nonautonomous ODE
`Z' s = truncatedDysonDrift ε n (Z s + w s.toNNReal)`, solved globally on `ℝ` by
`ODE.nonautonomousSolution`. Adding `w` back produces the global `ε`-truncated trajectory
`truncatedDysonPath`.

This file constructs `truncatedDysonPath` and develops its finite-horizon integral-equation
uniqueness, Grönwall stability in `(x, w)`, causal congruence in the driving path, global `ℓ²`
energy identity and contraction, consistency across cutoffs before chamber exit, localization of
`IsDysonPath`, and deterministic and almost-sure construction of global Dyson trajectories from
non-colliding chamber truncations.

## Main declarations

* `TauCeti.Probability.truncatedDysonPath`: global `ε`-truncated trajectory driven by continuous
  `w`.
* `TauCeti.Probability.truncatedDysonPath_eq_integral` and
  `TauCeti.Probability.eq_truncatedDysonPath_of_eq_integral`: integral equation and finite-horizon
  uniqueness.
* `TauCeti.Probability.dist_truncatedDysonPath_le` and
  `TauCeti.Probability.truncatedDysonPath_eq_of_eqOn`: Grönwall stability and causal congruence.
* `TauCeti.Probability.sum_truncatedDysonPath_sub_sq_eq` and
  `TauCeti.Probability.sum_truncatedDysonPath_sub_sq_le`: global `ℓ²` energy identity and
  contraction.
* `TauCeti.Probability.truncatedDysonPath_eq_of_le_sub`,
  `TauCeti.Probability.IsDysonPath.eq_truncatedDysonPath_of_le_sub`, and
  `TauCeti.Probability.isDysonPath_of_forall_exists_truncatedDysonPath`: cutoff consistency and
  localization between truncated and genuine Dyson trajectories.
* `TauCeti.Probability.exists_isDysonPath_of_forall_exists_le_truncatedDysonPath_sub` and
  `TauCeti.Probability.exists_isDysonSolution_of_ae_le_truncatedDysonPath_sub`: pasting
  non-exiting truncations into a global Dyson trajectory and an `IsDysonSolution`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §4.3.1.
* L. C. G. Rogers, Z. Shi, *Interacting Brownian particles and the Wigner law*, Probab. Theory
  Related Fields 95 (1993), 555–570.
* E. Cépa, D. Lépingle, *Diffusing particles with electrostatic repulsion*, Probab. Theory Related
  Fields 107 (1997), 429–449.
-/

public section

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

private noncomputable def shiftedTruncatedField (ε : ℝ) (n : ℕ) (w : ℝ≥0 → Fin n → ℝ)
    (s : ℝ) (z : Fin n → ℝ) : Fin n → ℝ :=
  truncatedDysonDrift ε n (z + w s.toNNReal)

private theorem continuous_shiftedTruncatedField {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) (z : Fin n → ℝ) :
    Continuous fun s : ℝ ↦ shiftedTruncatedField ε n w s z :=
  (continuous_truncatedDysonDrift hε n).comp
    (continuous_const.add (hw.comp continuous_real_toNNReal))

private theorem lipschitzWith_shiftedTruncatedField {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (w : ℝ≥0 → Fin n → ℝ) (s : ℝ) :
    LipschitzWith (2 * ε⁻¹ ^ 2).toNNReal (shiftedTruncatedField ε n w s) :=
  LipschitzWith.of_dist_le_mul fun y z ↦ by
    simpa [shiftedTruncatedField, dist_add_right] using
      (lipschitzWith_truncatedDysonDrift hε n).dist_le_mul (y + w s.toNNReal) (z + w s.toNNReal)

private noncomputable def shiftedTruncatedCurve {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x : Fin n → ℝ)
    (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) : ℝ → Fin n → ℝ :=
  ODE.nonautonomousSolution (shiftedTruncatedField ε n w)
    (continuous_shiftedTruncatedField hε n hw) (lipschitzWith_shiftedTruncatedField hε n w) 0 x

@[simp]
private theorem shiftedTruncatedCurve_zero {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x : Fin n → ℝ)
    (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) : shiftedTruncatedCurve hε n x w hw 0 = x :=
  ODE.nonautonomousSolution_self _ _ _ 0 x

private theorem continuous_shiftedTruncatedCurve {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x : Fin n → ℝ)
    (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) :
    Continuous (shiftedTruncatedCurve hε n x w hw) :=
  ODE.continuous_nonautonomousSolution_apply _ _ _ 0 x

private theorem hasDerivAt_shiftedTruncatedCurve {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x : Fin n → ℝ)
    (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) (r : ℝ) :
    HasDerivAt (shiftedTruncatedCurve hε n x w hw)
      (shiftedTruncatedField ε n w r (shiftedTruncatedCurve hε n x w hw r)) r :=
  ODE.hasDerivAt_nonautonomousSolution _ _ _ 0 x r

section Basic

variable {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x : Fin n → ℝ) (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w)

/-- **Global `ε`-truncated Dyson trajectory** started at `x` and driven by a continuous path `w`.
Defined on `[0, ∞)` by solving `Z' s = truncatedDysonDrift ε n (Z s + w s.toNNReal)` globally via
`ODE.nonautonomousSolution` and setting `X_ε t = Z t + w t`. -/
noncomputable def truncatedDysonPath (t : ℝ≥0) : Fin n → ℝ :=
  shiftedTruncatedCurve hε n x w hw t + w t

/-- `truncatedDysonPath` is continuous on `[0, ∞)`. -/
theorem continuous_truncatedDysonPath : Continuous (truncatedDysonPath hε n x w hw) :=
  ((continuous_shiftedTruncatedCurve hε n x w hw).comp NNReal.continuous_coe).add hw

/-- Value of `truncatedDysonPath` at time `0`. -/
@[simp]
theorem truncatedDysonPath_eval_zero : truncatedDysonPath hε n x w hw 0 = x + w 0 := by
  simp [truncatedDysonPath]

/-- After subtracting the continuous forcing, the truncated trajectory has the prescribed drift
as its derivative on the nonnegative half-line, including the right derivative at zero. -/
theorem hasDerivWithinAt_truncatedDysonPath_sub (r : ℝ) (hr : 0 ≤ r) :
    HasDerivWithinAt
      (fun s : ℝ ↦ truncatedDysonPath hε n x w hw s.toNNReal - w s.toNNReal)
      (truncatedDysonDrift ε n (truncatedDysonPath hε n x w hw r.toNNReal)) (Ici 0) r := by
  have heq (s : ℝ) (hs : 0 ≤ s) :
      truncatedDysonPath hε n x w hw s.toNNReal - w s.toNNReal =
        shiftedTruncatedCurve hε n x w hw s := by
    simp [truncatedDysonPath, Real.coe_toNNReal s hs]
  have hd := hasDerivAt_shiftedTruncatedCurve hε n x w hw r
  have hfield : shiftedTruncatedField ε n w r (shiftedTruncatedCurve hε n x w hw r) =
      truncatedDysonDrift ε n (truncatedDysonPath hε n x w hw r.toNNReal) := by
    simp [shiftedTruncatedField, truncatedDysonPath, Real.coe_toNNReal r hr]
  rw [hfield] at hd
  exact hd.hasDerivWithinAt.congr (fun s hs ↦ heq s hs) (heq r hr)

/-- **Integral equation of `truncatedDysonPath`.** Every coordinate satisfies the `ε`-truncated
Dyson integral equation driven by `w`. -/
theorem truncatedDysonPath_eq_integral (t : ℝ≥0) (i : Fin n) :
    truncatedDysonPath hε n x w hw t i =
      x i + w t i +
        ∫ s in (0 : ℝ)..t,
          truncatedDysonDrift ε n (truncatedDysonPath hε n x w hw s.toNNReal) i := by
  have hZ : shiftedTruncatedCurve hε n x w hw t =
      x + ∫ s in (0 : ℝ)..t,
        shiftedTruncatedField ε n w s (shiftedTruncatedCurve hε n x w hw s) := by
    rw [shiftedTruncatedCurve]
    exact ODE.nonautonomousSolution_eq_integral _ _ _ 0 x t
  have hcont : Continuous fun s : ℝ ↦
      shiftedTruncatedField ε n w s (shiftedTruncatedCurve hε n x w hw s) :=
    (continuous_truncatedDysonDrift hε n).comp
      ((continuous_shiftedTruncatedCurve hε n x w hw).add (hw.comp continuous_real_toNNReal))
  have hproj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ) i).intervalIntegral_comp_comm
    (hcont.intervalIntegrable (μ := volume) 0 t)
  simp only [ContinuousLinearMap.proj_apply] at hproj
  have hZ_i : shiftedTruncatedCurve hε n x w hw t i =
      x i + (∫ s in (0 : ℝ)..t,
        shiftedTruncatedField ε n w s (shiftedTruncatedCurve hε n x w hw s)) i := by
    simpa only [Pi.add_apply] using congrFun hZ i
  have hcongr : ∫ s in (0 : ℝ)..t,
        shiftedTruncatedField ε n w s (shiftedTruncatedCurve hε n x w hw s) i =
      ∫ s in (0 : ℝ)..t, truncatedDysonDrift ε n (truncatedDysonPath hε n x w hw s.toNNReal) i :=
    intervalIntegral.integral_congr fun s hs ↦ by
      rw [uIcc_of_le t.coe_nonneg] at hs
      simp only [shiftedTruncatedField, truncatedDysonPath, Real.coe_toNNReal s hs.1]
  rw [truncatedDysonPath, Pi.add_apply, hZ_i, ← hproj, hcongr]; ring

private theorem intervalIntegrable_truncatedDysonDrift_truncatedDysonPath (t : ℝ≥0) (i : Fin n) :
    IntervalIntegrable
      (fun s : ℝ ↦ truncatedDysonDrift ε n (truncatedDysonPath hε n x w hw s.toNNReal) i)
      volume 0 t :=
  ((continuous_apply i).comp ((continuous_truncatedDysonDrift hε n).comp
    ((continuous_truncatedDysonPath hε n x w hw).comp
      continuous_real_toNNReal))).intervalIntegrable 0 t

/-- Center-of-mass conservation for `truncatedDysonPath`. -/
@[simp]
theorem sum_truncatedDysonPath (t : ℝ≥0) :
    ∑ i : Fin n, truncatedDysonPath hε n x w hw t i = (∑ i : Fin n, x i) + ∑ i : Fin n, w t i := by
  simp_rw [truncatedDysonPath_eq_integral hε n x w hw t, Finset.sum_add_distrib]
  rw [← intervalIntegral.integral_finsetSum fun i _ ↦
    intervalIntegrable_truncatedDysonDrift_truncatedDysonPath hε n x w hw t i]
  simp [sum_truncatedDysonDrift_eq_zero]

end Basic

/-- For at most one particle (`n ≤ 1`), the `ε`-truncated drift vanishes and `truncatedDysonPath`
reduces to `t ↦ x + w t`. -/
theorem truncatedDysonPath_of_le_one {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : n ≤ 1)
    (x : Fin n → ℝ) (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) (t : ℝ≥0) :
    truncatedDysonPath hε n x w hw t = x + w t := by
  ext i
  rw [truncatedDysonPath_eq_integral hε n x w hw t i]
  simp [truncatedDysonDrift_of_le_one ε hn]

/-- For a single particle (`n = 1`), `truncatedDysonPath` equals `x + w t`. -/
@[simp]
theorem truncatedDysonPath_one {ε : ℝ} (hε : 0 < ε) (x : Fin 1 → ℝ)
    (w : ℝ≥0 → Fin 1 → ℝ) (hw : Continuous w) (t : ℝ≥0) :
    truncatedDysonPath hε 1 x w hw t = x + w t :=
  truncatedDysonPath_of_le_one hε le_rfl x w hw t

/-- **Finite-horizon uniqueness of `truncatedDysonPath`.** Any trajectory `Y` that is continuous on
`[0, T]` and satisfies the `ε`-truncated Dyson integral equation on `[0, T]` coincides with
`truncatedDysonPath hε n x w hw` on `[0, T]`. -/
theorem eq_truncatedDysonPath_of_eq_integral {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    {x : Fin n → ℝ} {w Y : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) {T : ℝ≥0}
    (hY : ContinuousOn Y (Iic T))
    (heq : ∀ u ≤ T, ∀ i : Fin n,
      Y u i = x i + w u i + ∫ s in (0 : ℝ)..u, truncatedDysonDrift ε n (Y s.toNNReal) i)
    {t : ℝ≥0} (ht : t ≤ T) : Y t = truncatedDysonPath hε n x w hw t := by
  let g : ℝ → Fin n → ℝ := fun s ↦ truncatedDysonDrift ε n (Y (min s.toNNReal T))
  have hg_cont : Continuous g :=
    (continuous_truncatedDysonDrift hε n).comp
      (hY.comp_continuous (continuous_real_toNNReal.min continuous_const) fun _ ↦ min_le_right _ _)
  let Z : ℝ → Fin n → ℝ := fun r ↦ x + ∫ s in (0 : ℝ)..r, g s
  have hZ_deriv (r : ℝ) : HasDerivAt Z (g r) r :=
    (intervalIntegral.integral_hasDerivAt_right (hg_cont.intervalIntegrable (μ := volume) 0 r)
      (hg_cont.stronglyMeasurableAtFilter _ _) hg_cont.continuousAt).const_add x
  have hZY (u : ℝ≥0) (hu : u ≤ T) : Z u + w u = Y u := by
    ext i
    have hproj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ) i).intervalIntegral_comp_comm
      (hg_cont.intervalIntegrable (μ := volume) 0 u)
    simp only [ContinuousLinearMap.proj_apply] at hproj
    have hcongr : ∫ s in (0 : ℝ)..u, g s i =
        ∫ s in (0 : ℝ)..u, truncatedDysonDrift ε n (Y s.toNNReal) i :=
      intervalIntegral.integral_congr fun s hs ↦ by
        rw [uIcc_of_le u.coe_nonneg] at hs
        simp only [g, min_eq_left ((Real.toNNReal_le_iff_le_coe.2 hs.2).trans hu)]
    dsimp only [Z, Pi.add_apply]; rw [← hproj, hcongr, heq u hu i]; ring
  have hZ_ode : ∀ r ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt Z (shiftedTruncatedField ε n w r (Z r)) (Icc (0 : ℝ) T) r := fun r hr ↦ by
    have hr_le : r.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hr.2
    have hZr : Z r + w r.toNNReal = Y r.toNNReal := by
      simpa only [Real.coe_toNNReal r hr.1] using hZY r.toNNReal hr_le
    have hfield : shiftedTruncatedField ε n w r (Z r) = g r := by
      simp only [g, shiftedTruncatedField, min_eq_left hr_le, hZr]
    rw [hfield]
    exact (hZ_deriv r).hasDerivWithinAt
  have hZ0 : Z 0 = x := by simp [Z]
  have hEqOn : EqOn Z (shiftedTruncatedCurve hε n x w hw) (Icc (0 : ℝ) T) := by
    rw [shiftedTruncatedCurve, ← hZ0]
    exact ODE.eqOn_nonautonomousSolution_of_hasDerivWithinAt (shiftedTruncatedField ε n w)
      (continuous_shiftedTruncatedField hε n hw) (lipschitzWith_shiftedTruncatedField hε n w)
      ordConnected_Icc ⟨le_rfl, T.coe_nonneg⟩ hZ_ode
  rw [← hZY t ht, truncatedDysonPath, hEqOn ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht⟩]

/-- **Grönwall stability of `truncatedDysonPath` in `(x, w)` on `[0, T]`.** Perturbing the initial
state from `x₁` to `x₂` and the driving path on `[0, T]` by at most `δ` in supremum distance
perturbs `truncatedDysonPath` at time `t ≤ T` by at most `(dist x₁ x₂ + δ) * exp (2 ε⁻² t)`. -/
theorem dist_truncatedDysonPath_le {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x₁ x₂ : Fin n → ℝ)
    {w₁ w₂ : ℝ≥0 → Fin n → ℝ} (hw₁ : Continuous w₁) (hw₂ : Continuous w₂) {T : ℝ≥0} {δ : ℝ}
    (hw : ∀ s ≤ T, dist (w₁ s) (w₂ s) ≤ δ) {t : ℝ≥0} (ht : t ≤ T) :
    dist (truncatedDysonPath hε n x₁ w₁ hw₁ t) (truncatedDysonPath hε n x₂ w₂ hw₂ t) ≤
      (dist x₁ x₂ + δ) * Real.exp (2 * ε⁻¹ ^ 2 * (t : ℝ)) := by
  let Z₁ := shiftedTruncatedCurve hε n x₁ w₁ hw₁
  let Z₂ := shiftedTruncatedCurve hε n x₂ w₂ hw₂
  set K : ℝ := 2 * ε⁻¹ ^ 2
  have hK : 0 < K := by positivity
  have hZ_le := norm_le_gronwallBound_of_norm_deriv_right_le (a := (0 : ℝ)) (b := T) (K := K)
    (δ := dist x₁ x₂) (ε := K * δ) (f := fun r ↦ Z₁ r - Z₂ r)
    (f' := fun r ↦ shiftedTruncatedField ε n w₁ r (Z₁ r) - shiftedTruncatedField ε n w₂ r (Z₂ r))
    ((continuous_shiftedTruncatedCurve hε n x₁ w₁ hw₁).sub
      (continuous_shiftedTruncatedCurve hε n x₂ w₂ hw₂)).continuousOn
    (fun r _ ↦ ((hasDerivAt_shiftedTruncatedCurve hε n x₁ w₁ hw₁ r).sub
      (hasDerivAt_shiftedTruncatedCurve hε n x₂ w₂ hw₂ r)).hasDerivWithinAt)
    (by simp [Z₁, Z₂, dist_eq_norm])
    fun r hr ↦ by
      have hlip := (lipschitzWith_truncatedDysonDrift hε n).dist_le_mul
        (Z₁ r + w₁ r.toNNReal) (Z₂ r + w₂ r.toNNReal)
      rw [Real.coe_toNNReal (2 * ε⁻¹ ^ 2) hK.le] at hlip
      calc ‖shiftedTruncatedField ε n w₁ r (Z₁ r) - shiftedTruncatedField ε n w₂ r (Z₂ r)‖
          ≤ K * dist (Z₁ r + w₁ r.toNNReal) (Z₂ r + w₂ r.toNNReal) := by
            simpa only [shiftedTruncatedField, dist_eq_norm] using hlip
        _ ≤ K * (‖Z₁ r - Z₂ r‖ + δ) := mul_le_mul_of_nonneg_left ((dist_add_add_le _ _ _ _).trans
            (by rw [dist_eq_norm]
                exact add_le_add_right (hw r.toNNReal (Real.toNNReal_le_iff_le_coe.2 hr.2.le)) _))
            hK.le
        _ = K * ‖Z₁ r - Z₂ r‖ + K * δ := mul_add _ _ _
  have hZt := hZ_le t ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht⟩
  rw [gronwallBound_of_K_ne_0 hK.ne', sub_zero, mul_div_cancel_left₀ δ hK.ne'] at hZt
  rw [truncatedDysonPath, truncatedDysonPath]
  calc dist (Z₁ t + w₁ t) (Z₂ t + w₂ t)
      ≤ dist (Z₁ t) (Z₂ t) + dist (w₁ t) (w₂ t) := dist_add_add_le _ _ _ _
    _ ≤ (dist x₁ x₂ * Real.exp (K * (t : ℝ)) + δ * (Real.exp (K * (t : ℝ)) - 1)) + δ := by
        rw [dist_eq_norm]; exact add_le_add hZt (hw t ht)
    _ = (dist x₁ x₂ + δ) * Real.exp (K * (t : ℝ)) := by ring

/-- **Causal congruence of `truncatedDysonPath` in the driving path.** Two continuous driving paths
that agree on `[0, T]` generate identical `ε`-truncated trajectories on `[0, T]`. -/
theorem truncatedDysonPath_eq_of_eqOn {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x : Fin n → ℝ)
    {w₁ w₂ : ℝ≥0 → Fin n → ℝ} (hw₁ : Continuous w₁) (hw₂ : Continuous w₂) {T : ℝ≥0}
    (hw : EqOn w₁ w₂ (Iic T)) {t : ℝ≥0} (ht : t ≤ T) :
    truncatedDysonPath hε n x w₁ hw₁ t = truncatedDysonPath hε n x w₂ hw₂ t := by
  have h := dist_truncatedDysonPath_le hε n x x hw₁ hw₂ (δ := 0) (fun s hs ↦ by simp [hw hs]) ht
  rw [dist_self, add_zero, zero_mul] at h
  exact dist_le_zero.1 h

private theorem truncatedDysonPath_eq_integral_of_mem_uIcc {ε : ℝ} (hε : 0 < ε) (n : ℕ)
    (x : Fin n → ℝ) (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) {s t : ℝ≥0} {r : ℝ}
    (hr : r ∈ uIcc (s : ℝ) t) (i : Fin n) :
    truncatedDysonPath hε n x w hw r.toNNReal i =
      x i + w r.toNNReal i +
        ∫ u in (0 : ℝ)..r,
          truncatedDysonDrift ε n (truncatedDysonPath hε n x w hw u.toNNReal) i := by
  simpa only [Real.coe_toNNReal r ((le_min s.coe_nonneg t.coe_nonneg).trans hr.1)] using
    truncatedDysonPath_eq_integral hε n x w hw r.toNNReal i

/-- **Global `ℓ²` energy identity for `truncatedDysonPath`.** For any initial configurations
`x, y : Fin n → ℝ` and times `s, t : ℝ≥0`, the change in squared Euclidean distance between the
`ε`-truncated trajectories from `x` and `y` equals twice the integrated truncated-drift difference
pairing over `s..t`. -/
theorem sum_truncatedDysonPath_sub_sq_eq {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x y : Fin n → ℝ)
    (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) (s t : ℝ≥0) :
    (∑ i : Fin n,
        (truncatedDysonPath hε n x w hw t i - truncatedDysonPath hε n y w hw t i) ^ 2) -
      ∑ i : Fin n,
        (truncatedDysonPath hε n x w hw s i - truncatedDysonPath hε n y w hw s i) ^ 2 =
      2 * ∫ r in (s : ℝ)..t, ∑ i : Fin n,
        (truncatedDysonDrift ε n (truncatedDysonPath hε n x w hw r.toNNReal) i -
          truncatedDysonDrift ε n (truncatedDysonPath hε n y w hw r.toNNReal) i) *
          (truncatedDysonPath hε n x w hw r.toNNReal i -
            truncatedDysonPath hε n y w hw r.toNNReal i) := by
  simpa only [Real.toNNReal_coe] using
    TauCeti.intervalIntegral.sum_sub_sq_eq_of_eq_add_integral (Finset.univ : Finset (Fin n))
      (fun i _ ↦ intervalIntegrable_truncatedDysonDrift_truncatedDysonPath hε n x w hw s i)
      (fun i _ ↦ intervalIntegrable_truncatedDysonDrift_truncatedDysonPath hε n x w hw t i)
      (fun i _ ↦ intervalIntegrable_truncatedDysonDrift_truncatedDysonPath hε n y w hw s i)
      (fun i _ ↦ intervalIntegrable_truncatedDysonDrift_truncatedDysonPath hε n y w hw t i)
      (fun _ hr i _ ↦ truncatedDysonPath_eq_integral_of_mem_uIcc hε n x w hw hr i)
      (fun _ hr i _ ↦ truncatedDysonPath_eq_integral_of_mem_uIcc hε n y w hw hr i)

/-- **Global `ℓ²` contraction for `truncatedDysonPath`.** Holds for arbitrary initial configurations
`x, y : Fin n → ℝ` without any chamber restriction. -/
theorem sum_truncatedDysonPath_sub_sq_le {ε : ℝ} (hε : 0 < ε) (n : ℕ) (x y : Fin n → ℝ)
    (w : ℝ≥0 → Fin n → ℝ) (hw : Continuous w) {s t : ℝ≥0} (hst : s ≤ t) :
    ∑ i : Fin n,
        (truncatedDysonPath hε n x w hw t i - truncatedDysonPath hε n y w hw t i) ^ 2 ≤
      ∑ i : Fin n,
        (truncatedDysonPath hε n x w hw s i - truncatedDysonPath hε n y w hw s i) ^ 2 := by
  simpa only [Real.toNNReal_coe] using
    TauCeti.intervalIntegral.sum_sub_sq_le_of_eq_add_integral (Finset.univ : Finset (Fin n))
      (NNReal.coe_le_coe.2 hst)
      (fun i _ ↦ intervalIntegrable_truncatedDysonDrift_truncatedDysonPath hε n x w hw s i)
      (fun i _ ↦ intervalIntegrable_truncatedDysonDrift_truncatedDysonPath hε n x w hw t i)
      (fun i _ ↦ intervalIntegrable_truncatedDysonDrift_truncatedDysonPath hε n y w hw s i)
      (fun i _ ↦ intervalIntegrable_truncatedDysonDrift_truncatedDysonPath hε n y w hw t i)
      (fun _ hr i _ ↦ truncatedDysonPath_eq_integral_of_mem_uIcc hε n x w hw hr i)
      (fun _ hr i _ ↦ truncatedDysonPath_eq_integral_of_mem_uIcc hε n y w hw hr i)
      fun _ _ ↦ sum_truncatedDysonDrift_sub_mul_sub_nonpos hε n _ _

/-- **Consistency of chamber truncations before exit.** If `truncatedDysonPath hε₁ n x w hw` stays
inside `{z | ∀ i < j, max ε₁ ε₂ ≤ z i - z j}` on `(0, T)`, then the `ε₁`- and `ε₂`-truncated paths
coincide on `[0, T]` (including at the hitting endpoint `t = T`). -/
theorem truncatedDysonPath_eq_of_le_sub {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) {n : ℕ}
    {x : Fin n → ℝ} {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w) {T : ℝ≥0}
    (hgap : ∀ s, 0 < s → s < T → ∀ i j : Fin n, i < j →
      max ε₁ ε₂ ≤ truncatedDysonPath hε₁ n x w hw s i - truncatedDysonPath hε₁ n x w hw s j)
    {t : ℝ≥0} (ht : t ≤ T) :
    truncatedDysonPath hε₁ n x w hw t = truncatedDysonPath hε₂ n x w hw t := by
  refine eq_truncatedDysonPath_of_eq_integral hε₂ hw
    (continuous_truncatedDysonPath hε₁ n x w hw).continuousOn (fun u hu i ↦ ?_) ht
  rw [truncatedDysonPath_eq_integral hε₁ n x w hw u i]
  refine congrArg _ (intervalIntegral.integral_congr_Ioo_of_le u.coe_nonneg fun s hs ↦ ?_)
  have hs_lt : s.toNNReal < T :=
    (Real.toNNReal_lt_iff_lt_coe hs.1.le).2 (hs.2.trans_le (NNReal.coe_le_coe.2 hu))
  have hs_pos : 0 < s.toNNReal := Real.toNNReal_pos.2 hs.1
  rw [truncatedDysonDrift_eq_dysonDrift fun j k hjk ↦
      (le_max_left _ _).trans (hgap s.toNNReal hs_pos hs_lt j k hjk),
    truncatedDysonDrift_eq_dysonDrift fun j k hjk ↦
      (le_max_right _ _).trans (hgap s.toNNReal hs_pos hs_lt j k hjk)]

/-- **Localization of `IsDysonPath` to `truncatedDysonPath`.** Any Dyson trajectory `X` whose
ordered gaps remain at least `ε > 0` on `(0, T)` coincides on `[0, T]` with
`truncatedDysonPath hε n x w hX.continuous_driving` (including at the hitting endpoint `t = T`). -/
theorem IsDysonPath.eq_truncatedDysonPath_of_le_sub {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    {x : Fin n → ℝ} {w X : ℝ≥0 → Fin n → ℝ} (hX : IsDysonPath n x w X)
    {T : ℝ≥0} (hgap : ∀ s, 0 < s → s < T → ∀ i j : Fin n, i < j → ε ≤ X s i - X s j)
    {t : ℝ≥0} (ht : t ≤ T) :
    X t = truncatedDysonPath hε n x w hX.continuous_driving t := by
  refine eq_truncatedDysonPath_of_eq_integral hε hX.continuous_driving
    hX.continuous.continuousOn (fun u hu i ↦ ?_) ht
  rw [hX.eq_integral u i]
  refine congrArg _ (intervalIntegral.integral_congr_Ioo_of_le u.coe_nonneg fun s hs ↦ ?_)
  have hs_lt : s.toNNReal < T :=
    (Real.toNNReal_lt_iff_lt_coe hs.1.le).2 (hs.2.trans_le (NNReal.coe_le_coe.2 hu))
  exact (congrFun (truncatedDysonDrift_eq_dysonDrift
    (hgap s.toNNReal (Real.toNNReal_pos.2 hs.1) hs_lt)) i).symm

/-- **Constructing a Dyson trajectory from non-colliding chamber truncations.** If for every
horizon `T : ℝ≥0` there exists `ε > 0` such that `X` agrees on `[0, T]` with
`truncatedDysonPath hε n x w hw` and keeps ordered gaps at least `ε` on `[0, T]`, then `X` is a
global `IsDysonPath`. -/
theorem isDysonPath_of_forall_exists_truncatedDysonPath {n : ℕ} {x : Fin n → ℝ}
    {w X : ℝ≥0 → Fin n → ℝ} (hw : Continuous w)
    (hloc : ∀ T : ℝ≥0, ∃ (ε : ℝ) (hε : 0 < ε),
      (∀ t ≤ T, X t = truncatedDysonPath hε n x w hw t) ∧
      ∀ t ≤ T, ∀ i j : Fin n, i < j → ε ≤ X t i - X t j) :
    IsDysonPath n x w X := by
  have hcont_X : Continuous X := continuous_iff_continuousAt.2 fun t ↦ by
    obtain ⟨ε, hε, hEq, _⟩ := hloc (t + 1)
    refine (continuous_truncatedDysonPath hε n x w hw).continuousAt.congr ?_
    filter_upwards [Iio_mem_nhds (lt_add_one t)] with s hs
    exact (hEq s hs.le).symm
  refine
    { continuous := hcont_X
      strictAnti := fun t _ i j hij ↦ by
        obtain ⟨ε, hε, _, hgap⟩ := hloc t; linarith [hgap t le_rfl i j hij]
      intervalIntegrable := fun t i ↦ ?_
      eq_integral := fun t i ↦ ?_ }
  · obtain ⟨ε, hε, _, hgap⟩ := hloc t
    refine ContinuousOn.intervalIntegrable (μ := volume) ?_
    rw [uIcc_of_le t.coe_nonneg]
    refine continuousOn_finsetSum _ fun j hj ↦
      ((((continuous_apply i).comp hcont_X).comp continuous_real_toNNReal).sub
        (((continuous_apply j).comp hcont_X).comp continuous_real_toNNReal)).continuousOn.inv₀
        fun s hs h0 ↦ ?_
    dsimp only [Pi.sub_apply, Function.comp_apply] at h0
    have hs_le : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj).symm with hij | hji
    · linarith [hgap s.toNNReal hs_le i j hij]
    · linarith [hgap s.toNNReal hs_le j i hji]
  · obtain ⟨ε, hε, hEq, hgap⟩ := hloc t
    rw [hEq t le_rfl, truncatedDysonPath_eq_integral hε n x w hw t i]
    refine congrArg _ (intervalIntegral.integral_congr fun s hs ↦ ?_)
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hs_le : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hs.2
    rw [← hEq s.toNNReal hs_le, truncatedDysonDrift_eq_dysonDrift (hgap s.toNNReal hs_le)]

/-- **Pasting non-exiting truncations into a global Dyson trajectory.** If for every horizon
`T : ℝ≥0` some `ε > 0` keeps `truncatedDysonPath hε n x w hw` inside the `ε`-chamber on `[0, T]`,
then these truncations paste into a global `IsDysonPath n x w X`, which agrees on `[0, T]` with
every truncation that stays inside its own chamber at positive times before `T`. -/
theorem exists_isDysonPath_of_forall_exists_le_truncatedDysonPath_sub {n : ℕ}
    {x : Fin n → ℝ} {w : ℝ≥0 → Fin n → ℝ} (hw : Continuous w)
    (hch : ∀ T : ℝ≥0, ∃ (ε : ℝ) (hε : 0 < ε), ∀ t ≤ T, ∀ i j : Fin n, i < j →
      ε ≤ truncatedDysonPath hε n x w hw t i - truncatedDysonPath hε n x w hw t j) :
    ∃ X : ℝ≥0 → Fin n → ℝ, IsDysonPath n x w X ∧
      ∀ (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε),
        (∀ s, 0 < s → s < T → ∀ i j : Fin n, i < j →
          ε ≤ truncatedDysonPath hε n x w hw s i - truncatedDysonPath hε n x w hw s j) →
        ∀ t ≤ T, X t = truncatedDysonPath hε n x w hw t := by
  choose εT hεT hchT using hch
  let X : ℝ≥0 → Fin n → ℝ := fun t ↦ truncatedDysonPath (hεT t) n x w hw t
  have hcompat : ∀ (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε),
      (∀ s, 0 < s → s < T → ∀ i j : Fin n, i < j →
        ε ≤ truncatedDysonPath hε n x w hw s i - truncatedDysonPath hε n x w hw s j) →
      ∀ t ≤ T, X t = truncatedDysonPath hε n x w hw t := by
    intro T ε hε hεch t ht
    have hm : 0 < min ε (εT t) := lt_min hε (hεT t)
    have h₁ := truncatedDysonPath_eq_of_le_sub (hεT t) hm hw (T := t)
      (fun s _ hs i j hij ↦ (max_eq_left (min_le_right ε (εT t))).trans_le
        (hchT t s hs.le i j hij)) le_rfl
    have h₂ := truncatedDysonPath_eq_of_le_sub hε hm hw
      (fun s hs₀ hs i j hij ↦ (max_eq_left (min_le_left ε (εT t))).trans_le
        (hεch s hs₀ hs i j hij)) ht
    exact h₁.trans h₂.symm
  refine ⟨X, isDysonPath_of_forall_exists_truncatedDysonPath hw fun T ↦
    ⟨εT T, hεT T, hcompat T (hεT T) (fun s _ hs ↦ hchT T s hs.le), fun t ht i j hij ↦ ?_⟩,
    hcompat⟩
  rw [hcompat T (hεT T) (fun s _ hs ↦ hchT T s hs.le) t ht]
  exact hchT T t ht i j hij

/-- **Almost-sure pasting into an `IsDysonSolution`.** If `B` has almost surely continuous paths
and, almost surely, every horizon `[0, T]` admits a cutoff `ε > 0` whose truncated trajectory stays
in the `ε`-chamber on `[0, T]`, then some process `X` is an `IsDysonSolution β n x P B X`. -/
theorem exists_isDysonSolution_of_ae_le_truncatedDysonPath_sub {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) (n : ℕ) (x : Fin n → ℝ) (P : Measure Ω) (B : Fin n → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, ∀ᵐ ω ∂P, Continuous (B i · ω))
    (hch : ∀ᵐ ω ∂P, ∀ (hw : Continuous fun t i ↦ Real.sqrt (2 / (β * n)) * B i t ω) (T : ℝ≥0),
      ∃ (ε : ℝ) (hε : 0 < ε), ∀ t ≤ T, ∀ i j : Fin n, i < j →
        ε ≤ truncatedDysonPath hε n x _ hw t i - truncatedDysonPath hε n x _ hw t j) :
    ∃ X : ℝ≥0 → Ω → Fin n → ℝ, IsDysonSolution β n x P B X := by
  classical
  let w : Ω → ℝ≥0 → Fin n → ℝ := fun ω t i ↦ Real.sqrt (2 / (β * n)) * B i t ω
  let good : Ω → Prop := fun ω ↦ ∃ γ : ℝ≥0 → Fin n → ℝ, IsDysonPath n x (w ω) γ
  let X : ℝ≥0 → Ω → Fin n → ℝ := fun t ω ↦ if h : good ω then h.choose t else x
  refine ⟨X, ?_⟩
  rw [isDysonSolution_def]
  rw [← ae_all_iff] at hB
  filter_upwards [hB, hch] with ω hωB hωch
  have hw : Continuous (w ω) := continuous_pi fun i ↦ continuous_const.mul (hωB i)
  obtain ⟨γ, hγ, -⟩ :=
    exists_isDysonPath_of_forall_exists_le_truncatedDysonPath_sub hw (hωch hw)
  have hg : good ω := ⟨γ, hγ⟩
  have hX : (fun t ↦ X t ω) = hg.choose := by
    ext t i
    simp [X, hg]
  rw [hX]
  exact hg.choose_spec

end TauCeti.Probability

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import TauCeti.Analysis.Analytic.Constructions
public import TauCeti.Analysis.Analytic.IntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Constant order of vanishing in a distinguished variable

Let `G (x, y)` be analytic near `(x₀, y₀)`, over `ℝ` or `ℂ`, with `y` a distinguished scalar
variable. This file shows that `G` vanishes to order exactly `m` in `y` along `y = y₀` for every
`x` near `x₀` if and only if `G (x, y) = (y - y₀) ^ m • u (x, y)` near `(x₀, y₀)` with `u` analytic
and `u (x₀, y₀) ≠ 0` (`AnalyticAt.eventually_analyticOrderAt_eq_natCast_iff`). This is
McCallum–Parusiński–Paunescu, Lemma 4.4. Since `u` is then nonzero near `(x₀, y₀)`, it writes a
function of constant order in a distinguished variable as a centered power `(y - y₀) ^ m` times a
nowhere-vanishing analytic factor, the form of the hypotheses of the Puiseux theorem with
parameters (op. cit., §4).

The version with `m ≤` the order in place of equality, and no condition on `u`, is
`AnalyticAt.eventually_natCast_le_analyticOrderAt_iff`. It rests on Hadamard's lemma in a
distinguished variable (`AnalyticAt.exists_eventuallyEq_sub_smul`): a function analytic at
`(x₀, y₀)` that vanishes on `y = y₀` near `x₀` is `(y - y₀) • H` near `(x₀, y₀)` with `H` analytic.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, J. Symbolic Comput. 92 (2019), 52–69, Lemma 4.4.
-/

public section

open Filter Set Topology

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Hadamard's lemma** in a distinguished variable: a function `G` analytic at `(x₀, y₀)` that
vanishes on the hyperplane `y = y₀` near `x₀` is `(y - y₀) • H (x, y)` near `(x₀, y₀)`, with `H`
analytic at `(x₀, y₀)`. -/
theorem AnalyticAt.exists_eventuallyEq_sub_smul {G : E × 𝕜 → F} {x₀ : E} {y₀ : 𝕜}
    (hG : AnalyticAt 𝕜 G (x₀, y₀)) (h0 : ∀ᶠ x in 𝓝 x₀, G (x, y₀) = 0) :
    ∃ H : E × 𝕜 → F, AnalyticAt 𝕜 H (x₀, y₀) ∧
      ∀ᶠ p in 𝓝 (x₀, y₀), G p = (p.2 - y₀) • H p := by
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  have : IsScalarTower ℝ 𝕜 F := .restrictScalars ℝ 𝕜 F
  -- `K` is the partial derivative of `G` in the distinguished variable
  set K : E × 𝕜 → F := fun p ↦ fderiv 𝕜 G p (0, 1) with hK
  have hKa {z : E × 𝕜} (hz : AnalyticAt 𝕜 G z) : AnalyticAt 𝕜 K z :=
    ((ContinuousLinearMap.apply 𝕜 F ((0 : E), (1 : 𝕜))).analyticAt _).comp hz.fderiv
  -- `L t` scales the distinguished variable by `t`
  set L : ℝ → (E × 𝕜) →L[𝕜] (E × 𝕜) := fun t ↦
    (ContinuousLinearMap.inl 𝕜 E 𝕜).comp (ContinuousLinearMap.fst 𝕜 E 𝕜) +
      (t : 𝕜) • (ContinuousLinearMap.inr 𝕜 E 𝕜).comp (ContinuousLinearMap.snd 𝕜 E 𝕜) with hL
  have hLapply (t : ℝ) (w : E × 𝕜) : L t w = (w.1, t * w.2) := by
    ext <;> simp [hL]
  have hLc : Continuous L := by
    rw [hL]
    fun_prop
  have hL1 : ∀ t ∈ Icc (0 : ℝ) 1, ‖L t‖ ≤ 1 := by
    intro t ht
    refine (L t).opNorm_le_bound zero_le_one fun w ↦ ?_
    rw [hLapply, one_mul, Prod.norm_def, Prod.norm_def]
    refine max_le_max le_rfl ?_
    rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  refine ⟨fun z ↦ ∫ t in (0 : ℝ)..1, K ((x₀, y₀) + L t (z - (x₀, y₀))),
    (hKa hG).intervalIntegral_comp hLc.continuousOn hL1, ?_⟩
  -- on a ball about `(x₀, y₀)`, `G` is analytic and vanishes on the hyperplane
  have hev : ∀ᶠ z in 𝓝 (x₀, y₀), AnalyticAt 𝕜 G z ∧ G (z.1, y₀) = 0 :=
    hG.eventually_analyticAt.and ((continuous_fst.tendsto (x₀, y₀)).eventually h0)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  filter_upwards [Metric.ball_mem_nhds (x₀, y₀) hρ] with ⟨x, y⟩ hz
  -- the segment from `(x, y₀)` to `(x, y)` stays in the ball
  have hmem (t : ℝ) (ht : t ∈ Icc 0 1) :
      ((x, y₀ + t • (y - y₀)) : E × 𝕜) ∈ Metric.ball (x₀, y₀) ρ := by
    rw [Metric.mem_ball] at hz ⊢
    refine lt_of_le_of_lt ?_ hz
    rw [Prod.dist_eq, Prod.dist_eq]
    refine max_le_max le_rfl ?_
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  -- the fundamental theorem of calculus along the segment
  have hFTC := intervalIntegral.integral_unitInterval_deriv_eq_sub (f := fun s ↦ G (x, s))
    (f' := fun s ↦ K (x, s)) (z₀ := y₀) (z₁ := y - y₀)
    (fun t ht ↦ (ContinuousAt.comp (f := fun t : ℝ ↦ ((x, y₀ + t • (y - y₀)) : E × 𝕜))
      (hKa (hball _ (hmem t ht)).1).continuousAt (by fun_prop)).continuousWithinAt)
    (fun t ht ↦ by
      simpa [hK, Function.comp_def] using
        (hball _ (hmem t ht)).1.differentiableAt.hasFDerivAt.comp_hasDerivAt
          (y₀ + t • (y - y₀)) ((hasDerivAt_const _ x).prodMk (hasDerivAt_id _)))
  rw [add_sub_cancel, (hball _ hz).2, sub_zero] at hFTC
  rw [← hFTC]
  congr 1
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  simp [hLapply, RCLike.real_smul_eq_coe_mul]

/-- **Order in a distinguished variable**, lower bound: a function `G` analytic at `(x₀, y₀)`
vanishes to order at least `m` in `y` at `y₀` along every slice `x = const` near `x₀` if and only
if `G (x, y) = (y - y₀) ^ m • u (x, y)` near `(x₀, y₀)` for some `u` analytic at `(x₀, y₀)`. -/
theorem AnalyticAt.eventually_natCast_le_analyticOrderAt_iff {G : E × 𝕜 → F} {x₀ : E} {y₀ : 𝕜}
    (hG : AnalyticAt 𝕜 G (x₀, y₀)) {m : ℕ} :
    (∀ᶠ x in 𝓝 x₀, (m : ℕ∞) ≤ analyticOrderAt (fun y ↦ G (x, y)) y₀) ↔
      ∃ u : E × 𝕜 → F, AnalyticAt 𝕜 u (x₀, y₀) ∧
        ∀ᶠ p in 𝓝 (x₀, y₀), G p = (p.2 - y₀) ^ m • u p := by
  refine ⟨fun h ↦ ?_, fun ⟨u, hu, hGu⟩ ↦ ?_⟩
  · induction m generalizing G with
    | zero => exact ⟨G, hG, by simp⟩
    | succ m ih =>
      have h0 : ∀ᶠ x in 𝓝 x₀, G (x, y₀) = 0 := h.mono fun x hx ↦
        apply_eq_zero_of_analyticOrderAt_ne_zero (f := fun y ↦ G (x, y)) fun h0 ↦ by
          simp [h0] at hx
      obtain ⟨H, hH, hGH⟩ := hG.exists_eventuallyEq_sub_smul h0
      have hHm : ∀ᶠ x in 𝓝 x₀, (m : ℕ∞) ≤ analyticOrderAt (fun y ↦ H (x, y)) y₀ := by
        rw [nhds_prod_eq] at hGH
        filter_upwards [h, hGH.curry, hH.eventually_analyticAt_curry_right] with x hx hGHx hHx
        rw [analyticOrderAt_congr (g := (· - y₀) • fun y ↦ H (x, y)) hGHx,
          analyticOrderAt_smul (by fun_prop) hHx, analyticOrderAt_id_sub_const_self,
          Nat.cast_succ, add_comm 1] at hx
        exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 hx
      obtain ⟨u, hu, hHu⟩ := ih hH hHm
      refine ⟨u, hu, ?_⟩
      filter_upwards [hGH, hHu] with p hGp hHp
      rw [hGp, hHp, smul_smul, pow_succ']
  · rw [nhds_prod_eq] at hGu
    filter_upwards [hGu.curry, hG.eventually_analyticAt_curry_right,
      hu.eventually_analyticAt_curry_right] with x hGux hGx hux
    exact (natCast_le_analyticOrderAt hGx).2 ⟨_, hux, hGux⟩

/-- **Order in a distinguished variable** (McCallum–Parusiński–Paunescu, Lemma 4.4): a function
`G` analytic at `(x₀, y₀)` vanishes to order exactly `m` in `y` at `y₀` along every slice
`x = const` near `x₀` if and only if `G (x, y) = (y - y₀) ^ m • u (x, y)` near `(x₀, y₀)` for some
`u` analytic at `(x₀, y₀)` with `u (x₀, y₀) ≠ 0`. -/
theorem AnalyticAt.eventually_analyticOrderAt_eq_natCast_iff {G : E × 𝕜 → F} {x₀ : E} {y₀ : 𝕜}
    (hG : AnalyticAt 𝕜 G (x₀, y₀)) {m : ℕ} :
    (∀ᶠ x in 𝓝 x₀, analyticOrderAt (fun y ↦ G (x, y)) y₀ = m) ↔
      ∃ u : E × 𝕜 → F, AnalyticAt 𝕜 u (x₀, y₀) ∧ u (x₀, y₀) ≠ 0 ∧
        ∀ᶠ p in 𝓝 (x₀, y₀), G p = (p.2 - y₀) ^ m • u p := by
  refine ⟨fun h ↦ ?_, fun ⟨u, hu, hu0, hGu⟩ ↦ ?_⟩
  · obtain ⟨u, hu, hGu⟩ :=
      hG.eventually_natCast_le_analyticOrderAt_iff.1 (h.mono fun _ hx ↦ hx.ge)
    refine ⟨u, hu, fun hu0 ↦ ?_, hGu⟩
    -- at `x₀` the order of `G` is `m` plus the order of `u`, so `u` has order zero there
    have hux : AnalyticAt 𝕜 (fun y ↦ u (x₀, y)) y₀ := hu.curry_right
    have hGx₀ := h.self_of_nhds
    rw [nhds_prod_eq] at hGu
    rw [analyticOrderAt_congr (g := (· - y₀) ^ m • fun y ↦ u (x₀, y)) hGu.curry.self_of_nhds,
      analyticOrderAt_smul (by fun_prop) hux, analyticOrderAt_centeredMonomial] at hGx₀
    have h0 : analyticOrderAt (fun y ↦ u (x₀, y)) y₀ = 0 := by
      refine nonpos_iff_eq_zero.1 ((ENat.add_le_add_iff_left (ENat.natCast_ne_top m)).1 ?_)
      rw [add_zero, hGx₀]
    exact (hux.analyticOrderAt_eq_zero.1 h0) hu0
  · have hne : ∀ᶠ x in 𝓝 x₀, u (x, y₀) ≠ 0 :=
      ((continuous_id.prodMk continuous_const).tendsto x₀).eventually
        (hu.continuousAt.eventually_ne hu0)
    rw [nhds_prod_eq] at hGu
    filter_upwards [hGu.curry, hG.eventually_analyticAt_curry_right,
      hu.eventually_analyticAt_curry_right, hne] with x hGux hGx hux hnex
    exact hGx.analyticOrderAt_eq_natCast.2 ⟨_, hux, hnex, hGux⟩

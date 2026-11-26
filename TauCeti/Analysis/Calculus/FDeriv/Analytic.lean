/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import TauCeti.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Derivatives of analytic functions and of power series on balls

Mathlib's `HasFPowerSeriesOnBall.fderiv` shows that the Fréchet derivative of an analytic function
into a complete normed space is represented on the same open extended ball by `p.derivSeries`.
Specializing to one-dimensional domain `𝕜` and evaluating at `1 : 𝕜` gives the scalar-derivative
power series `∑ₙ (n + 1) • p.coeff (n + 1) • zⁿ` on `Metric.eball z₀ r`
(`HasFPowerSeriesOnBall.deriv`).

Mathlib's `AnalyticAt.fderiv` says that the derivative `fderiv 𝕜 f` of a function analytic at `x`
is analytic at `x`. Evaluating it on a vector field `ξ` analytic at `x` gives the derivative of
`f` along `ξ`, `z ↦ f'(z) (ξ z)`, which is again analytic at `x` (`AnalyticAt.fderiv_apply`).

Over a field of characteristic zero, a function with power series `p` on `Metric.eball x r` whose
derivative in a direction `v` vanishes near `x` is constant along `v` on that ball:
`f (x + v) = f x` whenever `‖v‖ₑ < r`
(`HasFPowerSeriesOnBall.apply_add_eq_of_fderiv_apply_eq_zero`). The terms `p (n + 1) (v, …, v)`
are the diagonal values of the derivative series in the direction `v`, up to the factor `n + 1`,
so they vanish. This replaces the mean value theorem over nonarchimedean fields such as `ℚ_p`,
where the ball of convergence is totally disconnected. Characteristic zero is needed: over a field
of characteristic `p`, the derivative of `z ↦ z ^ p` vanishes identically, but the function is not
constant. This is the argument of Schneider, *p-Adic Lie Groups*, Corollary 5.8 (see the
references below). Consequently, if the derivative kills the kernel of a continuous projection
`π` on the ball of convergence `Metric.eball 0 r`, the function satisfies `g (π z) = g z` whenever
`‖π z‖ₑ + ‖z - π z‖ₑ < r` (`HasFPowerSeriesOnBall.apply_proj_eq_of_fderiv_apply_eq_zero`), as for
`ℝ` and `ℂ` in `TauCeti.apply_proj_eq_of_fderiv_apply_eq_zero`.

## References

* P. Schneider, *p-Adic Lie Groups*, Grundlehren der mathematischen Wissenschaften 344, Springer,
  2011, §5, Corollary 5.8 (an analytic function with vanishing derivative is locally constant in
  characteristic zero).
-/

public section

open Filter
open scoped ENNReal Topology

/-- If `f : 𝕜 → E` into a complete normed space has formal power series `p` on `Metric.eball z₀ r`,
then `deriv f` has formal power series `mkPiRingSeries 𝕜 (fun n ↦ (n + 1 : 𝕜) • p.coeff (n + 1))`
on the same ball `Metric.eball z₀ r`. -/
theorem HasFPowerSeriesOnBall.deriv
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {z₀ : 𝕜} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p z₀ r) :
    HasFPowerSeriesOnBall (deriv f)
      (TauCeti.mkPiRingSeries 𝕜 fun n ↦ ((n : 𝕜) + 1) • p.coeff (n + 1)) z₀ r := by
  convert (ContinuousLinearMap.apply 𝕜 E (1 : 𝕜)).comp_hasFPowerSeriesOnBall hf.fderiv using 1
  · ext z
    simp only [Function.comp_apply, ContinuousLinearMap.apply_apply, fderiv_apply_one_eq_deriv]
  · rw [← ((ContinuousLinearMap.apply 𝕜 E (1 : 𝕜)).compFormalMultilinearSeries
      p.derivSeries).mkPiRingSeries_coeff]
    congr 1
    ext n
    simp [← Nat.cast_smul_eq_nsmul 𝕜]

/-- The derivative of a function analytic at `x` along a vector field analytic at `x` is analytic
at `x`. -/
theorem AnalyticAt.fderiv_apply
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] {f : E → F} {ξ : E → E} {x : E}
    (hf : AnalyticAt 𝕜 f x) (hξ : AnalyticAt 𝕜 ξ x) :
    AnalyticAt 𝕜 (fun z ↦ fderiv 𝕜 f z (ξ z)) x :=
  ((ContinuousLinearMap.apply 𝕜 F : E →L[𝕜] (E →L[𝕜] F) →L[𝕜] F).analyticAt_bilinear _).comp
    (hξ.prod hf.fderiv)

/-- **An analytic function stationary in a direction is constant along it.** Over a field of
characteristic zero, if `f` has power series `p` on `Metric.eball x r` and its derivative in the
direction `v` vanishes near `x`, then `f (x + v) = f x` provided `‖v‖ₑ < r`. -/
theorem HasFPowerSeriesOnBall.apply_add_eq_of_fderiv_apply_eq_zero
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {x v : E} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p x r) (hv : ∀ᶠ y in 𝓝 x, fderiv 𝕜 f y v = 0)
    (hvr : ‖v‖ₑ < r) : f (x + v) = f x := by
  -- The derivative in the direction `v` has the power series `p.derivSeries` evaluated at `v`,
  -- and it vanishes near `x`, so all terms of that series vanish.
  have h0 := ((ContinuousLinearMap.apply 𝕜 F v).comp_hasFPowerSeriesOnBall
    hf.fderiv).hasFPowerSeriesAt.congr (g := 0) hv
  -- Its diagonal terms are `(n + 1) • p (n + 1) (v, …, v)`.
  have hterm (n : ℕ) : p (n + 1) (fun _ ↦ v) = 0 := by
    have h := h0.apply_eq_zero n v
    simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousLinearMap.apply_apply, FormalMultilinearSeries.derivSeries_apply_diag] at h
    rw [← Nat.cast_smul_eq_nsmul 𝕜] at h
    exact (smul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 n.succ_ne_zero)
  have hsum := hf.hasSum (Metric.mem_eball.2 (by simpa using hvr))
  rw [hsum.unique (hasSum_single 0 fun n hn ↦ by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    exact hterm m)]
  exact hf.coeff_zero _

/-- **An analytic function stationary along the kernel of a projection factors through it.** Over a
field of characteristic zero, let `π` be a continuous projection and let `g` have power series `p`
on `Metric.eball 0 r`, with derivative killing `ker π` on that ball. Then `g (π z) = g z` whenever
`‖π z‖ₑ + ‖z - π z‖ₑ < r`. -/
theorem HasFPowerSeriesOnBall.apply_proj_eq_of_fderiv_apply_eq_zero
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {g : E → F} {p : FormalMultilinearSeries 𝕜 E F} {r : ℝ≥0∞} (hg : HasFPowerSeriesOnBall g p 0 r)
    {π : E →L[𝕜] E} (hπ : IsIdempotentElem π)
    (hker : ∀ u ∈ Metric.eball (0 : E) r, ∀ v, π v = 0 → fderiv 𝕜 g u v = 0) {z : E}
    (hz : ‖π z‖ₑ + ‖z - π z‖ₑ < r) : g (π z) = g z := by
  have hπz : π z ∈ Metric.eball (0 : E) r := by
    simpa [edist_zero_right] using le_self_add.trans_lt hz
  -- Expand `g` about `π z`, on the ball of radius `r - ‖π z‖ₑ`, and move along `z - π z ∈ ker π`.
  have hg' := hg.changeOrigin (y := π z) (by simpa [edist_zero_right, eNorm_eq_nnNorm] using hπz)
  rw [zero_add] at hg'
  have h := hg'.apply_add_eq_of_fderiv_apply_eq_zero (v := z - π z)
    (eventually_of_mem (Metric.isOpen_eball.mem_nhds hπz) fun u hu ↦
      hker u hu _ (by rw [map_sub, sub_eq_zero]; exact congr($hπ z).symm))
    (by rw [eNorm_eq_nnNorm, lt_tsub_iff_left, ← eNorm_eq_nnNorm]; exact hz)
  rw [add_sub_cancel] at h
  exact h.symm

end

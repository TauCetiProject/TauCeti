/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Calculus.FDeriv.QuadraticMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Ultrafilter

/-!
# Smooth touching upper supports from approximate quadratic bounds

An upper error smaller than every positive multiple of the squared displacement gives a smooth
local upper support with the prescribed derivative and arbitrarily small loss in its Laplacian
at the contact point. Uniformly bounded approximate first and second coefficients give the same
conclusion along any nontrivial filter. Neither symmetry of the approximate coefficients nor
differentiability of the supported function is assumed.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Theorems 3.27–3.29:
  the Euclidean analytic step for the distance support barriers used in localization.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Filter Topology InnerProductSpace Laplacian
open scoped ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The canonical operator norm used when forming spaces of bilinear coefficients. -/
private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- A quadratic upper expansion with arbitrarily small quadratic error admits a smooth touching
local upper support. Its derivative at `x₀` is `a` and its Laplacian there is at most
`traceL B + ε`. -/
theorem exists_contDiff_apply_eq_ge_fderiv_eq_laplacian_le
    (f : E → ℝ) (x₀ : E) (a : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hmajor : ∀ μ > 0, ∀ᶠ x in 𝓝 x₀, f x ≤ f x₀ + a (x - x₀) +
      (1 / 2 : ℝ) * B (x - x₀) (x - x₀) + μ * ‖x - x₀‖ ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧ P x₀ = f x₀ ∧ (∀ᶠ x in 𝓝 x₀, f x ≤ P x) ∧
      fderiv ℝ P x₀ = a ∧ Δ P x₀ ≤ traceL B + ε := by
  let μ := ε / (2 * ((Module.finrank ℝ E : ℝ) + 1))
  have hμ : 0 < μ := by dsimp [μ]; positivity
  let J : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  have hJ (v w : E) : J v w = inner ℝ v w := innerSL_apply_apply ℝ v w
  let Q : E →L[ℝ] E →L[ℝ] ℝ :=
    (1 / 2 : ℝ) • (B + B.flip) + (2 * μ) • J
  have hQsym (v w : E) : Q v w = Q w v := by
    simp only [Q, add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.flip_apply,
      hJ]
    rw [real_inner_comm v w]
    ring
  let P := fun x ↦ f x₀ + a (x - x₀) + (1 / 2 : ℝ) * Q (x - x₀) (x - x₀)
  have hjet := quadratic_polynomial_derivatives x₀ (f x₀) a Q hQsym
  simp only [smul_eq_mul] at hjet
  obtain ⟨hP, hP0, hPd, hPdd⟩ := hjet
  have htrace : traceL Q = traceL B + (2 * μ) * (Module.finrank ℝ E : ℝ) := by
    have hJtrace : traceL J = (Module.finrank ℝ E : ℝ) := traceL_innerSL
    simp only [Q, map_add, map_smul, traceL_flip, hJtrace, smul_eq_mul]
    ring
  refine ⟨P, hP, hP0, ?_, hPd, ?_⟩
  · filter_upwards [hmajor μ hμ] with x hx
    refine hx.trans ?_
    simp only [P, Q, add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.flip_apply,
      hJ, real_inner_self_eq_norm_sq]
    ring_nf
    exact le_refl _
  · rw [laplacian_eq_traceL, hPdd, htrace]
    have hμeq : μ * (2 * ((Module.finrank ℝ E : ℝ) + 1)) = ε :=
      div_mul_cancel₀ ε (by positivity)
    linarith

/-- Uniformly bounded approximate linear and bilinear coefficients with arbitrarily small
quadratic upper errors yield a smooth touching local upper support. Its derivative norm at `x₀`
is at most `K` and its Laplacian there is at most `Λ + ε`. -/
theorem exists_contDiff_apply_eq_ge_norm_fderiv_le_laplacian_le
    {κ : Type*} {l : Filter κ} [l.NeBot] (f : E → ℝ) (x₀ : E)
    (c b : κ → ℝ) (A : κ → E →L[ℝ] ℝ) (H : κ → E →L[ℝ] E →L[ℝ] ℝ)
    (K M Λ : ℝ) (hc : Tendsto c l (𝓝 (f x₀))) (hb : Tendsto b l (𝓝 Λ))
    (hA : ∀ᶠ j in l, ‖A j‖ ≤ K) (hH : ∀ᶠ j in l, ‖H j‖ ≤ M)
    (htrace : ∀ᶠ j in l, traceL (H j) ≤ b j)
    (hmajor : ∀ μ > 0, ∀ᶠ x in 𝓝 x₀, ∀ᶠ j in l, f x ≤ c j + A j (x - x₀) +
      (1 / 2 : ℝ) * H j (x - x₀) (x - x₀) + μ * ‖x - x₀‖ ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧ P x₀ = f x₀ ∧ (∀ᶠ x in 𝓝 x₀, f x ≤ P x) ∧
      ‖fderiv ℝ P x₀‖ ≤ K ∧ Δ P x₀ ≤ Λ + ε := by
  classical
  have : ProperSpace (E →L[ℝ] E →L[ℝ] ℝ) := by
    simpa +instances using (FiniteDimensional.proper ℝ (E →L[ℝ] E →L[ℝ] ℝ))
  have hcompact : IsCompact (Metric.closedBall (0 : E →L[ℝ] ℝ) K ×ˢ
      Metric.closedBall (0 : E →L[ℝ] E →L[ℝ] ℝ) M) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hmem : ∀ᶠ j in l, (A j, H j) ∈
      Metric.closedBall (0 : E →L[ℝ] ℝ) K ×ˢ
        Metric.closedBall (0 : E →L[ℝ] E →L[ℝ] ℝ) M := by
    filter_upwards [hA, hH] with j hjA hjH
    constructor
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hjA
    · simpa only [Metric.mem_closedBall] using (dist_zero_right (H j)).le.trans hjH
  obtain ⟨⟨a, B⟩, hab, hcluster⟩ := hcompact.exists_mapClusterPt_of_frequently hmem.frequently
  obtain ⟨U, hUl, hlim⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  have hAlim := (continuous_fst.tendsto (a, B)).comp hlim
  have hBlim := (continuous_snd.tendsto (a, B)).comp hlim
  have hBtrace : traceL B ≤ Λ :=
    le_of_tendsto_of_tendsto ((traceL.continuous.tendsto B).comp hBlim)
      (hb.mono_left hUl) (htrace.filter_mono hUl)
  have hmajor' (μ : ℝ) (hμ : 0 < μ) : ∀ᶠ x in 𝓝 x₀, f x ≤ f x₀ + a (x - x₀) +
      (1 / 2 : ℝ) * B (x - x₀) (x - x₀) + μ * ‖x - x₀‖ ^ 2 := by
    filter_upwards [hmajor μ hμ] with x hx
    have hAEval : Tendsto (fun j ↦ A j (x - x₀)) (U : Filter κ) (𝓝 (a (x - x₀))) :=
      ((continuous_id.clm_apply continuous_const).tendsto a).comp hAlim
    have hBEval : Tendsto (fun j ↦ H j (x - x₀) (x - x₀)) (U : Filter κ)
        (𝓝 (B (x - x₀) (x - x₀))) := by
      have hcont : Continuous (fun Q : E →L[ℝ] E →L[ℝ] ℝ ↦ Q (x - x₀) (x - x₀)) :=
        (continuous_id.clm_apply continuous_const).clm_apply continuous_const
      exact (hcont.tendsto B).comp hBlim
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      ((((hc.mono_left hUl).add hAEval).add
        (tendsto_const_nhds.mul hBEval)).add tendsto_const_nhds) (hx.filter_mono hUl)
  obtain ⟨P, hP, hP0, hPf, hPd, hPΔ⟩ :=
    exists_contDiff_apply_eq_ge_fderiv_eq_laplacian_le f x₀ a B hmajor' hε
  refine ⟨P, hP, hP0, hPf, ?_, hPΔ.trans (add_le_add hBtrace le_rfl)⟩
  simpa only [hPd] using (mem_closedBall_zero_iff.mp hab.1)

end TauCeti

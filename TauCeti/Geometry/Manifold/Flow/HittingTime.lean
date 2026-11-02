/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Complete
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Smooth hitting times of transverse level sets

Let `ψ` be the flow of a complete `C^n` vector field `v` on a finite-dimensional boundaryless
manifold, and let `f` be a function whose level set `{f = c}` is crossed transversally by `v`,
`df(v) ≠ 0`. If the trajectory through `x` meets the level set at time `τ₀`, then the time at
which the trajectory through a nearby point `x'` meets it is a `C^n` function of `x'`. This is
the implicit function theorem for the equation `f(ψ_t(x')) = c` in the time variable `t`.

## Main results

* `TauCeti.IsCompleteVectorField.exists_contMDiffAt_hittingTime`: the hitting time of a level
  set crossed transversally by a complete `C^n` field is `C^n` near the initial point.
-/

public section

open Filter
open scoped Manifold Topology

namespace TauCeti

namespace IsCompleteVectorField

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I 1 M]

/-- **Smooth hitting times.** Let `v` be a complete `C^n` vector field, `n ≥ 1`, whose trajectory
through `x` reaches at time `τ₀` a point `y` at which `f` is `C^n` with nonzero derivative along
`v`. Then near `x` there is a `C^n` function `T` with `T x = τ₀` such that the trajectory through
`x'` meets the level set `{f = f y}` at time `T x'`. -/
theorem exists_contMDiffAt_hittingTime {n : ℕ∞} (hn : 1 ≤ n) [IsManifold I n M]
    {v : (x : M) → TangentSpace I x} (hcomplete : IsCompleteVectorField v)
    (hv : ContMDiff I I.tangent n (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {f : M → ℝ} {x : M} {τ₀ : ℝ} (hf : ContMDiffAt I 𝓘(ℝ) n f (flowOf v τ₀ x))
    (hfv : mvfderiv I f (flowOf v τ₀ x) (v (flowOf v τ₀ x)) ≠ 0) :
    ∃ T : M → ℝ, ContMDiffAt I 𝓘(ℝ) n T x ∧ T x = τ₀ ∧
      ∀ᶠ x' in 𝓝 x, f (flowOf v (T x') x') = f (flowOf v τ₀ x) := by
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hn).ne'
  -- The equation `G(u, t) = f(ψ_t(φ⁻¹ u)) = f(ψ_{τ₀}(x))`, read in the chart `φ` at `x`.
  set φ := extChartAt I x
  set G : E × ℝ → ℝ := fun p ↦ f (flowOf v p.2 (φ.symm p.1))
  have hφx : φ.symm (φ x) = x := extChartAt_to_inv x
  have hG : ContDiffAt ℝ n G (φ x, τ₀) := by
    rw [← contMDiffAt_iff_contDiffAt]
    have hsymm : ContMDiffAt 𝓘(ℝ, E) I n φ.symm (φ x) :=
      (contMDiffOn_extChartAt_symm x).contMDiffAt (extChartAt_target_mem_nhds x)
    have hfst : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) n Prod.fst (φ x, τ₀) :=
      contDiff_fst.contMDiff.contMDiffAt
    have hsnd : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ℝ) n Prod.snd (φ x, τ₀) :=
      contDiff_snd.contMDiff.contMDiffAt
    rw [← hφx] at hf
    exact hf.comp (φ x, τ₀) ((hcomplete.contMDiff_flowOf hn hv _).comp (φ x, τ₀)
      (hsnd.prodMk (hsymm.comp (φ x, τ₀) hfst)))
  -- The derivative of `G` in the time variable is `df(v) ≠ 0`.
  have hderiv : HasDerivAt (fun t ↦ G (φ x, t))
      (mvfderiv I f (flowOf v τ₀ x) (v (flowOf v τ₀ x))) τ₀ :=
    (Manifold.hasDerivAt_comp_curve (hf.mdifferentiableAt hn0)
      (hcomplete.isMIntegralCurve_flowOf (hv.of_le (mod_cast hn)) x τ₀)).congr_of_eventuallyEq
      (Eventually.of_forall fun t ↦ congrArg (fun y ↦ f (flowOf v t y)) hφx)
  have hinv : (fderiv ℝ G (φ x, τ₀) ∘L .inr ℝ E ℝ).IsInvertible := by
    have hpartial : HasFDerivAt (fun t ↦ G (φ x, t)) (fderiv ℝ G (φ x, τ₀) ∘L .inr ℝ E ℝ) τ₀ :=
      (hG.differentiableAt hn0).hasFDerivAt.comp τ₀ (hasFDerivAt_prodMk_right _ τ₀)
    rw [hpartial.unique hderiv.hasFDerivAt]
    exact ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hfv), by ext; simp⟩
  -- The implicit function solves `G(u, T u) = G(φ x, τ₀)` near `φ x`; read it back through `φ`.
  refine ⟨hG.implicitFunction hn0 hinv ∘ φ,
    (hG.contDiffAt_implicitFunction hn0 hinv).contMDiffAt.comp x contMDiffAt_extChartAt,
    hG.implicitFunction_apply_self hn0 hinv, ?_⟩
  have hφ : Tendsto φ (𝓝 x) (𝓝 (φ x)) := continuousAt_extChartAt x
  filter_upwards [hφ.eventually (hG.eventually_apply_implicitFunction hn0 hinv),
    extChartAt_source_mem_nhds (I := I) x] with x' h₁ h₂
  simpa only [G, Function.comp_apply, φ.left_inv h₂, hφx] using h₁

end IsCompleteVectorField

end TauCeti

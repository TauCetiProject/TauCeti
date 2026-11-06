/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Differential
public import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Continuity of form pullbacks in the weak Whitney topology

Let `α` be a smooth `k`-form on `M'` and `x` a point of `M`. The value at `x` of the pullback
`f^* α`, as an alternating map on `T_x M`, depends continuously on the smooth map
`f : M → M'` for the weak Whitney topology
(`TauCeti.SmoothForm.continuous_mpullback_contMDiffMap_apply`).

The value `(f^* α)_x = α_{f x} ∘ (d f_x)^k` involves the first derivative of `f` at `x` and the
value of `ω` at the moving point `f x`. Near a fixed map `f₀`, read both in the fixed chart at
`f₀ x`: the derivative becomes the coordinate differential of `f` from the chart at `x`, which is
continuous in `f` by `TauCeti.tendsto_fderivWithin_extChartAt`, and the form becomes its
coordinate expression, continuous on the chart target by
`TauCeti.IsSmoothForm.continuousOn_inChartAt`. Precomposition of alternating maps with linear
maps is jointly continuous, which assembles the two.

These pointwise first-jet tests are what make the diffeomorphisms preserving a form a closed
subset of the diffeomorphism group; see `TauCeti.Geometry.Diffeomorphism.FormStabilizer`.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1 (the weak topology).
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace TauCeti.SmoothForm

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The value at a fixed point of the pullback of a smooth form depends continuously on the
smooth map, for the weak Whitney topology on `C^∞⟮I, M; I', M'⟯`. -/
theorem continuous_mpullback_contMDiffMap_apply (α : SmoothForm I' M' F k) (x : M) :
    Continuous fun f : C^∞⟮I, M; I', M'⟯ ↦ (mpullback f f.contMDiff α).1 x := by
  refine continuous_iff_continuousAt.mpr fun f₀ ↦ ?_
  let y := f₀ x
  let φ := extChartAt I x
  let ψ := extChartAt I' y
  have hx : φ x ∈ φ.target := mem_extChartAt_target x
  have hf₀ : f₀ (φ.symm (φ x)) ∈ ψ.source := by
    rw [extChartAt_to_inv]
    exact mem_extChartAt_source y
  -- Maps near `f₀` still send `x` into the chart at `y = f₀ x`.
  have hsrc : ∀ᶠ f in 𝓝 f₀, f x ∈ ψ.source :=
    (ContMDiffMap.continuous_eval_const_manifoldWeakWhitney x).continuousAt.eventually_mem
      ((isOpen_extChartAt_source y).mem_nhds (mem_extChartAt_source y))
  -- Read the pullback in the source chart at `x` and the fixed target chart at `y`.
  have hrepr : ∀ f : C^∞⟮I, M; I', M'⟯, f x ∈ ψ.source →
      (mpullback f f.contMDiff α).1 x =
        (RoughForm.inChartAt α.1 y (ψ (f x))).compContinuousLinearMap
          (fderivWithin ℝ (ψ ∘ f ∘ φ.symm) φ.target (φ x)) := by
    intro f hf
    rw [coe_mpullback, RoughForm.mpullback_eq_compContinuousLinearMap α.1 y
      (f.contMDiff.mdifferentiable (by simp) x) hf,
      fderivWithin_congr_set (extChartAt_target_eventuallyEqSet (I := I) (x := x)).symm]
  -- The coordinate value of the form at the moving point `f x`.
  have hval : Tendsto (fun f : C^∞⟮I, M; I', M'⟯ ↦ RoughForm.inChartAt α.1 y (ψ (f x))) (𝓝 f₀)
      (𝓝 (RoughForm.inChartAt α.1 y (ψ (f₀ x)))) := by
    have hψ : Tendsto (fun f : C^∞⟮I, M; I', M'⟯ ↦ ψ (f x)) (𝓝 f₀) (𝓝[ψ.target] (ψ (f₀ x))) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨(continuousOn_extChartAt y (f₀ x) (mem_extChartAt_source y)).tendsto.comp
          (tendsto_nhdsWithin_iff.mpr
            ⟨(ContMDiffMap.continuous_eval_const_manifoldWeakWhitney x).continuousAt, hsrc⟩),
          hsrc.mono fun _ hf ↦ ψ.map_source hf⟩
    exact (α.isSmoothForm.continuousOn_inChartAt y _ (ψ.map_source (mem_extChartAt_source y)))
      |>.tendsto.comp hψ
  -- The coordinate differential of `f` at `x`.
  have hdiff : Tendsto (fun f : C^∞⟮I, M; I', M'⟯ ↦
      fderivWithin ℝ (ψ ∘ f ∘ φ.symm) φ.target (φ x)) (𝓝 f₀)
      (𝓝 (fderivWithin ℝ (ψ ∘ f₀ ∘ φ.symm) φ.target (φ x))) :=
    (tendsto_fderivWithin_extChartAt (by simp) hx hf₀).comp
      (tendsto_id.prodMk (tendsto_nhdsWithin_iff.mpr
        ⟨tendsto_const_nhds, Eventually.of_forall fun _ ↦ hx⟩))
  -- Precomposition of alternating maps with linear maps is jointly continuous.
  have hcomp := ((ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp
    continuous_snd).clm_apply continuous_fst).continuousAt.tendsto.comp (hval.prodMk_nhds hdiff)
  simp only [Function.comp_def, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply]
    at hcomp
  rw [ContinuousAt, hrepr f₀ (mem_extChartAt_source y)]
  refine hcomp.congr' ?_
  filter_upwards [hsrc] with f hf
  exact (hrepr f hf).symm

end TauCeti.SmoothForm

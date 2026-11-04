/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Differential
public import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart

/-!
# Continuity of pullback coefficients in the weak Whitney topology

Let `β` be a differential form on `N` whose coefficients are continuous, and fix a point `z` of the
target of a chart of `M`. The coordinate expression of the pullback `f^* β` at `z` depends
continuously on the `C^n` map `f : M → N`, `n ≥ 1`, for the weak Whitney topology
(`TauCeti.continuous_inChartAt_mpullback`). At the centre of the chart at `x` this coordinate
expression is the value `(f^* β)_x = β_(f x) ∘ (df_x × ⋯ × df_x)` itself, so the value of the
pullback at a fixed point depends continuously on the map.

Both the base point `f x` and the differential `df_x` move with `f`. The proof therefore reads them
in a fixed pair of charts: in a chart of `M` and a chart of `N` containing the image point, the
coordinate expression of `f^* β` is that of `β` precomposed with the coordinate derivative of `f`
(`TauCeti.RoughForm.inChartAt_mpullback_eq_inChartAt_compContinuousLinearMap`). The coordinate
expression of `β` is continuous on the chart target because `β` is a continuous section, and the
coordinate derivative is continuous in `f` by the definition of the weak Whitney topology
(`TauCeti.tendsto_fderivWithin_extChartAt`).

These first-jet tests show, for instance, that the diffeomorphisms preserving a given form are a
closed subset of the diffeomorphism group.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

namespace RoughForm

variable [IsManifold I 1 M] [IsManifold I' 1 N]

/-- The coordinate expression of a pullback `f^* β` in a chart at `x₀`, at a point `z` of the
chart target whose image under `f` lies in the chart at `y`, is the coordinate expression of `β`
in the chart at `y` precomposed with the coordinate derivative of `f`. -/
theorem inChartAt_mpullback_eq_inChartAt_compContinuousLinearMap (β : RoughForm I' N F k)
    {f : M → N} (x₀ : M) {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (hf : MDifferentiableAt I I' f ((extChartAt I x₀).symm z)) (y : N)
    (hfy : f ((extChartAt I x₀).symm z) ∈ (extChartAt I' y).source) :
    (mpullback I I' f β).inChartAt x₀ z =
      (β.inChartAt y (extChartAt I' y (f ((extChartAt I x₀).symm z)))).compContinuousLinearMap
        (fderivWithin ℝ (extChartAt I' y ∘ f ∘ (extChartAt I x₀).symm) (range I) z) := by
  have hw := mpullbackWithin_eq_compContinuousLinearMap β (f := f ∘ (extChartAt I x₀).symm)
    (s := range I) y hfy (hf.comp_mdifferentiableWithinAt _
      (mdifferentiableWithinAt_extChartAt_symm hz))
    (I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range x₀ hz))
  rw [Function.comp_apply] at hw
  rw [← hw, inChartAt_mpullback β f x₀ hz hf]
  ext v
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, mpullbackWithin_apply]
  -- Both sides are `β` at the same point, applied to `fun i ↦ L (v i)`, written once as `⇑L ∘ v`.
  rfl

end RoughForm

variable [LocallyCompactSpace E] [IsManifold I 1 M] [IsManifold I' 1 N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold I' n N]

/-- For a form `β` with continuous coefficients, the coordinate expression of its pullback
`f^* β` at a fixed point of a chart target depends continuously on the `C^n` map `f`, `n ≥ 1`,
for the weak Whitney topology. At the centre of the chart at `x` this coordinate expression is
the value `(f^* β)_x` (`TauCeti.RoughForm.inChartAt_chart_eq_iff`). -/
theorem continuous_inChartAt_mpullback {m : WithTop ℕ∞} {β : RoughForm I' N F k}
    (hβ : IsSmoothForm I' m β) (hn : 1 ≤ n) (x₀ : M) {z : E}
    (hz : z ∈ (extChartAt I x₀).target) :
    Continuous fun f : C^n⟮I, M; I', N⟯ ↦ (mpullback I I' f β).inChartAt x₀ z := by
  refine continuous_iff_continuousAt.2 fun f₀ ↦ ?_
  set x := (extChartAt I x₀).symm z
  set y := f₀ x
  have heval : ContinuousAt (fun f : C^n⟮I, M; I', N⟯ ↦ f x) f₀ :=
    (ContMDiffMap.continuous_eval_const_manifoldWeakWhitney x).continuousAt
  have hsource : ∀ᶠ f : C^n⟮I, M; I', N⟯ in 𝓝 f₀, f x ∈ (extChartAt I' y).source :=
    heval (extChartAt_source_mem_nhds y)
  -- The coordinate expression of `β` at the moving image point.
  have hcoeff : ContinuousAt
      (fun f : C^n⟮I, M; I', N⟯ ↦ β.inChartAt y (extChartAt I' y (f x))) f₀ := by
    refine ((hβ.continuousOn_inChartAt y) _ (mem_extChartAt_target y)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨(ContinuousAt.comp (g := extChartAt I' y)
        (f := fun f : C^n⟮I, M; I', N⟯ ↦ f x) (continuousAt_extChartAt y) heval).tendsto, ?_⟩)
    filter_upwards [hsource] with f hf using (extChartAt I' y).map_source hf
  -- The coordinate derivative of the moving map at `z`.
  have hderiv : ContinuousAt (fun f : C^n⟮I, M; I', N⟯ ↦
      fderivWithin ℝ (extChartAt I' y ∘ f ∘ (extChartAt I x₀).symm) (extChartAt I x₀).target z)
      f₀ :=
    (tendsto_fderivWithin_extChartAt hn hz (mem_extChartAt_source y)).comp
      (tendsto_id.prodMk (tendsto_const_nhdsWithin hz))
  have hkey : ∀ᶠ f : C^n⟮I, M; I', N⟯ in 𝓝 f₀, (mpullback I I' f β).inChartAt x₀ z =
      ContinuousAlternatingMap.compContinuousLinearMapCLM
        (fderivWithin ℝ (extChartAt I' y ∘ f ∘ (extChartAt I x₀).symm)
          (extChartAt I x₀).target z)
        (β.inChartAt y (extChartAt I' y (f x))) := by
    filter_upwards [hsource] with f hf
    rw [RoughForm.inChartAt_mpullback_eq_inChartAt_compContinuousLinearMap β x₀ hz
      (f.contMDiff.mdifferentiable (zero_lt_one.trans_le hn).ne' x) y hf,
      fderivWithin_congr_set (extChartAt_target_eventuallyEqSet_of_mem hz),
      ContinuousAlternatingMap.compContinuousLinearMapCLM_apply]
  exact (((ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.continuousAt).comp
    hderiv).clm_apply hcoeff).congr_of_eventuallyEq hkey

end TauCeti

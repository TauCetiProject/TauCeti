/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Evaluation
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.WithSeminorms
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Joint continuity of coordinate differentials

The first coordinate derivative varies continuously with the map and the chart point in the
weak Whitney topology. The derivative is taken within the extended chart target, including
boundary and corner points. This is the operator-valued form of joint chart-jet evaluation,
used when inverting the differential of a diffeomorphism. The proof specializes
`ContMDiffMap.tendsto_iteratedFDerivWithin_extChartAt` to order one and uses Mathlib's
`continuousMultilinearCurryFin1` to obtain a continuous linear operator.

First coordinate derivatives, as linear operators, and second coordinate derivatives, as bilinear
operators, converge uniformly on compact subsets of the chart target
(`TauCeti.tendstoUniformlyOn_fderivWithin_extChartAt`,
`TauCeti.tendstoUniformlyOn_fderivWithin_fderivWithin_extChartAt`). This is the form of `C²`
closeness used for the persistence of nondegenerate critical points.

For `1 ≤ n` and a point `x` of `M`, taking the derivative at `x` of vector-valued `C^n` maps is
therefore a continuous linear map `h ↦ dh_x : C^n(M, F) →L T_x M →L F` for the weak Whitney
topology (`ContMDiffMap.mvfderivCLM`). This holds on manifolds with boundary or corners and in any
regularity `n ≥ 1`, including the finite orders `C^k` on which the Banach space structure of a
compact manifold lives.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [LocallyCompactSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]

omit [LocallyCompactSpace E] [IsManifold I n M] in
/-- On the extended chart target, the first iterated derivative is the differential, read through
`continuousMultilinearCurryFin1`. -/
private theorem continuousMultilinearCurryFin1_iteratedFDerivWithin_extChartAt_target {x : M}
    (f : E → F) {w : E} (hw : w ∈ (extChartAt I x).target) :
    continuousMultilinearCurryFin1 𝕜 E F
        (iteratedFDerivWithin 𝕜 1 f (extChartAt I x).target w) =
      fderivWithin 𝕜 f (extChartAt I x).target w := by
  ext v
  exact iteratedFDerivWithin_one_apply ((uniqueDiffOn_extChartAt_target x) w hw) _

/-- Coordinate differentials vary continuously in the map and the chart point. -/
theorem tendsto_fderivWithin_extChartAt {f₀ : C^n⟮I, M; J, N⟯} {x : M} {y : N} {w₀ : E}
    (hn : 1 ≤ n) (hw₀ : w₀ ∈ (extChartAt I x).target)
    (hf₀ : f₀ ((extChartAt I x).symm w₀) ∈ (extChartAt J y).source) :
    Tendsto (fun p : C^n⟮I, M; J, N⟯ × E ↦
      fderivWithin 𝕜 (extChartAt J y ∘ p.1 ∘ (extChartAt I x).symm)
        (extChartAt I x).target p.2)
      (𝓝 f₀ ×ˢ 𝓝[(extChartAt I x).target] w₀)
      (𝓝 (fderivWithin 𝕜 (extChartAt J y ∘ f₀ ∘ (extChartAt I x).symm)
        (extChartAt I x).target w₀)) := by
  have h := (continuousMultilinearCurryFin1 𝕜 E F).continuous.continuousAt.tendsto.comp
    (ContMDiffMap.tendsto_iteratedFDerivWithin_extChartAt hw₀ hf₀ hn)
  rw [continuousMultilinearCurryFin1_iteratedFDerivWithin_extChartAt_target _ hw₀] at h
  apply h.congr'
  filter_upwards [prod_mem_prod (Filter.univ_mem : Set.univ ∈ 𝓝 f₀)
    self_mem_nhdsWithin] with p hp
  exact continuousMultilinearCurryFin1_iteratedFDerivWithin_extChartAt_target _ hp.2

omit [LocallyCompactSpace E] in
/-- On a compact subset of a source chart target which `f₀` maps into a target chart, the
coordinate differentials of maps near `f₀` converge uniformly to those of `f₀`. -/
theorem tendstoUniformlyOn_fderivWithin_extChartAt {f₀ : C^n⟮I, M; J, N⟯} {x : M} {y : N}
    {C : Set E} (hn : 1 ≤ n) (hC : IsCompact C) (hCx : C ⊆ (extChartAt I x).target)
    (hCy : ∀ w ∈ C, f₀ ((extChartAt I x).symm w) ∈ (extChartAt J y).source) :
    TendstoUniformlyOn (fun (f : C^n⟮I, M; J, N⟯) w ↦
        fderivWithin 𝕜 (extChartAt J y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x).target w)
      (fun w ↦ fderivWithin 𝕜 (extChartAt J y ∘ f₀ ∘ (extChartAt I x).symm)
        (extChartAt I x).target w) (𝓝 f₀) C := by
  have hc (f : E → F) {w : E} (hw : w ∈ C) :=
    continuousMultilinearCurryFin1_iteratedFDerivWithin_extChartAt_target f (hCx hw)
  exact (((continuousMultilinearCurryFin1 𝕜 E F).isometry.uniformContinuous.comp_tendstoUniformlyOn
    (ContMDiffMap.tendstoUniformlyOn_iteratedFDerivWithin_extChartAt hC hCx hCy hn)).congr
      (Eventually.of_forall fun _ _ hw ↦ hc _ hw)).congr_right fun _ hw ↦ hc _ hw

omit [LocallyCompactSpace E] in
/-- On a compact subset of a source chart target which `f₀` maps into a target chart, the second
coordinate derivatives of maps near `f₀` converge uniformly to those of `f₀`. -/
theorem tendstoUniformlyOn_fderivWithin_fderivWithin_extChartAt {f₀ : C^n⟮I, M; J, N⟯} {x : M}
    {y : N} {C : Set E} (hn : 2 ≤ n) (hC : IsCompact C) (hCx : C ⊆ (extChartAt I x).target)
    (hCy : ∀ w ∈ C, f₀ ((extChartAt I x).symm w) ∈ (extChartAt J y).source) :
    TendstoUniformlyOn (fun (f : C^n⟮I, M; J, N⟯) w ↦
        fderivWithin 𝕜 (fderivWithin 𝕜 (extChartAt J y ∘ f ∘ (extChartAt I x).symm)
          (extChartAt I x).target) (extChartAt I x).target w)
      (fun w ↦ fderivWithin 𝕜 (fderivWithin 𝕜 (extChartAt J y ∘ f₀ ∘ (extChartAt I x).symm)
        (extChartAt I x).target) (extChartAt I x).target w) (𝓝 f₀) C := by
  -- The second derivative is the order-two iterated derivative, curried twice.
  let c := (ContinuousLinearMap.compL 𝕜 E (E [×1]→L[𝕜] F) (E →L[𝕜] F)
      (continuousMultilinearCurryFin1 𝕜 E F).toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin 2 ↦ E) F).toContinuousLinearEquiv :
      (E [×2]→L[𝕜] F) →L[𝕜] E →L[𝕜] E [×1]→L[𝕜] F)
  have hc (f : E → F) {w : E} (hw : w ∈ (extChartAt I x).target) :
      c (iteratedFDerivWithin 𝕜 2 f (extChartAt I x).target w) =
        fderivWithin 𝕜 (fderivWithin 𝕜 f (extChartAt I x).target) (extChartAt I x).target w := by
    ext v v'
    rw [← iteratedFDerivWithin_two_apply' f (uniqueDiffOn_extChartAt_target x) hw v v']
    simp [c]
  exact ((c.uniformContinuous.comp_tendstoUniformlyOn
    (ContMDiffMap.tendstoUniformlyOn_iteratedFDerivWithin_extChartAt hC hCx hCy hn)).congr
      (Eventually.of_forall fun f w hw ↦ hc _ (hCx hw))).congr_right fun w hw ↦ hc _ (hCx hw)

end TauCeti

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ∞ω} [IsManifold I n M]

/-- The **derivative at `x`** of vector-valued `C^n` maps, `1 ≤ n`, as a continuous linear map for
the weak Whitney topology. -/
noncomputable def mvfderivCLM (hn : 1 ≤ n) (x : M) :
    C^n⟮I, M; 𝓘(𝕜, F), F⟯ →L[𝕜] TangentSpace I x →L[𝕜] F where
  toFun f := mvfderiv I f x
  map_add' f g := mvfderiv_add (f.contMDiff.mdifferentiableAt (zero_lt_one.trans_le hn).ne')
    (g.contMDiff.mdifferentiableAt (zero_lt_one.trans_le hn).ne')
  map_smul' c f := TauCeti.mvfderiv_const_smul_field f x c
  cont := by
    refine (continuous_congr fun f : C^n⟮I, M; 𝓘(𝕜, F), F⟯ ↦
      TauCeti.mvfderiv_eq_fderivWithin_extChartAt_target
        (f.contMDiff.mdifferentiableAt (zero_lt_one.trans_le hn).ne')).2
      (continuous_iff_continuousAt.2 fun f₀ ↦ ?_)
    -- The coordinate differentials converge uniformly on the compact set `{φ x}`.
    have h := (TauCeti.tendstoUniformlyOn_fderivWithin_extChartAt (J := 𝓘(𝕜, F)) (y := f₀ x)
      (f₀ := f₀) hn isCompact_singleton (singleton_subset_iff.2 (mem_extChartAt_target x))
      (fun _ _ ↦ by simp)).tendsto_at (mem_singleton _)
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] at h
    -- `ContinuousAt` is this limit, with `TangentSpace I x` read as the model space `E`.
    exact h

/-- The derivative at `x` of a `C^n` map. -/
@[simp]
theorem mvfderivCLM_apply (hn : 1 ≤ n) (x : M) (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    mvfderivCLM hn x f = mvfderiv I f x :=
  (rfl)

end ContMDiffMap

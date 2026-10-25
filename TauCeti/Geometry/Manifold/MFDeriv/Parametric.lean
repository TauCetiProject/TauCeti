/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Analysis.Calculus.ParametricFDeriv

/-!
# Parametric families of functions on a manifold

Let `F : 𝕜 → M → F'` be a one-parameter family of functions from a manifold `M` to a normed space,
jointly smooth on `𝕜 × M`. This file proves the two facts needed to differentiate expressions
built from `F` and its manifold differentials in the parameter:

* the parameter derivative `y ↦ ∂ᵣ F (t, y)` at a fixed parameter `t` loses one derivative of
  joint regularity;
* for a jointly `C²` family, the parameter derivative and the manifold differential commute:
  `∂ₜ (d (F t) x v) = d (∂ₜ F t) x v`.

The second fact is the manifold form of the symmetry of mixed partial derivatives. It is read in
the extended chart at `x`, within the range of the model with corners, so it also holds at
boundary points.

## Main results

* `TauCeti.Manifold.contMDiffAt_deriv_of_contMDiffAt_uncurry`: the parameter derivative of a
  jointly `C^n` family is `C^m` for `m + 1 ≤ n`.
* `TauCeti.Manifold.hasDerivAt_mvfderiv_apply`: the parameter derivative of the differential of a
  jointly `C²` family is the differential of its parameter derivative.
-/

public section

open Function Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {F : 𝕜 → M → F'} {t : 𝕜} {x : M} {m n : WithTop ℕ∞}

/-- A jointly `C^n` family of functions on a manifold, read in the extended chart at `x`, is
`C^n` within the product of the parameter space and the range of the model. -/
private theorem contDiffWithinAt_extChartAt_symm_of_contMDiffAt_uncurry
    (hF : ContMDiffAt (𝓘(𝕜).prod I) 𝓘(𝕜, F') n (uncurry F) (t, x)) :
    ContDiffWithinAt 𝕜 n (fun p : 𝕜 × E ↦ F p.1 ((extChartAt I x).symm p.2))
      (univ ×ˢ range I) (t, extChartAt I x x) := by
  -- The chart reading of `uncurry F` at `(t, x)` is this map, up to unfolding the product chart.
  have h : ContDiffWithinAt 𝕜 n (fun p : 𝕜 × E ↦ F p.1 ((extChartAt I x).symm p.2))
      (range (𝓘(𝕜).prod I)) (extChartAt (𝓘(𝕜).prod I) (t, x) (t, x)) :=
    (contMDiffAt_iff.mp hF).2
  rw [ModelWithCorners.range_prod] at h
  simpa [extChartAt_prod] using h

variable [IsManifold I 1 M]

/-- **Regularity of the parameter derivative.** If a family `F : 𝕜 → M → F'` is jointly `C^n` at
`(t, x)`, then its parameter derivative `y ↦ ∂ᵣ F (r, y)` at `r = t` is `C^m` at `x` for every
`m` with `m + 1 ≤ n`. -/
theorem contMDiffAt_deriv_of_contMDiffAt_uncurry
    (hF : ContMDiffAt (𝓘(𝕜).prod I) 𝓘(𝕜, F') n (uncurry F) (t, x)) (hmn : m + 1 ≤ n) :
    ContMDiffAt I 𝓘(𝕜, F') m (fun y ↦ deriv (fun r ↦ F r y) t) x := by
  have hswap : ContMDiffAt (I.prod 𝓘(𝕜)) 𝓘(𝕜, F') n (uncurry fun y r ↦ F r y) (x, t) :=
    hF.comp (x, t) (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have h := (hswap.mfderiv (fun y r ↦ F r y) (fun _ ↦ t) contMDiffAt_const hmn).clm_apply
    (contMDiffAt_const (c := (1 : 𝕜)))
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
  dsimp only
  -- Between model spaces, tangent coordinates are trivial; `erw` sees through the tangent spaces
  -- of `𝕜` and `F'`, which are the model spaces themselves.
  erw [inTangentCoordinates_model_space]
  rw [mfderiv_eq_fderiv, ← fderiv_apply_one_eq_deriv]
  rfl

/-- **Mixed derivatives on a manifold.** If a family `F : 𝕜 → M → F'` is jointly `C²` at `(t, x)`
(analytic, over a field other than `ℝ` or `ℂ`), then the parameter derivative at `t` of the
differential of `F r` at `x`, applied to `v`, is the differential at `x` of the parameter
derivative `y ↦ ∂ᵣ F (r, y)` at `r = t`, applied to `v`. -/
theorem hasDerivAt_mvfderiv_apply
    (hF : ContMDiffAt (𝓘(𝕜).prod I) 𝓘(𝕜, F') (minSmoothness 𝕜 2) (uncurry F) (t, x))
    (v : TangentSpace I x) :
    HasDerivAt (fun r ↦ mvfderiv I (F r) x v)
      (mvfderiv I (fun y ↦ deriv (fun r ↦ F r y) t) x v) t := by
  have h1 : (1 : WithTop ℕ∞) ≤ minSmoothness 𝕜 2 := le_trans (by norm_num) le_minSmoothness
  have h2 : (1 : WithTop ℕ∞) + 1 ≤ minSmoothness 𝕜 2 := le_trans (by norm_num) le_minSmoothness
  -- The statement read in the extended chart at `x`, within the range of the model.
  have hchart := hasDerivAt_fderivWithin_slice
    (contDiffWithinAt_extChartAt_symm_of_contMDiffAt_uncurry hF) I.uniqueDiffOn
    (I.range_subset_closure_interior (mem_range_self _)) (mem_range_self _)
  have hv := hchart.clm_apply (hasDerivAt_const (x := t) (c := tangentSpaceCastModel I x v))
  simp only [map_zero, add_zero] at hv
  have hG : MDifferentiableAt I 𝓘(𝕜, F') (fun y ↦ deriv (fun r ↦ F r y) t) x :=
    (contMDiffAt_deriv_of_contMDiffAt_uncurry hF h2).mdifferentiableAt one_ne_zero
  rw [hG.mvfderiv]
  refine hv.congr_of_eventuallyEq ?_
  -- Near `t`, each `F r` is differentiable at `x`, so its differential is read in the chart.
  have hnear := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp (hF.of_le h1)
  filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually hnear]
    with r hr
  have hr' : MDifferentiableAt I 𝓘(𝕜, F') (F r) x :=
    (hr.comp x (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt one_ne_zero
  rw [hr'.mvfderiv]
  -- The chart reading of `F r` is `F r ∘ (extChartAt I x).symm`, since the chart of the target
  -- model space is the identity.
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp]
  -- `tangentSpaceCastModel I x` is the identity of `E`, the tangent space at `x`.
  rfl

end TauCeti.Manifold

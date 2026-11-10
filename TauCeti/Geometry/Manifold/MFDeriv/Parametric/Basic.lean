/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Analysis.Calculus.ParametricFDeriv

/-!
# Parametric families of functions on a manifold

Let `F : 𝕜 → M → F'` be a one-parameter family of functions from a manifold `M` to a normed space,
jointly smooth on `𝕜 × M`. This file proves the two facts needed to differentiate expressions
built from `F` and its manifold differentials in the parameter:

* the parameter derivative `y ↦ ∂ᵣ F (t, y)` at a fixed parameter `t` loses one derivative of
  joint regularity, and so does the field of velocities of the curves of a two-parameter family
  of points of `M`;
* for a jointly `C²` family, the parameter derivative and the manifold differential commute:
  `∂ₜ (d (F t) x v) = d (∂ₜ F t) x v`.

More generally, for a family `G : P → M → F'` parametrized by a manifold `P` and jointly `C^n`,
the differential `d (G r) x` at a fixed point `x`, as a covector-valued function of the parameter
`r`, loses one derivative of joint regularity. This is the regularity input for mixed second
derivatives of functions on a product of manifolds.

The second fact is the manifold form of the symmetry of mixed partial derivatives. It is read in
the extended chart at `x`, within the range of the model with corners, so it also holds at
boundary points.

## Main results

* `TauCeti.Manifold.contDiffAt_extChartAt_family`: a jointly `C^n` family of maps of `M` fixing
  `x` is jointly `C^n` when read in the chart at `x`.
* `TauCeti.Manifold.eventuallyEq_extChartAt_family_of_eq_id`: a family of maps which is the
  identity near `x` at time `t` is, read in the chart at `x`, the identity near the image of `x`.
* `TauCeti.Manifold.contMDiffAt_deriv_of_contMDiffAt_uncurry`: the parameter derivative of a
  jointly `C^n` family is `C^m` for `m + 1 ≤ n`.
* `ContMDiffAt.contMDiffAt_curveVelocity_snd`: for a jointly `C^n` map `f : 𝕜 → 𝕜 → M`, the
  velocities of the curves `f q`, as a map of both parameters to the tangent bundle, are `C^m`
  for `m + 1 ≤ n`.
* `TauCeti.Manifold.hasDerivAt_mvfderiv_apply`: the parameter derivative of the differential of a
  jointly `C²` family is the differential of its parameter derivative.
* `TauCeti.Manifold.contMDiffAt_mvfderiv_of_contMDiffAt_uncurry`: the differential at a fixed point
  of a jointly `C^n` family parametrized by a manifold is `C^m` in the parameter for `m + 1 ≤ n`.
* `TauCeti.Manifold.contMDiff_mfderiv_apply_one_zero`: the velocity `q ↦ dΓ_q (1, 0)` of a `C^n`
  map `Γ` out of `𝕜 × M` is a `C^m` section along it for `m + 1 ≤ n`.
-/

public section

open Bundle Function Set
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

/-- A family of maps `ψᵤ` of `M` which is jointly `C^n` at `(t, x)` and fixes `x` at time `t` is,
read in the chart at `x`, a jointly `C^n` map of `𝕜 × E` at `(t, extChartAt I x x)`. -/
theorem contDiffAt_extChartAt_family [I.Boundaryless] {ψ : 𝕜 → M → M} (hid : ψ t x = x)
    (hψ : ContMDiffAt (𝓘(𝕜).prod I) I n (uncurry ψ) (t, x)) :
    ContDiffAt 𝕜 n (fun p : 𝕜 × E ↦ extChartAt I x (ψ p.1 ((extChartAt I x).symm p.2)))
      (t, extChartAt I x x) := by
  have hsymm : ContMDiffAt 𝓘(𝕜, E) I n (extChartAt I x).symm (extChartAt I x x) := by
    have h := contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := n) x
    rwa [I.range_eq_univ, contMDiffWithinAt_univ] at h
  have hpair : ContMDiffAt (𝓘(𝕜).prod 𝓘(𝕜, E)) (𝓘(𝕜).prod I) n
      (fun p : 𝕜 × E ↦ (p.1, (extChartAt I x).symm p.2)) (t, extChartAt I x x) :=
    contMDiffAt_fst.prodMk (ContMDiffAt.comp (t, extChartAt I x x) hsymm contMDiffAt_snd)
  have hcomp := (contMDiffAt_extChartAt (I := I) (n := n) (x := x)).comp_of_eq
    (hψ.comp_of_eq hpair (Prod.ext rfl (extChartAt_to_inv x))) (by
      simp only [Function.comp_apply, uncurry_apply_pair, extChartAt_to_inv]
      exact hid)
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod, contMDiffAt_iff_contDiffAt] at hcomp
  exact hcomp

/-- A family of maps which is the identity near `x` at time `t`, read in the chart at `x`, is the
identity near the image of `x` at time `t`. -/
theorem eventuallyEq_extChartAt_family_of_eq_id [I.Boundaryless] {ψ : 𝕜 → M → M}
    (hid : ∀ᶠ y in 𝓝 x, ψ t y = y) :
    (fun z ↦ extChartAt I x (ψ t ((extChartAt I x).symm z))) =ᶠ[𝓝 (extChartAt I x x)] id := by
  have hid' : ∀ᶠ z in 𝓝 (extChartAt I x x), ψ t ((extChartAt I x).symm z) =
      (extChartAt I x).symm z :=
    (continuousAt_extChartAt_symm x).tendsto.eventually (p := fun y ↦ ψ t y = y)
      (by rwa [extChartAt_to_inv])
  filter_upwards [extChartAt_target_mem_nhds x, hid'] with z hz hz'
  simp only [hz', id_eq]
  exact (extChartAt I x).right_inv hz

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

/-- **Regularity of the velocity field of a two-parameter family.** If `f : 𝕜 → 𝕜 → M` is jointly
`C^n` at `(u, v)`, then the velocities of its curves `f q`, as a map of both parameters to the
tangent bundle, are `C^m` at `(u, v)` for every `m` with `m + 1 ≤ n`. -/
theorem _root_.ContMDiffAt.contMDiffAt_curveVelocity_snd {f : 𝕜 → 𝕜 → M} {u v : 𝕜}
    (hf : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I n (fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) (u, v)) (hmn : m + 1 ≤ n) :
    ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I.tangent m
      (fun z : 𝕜 × 𝕜 ↦ TotalSpace.mk' E (f z.1 z.2) (curveVelocity I (f z.1) z.2)) (u, v) := by
  let ι : 𝕜 × 𝕜 → TangentBundle 𝓘(𝕜, 𝕜 × 𝕜) (𝕜 × 𝕜) := fun z ↦ TotalSpace.mk' (𝕜 × 𝕜) z (0, 1)
  have hι : ContMDiff 𝓘(𝕜, 𝕜 × 𝕜) 𝓘(𝕜, 𝕜 × 𝕜).tangent m ι := by
    intro z
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    refine (contMDiffAt_const (c := ((0 : 𝕜), (1 : 𝕜)))).congr_of_eventuallyEq ?_
    filter_upwards with r
    rw [trivializationAt_model_space_apply]
  have htangent := (hf.contMDiffAt_tangentMap (X := ι (u, v)) hmn).comp (u, v) (hι (u, v))
  have hone : (1 : WithTop ℕ∞) ≤ n := le_trans le_add_self hmn
  have hnear : ∀ᶠ z in 𝓝 (u, v), MDifferentiableAt 𝓘(𝕜, 𝕜 × 𝕜) I (fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) z :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp (hf.of_le hone)).mono fun z hz ↦
      hz.mdifferentiableAt one_ne_zero
  refine htangent.congr_of_eventuallyEq ?_
  filter_upwards [hnear] with z hz
  simp only [Function.comp_apply, ι, tangentMap, curveVelocity_eq_mfderiv_snd hz]

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

section ManifoldParameter

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  [IsManifold J 1 P] {G : P → M → F'} {p : P}

/-- **Regularity of the differential in a manifold parameter.** If a family `G : P → M → F'` is
jointly `C^n` at `(p, x)`, then the differential `d (G r) x`, as a function of `r` with values in
the covectors `E →L[𝕜] F'` on the model space of `T_x M`, is `C^m` at `p` for every `m` with
`m + 1 ≤ n`. -/
theorem contMDiffAt_mvfderiv_of_contMDiffAt_uncurry
    (hG : ContMDiffAt (J.prod I) 𝓘(𝕜, F') n (uncurry G) (p, x)) (hmn : m + 1 ≤ n) :
    ContMDiffAt (M' := E →L[𝕜] F') J 𝓘(𝕜, E →L[𝕜] F') m (fun r ↦ mvfderiv I (G r) x) p := by
  refine (hG.mfderiv G (fun _ ↦ x) contMDiffAt_const hmn).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r ↦ ?_)
  ext v
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates]
  -- With the base point of `M` fixed, the source coordinate change is the derivative of the inverse
  -- chart at its own centre, which is the identity, and the target coordinate change is that of the
  -- model space `F'`. `erw` sees through the tangent spaces of `E` and `F'`, which are the model
  -- spaces themselves.
  erw [TangentBundle.symmL_trivializationAt (mem_chart_source H x),
    mfderivWithin_range_extChartAt_symm, TangentBundle.continuousLinearMapAt_model_space]
  rfl

end ManifoldParameter

section Velocity

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J 1 N] {Γ : 𝕜 × M → N}

/-- The velocity `q ↦ dΓ_q (1, 0)` of a `C^n` map out of `𝕜 × M` is a `C^m` section along it when
`m + 1 ≤ n`. -/
theorem contMDiff_mfderiv_apply_one_zero
    (hΓ : ContMDiff (𝓘(𝕜, 𝕜).prod I) J n Γ) (hmn : m + 1 ≤ n) :
    ContMDiff (𝓘(𝕜, 𝕜).prod I) J.tangent m fun q =>
      TotalSpace.mk' E' (Γ q) (mfderiv (𝓘(𝕜, 𝕜).prod I) J Γ q ((1 : 𝕜), (0 : E))) := by
  have hclock : ContMDiff 𝓘(𝕜, 𝕜) 𝓘(𝕜, 𝕜).tangent m
      (fun s : 𝕜 => (⟨s, (1 : 𝕜)⟩ : TangentBundle 𝓘(𝕜, 𝕜) 𝕜)) :=
    contMDiff_vectorSpace_iff_contDiff.2 contDiff_const
  have hunit : ContMDiff (𝓘(𝕜, 𝕜).prod I) (𝓘(𝕜, 𝕜).prod I).tangent m
      (fun q : 𝕜 × M => (⟨q, ((1 : 𝕜), (0 : E))⟩ : TangentBundle (𝓘(𝕜, 𝕜).prod I) (𝕜 × M))) :=
    (contMDiff_equivTangentBundleProd_symm (I := 𝓘(𝕜, 𝕜)) (M := 𝕜) (I' := I) (M' := M)).comp
      ((hclock.comp contMDiff_fst).prodMk
        ((Bundle.contMDiff_zeroSection 𝕜 (TangentSpace I : M → Type _)).comp contMDiff_snd))
  exact (hΓ.contMDiff_tangentMap hmn).comp hunit

end Velocity

end TauCeti.Manifold

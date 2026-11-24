/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Geometry.Manifold.ExtChartAt
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import TauCeti.Analysis.Calculus.FDeriv.Comp

/-!
# Manifold derivatives and regularity read in charts

A map `f : M → M'` with manifold derivative `f'` at `x'` becomes, in the extended charts centred at
any `x` and `y` whose sources contain `x'` and `f x'`, a map between model vector spaces. Its
Fréchet derivative within `range I` is `f'` conjugated by the derivatives of the two charts.
Mathlib's `mdifferentiableAt_iff_of_mem_source` records differentiability in such charts, but not
the value of the derivative. Change-of-variables arguments on a manifold need that value, because
they integrate the absolute Jacobian determinant of `f` read in fixed charts.

For a map into a normed space on a boundaryless manifold, the coordinate expression in the
preferred extended chart at `x` is an honest function on the model space, `C^n` or differentiable
whenever `f` is, and its Fréchet derivative at the chart image of `x` is the vector-valued
manifold derivative `mvfderiv I f x`. This is how critical points defined through the preferred
chart, as in Morse theory, are identified with the zeros of `mvfderiv`.

## Main results

* **Preferred charts without atlas smoothness**:
  - `ContinuousAt.hasMFDerivAt_of_writtenInExtChartAt_eventuallyEq` and
    `TauCeti.Manifold.hasMFDerivAt_of_hasFDerivWithinAt_extChartAt_target`: infer `HasMFDerivAt`
    from local linearity or a Fréchet derivative on the chart target (including corners).
  - `ContDiffAt.contMDiffAt_extChartAt_symm_comp_extChartAt` and
    `ContMDiffAt.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint`: transfer `C^n` regularity
    between model spaces and manifolds (into a boundaryless target, or at an interior point).
  - `TauCeti.Manifold.mdifferentiableAt_iff_of_chartAt_eq` and
    `TauCeti.Manifold.mfderiv_eq_of_chartAt_eq`: differentiability and `mfderiv` at a point depend
    only on its preferred chart.
  - `TauCeti.hasMFDerivAt_extChartAt_self`, `TauCeti.mfderiv_extChartAt_eq_id`,
    `TauCeti.hasMFDerivWithinAt_extChartAt_symm_self`,
    `TauCeti.mfderivWithin_extChartAt_symm_eq_id`, and `TauCeti.hasMFDerivAt_extChartAt_symm_self`:
    the preferred extended chart and its inverse have the identity as their derivative at its
    centre.
  - `TauCeti.writtenInExtChartAt_self_eq` and `MDifferentiableAt.mfderiv_eq_fderivWithin_self`: a
    map of model spaces reads in charts as `I' ∘ g ∘ I.symm`, with `mfderiv` its derivative on
    `range I`.
* **Charts of the maximal atlas**:
  - `TauCeti.mdifferentiable_of_mem_maximalAtlas` and `TauCeti.isInvertible_mvfderiv_extend`:
    differentiability and invertibility of the differential for charts of the `C¹` maximal atlas.
  - `ModelWithCorners.det_fderiv_extendCoordChange_ne_zero`,
    `OpenPartialHomeomorph.mdifferentiableAt_extend_symm_of_mem_interior`,
    `OpenPartialHomeomorph.mfderivWithin_extend_symm_of_mem_interior`, and
    `OpenPartialHomeomorph.contDiffOn_extend_comp`: nonvanishing Jacobian determinant, interior
    differentiability, and `C^n` coordinate-expression regularity on chart overlaps.
* **Boundaryless manifolds**:
  - `ContMDiffAt.contDiffAt_writtenInExtChartAt`,
    `MDifferentiableAt.differentiableAt_writtenInExtChartAt`,
    `MDifferentiableAt.mfderiv_eq_fderiv_extChartAt_conj`, and
    `MDifferentiableAt.tangentSpaceCastModel_mfderiv_apply`: regularity and derivative formulas
    for maps between manifolds in preferred extended charts, with product-chart forms
    `ContMDiffAt.contDiffAt_comp_prod_extChartAt_symm` and
    `MDifferentiableAt.differentiableAt_comp_prod_extChartAt_symm`.
  - `TauCeti.contMDiffAt_iff_contDiffAt_comp_extChartAt_symm`,
    `TauCeti.contMDiffAt_iff_contDiffAt_comp_extend_symm`,
    `ContMDiffAt.contDiffAt_comp_extChartAt_symm`,
    `MDifferentiableAt.differentiableAt_comp_extChartAt_symm`, and
    `TauCeti.mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm`: `C^n` and
    differentiability equivalences for maps into a normed space in preferred or maximal-atlas
    charts.
  - `TauCeti.mvfderiv_eq_fderiv_comp_extChartAt_symm`,
    `TauCeti.mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm`,
    `TauCeti.mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero`,
    `TauCeti.mvfderiv_comp_tangentSpaceCastModel_symm`,
    `TauCeti.mvfderiv_apply_eq_fderiv_comp_extChartAt_symm`,
    `TauCeti.range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm`, and
    `TauCeti.injective_fderiv_comp_extChartAt_symm_iff`: identify `mvfderiv` with the Fréchet
    derivative of the coordinate expression and transfer zeros, range, and injectivity.
* **Arbitrary charts on `C¹` and `C^n` manifolds**:
  - `TauCeti.hasFDerivWithinAt_extChartAt_coordChange`,
    `TauCeti.mfderivWithin_extChartAt_symm_of_subset`, and
    `TauCeti.tangentCoordChange_tangentCoordChange`: derivatives of coordinate changes, inverse
    charts on subsets, and inverse tangent coordinate changes.
  - `TauCeti.mfderiv_eq_fderiv_comp_mfderiv_extChartAt`,
    `TauCeti.fderiv_comp_extChartAt_symm_injective`,
    `TauCeti.mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm_eq_zero`,
    `TauCeti.mvfderiv_eq_iff_fderiv_comp_extChartAt_symm_eq`,
    `TauCeti.eventually_mfderiv_eq_zero_iff_extChartAt_symm`, and
    `TauCeti.exists_norm_fderiv_comp_extend_symm_le_mul_norm_fderiv_comp_extChartAt_symm`: compare
    differentials, zeros, injectivity, critical points, and norms across arbitrary charts for
    maps into a normed space.
  - `TauCeti.fderivWithin_comp_extChartAt_symm`,
    `ContMDiffOn.exists_forall_norm_mvfderiv_le_mul_norm`,
    `HasMFDerivAt.hasFDerivAt_extChartAt_comp`, `ContinuousAt.fderiv_extChartAt_comp_apply`, and
    `ContinuousAt.symmL_fderiv_extChartAt_comp_apply`: chart-coordinate derivatives and compact-set
    bounds for maps out of or into a manifold.
  - `HasMFDerivAt.hasFDerivWithinAt_of_mem_source`,
    `ContinuousAt.fderivWithin_extChartAt_comp_extChartAt_symm`,
    `ContinuousAt.fderivWithin_extChartAt_comp_extChartAt_symm_eq_zero_iff`, and
    `MDifferentiableAt.differentiableWithinAt_and_fderivWithin_extChartAt_comp_eq_zero`:
    coordinate derivatives within `range I` and zero-differential transfer for maps between `C¹`
    manifolds.
  - `ContMDiffAt.contDiffAt_extChartAt_comp_extChartAt_symm`,
    `TauCeti.contDiffAt_ext_coord_change`, `TauCeti.contDiffAt_ext_coord_change_extChartAt`, and
    `TauCeti.isOpen_mem_contDiffOn_mapsTo_writtenInExtChartAt`: `C^n` regularity of maps,
    coordinate changes, and open coordinate domains on `C^n` manifolds.
* **Self-model, composite, and `M × 𝕜` charts**:
  - `ContMDiffAt.contDiffAt_comp_chartAt_symm`, `MDifferentiableAt.differentiableAt_chartAt_comp`,
    `ContinuousAt.fderiv_chartAt_comp`, `TauCeti.fderiv_comp_chartAt_symm`,
    `TauCeti.ker_mvfderiv_eq_ker_fderiv_comp_chartAt_symm`,
    `TauCeti.mdifferentiableAt_of_differentiableAt_comp_symm`,
    `TauCeti.eventually_differentiableAt_chart_comp_of_eventually_mdifferentiableAt`, and
    `TauCeti.eventually_mdifferentiableAt_chart_symm_comp_of_eventually_differentiableAt`:
    regularity, derivatives, kernels, and product-chart differentiability for manifolds modelled on
    their model space.
  - `TauCeti.writtenInExtChartAt_chartAt_comp_eventuallyEq`, `TauCeti.hasMFDerivAt_chartAt_comp`,
    and `TauCeti.contMDiffAt_chartAt_comp`: preferred charts of a composite charted space read as
    the identity near their centre.
  - `TauCeti.fderiv_comp_extChartAt_symm_apply_zero_one`,
    `TauCeti.deriv_prodMk_eventuallyEq_fderiv`, `ContMDiff.contMDiff_deriv_prodMk`, and
    `ContMDiff.continuous_deriv_prodMk`: derivatives along the scalar factor of `M × 𝕜` in
    coordinates and their `C^n` / continuity regularity.
* **Strict differentiability over `ℝ` or `ℂ`**: `ContMDiffAt.hasStrictFDerivAt_extChartAt_conj`
  gives strict differentiability of the preferred coordinate expression of a `C¹` map on a
  boundaryless manifold over an `RCLike` field.
-/

public section

open Set
open scoped Manifold Topology

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-! ### Preferred charts without atlas smoothness assumptions -/

/-- A continuous map whose preferred coordinate expression agrees locally with a continuous
linear map has that manifold derivative. The equality is only required within the source model. -/
theorem ContinuousAt.hasMFDerivAt_of_writtenInExtChartAt_eventuallyEq
    {f : M → M'} {x : M} (hf : ContinuousAt f x) (L : E →L[𝕜] E')
    (hL : writtenInExtChartAt I I' x f =ᶠ[𝓝[range I] (extChartAt I x x)] L) :
    HasMFDerivAt I I' f x L := by
  refine ⟨hf, ?_⟩
  have hd := L.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq hL
    (hL.eq_of_nhdsWithin ⟨chartAt H x x, rfl⟩)
  -- `HasMFDerivAt` conjugates by the tangent-to-model casts, which are the identity on model
  -- vectors, so identify the continuous linear maps pointwise once.
  convert hd using 1
  ext v
  rfl

/-- A map `g` between model spaces which is `C^n` at the chart image of `x` and sends it to the
chart image of `y` gives, read back through the extended charts at `x` and `y`, a map `M → M'`
which is `C^n` at `x`. The target model must be boundaryless, so that `g` stays in the chart
target near the chart image of `x`. -/
theorem ContDiffAt.contMDiffAt_extChartAt_symm_comp_extChartAt [I'.Boundaryless]
    {n : WithTop ℕ∞} {g : E → E'} {x : M} {y : M'} (hg : ContDiffAt 𝕜 n g (extChartAt I x x))
    (hgx : g (extChartAt I x x) = extChartAt I' y y) :
    ContMDiffAt I I' n (fun z ↦ (extChartAt I' y).symm (g (extChartAt I x z))) x := by
  have hy : (extChartAt I' y).symm (g (extChartAt I x x)) = y := by rw [hgx, extChartAt_to_inv]
  have htarget : ∀ᶠ w in 𝓝 (extChartAt I x x), g w ∈ (extChartAt I' y).target :=
    hg.continuousAt.preimage_mem_nhds (hgx ▸ extChartAt_target_mem_nhds y)
  rw [contMDiffAt_iff, hy]
  refine ⟨ContinuousAt.comp_of_eq (continuousAt_extChartAt_symm y)
    (hg.continuousAt.comp (continuousAt_extChartAt x)) hgx, ?_⟩
  refine hg.contDiffWithinAt.congr_of_eventuallyEq_of_mem ?_ (mem_range_self _)
  filter_upwards [nhdsWithin_le_nhds htarget, extChartAt_target_mem_nhdsWithin x] with w hw hw'
  simp only [Function.comp_apply, (extChartAt I x).right_inv hw', (extChartAt I' y).right_inv hw]

/-- At an interior point `x`, a map into a normed space which is `C^n` at `x` has a `C^n`
coordinate expression in the preferred extended chart at `x`. This is the interior-point
counterpart of `ContMDiffAt.contDiffAt_comp_extChartAt_symm`, which assumes a boundaryless
manifold. -/
theorem ContMDiffAt.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : M → F} {x : M} {n : WithTop ℕ∞}
    (hf : ContMDiffAt I 𝓘(𝕜, F) n f x) (hx : I.IsInteriorPoint x) :
    ContDiffAt 𝕜 n (f ∘ (extChartAt I x).symm) (extChartAt I x x) :=
  -- At an interior point the range of `I` is a neighbourhood of the chart image of `x`.
  contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_iff_source.mp hf).contMDiffAt (mem_interior_iff_mem_nhds.mp hx))

namespace TauCeti.Manifold

omit [ChartedSpace H M] in
/-- The preferred chart at a point determines manifold differentiability there, independently of
the rest of the atlas. -/
theorem mdifferentiableAt_iff_of_chartAt_eq {c c' : ChartedSpace H M} (f : M → M') (x : M)
    (h : c.chartAt x = c'.chartAt x) :
    (letI := c; MDifferentiableAt I I' f x) ↔ (letI := c'; MDifferentiableAt I I' f x) := by
  simp only [mdifferentiableAt_iff, writtenInExtChartAt, extChartAt, chartAt, h]

omit [ChartedSpace H M] in
/-- Changing the source atlas while retaining its preferred chart at a point preserves the manifold
derivative there for maps to any charted target. -/
theorem mfderiv_eq_of_chartAt_eq {c c' : ChartedSpace H M} (f : M → M') (x : M)
    (h : c.chartAt x = c'.chartAt x) :
    (letI := c; mfderiv I I' f x) = (letI := c'; mfderiv I I' f x) := by
  have hd := mdifferentiableAt_iff_of_chartAt_eq (I := I) (I' := I') f x h
  let _ : ChartedSpace H M := c
  by_cases hf : (letI := c; MDifferentiableAt I I' f x)
  · have hleft : (letI := c; mfderiv I I' f x) = _ := hf.mfderiv
    let _ : ChartedSpace H M := c'
    have hright : (letI := c'; mfderiv I I' f x) = _ := (hd.mp hf).mfderiv
    apply hleft.trans
    apply Eq.trans ?_ hright.symm
    simp only [writtenInExtChartAt, extChartAt, chartAt, h]
    -- The tangent-space implementation casts are independent of the chosen atlas.
    rfl
  · have hleft : (letI := c; mfderiv I I' f x) = 0 :=
      mfderiv_zero_of_not_mdifferentiableAt hf
    let _ : ChartedSpace H M := c'
    have hright : (letI := c'; mfderiv I I' f x) = 0 :=
      mfderiv_zero_of_not_mdifferentiableAt (hd.not.mp hf)
    exact hleft.trans hright.symm

/-- **Manifold derivatives from derivatives on the chart target.** If the expression of `f` in the
extended charts at `x` and `f x` agrees on the chart target with a map `φ` between the model
spaces that has derivative `f'` within that target at the chart image `p` of `x`, and `f` is
continuous at `x`, then `f'` is the manifold derivative of `f` at `x`. The chart target is a
neighbourhood of `p` within the range of the model, so no boundaryless hypothesis is needed. -/
theorem hasMFDerivAt_of_hasFDerivWithinAt_extChartAt_target {f : M → M'} {x : M}
    {φ : E → E'} {f' : E →L[𝕜] E'} {p : E} (hp : extChartAt I x x = p) (hf : ContinuousAt f x)
    (hφ : HasFDerivWithinAt φ f' (extChartAt I x).target p)
    (heq : EqOn (writtenInExtChartAt I I' x f) φ (extChartAt I x).target) :
    HasMFDerivAt I I' f x f' := by
  subst hp
  exact ⟨hf, (hasFDerivWithinAt_inter' (extChartAt_target_mem_nhdsWithin x)).1
    ((hφ.mono inter_subset_right).congr (fun _ hw ↦ heq hw.2) (heq (mem_extChartAt_target x)))⟩

end TauCeti.Manifold

namespace TauCeti

/-- The preferred extended chart at `x` has the identity as its manifold derivative at `x`. This
is `mfderiv_extChartAt_self` without any smoothness hypothesis on the atlas, in the form of a
`HasMFDerivAt` statement. -/
theorem hasMFDerivAt_extChartAt_self (x : M) :
    HasMFDerivAt I 𝓘(𝕜, E) (extChartAt I x) x (ContinuousLinearMap.id 𝕜 E) :=
  ⟨continuousAt_extChartAt x,
    (hasFDerivWithinAt_id (extChartAt I x x) (range I)).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin x)
        fun _ h ↦ writtenInExtChartAt_extChartAt h)
      (writtenInExtChartAt_extChartAt (mem_extChartAt_target x))⟩

/-- The manifold derivative of the preferred extended chart at its centre is the identity, with no
smoothness hypothesis on the atlas. -/
theorem mfderiv_extChartAt_eq_id (x : M) :
    mfderiv I 𝓘(𝕜, E) (extChartAt I x) x = ContinuousLinearMap.id 𝕜 E :=
  (hasMFDerivAt_extChartAt_self x).mfderiv

/-- The inverse of the preferred extended chart at `x` has the identity as its manifold derivative
within `range I` at the chart image `extChartAt I x x` of its centre, with no boundaryless or atlas
smoothness hypothesis. -/
theorem hasMFDerivWithinAt_extChartAt_symm_self (x : M) :
    HasMFDerivWithinAt 𝓘(𝕜, E) I (extChartAt I x).symm (range I) (extChartAt I x x)
      (ContinuousLinearMap.id 𝕜 E) := by
  have hm := mem_extChartAt_target (I := I) x
  refine ⟨(continuousAt_extChartAt_symm'' hm).continuousWithinAt, ?_⟩
  simp only [writtenInExtChartAt, extChartAt_to_inv, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, PartialEquiv.refl_symm, preimage_id, modelWithCornersSelf_coe,
    range_id, inter_univ]
  refine (hasFDerivWithinAt_id _ _).congr_of_eventuallyEq ?_ ((extChartAt I x).right_inv hm)
  filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hm] with u hu
  exact (extChartAt I x).right_inv hu

/-- The manifold derivative within `range I` of the inverse of the preferred extended chart at its
centre's image is the identity, with no boundaryless or atlas smoothness hypothesis. -/
theorem mfderivWithin_extChartAt_symm_eq_id (x : M) :
    mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) (extChartAt I x x) =
      ContinuousLinearMap.id 𝕜 E :=
  (hasMFDerivWithinAt_extChartAt_symm_self x).mfderivWithin
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2
      (I.uniqueDiffOn _ (extChartAt_target_subset_range x (mem_extChartAt_target x))))

/-- On a boundaryless manifold, the inverse of the preferred extended chart at `x` has the identity
as its manifold derivative at the chart image `extChartAt I x x` of its centre. There is no
smoothness hypothesis on the atlas. -/
theorem hasMFDerivAt_extChartAt_symm_self [I.Boundaryless] (x : M) :
    HasMFDerivAt 𝓘(𝕜, E) I (extChartAt I x).symm (extChartAt I x x)
      (ContinuousLinearMap.id 𝕜 E) :=
  hasMFDerivWithinAt_univ.mp
    (I.range_eq_univ ▸ hasMFDerivWithinAt_extChartAt_symm_self (I := I) x)

/-- A map between model spaces, read in their preferred extended charts at `z` and at `g z`, is the
map read through the models, `I' ∘ g ∘ I.symm`. -/
theorem writtenInExtChartAt_self_eq (g : H → H') (z : H) :
    writtenInExtChartAt I I' z g = I' ∘ g ∘ I.symm := rfl

/-! ### Charts of the maximal atlas -/

/-- `mdifferentiable_of_mem_atlas` for the maximal atlas: a chart of the `C^1` maximal atlas is
differentiable on its source, and its inverse on its target. -/
theorem mdifferentiable_of_mem_maximalAtlas {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) : e.MDifferentiable I I :=
  ⟨fun _ hy ↦ (mdifferentiableAt_of_mem_maximalAtlas he hy).mdifferentiableWithinAt,
    fun _ hz ↦ (mdifferentiableAt_symm_of_mem_maximalAtlas he hz).mdifferentiableWithinAt⟩

/-- The derivative of an extended chart of the `C¹` maximal atlas, read as a map into the model
space, is invertible at every point of the chart source. -/
theorem isInvertible_mvfderiv_extend {x : M} {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (hx : x ∈ e.source) :
    (mvfderiv I (e.extend I) x).IsInvertible := by
  -- `mvfderiv` is `mfderiv` followed by `fromTangentSpace`; both factors are invertible.
  unfold mvfderiv
  exact ContinuousLinearMap.IsInvertible.comp ⟨NormedSpace.fromTangentSpace (e.extend I x), rfl⟩
    (isInvertible_mfderiv_extend he hx)

end TauCeti

/-- The manifold derivative at `z` of a map between model spaces, differentiable at `z`, is the
Fréchet derivative at `I z` within `range I` of `I' ∘ g ∘ I.symm`, the map read in the models. -/
theorem MDifferentiableAt.mfderiv_eq_fderivWithin_self {g : H → H'} {z : H}
    (hg : MDifferentiableAt I I' g z) :
    mfderiv I I' g z = fderivWithin 𝕜 (I' ∘ g ∘ I.symm) (range I) (I z) := by
  -- The tangent-space casts `tangentSpaceCastModel` are the identity maps of the model spaces.
  rw [hg.mfderiv, TauCeti.writtenInExtChartAt_self_eq, extChartAt_self_apply]; rfl

section MaximalAtlasExtend

open scoped ContDiff

/-- Nonvanishing Jacobian `det` of `φ.extend I ∘ (φ'.extend I).symm` on the overlap interior. -/
theorem ModelWithCorners.det_fderiv_extendCoordChange_ne_zero (I : ModelWithCorners 𝕜 E H)
    {n : ℕ∞ω} (hn : n ≠ 0) {φ' φ : OpenPartialHomeomorph M H}
    (hφ' : φ' ∈ IsManifold.maximalAtlas I n M) (hφ : φ ∈ IsManifold.maximalAtlas I n M)
    {w : E} (hw : w ∈ interior ((φ'.extend I).target ∩ (φ'.extend I).symm ⁻¹' φ.source)) :
    (fderiv 𝕜 (φ.extend I ∘ (φ'.extend I).symm) w).det ≠ 0 := by
  have hsrc : (I.extendCoordChange φ' φ).source =
      (φ'.extend I).target ∩ (φ'.extend I).symm ⁻¹' φ.source := by
    rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_source, PartialEquiv.symm_source,
      φ.extend_source]
  rcases I.isInvertible_fderivWithin_extendCoordChange hn hφ' hφ (hsrc ▸ interior_subset hw) with
    ⟨L, hL⟩
  rw [fderivWithin_of_mem_nhds (hsrc ▸ Filter.mem_of_superset (isOpen_interior.mem_nhds hw)
    interior_subset)] at hL
  rw [← PartialEquiv.coe_trans, ← hL]
  exact L.toLinearEquiv.isUnit_det'.ne_zero

/-- Differentiability of `(φ.extend I).symm` on `interior (φ.extend I).target` for `C^n` `φ`
(`n ≠ 0`). -/
theorem OpenPartialHomeomorph.mdifferentiableAt_extend_symm_of_mem_interior {n : ℕ∞ω} (hn : n ≠ 0)
    {φ : OpenPartialHomeomorph M H} (hφ : φ ∈ IsManifold.maximalAtlas I n M) {z : E}
    (hz : z ∈ interior (φ.extend I).target) :
    MDifferentiableAt 𝓘(𝕜, E) I (φ.extend I).symm z :=
  (((φ.extend_target' (I := I) ▸ contMDiffOn_extend_symm hφ) z (interior_subset hz)).contMDiffAt
    (mem_interior_iff_mem_nhds.1 hz)).mdifferentiableAt hn

/-- On `interior (φ.extend I).target`, `mfderivWithin` of `(φ.extend I).symm` equals `mfderiv`. -/
theorem OpenPartialHomeomorph.mfderivWithin_extend_symm_of_mem_interior
    (φ : OpenPartialHomeomorph M H) {z : E} (hz : z ∈ interior (φ.extend I).target) :
    mfderivWithin 𝓘(𝕜, E) I (φ.extend I).symm (range I) z =
      mfderiv 𝓘(𝕜, E) I (φ.extend I).symm z :=
  mfderivWithin_of_mem_nhds
    (Filter.mem_of_superset (mem_interior_iff_mem_nhds.1 hz) φ.extend_target_subset_range)

/-- `C^n` regularity of `ψ'.extend I' ∘ f ∘ (ψ.extend I).symm` on the chart overlap domain. -/
theorem OpenPartialHomeomorph.contDiffOn_extend_comp {n : ℕ∞ω}
    {ψ : OpenPartialHomeomorph M H} (hψ : ψ ∈ IsManifold.maximalAtlas I n M)
    {ψ' : OpenPartialHomeomorph M' H'} (hψ' : ψ' ∈ IsManifold.maximalAtlas I' n M')
    {f : M → M'} {t : Set M} (hf : ContMDiffOn I I' n f t) :
    ContDiffOn 𝕜 n (ψ'.extend I' ∘ f ∘ (ψ.extend I).symm)
      ((ψ.extend I).target ∩ (ψ.extend I).symm ⁻¹' (t ∩ f ⁻¹' ψ'.source)) :=
  contMDiffOn_iff_contDiffOn.1 ((ψ'.contMDiffOn_extend hψ').comp
    (hf.comp ((ψ.extend_target' (I := I) ▸ contMDiffOn_extend_symm hψ).mono inter_subset_left)
      fun _ hw ↦ hw.2.1) fun _ hw ↦ hw.2.2)

end MaximalAtlasExtend

/-! ### Maps on a boundaryless manifold -/

section Boundaryless

variable [I.Boundaryless]

/-- On a boundaryless source, a map between manifolds which is `C^n` at `x` has a `C^n` coordinate
expression in the extended charts at `x` and at `g x`. -/
theorem ContMDiffAt.contDiffAt_writtenInExtChartAt {n : WithTop ℕ∞} {g : M → M'} {x : M}
    (hg : ContMDiffAt I I' n g x) :
    ContDiffAt 𝕜 n (writtenInExtChartAt I I' x g) (extChartAt I x x) := by
  simpa only [writtenInExtChartAt, I.range_eq_univ, contDiffWithinAt_univ] using
    (contMDiffAt_iff.1 hg).2

/-- On a boundaryless source, a map between manifolds which is differentiable at `x` has a
differentiable coordinate expression in the extended charts at `x` and at `g x`. -/
theorem MDifferentiableAt.differentiableAt_writtenInExtChartAt {g : M → M'} {x : M}
    (hg : MDifferentiableAt I I' g x) :
    DifferentiableAt 𝕜 (writtenInExtChartAt I I' x g) (extChartAt I x x) := by
  simpa only [writtenInExtChartAt, I.range_eq_univ, differentiableWithinAt_univ] using
    ((mdifferentiableAt_iff _ _).1 hg).2

/-- On a product of boundaryless manifolds, a map into a manifold which is differentiable at
`(x, x')` has a differentiable coordinate expression in the preferred extended charts at `x` and
`x'` and at the image of `(x, x')`, at the pair of chart images. -/
theorem MDifferentiableAt.differentiableAt_comp_prod_extChartAt_symm [I'.Boundaryless]
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
    {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M'']
    [ChartedSpace H'' M''] {g : M × M' → M''} {x : M} {x' : M'}
    (hg : MDifferentiableAt (I.prod I') I'' g (x, x')) :
    DifferentiableAt 𝕜
      (fun z : E × E' ↦ extChartAt I'' (g (x, x'))
        (g ((extChartAt I x).symm z.1, (extChartAt I' x').symm z.2)))
      (extChartAt I x x, extChartAt I' x' x') := by
  simpa only [writtenInExtChartAt, extChartAt_prod, PartialEquiv.prod_coe_symm,
    PartialEquiv.prod_coe, Function.comp_def] using hg.differentiableAt_writtenInExtChartAt

/-- On a boundaryless manifold, the manifold derivative of `g : M → M'` at `x` is the Fréchet
derivative of `g` read in the extended charts at `x` and at `y = g x`, with the tangent spaces at
`x` and `g x` identified with the model spaces. Naming the image point `y` allows a self-map
fixing `x` to be read in the single chart at `x`. -/
theorem MDifferentiableAt.mfderiv_eq_fderiv_extChartAt_conj {g : M → M'} {x : M} {y : M'}
    (hg : MDifferentiableAt I I' g x) (hy : g x = y) :
    mfderiv I I' g x =
      fderiv 𝕜 (extChartAt I' y ∘ g ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  subst hy
  rw [hg.mfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  -- The tangent-space casts `tangentSpaceCastModel` are the identity maps of the model spaces.
  rfl

/-- On a boundaryless source, the manifold derivative, transported to the model spaces by the
canonical tangent casts, is the Fréchet derivative of the preferred coordinate expression. -/
theorem MDifferentiableAt.tangentSpaceCastModel_mfderiv_apply {g : M → M'} {x : M}
    (hg : MDifferentiableAt I I' g x) (v : TangentSpace I x) :
    tangentSpaceCastModel I' (g x) (mfderiv I I' g x v) =
      fderiv 𝕜 (writtenInExtChartAt I I' x g) (extChartAt I x x)
        (tangentSpaceCastModel I x v) := by
  rw [hg.mfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

section NormedTarget

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : M → F} {x : M}

namespace TauCeti

/-- On a boundaryless manifold, a map into a normed space is `C^n` at `x` exactly when its
coordinate expression in the preferred extended chart at `x` is `C^n` at the chart image of `x`. -/
theorem contMDiffAt_iff_contDiffAt_comp_extChartAt_symm {n : WithTop ℕ∞} :
    ContMDiffAt I 𝓘(𝕜, F) n f x ↔
      ContDiffAt 𝕜 n (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  rw [contMDiffAt_iff_source, ModelWithCorners.Boundaryless.range_eq_univ,
    contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]

/-- On a boundaryless manifold, a map into a normed space is `C^n` at `x` exactly when its
coordinate expression in a chart of the `C^n` maximal atlas containing `x` is `C^n` at the chart
image of `x`. -/
theorem contMDiffAt_iff_contDiffAt_comp_extend_symm {n : WithTop ℕ∞}
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I n M)
    (hx : x ∈ e.source) :
    ContMDiffAt I 𝓘(𝕜, F) n f x ↔ ContDiffAt 𝕜 n (f ∘ (e.extend I).symm) (e.extend I x) := by
  rw [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_source_of_mem_maximalAtlas he hx,
    preimage_univ, univ_inter, ModelWithCorners.Boundaryless.range_eq_univ,
    contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]

/-- On a boundaryless manifold, the differential of a map into a normed space vanishes exactly
when the derivative of its coordinate expression in a chart of the `C¹` maximal atlas containing
`x` vanishes at the chart image of `x`. Both sides are `0` when the map is not differentiable
at `x`. -/
theorem mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M) (hx : x ∈ e.source) :
    mvfderiv I f x = 0 ↔ fderiv 𝕜 (f ∘ (e.extend I).symm) (e.extend I x) = 0 := by
  have hiff : MDifferentiableAt I 𝓘(𝕜, F) f x ↔
      DifferentiableAt 𝕜 (f ∘ (e.extend I).symm) (e.extend I x) := by
    have h := mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas (s := univ) (f := f)
      (I' := 𝓘(𝕜, F)) he hx
    rwa [preimage_univ, univ_inter, ModelWithCorners.Boundaryless.range_eq_univ,
      mdifferentiableWithinAt_univ, mdifferentiableWithinAt_univ,
      mdifferentiableAt_iff_differentiableAt] at h
  by_cases hf : MDifferentiableAt I 𝓘(𝕜, F) f x
  swap
  · rw [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hf,
      fderiv_zero_of_not_differentiableAt (mt hiff.mpr hf), ContinuousLinearMap.comp_zero]
    exact iff_of_true rfl rfl
  have hg := hiff.mp hf
  have hfg : f =ᶠ[𝓝 x] (f ∘ (e.extend I).symm) ∘ e.extend I := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    rw [Function.comp_apply, Function.comp_apply, (e.extend I).left_inv (by rwa [e.extend_source])]
  have hcomp : mvfderiv I f x = mvfderiv I ((f ∘ (e.extend I).symm) ∘ e.extend I) x := by
    simp only [mvfderiv, hfg.mfderiv_eq]
    -- The two sides differ only in the point indexing the tangent space of `F`, which is `F`.
    rfl
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_extend he hx
  rw [hcomp, mvfderiv_comp_of_eq hg.mdifferentiableAt
    ((e.contMDiffAt_extend he hx).mdifferentiableAt one_ne_zero) rfl, mvfderiv_eq_fderiv, ← hL]
  -- Precomposition with the invertible chart derivative `L` neither creates nor kills zeros.
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; exact ContinuousLinearMap.zero_comp _⟩
  ext u
  rw [← L.apply_symm_apply u]
  exact DFunLike.congr_fun h (L.symm u)

end TauCeti

/-- On a boundaryless manifold, a map into a normed space which is `C^n` at `x` has a `C^n`
coordinate expression in the preferred extended chart at `x`. -/
theorem ContMDiffAt.contDiffAt_comp_extChartAt_symm {n : WithTop ℕ∞}
    (hf : ContMDiffAt I 𝓘(𝕜, F) n f x) :
    ContDiffAt 𝕜 n (f ∘ (extChartAt I x).symm) (extChartAt I x x) :=
  TauCeti.contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.mp hf

/-- On a product of boundaryless manifolds, a map into a normed space which is `C^n` at `(x, x')`
has a `C^n` coordinate expression in the preferred extended charts at `x` and `x'`, at the pair of
chart images. -/
theorem ContMDiffAt.contDiffAt_comp_prod_extChartAt_symm [I'.Boundaryless]
    {n : WithTop ℕ∞} {g : M × M' → F} {x' : M'}
    (hg : ContMDiffAt (I.prod I') 𝓘(𝕜, F) n g (x, x')) :
    ContDiffAt 𝕜 n (fun z : E × E' ↦ g ((extChartAt I x).symm z.1, (extChartAt I' x').symm z.2))
      (extChartAt I x x, extChartAt I' x' x') := by
  simpa only [extChartAt_prod, PartialEquiv.prod_coe_symm, PartialEquiv.prod_coe,
    Function.comp_def] using hg.contDiffAt_comp_extChartAt_symm

/-- On a boundaryless manifold, a map into a normed space which is differentiable at `x` has a
differentiable coordinate expression in the preferred extended chart at `x`. -/
theorem MDifferentiableAt.differentiableAt_comp_extChartAt_symm
    (hf : MDifferentiableAt I 𝓘(𝕜, F) f x) :
    DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  simpa [ModelWithCorners.Boundaryless.range_eq_univ, differentiableWithinAt_univ] using
    hf.mdifferentiableWithinAt.differentiableWithinAt_comp_extChartAt_symm (s := Set.univ)

namespace TauCeti

/-- On a boundaryless manifold, a map into a normed space is differentiable at `x` exactly when
its coordinate expression in the preferred extended chart is differentiable at the chart image
of `x`. -/
theorem mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm :
    MDifferentiableAt I 𝓘(𝕜, F) f x ↔
      DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  refine ⟨MDifferentiableAt.differentiableAt_comp_extChartAt_symm, fun h ↦ ?_⟩
  rw [mdifferentiableAt_iff]
  refine ⟨?_, ?_⟩
  · -- Near `x`, the map is its coordinate expression composed with the chart.
    exact (h.continuousAt.comp (continuousAt_extChartAt x)).congr
      (comp_extChartAt_symm_comp_extChartAt_eventuallyEq f x)
  · rwa [ModelWithCorners.Boundaryless.range_eq_univ, differentiableWithinAt_univ,
      writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp]

/-- On a boundaryless manifold, the vector-valued manifold derivative of a map into a normed space
is the Fréchet derivative of its coordinate expression in the preferred extended chart. Both sides
are `0` when the map is not differentiable at the point. -/
theorem mvfderiv_eq_fderiv_comp_extChartAt_symm :
    mvfderiv I f x = fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  by_cases hf : MDifferentiableAt I 𝓘(𝕜, F) f x
  · rw [hf.mvfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ,
      writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp]
  · have hd : ¬ DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) :=
      mt mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm.mpr hf
    rw [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hf, fderiv_zero_of_not_differentiableAt hd]
    rfl

/-- On a boundaryless manifold, the differential of a map into a normed space vanishes at `x` if
and only if the Fréchet derivative of its coordinate expression in the preferred extended chart
vanishes at `extChartAt I x x`. Both sides are `0` when the map is not differentiable at the
point. -/
theorem mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm :
    mfderiv I 𝓘(𝕜, F) f x = 0 ↔
      fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 := by
  rw [← mvfderiv_eq_fderiv_comp_extChartAt_symm]
  refine ⟨fun h ↦ by rw [mvfderiv, h]; exact ContinuousLinearMap.comp_zero _, fun h ↦ ?_⟩
  ext u
  exact DFunLike.congr_fun h u

/-- On a boundaryless manifold, `mvfderiv I f x`, read on the model space `E`, agrees with the
Fréchet derivative of the preferred coordinate expression at `extChartAt I x x`, even without a
differentiability hypothesis (both vanish when `f` is not differentiable at `x`). -/
theorem mvfderiv_comp_tangentSpaceCastModel_symm (f : M → F) (x : M) :
    (mvfderiv I f x).comp ((tangentSpaceCastModel I x).symm : E →L[𝕜] TangentSpace I x) =
      fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  ext v
  exact DFunLike.congr_fun (mvfderiv_eq_fderiv_comp_extChartAt_symm (I := I)) v

/-- On a boundaryless manifold, `mvfderiv I f x` evaluated on `v` equals the Fréchet derivative of
the preferred coordinate expression evaluated on `tangentSpaceCastModel I x v`, without any
differentiability assumption. -/
theorem mvfderiv_apply_eq_fderiv_comp_extChartAt_symm (f : M → F) (x : M)
    (v : TangentSpace I x) :
    mvfderiv I f x v =
      fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) (tangentSpaceCastModel I x v) := by
  rw [← mvfderiv_comp_tangentSpaceCastModel_symm, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

/-- On a boundaryless manifold, the range of `mvfderiv I f x` equals the range of the Fréchet
derivative of the preferred coordinate expression at `extChartAt I x x`. -/
theorem range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm (f : M → F) (x : M) :
    (mvfderiv I f x).range = (fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x)).range := by
  rw [← mvfderiv_comp_tangentSpaceCastModel_symm, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.mpr (tangentSpaceCastModel I x).symm.surjective

/-- On a boundaryless manifold, injectivity of `mvfderiv I f x` is equivalent to injectivity of the
Fréchet derivative of the preferred coordinate expression at `extChartAt I x x`. -/
theorem injective_fderiv_comp_extChartAt_symm_iff :
    Function.Injective (fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x)) ↔
      Function.Injective (mvfderiv I f x) := by
  rw [← mvfderiv_comp_tangentSpaceCastModel_symm, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.coe_coe]
  refine ⟨fun h u w huw ↦ ?_, fun h ↦ h.comp (tangentSpaceCastModel I x).symm.injective⟩
  exact (tangentSpaceCastModel I x).injective (h (by simpa using huw))

end TauCeti

end NormedTarget

end Boundaryless

/-! ### Derivatives in arbitrary charts of a `C¹` manifold -/

section C1Manifold

variable [IsManifold I 1 M]

namespace TauCeti

/-- On a subset of a chart overlap, the derivative of the extended coordinate change is its
Fréchet derivative within the full model range, including at boundary and corner points. -/
theorem hasFDerivWithinAt_extChartAt_coordChange (α β : M) {s : Set M}
    (hsub : s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source) :
    ∀ y ∈ (extChartAt I α) '' s,
      HasFDerivWithinAt ((extChartAt I α).symm ≫ extChartAt I β)
        (fderivWithin 𝕜 (extChartAt I β ∘ (extChartAt I α).symm) (Set.range I) y)
        ((extChartAt I α) '' s) y := by
  rintro _ ⟨x, hx, rfl⟩
  exact (hasFDerivWithinAt_tangentCoordChange (I := I) (hsub hx)).mono fun y hy ↦ by
    obtain ⟨z, -, rfl⟩ := hy
    exact mem_range_self _

/-- On a subset of the chart target, at a point where it has unique derivatives, the derivative of
the inverse chart within the subset is its derivative within the model range. -/
theorem mfderivWithin_extChartAt_symm_of_subset (x₀ : M) {s : Set E}
    (hs : s ⊆ (extChartAt I x₀).target) {y : E} (hy : y ∈ s) (hsu : UniqueDiffWithinAt 𝕜 s y) :
    mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm s y =
      mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) y :=
  mfderivWithin_subset (fun _ hz ↦ extChartAt_target_subset_range x₀ (hs hz))
    hsu.uniqueMDiffWithinAt (mdifferentiableWithinAt_extChartAt_symm (hs hy))

/-- Changing tangent coordinates from the chart at `x` to the chart at `y` and back is the
identity at every point of both chart sources. -/
theorem tangentCoordChange_tangentCoordChange {x y z : M} (hx : z ∈ (extChartAt I x).source)
    (hy : z ∈ (extChartAt I y).source) (v : E) :
    tangentCoordChange I y x z (tangentCoordChange I x y z v) = v := by
  rw [tangentCoordChange_comp ⟨⟨hx, hy⟩, hx⟩, tangentCoordChange_self hx]

end TauCeti

section NormedSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace TauCeti

section SourceCharts

variable {f : M → F} {x y : M}

/-- At a point `y` of the source of the extended chart at `x`, the manifold derivative of a map
into a normed space is the Fréchet derivative of its coordinate expression
`f ∘ (extChartAt I x).symm` at the chart image of `y`, composed with the manifold derivative of
the chart, provided the coordinate expression is Fréchet differentiable there. The chart need not
be centred at `y`. -/
theorem mfderiv_eq_fderiv_comp_mfderiv_extChartAt (hy : y ∈ (extChartAt I x).source)
    (hg : DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)) :
    mfderiv I 𝓘(𝕜, F) f y = (fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)).comp
      (mfderiv I 𝓘(𝕜, E) (extChartAt I x) y) := by
  have he : HasMFDerivAt I 𝓘(𝕜, E) (extChartAt I x) y (mfderiv I 𝓘(𝕜, E) (extChartAt I x) y) :=
    (mdifferentiableAt_extChartAt (by simpa using hy)).hasMFDerivAt
  have hfeq : f =ᶠ[𝓝 y] (f ∘ (extChartAt I x).symm) ∘ extChartAt I x := by
    filter_upwards [(isOpen_extChartAt_source x).mem_nhds hy] with z hz
    rw [Function.comp_apply, Function.comp_apply, (extChartAt I x).left_inv hz]
  exact ((hg.hasFDerivAt.hasMFDerivAt.comp y he).congr_of_eventuallyEq_abuse hfeq).mfderiv

/-- Read in a chart, a map into a normed space whose manifold derivative at `y` is injective has
injective Fréchet derivative at the chart image of `y`, provided the coordinate expression is
Fréchet differentiable there. -/
theorem fderiv_comp_extChartAt_symm_injective (hy : y ∈ (extChartAt I x).source)
    (hg : DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y))
    (hf : Function.Injective (mfderiv I 𝓘(𝕜, F) f y)) :
    Function.Injective (fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)) := by
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_extChartAt hy
  rw [mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy hg, ← hL] at hf
  exact Function.Injective.of_comp_right (g := L) hf L.surjective

/-- Read in a chart whose source contains `y`, a map into a normed space with differentiable
coordinate expression has zero manifold derivative at `y` exactly when that coordinate expression
has zero Fréchet derivative at the chart image of `y`. -/
theorem mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm_eq_zero
    (hy : y ∈ (extChartAt I x).source)
    (hg : DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)) :
    mfderiv I 𝓘(𝕜, F) f y = 0 ↔
      fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y) = 0 := by
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_extChartAt hy
  rw [mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy hg, ← hL]
  -- Precomposition with the invertible chart derivative `L` detects the zero map.
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_, fun h ↦ ContinuousLinearMap.ext fun w ↦ ?_⟩
  · obtain ⟨w, rfl⟩ := L.surjective v
    exact DFunLike.congr_fun h w
  · exact DFunLike.congr_fun h (L w)

/-- Read in a chart whose source contains `y`, two maps into a normed space have the same
differential at `y` exactly when, near the chart image of `y`, their coordinate expressions agree
with maps `f'` and `g'` that are differentiable there with the same Fréchet derivative. Taking
`f' = f ∘ (extChartAt I x).symm` and `g' = g ∘ (extChartAt I x).symm` compares the coordinate
expressions themselves. -/
theorem mvfderiv_eq_iff_fderiv_comp_extChartAt_symm_eq {g : M → F} {f' g' : E → F}
    (hy : y ∈ (extChartAt I x).source)
    (hf : f ∘ (extChartAt I x).symm =ᶠ[𝓝 (extChartAt I x y)] f')
    (hg : g ∘ (extChartAt I x).symm =ᶠ[𝓝 (extChartAt I x y)] g')
    (hf' : DifferentiableAt 𝕜 f' (extChartAt I x y))
    (hg' : DifferentiableAt 𝕜 g' (extChartAt I x y)) :
    mvfderiv I f y = mvfderiv I g y ↔
      fderiv 𝕜 f' (extChartAt I x y) = fderiv 𝕜 g' (extChartAt I x y) := by
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_extChartAt hy
  simp only [mvfderiv,
    mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy (hf'.congr_of_eventuallyEq hf),
    mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy (hg'.congr_of_eventuallyEq hg),
    hf.fderiv_eq, hg.fderiv_eq, ← hL]
  -- Both sides are the Fréchet derivatives after the invertible chart derivative `L`, read in `F`.
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_, fun h ↦ by rw [h]; rfl⟩
  obtain ⟨w, rfl⟩ := L.surjective v
  exact DFunLike.congr_fun h w

open Filter in
/-- Transfer of local uniqueness of critical points to the manifold. Suppose that `η q.1` lies in
the target of the extended chart at `x` for `q.1` near `p`, and that near `(p, extChartAt I x x)`
the coordinate expression `fun v ↦ f (q.1, (extChartAt I x).symm v)` is differentiable in `v` and
its Fréchet derivative at `q.2` vanishes exactly when `η q.1 = q.2`. Then near `(p, x)` the manifold
derivative of `fun y ↦ f (q.1, y)` at `q.2` vanishes exactly when
`(extChartAt I x).symm (η q.1) = q.2`. This transfers the equivalence only: it does not assert that
a critical point exists. -/
theorem eventually_mfderiv_eq_zero_iff_extChartAt_symm {P : Type*} [TopologicalSpace P]
    {f : P × M → F} {p : P} {x : M} {η : P → E}
    (hslice : ∀ᶠ q in 𝓝 (p, extChartAt I x x),
      DifferentiableAt 𝕜 (fun v ↦ f (q.1, (extChartAt I x).symm v)) q.2)
    (htarget : ∀ᶠ q in 𝓝 p, η q ∈ (extChartAt I x).target)
    (huniq : ∀ᶠ q in 𝓝 (p, extChartAt I x x),
      fderiv 𝕜 (fun v ↦ f (q.1, (extChartAt I x).symm v)) q.2 = 0 ↔ η q.1 = q.2) :
    ∀ᶠ q in 𝓝 (p, x), mfderiv I 𝓘(𝕜, F) (fun y ↦ f (q.1, y)) q.2 = 0 ↔
      (extChartAt I x).symm (η q.1) = q.2 := by
  let φ := extChartAt I x
  have hmap : ContinuousAt (fun q : P × M ↦ (q.1, φ q.2)) (p, x) :=
    continuousAt_fst.prodMk ((continuousAt_extChartAt (I := I) x).comp continuousAt_snd)
  have hsnear : ∀ᶠ q : P × M in 𝓝 (p, x), q.2 ∈ φ.source :=
    continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds x)
  filter_upwards [hmap.eventually huniq, hmap.eventually hslice, hsnear,
    continuousAt_fst.preimage_mem_nhds htarget] with q hu hg hs ht
  have hg' : DifferentiableAt 𝕜 ((fun y ↦ f (q.1, y)) ∘ φ.symm) (φ q.2) := hg
  rw [mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm_eq_zero hs hg']
  exact hu.trans (φ.symm_apply_eq hs ht).symm

/-- **Bounds on the differential read in a chart do not depend on the chart.** If `f` is `C¹` at
`x` and `e` is a chart of the `C¹` maximal atlas whose source contains `x`, then near `x` the
differential of the coordinate expression of `f` in `e` has norm at most a fixed multiple of that of
its coordinate expression in the preferred extended chart at `x`. The constant bounds the
derivative of the change of coordinates near the image of `x`. -/
theorem exists_norm_fderiv_comp_extend_symm_le_mul_norm_fderiv_comp_extChartAt_symm
    [I.Boundaryless] {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (hx : x ∈ e.source) (hf : ContMDiffAt I 𝓘(𝕜, F) 1 f x) :
    ∃ K > 0, ∀ᶠ y in 𝓝 x, ‖fderiv 𝕜 (f ∘ (e.extend I).symm) (e.extend I y)‖ ≤
      K * ‖fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)‖ := by
  -- The change of coordinates `T` from `e` to the preferred chart is `C¹` near `e.extend I x`.
  set T := I.extendCoordChange e (chartAt H x)
  have hT : ContDiffOn 𝕜 1 T T.source :=
    I.contDiffOn_extendCoordChange he (IsManifold.chart_mem_maximalAtlas x)
  have hTe (y) (hy : y ∈ e.source ∩ (chartAt H x).source) :
      T (e.extend I y) = extChartAt I x y := by
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, extChartAt_coe, Function.comp_apply]
    exact I.extendCoordChange_apply hy.1
  have hTx : T.source ∈ 𝓝 (e.extend I x) := by
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply]
    exact I.extendCoordChange_source_mem_nhds hx (mem_chart_source H x)
  -- Near `e.extend I x`, the expression of `f` in `e` is its expression in the preferred chart
  -- composed with `T`, and that expression is differentiable along `T`.
  have hcomp : f ∘ (e.extend I).symm =ᶠ[𝓝 (e.extend I x)] (f ∘ (extChartAt I x).symm) ∘ T := by
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply]
    exact (I.extend_symm_comp_extendCoordChange_eventuallyEq hx
      (mem_chart_source H x)).symm.fun_comp f
  have hd := hf.contDiffAt_comp_extChartAt_symm.eventually (by simp)
  rw [← hTe x ⟨hx, mem_chart_source H x⟩] at hd
  obtain ⟨K, hK, hKb⟩ := exists_norm_fderiv_comp_le_mul_norm_fderiv hcomp
    (Filter.mem_of_superset (I.isOpen_extendCoordChange_source.mem_nhds (mem_of_mem_nhds hTx))
      fun w hw ↦ ((hT.contDiffAt (I.isOpen_extendCoordChange_source.mem_nhds hw)).differentiableAt
        one_ne_zero))
    ((hT.contDiffAt hTx).fderiv_right (m := 0) le_rfl).continuousAt
    ((hT.contDiffAt hTx).continuousAt.eventually
      (hd.mono fun w hw ↦ hw.differentiableAt one_ne_zero))
  refine ⟨K, hK, ?_⟩
  filter_upwards [(e.continuousAt_extend (I := I) hx).eventually hKb, e.open_source.mem_nhds hx,
    chart_source_mem_nhds H x] with y hy hye hyc
  rwa [hTe y ⟨hye, hyc⟩] at hy

end SourceCharts

/-- The derivative of a model-valued map in an arbitrary preferred chart is its actual
manifold derivative composed with the inverse tangent chart. Both sides vanish when the map is not
differentiable at the point. -/
theorem fderivWithin_comp_extChartAt_symm {f : M → F} {x : M} (α : M)
    (hx : x ∈ (extChartAt I α).source) :
    fderivWithin 𝕜 (f ∘ (extChartAt I α).symm) (range I) (extChartAt I α x) =
      -- `TangentSpace I x` and `TangentSpace 𝓘(𝕜, F) (f x)` unfold to `E` and `F`.
      (mfderiv I 𝓘(𝕜, F) f x ∘L tangentCoordChange I α x x : E →L[𝕜] F) := by
  have hx' : x ∈ (chartAt H α).source := by simpa only [extChartAt_source] using hx
  by_cases hf : MDifferentiableAt I 𝓘(𝕜, F) f x
  · have ht := (extChartAt I α).map_source hx
    have h := mfderiv_comp_mfderivWithin (I := 𝓘(𝕜, E)) (I' := I) (I'' := 𝓘(𝕜, F))
      (extChartAt I α x) (by simpa only [(extChartAt I α).left_inv hx] using hf)
      (mdifferentiableWithinAt_extChartAt_symm ht)
      (I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range α ht)
        |>.uniqueMDiffWithinAt)
    rw [(extChartAt I α).left_inv hx, ← TangentBundle.symmL_trivializationAt hx',
      TangentBundle.symmL_trivializationAt_eq_core hx', mfderivWithin_eq_fderivWithin] at h
    -- The tangent spaces `TangentSpace 𝓘(𝕜, E) _` and `TangentSpace 𝓘(𝕜, F) _` unfold to `E` / `F`.
    exact h
  · -- Off the differentiable locus both sides are `0`.
    have hiff : MDifferentiableAt I 𝓘(𝕜, F) f x ↔ DifferentiableWithinAt 𝕜
        (f ∘ (extChartAt I α).symm) (range I) (extChartAt I α x) :=
      (mdifferentiableAt_iff_source_of_mem_source hx').trans
        mdifferentiableWithinAt_iff_differentiableWithinAt
    rw [fderivWithin_zero_of_not_differentiableWithinAt (mt hiff.mpr hf),
      mfderiv_zero_of_not_mdifferentiableAt hf]
    exact (ContinuousLinearMap.zero_comp _).symm

end TauCeti

/-- **The differential in chart coordinates is bounded on compact sets.** For a `C¹` map into a
normed space and a compact set `L` of coordinates in the target of the extended chart at `x`, there
is a constant `B` with `‖d f_y v‖ ≤ B ‖a‖` for every point `y` of the chart source with coordinate
in `L` and every tangent vector `v` at `y` with coordinates `a` in the chart at `x`. -/
theorem ContMDiffOn.exists_forall_norm_mvfderiv_le_mul_norm {f : M → F} {x : M}
    (hf : ContMDiffOn I 𝓘(𝕜, F) 1 f (extChartAt I x).source) {L : Set E}
    (hL : IsCompact L) (hLt : L ⊆ (extChartAt I x).target) :
    ∃ B, ∀ y ∈ (extChartAt I x).source, extChartAt I x y ∈ L → ∀ v : TangentSpace I y,
      ‖mvfderiv I f y v‖ ≤
        B * ‖(trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 y v‖ := by
  -- The derivative of the coordinate expression is continuous on the chart target.
  set g := f ∘ (extChartAt I x).symm
  have hg : ContDiffOn 𝕜 1 g (extChartAt I x).target :=
    contMDiffOn_iff_contDiffOn.1
      (hf.comp (contMDiffOn_extChartAt_symm x) fun _ hz ↦ (extChartAt I x).map_target hz)
  have hdg : ContinuousOn (fderivWithin 𝕜 g (range I)) (extChartAt I x).target :=
    (hg.continuousOn_fderivWithin (uniqueDiffOn_extChartAt_target x) le_rfl).congr fun z hz ↦
      fderivWithin_of_mem_nhdsWithin (extChartAt_target_mem_nhdsWithin_of_mem hz)
        (I.uniqueDiffOn _ (extChartAt_target_subset_range x hz))
        ((hg.differentiableOn one_ne_zero) z hz)
  obtain ⟨B, hB⟩ := hL.exists_bound_of_continuousOn (hdg.mono hLt)
  refine ⟨B, fun y hy hyL v ↦ ?_⟩
  have hyc : y ∈ (chartAt H x).source := by rwa [← extChartAt_source I]
  have hyT : y ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  -- Read `v` through its coordinates in the chart at `x`, then use the chart-derivative formula.
  have hv : mvfderiv I f y v = fderivWithin 𝕜 g (range I) (extChartAt I x y)
      ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt 𝕜 y v) := by
    conv_lhs => rw [← Bundle.Trivialization.symmL_continuousLinearMapAt (R := 𝕜) _ hyT v,
      TangentBundle.symmL_trivializationAt_eq_core hyc]
    rw [TauCeti.fderivWithin_comp_extChartAt_symm x hy, mvfderiv]
    -- `NormedSpace.fromTangentSpace` is the identity on vectors, and `tangentCoordChange` is an
    -- abbreviation of the core coordinate change.
    rfl
  rw [hv]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hB _ hyL)

/-- In a preferred chart, a manifold derivative from a normed source gives the ordinary
coordinate derivative by composing with the tangent chart. -/
theorem HasMFDerivAt.hasFDerivAt_extChartAt_comp {Q : F → M} {z : F} {α : M}
    {e : F →L[𝕜] TangentSpace I (Q z)}
    (hQ : HasMFDerivAt 𝓘(𝕜, F) I Q z
      (e.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (hx : Q z ∈ (chartAt H α).source) :
    HasFDerivAt (extChartAt I α ∘ Q)
      (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt 𝕜 (Q z)).comp e) z := by
  refine ((hasMFDerivAt_extChartAt (I := I) hx).comp z hQ).hasFDerivAt.congr_fderiv ?_
  have hη : (trivializationAt E (TangentSpace I) α).continuousLinearMapAt 𝕜 (Q z) =
      mfderiv I I (chartAt H α) (Q z) := by
    rw [mfderiv_chartAt_eq_tangentCoordChange hx,
      TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx]
  -- Cancel the canonical source tangent identification `NormedSpace.fromTangentSpace z`.
  ext v
  exact congrArg (· (e v)) hη.symm

/-- Read in a preferred chart, the derivative of a map from a normed space is its manifold
derivative followed by the manifold derivative of the chart. Both sides are `0` when the map is not
differentiable at the point, so continuity at the point suffices. -/
theorem ContinuousAt.fderiv_extChartAt_comp_apply {Q : F → M} {z : F} {α : M}
    (hQc : ContinuousAt Q z) (hz : Q z ∈ (extChartAt I α).source) (v : F) :
    fderiv 𝕜 (extChartAt I α ∘ Q) z v =
      mfderiv I 𝓘(𝕜, E) (extChartAt I α) (Q z) (mfderiv 𝓘(𝕜, F) I Q z v) := by
  have hz' : Q z ∈ (chartAt H α).source := by rwa [← extChartAt_source I]
  by_cases hQ : MDifferentiableAt 𝓘(𝕜, F) I Q z
  · have h := congr($(mfderiv_comp z (mdifferentiableAt_extChartAt hz') hQ) v)
    rw [mfderiv_eq_fderiv] at h
    -- `mfderiv_eq_fderiv` only inserts the identifications of tangent spaces of `F` and `E`.
    exact h
  · have hd : ¬ DifferentiableAt 𝕜 (extChartAt I α ∘ Q) z := fun hd ↦ hQ
      ((mdifferentiableAt_iff_target_of_mem_source hz').2 ⟨hQc, hd.mdifferentiableAt⟩)
    rw [mfderiv_zero_of_not_mdifferentiableAt hQ, fderiv_zero_of_not_differentiableAt hd]
    exact (map_zero _).symm

/-- In the tangent coordinates of a preferred chart, the derivative of the coordinate expression of
a map from a normed space is its manifold derivative: the inverse tangent coordinates `symmL`
recover `mfderiv` from the coordinate derivative. -/
theorem ContinuousAt.symmL_fderiv_extChartAt_comp_apply {Q : F → M} {z : F} {α : M}
    (hQc : ContinuousAt Q z) (hz : Q z ∈ (extChartAt I α).source) (v : F) :
    (trivializationAt E (TangentSpace I) α).symmL 𝕜 (Q z)
        (fderiv 𝕜 (extChartAt I α ∘ Q) z v) = mfderiv 𝓘(𝕜, F) I Q z v := by
  have hb : Q z ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet, ← extChartAt_source I]
  rw [hQc.fderiv_extChartAt_comp_apply hz,
    ← TangentBundle.continuousLinearMapAt_trivializationAt (by rwa [← extChartAt_source I])]
  exact Bundle.Trivialization.symmL_continuousLinearMapAt _ hb _

end NormedSpace

section BetweenManifolds

variable [IsManifold I' 1 M']

/-- Read in the extended charts at `x` and `y`, a map with manifold derivative `f'` at `x'` has
Fréchet derivative within `range I` equal to `f'` pre- and post-composed with the derivatives of
the inverse chart at `x` and of the chart at `y`. The charts need only contain `x'` and `f x'` in
their sources; they need not be centred there. -/
theorem HasMFDerivAt.hasFDerivWithinAt_of_mem_source {f : M → M'} {x x' : M} {y : M'}
    {f' : TangentSpace I x' →L[𝕜] TangentSpace I' (f x')} (hf : HasMFDerivAt I I' f x' f')
    (hx : x' ∈ (chartAt H x).source) (hy : f x' ∈ (chartAt H' y).source) :
    HasFDerivWithinAt (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
      (mfderiv I' 𝓘(𝕜, E') (extChartAt I' y) (f x') ∘L f' ∘L
        mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) (extChartAt I x x') :
          E →L[𝕜] E')
      (range I) (extChartAt I x x') := by
  have hx' : x' ∈ (extChartAt I x).source := by rwa [extChartAt_source]
  have hsymm := (mdifferentiableWithinAt_extChartAt_symm
    ((extChartAt I x).map_source hx')).hasMFDerivWithinAt
  -- Both remaining derivatives are taken at `(extChartAt I x).symm (extChartAt I x x') = x'`.
  have hf' : HasMFDerivAt I I' f ((extChartAt I x).symm (extChartAt I x x')) f' := by
    rwa [(extChartAt I x).left_inv hx']
  have hchart : HasMFDerivAt I' 𝓘(𝕜, E') (extChartAt I' y)
      (f ((extChartAt I x).symm (extChartAt I x x')))
      (mfderiv I' 𝓘(𝕜, E') (extChartAt I' y) (f x')) := by
    rw [(extChartAt I x).left_inv hx']
    exact (mdifferentiableAt_extChartAt hy).hasMFDerivAt
  exact hasMFDerivWithinAt_iff_hasFDerivWithinAt.1
    ((hchart.comp _ hf').comp_hasMFDerivWithinAt _ hsymm)

/-- The coordinate expression of a map between manifolds in arbitrary preferred charts at `β`
and `α` has, as its derivative within the model range, the manifold derivative composed with the
tangent coordinate changes of the two charts. Both sides are `0` when the map is not differentiable
at the point, so continuity at the point suffices. -/
theorem ContinuousAt.fderivWithin_extChartAt_comp_extChartAt_symm {f : M → M'}
    {x : M} (hc : ContinuousAt f x) {β : M} {α : M'}
    (hx : x ∈ (extChartAt I β).source) (hfx : f x ∈ (extChartAt I' α).source) :
    fderivWithin 𝕜 (extChartAt I' α ∘ f ∘ (extChartAt I β).symm) (range I) (extChartAt I β x) =
      (tangentCoordChange I' (f x) α (f x) ∘L mfderiv I I' f x ∘L
        tangentCoordChange I β x x : E →L[𝕜] E') := by
  have hfx' : f x ∈ (chartAt H' α).source := by simpa only [extChartAt_source] using hfx
  by_cases hf : MDifferentiableAt I I' f x
  · have hα : MDifferentiableAt I' 𝓘(𝕜, E') (extChartAt I' α) (f x) :=
      mdifferentiableAt_extChartAt hfx'
    have h := TauCeti.fderivWithin_comp_extChartAt_symm (f := extChartAt I' α ∘ f) β hx
    rw [mfderiv_comp x hα hf, (hasMFDerivAt_extChartAt hfx').mfderiv,
      mfderiv_chartAt_eq_tangentCoordChange hfx'] at h
    exact h
  · have hx' : x ∈ (chartAt H β).source := by rwa [← extChartAt_source I]
    have hd : ¬ DifferentiableWithinAt 𝕜 (extChartAt I' α ∘ f ∘ (extChartAt I β).symm) (range I)
        (extChartAt I β x) :=
      fun hd ↦ hf ((mdifferentiableAt_iff_of_mem_source hx' hfx').2 ⟨hc, hd⟩)
    rw [mfderiv_zero_of_not_mdifferentiableAt hf,
      fderivWithin_zero_of_not_differentiableWithinAt hd]
    ext _
    exact (map_zero (tangentCoordChange I' (f x) α (f x))).symm

/-- The coordinate expression of a map between manifolds in arbitrary preferred charts at `β` and
`α` has vanishing derivative within the model range at the chart image of `x` exactly when the
map has vanishing manifold derivative at `x`: the tangent coordinate changes are invertible. -/
theorem ContinuousAt.fderivWithin_extChartAt_comp_extChartAt_symm_eq_zero_iff
    {f : M → M'} {x : M} (hc : ContinuousAt f x) {β : M} {α : M'}
    (hx : x ∈ (extChartAt I β).source) (hfx : f x ∈ (extChartAt I' α).source) :
    fderivWithin 𝕜 (extChartAt I' α ∘ f ∘ (extChartAt I β).symm) (range I) (extChartAt I β x) = 0 ↔
      mfderiv I I' f x = 0 := by
  rw [hc.fderivWithin_extChartAt_comp_extChartAt_symm hx hfx]
  refine ⟨fun h0 ↦ ContinuousLinearMap.ext fun (v : E) ↦ ?_,
    fun h0 ↦ ContinuousLinearMap.ext fun w ↦ ?_⟩
  · -- Evaluate at the preimage of `v` under the source coordinate change; the tangent spaces are
    -- the model spaces by definition, so the composite applies pointwise.
    have hv : tangentCoordChange I' (f x) α (f x) (mfderiv I I' f x
        (tangentCoordChange I β x x (tangentCoordChange I x β x v))) = 0 :=
      congr($h0 (tangentCoordChange I x β x v))
    rw [TauCeti.tangentCoordChange_tangentCoordChange (mem_extChartAt_source x) hx] at hv
    -- Undo the target coordinate change.
    have hm := TauCeti.tangentCoordChange_tangentCoordChange (mem_extChartAt_source (f x)) hfx
      (mfderiv I I' f x v)
    rw [hv, map_zero] at hm
    exact hm.symm
  · -- With `df = 0` the composite sends `w` to the image of `0` under the target coordinate change.
    rw [h0]
    exact map_zero (tangentCoordChange I' (f x) α (f x))

/-- The chain rule transfers a vanishing manifold differential to the coordinate expression
`extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm`, computed within the model range: at a point `u`
of the chart target whose image `(extChartAt I x).symm u` is a point of differentiability of `f`
with zero differential, mapped into the source of the target chart, the expression is
differentiable within the range with zero derivative. -/
theorem MDifferentiableAt.differentiableWithinAt_and_fderivWithin_extChartAt_comp_eq_zero
    {f : M → M'} {x : M} {u : E} (hu1 : u ∈ (extChartAt I x).target)
    (hfu : MDifferentiableAt I I' f ((extChartAt I x).symm u))
    (hzero : mfderiv I I' f ((extChartAt I x).symm u) = 0)
    (hu3 : f ((extChartAt I x).symm u) ∈ (extChartAt I' (f x)).source) :
    DifferentiableWithinAt 𝕜 (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm) (range I) u ∧
      fderivWithin 𝕜 (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm) (range I) u = 0 := by
  have hd : MDifferentiableAt I' 𝓘(𝕜, E') (extChartAt I' (f x)) (f ((extChartAt I x).symm u)) :=
    mdifferentiableAt_extChartAt (by rwa [← extChartAt_source I'])
  refine ⟨((hd.comp _ hfu).comp_mdifferentiableWithinAt _
    (mdifferentiableWithinAt_extChartAt_symm hu1)).differentiableWithinAt, ?_⟩
  simpa only [(extChartAt I x).right_inv hu1] using
    (hfu.continuousAt.fderivWithin_extChartAt_comp_extChartAt_symm_eq_zero_iff
      ((extChartAt I x).map_target hu1) hu3).2 hzero

end BetweenManifolds

end C1Manifold

/-! ### Higher regularity in arbitrary charts of a `C^n` manifold -/

section CnManifold

variable {n : WithTop ℕ∞} [IsManifold I n M]

/-- A map between manifolds which is `C^n` at the point with coordinate `y` in the preferred chart
at `β`, and sends it into the source of the preferred chart at `α`, is `C^n` at `y` when read in
these charts, provided `y` lies in the interior of the chart target. -/
theorem ContMDiffAt.contDiffAt_extChartAt_comp_extChartAt_symm [IsManifold I' n M']
    {f : M → M'} {β : M} {α : M'} {y : E} (hf : ContMDiffAt I I' n f ((extChartAt I β).symm y))
    (hy : y ∈ interior (extChartAt I β).target)
    (hfy : f ((extChartAt I β).symm y) ∈ (extChartAt I' α).source) :
    ContDiffAt 𝕜 n (extChartAt I' α ∘ f ∘ (extChartAt I β).symm) y := by
  have hfs : f ((extChartAt I β).symm y) ∈ (chartAt H' α).source := by
    rwa [← extChartAt_source (I := I')]
  have hβs : (extChartAt I β).symm y ∈ (chartAt H β).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I β).map_target (interior_subset hy)
  have h := ((contMDiffAt_iff_of_mem_source hβs hfs).1 hf).2
  rw [(extChartAt I β).right_inv (interior_subset hy)] at h
  exact h.contDiffAt (Filter.mem_of_superset (isOpen_interior.mem_nhds hy)
    (interior_subset.trans (extChartAt_target_subset_range β)))

namespace TauCeti

/-- On a boundaryless manifold, the change of extended charts from `x'` to `x` is `C^n` at every
point of its domain. This is Mathlib's `contDiffWithinAt_ext_coord_change` with the model range
the whole space. -/
theorem contDiffAt_ext_coord_change [I.Boundaryless] (x x' : M) {y : E}
    (hy : y ∈ ((extChartAt I x').symm ≫ extChartAt I x).source) :
    ContDiffAt 𝕜 n (extChartAt I x ∘ (extChartAt I x').symm) y := by
  have h := contDiffWithinAt_ext_coord_change (n := n) x x' hy
  rwa [I.range_eq_univ, contDiffWithinAt_univ] at h

/-- On a boundaryless manifold, the change of extended charts from `x'` to `x` is `C^n` at the
image under the chart at `x'` of every point of both chart domains. -/
theorem contDiffAt_ext_coord_change_extChartAt [I.Boundaryless] {x x' y : M}
    (hx : y ∈ (chartAt H x).source) (hx' : y ∈ (chartAt H x').source) :
    ContDiffAt 𝕜 n (extChartAt I x ∘ (extChartAt I x').symm) (extChartAt I x' y) :=
  contDiffAt_ext_coord_change x x' (PartialEquiv.mem_symm_trans_source _
    (by rwa [extChartAt_source]) (by rwa [extChartAt_source]))

/-- **The coordinate domain of a map read in charts.** For a `C^n` map `ι` out of a boundaryless
manifold and the extended charts `φ` at `x₀` and `χ` at `ι x₀`, the chart points `z` with
`φ⁻¹ z ∈ ι⁻¹ (χ.source)` form an open neighbourhood of `φ x₀` on which `χ ∘ ι ∘ φ⁻¹` is `C^n`
with values in the target of `χ`. -/
theorem isOpen_mem_contDiffOn_mapsTo_writtenInExtChartAt [I.Boundaryless] [IsManifold I' n M']
    {ι : M → M'} (hι : ContMDiff I I' n ι) (x₀ : M) :
    IsOpen ((extChartAt I x₀).target ∩
        (extChartAt I x₀).symm ⁻¹' (ι ⁻¹' (extChartAt I' (ι x₀)).source)) ∧
      extChartAt I x₀ x₀ ∈ (extChartAt I x₀).target ∩
        (extChartAt I x₀).symm ⁻¹' (ι ⁻¹' (extChartAt I' (ι x₀)).source) ∧
      ContDiffOn 𝕜 n (writtenInExtChartAt I I' x₀ ι) ((extChartAt I x₀).target ∩
        (extChartAt I x₀).symm ⁻¹' (ι ⁻¹' (extChartAt I' (ι x₀)).source)) ∧
      MapsTo (writtenInExtChartAt I I' x₀ ι) ((extChartAt I x₀).target ∩
        (extChartAt I x₀).symm ⁻¹' (ι ⁻¹' (extChartAt I' (ι x₀)).source))
        (extChartAt I' (ι x₀)).target := by
  refine ⟨(continuousOn_extChartAt_symm x₀).isOpen_inter_preimage (isOpen_extChartAt_target x₀)
      ((isOpen_extChartAt_source (ι x₀)).preimage hι.continuous),
    ⟨mem_extChartAt_target x₀, ?_⟩, (contMDiff_iff.1 hι).2 x₀ (ι x₀), writtenInExtChartAt_mapsTo⟩
  rw [mem_preimage, mem_preimage, (extChartAt I x₀).left_inv (mem_extChartAt_source x₀)]
  exact mem_extChartAt_source (ι x₀)

end TauCeti

end CnManifold

/-! ### Manifolds modelled on their own model space -/

section SelfModel

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {N : Type*} [TopologicalSpace N] [ChartedSpace E N]

/-- On a manifold modelled on its model space, the preferred-chart coordinate expression of a
`C^n` map into a normed space is `C^n` at the chart image of the point. -/
theorem ContMDiffAt.contDiffAt_comp_chartAt_symm {g : N → F} {z : N} {n : WithTop ℕ∞}
    (hg : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, F) n g z) :
    ContDiffAt 𝕜 n (g ∘ (chartAt E z).symm) (chartAt E z z) := by
  simpa only [TauCeti.extChartAt_model_symm_eq_chartAt_symm,
    TauCeti.extChartAt_model_apply_eq_chartAt_apply] using
    hg.contDiffAt_comp_extChartAt_symm

/-- A map from a normed space into a manifold modelled on a normed space, differentiable at `x`,
read in the preferred chart at its image, is differentiable at `x`. -/
theorem MDifferentiableAt.differentiableAt_chartAt_comp {g : F → N} {x : F}
    (hg : MDifferentiableAt 𝓘(𝕜, F) 𝓘(𝕜, E) g x) :
    DifferentiableAt 𝕜 (chartAt E (g x) ∘ g) x := by
  have h := hg.hasMFDerivAt.2.differentiableWithinAt
  simpa [writtenInExtChartAt, differentiableWithinAt_univ] using h

/-- For a normed source and a manifold modelled on a normed space, the derivative in the
preferred chart at the image is the manifold derivative, using the canonical tangent-space
identifications. Both sides are `0` when the map is not differentiable at `x`, so continuity at `x`
suffices. -/
theorem ContinuousAt.fderiv_chartAt_comp {g : F → N} {x : F} (hc : ContinuousAt g x) :
    fderiv 𝕜 (chartAt E (g x) ∘ g) x =
      (mfderiv 𝓘(𝕜, F) 𝓘(𝕜, E) g x).comp
        (NormedSpace.fromTangentSpace (𝕜 := 𝕜) x).symm.toContinuousLinearMap := by
  by_cases hg : MDifferentiableAt 𝓘(𝕜, F) 𝓘(𝕜, E) g x
  · -- For the self model, the extended chart is the chart itself, and tangent spaces of normed
    -- spaces have the canonical identity equivalence with their underlying spaces.
    rw [hg.mfderiv]
    ext v
    simp [writtenInExtChartAt, fderivWithin_univ]
    rfl
  · have hd : ¬ DifferentiableAt 𝕜 (chartAt E (g x) ∘ g) x := fun hd ↦ hg
      ((mdifferentiableAt_iff g x).2 ⟨hc, by
        simpa [writtenInExtChartAt, differentiableWithinAt_univ] using hd⟩)
    rw [mfderiv_zero_of_not_mdifferentiableAt hg, fderiv_zero_of_not_differentiableAt hd]
    exact (ContinuousLinearMap.zero_comp _).symm

namespace TauCeti

/-- On a manifold modelled on its model space, the derivative of the preferred-chart coordinate
expression is the vector-valued manifold derivative. Both sides are `0` when the map is not
differentiable at the point. -/
theorem fderiv_comp_chartAt_symm {g : N → F} {z : N} :
    fderiv 𝕜 (g ∘ (chartAt E z).symm) (chartAt E z z) = mvfderiv 𝓘(𝕜, E) g z := by
  rw [mvfderiv_eq_fderiv_comp_extChartAt_symm,
    extChartAt_model_symm_eq_chartAt_symm, extChartAt_model_apply_eq_chartAt_apply]

/-- On a manifold modelled on its model space, the kernel of the vector-valued manifold derivative
is the kernel of the derivative of the preferred-chart coordinate expression, a subspace of the
model space. -/
theorem ker_mvfderiv_eq_ker_fderiv_comp_chartAt_symm {g : N → F} {z : N} :
    (mvfderiv 𝓘(𝕜, E) g z).ker = (fderiv 𝕜 (g ∘ (chartAt E z).symm) (chartAt E z z)).ker := by
  rw [fderiv_comp_chartAt_symm]
  -- The two sides are the kernel of the same map, viewed as a subspace of the tangent space
  -- `TangentSpace 𝓘(𝕜, E) z` and of `E`; these are the same space by definition.
  rfl

/-- On a manifold modelled on its model space, a map into a normed space whose coordinate
expression in a chart of the `C¹` maximal atlas is differentiable at a coordinate is manifold
differentiable at the corresponding point. -/
theorem mdifferentiableAt_of_differentiableAt_comp_symm {g : N → F} {e : OpenPartialHomeomorph N E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) 1 N) {w : E} (hw : w ∈ e.target)
    (hg : DifferentiableAt 𝕜 (g ∘ e.symm) w) :
    MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, F) g (e.symm w) := by
  rw [← e.right_inv hw] at hg
  refine (hg.mdifferentiableAt.comp _
    (mdifferentiableAt_of_mem_maximalAtlas he (e.map_target hw))).congr_of_eventuallyEq ?_
  filter_upwards [e.open_source.mem_nhds (e.map_target hw)] with y hy
  simp only [Function.comp_apply, e.left_inv hy]

section ProductCharts

open Filter

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace 𝕜 K]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace F N']
  {P : Type*} [TopologicalSpace P] [ChartedSpace K P]

/-- The representative of a map differentiable near a point in maximal-atlas product charts is
Fréchet differentiable near the corresponding model-space point. -/
theorem eventually_differentiableAt_chart_comp_of_eventually_mdifferentiableAt
    {G : N × N' → P} {u : N × N'}
    {e : OpenPartialHomeomorph N E} {d : OpenPartialHomeomorph N' F}
    {c : OpenPartialHomeomorph P K}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) 1 N)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(𝕜, F) 1 N')
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(𝕜, K) 1 P)
    (hu : u.1 ∈ e.source) (hv : u.2 ∈ d.source) (hw : G u ∈ c.source)
    (hG : ∀ᶠ q in 𝓝 u, MDifferentiableAt (𝓘(𝕜, E).prod 𝓘(𝕜, F)) 𝓘(𝕜, K) G q) :
    ∀ᶠ q in 𝓝 (e u.1, d u.2),
      DifferentiableAt 𝕜 (fun q : E × F ↦ c (G (e.symm q.1, d.symm q.2))) q := by
  have hback : Tendsto (fun q : E × F ↦ (e.symm q.1, d.symm q.2))
      (𝓝 (e u.1, d u.2)) (𝓝 u) :=
    (e.tendsto_symm hu).prodMap_nhds (d.tendsto_symm hv)
  have hgc : ContinuousAt G u := hG.self_of_nhds.continuousAt
  filter_upwards [(continuous_fst.tendsto (e u.1, d u.2)).eventually
    (e.open_target.mem_nhds (e.map_source hu)),
    (continuous_snd.tendsto (e u.1, d u.2)).eventually
      (d.open_target.mem_nhds (d.map_source hv)),
    hback.eventually hG,
    (hgc.tendsto.comp hback).eventually (c.open_source.mem_nhds hw)] with q hqe hqd hqG hqc
  have hq := (mdifferentiableAt_of_mem_maximalAtlas hc hqc).comp q
    (hqG.comp q
      (((mdifferentiableAt_symm_of_mem_maximalAtlas he hqe).comp q mdifferentiableAt_fst).prodMk
        ((mdifferentiableAt_symm_of_mem_maximalAtlas hd hqd).comp q mdifferentiableAt_snd)))
  apply mdifferentiableAt_iff_differentiableAt.1
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hq

/-- Pulling a map differentiable near a model-space point back through maximal-atlas product
charts gives a map differentiable near the original point, provided its value lies in the target
of the output chart. -/
theorem eventually_mdifferentiableAt_chart_symm_comp_of_eventually_differentiableAt
    {φ : E × K → F} {u : N × P}
    {e : OpenPartialHomeomorph N E} {d : OpenPartialHomeomorph N' F}
    {c : OpenPartialHomeomorph P K}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) 1 N)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(𝕜, F) 1 N')
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(𝕜, K) 1 P)
    (hu : u.1 ∈ e.source) (hw : u.2 ∈ c.source)
    (hφ : ∀ᶠ q in 𝓝 (e u.1, c u.2), DifferentiableAt 𝕜 φ q)
    (ht : φ (e u.1, c u.2) ∈ d.target) :
    ∀ᶠ p in 𝓝 u, MDifferentiableAt (𝓘(𝕜, E).prod 𝓘(𝕜, K)) 𝓘(𝕜, F)
      (fun p : N × P ↦ d.symm (φ (e p.1, c p.2))) p := by
  have hfront : Tendsto (fun p : N × P ↦ (e p.1, c p.2))
      (𝓝 u) (𝓝 (e u.1, c u.2)) :=
    (e.continuousAt hu).prodMap_nhds (c.continuousAt hw)
  have htarget := (hφ.self_of_nhds.continuousAt.tendsto.comp hfront).eventually
    (d.open_target.mem_nhds ht)
  filter_upwards [hfront.eventually hφ, htarget,
    (continuous_fst.tendsto u).eventually (e.open_source.mem_nhds hu),
    (continuous_snd.tendsto u).eventually (c.open_source.mem_nhds hw)]
    with p hp hpt hpe hpc
  exact (mdifferentiableAt_symm_of_mem_maximalAtlas hd hpt).comp p
    (hp.mdifferentiableAt.comp p
      ((mdifferentiableAt_prod_module_iff _).2
        ⟨(mdifferentiableAt_of_mem_maximalAtlas he hpe).comp p mdifferentiableAt_fst,
          (mdifferentiableAt_of_mem_maximalAtlas hc hpc).comp p mdifferentiableAt_snd⟩))

end ProductCharts

end TauCeti

end SelfModel

/-! ### Preferred charts of a composite charted space -/

section CompositeCharts

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  {N : Type*} [TopologicalSpace N] [ChartedSpace X N]

/-- For the composite charts `ChartedSpace.comp H X N` of a space charted over a charted space `X`,
the preferred `X`-valued chart at `x`, read in the composite chart at `x` and the chart of `X` at
its image, is the identity near the image of `x`. -/
theorem writtenInExtChartAt_chartAt_comp_eventuallyEq (x : N) :
    letI := ChartedSpace.comp H X N
    writtenInExtChartAt I I x (chartAt X x) =ᶠ[𝓝[range I] extChartAt I x x] id := by
  let := ChartedSpace.comp H X N
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with y hy
  exact writtenInExtChartAt_chartAt_comp x hy

/-- For the composite charts `ChartedSpace.comp H X N`, the preferred `X`-valued chart at `x` has
the identity as its manifold derivative at `x`. -/
theorem hasMFDerivAt_chartAt_comp (x : N) :
    letI := ChartedSpace.comp H X N
    HasMFDerivAt I I (chartAt X x) x (ContinuousLinearMap.id 𝕜 (TangentSpace I x)) := by
  let := ChartedSpace.comp H X N
  exact ⟨(chartAt X x).continuousAt (mem_chart_source X x),
    (hasFDerivWithinAt_id _ _).congr_of_eventuallyEq
      (writtenInExtChartAt_chartAt_comp_eventuallyEq x)
      (writtenInExtChartAt_chartAt_comp x (mem_extChartAt_target x))⟩

/-- For the composite charts `ChartedSpace.comp H X N`, the preferred `X`-valued chart at `x` is
`C^n` at `x`, for every `n`. -/
theorem contMDiffAt_chartAt_comp {n : WithTop ℕ∞} (x : N) :
    letI := ChartedSpace.comp H X N
    ContMDiffAt I I n (chartAt X x) x := by
  let := ChartedSpace.comp H X N
  exact contMDiffAt_iff.2 ⟨(chartAt X x).continuousAt (mem_chart_source X x),
    contDiffWithinAt_id.congr_of_eventuallyEq (writtenInExtChartAt_chartAt_comp_eventuallyEq x)
      (writtenInExtChartAt_chartAt_comp x (mem_extChartAt_target x))⟩

end TauCeti

end CompositeCharts

/-! ### The derivative along the scalar factor of `M × 𝕜` -/

section TimeDerivative

open Filter

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : M × 𝕜 → F}

namespace TauCeti

/-- **The derivative along `𝕜` in coordinates.** At the chart image of a point `(x, s)` of the
chart source, the derivative of the coordinate expression of `f : M × 𝕜 → F` in the direction
`(0, 1)` is the derivative of the slice of `f` through `x`. -/
theorem fderiv_comp_extChartAt_symm_apply_zero_one {z : M × 𝕜} {x : M} {s : 𝕜}
    (hx : x ∈ (extChartAt I z.1).source)
    (hf : DifferentiableAt 𝕜 (f ∘ (extChartAt (I.prod 𝓘(𝕜)) z).symm) (extChartAt I z.1 x, s)) :
    fderiv 𝕜 (f ∘ (extChartAt (I.prod 𝓘(𝕜)) z).symm) (extChartAt I z.1 x, s) (0, 1) =
      deriv (fun s' ↦ f (x, s')) s := by
  have h : HasDerivAt (fun s' : 𝕜 ↦ (extChartAt I z.1 x, s')) ((0 : E), (1 : 𝕜)) s :=
    HasDerivAt.prodMk (hasDerivAt_const _ _) (hasDerivAt_id _)
  rw [← comp_extChartAt_symm_prodMk_left z hx]
  exact ((hf.hasFDerivAt.comp_hasDerivAt s h).deriv).symm

/-- **The derivative along `𝕜` near a point, in coordinates.** Near a point `z₀` at which
`f : M × 𝕜 → F` is `C¹`, the derivative of `f` along `𝕜` at `(x, t)` is the derivative of the
coordinate expression of `f` in the preferred chart at `z₀`, in the direction `(0, 1)`, at the chart
image `(φ x, t)` of `(x, t)`. -/
theorem deriv_prodMk_eventuallyEq_fderiv {z₀ : M × 𝕜}
    (hf : ContDiffAt 𝕜 1 (f ∘ (extChartAt (I.prod 𝓘(𝕜)) z₀).symm)
      (extChartAt I z₀.1 z₀.1, z₀.2)) :
    (fun z : M × 𝕜 ↦ deriv (fun s ↦ f (z.1, s)) z.2) =ᶠ[𝓝 z₀]
      fun z ↦ fderiv 𝕜 (f ∘ (extChartAt (I.prod 𝓘(𝕜)) z₀).symm)
        (extChartAt I z₀.1 z.1, z.2) (0, 1) := by
  have hφ : ContinuousAt (fun z : M × 𝕜 ↦ (extChartAt I z₀.1 z.1, z.2)) z₀ :=
    ((continuousAt_extChartAt z₀.1).comp continuousAt_fst).prodMk continuousAt_snd
  filter_upwards [continuousAt_fst.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) z₀.1),
    hφ.eventually (hf.eventually (by simp))] with z hz hzG
  exact (fderiv_comp_extChartAt_symm_apply_zero_one hz (hzG.differentiableAt one_ne_zero)).symm

end TauCeti

variable [I.Boundaryless]

/-- **The derivative along `𝕜` of a `C^(n + 1)` function on `M × 𝕜` is `C^n`.** On a boundaryless
manifold `M`, the map `(x, t) ↦ ∂ₜ f (x, t)` is `C^n`; near each point it is the derivative of the
coordinate expression of `f` in the direction of the last factor, which is unchanged by the charts.
-/
theorem ContMDiff.contMDiff_deriv_prodMk {n : WithTop ℕ∞}
    (hf : ContMDiff (I.prod 𝓘(𝕜)) 𝓘(𝕜, F) (n + 1) f) :
    ContMDiff (I.prod 𝓘(𝕜)) 𝓘(𝕜, F) n fun z : M × 𝕜 ↦ deriv (fun s ↦ f (z.1, s)) z.2 := by
  intro z₀
  set G := f ∘ (extChartAt (I.prod 𝓘(𝕜)) z₀).symm with hG
  have hG₀ : ContDiffAt 𝕜 (n + 1) G (extChartAt I z₀.1 z₀.1, z₀.2) := by
    simpa [hG, TauCeti.extChartAt_prod_modelSpace_apply] using
      TauCeti.contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.1 (hf z₀)
  -- The chart image `(φ x, t)` of `(x, t)` depends smoothly on `(x, t)` near `z₀`.
  have hφ : ContMDiffAt (I.prod 𝓘(𝕜)) 𝓘(𝕜, E × 𝕜) n
      (fun z : M × 𝕜 ↦ (extChartAt I z₀.1 z.1, z.2)) z₀ :=
    (contMDiffAt_extChartAt.comp z₀ contMDiffAt_fst).prodMk_space contMDiffAt_snd
  refine ContMDiffAt.congr_of_eventuallyEq ?_
    (TauCeti.deriv_prodMk_eventuallyEq_fderiv (hG₀.of_le le_add_self))
  exact ((hG₀.fderiv_right le_rfl).clm_apply contDiffAt_const).contMDiffAt.comp z₀ hφ

/-- **The derivative along `𝕜` of a `C¹` function on `M × 𝕜` is continuous.** On a boundaryless
manifold `M`, the map `(x, t) ↦ ∂ₜ f (x, t)` is continuous; near each point it is the derivative of
the coordinate expression of `f` in the direction of the last factor, which is unchanged by the
charts. -/
theorem ContMDiff.continuous_deriv_prodMk (hf : ContMDiff (I.prod 𝓘(𝕜)) 𝓘(𝕜, F) 1 f) :
    Continuous fun z : M × 𝕜 ↦ deriv (fun s ↦ f (z.1, s)) z.2 :=
  (hf.contMDiff_deriv_prodMk (n := 0)).continuous

end TimeDerivative

end NontriviallyNormedField

/-! ### Strict differentiability over `ℝ` or `ℂ` -/

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- A map out of a manifold without boundary that is `C¹` at `y`, read in the extended charts at
`y` and at `f y`, has a strict derivative at the image of `y`. -/
theorem ContMDiffAt.hasStrictFDerivAt_extChartAt_conj {f : M → M'} {y : M}
    (hf : ContMDiffAt I I' 1 f y) :
    HasStrictFDerivAt (extChartAt I' (f y) ∘ f ∘ (extChartAt I y).symm)
      (fderiv 𝕜 (extChartAt I' (f y) ∘ f ∘ (extChartAt I y).symm) (extChartAt I y y))
      (extChartAt I y y) := hf.contDiffAt_writtenInExtChartAt.hasStrictFDerivAt_fderiv one_ne_zero

end RCLike

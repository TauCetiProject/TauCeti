/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
# A manifold derivative read in arbitrary charts

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

* `TauCeti.Manifold.mdifferentiableAt_iff_of_chartAt_eq`: preferred-chart invariance of
  manifold differentiability.
* `TauCeti.Manifold.mfderiv_eq_of_chartAt_eq`: retaining the preferred charts preserves
  manifold derivatives when the source atlas changes.

* `HasMFDerivAt.hasFDerivWithinAt_of_mem_source`: the derivative of `f` read in the extended
  charts at `x` and `y`.
* `TauCeti.mfderiv_eq_fderiv_comp_mfderiv_extChartAt` and
  `TauCeti.fderiv_comp_extChartAt_symm_injective`: for a map into a normed space, the manifold
  derivative at any point of a chart's source, in terms of the Fréchet derivative of the
  coordinate expression, and the resulting transfer of injectivity.
* `ContMDiffAt.contDiffAt_comp_extChartAt_symm` and
  `MDifferentiableAt.differentiableAt_comp_extChartAt_symm`: on a boundaryless manifold, the
  coordinate expression of a `C^n` (resp. differentiable) map into a normed space is `C^n` (resp.
  differentiable) at the chart image of the point.
* `MDifferentiableAt.mvfderiv_eq_fderiv_comp_extChartAt_symm`: on a boundaryless manifold, the
  vector-valued manifold derivative is the Fréchet derivative of the coordinate expression.
* `MDifferentiableAt.fderivWithin_comp_extChartAt_symm`: read a model-valued manifold
  derivative after an inverse chart, including derivatives within the model range.
* `HasMFDerivAt.hasFDerivAt_extChartAt_comp`: read the coordinate derivative of a map from
  a normed source by composing its manifold derivative with the tangent chart.
* `TauCeti.writtenInExtChartAt_chartAt_comp_eventuallyEq`, `TauCeti.hasMFDerivAt_chartAt_comp` and
  `TauCeti.contMDiffAt_chartAt_comp`: for a space charted over a charted space `X`, with the
  composite charts, the preferred `X`-valued chart at `x` reads as the identity near `x`, so it is
  smooth at `x` with the identity as its derivative there.
-/

public section

open Set
open scoped Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']

namespace TauCeti.Manifold

omit [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I' 1 M'] in
/-- Preferred charts determine manifold differentiability independently of the rest of the atlas. -/
theorem mdifferentiableAt_iff_of_chartAt_eq {c c' : ChartedSpace H M}
    (h : c.chartAt = c'.chartAt) (f : M → M') (x : M) :
    (letI := c; MDifferentiableAt I I' f x) ↔ (letI := c'; MDifferentiableAt I I' f x) := by
  simp only [mdifferentiableAt_iff, writtenInExtChartAt, extChartAt, chartAt, h]

omit [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I' 1 M'] in
/-- Changing the source atlas while retaining its preferred charts preserves manifold derivatives
for maps to any charted target. -/
theorem mfderiv_eq_of_chartAt_eq {c c' : ChartedSpace H M} (h : c.chartAt = c'.chartAt)
    (f : M → M') (x : M) :
    (letI := c; mfderiv I I' f x) = (letI := c'; mfderiv I I' f x) := by
  have hd := mdifferentiableAt_iff_of_chartAt_eq (I := I) (I' := I') h f x
  -- Select c as the local atlas for the source-side derivative formula.
  let sourceAtlas : ChartedSpace H M := c
  by_cases hf : (letI := c; MDifferentiableAt I I' f x)
  · have hleft : (letI := c; mfderiv I I' f x) = _ := hf.mfderiv
    -- Select c' for the target-side formula; both displayed statements fix their atlas.
    let targetAtlas : ChartedSpace H M := c'
    have hright : (letI := c'; mfderiv I I' f x) = _ := (hd.mp hf).mfderiv
    apply hleft.trans
    apply Eq.trans ?_ hright.symm
    simp only [writtenInExtChartAt, extChartAt, chartAt, h]
    -- The tangent-space implementation casts are independent of the chosen atlas.
    rfl
  · have hleft : (letI := c; mfderiv I I' f x) = 0 :=
      mfderiv_zero_of_not_mdifferentiableAt hf
    -- Select c' to apply its non-differentiability law.
    let targetAtlas : ChartedSpace H M := c'
    have hright : (letI := c'; mfderiv I I' f x) = 0 :=
      mfderiv_zero_of_not_mdifferentiableAt (hd.not.mp hf)
    exact hleft.trans hright.symm

end TauCeti.Manifold

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

/-! ### Maps into a normed space, read in a chart of the source -/

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : M → F} {x y : M}

/-- At a point `y` of the source of the extended chart at `x`, the manifold derivative of a map
into a normed space is the Fréchet derivative of its coordinate expression
`f ∘ (extChartAt I x).symm` at the chart image of `y`, composed with the manifold derivative of
the chart. The chart need not be centred at `y`. -/
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
injective Fréchet derivative at the chart image of `y`. -/
theorem fderiv_comp_extChartAt_symm_injective (hy : y ∈ (extChartAt I x).source)
    (hg : DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y))
    (hf : Function.Injective (mfderiv I 𝓘(𝕜, F) f y)) :
    Function.Injective (fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)) := by
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_extChartAt hy
  rw [mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy hg, ← hL] at hf
  exact Function.Injective.of_comp_right (g := L) hf L.surjective

end TauCeti

/-! ### Maps into a normed space on a boundaryless manifold -/

section Boundaryless

variable [I.Boundaryless] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : M → F} {x : M}

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, a map into a normed space which is `C^n` at `x` has a `C^n`
coordinate expression in the preferred extended chart at `x`. -/
theorem _root_.ContMDiffAt.contDiffAt_comp_extChartAt_symm {n : WithTop ℕ∞}
    (hf : ContMDiffAt I 𝓘(𝕜, F) n f x) :
    ContDiffAt 𝕜 n (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  have h := (contMDiffAt_iff.1 hf).2
  rwa [ModelWithCorners.Boundaryless.range_eq_univ, contDiffWithinAt_univ,
    extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] at h

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, a map into a normed space which is differentiable at `x` has a
differentiable coordinate expression in the preferred extended chart at `x`. -/
theorem _root_.MDifferentiableAt.differentiableAt_comp_extChartAt_symm
    (hf : MDifferentiableAt I 𝓘(𝕜, F) f x) :
    DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  have h := ((mdifferentiableAt_iff f x).1 hf).2
  rwa [ModelWithCorners.Boundaryless.range_eq_univ, differentiableWithinAt_univ,
    writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp] at h

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, the vector-valued manifold derivative of a map into a normed space
is the Fréchet derivative of its coordinate expression in the preferred extended chart. -/
theorem _root_.MDifferentiableAt.mvfderiv_eq_fderiv_comp_extChartAt_symm
    (hf : MDifferentiableAt I 𝓘(𝕜, F) f x) :
    mvfderiv I f x = fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  rw [hf.mvfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ,
    writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp]

end Boundaryless

/-! ### Preferred charts of a composite charted space -/

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

section ChartOverlap

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
    obtain ⟨z, hz, rfl⟩ := hy
    exact extChartAt_target_subset_range α ((extChartAt I α).map_source (hsub hz).1)

end ChartOverlap

end TauCeti

namespace TauCeti

section NormedFieldCharts

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of a model-valued map in an arbitrary preferred chart is its actual
manifold derivative composed with the inverse tangent chart. -/
theorem _root_.MDifferentiableAt.fderivWithin_comp_extChartAt_symm {f : M → F} {x : M}
    (hf : MDifferentiableAt I 𝓘(𝕜, F) f x) (α : M) (hx : x ∈ (extChartAt I α).source) :
    fderivWithin 𝕜 (f ∘ (extChartAt I α).symm) (range I) (extChartAt I α x) =
      -- Use the fixed model fibers to compose the derivative with the tangent chart.
      (show E →L[𝕜] F from mfderiv I 𝓘(𝕜, F) f x).comp
        (tangentCoordChange I α x x) := by
  have ht := (extChartAt I α).map_source hx
  have h := mfderiv_comp_mfderivWithin (I := 𝓘(𝕜, E)) (I' := I) (I'' := 𝓘(𝕜, F))
    (extChartAt I α x) (by simpa only [(extChartAt I α).left_inv hx] using hf)
    (mdifferentiableWithinAt_extChartAt_symm ht)
    (I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range α ht)
      |>.uniqueMDiffWithinAt)
  rw [(extChartAt I α).left_inv hx] at h
  have hx' : x ∈ (chartAt H α).source := by simpa only [extChartAt_source] using hx
  rw [← TangentBundle.symmL_trivializationAt hx',
    TangentBundle.symmL_trivializationAt_eq_core hx'] at h
  rw [mfderivWithin_eq_fderivWithin] at h
  -- The tangent spaces of normed model spaces reduce to their underlying normed spaces.
  convert! h using 1

/-- In a preferred chart, a manifold derivative from a normed source gives the ordinary
coordinate derivative by composing with the tangent chart. -/
theorem _root_.HasMFDerivAt.hasFDerivAt_extChartAt_comp {Q : F → M} {z : F} {α : M}
    {e : F →L[𝕜] TangentSpace I (Q z)}
    (hQ : HasMFDerivAt 𝓘(𝕜, F) I Q z
      (e.comp
        (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (hx : Q z ∈ (chartAt H α).source) :
    HasFDerivAt (extChartAt I α ∘ Q)
      (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt 𝕜 (Q z)).comp
        e) z := by
  let η := (trivializationAt E (TangentSpace I) α).continuousLinearEquivAt 𝕜 (Q z)
    (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)
  let L := η.toContinuousLinearMap.comp e
  have hη : η.toContinuousLinearMap = tangentCoordChange I (Q z) α (Q z) := by
    rw [Bundle.Trivialization.coe_continuousLinearEquivAt_eq',
      TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx]
  have hη' : η.toContinuousLinearMap = mfderiv I I (chartAt H α) (Q z) := by
    rw [mfderiv_chartAt_eq_tangentCoordChange hx]
    exact hη
  have hd : HasFDerivAt (extChartAt I α ∘ Q) L z := by
    have h := (hasMFDerivAt_extChartAt (I := I) hx).comp z hQ
    -- Cancel the canonical source tangent identification in the derivative composition.
    convert! h.hasFDerivAt using 2
    ext v
    rw [← hη']
    rfl
  have he : L =
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt 𝕜 (Q z)).comp
        e := by
    rw [← Bundle.Trivialization.coe_continuousLinearEquivAt_eq' _
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)]
  exact he ▸ hd

end NormedFieldCharts

end TauCeti

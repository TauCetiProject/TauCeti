/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Complex.Chart
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Topology.OpenPartialHomeomorph.Composition
import TauCeti.Analysis.Complex.Beltrami.Isothermal
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart

/-!
# Isothermal charts of an almost complex surface

Let `M` be a real surface, a smooth manifold modelled on `𝓘(ℝ, ℂ)`, with a smooth almost complex
structure `j`. A chart `e : M → ℂ` of the real `C¹` maximal atlas is *isothermal* for `j` when
`j = i` in it: its differential carries `j` to multiplication by `i` at every point of its source.

The derivative of the transition map between two isothermal charts commutes with multiplication
by `i`: this is the Cauchy–Riemann equation, so the transition is holomorphic, hence analytic.
Isothermal charts cover `M` (see below), so they are the atlas of a complex analytic curve
`TauCeti.IsothermalSurface j`, a copy of `M`. The identity of `M` is a smooth real diffeomorphism
`IsothermalSurface.diffeomorph` from this copy to `M`, which carries the almost complex structure
`ofComplexManifold` of the copy to `j`.

Conversely, on a complex curve `X` the isothermal charts of `ofComplexManifold ℂ X` are exactly the
holomorphic charts, so isothermal charts cover `X`, and the identity is a biholomorphism
`IsothermalSurface.biholomorph` from the complex curve `IsothermalSurface (ofComplexManifold ℂ X)`
to `X`. The two constructions are mutually inverse.

Isothermal charts always exist: every point of `M` lies in the source of an isothermal chart of
`j` (`SmoothAlmostComplexStructure.exists_isIsothermalChart`). Read in a chart of `M`, `j` is a
smooth field of complex structures on the plane, and the Beltrami equation gives a chart in which
it is `i` (`TauCeti.Beltrami.exists_isothermal_chart_of_contDiffAt_of_sq_eq_neg_one`). This is the
integrability of almost complex structures in real dimension two: every almost complex surface is,
through `IsothermalSurface`, a complex curve. Smooth planar coordinates and holomorphic
transitions show that every isothermal chart is smooth in the original real atlas
(`IsIsothermalChart.mem_maximalAtlas_infty`).

## Main declarations

* `TauCeti.IsIsothermalChart j e`: the chart `e` belongs to the real `C¹` maximal atlas and `j = i`
  in it.
* `TauCeti.IsIsothermalChart.differentiableOn_symm_trans`,
  `TauCeti.IsIsothermalChart.analyticOnNhd_symm_trans`: the transition map between two isothermal
  charts is holomorphic, hence analytic.
* `TauCeti.SmoothAlmostComplexStructure.exists_isIsothermalChart`: every smooth almost complex
  structure on a surface has isothermal charts.
* `TauCeti.IsothermalSurface j`: the surface `M` charted by the isothermal charts of `j`; it is a
  complex analytic curve, `IsManifold 𝓘(ℂ) ω (IsothermalSurface j)`.
* `TauCeti.IsIsothermalChart.mem_maximalAtlas_infty`: every isothermal chart is smooth in the
  original real atlas.
* `TauCeti.IsothermalSurface.mem_atlas_iff`: its charts are exactly the isothermal charts of `j`,
  read through `IsothermalSurface.homeomorph`.
* `TauCeti.IsothermalSurface.diffeomorph`: the identity, a smooth diffeomorphism of real surfaces;
  `TauCeti.IsothermalSurface.isPseudoholomorphic_homeomorph` and
  `TauCeti.IsothermalSurface.isPseudoholomorphic_homeomorph_symm`: it carries
  `ofComplexManifold ℂ (IsothermalSurface j)` to `j` and back.
* `TauCeti.isIsothermalChart_ofComplexManifold_iff`: on a complex curve, the isothermal charts of
  `ofComplexManifold` are the holomorphic charts.
* `TauCeti.IsothermalSurface.biholomorph`: the identity, a biholomorphism from
  `IsothermalSurface (ofComplexManifold ℂ X)` to `X`.
* `TauCeti.not_isIsothermalChart_conj`: complex conjugation is not an isothermal chart of `ℂ` for
  multiplication by `i`, a check that isothermal charts preserve orientation and are not merely
  conformal.

## References

* Dusa McDuff and Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Appendix E.
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Section 1.
-/

public section

open Filter IsManifold Set Topology
open scoped ContDiff Manifold TauCeti.ComplexManifold

noncomputable section

namespace TauCeti

open SmoothAlmostComplexStructure

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]

/-! ### Isothermal charts -/

variable (j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M) in
/-- A chart `e : M → ℂ` of a real surface is *isothermal* for the almost complex structure `j`
when it belongs to the real `C¹` maximal atlas and `j = i` in it: at every point of its source it
is pseudoholomorphic from `j` to multiplication by `i`, that is, its differential carries `j` to
multiplication by `i`. -/
structure IsIsothermalChart (e : OpenPartialHomeomorph M ℂ) : Prop where
  /-- An isothermal chart is a chart of the real `C¹` maximal atlas. -/
  mem_maximalAtlas : e ∈ maximalAtlas 𝓘(ℝ, ℂ) 1 M
  /-- The differential of an isothermal chart carries `j` to multiplication by `i`. -/
  isPseudoholomorphicAt : ∀ x ∈ e.source, IsPseudoholomorphicAt j (ofComplexManifold ℂ ℂ) e x

namespace IsIsothermalChart

variable {j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M} {e e' : OpenPartialHomeomorph M ℂ}
  {x : M} {z : ℂ}

/-- An isothermal chart is a differentiable open partial homeomorphism. -/
theorem mdifferentiable (he : IsIsothermalChart j e) : e.MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) :=
  mdifferentiable_of_mem_maximalAtlas he.mem_maximalAtlas

/-- In an isothermal chart, `j = i`: the differential of the chart carries `j` to multiplication
by `i`. -/
theorem mfderiv_apply_commute (he : IsIsothermalChart j e) (hx : x ∈ e.source)
    (v : TangentSpace 𝓘(ℝ, ℂ) x) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x (j x v) =
      ofComplexManifold ℂ ℂ (e x) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e x v) :=
  (he.isPseudoholomorphicAt x hx).mfderiv_apply_commute v

/-- The inverse of an isothermal chart is pseudoholomorphic at every point of its target, from
multiplication by `i` to `j`. -/
theorem isPseudoholomorphicAt_symm (he : IsIsothermalChart j e) (hz : z ∈ e.target) :
    IsPseudoholomorphicAt (ofComplexManifold ℂ ℂ) j e.symm z :=
  he.mdifferentiable.isPseudoholomorphicAt_symm hz (he.isPseudoholomorphicAt _ (e.map_target hz))

/-- **The transition between two isothermal charts is holomorphic.** Its differential commutes
with multiplication by `i`, which is the Cauchy–Riemann equation. -/
theorem differentiableOn_symm_trans (he : IsIsothermalChart j e) (he' : IsIsothermalChart j e') :
    DifferentiableOn ℂ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by
  intro z hz
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
  have h := (he'.isPseudoholomorphicAt _ hz.2).comp (he.isPseudoholomorphicAt_symm hz.1)
  rw [isPseudoholomorphicAt_ofComplexManifold_iff, mdifferentiableAt_iff_differentiableAt] at h
  exact h.differentiableWithinAt

/-- **The transition between two isothermal charts is analytic.** -/
theorem analyticOnNhd_symm_trans (he : IsIsothermalChart j e) (he' : IsIsothermalChart j e') :
    AnalyticOnNhd ℂ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source :=
  (he.differentiableOn_symm_trans he').analyticOnNhd (e.symm ≫ₕ e').open_source

end IsIsothermalChart

/-- Complex conjugation is not an isothermal chart of `ℂ` for multiplication by `i`: its
differential anticommutes with `i`. This is a check that isothermal charts preserve orientation
and are not merely conformal. -/
theorem not_isIsothermalChart_conj :
    ¬ IsIsothermalChart (ofComplexManifold ℂ ℂ)
      Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph := by
  intro h
  have hd : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph 0 =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
    rw [mfderiv_eq_fderiv]
    simp only [mfld_simps, ContinuousLinearEquiv.coe_toHomeomorph]
    exact Complex.conjCLE.fderiv
  have h1 := h.mfderiv_apply_commute (mem_univ 0) (1 : ℂ)
  rw [hd] at h1
  -- Read both sides of `h1` through `ofComplexManifold_apply`: the tangent spaces of `ℂ` are `ℂ`,
  -- on which `ofComplexManifold ℂ ℂ` is multiplication by `i`.
  have h2 : Complex.conjCLE (Complex.I • (1 : ℂ)) = Complex.I • Complex.conjCLE (1 : ℂ) :=
    (congrArg Complex.conjCLE (ofComplexManifold_apply (E := ℂ) 0 1).symm).trans
      (h1.trans (ofComplexManifold_apply (E := ℂ) _ _))
  rw [Complex.conjCLE_apply, Complex.conjCLE_apply] at h2
  norm_num [Complex.ext_iff] at h2

/-! ### The complex curve of an almost complex surface -/

variable (j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M)

/-- Planar isothermal coordinates pull back through a chart of the real maximal atlas. -/
private theorem isIsothermalChart_trans_of_fderiv_comp {q : OpenPartialHomeomorph M ℂ}
    (hq : q ∈ maximalAtlas 𝓘(ℝ, ℂ) 1 M) {e : OpenPartialHomeomorph ℂ ℂ}
    (he : ∀ z ∈ e.source, ContDiffAt ℝ 1 e z)
    (hes : ∀ z ∈ e.target, ContDiffAt ℝ 1 e.symm z)
    (hlin : ∀ z ∈ e.source, ∀ v,
      fderiv ℝ e z (j.chartPushforward q z v) = Complex.I * fderiv ℝ e z v) :
    IsIsothermalChart j (q.trans e) := by
  have hqd : ∀ y ∈ q.source, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) q y :=
    fun y hy ↦ mdifferentiableAt_of_mem_maximalAtlas hq hy
  have hqsd : ∀ z ∈ q.target, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) q.symm z :=
    fun z hz ↦ mdifferentiableAt_symm_of_mem_maximalAtlas hq hz
  refine ⟨trans_mem_maximalAtlas_of_contDiffAt hq he hes, fun y hy ↦ ?_⟩
  rw [OpenPartialHomeomorph.trans_source] at hy
  have hed : HasFDerivAt e (fderiv ℝ e (q y)) (q y) :=
    ((he _ hy.2).differentiableAt one_ne_zero).hasFDerivAt
  -- The derivative of `q` carries `j` to `j` read in `q`, which `e` carries to `i`.
  have hcomm := (j.toContMDiff ⊤).mfderiv_comp_toEndomorphism q hy.1 (hqd y hy.1)
    (hqsd _ (q.map_source hy.1))
  rw [toContMDiff_chartPushforward] at hcomm
  refine isPseudoholomorphicAt_of_hasMFDerivAt
    (u' := (fderiv ℝ e (q y)).comp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) q y))
    (hed.hasMFDerivAt.comp y (hqd y hy.1).hasMFDerivAt) fun w ↦ ?_
  -- The last step is elaborated late, so that its tangent-space type is read as `ℂ`.
  calc _ = fderiv ℝ e (q y) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) q y (j.toContMDiff ⊤ y w)) := by
        rw [toContMDiff_apply]
        exact ContinuousLinearMap.comp_apply _ _ _
    _ = fderiv ℝ e (q y) (j.chartPushforward q (q y) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) q y w)) :=
        congrArg _ (DFunLike.congr_fun hcomm w)
    _ = Complex.I * fderiv ℝ e (q y) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) q y w) := hlin _ hy.2 _
    _ = _ := by exact (ofComplexManifold_apply (E := ℂ) (M := ℂ) _ _).symm

/-- Smooth planar coordinates give smooth isothermal charts on the original surface. -/
private theorem SmoothAlmostComplexStructure.exists_smooth_isIsothermalChart (x : M) :
    ∃ e : OpenPartialHomeomorph M ℂ, IsIsothermalChart j e ∧ x ∈ e.source ∧
      e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M := by
  set q := chartAt ℂ x
  have hxq : x ∈ q.source := mem_chart_source ℂ x
  have hJ : ContDiffOn ℝ ∞ (j.chartPushforward q) q.target :=
    j.contDiffOn_chartPushforward contMDiffOn_chart contMDiffOn_chart_symm
  obtain ⟨e, hxe, -, -, he, hes, hlin⟩ :=
    Beltrami.exists_centered_smooth_isothermal_chart hJ q.open_target (q.map_source hxq)
      (fun z hz v ↦ by
        simpa only [toContMDiff_chartPushforward] using
          (j.toContMDiff ⊤).chartPushforward_apply_chartPushforward_apply q hz
            (mdifferentiableAt_atlas (chart_mem_atlas ℂ x) (q.map_target hz))
            (mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ x) hz) v)
  have hA : q.trans e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M :=
    trans_mem_maximalAtlas_of_contDiffAt (chart_mem_maximalAtlas x)
      (fun z hz ↦ he.contDiffAt (e.open_source.mem_nhds hz))
      (fun z hz ↦ hes.contDiffAt (e.open_target.mem_nhds hz))
  refine ⟨q.trans e, isIsothermalChart_trans_of_fderiv_comp j (chart_mem_maximalAtlas x)
    (fun z hz ↦ (he.contDiffAt (e.open_source.mem_nhds hz)).of_le (by simp))
    (fun z hz ↦ (hes.contDiffAt (e.open_target.mem_nhds hz)).of_le (by simp)) hlin,
    ⟨hxq, hxe⟩, hA⟩

/-- **Isothermal charts exist.** Every smooth almost complex structure `j` on a real surface has
isothermal charts: every point `x` lies in the source of a chart of the real `C¹` maximal atlas in
which `j = i`. Read in a chart of `M`, `j` is a smooth field of complex structures on the plane,
and the Beltrami equation straightens it
(`TauCeti.Beltrami.exists_isothermal_chart_of_contDiffAt_of_sq_eq_neg_one`). So every
almost complex structure in real dimension two is integrable: `IsothermalSurface j` is a complex
curve. -/
theorem SmoothAlmostComplexStructure.exists_isIsothermalChart (x : M) :
    ∃ e : OpenPartialHomeomorph M ℂ, IsIsothermalChart j e ∧ x ∈ e.source := by
  obtain ⟨e, he, hx, -⟩ := j.exists_smooth_isIsothermalChart x
  exact ⟨e, he, hx⟩

variable {j} in
/-- Every isothermal chart belongs to the smooth maximal atlas: its transitions with smooth
isothermal charts are holomorphic. -/
theorem IsIsothermalChart.mem_maximalAtlas_infty
    {e : OpenPartialHomeomorph M ℂ} (he : IsIsothermalChart j e) :
    e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M := by
  apply (IsManifold.mem_maximalAtlas_iff_contMDiffOn _).mpr
  constructor
  · intro x hx
    obtain ⟨e', he', hx', hA⟩ := j.exists_smooth_isIsothermalChart x
    have hT : ContDiffOn ℝ ∞ (e'.symm.trans e) (e'.symm.trans e).source :=
      ((he'.differentiableOn_symm_trans he).contDiffOn
        (e'.symm.trans e).open_source).restrict_scalars ℝ
    have hxT : e' x ∈ (e'.symm.trans e).source :=
      e'.toPartialEquiv.mem_symm_trans_source hx' hx
    have hTc := (hT.contDiffAt ((e'.symm.trans e).open_source.mem_nhds hxT)).contMDiffAt
    refine ((hTc.comp x (contMDiffAt_of_mem_maximalAtlas hA hx')).congr_of_eventuallyEq
      ?_).contMDiffWithinAt
    filter_upwards [e'.open_source.mem_nhds hx'] with y hy
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans, e'.left_inv hy]
  · intro z hz
    obtain ⟨e', he', hx', hA⟩ := j.exists_smooth_isIsothermalChart (e.symm z)
    have hT : ContDiffOn ℝ ∞ (e.symm.trans e') (e.symm.trans e').source :=
      ((he.differentiableOn_symm_trans he').contDiffOn
        (e.symm.trans e').open_source).restrict_scalars ℝ
    have hzT : z ∈ (e.symm.trans e').source := ⟨hz, hx'⟩
    have hTc := (hT.contDiffAt ((e.symm.trans e').open_source.mem_nhds hzT)).contMDiffAt
    have hEc : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e'.symm ((e.symm.trans e') z) := by
      simpa using contMDiffAt_symm_of_mem_maximalAtlas hA (e'.map_source hx')
    refine ((hEc.comp z hTc).congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [(e.symm.trans e').open_source.mem_nhds hzT] with w hw
    exact (e'.left_inv hw.2).symm

/-- The surface `M` with the complex charted space structure given by the isothermal charts of
`j`, a copy of `M` through `IsothermalSurface.homeomorph`. It is a complex analytic curve. -/
structure IsothermalSurface (j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M) where
  /-- The point of `IsothermalSurface j` corresponding to a point of `M`. -/
  ofSurface ::
  /-- The point of `M` corresponding to a point of `IsothermalSurface j`. -/
  toSurface : M

namespace IsothermalSurface

instance instTopologicalSpace : TopologicalSpace (IsothermalSurface j) :=
  TopologicalSpace.induced toSurface ‹_›

/-- The isothermal surface of `j` is homeomorphic to `M`, through the identity. -/
def homeomorph : IsothermalSurface j ≃ₜ M where
  toFun := toSurface
  invFun := ofSurface
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 continuous_id

@[simp]
theorem homeomorph_apply (p : IsothermalSurface j) : homeomorph j p = p.toSurface :=
  (rfl)

@[simp]
theorem homeomorph_symm_apply (x : M) : (homeomorph j).symm x = ofSurface x :=
  (rfl)

/-- The isothermal surface of `j` is charted by the isothermal charts of `j`. -/
instance instChartedSpace : ChartedSpace ℂ (IsothermalSurface j) where
  atlas := (homeomorph j).transOpenPartialHomeomorph '' {e | IsIsothermalChart j e}
  chartAt p := (homeomorph j).transOpenPartialHomeomorph
    (j.exists_isIsothermalChart p.toSurface).choose
  mem_chart_source p := by
    simpa using (j.exists_isIsothermalChart p.toSurface).choose_spec.2
  chart_mem_atlas p :=
    ⟨_, (j.exists_isIsothermalChart p.toSurface).choose_spec.1, rfl⟩

variable {j} in
/-- The charts of the isothermal surface of `j` are exactly the isothermal charts of `j`, read
through `homeomorph`. -/
theorem mem_atlas_iff {c : OpenPartialHomeomorph (IsothermalSurface j) ℂ} :
    c ∈ atlas ℂ (IsothermalSurface j) ↔
      ∃ e, IsIsothermalChart j e ∧ c = (homeomorph j).transOpenPartialHomeomorph e :=
  ⟨fun ⟨e, he, h⟩ ↦ ⟨e, he, h.symm⟩, fun ⟨e, he, h⟩ ↦ ⟨e, he, h.symm⟩⟩

variable {j} in
/-- An isothermal chart of `j`, read through `homeomorph`, is a chart of the isothermal surface
of `j`. -/
theorem transOpenPartialHomeomorph_mem_atlas {e : OpenPartialHomeomorph M ℂ}
    (he : IsIsothermalChart j e) :
    (homeomorph j).transOpenPartialHomeomorph e ∈ atlas ℂ (IsothermalSurface j) :=
  mem_atlas_iff.2 ⟨e, he, rfl⟩

variable {j} in
/-- A chart of the isothermal surface of `j`, read on `M` through `homeomorph`, is an isothermal
chart of `j`; for instance `chartAt ℂ p`. -/
theorem isIsothermalChart_symm_transOpenPartialHomeomorph
    {c : OpenPartialHomeomorph (IsothermalSurface j) ℂ} (hc : c ∈ atlas ℂ (IsothermalSurface j)) :
    IsIsothermalChart j ((homeomorph j).symm.transOpenPartialHomeomorph c) := by
  obtain ⟨e, he, rfl⟩ := mem_atlas_iff.1 hc
  rwa [Homeomorph.symm_transOpenPartialHomeomorph_transOpenPartialHomeomorph]

/-- **The isothermal charts form a complex analytic atlas.** -/
instance instIsManifold : IsManifold 𝓘(ℂ) ω (IsothermalSurface j) := by
  refine isManifold_of_contDiffOn 𝓘(ℂ) ω _ ?_
  rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, inter_univ,
    preimage_id_eq, CompTriple.comp_eq, Homeomorph.transOpenPartialHomeomorph_symm_trans]
  exact (he.differentiableOn_symm_trans he').contDiffOn (e.symm ≫ₕ e').open_source

/-! ### The isothermal surface carries `j` -/

/-- The identity from the isothermal surface of `j` to `M` is a smooth real map. -/
theorem contMDiff_homeomorph : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (homeomorph j) := by
  intro p
  obtain ⟨e, he, hx⟩ := j.exists_isIsothermalChart p.toSurface
  set c := (homeomorph j).transOpenPartialHomeomorph e
  have hc : c ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ (IsothermalSurface j) :=
    subset_maximalAtlas (transOpenPartialHomeomorph_mem_atlas he)
  -- Near `p`, the identity is the inverse of `e` after the chart `c`.
  exact ((contMDiffAt_symm_of_mem_maximalAtlas he.mem_maximalAtlas_infty (e.map_source hx)).comp p
    (contMDiffAt_of_mem_maximalAtlas hc (by simpa [c] using hx)))
    |>.congr_of_eventuallyEq ((homeomorph j).eventuallyEq_symm_comp_transOpenPartialHomeomorph hx)

/-- The identity from `M` to the isothermal surface of `j` is a smooth real map. -/
theorem contMDiff_homeomorph_symm : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (homeomorph j).symm := by
  intro x
  obtain ⟨e, he, hx⟩ := j.exists_isIsothermalChart x
  set c := (homeomorph j).transOpenPartialHomeomorph e
  have hc : c ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ (IsothermalSurface j) :=
    subset_maximalAtlas (transOpenPartialHomeomorph_mem_atlas he)
  -- Near `x`, the identity is the inverse of the chart `c` after `e`.
  exact ((contMDiffAt_symm_of_mem_maximalAtlas hc (by simpa [c] using e.map_source hx)).comp x
    (contMDiffAt_of_mem_maximalAtlas he.mem_maximalAtlas_infty hx))
    |>.congr_of_eventuallyEq
      ((homeomorph j).symm_eventuallyEq_symm_transOpenPartialHomeomorph_comp hx)

/-- The identity from the isothermal surface of `j` to `M`, as a smooth real diffeomorphism. -/
def diffeomorph : IsothermalSurface j ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ M where
  toEquiv := (homeomorph j).toEquiv
  contMDiff_toFun := contMDiff_homeomorph j
  contMDiff_invFun := contMDiff_homeomorph_symm j

@[simp]
theorem coe_diffeomorph : ⇑(diffeomorph j) = homeomorph j :=
  (rfl)

@[simp]
theorem coe_diffeomorph_symm : ⇑(diffeomorph j).symm = (homeomorph j).symm :=
  (rfl)

/-- **The induced almost complex structure is `j`.** The identity from the isothermal surface of
`j` to `M` is pseudoholomorphic from `ofComplexManifold` to `j`. -/
theorem isPseudoholomorphic_homeomorph :
    IsPseudoholomorphic (ofComplexManifold ℂ (IsothermalSurface j)) j (homeomorph j) := by
  rw [isPseudoholomorphic_iff]
  intro p
  obtain ⟨e, he, hx⟩ := j.exists_isIsothermalChart p.toSurface
  set c := (homeomorph j).transOpenPartialHomeomorph e
  have hc := transOpenPartialHomeomorph_mem_atlas he
  have hcp : IsPseudoholomorphicAt (ofComplexManifold ℂ (IsothermalSurface j))
      (ofComplexManifold ℂ ℂ) c p :=
    isPseudoholomorphicAt_ofComplexManifold_iff.2
      (mdifferentiableAt_atlas hc (by simpa [c] using hx))
  exact (IsPseudoholomorphicAt.comp (u := c) (x := p)
    (he.isPseudoholomorphicAt_symm (e.map_source hx)) hcp).congr_of_eventuallyEq
    ((homeomorph j).eventuallyEq_symm_comp_transOpenPartialHomeomorph hx)

/-- **The induced almost complex structure is `j`.** The identity from `M` to the isothermal
surface of `j` is pseudoholomorphic from `j` to `ofComplexManifold`. -/
theorem isPseudoholomorphic_homeomorph_symm :
    IsPseudoholomorphic j (ofComplexManifold ℂ (IsothermalSurface j)) (homeomorph j).symm := by
  rw [isPseudoholomorphic_iff]
  intro x
  obtain ⟨e, he, hx⟩ := j.exists_isIsothermalChart x
  set c := (homeomorph j).transOpenPartialHomeomorph e
  have hc := transOpenPartialHomeomorph_mem_atlas he
  have hcz : IsPseudoholomorphicAt (ofComplexManifold ℂ ℂ)
      (ofComplexManifold ℂ (IsothermalSurface j)) c.symm (e x) :=
    isPseudoholomorphicAt_ofComplexManifold_iff.2 (mdifferentiableAt_atlas_symm hc
      (by simpa [c] using e.map_source hx))
  exact (IsPseudoholomorphicAt.comp (v := c.symm) hcz (he.isPseudoholomorphicAt x hx))
    |>.congr_of_eventuallyEq
      ((homeomorph j).symm_eventuallyEq_symm_transOpenPartialHomeomorph_comp hx)

end IsothermalSurface

end

/-! ### Complex curves -/

section ComplexCurve

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X]
  {e : OpenPartialHomeomorph X ℂ}

/-- **On a complex curve, the isothermal charts are the holomorphic charts.** A chart is isothermal
for the almost complex structure of the complex curve exactly when it is a chart of the
holomorphic maximal atlas. -/
theorem isIsothermalChart_ofComplexManifold_iff :
    IsIsothermalChart (ofComplexManifold ℂ X) e ↔ e ∈ maximalAtlas 𝓘(ℂ) 1 X := by
  refine ⟨fun he ↦ e.mem_maximalAtlas_of_contMDiffOn_symm ?_, fun he ↦
    ⟨IsManifold.maximalAtlas_subset_restrictScalars ℝ he, fun x hx ↦
      isPseudoholomorphicAt_ofComplexManifold_iff.2 (mdifferentiableAt_of_mem_maximalAtlas he hx)⟩⟩
  refine MDifferentiableOn.contMDiffOn (fun z hz ↦ ?_) e.open_target
  exact (isPseudoholomorphicAt_ofComplexManifold_iff.1
    (he.isPseudoholomorphicAt_symm hz)).mdifferentiableWithinAt

/-- **The isothermal surface of a complex curve is the complex curve.** The identity from the
isothermal surface of the almost complex structure of a complex curve `X` to `X` is a
biholomorphism. -/
def IsothermalSurface.biholomorph :
    IsothermalSurface (ofComplexManifold ℂ X) ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ X where
  toEquiv := (homeomorph (ofComplexManifold ℂ X)).toEquiv
  contMDiff_toFun := MDifferentiable.contMDiff (isPseudoholomorphic_ofComplexManifold_iff.1
    (isPseudoholomorphic_homeomorph (ofComplexManifold ℂ X)))
  contMDiff_invFun := MDifferentiable.contMDiff (isPseudoholomorphic_ofComplexManifold_iff.1
    (isPseudoholomorphic_homeomorph_symm (ofComplexManifold ℂ X)))

@[simp]
theorem IsothermalSurface.coe_biholomorph :
    ⇑(biholomorph (X := X)) = homeomorph (ofComplexManifold ℂ X) :=
  (rfl)

@[simp]
theorem IsothermalSurface.coe_biholomorph_symm :
    ⇑(biholomorph (X := X)).symm = (homeomorph (ofComplexManifold ℂ X)).symm :=
  (rfl)

end ComplexCurve

end TauCeti

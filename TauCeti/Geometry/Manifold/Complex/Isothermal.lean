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

/-!
# Isothermal charts of an almost complex surface

Let `M` be a real surface, a smooth manifold modelled on `𝓘(ℝ, ℂ)`, with a smooth almost complex
structure `j`. A chart `e : M → ℂ` of the real `C¹` maximal atlas is *isothermal* for `j` when
`j = i` in it: its differential carries `j` to multiplication by `i` at every point of its source.

The derivative of the transition map between two isothermal charts commutes with multiplication
by `i`: this is the Cauchy–Riemann equation, so the transition is holomorphic, hence analytic. If
isothermal charts cover `M` (`SmoothAlmostComplexStructure.HasIsothermalCharts`), they are
therefore the atlas of a complex analytic curve `TauCeti.IsothermalSurface j`, a copy of `M`. The
identity of `M` is then a real `C¹` diffeomorphism `IsothermalSurface.diffeomorph` from this
copy to `M`, which carries the almost complex structure `ofComplexManifold` of the copy to `j`.

Conversely, on a complex curve `X` the isothermal charts of `ofComplexManifold ℂ X` are exactly the
holomorphic charts, so isothermal charts cover `X`, and the identity is a biholomorphism
`IsothermalSurface.biholomorph` from the complex curve `IsothermalSurface (ofComplexManifold ℂ X)`
to `X`. The two constructions are mutually inverse.

That isothermal charts exist, that is `HasIsothermalCharts j` for every smooth `j` (the
integrability of almost complex structures in real dimension two), is not proved here: it follows
from solving the Beltrami equation (McDuff–Salamon, Appendix E).

## Main declarations

* `TauCeti.IsIsothermalChart j e`: the chart `e` belongs to the real `C¹` maximal atlas and `j = i`
  in it.
* `TauCeti.IsIsothermalChart.differentiableOn_symm_trans`,
  `TauCeti.IsIsothermalChart.analyticOnNhd_symm_trans`: the transition map between two isothermal
  charts is holomorphic, hence analytic.
* `TauCeti.IsothermalSurface j`: the surface `M` charted by the isothermal charts of `j`; it is a
  complex analytic curve, `IsManifold 𝓘(ℂ) ω (IsothermalSurface j)`.
* `TauCeti.IsothermalSurface.mem_atlas_iff`: its charts are exactly the isothermal charts of `j`,
  read through `IsothermalSurface.homeomorph`.
* `TauCeti.IsothermalSurface.diffeomorph`: the identity, a `C¹` diffeomorphism of real surfaces;
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
  ⟨fun _ hx ↦
      (mdifferentiableAt_of_mem_maximalAtlas he.mem_maximalAtlas hx).mdifferentiableWithinAt,
    fun _ hz ↦
      (mdifferentiableAt_symm_of_mem_maximalAtlas he.mem_maximalAtlas hz).mdifferentiableWithinAt⟩

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
    IsPseudoholomorphicAt (ofComplexManifold ℂ ℂ) j e.symm z := by
  have hd := he.mdifferentiable
  have hx : e.symm z ∈ e.source := e.map_target hz
  refine isPseudoholomorphicAt_of_hasMFDerivAt (hd.mdifferentiableAt_symm hz).hasMFDerivAt
    fun w ↦ hd.mfderiv_injective hx ?_
  -- Apply the differential `u` of `e` at `e.symm z`, which inverts that of `e.symm` at `z` and
  -- carries `j` to multiplication by `i`.
  have hinv (a : TangentSpace 𝓘(ℝ, ℂ) z) :
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e (e.symm z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e.symm z a) = a :=
    DFunLike.congr_fun (hd.comp_symm_deriv hz) a
  rw [he.mfderiv_apply_commute hx, hinv, hinv]
  exact (ofComplexManifold_apply (E := ℂ) z w).trans (ofComplexManifold_apply (E := ℂ) _ w).symm

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
    exact Complex.conjCLE.fderiv
  have h1 := h.mfderiv_apply_commute (mem_univ 0) (1 : ℂ)
  rw [hd] at h1
  have h2 : (starRingEnd ℂ) (Complex.I * 1) = Complex.I * (starRingEnd ℂ) 1 :=
    (congrArg Complex.conjCLE (ofComplexManifold_apply (E := ℂ) 0 1).symm).trans
      (h1.trans (ofComplexManifold_apply (E := ℂ) _ _))
  norm_num [Complex.ext_iff] at h2

/-! ### The complex curve of an almost complex surface with isothermal charts -/

variable (j : SmoothAlmostComplexStructure 𝓘(ℝ, ℂ) M)

/-- An almost complex structure on a real surface *has isothermal charts* when every point lies in
the source of an isothermal chart. -/
class SmoothAlmostComplexStructure.HasIsothermalCharts : Prop where
  /-- Every point lies in the source of an isothermal chart. -/
  exists_isIsothermalChart (x : M) : ∃ e : OpenPartialHomeomorph M ℂ,
    IsIsothermalChart j e ∧ x ∈ e.source

/-- The surface `M` with the complex charted space structure given by the isothermal charts of
`j`, a copy of `M` through `IsothermalSurface.homeomorph`. When `j` has isothermal charts, it is a
complex analytic curve. -/
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

section transOpenPartialHomeomorph

variable {e : OpenPartialHomeomorph M ℂ}

variable {j} in
/-- A point of the isothermal surface lies in the source of `e` read through `homeomorph` exactly
when the corresponding point of `M` lies in the source of `e`. -/
theorem mem_transOpenPartialHomeomorph_source {p : IsothermalSurface j} :
    p ∈ ((homeomorph j).transOpenPartialHomeomorph e).source ↔ p.toSurface ∈ e.source :=
  (Iff.rfl)

/-- A point of `ℂ` lies in the target of `e` read through `homeomorph` exactly when it lies in the
target of `e`. -/
theorem mem_transOpenPartialHomeomorph_target {z : ℂ} :
    z ∈ ((homeomorph j).transOpenPartialHomeomorph e).target ↔ z ∈ e.target :=
  (Iff.rfl)

variable {j} in
/-- Near a point whose image lies in the source of `e`, the identity to `M` is the inverse of `e`
after the chart `(homeomorph j).transOpenPartialHomeomorph e`. -/
theorem homeomorph_eventuallyEq_symm_comp {p : IsothermalSurface j}
    (hp : p.toSurface ∈ e.source) :
    homeomorph j =ᶠ[𝓝 p] e.symm ∘ (homeomorph j).transOpenPartialHomeomorph e := by
  filter_upwards [((homeomorph j).transOpenPartialHomeomorph e).open_source.mem_nhds
    (mem_transOpenPartialHomeomorph_source.2 hp)] with q hq
  simp [e.left_inv (mem_transOpenPartialHomeomorph_source.1 hq)]

variable {j} in
/-- Near a point of the source of `e`, the identity from `M` is the inverse of the chart
`(homeomorph j).transOpenPartialHomeomorph e` after `e`. -/
theorem homeomorph_symm_eventuallyEq_symm_comp {x : M} (hx : x ∈ e.source) :
    (homeomorph j).symm =ᶠ[𝓝 x] ((homeomorph j).transOpenPartialHomeomorph e).symm ∘ e := by
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  simp [e.left_inv hy]

end transOpenPartialHomeomorph

variable [j.HasIsothermalCharts]

/-- The isothermal surface of `j` is charted by the isothermal charts of `j`. -/
instance instChartedSpace : ChartedSpace ℂ (IsothermalSurface j) where
  atlas := (homeomorph j).transOpenPartialHomeomorph '' {e | IsIsothermalChart j e}
  chartAt p := (homeomorph j).transOpenPartialHomeomorph
    (HasIsothermalCharts.exists_isIsothermalChart (j := j) p.toSurface).choose
  mem_chart_source p := mem_transOpenPartialHomeomorph_source.2
    (HasIsothermalCharts.exists_isIsothermalChart (j := j) p.toSurface).choose_spec.2
  chart_mem_atlas p :=
    ⟨_, (HasIsothermalCharts.exists_isIsothermalChart (j := j) p.toSurface).choose_spec.1, rfl⟩

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

/-- The identity from the isothermal surface of `j` to `M` is a real `C¹` map. -/
theorem contMDiff_homeomorph : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 (homeomorph j) := by
  intro p
  obtain ⟨e, he, hx⟩ := HasIsothermalCharts.exists_isIsothermalChart (j := j) p.toSurface
  set c := (homeomorph j).transOpenPartialHomeomorph e
  have hc : c ∈ maximalAtlas 𝓘(ℝ, ℂ) 1 (IsothermalSurface j) :=
    subset_maximalAtlas (transOpenPartialHomeomorph_mem_atlas he)
  -- Near `p`, the identity is the inverse of `e` after the chart `c`.
  exact ((contMDiffAt_symm_of_mem_maximalAtlas he.mem_maximalAtlas (e.map_source hx)).comp p
    (contMDiffAt_of_mem_maximalAtlas hc (mem_transOpenPartialHomeomorph_source.2 hx)))
    |>.congr_of_eventuallyEq (homeomorph_eventuallyEq_symm_comp hx)

/-- The identity from `M` to the isothermal surface of `j` is a real `C¹` map. -/
theorem contMDiff_homeomorph_symm : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) 1 (homeomorph j).symm := by
  intro x
  obtain ⟨e, he, hx⟩ := HasIsothermalCharts.exists_isIsothermalChart (j := j) x
  set c := (homeomorph j).transOpenPartialHomeomorph e
  have hc : c ∈ maximalAtlas 𝓘(ℝ, ℂ) 1 (IsothermalSurface j) :=
    subset_maximalAtlas (transOpenPartialHomeomorph_mem_atlas he)
  -- Near `x`, the identity is the inverse of the chart `c` after `e`.
  exact ((contMDiffAt_symm_of_mem_maximalAtlas hc
    ((mem_transOpenPartialHomeomorph_target j).2 (e.map_source hx))).comp x
    (contMDiffAt_of_mem_maximalAtlas he.mem_maximalAtlas hx))
    |>.congr_of_eventuallyEq (homeomorph_symm_eventuallyEq_symm_comp hx)

/-- The identity from the isothermal surface of `j` to `M`, as a real `C¹` diffeomorphism. -/
def diffeomorph : IsothermalSurface j ≃ₘ^1⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ M where
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
  obtain ⟨e, he, hx⟩ := HasIsothermalCharts.exists_isIsothermalChart (j := j) p.toSurface
  set c := (homeomorph j).transOpenPartialHomeomorph e
  have hc := transOpenPartialHomeomorph_mem_atlas he
  have hcp : IsPseudoholomorphicAt (ofComplexManifold ℂ (IsothermalSurface j))
      (ofComplexManifold ℂ ℂ) c p :=
    isPseudoholomorphicAt_ofComplexManifold_iff.2
      (mdifferentiableAt_atlas hc (mem_transOpenPartialHomeomorph_source.2 hx))
  exact (IsPseudoholomorphicAt.comp (u := c) (x := p)
    (he.isPseudoholomorphicAt_symm (e.map_source hx)) hcp).congr_of_eventuallyEq
    (homeomorph_eventuallyEq_symm_comp hx)

/-- **The induced almost complex structure is `j`.** The identity from `M` to the isothermal
surface of `j` is pseudoholomorphic from `j` to `ofComplexManifold`. -/
theorem isPseudoholomorphic_homeomorph_symm :
    IsPseudoholomorphic j (ofComplexManifold ℂ (IsothermalSurface j)) (homeomorph j).symm := by
  rw [isPseudoholomorphic_iff]
  intro x
  obtain ⟨e, he, hx⟩ := HasIsothermalCharts.exists_isIsothermalChart (j := j) x
  set c := (homeomorph j).transOpenPartialHomeomorph e
  have hc := transOpenPartialHomeomorph_mem_atlas he
  have hcz : IsPseudoholomorphicAt (ofComplexManifold ℂ ℂ)
      (ofComplexManifold ℂ (IsothermalSurface j)) c.symm (e x) :=
    isPseudoholomorphicAt_ofComplexManifold_iff.2 (mdifferentiableAt_atlas_symm hc
      ((mem_transOpenPartialHomeomorph_target j).2 (e.map_source hx)))
  exact (IsPseudoholomorphicAt.comp (v := c.symm) hcz (he.isPseudoholomorphicAt x hx))
    |>.congr_of_eventuallyEq (homeomorph_symm_eventuallyEq_symm_comp hx)

end IsothermalSurface

/-! ### Complex curves -/

section ComplexCurve

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ∞ X]
  {e : OpenPartialHomeomorph X ℂ}

/-- **On a complex curve, the isothermal charts are the holomorphic charts.** A chart is isothermal
for the almost complex structure of the complex curve exactly when it is a chart of the
holomorphic maximal atlas. -/
theorem isIsothermalChart_ofComplexManifold_iff :
    IsIsothermalChart (ofComplexManifold ℂ X) e ↔ e ∈ maximalAtlas 𝓘(ℂ) 1 X := by
  refine ⟨fun he ↦ e.mem_maximalAtlas_of_contMDiffOn_symm one_ne_zero ?_, fun he ↦
    ⟨IsManifold.maximalAtlas_subset_restrictScalars ℝ he, fun x hx ↦
      isPseudoholomorphicAt_ofComplexManifold_iff.2 (mdifferentiableAt_of_mem_maximalAtlas he hx)⟩⟩
  refine MDifferentiableOn.contMDiffOn (fun z hz ↦ ?_) e.open_target
  exact (isPseudoholomorphicAt_ofComplexManifold_iff.1
    (he.isPseudoholomorphicAt_symm hz)).mdifferentiableWithinAt

/-- The almost complex structure of a complex curve has isothermal charts: its holomorphic
charts. -/
instance SmoothAlmostComplexStructure.hasIsothermalCharts_ofComplexManifold :
    (ofComplexManifold ℂ X).HasIsothermalCharts :=
  ⟨fun x ↦ ⟨chartAt ℂ x, isIsothermalChart_ofComplexManifold_iff.2 (chart_mem_maximalAtlas x),
    mem_chart_source ℂ x⟩⟩

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

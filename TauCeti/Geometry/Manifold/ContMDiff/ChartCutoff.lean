/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Cutting a function off in a chart

Let `u` be a `C¹` real function on a manifold without boundary and `b` a smooth bump function on
the model space, centred at the chart image of a point `c`, whose closed support ball lies in the
target of the extended chart at `c`. The product `y ↦ b y * u ((extChartAt I c).symm y)` is then a
compactly supported `C¹` function on the model space, agreeing with the coordinate expression of
`u` where `b = 1`. This is the standard way to localize an estimate from the model space to a
manifold. This file records its regularity and the bound on its derivative.

Conversely, a compactly supported function on the model space whose support lies in the chart
target is the coordinate expression of a compactly supported function on the manifold, extended by
zero outside the chart. This is the standard way to transplant a test function from the model
space to a manifold.

## Main results

* `ContDiff.mul_comp_extChartAt_symm`: a `C^n` function supported in the chart target, times the
  coordinate expression of a `C^n` function, is `C^n`.
* `ContDiffBump.contDiff_mul_comp_extChartAt_symm`: the cut-off coordinate expression is `C¹`.
* `ContDiffBump.norm_fderiv_mul_comp_extChartAt_symm_le`: in the chart target its derivative is
  bounded by the derivative of the coordinate expression plus `G |u|`, where `G` bounds the
  derivative of the bump.
* `ContDiffBump.fderiv_mul_comp_extChartAt_symm_eq_zero`: its derivative vanishes outside the
  closed support ball of the bump.
* `OpenPartialHomeomorph.contMDiff_indicator_comp_extend`: for a chart `e` of the maximal atlas,
  a `C^n` function on the model space with compact support in the target of the extended chart,
  read in the chart and extended by zero outside the chart source, is `C^n`.
* `OpenPartialHomeomorph.exists_contMDiff_eq_comp_prodMap`: the same through the product of two
  charts, giving a compactly supported `C^n` function on a product of manifolds.
* `TauCeti.Manifold.exists_contMDiff_comp_extChartAt_symm_eq`: a `C^n` function on the model
  space with compact support in the chart target is the coordinate expression of a compactly
  supported `C^n` function on the manifold.
* `TauCeti.Manifold.exists_contMDiff_transplant`: a `C^n` nonnegative function on the model space
  supported in a compact subset of a coordinate ball transplants to a `C^n` nonnegative compactly
  supported function on the manifold supported in any prescribed set containing the chart
  preimage of the ball.
* `TauCeti.Manifold.exists_contMDiff_eq_comp_extChartAt`: a `C^n` map from the model space to a
  manifold that is constant outside a closed ball in the chart target is the coordinate expression
  of a `C^n` map on the manifold, constant off the chart domain.
-/

public section

open Function Metric Set
open scoped Manifold

namespace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞} {c : M} {u : M → ℝ}

/-- A `C^n` function on the model space supported in the chart target, times the coordinate
expression of a `C^n` function, is a `C^n` function on the model space. -/
theorem mul_comp_extChartAt_symm [I.Boundaryless] [IsManifold I n M] {ψ : E → ℝ}
    (hψ : ContDiff ℝ n ψ) (hψt : tsupport ψ ⊆ (extChartAt I c).target)
    (hu : ContMDiff I 𝓘(ℝ) n u) :
    ContDiff ℝ n fun y ↦ ψ y * u ((extChartAt I c).symm y) := by
  refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
  by_cases hy : y ∈ (extChartAt I c).target
  · exact hψ.contDiffAt.mul ((hu.comp_contMDiffOn (contMDiffOn_extChartAt_symm c)).contDiffOn
      |>.contDiffAt ((isOpen_extChartAt_target c).mem_nhds hy))
  · -- Off the chart target, `ψ` vanishes near `y`.
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds fun h ↦ hy (hψt h)] with z hz
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

end ContDiff

namespace ContDiffBump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {c : M} (b : ContDiffBump (extChartAt I c c)) {u : M → ℝ}

/-- A bump function whose closed support ball lies in the chart target, times the coordinate
expression of a `C¹` function, is a `C¹` function on the model space. -/
theorem contDiff_mul_comp_extChartAt_symm [I.Boundaryless] [IsManifold I 1 M]
    (hb : closedBall (extChartAt I c c) b.rOut ⊆ (extChartAt I c).target)
    (hu : ContMDiff I 𝓘(ℝ) 1 u) :
    ContDiff ℝ 1 fun y ↦ b y * u ((extChartAt I c).symm y) :=
  b.contDiff.mul_comp_extChartAt_symm (b.tsupport_eq.trans_subset hb) hu

/-- The derivative of the cut-off coordinate expression at a point of the chart target is bounded
by the derivative of the coordinate expression plus `G |u|`, where `G` bounds the derivative of
the bump. -/
theorem norm_fderiv_mul_comp_extChartAt_symm_le [I.Boundaryless] [IsManifold I 1 M]
    (hu : ContMDiff I 𝓘(ℝ) 1 u) {G : ℝ} (hG : ∀ y, ‖fderiv ℝ b y‖ ≤ G) {y : E}
    (hy : y ∈ (extChartAt I c).target) :
    ‖fderiv ℝ (fun y ↦ b y * u ((extChartAt I c).symm y)) y‖ ≤
      ‖fderiv ℝ (fun y ↦ u ((extChartAt I c).symm y)) y‖ + G * |u ((extChartAt I c).symm y)| := by
  have hd : DifferentiableAt ℝ (fun y ↦ u ((extChartAt I c).symm y)) y :=
    ((hu.comp_contMDiffOn (contMDiffOn_extChartAt_symm c)).contDiffOn.contDiffAt
      ((isOpen_extChartAt_target c).mem_nhds hy)).differentiableAt one_ne_zero
  rw [fderiv_fun_mul (b.contDiffAt (n := 1).differentiableAt one_ne_zero) hd]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg b.nonneg,
    mul_comm |u _|]
  gcongr
  · exact mul_le_of_le_one_left (norm_nonneg _) b.le_one
  · exact hG y

/-- The cut-off coordinate expression has zero derivative outside the closed support ball of the
bump. -/
theorem fderiv_mul_comp_extChartAt_symm_eq_zero {y : E}
    (hy : y ∉ closedBall (extChartAt I c c) b.rOut) :
    fderiv ℝ (fun y ↦ b y * u ((extChartAt I c).symm y)) y = 0 :=
  notMem_support.1 fun h ↦ hy <| b.tsupport_eq ▸
    tsupport_mul_subset_left (support_fderiv_subset ℝ h)

end ContDiffBump

namespace OpenPartialHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] {n : WithTop ℕ∞}
  {e : OpenPartialHomeomorph M H} {w : E → F}

omit [NormedSpace 𝕜 F] [ChartedSpace H M] in
/-- For a function `w` on the model space whose support is a compact subset of the target of the
extended chart `e.extend I`, the function equal to `w ∘ e.extend I` on the chart source and to `0`
elsewhere is supported in the chart preimage of the support of `w`. -/
theorem tsupport_indicator_comp_extend_subset (hwc : HasCompactSupport w)
    (hwe : tsupport w ⊆ (e.extend I).target) :
    tsupport (e.source.indicator (w ∘ e.extend I)) ⊆ (e.extend I).symm '' tsupport w := by
  refine closure_minimal (fun x hx ↦ ?_)
    (hwc.isCompact.image_of_continuousOn (e.continuousOn_extend_symm.mono hwe)).isClosed
  by_cases hxs : x ∈ e.source
  · rw [mem_support, indicator_of_mem hxs] at hx
    exact ⟨e.extend I x, subset_tsupport _ hx, e.extend_left_inv hxs⟩
  · exact absurd (indicator_of_notMem hxs _) hx

/-- **Transplanting a function through an arbitrary chart.** For a chart `e` of the maximal `C^n`
atlas, and a `C^n` function `w` on the model space whose support is a compact subset of the target
of the extended chart `e.extend I`, the function equal to `w ∘ e.extend I` on the chart source and
to `0` elsewhere is `C^n`. -/
theorem contMDiff_indicator_comp_extend (he : e ∈ IsManifold.maximalAtlas I n M)
    (hw : ContDiff 𝕜 n w) (hwc : HasCompactSupport w) (hwe : tsupport w ⊆ (e.extend I).target) :
    ContMDiff I 𝓘(𝕜, F) n (e.source.indicator (w ∘ e.extend I)) := by
  refine contMDiff_of_tsupport fun x hx ↦ ?_
  -- On the chart source, the function is the coordinate expression `w ∘ e.extend I`.
  obtain ⟨y, hy, rfl⟩ := tsupport_indicator_comp_extend_subset hwc hwe hx
  have hys : (e.extend I).symm y ∈ e.source := by
    simpa only [e.extend_source] using (e.extend I).map_target (hwe hy)
  refine ContMDiffAt.congr_of_eventuallyEq (f := w ∘ e.extend I) ?_
    (Filter.eventually_of_mem (e.open_source.mem_nhds hys) fun z hz ↦ indicator_of_mem hz _)
  exact hw.contMDiff.contMDiffAt.comp _ (e.contMDiffAt_extend he hys)

omit [NormedSpace 𝕜 F] in
/-- **Transplanting a function through a product chart.** For charts `e` of `M` and `e'` of `M'`
in the maximal `C^n` atlases, and a `C^n` function `v` on the product of the model spaces with
compact support in the product of the targets of the extended charts, there is a compactly
supported `C^n` function `K` on `M × M'` equal to `v` read through `e` and `e'` on the product of
the chart sources, and to `0` elsewhere. -/
theorem exists_contMDiff_eq_comp_prodMap [NormedSpace 𝕜 F] {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [T2Space M'] [IsManifold I n M]
    [IsManifold I' n M'] {e' : OpenPartialHomeomorph M' H'}
    (he : e ∈ IsManifold.maximalAtlas I n M) (he' : e' ∈ IsManifold.maximalAtlas I' n M')
    {v : E × E' → F} (hv : ContDiff 𝕜 n v) (hvc : HasCompactSupport v)
    (hvt : tsupport v ⊆ (e.extend I).target ×ˢ (e'.extend I').target) :
    ∃ K : M × M' → F, ContMDiff (I.prod I') 𝓘(𝕜, F) n K ∧ HasCompactSupport K ∧
      (∀ p ∈ e.source ×ˢ e'.source, K p = v (e.extend I p.1, e'.extend I' p.2)) ∧
        ∀ p ∉ e.source ×ˢ e'.source, K p = 0 := by
  -- `K` is `v` read through the product chart `e × e'` of the maximal atlas of `M × M'`.
  have hEt : tsupport v ⊆ ((e.prod e').extend (I.prod I')).target := by
    simpa [extend_prod] using hvt
  refine ⟨(e.prod e').source.indicator (v ∘ (e.prod e').extend (I.prod I')),
    contMDiff_indicator_comp_extend (IsManifold.mem_maximalAtlas_prod he he') hv hvc hEt,
    (hvc.isCompact.image_of_continuousOn
      ((e.prod e').continuousOn_extend_symm.mono hEt)).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_indicator_comp_extend_subset hvc hEt),
    fun p hp ↦ by simp [hp], fun p hp ↦ indicator_of_notMem (by simpa using hp) _⟩

end OpenPartialHomeomorph

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

/-- **Transplanting a function from a chart.** A `C^n` function `w` on the model space whose
support is a compact subset of the target of the extended chart at `c` is, on that target, the
coordinate expression of a compactly supported `C^n` function `u` on `M` whose support lies in the
chart preimage of the support of `w`. -/
theorem exists_contMDiff_comp_extChartAt_symm_eq {n : WithTop ℕ∞} [IsManifold I n M] {c : M}
    {w : E → F} (hw : ContDiff 𝕜 n w) (hwc : HasCompactSupport w)
    (hwt : tsupport w ⊆ (extChartAt I c).target) :
    ∃ u : M → F, ContMDiff I 𝓘(𝕜, F) n u ∧ HasCompactSupport u ∧
      tsupport u ⊆ (extChartAt I c).symm '' tsupport w ∧
      ∀ y ∈ (extChartAt I c).target, u ((extChartAt I c).symm y) = w y := by
  -- `extChartAt I c` is `(chartAt H c).extend I` by definition; unfolding it lets the lemmas
  -- about `e.extend I` with `e = chartAt H c` match syntactically.
  unfold extChartAt at hwt ⊢
  have hsupp := (chartAt H c).tsupport_indicator_comp_extend_subset hwc hwt
  have hK : IsCompact (((chartAt H c).extend I).symm '' tsupport w) :=
    hwc.isCompact.image_of_continuousOn ((chartAt H c).continuousOn_extend_symm.mono hwt)
  refine ⟨_, (chartAt H c).contMDiff_indicator_comp_extend
    (IsManifold.chart_mem_maximalAtlas c) hw hwc hwt,
    hK.of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp, fun y hy ↦ ?_⟩
  -- On the chart target, the function is `w` read through the chart and its inverse.
  rw [indicator_of_mem (by
    simpa only [(chartAt H c).extend_source] using ((chartAt H c).extend I).map_target hy)]
  exact congrArg w (((chartAt H c).extend I).right_inv hy)

end TauCeti.Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {n : WithTop ℕ∞} [IsManifold I n M]

/-- A `C^n` nonnegative function on the model space supported in a compact subset `K` of a
coordinate ball, transplanted to the manifold: it is a `C^n` nonnegative compactly supported
function whose support lies in any `U` containing the chart preimage of the ball, and which agrees
with `w` in the chart. -/
theorem exists_contMDiff_transplant (p : M) {R : ℝ} {U : Set M}
    (hballt : ball (extChartAt I p p) R ⊆ (extChartAt I p).target)
    (hballU : ∀ y ∈ ball (extChartAt I p p) R, (extChartAt I p).symm y ∈ U) {K : Set E}
    (hK : IsCompact K) (hKR : K ⊆ ball (extChartAt I p p) R) {w : E → ℝ}
    (hw : ContDiff ℝ n w) (hw0 : ∀ y, 0 ≤ w y) (hwK : tsupport w ⊆ K) :
    ∃ u : M → ℝ, ContMDiff I 𝓘(ℝ) n u ∧ HasCompactSupport u ∧ tsupport u ⊆ U ∧
      (∀ x, 0 ≤ u x) ∧
      (∀ x ∈ tsupport u, x ∈ (extChartAt I p).source ∧
        extChartAt I p x ∈ ball (extChartAt I p p) R) ∧
      ∀ y ∈ ball (extChartAt I p p) R, u ((extChartAt I p).symm y) = w y := by
  set φ := extChartAt I p
  obtain ⟨u, hu, huc, htsupp, hu_symm⟩ := exists_contMDiff_comp_extChartAt_symm_eq (c := p) hw
    (HasCompactSupport.intro hK fun y hy ↦ image_eq_zero_of_notMem_tsupport fun h ↦
      hy (hwK h)) (hwK.trans (hKR.trans hballt))
  have hsup (x : M) (hx : x ∈ tsupport u) : x ∈ φ.source ∧ φ x ∈ ball (φ p) R := by
    obtain ⟨y, hy, rfl⟩ := htsupp hx
    have hyt := hballt (hKR (hwK hy))
    exact ⟨φ.map_target hyt, by rw [φ.right_inv hyt]; exact hKR (hwK hy)⟩
  refine ⟨u, hu, huc, fun x hx ↦ ?_, fun x ↦ ?_, hsup, fun y hy ↦ hu_symm y (hballt hy)⟩
  · obtain ⟨hxs, hxb⟩ := hsup x hx
    have h := hballU _ hxb
    rwa [φ.left_inv hxs] at h
  · by_cases hx : x ∈ tsupport u
    · obtain ⟨y, hy, rfl⟩ := htsupp hx
      rw [hu_symm y (hballt (hKR (hwK hy)))]
      exact hw0 _
    · rw [image_eq_zero_of_notMem_tsupport hx]

end TauCeti.Manifold

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [ProperSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞} [IsManifold I n M]

/-- **Extending a map constant off a coordinate ball.** A `C^n` map `g` from the model space to a
manifold `N` which is constant, equal to `c`, outside a closed ball inside the target of the
extended chart at `x₀` is, on the chart domain, the coordinate expression of a `C^n` map on `M`
equal to `c` off the chart domain. -/
theorem exists_contMDiff_eq_comp_extChartAt (x₀ : M) {r : ℝ}
    (hball : closedBall (extChartAt I x₀ x₀) r ⊆ (extChartAt I x₀).target) {g : E → N}
    (hg : ContMDiff 𝓘(𝕜, E) J n g) {c : N}
    (hc : ∀ z, r < dist z (extChartAt I x₀ x₀) → g z = c) :
    ∃ f : M → N, ContMDiff I J n f ∧
      (∀ x ∈ (chartAt H x₀).source, f x = g (extChartAt I x₀ x)) ∧
      ∀ x ∉ (chartAt H x₀).source, f x = c := by
  classical
  set φ := extChartAt I x₀
  have hsrc : φ.source = (chartAt H x₀).source := extChartAt_source I x₀
  let f : M → N := fun x ↦ if x ∈ (chartAt H x₀).source then g (φ x) else c
  have hfg : ∀ x ∈ (chartAt H x₀).source, f x = g (φ x) := fun x hx ↦ by simp [f, hx]
  -- Outside the compact preimage `K` of the closed ball, `f` is `c`.
  set K := φ.symm '' closedBall (φ x₀) r
  have hK : IsClosed K := ((isCompact_closedBall _ _).image_of_continuousOn
    ((continuousOn_extChartAt_symm x₀).mono hball)).isClosed
  have hKs : K ⊆ (chartAt H x₀).source := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← hsrc]
    exact φ.map_target (hball hz)
  have hfK (x : M) (hx : x ∉ K) : f x = c := by
    simp only [f]
    split_ifs with hxs
    · refine hc _ (not_le.1 fun h ↦ hx ⟨φ x, mem_closedBall.2 h, φ.left_inv (by rwa [hsrc])⟩)
    · rfl
  -- `f` is smooth on the chart domain and on the complement of `K`, which cover `M`.
  refine ⟨f, contMDiff_of_contMDiffOn_union_of_isOpen
    ((hg.comp_contMDiffOn contMDiffOn_extChartAt).congr hfg) (contMDiffOn_const.congr hfK)
    (eq_univ_of_forall fun x ↦ (em (x ∈ K)).imp (fun h ↦ hKs h) id)
    (chartAt H x₀).open_source hK.isOpen_compl, hfg, fun x hx ↦ by simp [f, hx]⟩

end TauCeti.Manifold

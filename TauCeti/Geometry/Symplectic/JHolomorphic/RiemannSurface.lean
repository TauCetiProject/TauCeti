/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.GermFactorization
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import Mathlib.Topology.DiscreteSubset
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.ExtChartAt.Basic
import TauCeti.Geometry.Symplectic.JHolomorphic.Coincidence
import TauCeti.Geometry.Symplectic.JHolomorphic.CriticalPoint
import TauCeti.Geometry.Symplectic.JHolomorphic.UniqueContinuation
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Chart
import TauCeti.Topology.Codiscrete
import TauCeti.Topology.Separation.Hausdorff

/-!
# Critical points, fibres and coincident branches of pseudoholomorphic curves on Riemann surfaces

Let `S` be a Riemann surface, a complex manifold modelled on `ℂ`, with its almost complex structure
`SmoothAlmostComplexStructure.ofComplexManifold ℂ S`, let `N` be a finite-dimensional manifold
without boundary carrying a smooth almost complex structure `J`, and let `u : S → N` be a
pseudoholomorphic map. Nothing is assumed about `J` beyond smoothness: no taming form, no
integrability and no genericity. This file globalizes the local theory of
`TauCeti.Geometry.Symplectic.JHolomorphic.UniqueContinuation`,
`TauCeti.Geometry.Symplectic.JHolomorphic.CriticalPoint` (McDuff–Salamon, Lemma 2.4.1) and
`TauCeti.Geometry.Symplectic.JHolomorphic.Coincidence` (McDuff–Salamon, Lemma 2.4.3) from
domains in `ℂ` and targets in a normed space to such maps:

* **unique continuation**: on a connected `S`, a `C¹` pseudoholomorphic map that is constant near
  one point is constant (`TauCeti.eq_of_isPseudoholomorphic_of_eventually_eq`);
* **isolated fibres**: if such a map is not constant, each of its fibres is a discrete subset of
  `S` (`TauCeti.setOf_ne_mem_codiscrete_of_isPseudoholomorphic`);
* **isolated critical points**: if such a map is not constant, its critical points, where its
  manifold derivative vanishes, form a discrete subset of `S`
  (`TauCeti.setOf_mfderiv_ne_zero_mem_codiscrete_of_isPseudoholomorphic`);
* **accumulating coincidences factor**: for a second pseudoholomorphic map `u₁ : S' → N` of class
  `C¹`, a target `N` that is Hausdorff and `u` of class `C²` and immersed at `a₀`, if the points
  `b ≠ b₀` at which `u₁` meets the image under `u` of a neighbourhood of `a₀` accumulate at `b₀`,
  however small the neighbourhood, then `u₁ = u ∘ φ` near `b₀` for a map `φ` holomorphic near `b₀`
  with `φ b₀ = a₀` (`TauCeti.germFactorsThrough_of_frequently_mem_image`, and
  `TauCeti.germFactorsThrough_of_tendsto` for sequences of coincidences). In the terms of
  `TauCeti.RiemannSurface.GermFactorsThrough`, the germ of `u₁` at `b₀` factors holomorphically
  through the germ of `u` at `a₀`, and this property is characterized by the accumulation of
  coincidences (`TauCeti.germFactorsThrough_iff_frequently_mem_image`).

On a compact connected Riemann surface a nonconstant `C¹` pseudoholomorphic map therefore has
finitely many critical points (`TauCeti.finite_setOf_mfderiv_eq_zero_of_isPseudoholomorphic`) and
finite fibres (`TauCeti.finite_preimage_singleton_of_isPseudoholomorphic`), so the preimage
`u⁻¹(u(Crit u))` of its critical values is finite
(`TauCeti.finite_preimage_image_setOf_mfderiv_eq_zero_of_isPseudoholomorphic`). This finite
exceptional set is where the factorization of a nonconstant closed curve through a simple curve
starts (McDuff–Salamon, Proposition 2.5.1). Off it the curve is immersed, and the factorization is
built from the relation `Γ₀` under which two points `z` and `ζ` are related when the branches of
`u` at `z` and at `ζ` differ by a holomorphic change of source coordinate,
`GermFactorsThrough u ζ u z`. On the points where `u` is immersed this relation is an equivalence
relation (`TauCeti.equivalence_germFactorsThrough`): it is reflexive and transitive for any map,
and it is symmetric (`TauCeti.RiemannSurface.GermFactorsThrough.symm`) because a factor `φ` with
`u = u ∘ φ` cannot be constant near an immersed point, so the coincidences it produces accumulate.
It is closed there (`TauCeti.germFactorsThrough_of_mem_closure`,
`TauCeti.isClosed_setOf_germFactorsThrough`): near a limit of related pairs, coincidences
accumulate.

The proofs read `u` in the preferred chart `φ` of `S` at a point `x` and the preferred extended
chart `ψ` of `N` at `u x`. Since the charts of `S` are holomorphic, the coordinate expression
`ψ ∘ u ∘ φ⁻¹` solves the Cauchy–Riemann equation `∂ₜw = J_ψ(w) ∂ₛw` for the structure
`J_ψ = J.inChart (u x)` read in `ψ`, which is smooth and squares to `-1` on the chart target; the
local theorems apply to it on a ball about `φ x`. The set of points near which `u` is constant is
open, and it is closed by local unique continuation, which gives the global statement. The critical
points of `u` correspond to those of its coordinate expression because the tangent coordinate
changes of the charts are invertible. For two curves, both are read in the chart of `N` at their
common value; the local factor `φ'` of the coordinate expressions gives the factor
`φ₀⁻¹ ∘ φ' ∘ φ₁` of the curves, for the charts `φ₀` and `φ₁` of the two Riemann surfaces.

## Main results

* `TauCeti.eq_of_isPseudoholomorphic_of_eventually_eq`: unique continuation on a connected
  Riemann surface.
* `TauCeti.setOf_ne_mem_codiscrete_of_isPseudoholomorphic`: the fibres of a nonconstant
  pseudoholomorphic map are discrete.
* `TauCeti.setOf_mfderiv_ne_zero_mem_codiscrete_of_isPseudoholomorphic`: the critical points of a
  nonconstant `C¹` pseudoholomorphic map are isolated.
* `TauCeti.finite_preimage_singleton_of_isPseudoholomorphic`,
  `TauCeti.finite_setOf_mfderiv_eq_zero_of_isPseudoholomorphic`,
  `TauCeti.finite_preimage_image_setOf_mfderiv_eq_zero_of_isPseudoholomorphic`: on a compact
  connected Riemann surface the fibres, the critical set and the preimage of the critical values of
  a nonconstant `C¹` pseudoholomorphic map are finite.
* `TauCeti.germFactorsThrough_of_frequently_mem_image`, `TauCeti.germFactorsThrough_of_tendsto`:
  accumulating coincidences factor a pseudoholomorphic curve (McDuff–Salamon, Lemma 2.4.3).
* `TauCeti.germFactorsThrough_iff_frequently_mem_image`: holomorphic factorization of germs at an
  immersed point is characterized by accumulating coincidences.
* `TauCeti.RiemannSurface.GermFactorsThrough.symm`, `TauCeti.equivalence_germFactorsThrough`:
  coincidence of branches is an equivalence relation on the immersed points.
* `TauCeti.germFactorsThrough_of_mem_closure`, `TauCeti.isClosed_setOf_germFactorsThrough`:
  coincidence of branches is a closed relation on the immersed points.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Lemmas 2.4.1 and 2.4.3 and Proposition 2.5.1.
-/

public section

open Set Filter Topology Function
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure

variable {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ∞ S]
  {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {J : SmoothAlmostComplexStructure I N} {u : S → N}

/-! ### The coordinate expression of a pseudoholomorphic curve -/

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- In the preferred charts at `x` and at `u x`, a pseudoholomorphic curve on a Riemann surface
solves the Cauchy–Riemann equation `∂ₜw = J_ψ(w) ∂ₛw` for the structure read in the target chart. -/
private theorem fderiv_writtenInExtChartAt_I (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hu : Continuous u) {x : S} {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℝ, ℂ) x).target)
    (hzu : u ((extChartAt 𝓘(ℝ, ℂ) x).symm z) ∈ (extChartAt I (u x)).source) :
    fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, ℂ) I x u) z Complex.I =
      J.inChart (u x) (writtenInExtChartAt 𝓘(ℝ, ℂ) I x u z)
        (fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, ℂ) I x u) z 1) := by
  -- The inverse chart is holomorphic, hence pseudoholomorphic, and so is its composite with `u`.
  -- The extended charts of `S` for the complex and the real model agree.
  have hφeq : extChartAt 𝓘(ℝ, ℂ) x = extChartAt 𝓘(ℂ) x := by
    rw [← modelWithCornersSelf_restrictScalars (𝕜 := ℝ) (𝕜' := ℂ),
      ModelWithCorners.extChartAt_restrictScalars]
  have hφ : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℝ, ℂ) x).symm z := by
    rw [hφeq] at hz ⊢
    exact (mdifferentiableWithinAt_extChartAt_symm hz).mdifferentiableAt (by simp)
  have hg : IsPseudoholomorphicAt (ofComplexManifold ℂ ℂ) J (u ∘ (extChartAt 𝓘(ℝ, ℂ) x).symm) z :=
    (hJu.isPseudoholomorphicAt _).comp (isPseudoholomorphicAt_ofComplexManifold_iff.2 hφ)
  have h := hg.mfderiv_apply_commute (1 : ℂ)
  rw [ofComplexManifold_apply, smul_eq_mul, mul_one] at h
  exact J.fderiv_extChartAt_comp_apply_eq_inChart (u x)
    (hu.continuousAt.comp (continuousAt_extChartAt_symm'' hz)) hzu h

omit [FiniteDimensional ℝ E] in
/-- The local data of a pseudoholomorphic curve near `x`: a connected open neighbourhood `B` of the
chart image of `x` on which the coordinate expression `ψ ∘ u ∘ φ⁻¹` is `C^n` and solves the
Cauchy–Riemann equation for a `C¹` field of complex structures. -/
private theorem exists_chartBall (n : WithTop ℕ∞) [IsManifold 𝓘(ℝ, ℂ) n S] [IsManifold I n N]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I n u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (x : S) :
    ∃ B : Set ℂ, IsOpen B ∧ IsPreconnected B ∧ extChartAt 𝓘(ℝ, ℂ) x x ∈ B ∧
      B ⊆ (extChartAt 𝓘(ℝ, ℂ) x).target ∧
      (∀ z ∈ B, u ((extChartAt 𝓘(ℝ, ℂ) x).symm z) ∈ (extChartAt I (u x)).source) ∧
      ContDiffOn ℝ n (writtenInExtChartAt 𝓘(ℝ, ℂ) I x u) B ∧
      (∀ z ∈ B, ContDiffAt ℝ 1 (J.inChart (u x)) (writtenInExtChartAt 𝓘(ℝ, ℂ) I x u z) ∧
        J.inChart (u x) (writtenInExtChartAt 𝓘(ℝ, ℂ) I x u z) ∘L
          J.inChart (u x) (writtenInExtChartAt 𝓘(ℝ, ℂ) I x u z) = -ContinuousLinearMap.id ℝ E) ∧
      ∀ z ∈ B, fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, ℂ) I x u) z Complex.I =
        J.inChart (u x) (writtenInExtChartAt 𝓘(ℝ, ℂ) I x u z)
          (fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, ℂ) I x u) z 1) := by
  obtain ⟨hΩ, hxΩ, hcd, hmaps⟩ := isOpen_mem_contDiffOn_mapsTo_writtenInExtChartAt hu x
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ _ hxΩ
  have hc : Continuous u := hu.continuous
  refine ⟨Metric.ball _ ε, Metric.isOpen_ball, (convex_ball _ _).isPreconnected,
    Metric.mem_ball_self hε, fun z hz ↦ (hball hz).1, fun z hz ↦ (hball hz).2,
    hcd.mono hball, fun z hz ↦ ⟨((J.contDiffOn_inChart (u x)).contDiffAt
      ((isOpen_extChartAt_target (u x)).mem_nhds (hmaps (hball hz)))).of_le (by simp),
      J.inChart_comp_inChart (u x) (hmaps (hball hz))⟩,
    fun z hz ↦ fderiv_writtenInExtChartAt_I hJu hc (hball hz).1 (hball hz).2⟩

omit [IsManifold 𝓘(ℂ) ∞ S] [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
/-- If the coordinate expression of `u` takes the value `ψ (u y)` near the chart image of a point
`x'` of the chart source, then `u` takes the value `u y` near `x'`. -/
private theorem eventually_eq_of_writtenInExtChartAt {x x' : S} {y : N}
    (hy : y ∈ (extChartAt I (u x)).source) {B : Set ℂ} (hB : IsOpen B)
    (hBs : ∀ z ∈ B, u ((extChartAt 𝓘(ℝ, ℂ) x).symm z) ∈ (extChartAt I (u x)).source)
    (hx' : x' ∈ (extChartAt 𝓘(ℝ, ℂ) x).source) (hx'B : extChartAt 𝓘(ℝ, ℂ) x x' ∈ B)
    (hw : ∀ z ∈ B, writtenInExtChartAt 𝓘(ℝ, ℂ) I x u z = extChartAt I (u x) y) :
    ∀ᶠ x'' in 𝓝 x', u x'' = y := by
  have hmem : (extChartAt 𝓘(ℝ, ℂ) x).source ∩ extChartAt 𝓘(ℝ, ℂ) x ⁻¹' B ∈ 𝓝 x' :=
    inter_mem ((isOpen_extChartAt_source x).mem_nhds hx')
      ((continuousAt_extChartAt' hx').preimage_mem_nhds (hB.mem_nhds hx'B))
  filter_upwards [hmem] with x'' ⟨hs, hb⟩
  have hl := (extChartAt 𝓘(ℝ, ℂ) x).left_inv hs
  have h := hw _ hb
  have hs' := hBs _ hb
  rw [hl] at hs'
  rw [writtenInExtChartAt_apply_extChartAt hs] at h
  exact (extChartAt I (u x)).injOn hs' hy h

/-! ### Unique continuation -/

/-- The set of points near which `u` is constant is closed, by local unique continuation. -/
private theorem isClosed_setOf_eventually_eq (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) :
    IsClosed {x | ∀ᶠ x' in 𝓝 x, u x' = u x} := by
  refine isClosed_iff_clusterPt.2 fun x hx ↦ ?_
  obtain ⟨B, hBo, hBc, hxB, hBt, hBs, hcd, hJ, hCR⟩ := exists_chartBall 1 hu hJu x
  set φ := extChartAt 𝓘(ℝ, ℂ) x
  set ψ := extChartAt I (u x)
  -- A point `y` near `x` near which `u` is constant.
  have hV : φ.source ∩ φ ⁻¹' B ∈ 𝓝 x :=
    inter_mem ((isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x))
      ((continuousAt_extChartAt x).preimage_mem_nhds (hBo.mem_nhds hxB))
  obtain ⟨y, ⟨hys, hyB⟩, hyL⟩ := (clusterPt_principal_iff.1 hx) _ hV
  have hyφ : φ.symm (φ y) = y := φ.left_inv hys
  have huy : u y ∈ ψ.source := by simpa [hyφ] using hBs _ hyB
  -- The coordinate expression is constant near `φ y`, hence on `B`.
  have hw₀ : ∀ᶠ z in 𝓝 (φ y), writtenInExtChartAt 𝓘(ℝ, ℂ) I x u z = ψ (u y) := by
    have ht : Tendsto φ.symm (𝓝 (φ y)) (𝓝 y) := by
      have h := (continuousAt_extChartAt_symm'' (hBt hyB)).tendsto
      rwa [hyφ] at h
    filter_upwards [ht.eventually hyL] with z hz
    exact congrArg (extChartAt I (u x)) hz
  have hJy := hJ _ hyB
  have hval : writtenInExtChartAt 𝓘(ℝ, ℂ) I x u (φ y) = ψ (u y) := hw₀.self_of_nhds
  rw [hval] at hJy
  have hconst := eqOn_const_of_cauchyRiemann_of_eventually_eq hJy.1.exists_lipschitzOnWith hJy.2
    hBo hBc hcd hCR hyB hw₀
  have hux := eventually_eq_of_writtenInExtChartAt huy hBo hBs (mem_extChartAt_source x) hxB
    hconst
  have hxy : u x = u y := hux.self_of_nhds
  rw [mem_ofPred_eq, hxy]
  exact hux

/-- **Unique continuation for pseudoholomorphic curves.** On a connected Riemann surface, a `C¹`
pseudoholomorphic map into an almost complex manifold that is constant near one point is
constant. -/
theorem eq_of_isPseudoholomorphic_of_eventually_eq [PreconnectedSpace S]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    {x₀ : S} (h₀ : ∀ᶠ x in 𝓝 x₀, u x = u x₀) (x : S) : u x = u x₀ := by
  have hL : IsOpen {x | ∀ᶠ x' in 𝓝 x, u x' = u x} := isOpen_iff_mem_nhds.2 fun x hx ↦ by
    filter_upwards [hx.eventually_nhds] with x' hx'
    exact hx'.mono fun _ h ↦ h.trans hx'.self_of_nhds.symm
  have huniv := IsClopen.eq_univ ⟨isClosed_setOf_eventually_eq hu hJu, hL⟩ ⟨x₀, h₀⟩
  have hlc : IsLocallyConstant u := (IsLocallyConstant.iff_eventually_eq u).2 fun x ↦ by
    have hx : x ∈ {x | ∀ᶠ x' in 𝓝 x, u x' = u x} := huniv ▸ mem_univ x
    exact hx
  exact hlc.apply_eq_of_preconnectedSpace x x₀

/-- A nonconstant `C¹` pseudoholomorphic map on a connected Riemann surface has, in the charts at
any point, a coordinate expression that is not constant on the chart ball. -/
private theorem exists_ne_of_isPseudoholomorphic [PreconnectedSpace S]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) {x : S} {B : Set ℂ} (hB : IsOpen B)
    (hxB : extChartAt 𝓘(ℝ, ℂ) x x ∈ B)
    (hBs : ∀ z ∈ B, u ((extChartAt 𝓘(ℝ, ℂ) x).symm z) ∈ (extChartAt I (u x)).source) :
    ∃ z ∈ B, writtenInExtChartAt 𝓘(ℝ, ℂ) I x u z ≠ extChartAt I (u x) (u x) := by
  by_contra! h
  have hux := eventually_eq_of_writtenInExtChartAt (mem_extChartAt_source (u x)) hB hBs
    (mem_extChartAt_source x) hxB h
  obtain ⟨x₁, x₂, h₁₂⟩ := hne
  exact h₁₂ ((eq_of_isPseudoholomorphic_of_eventually_eq hu hJu hux x₁).trans
    (eq_of_isPseudoholomorphic_of_eventually_eq hu hJu hux x₂).symm)

/-! ### Discreteness of fibres and critical points -/

omit [IsManifold 𝓘(ℂ) ∞ S] in
/-- A property of the chart images of points, holding on a punctured neighbourhood of the chart
image of `x`, holds on a punctured neighbourhood of `x`, inside the chart source. -/
private theorem eventually_nhdsNE_of_extChartAt {x : S} {p : ℂ → Prop}
    (h : ∀ᶠ z in 𝓝[≠] extChartAt 𝓘(ℝ, ℂ) x x, p z) :
    ∀ᶠ x' in 𝓝[≠] x, x' ∈ (extChartAt 𝓘(ℝ, ℂ) x).source ∧ p (extChartAt 𝓘(ℝ, ℂ) x x') := by
  filter_upwards [nhdsWithin_le_nhds (extChartAt_source_mem_nhds (I := 𝓘(ℝ, ℂ)) x),
    (𝓘(ℝ, ℂ).tendsto_extChartAt_nhdsNE x).eventually h] with x' hx' hp
  exact ⟨hx', hp⟩

/-- **The fibres of a pseudoholomorphic curve are discrete.** On a connected Riemann surface, a
nonconstant `C¹` pseudoholomorphic map into an almost complex manifold takes each value on a
discrete subset. -/
theorem setOf_ne_mem_codiscrete_of_isPseudoholomorphic [PreconnectedSpace S]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) (y : N) : {x | u x ≠ y} ∈ codiscrete S := by
  refine mem_codiscrete_iff_forall_mem_nhdsNE.2 fun x ↦ ?_
  by_cases hxy : u x = y
  · subst hxy
    obtain ⟨B, hBo, hBc, hxB, -, hBs, hcd, hJ, hCR⟩ := exists_chartBall 1 hu hJu x
    have hJx := hJ _ hxB
    rw [writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x)] at hJx
    have hdisc := setOf_ne_mem_codiscreteWithin_of_cauchyRiemann hJx.1.exists_lipschitzOnWith
      hJx.2 hBo hBc hcd hCR (exists_ne_of_isPseudoholomorphic hu hJu hne hBo hxB hBs)
    filter_upwards [eventually_nhdsNE_of_extChartAt
      (hBo.inter_mem_nhdsNE_of_mem_codiscreteWithin hdisc hxB)] with x' ⟨hs, _, hx'⟩ hux'
    apply hx'
    rw [writtenInExtChartAt_apply_extChartAt hs]
    exact congrArg (extChartAt I (u x)) hux'
  · have := I.t1Space N
    exact nhdsWithin_le_nhds (hu.continuous.continuousAt.eventually_ne hxy)

/-- **The critical points of a pseudoholomorphic curve are isolated.** On a connected Riemann
surface, the critical points of a nonconstant `C¹` pseudoholomorphic map into an almost complex
manifold, the points where its manifold derivative vanishes, form a discrete subset. -/
theorem setOf_mfderiv_ne_zero_mem_codiscrete_of_isPseudoholomorphic [PreconnectedSpace S]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) : {x | mfderiv 𝓘(ℝ, ℂ) I u x ≠ 0} ∈ codiscrete S := by
  refine mem_codiscrete_iff_forall_mem_nhdsNE.2 fun x ↦ ?_
  obtain ⟨B, hBo, hBc, hxB, -, hBs, hcd, hJ, hCR⟩ := exists_chartBall 1 hu hJu x
  obtain ⟨z, hz, hzne⟩ := exists_ne_of_isPseudoholomorphic hu hJu hne hBo hxB hBs
  have hdisc := setOf_fderiv_ne_zero_mem_codiscreteWithin_of_cauchyRiemann_comp hBo hBc
    (fun z hz ↦ (hJ z hz).1) (fun z hz ↦ (hJ z hz).2) hcd hCR
    ⟨z, hz, _, hxB, by rwa [writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x)]⟩
  filter_upwards [eventually_nhdsNE_of_extChartAt
    (hBo.inter_mem_nhdsNE_of_mem_codiscreteWithin hdisc hxB)] with x' ⟨hs, hx'B, hx'⟩
  -- The critical points of `u` are those of its coordinate expression.
  have h := (hu.continuous.continuousAt.fderivWithin_extChartAt_comp_extChartAt_symm_eq_zero_iff
    hs ((extChartAt 𝓘(ℝ, ℂ) x).left_inv hs ▸ hBs _ hx'B)).not
  rw [ModelWithCorners.range_eq_univ, fderivWithin_univ] at h
  exact h.1 hx'

/-! ### Coincident branches -/

section Coincidence

open RiemannSurface

variable {S' : Type*} [TopologicalSpace S'] [ChartedSpace ℂ S'] [IsManifold 𝓘(ℂ) ∞ S']
  {u₀ : S → N} {u₁ : S' → N} {a₀ : S} {b₀ : S'}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] in
/-- A holomorphic factorization of coordinate expressions is a holomorphic factorization of germs.
Let `B₀` and `B₁` be open sets of chart images of points near `a₀` and `b₀` that `u₀` and `u₁`
map into the source of the chart of `N` at `y`. If `φ'` is holomorphic at the chart image of `b₀`,
sends it to the chart image of `a₀`, and factors the coordinate expression of `u₁` through that of
`u₀` near it, then the germ of `u₁` at `b₀` factors holomorphically through the germ of `u₀` at
`a₀`, by `φ₀⁻¹ ∘ φ' ∘ φ₁` for the charts `φ₀` at `a₀` and `φ₁` at `b₀`. -/
private theorem germFactorsThrough_of_eventuallyEq_comp {y : N} {B₀ B₁ : Set ℂ}
    (hB₀o : IsOpen B₀) (ha₀B : extChartAt 𝓘(ℝ, ℂ) a₀ a₀ ∈ B₀)
    (hB₀t : B₀ ⊆ (extChartAt 𝓘(ℝ, ℂ) a₀).target)
    (hB₀s : ∀ z ∈ B₀, u₀ ((extChartAt 𝓘(ℝ, ℂ) a₀).symm z) ∈ (extChartAt I y).source)
    (hB₁o : IsOpen B₁) (hb₀B : extChartAt 𝓘(ℝ, ℂ) b₀ b₀ ∈ B₁)
    (hB₁s : ∀ z ∈ B₁, u₁ ((extChartAt 𝓘(ℝ, ℂ) b₀).symm z) ∈ (extChartAt I y).source)
    {φ' : ℂ → ℂ} (hφ'a : AnalyticAt ℂ φ' (extChartAt 𝓘(ℝ, ℂ) b₀ b₀))
    (hφ'b : φ' (extChartAt 𝓘(ℝ, ℂ) b₀ b₀) = extChartAt 𝓘(ℝ, ℂ) a₀ a₀)
    (hφ'u : extChartAt I y ∘ u₁ ∘ (extChartAt 𝓘(ℝ, ℂ) b₀).symm =ᶠ[𝓝 (extChartAt 𝓘(ℝ, ℂ) b₀ b₀)]
      (extChartAt I y ∘ u₀ ∘ (extChartAt 𝓘(ℝ, ℂ) a₀).symm) ∘ φ') :
    GermFactorsThrough u₁ b₀ u₀ a₀ := by
  have hφ'B : ∀ᶠ b in 𝓝 b₀, φ' (extChartAt 𝓘(ℝ, ℂ) b₀ b) ∈ B₀ :=
    (continuousAt_extChartAt b₀).eventually
      (hφ'a.continuousAt.eventually (hφ'b ▸ hB₀o.mem_nhds ha₀B))
  refine germFactorsThrough_iff.2 ⟨(extChartAt 𝓘(ℝ, ℂ) a₀).symm ∘ φ' ∘ extChartAt 𝓘(ℝ, ℂ) b₀,
    by rw [Function.comp_apply, Function.comp_apply, hφ'b, extChartAt_to_inv (I := 𝓘(ℝ, ℂ))], ?_,
    ?_⟩
  · -- The two charts are holomorphic, and so is `φ'` near the chart image of `b₀`.
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ, ℂ)) b₀,
      (continuousAt_extChartAt b₀).eventually hφ'a.eventually_analyticAt, hφ'B]
      with b hbs hbφ' hbB
    have ht := hB₀t hbB
    -- The extended charts of a Riemann surface for the complex and the real model agree.
    simp only [← modelWithCornersSelf_restrictScalars (𝕜 := ℝ) (𝕜' := ℂ),
      ModelWithCorners.extChartAt_restrictScalars] at hbs ht ⊢
    refine ((mdifferentiableWithinAt_extChartAt_symm ht).mdifferentiableAt (by simp)).comp b ?_
    exact hbφ'.differentiableAt.mdifferentiableAt.comp b
      (mdifferentiableAt_extChartAt (by rwa [extChartAt_source] at hbs))
  · -- The chart of `N` at `y` is injective on its source, where both curves take their values.
    filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ, ℂ)) b₀,
      (continuousAt_extChartAt b₀).preimage_mem_nhds (hB₁o.mem_nhds hb₀B),
      (continuousAt_extChartAt b₀).eventually hφ'u, hφ'B] with b hbs hbB hbu hb₀
    have h₁ := hB₁s _ hbB
    rw [(extChartAt 𝓘(ℝ, ℂ) b₀).left_inv hbs] at h₁
    refine (extChartAt I y).injOn h₁ (hB₀s _ hb₀) ?_
    simpa only [Function.comp_apply, (extChartAt 𝓘(ℝ, ℂ) b₀).left_inv hbs] using hbu

/-- The core of `TauCeti.germFactorsThrough_of_frequently_mem_image`, given that the two curves
take the same value at `a₀` and at `b₀`. -/
private theorem germFactorsThrough_of_frequently_mem_image_of_eq (hu₀ : ContMDiff 𝓘(ℝ, ℂ) I 2 u₀)
    (hJu₀ : IsPseudoholomorphic (ofComplexManifold ℂ S) J u₀) (hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁)
    (hJu₁ : IsPseudoholomorphic (ofComplexManifold ℂ S') J u₁)
    (hdu₀ : mfderiv 𝓘(ℝ, ℂ) I u₀ a₀ ≠ 0) (hub : u₁ b₀ = u₀ a₀)
    (hacc : ∀ s ∈ 𝓝 a₀, ∃ᶠ b in 𝓝[≠] b₀, u₁ b ∈ u₀ '' s) : GermFactorsThrough u₁ b₀ u₀ a₀ := by
  -- Read both curves in the preferred charts at `a₀`, at `b₀` and at their common image point.
  obtain ⟨B₀, hB₀o, -, ha₀B, hB₀t, hB₀s, hcd₀, -, hCR₀⟩ := exists_chartBall 2 hu₀ hJu₀ a₀
  obtain ⟨B₁, hB₁o, -, hb₀B, -, hB₁s, hcd₁, -, hCR₁⟩ := exists_chartBall 1 hu₁ hJu₁ b₀
  simp only [writtenInExtChartAt, hub] at hB₁s hcd₁ hCR₁
  simp only [writtenInExtChartAt] at hcd₀ hCR₀
  have hmaps₀ : MapsTo (extChartAt I (u₀ a₀) ∘ u₀ ∘ (extChartAt 𝓘(ℝ, ℂ) a₀).symm) B₀
      (extChartAt I (u₀ a₀)).target := fun z hz ↦ (extChartAt I (u₀ a₀)).map_source (hB₀s z hz)
  have hmaps₁ : MapsTo (extChartAt I (u₀ a₀) ∘ u₁ ∘ (extChartAt 𝓘(ℝ, ℂ) b₀).symm) B₁
      (extChartAt I (u₀ a₀)).target := fun z hz ↦ (extChartAt I (u₀ a₀)).map_source (hB₁s z hz)
  -- The Cauchy–Riemann equation `∂ₜw = K(w) ∂ₛw` in the form `∂ₛw + K(w) ∂ₜw = 0`, for the
  -- structure `K` read in the chart at `u₀ a₀`.
  have hCR : ∀ {w : ℂ → E} {z : ℂ}, w z ∈ (extChartAt I (u₀ a₀)).target →
      fderiv ℝ w z Complex.I = J.inChart (u₀ a₀) (w z) (fderiv ℝ w z 1) →
      fderiv ℝ w z 1 + J.inChart (u₀ a₀) (w z) (fderiv ℝ w z Complex.I) = 0 := fun hz h ↦ by
    rw [h, J.inChart_inChart (u₀ a₀) hz, add_neg_cancel]
  have hdw₀ : fderiv ℝ (extChartAt I (u₀ a₀) ∘ u₀ ∘ (extChartAt 𝓘(ℝ, ℂ) a₀).symm)
      (extChartAt 𝓘(ℝ, ℂ) a₀ a₀) ≠ 0 := by
    have h := (hu₀.continuous.continuousAt.fderivWithin_extChartAt_comp_extChartAt_symm_eq_zero_iff
      (mem_extChartAt_source (I := 𝓘(ℝ, ℂ)) a₀) (mem_extChartAt_source (I := I) (u₀ a₀))).not
    rw [ModelWithCorners.range_eq_univ, fderivWithin_univ] at h
    exact h.2 hdu₀
  -- The coincidences, read in the charts.
  have hacc' : ∀ T ∈ 𝓝 (extChartAt 𝓘(ℝ, ℂ) a₀ a₀), ∃ᶠ ζ in 𝓝[≠] (extChartAt 𝓘(ℝ, ℂ) b₀ b₀),
      (extChartAt I (u₀ a₀) ∘ u₁ ∘ (extChartAt 𝓘(ℝ, ℂ) b₀).symm) ζ ∈
        (extChartAt I (u₀ a₀) ∘ u₀ ∘ (extChartAt 𝓘(ℝ, ℂ) a₀).symm) '' T := fun T hT ↦ by
    have hs : (extChartAt 𝓘(ℝ, ℂ) a₀).source ∩ extChartAt 𝓘(ℝ, ℂ) a₀ ⁻¹' T ∈ 𝓝 a₀ :=
      inter_mem (extChartAt_source_mem_nhds a₀) ((continuousAt_extChartAt a₀).preimage_mem_nhds hT)
    have hb : ∀ᶠ b in 𝓝[≠] b₀, b ∈ (extChartAt 𝓘(ℝ, ℂ) b₀).source :=
      nhdsWithin_le_nhds (extChartAt_source_mem_nhds b₀)
    refine (𝓘(ℝ, ℂ).tendsto_extChartAt_nhdsNE b₀).frequently
      (((hacc _ hs).and_eventually hb).mono fun b ⟨⟨a, ⟨has, haT⟩, hab⟩, hbs⟩ ↦ ?_)
    refine ⟨extChartAt 𝓘(ℝ, ℂ) a₀ a, haT, ?_⟩
    simp only [Function.comp_apply, (extChartAt 𝓘(ℝ, ℂ) a₀).left_inv has,
      (extChartAt 𝓘(ℝ, ℂ) b₀).left_inv hbs, hab]
  -- The local theorem factors the coordinate expressions.
  obtain ⟨φ', hφ'a, hφ'b, hφ'u⟩ := exists_analyticAt_eventuallyEq_comp_of_frequently_mem_image
    hB₀o (isOpen_extChartAt_target (u₀ a₀)) ha₀B hcd₀ ((J.contDiffOn_inChart (u₀ a₀)).of_le
      (by simp)) hmaps₀ (fun z hz v ↦ J.inChart_inChart (u₀ a₀) (hmaps₀ hz) v)
    (fun z hz ↦ hCR (hmaps₀ hz) (hCR₀ z hz)) hdw₀ hB₁o hb₀B hcd₁
    (fun z hz ↦ hCR (hmaps₁ hz) (hCR₁ z hz)) hacc'
  exact germFactorsThrough_of_eventuallyEq_comp hB₀o ha₀B hB₀t hB₀s hB₁o hb₀B hB₁s hφ'a hφ'b hφ'u

/-- **Accumulating coincidences factor a pseudoholomorphic curve** (McDuff–Salamon, Lemma 2.4.3).
Let `u₀ : S → N` and `u₁ : S' → N` be pseudoholomorphic maps from Riemann surfaces into a
Hausdorff almost complex manifold, `u₀` of class `C²` and immersed at `a₀`, and `u₁` of class `C¹`.
If for every neighbourhood `s` of `a₀` the points `b ≠ b₀` with `u₁ b ∈ u₀ '' s` accumulate at
`b₀`, then the germ of `u₁` at `b₀` factors holomorphically through the germ of `u₀` at `a₀`:
`u₁ = u₀ ∘ φ` near `b₀` for a map `φ` holomorphic near `b₀` with `φ b₀ = a₀`. The curve `u₁` may
be critical at `b₀`. -/
theorem germFactorsThrough_of_frequently_mem_image [T2Space N] (hu₀ : ContMDiff 𝓘(ℝ, ℂ) I 2 u₀)
    (hJu₀ : IsPseudoholomorphic (ofComplexManifold ℂ S) J u₀) (hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁)
    (hJu₁ : IsPseudoholomorphic (ofComplexManifold ℂ S') J u₁)
    (hdu₀ : mfderiv 𝓘(ℝ, ℂ) I u₀ a₀ ≠ 0)
    (hacc : ∀ s ∈ 𝓝 a₀, ∃ᶠ b in 𝓝[≠] b₀, u₁ b ∈ u₀ '' s) : GermFactorsThrough u₁ b₀ u₀ a₀ :=
  germFactorsThrough_of_frequently_mem_image_of_eq hu₀ hJu₀ hu₁ hJu₁ hdu₀
    (eq_of_frequently_mem_image hu₀.continuous.continuousAt hu₁.continuous.continuousAt
      fun s hs ↦ (hacc s hs).filter_mono nhdsWithin_le_nhds) hacc

/-- **Accumulating coincidences factor a pseudoholomorphic curve**, for sequences
(McDuff–Salamon, Lemma 2.4.3). Under the hypotheses on `u₀` and `u₁` of
`TauCeti.germFactorsThrough_of_frequently_mem_image`, if `u₀ (z k) = u₁ (ζ k)` with `z k → a₀`,
`ζ k → b₀` and `ζ k ≠ b₀`, then the germ of `u₁` at `b₀` factors holomorphically through the germ
of `u₀` at `a₀`. -/
theorem germFactorsThrough_of_tendsto [T2Space N] (hu₀ : ContMDiff 𝓘(ℝ, ℂ) I 2 u₀)
    (hJu₀ : IsPseudoholomorphic (ofComplexManifold ℂ S) J u₀) (hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁)
    (hJu₁ : IsPseudoholomorphic (ofComplexManifold ℂ S') J u₁)
    (hdu₀ : mfderiv 𝓘(ℝ, ℂ) I u₀ a₀ ≠ 0) {z : ℕ → S} {ζ : ℕ → S'}
    (hz : Tendsto z atTop (𝓝 a₀)) (hζ : Tendsto ζ atTop (𝓝 b₀)) (hζb₀ : ∀ k, ζ k ≠ b₀)
    (hzζ : ∀ k, u₀ (z k) = u₁ (ζ k)) : GermFactorsThrough u₁ b₀ u₀ a₀ := by
  refine germFactorsThrough_of_frequently_mem_image hu₀ hJu₀ hu₁ hJu₁ hdu₀ fun s hs ↦ ?_
  have hζ' : Tendsto ζ atTop (𝓝[≠] b₀) := tendsto_nhdsWithin_iff.2 ⟨hζ, .of_forall hζb₀⟩
  exact hζ'.frequently ((hz.eventually hs).frequently.mono fun k hk ↦ ⟨z k, hk, hzζ k⟩)

/-- **Coincident branches are characterized by accumulating coincidences.** For pseudoholomorphic
maps `u₀ : S → N` and `u₁ : S' → N` into a Hausdorff almost complex manifold, `u₀` of class `C²`
and immersed at `a₀` and `u₁` of class `C¹`, the germ of `u₁` at `b₀` factors holomorphically
through the germ of `u₀` at `a₀` exactly when, for every neighbourhood `s` of `a₀`, the points
`b ≠ b₀` with `u₁ b ∈ u₀ '' s` accumulate at `b₀`. -/
theorem germFactorsThrough_iff_frequently_mem_image [T2Space N]
    (hu₀ : ContMDiff 𝓘(ℝ, ℂ) I 2 u₀) (hJu₀ : IsPseudoholomorphic (ofComplexManifold ℂ S) J u₀)
    (hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁) (hJu₁ : IsPseudoholomorphic (ofComplexManifold ℂ S') J u₁)
    (hdu₀ : mfderiv 𝓘(ℝ, ℂ) I u₀ a₀ ≠ 0) :
    GermFactorsThrough u₁ b₀ u₀ a₀ ↔ ∀ s ∈ 𝓝 a₀, ∃ᶠ b in 𝓝[≠] b₀, u₁ b ∈ u₀ '' s :=
  ⟨fun h _ hs ↦ h.frequently_mem_image hs,
    germFactorsThrough_of_frequently_mem_image hu₀ hJu₀ hu₁ hJu₁ hdu₀⟩

/-- **Coincidence of immersed branches is symmetric.** Let `u₀ : S → N` and `u₁ : S' → N` be
pseudoholomorphic maps into an almost complex manifold, `u₀` of class `C¹` and `u₁` of
class `C²` and immersed at `b₀`. If the germ of `u₁` at `b₀` factors holomorphically through the
germ of `u₀` at `a₀`, then the germ of `u₀` at `a₀` factors holomorphically through the germ of
`u₁` at `b₀`. -/
theorem RiemannSurface.GermFactorsThrough.symm (hu₀ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₀)
    (hJu₀ : IsPseudoholomorphic (ofComplexManifold ℂ S) J u₀) (hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 2 u₁)
    (hJu₁ : IsPseudoholomorphic (ofComplexManifold ℂ S') J u₁)
    (h : GermFactorsThrough u₁ b₀ u₀ a₀) (hdu₁ : mfderiv 𝓘(ℝ, ℂ) I u₁ b₀ ≠ 0) :
    GermFactorsThrough u₀ a₀ u₁ b₀ := by
  obtain ⟨φ, hφb, hφd, hφu⟩ := germFactorsThrough_iff.1 h
  refine germFactorsThrough_of_frequently_mem_image_of_eq hu₁ hJu₁ hu₀ hJu₀ hdu₁ h.apply_eq.symm
    fun s hs ↦ ?_
  -- Otherwise the factor `φ` would take the value `a₀` near `b₀`, and `u₁` would be constant there.
  by_contra hfr
  rw [not_frequently, eventually_nhdsWithin_iff] at hfr
  have ht : Tendsto φ (𝓝 b₀) (𝓝 a₀) := hφb ▸ hφd.self_of_nhds.continuousAt.tendsto
  have hc : u₁ =ᶠ[𝓝 b₀] fun _ ↦ u₁ b₀ := by
    filter_upwards [hφu, hs, ht.eventually hfr] with b hb hbs hφ
    have hφa : φ b = a₀ := by
      by_contra hne
      exact hφ hne ⟨b, hbs, hb⟩
    simp only [hb, hφu.self_of_nhds, Function.comp_apply, hφa, hφb]
  exact hdu₁ (by rw [hc.mfderiv_eq, mfderiv_const, ContinuousLinearMap.comp_zero])

/-- **The coincident-branch relation is closed at immersed points.** Let `u₀ : S → N` and
`u₁ : S' → N` be pseudoholomorphic maps into a Hausdorff almost complex manifold, `u₀` of class
`C²` and `u₁` of class `C¹`. If `(a₀, b₀)` is a limit of pairs `(a, b)` such that the germ of `u₁`
at `b` factors holomorphically through the germ of `u₀` at `a`, and `u₀` is immersed at `a₀`, then
the germ of `u₁` at `b₀` factors holomorphically through the germ of `u₀` at `a₀`. -/
theorem germFactorsThrough_of_mem_closure [T2Space N] (hu₀ : ContMDiff 𝓘(ℝ, ℂ) I 2 u₀)
    (hJu₀ : IsPseudoholomorphic (ofComplexManifold ℂ S) J u₀) (hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁)
    (hJu₁ : IsPseudoholomorphic (ofComplexManifold ℂ S') J u₁)
    (h : (a₀, b₀) ∈ closure {p : S × S' | GermFactorsThrough u₁ p.2 u₀ p.1})
    (hdu₀ : mfderiv 𝓘(ℝ, ℂ) I u₀ a₀ ≠ 0) : GermFactorsThrough u₁ b₀ u₀ a₀ := by
  have := ChartedSpace.t1Space ℂ S'
  have : PerfectSpace S' := ChartedSpace.perfectSpace (H := ℂ)
  refine germFactorsThrough_of_frequently_mem_image hu₀ hJu₀ hu₁ hJu₁ hdu₀ fun s hs ↦ ?_
  refine frequently_iff.2 fun {U} hU ↦ ?_
  obtain ⟨W, hW, hWU⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hU
  -- A nearby related pair `p`: the points near `p.2` are mapped by `u₁` into `u₀ '' s`.
  obtain ⟨p, ⟨hps, hpW⟩, hp⟩ := mem_closure_iff_nhds.1 h _
    (prod_mem_nhds (interior_mem_nhds.2 hs) (interior_mem_nhds.2 hW))
  have hev := (hp : GermFactorsThrough u₁ p.2 u₀ p.1).eventually_mem_image
    (isOpen_interior.mem_nhds hps)
  have hne : ∀ᶠ y in 𝓝[≠] p.2, y ≠ b₀ := by
    rcases eq_or_ne p.2 b₀ with hpb | hpb
    · exact hpb ▸ self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds hpb)
  have : (𝓝[≠] p.2).NeBot := perfectSpace_iff_forall_not_isolated.1 ‹_› p.2
  have hWev : ∀ᶠ y in 𝓝 p.2, y ∈ interior W := isOpen_interior.mem_nhds hpW
  obtain ⟨y, hyb, hyW, hys⟩ := (hne.and (nhdsWithin_le_nhds (hWev.and hev))).exists
  exact ⟨y, hWU ⟨interior_subset hyW, hyb⟩, image_mono interior_subset hys⟩

/-- **The coincident-branch relation is closed on immersed points.** For pseudoholomorphic maps
`u₀ : S → N` of class `C²` and `u₁ : S' → N` of class `C¹` into a Hausdorff almost complex
manifold, a set `s` of points at which `u₀` is immersed and any set `t`, the pairs `(a, b)` of
`s × t` such that the germ of `u₁` at `b` factors holomorphically through the germ of `u₀` at `a`
form a closed subset of `s × t`. -/
theorem isClosed_setOf_germFactorsThrough [T2Space N] (hu₀ : ContMDiff 𝓘(ℝ, ℂ) I 2 u₀)
    (hJu₀ : IsPseudoholomorphic (ofComplexManifold ℂ S) J u₀) (hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u₁)
    (hJu₁ : IsPseudoholomorphic (ofComplexManifold ℂ S') J u₁) {s : Set S}
    (hs : ∀ a ∈ s, mfderiv 𝓘(ℝ, ℂ) I u₀ a ≠ 0) (t : Set S') :
    IsClosed {p : s × t | GermFactorsThrough u₁ (p.2 : S') u₀ (p.1 : S)} :=
  isClosed_of_closure_subset fun p hp ↦ germFactorsThrough_of_mem_closure hu₀ hJu₀ hu₁ hJu₁
    (map_mem_closure (f := Prod.map Subtype.val Subtype.val)
      (continuous_subtypeVal.prodMap continuous_subtypeVal) hp fun _ hq ↦ hq) (hs _ p.1.prop)

/-- **Coincidence of branches is an equivalence relation on the immersed points.** For a
pseudoholomorphic map `u` of class `C²` from a Riemann surface into an almost complex manifold,
the relation on the points where `u` is immersed, under which `z` and `ζ` are related
when the branches of `u` at `z` and at `ζ` differ by a holomorphic change of source coordinate,
is an equivalence relation. -/
theorem equivalence_germFactorsThrough (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) :
    Equivalence fun z ζ : {x // mfderiv 𝓘(ℝ, ℂ) I u x ≠ 0} ↦ GermFactorsThrough u (ζ : S) u z :=
  ⟨fun z ↦ .refl u z, fun {_ ζ} h ↦ h.symm (hu.of_le one_le_two) hJu hu hJu ζ.prop,
    fun h₁ h₂ ↦ h₂.trans h₁⟩

end Coincidence

/-! ### Compact Riemann surfaces -/

/-- **Finite fibres.** On a compact connected Riemann surface, a nonconstant `C¹`
pseudoholomorphic map into an almost complex manifold takes each value finitely often. -/
theorem finite_preimage_singleton_of_isPseudoholomorphic [CompactSpace S] [PreconnectedSpace S]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) (y : N) : (u ⁻¹' {y}).Finite := by
  have h := isCompact_univ.finite_sdiff_of_mem_codiscreteWithin
    (setOf_ne_mem_codiscrete_of_isPseudoholomorphic hu hJu hne y)
  convert h using 1
  ext x
  simp

/-- **Finitely many critical points.** On a compact connected Riemann surface, a nonconstant `C¹`
pseudoholomorphic map into an almost complex manifold has finitely many critical points. -/
theorem finite_setOf_mfderiv_eq_zero_of_isPseudoholomorphic [CompactSpace S] [PreconnectedSpace S]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) : {x | mfderiv 𝓘(ℝ, ℂ) I u x = 0}.Finite := by
  have h := isCompact_univ.finite_sdiff_of_mem_codiscreteWithin
    (setOf_mfderiv_ne_zero_mem_codiscrete_of_isPseudoholomorphic hu hJu hne)
  convert h using 1
  ext x
  simp

/-- **The preimage of the critical values is finite.** On a compact connected Riemann surface, a
nonconstant `C¹` pseudoholomorphic map `u` into an almost complex manifold has finitely many
points in `u⁻¹(u(Crit u))`, the preimage of the images of its critical points. -/
theorem finite_preimage_image_setOf_mfderiv_eq_zero_of_isPseudoholomorphic [CompactSpace S]
    [PreconnectedSpace S] (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) :
    (u ⁻¹' (u '' {x | mfderiv 𝓘(ℝ, ℂ) I u x = 0})).Finite :=
  ((finite_setOf_mfderiv_eq_zero_of_isPseudoholomorphic hu hJu hne).image u).preimage' fun y _ ↦
    finite_preimage_singleton_of_isPseudoholomorphic hu hJu hne y

end TauCeti

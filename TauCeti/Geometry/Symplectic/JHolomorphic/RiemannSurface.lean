/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import Mathlib.Topology.DiscreteSubset
import TauCeti.Geometry.Symplectic.JHolomorphic.CriticalPoint
import TauCeti.Geometry.Symplectic.JHolomorphic.UniqueContinuation
import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Chart
import TauCeti.Topology.Codiscrete

/-!
# Critical points and fibres of pseudoholomorphic curves on Riemann surfaces

Let `S` be a Riemann surface, a complex manifold modelled on `ℂ`, with its almost complex structure
`SmoothAlmostComplexStructure.ofComplexManifold ℂ S`, let `N` be a finite-dimensional manifold
without boundary carrying a smooth almost complex structure `J`, and let `u : S → N` be a
pseudoholomorphic map. Nothing is assumed about `J` beyond smoothness: no taming form, no
integrability and no genericity. This file globalizes the local theory of
`TauCeti.Geometry.Symplectic.JHolomorphic.UniqueContinuation` and
`TauCeti.Geometry.Symplectic.JHolomorphic.CriticalPoint` (McDuff–Salamon, Lemma 2.4.1) from
domains in `ℂ` and targets in a normed space to such maps:

* **unique continuation**: on a connected `S`, a `C¹` pseudoholomorphic map that is constant near
  one point is constant (`TauCeti.eq_of_isPseudoholomorphic_of_eventually_eq`);
* **isolated fibres**: if such a map is not constant, each of its fibres is a discrete subset of
  `S` (`TauCeti.setOf_ne_mem_codiscrete_of_isPseudoholomorphic`);
* **isolated critical points**: if it is moreover `C²`, its critical points, where its manifold
  derivative vanishes, form a discrete subset of `S`
  (`TauCeti.setOf_mfderiv_ne_zero_mem_codiscrete_of_isPseudoholomorphic`).

On a compact connected Riemann surface a nonconstant `C²` pseudoholomorphic map therefore has
finitely many critical points (`TauCeti.finite_setOf_mfderiv_eq_zero_of_isPseudoholomorphic`) and
finite fibres (`TauCeti.finite_preimage_singleton_of_isPseudoholomorphic`), so the preimage
`u⁻¹(u(Crit u))` of its critical values is finite
(`TauCeti.finite_preimage_image_setOf_mfderiv_eq_zero_of_isPseudoholomorphic`). This finite
exceptional set is where the factorization of a nonconstant closed curve through a simple curve
starts (McDuff–Salamon, Proposition 2.5.1).

The proofs read `u` in the preferred chart `φ` of `S` at a point `x` and the preferred extended
chart `ψ` of `N` at `u x`. Since the charts of `S` are holomorphic, the coordinate expression
`ψ ∘ u ∘ φ⁻¹` solves the Cauchy–Riemann equation `∂ₜw = J_ψ(w) ∂ₛw` for the structure
`J_ψ = J.inChart (u x)` read in `ψ`, which is smooth and squares to `-1` on the chart target; the
local theorems apply to it on a ball about `φ x`. The set of points near which `u` is constant is
open, and it is closed by local unique continuation, which gives the global statement. The critical
points of `u` correspond to those of its coordinate expression because the tangent coordinate
changes of the charts are invertible.

## Main results

* `TauCeti.eq_of_isPseudoholomorphic_of_eventually_eq`: unique continuation on a connected
  Riemann surface.
* `TauCeti.setOf_ne_mem_codiscrete_of_isPseudoholomorphic`: the fibres of a nonconstant
  pseudoholomorphic map are discrete.
* `TauCeti.setOf_mfderiv_ne_zero_mem_codiscrete_of_isPseudoholomorphic`: the critical points of a
  nonconstant `C²` pseudoholomorphic map are isolated.
* `TauCeti.finite_preimage_singleton_of_isPseudoholomorphic`,
  `TauCeti.finite_setOf_mfderiv_eq_zero_of_isPseudoholomorphic`,
  `TauCeti.finite_preimage_image_setOf_mfderiv_eq_zero_of_isPseudoholomorphic`: on a compact
  connected Riemann surface the fibres of a nonconstant `C¹` pseudoholomorphic map are finite, and
  so are the critical set and the preimage of the critical values of a nonconstant `C²` one.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Lemma 2.4.1 and Proposition 2.5.1.
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
surface, the critical points of a nonconstant `C²` pseudoholomorphic map into an almost complex
manifold, the points where its manifold derivative vanishes, form a discrete subset. -/
theorem setOf_mfderiv_ne_zero_mem_codiscrete_of_isPseudoholomorphic [PreconnectedSpace S]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) : {x | mfderiv 𝓘(ℝ, ℂ) I u x ≠ 0} ∈ codiscrete S := by
  refine mem_codiscrete_iff_forall_mem_nhdsNE.2 fun x ↦ ?_
  have hu₁ : ContMDiff 𝓘(ℝ, ℂ) I 1 u := hu.of_le one_le_two
  obtain ⟨B, hBo, hBc, hxB, -, hBs, hcd, hJ, hCR⟩ := exists_chartBall 2 hu hJu x
  obtain ⟨z, hz, hzne⟩ := exists_ne_of_isPseudoholomorphic hu₁ hJu hne hBo hxB hBs
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

/-- **Finitely many critical points.** On a compact connected Riemann surface, a nonconstant `C²`
pseudoholomorphic map into an almost complex manifold has finitely many critical points. -/
theorem finite_setOf_mfderiv_eq_zero_of_isPseudoholomorphic [CompactSpace S] [PreconnectedSpace S]
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u) (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u)
    (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) : {x | mfderiv 𝓘(ℝ, ℂ) I u x = 0}.Finite := by
  have h := isCompact_univ.finite_sdiff_of_mem_codiscreteWithin
    (setOf_mfderiv_ne_zero_mem_codiscrete_of_isPseudoholomorphic hu hJu hne)
  convert h using 1
  ext x
  simp

/-- **The preimage of the critical values is finite.** On a compact connected Riemann surface, a
nonconstant `C²` pseudoholomorphic map `u` into an almost complex manifold has finitely many
points in `u⁻¹(u(Crit u))`, the preimage of the images of its critical points. -/
theorem finite_preimage_image_setOf_mfderiv_eq_zero_of_isPseudoholomorphic [CompactSpace S]
    [PreconnectedSpace S] (hu : ContMDiff 𝓘(ℝ, ℂ) I 2 u)
    (hJu : IsPseudoholomorphic (ofComplexManifold ℂ S) J u) (hne : ∃ x₁ x₂, u x₁ ≠ u x₂) :
    (u ⁻¹' (u '' {x | mfderiv 𝓘(ℝ, ℂ) I u x = 0})).Finite :=
  ((finite_setOf_mfderiv_eq_zero_of_isPseudoholomorphic hu hJu hne).image u).preimage' fun y _ ↦
    finite_preimage_singleton_of_isPseudoholomorphic (hu.of_le one_le_two) hJu hne y

end TauCeti

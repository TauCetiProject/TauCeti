/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.TopBranchedCover
public import TauCeti.Analysis.Complex.RiemannSurface.BelyiPair

/-!
# The filled cover as an analytic Belyi pair

Let `p : E → ℂ ∖ {0, 1}` be a covering map with finite fibres. Its filled cover
`TauCeti.FilledCover p` is a compact Riemann surface for the charts
`TauCeti.FilledCover.chartedSpace`: the charts of `ℂ` pulled back along `p` on `E`, and at the
added point of each component of `p ⁻¹' D_q*` the inverse of the filled disc of its filling chart.
This file proves that the extension `TauCeti.FilledCover.fillMap p : FilledCover p → OnePoint ℂ`
of `p` is holomorphic for these charts and the two charts of the Riemann sphere. Read in the chart
at a point of `E`, it is the inclusion `ℂ → OnePoint ℂ`; read in the chart at the added point of a
component of local degree `e` over the puncture `q`, it is `w ↦ w ^ e` followed by the inverse
`q.sphereCoordInv` of the standard coordinate at `q`, which is holomorphic even at `w = 0`
(`TauCeti.ThricePuncturedSphere.Puncture.contMDiff_sphereCoordInv`).

Consequently the filled cover of a connected degree-`n` cover `C` of `ℂ ∖ {0, 1}`, with its
extended projection, is an analytic Belyi pair of degree `n`
(`TauCeti.ConnectedCover.toAnalyticBelyiPair`): `fillMap` is a covering map off `{0, 1, ∞}`
(`TauCeti.FilledCover.isCoveringMapOn_fillMap`) and is onto the sphere. This is the construction of
an analytic Belyi pair from a finite cover of the thrice-punctured sphere, hence from a connected
permutation triple, on which analytic Riemann existence for three-point covers rests. Its
underlying topological branched cover is the filled cover
`TauCeti.ConnectedCover.toTopBranchedCover`
(`TauCeti.ConnectedCover.toTopBranchedCoverIsoClass_toAnalyticBelyiPair`).

## Main results

* `TauCeti.FilledCover.contMDiff_fillMap`, `TauCeti.FilledCover.mdifferentiable_fillMap`: the
  extended projection of the filled cover is holomorphic.
* `TauCeti.ConnectedCover.toAnalyticBelyiPair`: the filled cover of a connected finite cover of
  `ℂ ∖ {0, 1}`, as an analytic Belyi pair.
* `TauCeti.ConnectedCover.degree_toAnalyticBelyiPair`: its degree is the degree of the cover.
* `TauCeti.ConnectedCover.toTopBranchedCoverIsoClass_toAnalyticBelyiPair`: its underlying
  topological branched cover is the filled branched cover of the cover.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer 1981,
  §8, Theorem 8.4 (an unbranched proper holomorphic covering of `X ∖ A` extends across `A`).
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2.7 (Lemma 1.80: the extended map is holomorphic in the added charts).
-/

public noncomputable section

namespace TauCeti

open Function Set Topology ThricePuncturedSphere PunctureFilling

open scoped ContDiff Manifold OnePoint

namespace FilledCover

variable {E : Type*} [TopologicalSpace E] {p : E → ThricePuncturedSphere}

variable (hp : IsCoveringMap p) {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀}))
include hp hfin

/-- **The extended projection of the filled cover is holomorphic**, indeed analytic, for the
charts `TauCeti.FilledCover.chartedSpace` of the filled cover and the charts of the Riemann
sphere. -/
theorem contMDiff_fillMap :
    letI := chartedSpace hp hfin
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fillMap p) := by
  let := chartedSpace hp hfin
  have : IsManifold 𝓘(ℂ) ω (FilledCover p) := isManifold hp hfin
  intro y
  -- On the source of the chart at `y`, `fillMap p` is an analytic map of the chart coordinate.
  suffices ∃ g : ℂ → OnePoint ℂ, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g (chartAt ℂ y y) ∧
      ∀ y' ∈ (chartAt ℂ y).source, fillMap p y' = g (chartAt ℂ y y') by
    obtain ⟨g, hg, hfg⟩ := this
    exact (hg.comp y (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas y)
      (mem_chart_source ℂ y))).congr_of_eventuallyEq
        (Filter.eventually_of_mem (chart_source_mem_nhds ℂ y) hfg)
  induction y using PunctureFilling.induction with
  | incl x =>
    -- In the chart at a point of `E`, the extended projection is the inclusion `ℂ → OnePoint ℂ`.
    refine ⟨(↑), OnePoint.contMDiff_coe _, fun y' hy' => ?_⟩
    rw [chartAt_incl_source] at hy'
    obtain ⟨x', -, rfl⟩ := hy'
    rw [fillMap_incl, chartAt_incl_apply_incl, toOnePoint_apply]
  | center i =>
    -- In the chart at an added point, it is the power map followed by the inverse coordinate.
    refine ⟨fun w => (FilledPoint.sigmaEquiv p i).1.sphereCoordInv (w ^ degree p i),
      ((FilledPoint.sigmaEquiv p i).1.contMDiff_sphereCoordInv.comp
        (contDiff_id.pow _).contMDiff) _, fun y' hy' => ?_⟩
    rw [chartAt_center_source] at hy'
    obtain ⟨w, rfl⟩ := hy'
    rw [fillMap_disc hp hfin, chartAt_center_apply_disc]

/-- **The extended projection of the filled cover is holomorphic**, as a map from the filled cover
with its charts `TauCeti.FilledCover.chartedSpace` to the Riemann sphere. -/
theorem mdifferentiable_fillMap :
    letI := chartedSpace hp hfin
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fillMap p) := by
  let := chartedSpace hp hfin
  exact (contMDiff_fillMap hp hfin).mdifferentiable (by simp)

end FilledCover

namespace ConnectedCover

open FilledCover

variable {n : ℕ} (C : ConnectedCover (X := TopCat.of ThricePuncturedSphere) basePt n)

/-- **The filled cover as an analytic Belyi pair.** The filled cover of a connected degree-`n`
cover `C` of `ℂ ∖ {0, 1}`, with its charts `TauCeti.FilledCover.chartedSpace` and the extension
`TauCeti.FilledCover.fillMap` of the projection of `C`, is an analytic Belyi pair, of degree `n`
(`TauCeti.ConnectedCover.degree_toAnalyticBelyiPair`). -/
-- The body is exposed so that the surface of the pair is the filled cover by definition.
@[expose]
def toAnalyticBelyiPair : AnalyticBelyiPair.{0} :=
  letI := chartedSpace C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton
  haveI := isManifold (n := ω) C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton
  haveI := compactSpace C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton
  haveI := t2Space C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton
  haveI : ConnectedSpace (FilledCover ⇑C.cover.proj) := PunctureFilling.connectedSpace
  AnalyticBelyiPair.ofIsCoveringMapOn (FilledCover ⇑C.cover.proj)
    (mdifferentiable_fillMap C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton)
    (by
      obtain ⟨x, hx⟩ := surjective_fillMap C.cover.isCoveringMap_proj.surjective ∞
      obtain ⟨x', hx'⟩ := surjective_fillMap C.cover.isCoveringMap_proj.surjective
        ((0 : ℂ) : OnePoint ℂ)
      exact ⟨x, x', by rw [hx, hx']; exact OnePoint.infty_ne_coe 0⟩)
    (by
      convert isCoveringMapOn_fillMap C.cover.isCoveringMap_proj
        C.finite_proj_preimage_singleton using 1
      ext y
      simp only [mem_compl_iff, mem_marked, mem_insert_iff, mem_singleton_iff])

/-- The Belyi map of the filled cover is the extension of the projection of `C`. -/
@[simp]
theorem coe_β_toAnalyticBelyiPair : ⇑C.toAnalyticBelyiPair.β = fillMap ⇑C.cover.proj := by
  let := chartedSpace C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton
  have := isManifold (n := ω) C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton
  have := compactSpace C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton
  have := t2Space C.cover.isCoveringMap_proj C.finite_proj_preimage_singleton
  have : ConnectedSpace (FilledCover ⇑C.cover.proj) := PunctureFilling.connectedSpace
  exact AnalyticBelyiPair.coe_β_ofIsCoveringMapOn _ _ _ _

/-- The analytic Belyi pair of a connected degree-`n` cover has degree `n`. -/
-- A pre-simp lemma, so that it fires before `coe_β_toAnalyticBelyiPair` rewrites the coercion
-- of the Belyi map, after which the degree is no longer stated about the pair's surface.
@[simp↓]
theorem degree_toAnalyticBelyiPair : RiemannSurface.degree C.toAnalyticBelyiPair.β = n := by
  have hy : toOnePoint basePt ∉ marked := by
    rw [← mem_compl_iff, ← range_toOnePoint]
    exact mem_range_self _
  refine (C.toAnalyticBelyiPair.ncard_preimage_singleton (y := toOnePoint basePt)
    (by simpa only [mem_marked, mem_insert_iff, mem_singleton_iff] using hy)).symm.trans ?_
  rw [← Nat.card_coe_set_eq, coe_β_toAnalyticBelyiPair,
    ← funext C.toTopBranchedCover_π_apply]
  exact C.toTopBranchedCover.natCard_preimage_singleton _ hy

/-- **The topological branched cover underlying the filled analytic Belyi pair** of a connected
degree-`n` cover `C` of `ℂ ∖ {0, 1}` is the filled branched cover
`TauCeti.ConnectedCover.toTopBranchedCover` of `C`. -/
theorem toTopBranchedCoverIsoClass_toAnalyticBelyiPair :
    AnalyticBelyiPair.toTopBranchedCoverIsoClass n
        ⟦⟨C.toAnalyticBelyiPair, C.degree_toAnalyticBelyiPair⟩⟧ =
      .mk C.toTopBranchedCover := by
  rw [AnalyticBelyiPair.toTopBranchedCoverIsoClass_mk]
  -- Both branched covers have total space the filled cover.
  exact TopBranchedCover.IsoClass.mk_eq_mk_iff.2
    ⟨⟨Homeomorph.refl (FilledCover ⇑C.cover.proj), fun z =>
      (C.toTopBranchedCover_π_apply z).trans <| (congrFun C.coe_β_toAnalyticBelyiPair z).symm.trans
        (AnalyticBelyiPair.toTopBranchedCover_π_apply _ _ z).symm⟩⟩

end ConnectedCover

end TauCeti

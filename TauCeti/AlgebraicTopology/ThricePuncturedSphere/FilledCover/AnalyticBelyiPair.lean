/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.Classification
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

Since a homeomorphism over the sphere between analytic Belyi pairs is holomorphic
(`TauCeti.AnalyticBelyiPair.Iso.ofHomeomorph`), the filled pair is well defined on isomorphism
classes of covers (`TauCeti.ConnectedCoverClass.toAnalyticBelyiPair`). With the uniqueness of the
compactification (`TauCeti.TopBranchedCover.IsoClass.restrict_bijective`) it follows that every
topological branched cover of the sphere with branch values in `{0, 1, ∞}` carries a complex
structure making it an analytic Belyi pair, unique up to isomorphism
(`TauCeti.AnalyticBelyiPair.toTopBranchedCoverIsoClass_bijective`). Equivalently, analytic Belyi
pairs of degree `n` up to isomorphism correspond to connected degree-`n` covers of `ℂ ∖ {0, 1}` up
to isomorphism, by restriction and filling
(`TauCeti.AnalyticBelyiPair.isoClassEquivConnectedCoverClass`). Composing with the classification
of covers by their triples, analytic Belyi pairs of degree `n` up to isomorphism correspond to
connected permutation triples of degree `n` up to isomorphism, a pair going to its monodromy triple
(`TauCeti.AnalyticBelyiPair.isoClassEquivConnectedIsoClass`); so two pairs are isomorphic exactly
when their monodromy triples are
(`TauCeti.AnalyticBelyiPair.nonempty_iso_iff_isoClass_monodromyTriple_eq`).

The ramification of a Belyi map is read off its monodromy triple: over `0`, `1` and `∞` the
local multiplicities of `β` at the points of the fibre are the cycle lengths of `σ0`, `σ1` and
`σinf`, fixed points included (`TauCeti.AnalyticBelyiPair.map_localMultiplicity_fiber_zero`). This
is the topological statement for the underlying branched cover, whose local degrees are the local
multiplicities. In particular `β` is unramified over `0`, `1` or `∞` exactly when `σ0`, `σ1` or
`σinf` is the identity (`TauCeti.AnalyticBelyiPair.monodromyTriple_σ1_eq_one_iff`).

## Main results

* `TauCeti.FilledCover.contMDiff_fillMap`, `TauCeti.FilledCover.mdifferentiable_fillMap`: the
  extended projection of the filled cover is holomorphic.
* `TauCeti.ConnectedCover.toAnalyticBelyiPair`: the filled cover of a connected finite cover of
  `ℂ ∖ {0, 1}`, as an analytic Belyi pair.
* `TauCeti.ConnectedCover.degree_toAnalyticBelyiPair`: its degree is the degree of the cover.
* `TauCeti.ConnectedCover.toTopBranchedCoverIsoClass_toAnalyticBelyiPair`: its underlying
  topological branched cover is the filled branched cover of the cover.
* `TauCeti.ConnectedCoverClass.toAnalyticBelyiPair`: the filled analytic Belyi pair of an
  isomorphism class of connected covers.
* `TauCeti.AnalyticBelyiPair.toTopBranchedCoverIsoClass_bijective`: analytic Belyi pairs and
  topological branched covers of degree `n` have the same isomorphism classes.
* `TauCeti.AnalyticBelyiPair.isoClassEquivConnectedCoverClass`: isomorphism classes of analytic
  Belyi pairs of degree `n` are isomorphism classes of connected degree-`n` covers of
  `ℂ ∖ {0, 1}`.
* `TauCeti.AnalyticBelyiPair.isoClassEquivConnectedIsoClass`: isomorphism classes of analytic
  Belyi pairs of degree `n` are isomorphism classes of connected permutation triples of degree `n`.
* `TauCeti.AnalyticBelyiPair.nonempty_iso_iff_isoClass_monodromyTriple_eq`: two analytic Belyi
  pairs are isomorphic exactly when their monodromy triples are.
* `TauCeti.AnalyticBelyiPair.map_localMultiplicity_fiber_zero`,
  `TauCeti.AnalyticBelyiPair.map_localMultiplicity_fiber_one`,
  `TauCeti.AnalyticBelyiPair.map_localMultiplicity_fiber_inf`: the local multiplicities of the
  Belyi map over `0`, `1` and `∞` are the full cycle types of `σ0`, `σ1` and `σinf`.
* `TauCeti.AnalyticBelyiPair.monodromyTriple_σ0_eq_one_iff`,
  `TauCeti.AnalyticBelyiPair.monodromyTriple_σ1_eq_one_iff`,
  `TauCeti.AnalyticBelyiPair.monodromyTriple_σinf_eq_one_iff`: the Belyi map is unramified over
  `0`, `1` or `∞` exactly when `σ0`, `σ1` or `σinf` is the identity.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer 1981,
  §8, Theorems 8.4 and 8.5 (an unbranched proper holomorphic covering of `X ∖ A` extends across
  `A`, uniquely up to biholomorphism over `X`).
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2.7 (Lemma 1.80: the extended map is holomorphic in the added charts, and Proposition 1.81:
  its uniqueness).
-/

public noncomputable section

namespace TauCeti

open Equiv.Perm Function Set Topology ThricePuncturedSphere PunctureFilling

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

/-! ### Isomorphism classes -/

/-- **The filled analytic Belyi pair of an isomorphism class of covers.** Filling the punctures of a
connected degree-`n` cover of `ℂ ∖ {0, 1}` is well defined on isomorphism classes: an isomorphism of
covers extends to a homeomorphism of filled covers over the sphere
(`TauCeti.ConnectedCover.toTopBranchedCoverIso`), which is holomorphic. -/
def ConnectedCoverClass.toAnalyticBelyiPair {n : ℕ} :
    ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n →
      Quotient (AnalyticBelyiPair.isoSetoid.{0} n) :=
  lift (fun C ↦ ⟦⟨C.toAnalyticBelyiPair, C.degree_toAnalyticBelyiPair⟩⟧) fun _ _ ⟨f⟩ ↦
    Quotient.sound <| AnalyticBelyiPair.isoSetoid_r.2
      ⟨.ofHomeomorph (ConnectedCover.toTopBranchedCoverIso f).toHomeomorph fun x ↦ by
        rw [ConnectedCover.coe_β_toAnalyticBelyiPair, ConnectedCover.coe_β_toAnalyticBelyiPair]
        exact (ConnectedCover.toTopBranchedCoverIso f).π_apply x⟩

/-- The filled analytic Belyi pair of the class of `C` is the class of the filled pair of `C`. -/
@[simp]
theorem ConnectedCoverClass.toAnalyticBelyiPair_mk {n : ℕ}
    (C : ConnectedCover (X := TopCat.of ThricePuncturedSphere) basePt n) :
    (mk C).toAnalyticBelyiPair = ⟦⟨C.toAnalyticBelyiPair, C.degree_toAnalyticBelyiPair⟩⟧ :=
  lift_mk _ _ C

/-- The topological branched cover underlying the filled analytic Belyi pair of a class of covers
is the filled branched cover of that class. -/
@[simp]
theorem ConnectedCoverClass.toTopBranchedCoverIsoClass_toAnalyticBelyiPair {n : ℕ}
    (c : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    AnalyticBelyiPair.toTopBranchedCoverIsoClass n c.toAnalyticBelyiPair =
      c.toTopBranchedCover := by
  obtain ⟨C, rfl⟩ := mk_surjective c
  rw [toAnalyticBelyiPair_mk, toTopBranchedCover_mk,
    ConnectedCover.toTopBranchedCoverIsoClass_toAnalyticBelyiPair]

namespace AnalyticBelyiPair

/-- **Every topological branched cover of the sphere with branch values in `{0, 1, ∞}` comes from an
analytic Belyi pair**: up to isomorphism, it is the underlying branched cover of the filled pair of
its unbranched part. -/
theorem toTopBranchedCoverIsoClass_surjective (n : ℕ) :
    Surjective (toTopBranchedCoverIsoClass.{0} n) := fun t ↦
  ⟨t.restrict.toAnalyticBelyiPair, by
    rw [ConnectedCoverClass.toTopBranchedCoverIsoClass_toAnalyticBelyiPair]
    exact TopBranchedCover.IsoClass.restrict_injective (by simp)⟩

/-- **Analytic Belyi pairs are topological branched covers.** Forgetting the complex structure is a
bijection from isomorphism classes of analytic Belyi pairs of degree `n` to isomorphism classes of
topological branched covers of the sphere of degree `n` with branch values in `{0, 1, ∞}`: every
such branched cover carries a complex structure making it an analytic Belyi pair, unique up to
isomorphism. -/
theorem toTopBranchedCoverIsoClass_bijective (n : ℕ) :
    Bijective (toTopBranchedCoverIsoClass.{0} n) :=
  ⟨toTopBranchedCoverIsoClass_injective n, toTopBranchedCoverIsoClass_surjective n⟩

/-- **Analytic Belyi pairs are classified by finite covers of the thrice-punctured sphere.**
Restricting the Belyi map over `ℂ ∖ {0, 1}` and filling the punctures are inverse bijections between
isomorphism classes of analytic Belyi pairs of degree `n` and isomorphism classes of connected
degree-`n` covers of `ℂ ∖ {0, 1}`. -/
def isoClassEquivConnectedCoverClass (n : ℕ) :
    Quotient (isoSetoid.{0} n) ≃
      ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n where
  toFun P := (toTopBranchedCoverIsoClass n P).restrict
  invFun c := c.toAnalyticBelyiPair
  left_inv P := toTopBranchedCoverIsoClass_injective n <| by
    rw [ConnectedCoverClass.toTopBranchedCoverIsoClass_toAnalyticBelyiPair]
    exact TopBranchedCover.IsoClass.restrict_injective (by simp)
  right_inv c := by simp

/-- The equivalence `TauCeti.AnalyticBelyiPair.isoClassEquivConnectedCoverClass` restricts the
underlying topological branched cover over `ℂ ∖ {0, 1}`. -/
@[simp]
theorem isoClassEquivConnectedCoverClass_apply {n : ℕ} (P : Quotient (isoSetoid.{0} n)) :
    isoClassEquivConnectedCoverClass n P = (toTopBranchedCoverIsoClass n P).restrict :=
  (rfl)

/-- The inverse of `TauCeti.AnalyticBelyiPair.isoClassEquivConnectedCoverClass` is the filled
analytic Belyi pair. -/
@[simp]
theorem isoClassEquivConnectedCoverClass_symm_apply {n : ℕ}
    (c : ConnectedCoverClass (X := TopCat.of ThricePuncturedSphere) basePt n) :
    (isoClassEquivConnectedCoverClass n).symm c = c.toAnalyticBelyiPair :=
  (rfl)

open RiemannSurface

/-! ### Classification by permutation triples -/

/-- **Analytic Belyi pairs are classified by their permutation triples.** Isomorphism classes of
analytic Belyi pairs of degree `n` correspond to isomorphism classes of connected permutation
triples of degree `n`: the class of a pair goes to the class of the monodromy triple of the cover of
`ℂ ∖ {0, 1}` attached to it (`TauCeti.AnalyticBelyiPair.isoClassEquivConnectedIsoClass_mk`). -/
noncomputable def isoClassEquivConnectedIsoClass (n : ℕ) :
    Quotient (isoSetoid.{0} n) ≃ ConnectedIsoClass n :=
  (isoClassEquivConnectedCoverClass n).trans ConnectedCoverClass.isoClassEquiv

/-- The classification `TauCeti.AnalyticBelyiPair.isoClassEquivConnectedIsoClass` is the
classification of the class of covers of `ℂ ∖ {0, 1}` attached to a class of pairs by
`TauCeti.AnalyticBelyiPair.isoClassEquivConnectedCoverClass`. -/
theorem isoClassEquivConnectedIsoClass_apply {n : ℕ} (P : Quotient (isoSetoid.{0} n)) :
    isoClassEquivConnectedIsoClass n P = (isoClassEquivConnectedCoverClass n P).isoClass := by
  rw [isoClassEquivConnectedIsoClass, Equiv.trans_apply, ConnectedCoverClass.isoClassEquiv_apply]

/-- The classification `TauCeti.AnalyticBelyiPair.isoClassEquivConnectedIsoClass` sends the class of
a pair to the class of its monodromy triple, for any numbering of its fibre over `1/2`. -/
theorem isoClassEquivConnectedIsoClass_mk {n : ℕ}
    (P : {P : AnalyticBelyiPair.{0} // degree P.β = n}) (ν : P.1.restrict ⁻¹' {basePt} ≃ Fin n) :
    isoClassEquivConnectedIsoClass n ⟦P⟧ =
      .mk ⟨P.1.isCoveringMap_restrict.monodromyTriple ν,
        P.1.isCoveringMap_restrict.isConnected_monodromyTriple ν⟩ := by
  set X := P.1.toTopBranchedCover P.2
  obtain ⟨ν'⟩ := X.connectedCover.nonempty_equiv_fin
  obtain ⟨ν''⟩ := X.nonempty_restrict_preimage_singleton_equiv basePt
  rw [isoClassEquivConnectedIsoClass_apply, isoClassEquivConnectedCoverClass_apply,
    toTopBranchedCoverIsoClass_mk, TopBranchedCover.IsoClass.restrict_mk,
    ConnectedCoverClass.isoClass_mk _ ν']
  refine ConnectedIsoClass.forget_injective ?_
  rw [ConnectedIsoClass.forget_mk, ConnectedIsoClass.forget_mk,
    ConnectedFiberNumberedCover.coe_connectedTriple]
  -- The packaged cover of `X` is the restriction of `X`, which is the cover attached to `P`.
  exact (X.connectedCover.cover.isCoveringMap_proj.isoClass_monodromyTriple_eq_of_homeomorph ν'
      X.isCoveringMap_restrict ν'' X.connectedCoverHomeomorph
      (funext X.restrict_connectedCoverHomeomorph)).symm.trans
    (P.1.isoClass_monodromyTriple_toTopBranchedCover P.2 ν ν'')

/-- Forgetting connectedness, the classification
`TauCeti.AnalyticBelyiPair.isoClassEquivConnectedIsoClass` is the permutation triple
`TauCeti.AnalyticBelyiPair.toIsoClass` of a class of pairs. -/
@[simp]
theorem forget_isoClassEquivConnectedIsoClass {n : ℕ} (P : Quotient (isoSetoid.{0} n)) :
    (isoClassEquivConnectedIsoClass n P).forget = toIsoClass n P := by
  induction P using Quotient.inductionOn with
  | h P =>
    obtain ⟨ν⟩ := P.1.nonempty_restrict_preimage_singleton_equiv basePt
    rw [isoClassEquivConnectedIsoClass_mk P (ν.trans (finCongr P.2)), ConnectedIsoClass.forget_mk,
      toIsoClass_mk P (ν.trans (finCongr P.2))]

/-- **An analytic Belyi pair is determined up to isomorphism by its permutation triple.** -/
theorem toIsoClass_injective (n : ℕ) : Injective (toIsoClass.{0} n) := fun P Q h ↦
  (isoClassEquivConnectedIsoClass n).injective <| ConnectedIsoClass.forget_injective <| by
    rw [forget_isoClassEquivConnectedIsoClass, forget_isoClassEquivConnectedIsoClass, h]

/-- **Two analytic Belyi pairs are isomorphic exactly when their monodromy triples are**, for any
numberings of their fibres over `1/2` by the same `Fin n`. -/
theorem nonempty_iso_iff_isoClass_monodromyTriple_eq {P Q : AnalyticBelyiPair.{0}} {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) (ν' : Q.restrict ⁻¹' {basePt} ≃ Fin n) :
    Nonempty (P.Iso Q) ↔
      PermutationTriple.IsoClass.mk (P.isCoveringMap_restrict.monodromyTriple ν) =
        PermutationTriple.IsoClass.mk (Q.isCoveringMap_restrict.monodromyTriple ν') := by
  refine ⟨fun ⟨e⟩ ↦ (e.isoClass_monodromyTriple_eq ν ν').symm, fun h ↦ ?_⟩
  have hP := P.degree_β_eq_of_restrict_preimage_singleton_equiv ν
  have hQ := Q.degree_β_eq_of_restrict_preimage_singleton_equiv ν'
  refine isoSetoid_r.1 (Quotient.exact (s := isoSetoid n) (a := ⟨P, hP⟩) (b := ⟨Q, hQ⟩) ?_)
  exact toIsoClass_injective n (by rw [toIsoClass_mk _ ν, toIsoClass_mk _ ν', h])

/-! ### Ramification over `0`, `1` and `∞` -/

/-- A numbering of the fibre over `1/2` of the cover attached to `P` determines the degree of `P`,
and the monodromy triple it gives has the cycle data of the unbranched part of the underlying
topological branched cover. -/
private theorem exists_cycleData_monodromyTriple_eq (P : AnalyticBelyiPair.{0}) {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    ∃ (hn : degree P.β = n) (ν' : (P.toTopBranchedCover hn).restrict ⁻¹' {basePt} ≃ Fin n),
      ((P.toTopBranchedCover hn).isCoveringMap_restrict.monodromyTriple ν').cycleData =
        (P.isCoveringMap_restrict.monodromyTriple ν).cycleData := by
  have hn : degree P.β = n := P.degree_β_eq_of_restrict_preimage_singleton_equiv ν
  obtain ⟨ν'⟩ := (P.toTopBranchedCover hn).nonempty_restrict_preimage_singleton_equiv basePt
  exact ⟨hn, ν', PermutationTriple.cycleData_eq_of_equivalent <|
    PermutationTriple.IsoClass.mk_eq_mk_iff.1 <|
      P.isoClass_monodromyTriple_toTopBranchedCover hn ν ν'⟩

/-- **The ramification of a Belyi map over `0`.** The local multiplicities of the Belyi map of
an analytic Belyi pair at the points over `0` are the cycle lengths of `σ0` in the monodromy
triple of the pair, fixed points included. -/
theorem map_localMultiplicity_fiber_zero (P : AnalyticBelyiPair.{0}) {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    (P.β.finite_fiber ((0 : ℂ) : OnePoint ℂ)).toFinset.val.map (localMultiplicity P.β) =
      fullCycleType (P.isCoveringMap_restrict.monodromyTriple ν).σ0 := by
  obtain ⟨hn, ν', h⟩ := P.exists_cycleData_monodromyTriple_eq ν
  rw [← P.parts_ramificationPartition_toTopBranchedCover hn,
    TopBranchedCover.parts_ramificationPartition_zero _ ν', fullCycleType_def, fullCycleType_def,
    ← PermutationTriple.cycleData_σ0, ← PermutationTriple.cycleData_σ0, h]

/-- **The ramification of a Belyi map over `1`.** The local multiplicities of the Belyi map of
an analytic Belyi pair at the points over `1` are the cycle lengths of `σ1` in the monodromy
triple of the pair, fixed points included. -/
theorem map_localMultiplicity_fiber_one (P : AnalyticBelyiPair.{0}) {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    (P.β.finite_fiber ((1 : ℂ) : OnePoint ℂ)).toFinset.val.map (localMultiplicity P.β) =
      fullCycleType (P.isCoveringMap_restrict.monodromyTriple ν).σ1 := by
  obtain ⟨hn, ν', h⟩ := P.exists_cycleData_monodromyTriple_eq ν
  rw [← P.parts_ramificationPartition_toTopBranchedCover hn,
    TopBranchedCover.parts_ramificationPartition_one _ ν', fullCycleType_def, fullCycleType_def,
    ← PermutationTriple.cycleData_σ1, ← PermutationTriple.cycleData_σ1, h]

/-- **The ramification of a Belyi map over `∞`.** The local multiplicities of the Belyi map of
an analytic Belyi pair at the points over `∞` are the cycle lengths of `σinf` in the monodromy
triple of the pair, fixed points included. -/
theorem map_localMultiplicity_fiber_inf (P : AnalyticBelyiPair.{0}) {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    (P.β.finite_fiber (∞ : OnePoint ℂ)).toFinset.val.map (localMultiplicity P.β) =
      fullCycleType (P.isCoveringMap_restrict.monodromyTriple ν).σinf := by
  obtain ⟨hn, ν', h⟩ := P.exists_cycleData_monodromyTriple_eq ν
  rw [← P.parts_ramificationPartition_toTopBranchedCover hn,
    TopBranchedCover.parts_ramificationPartition_inf _ ν', fullCycleType_def, fullCycleType_def,
    ← PermutationTriple.cycleData_σinf, ← PermutationTriple.cycleData_σinf, h]

/-- **A Belyi map is unramified over `0` exactly when `σ0` is the identity**, in the monodromy
triple of the pair for any numbering of its fibre over `1/2`. -/
theorem monodromyTriple_σ0_eq_one_iff {P : AnalyticBelyiPair.{0}} {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    (P.isCoveringMap_restrict.monodromyTriple ν).σ0 = 1 ↔
      ((0 : ℂ) : OnePoint ℂ) ∉ P.β.branchValues := by
  rw [← forall_mem_fullCycleType_eq_one_iff, ← P.map_localMultiplicity_fiber_zero ν,
    Multiset.forall_mem_map_iff, P.β.notMem_branchValues_iff]
  simp

/-- **A Belyi map is unramified over `1` exactly when `σ1` is the identity**, in the monodromy
triple of the pair for any numbering of its fibre over `1/2`. -/
theorem monodromyTriple_σ1_eq_one_iff {P : AnalyticBelyiPair.{0}} {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    (P.isCoveringMap_restrict.monodromyTriple ν).σ1 = 1 ↔
      ((1 : ℂ) : OnePoint ℂ) ∉ P.β.branchValues := by
  rw [← forall_mem_fullCycleType_eq_one_iff, ← P.map_localMultiplicity_fiber_one ν,
    Multiset.forall_mem_map_iff, P.β.notMem_branchValues_iff]
  simp

/-- **A Belyi map is unramified over `∞` exactly when `σinf` is the identity**, in the monodromy
triple of the pair for any numbering of its fibre over `1/2`. -/
theorem monodromyTriple_σinf_eq_one_iff {P : AnalyticBelyiPair.{0}} {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    (P.isCoveringMap_restrict.monodromyTriple ν).σinf = 1 ↔
      (∞ : OnePoint ℂ) ∉ P.β.branchValues := by
  rw [← forall_mem_fullCycleType_eq_one_iff, ← P.map_localMultiplicity_fiber_inf ν,
    Multiset.forall_mem_map_iff, P.β.notMem_branchValues_iff]
  simp

end AnalyticBelyiPair

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Basic
public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Geometry.Manifold.Instances.PunctureFilling

/-!
# Charts on the filled cover

Let `p : E → ℂ ∖ {0, 1}` be a covering map with finite fibres. Pulling the standard complex
charts back along `p` makes `E` locally homeomorphic to `ℂ`. The filling chart of every component
over a puncture is an open embedding of a punctured disc, so these charts extend across the added
centres and make `TauCeti.FilledCover p` locally homeomorphic to `ℂ` as well.

The preferred chart at a point of `E` reads a nearby point through `p`. The preferred chart at an
added point is the inverse of its filled disc and sends that point to `0`. These two computations
are the topological charts used to extend the covering map across the punctures.

## Main declarations

* `TauCeti.FilledCover.chartedSpace`: the charted-space structure on a filled finite cover.
* `TauCeti.FilledCover.chartAt_incl_apply_incl`: the chart on the original cover reads points
  through the covering map.
* `TauCeti.FilledCover.chartAt_center_apply_disc`: the chart at an added point is inverse to its
  filled disc.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2.7.
* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer 1981,
  §8, Theorem 8.4.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set Topology ThricePuncturedSphere

open scoped Manifold

namespace FilledCover

/-- The charted-space structure on the filled cover of a finite cover of the thrice-punctured
sphere. On the original cover it uses the charts pulled back along the covering map; at an added
point it uses the corresponding filled disc as a complex coordinate neighbourhood. -/
@[instance_reducible]
def chartedSpace {E : Type*} [TopologicalSpace E] {p : E → ThricePuncturedSphere}
    (hp : IsCoveringMap p) {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀})) :
    ChartedSpace ℂ (FilledCover p) := by
  let : ChartedSpace ℂ ThricePuncturedSphere :=
    ThricePuncturedSphere.isOpenEmbedding_coe.singletonChartedSpace
  let : ChartedSpace ℂ E := hp.isLocalHomeomorph.chartedSpaceComap
  exact PunctureFilling.chartedSpace (isOpenEmbedding_chart hp hfin)

/-- At a point of the original cover, the preferred chart on the filled cover reads a nearby
point through the covering map and the standard complex chart of the thrice-punctured sphere. -/
theorem chartAt_incl_apply_incl {E : Type*} [TopologicalSpace E]
    {p : E → ThricePuncturedSphere}
    (hp : IsCoveringMap p) {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀}))
    (x y : E) :
    @chartAt ℂ _ _ _ (chartedSpace hp hfin) (PunctureFilling.incl (chart p) x)
        (PunctureFilling.incl (chart p) y) = p y := by
  let : ChartedSpace ℂ ThricePuncturedSphere :=
    ThricePuncturedSphere.isOpenEmbedding_coe.singletonChartedSpace
  let : ChartedSpace ℂ E := hp.isLocalHomeomorph.chartedSpaceComap
  rw [PunctureFilling.chartAt_incl_apply_incl]
  exact hp.isLocalHomeomorph.chartAt_chartedSpaceComap_apply x y

/-- At an added point, the preferred chart on the filled cover is inverse to the corresponding
filled disc. -/
theorem chartAt_center_apply_disc {E : Type*} [TopologicalSpace E]
    {p : E → ThricePuncturedSphere} (hp : IsCoveringMap p) {z₀ : ThricePuncturedSphere}
    (hfin : Finite (p ⁻¹' {z₀})) (i : FilledPoint p) (z : Set.Elem (ball (0 : ℂ) 1)) :
    @chartAt ℂ _ _ _ (chartedSpace hp hfin) (PunctureFilling.center (chart p) i)
        (PunctureFilling.disc (chart p) i z) = z := by
  let : ChartedSpace ℂ ThricePuncturedSphere :=
    ThricePuncturedSphere.isOpenEmbedding_coe.singletonChartedSpace
  let : ChartedSpace ℂ E := hp.isLocalHomeomorph.chartedSpaceComap
  exact PunctureFilling.chartAt_center_apply_disc (isOpenEmbedding_chart hp hfin) i z

end FilledCover

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Basic
public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Geometry.Manifold.Instances.PunctureFilling

import TauCeti.Geometry.Manifold.Complex.Chart

/-!
# The complex charts of the filled cover

Let `p : E → ℂ ∖ {0, 1}` be a covering map with finite fibres. Its filled cover
`TauCeti.FilledCover p` adds to `E` one point for each component of `p ⁻¹' D_q*` over each
puncture `q ∈ {0, 1, ∞}`. This file makes it a space charted over `ℂ`, and shows that the charts
are holomorphically compatible, so that the filled cover is a one-dimensional complex manifold.
Together with `TauCeti.FilledCover.t2Space` and `TauCeti.FilledCover.compactSpace` it is a compact
Riemann surface, connected when `E` is (`TauCeti.PunctureFilling.connectedSpace`).

The charts (`TauCeti.FilledCover.chartedSpace`) are those of the puncture filling
`TauCeti.PunctureFilling.chartedSpace`:

* at a point `x` of `E`, the chart is `p` itself, read in `ℂ`, near `x`
  (`TauCeti.FilledCover.chartAt_incl_apply_incl`); these are the charts of `ℂ` pulled back along
  the local homeomorphism `E → ℂ`;
* at the added point of a component `i` over `q`, the chart is the inverse of the filled disc of
  the filling chart `TauCeti.FilledCover.chart p i`, sending that point to `0`.

These charts are holomorphically compatible (`TauCeti.FilledCover.isManifold`). The only
transitions to check are between a filling chart and the charts of `E`, away from the added points:
along the filling chart of `i`, the cover `p` is `w ↦ w ^ e` followed by the inverse of the
standard coordinate of `D_q*` (`w ↦ w / 2`, `w ↦ 1 - w / 2` or `w ↦ 2 / w`), which is holomorphic.
A homeomorphism with holomorphic inverse is a holomorphic chart
(`OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn_symm`).

## Main declarations

* `TauCeti.FilledCover.chartedSpace`: the charts of the filled cover.
* `TauCeti.FilledCover.chartAt_incl_apply_incl`: the chart at a point of `E` reads every point of
  `E` as its image under `p`.
* `TauCeti.FilledCover.chartAt_incl_source`, `TauCeti.FilledCover.chartAt_incl_target`,
  `TauCeti.FilledCover.chartAt_incl_symm_apply`: the inverse of the chart at a point `x` of `E` is
  the local inverse of `p` at `x`.
* `TauCeti.FilledCover.chartAt_center_source`, `TauCeti.FilledCover.chartAt_center_apply_disc`,
  `TauCeti.FilledCover.chartAt_center_symm_apply`: the chart at an added point is the inverse of the
  filled disc of its component.
* `TauCeti.FilledCover.isManifold`: the filled cover is a complex manifold.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2.7 (the charts added at the filled points are declared holomorphic, and the transition
  functions are checked).
* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer 1981,
  §8, Theorem 8.4.
-/

public section

noncomputable section

namespace TauCeti

open Function Metric Set Topology ThricePuncturedSphere

open scoped ContDiff Manifold

/-- The punctured unit disc of `ℂ`, as a subtype. -/
local notation "𝔻*" => Set.Elem (ball (0 : ℂ) 1 \ {0})

namespace ThricePuncturedSphere.Puncture

/-- The inverse of the standard coordinate of the punctured neighbourhood of a puncture, as a
function on `ℂ`: `w ↦ w / 2` at `0`, `w ↦ 1 - w / 2` at `1` and `w ↦ 2 / w` at `∞`. -/
private def coordInv : Puncture → ℂ → ℂ
  | .zero, w => w / 2
  | .one, w => 1 - w / 2
  | .inf, w => 2 / w

private theorem coordInv_coord (q : Puncture) (y : q.neighborhood) :
    coordInv q (q.coord y) = ((y : ThricePuncturedSphere) : ℂ) := by
  cases q <;> simp [coordInv]

private theorem differentiableAt_coordInv (q : Puncture) {w : ℂ} (hw : w ≠ 0) :
    DifferentiableAt ℂ (coordInv q) w := by
  cases q
  · exact differentiableAt_id.div_const 2
  · exact (differentiableAt_id.div_const 2).const_sub 1
  · exact (differentiableAt_const 2).div differentiableAt_id hw

end ThricePuncturedSphere.Puncture

variable {E : Type*} [TopologicalSpace E] {p : E → ThricePuncturedSphere}

namespace FilledCover

open FilledPoint PunctureFilling

variable (hp : IsCoveringMap p) {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀}))
include hp hfin

/-- **The charts of the filled cover.** The filled cover of a covering map `p : E → ℂ ∖ {0, 1}`
with finite fibres is charted over `ℂ` as a puncture filling: `E` carries the charts of `ℂ` pulled
back along `p`, and the added point of each component `i` the inverse of the filled disc of its
filling chart `FilledCover.chart p i`. -/
@[instance_reducible]
def chartedSpace : ChartedSpace ℂ (FilledCover p) :=
  letI := (isOpenEmbedding_coe.isLocalHomeomorph.comp hp.isLocalHomeomorph).chartedSpaceComap
    (H := ℂ)
  PunctureFilling.chartedSpace (isOpenEmbedding_chart hp hfin)

/-- The chart of the filled cover at a point `x` of `E` reads every point `y` of `E` as its image
`p y` in `ℂ`. -/
theorem chartAt_incl_apply_incl (x y : E) :
    @chartAt ℂ _ _ _ (chartedSpace hp hfin) (incl (chart p) x) (incl (chart p) y) = p y := by
  have hπ := isOpenEmbedding_coe.isLocalHomeomorph.comp hp.isLocalHomeomorph
  let := hπ.chartedSpaceComap (H := ℂ)
  exact (PunctureFilling.chartAt_incl_apply_incl _ x y).trans
    (hπ.chartAt_chartedSpaceComap_apply x y)

/-- The chart of the filled cover at a point `x` of `E` is defined on the image in the filled
cover of the neighbourhood of `x` on which `p` is inverted by its local inverse at `x`. -/
theorem chartAt_incl_source (x : E) :
    (@chartAt ℂ _ _ _ (chartedSpace hp hfin) (incl (chart p) x)).source =
      incl (chart p) ''
        ((isOpenEmbedding_coe.isLocalHomeomorph.comp hp.isLocalHomeomorph).localInverseAt
          x).target := by
  have hπ := isOpenEmbedding_coe.isLocalHomeomorph.comp hp.isLocalHomeomorph
  let := hπ.chartedSpaceComap (H := ℂ)
  rw [PunctureFilling.chartAt_incl_source, hπ.chartAt_chartedSpaceComap]
  simp

/-- The chart of the filled cover at a point `x` of `E` takes values in the domain of the local
inverse of `p` at `x`. -/
theorem chartAt_incl_target (x : E) :
    (@chartAt ℂ _ _ _ (chartedSpace hp hfin) (incl (chart p) x)).target =
      ((isOpenEmbedding_coe.isLocalHomeomorph.comp hp.isLocalHomeomorph).localInverseAt
        x).source := by
  have hπ := isOpenEmbedding_coe.isLocalHomeomorph.comp hp.isLocalHomeomorph
  let := hπ.chartedSpaceComap (H := ℂ)
  rw [PunctureFilling.chartAt_incl_target, hπ.chartAt_chartedSpaceComap]
  simp

/-- The inverse of the chart of the filled cover at a point `x` of `E` is the local inverse of `p`
at `x`, followed by the inclusion of `E`. -/
theorem chartAt_incl_symm_apply (x : E) (z : ℂ) :
    (@chartAt ℂ _ _ _ (chartedSpace hp hfin) (incl (chart p) x)).symm z =
      incl (chart p)
        ((isOpenEmbedding_coe.isLocalHomeomorph.comp hp.isLocalHomeomorph).localInverseAt x z) := by
  have hπ := isOpenEmbedding_coe.isLocalHomeomorph.comp hp.isLocalHomeomorph
  let := hπ.chartedSpaceComap (H := ℂ)
  rw [PunctureFilling.chartAt_incl_symm_apply, hπ.chartAt_chartedSpaceComap]
  simp

/-- The chart of the filled cover at the added point of the component `i` is defined on the filled
disc of `i`. -/
theorem chartAt_center_source (i : FilledPoint p) :
    (@chartAt ℂ _ _ _ (chartedSpace hp hfin) (center (chart p) i)).source =
      range (disc (chart p) i) :=
  let := (isOpenEmbedding_coe.isLocalHomeomorph.comp hp.isLocalHomeomorph).chartedSpaceComap
    (H := ℂ)
  PunctureFilling.chartAt_center_source _ i

/-- The chart of the filled cover at the added point of a component takes values in the unit
disc. -/
theorem chartAt_center_target (i : FilledPoint p) :
    (@chartAt ℂ _ _ _ (chartedSpace hp hfin) (center (chart p) i)).target = ball (0 : ℂ) 1 :=
  let := (isOpenEmbedding_coe.isLocalHomeomorph.comp hp.isLocalHomeomorph).chartedSpaceComap
    (H := ℂ)
  PunctureFilling.chartAt_center_target _ i

/-- The chart of the filled cover at the added point of the component `i` reads the point
`disc (chart p) i z` of the filled disc of `i` as `z`. -/
theorem chartAt_center_apply_disc (i : FilledPoint p) (z : ball (0 : ℂ) 1) :
    @chartAt ℂ _ _ _ (chartedSpace hp hfin) (center (chart p) i) (disc (chart p) i z) = z :=
  let := (isOpenEmbedding_coe.isLocalHomeomorph.comp hp.isLocalHomeomorph).chartedSpaceComap
    (H := ℂ)
  PunctureFilling.chartAt_center_apply_disc _ i z

/-- The chart of the filled cover at the added point of a component sends that point to `0`. -/
theorem chartAt_center_apply_center (i : FilledPoint p) :
    @chartAt ℂ _ _ _ (chartedSpace hp hfin) (center (chart p) i) (center (chart p) i) = 0 :=
  let := (isOpenEmbedding_coe.isLocalHomeomorph.comp hp.isLocalHomeomorph).chartedSpaceComap
    (H := ℂ)
  PunctureFilling.chartAt_center_apply_center _ i

/-- The inverse of the chart of the filled cover at the added point of the component `i` is the
filled disc of `i`. -/
theorem chartAt_center_symm_apply (i : FilledPoint p) (z : ball (0 : ℂ) 1) :
    (@chartAt ℂ _ _ _ (chartedSpace hp hfin) (center (chart p) i)).symm z =
      disc (chart p) i z :=
  let := (isOpenEmbedding_coe.isLocalHomeomorph.comp hp.isLocalHomeomorph).chartedSpaceComap
    (H := ℂ)
  PunctureFilling.chartAt_center_symm_apply _ i z

/-- Along the filling chart of the component `i` over `q`, the cover `p` is `w ↦ w ^ degree p i`
followed by the inverse of the standard coordinate of `D_q*`. -/
private theorem coe_comp_chart (i : FilledPoint p) (w : 𝔻*) :
    (p (chart p i w) : ℂ) = (sigmaEquiv p i).1.coordInv ((w : ℂ) ^ degree p i) := by
  obtain ⟨hw, -, h⟩ := exists_coe_coord_chart_eq_pow hp hfin i w
  rw [← h, Puncture.coordInv_coord]

/-- **The filled cover is a complex manifold.** The charts of the filled cover of a covering map
`p : E → ℂ ∖ {0, 1}` with finite fibres are holomorphically compatible. -/
theorem isManifold {n : ℕ∞ω} :
    @IsManifold _ _ _ _ _ _ _ 𝓘(ℂ) n (FilledCover p) _ (chartedSpace hp hfin) := by
  have hπ := isOpenEmbedding_coe.isLocalHomeomorph.comp hp.isLocalHomeomorph
  let := hπ.chartedSpaceComap (H := ℂ)
  have : IsManifold 𝓘(ℂ) ω E := hπ.isManifold_chartedSpaceComap
  let := chartedSpace hp hfin
  suffices IsManifold 𝓘(ℂ) ω (FilledCover p) from IsManifold.of_le le_top
  -- The inverse of each filling chart is holomorphic: in the charts of `E` it is
  -- `w ↦ coordInv q (w ^ degree p i)`.
  refine PunctureFilling.isManifold (isOpenEmbedding_chart hp hfin) fun i ↦
    OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn_symm (by simp) _ ?_
  rw [puncturedDiscChart_target, hπ.contMDiffOn_chartedSpaceComap_iff]
  refine ⟨puncturedDiscChart_target (isOpenEmbedding_chart hp hfin i) ▸
    (puncturedDiscChart _).continuousOn_symm, ?_⟩
  rw [contMDiffOn_iff_contDiffOn]
  refine DifferentiableOn.contDiffOn (fun z hz ↦ ?_) (isOpen_ball.sdiff isClosed_singleton)
  have hd : DifferentiableAt ℂ (fun w : ℂ ↦ (sigmaEquiv p i).1.coordInv (w ^ degree p i)) z :=
    (Puncture.differentiableAt_coordInv _ (pow_ne_zero _ hz.2)).comp z (differentiableAt_pow _)
  refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds hz] with z' hz'
  have := puncturedDiscChart_symm_apply (isOpenEmbedding_chart hp hfin i) ⟨z', hz'⟩
  simp only [comp_apply, this, coe_comp_chart hp hfin]

end FilledCover

end TauCeti

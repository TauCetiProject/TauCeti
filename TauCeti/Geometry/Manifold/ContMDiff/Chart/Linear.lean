/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Maps which are linear in preferred charts

Let `X` and `Y` be charted spaces over normed spaces `E` and `E'`, with their self-models
`𝓘(𝕜, E)` and `𝓘(𝕜, E')`. Suppose a map `g : X → Y` is continuous at `p` and, near `p`, is read
in the preferred charts at `p` and at `g p` as a continuous linear map `L`:

`chartAt E' (g p) (g q) = L (chartAt E p q)` for `q` near `p`.

Then the coordinate expression of `g` at `p` agrees with `L` near the chart point of `p`, so `g` is
`C^m` at `p` for every `m`, including `m = ω`
(`TauCeti.contMDiffAt_of_eventually_chartAt_apply_eq`). A homeomorphism which is read in this way
through one continuous linear equivalence on the source of every preferred chart is therefore a
diffeomorphism of every order (`Homeomorph.toDiffeomorphOfChartAt`).

This is how two atlases on one space are compared when their preferred charts differ by a fixed
linear change of coordinates, for instance when both are read off the same charts of an ambient
manifold.

## Main declarations

* `TauCeti.contMDiffAt_of_eventually_chartAt_apply_eq`: a map which is linear in the preferred
  charts near a point is `C^m` there.
* `Homeomorph.toDiffeomorphOfChartAt`: a homeomorphism which is linear in the preferred charts is
  a diffeomorphism of every order.
-/

public section

open Filter Function Set
open scoped ContDiff Manifold Topology

variable {𝕜 E E' X Y : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace X]
  [ChartedSpace E X] [TopologicalSpace Y] [ChartedSpace E' Y] {m : ℕ∞ω}

namespace TauCeti

/-- A map which, near `p`, reads in the preferred charts at `p` and `g p` as a continuous linear
map `L` is `C^m` at `p`, for every `m`. -/
theorem contMDiffAt_of_eventually_chartAt_apply_eq {g : X → Y} {p : X} (hg : ContinuousAt g p)
    (L : E →L[𝕜] E') (hL : ∀ᶠ q in 𝓝 p, chartAt E' (g p) (g q) = L (chartAt E p q)) :
    ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E') m g p := by
  refine contMDiffAt_iff.2 ⟨hg, ?_⟩
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, range_id, contDiffWithinAt_univ, CompTriple.comp_eq]
  refine L.contDiff.contDiffAt.congr_of_eventuallyEq ?_
  have hsymm : Tendsto (chartAt E p).symm (𝓝 (chartAt E p p)) (𝓝 p) := by
    simpa only [(chartAt E p).left_inv (mem_chart_source E p)] using
      ((chartAt E p).continuousAt_symm (mem_chart_target E p)).tendsto
  filter_upwards [hsymm.eventually hL,
    (chartAt E p).open_target.mem_nhds (mem_chart_target E p)] with z hz hzt
  rw [comp_apply, comp_apply, hz, (chartAt E p).right_inv hzt]

end TauCeti

namespace Homeomorph

/-- A homeomorphism `h` which, on the source of the preferred chart at every point `p`, reads in
the preferred charts at `p` and `h p` as one continuous linear equivalence `L`, is a
diffeomorphism of every order `m`. -/
noncomputable def toDiffeomorphOfChartAt (h : X ≃ₜ Y) (L : E ≃L[𝕜] E')
    (hL : ∀ p, ∀ q ∈ (chartAt E p).source, chartAt E' (h p) (h q) = L (chartAt E p q))
    (m : ℕ∞ω) : Diffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') X Y m where
  toEquiv := h.toEquiv
  contMDiff_toFun p :=
    TauCeti.contMDiffAt_of_eventually_chartAt_apply_eq h.continuous.continuousAt (L : E →L[𝕜] E')
      (eventually_of_mem ((chartAt E p).open_source.mem_nhds (mem_chart_source E p)) (hL p))
  contMDiff_invFun y := by
    refine TauCeti.contMDiffAt_of_eventually_chartAt_apply_eq h.symm.continuous.continuousAt
      (L.symm : E' →L[𝕜] E) ?_
    have hsrc : ∀ᶠ y' in 𝓝 y, h.symm y' ∈ (chartAt E (h.symm y)).source :=
      h.symm.continuous.continuousAt.preimage_mem_nhds
        ((chartAt E (h.symm y)).open_source.mem_nhds (mem_chart_source E _))
    filter_upwards [hsrc] with y' hy'
    have := hL (h.symm y) (h.symm y') hy'
    rw [h.apply_symm_apply, h.apply_symm_apply] at this
    simp only [coe_symm_toEquiv, this,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

/-- The diffeomorphism `Homeomorph.toDiffeomorphOfChartAt` has the underlying map of `h`. -/
@[simp]
theorem coe_toDiffeomorphOfChartAt (h : X ≃ₜ Y) (L : E ≃L[𝕜] E')
    (hL : ∀ p, ∀ q ∈ (chartAt E p).source, chartAt E' (h p) (h q) = L (chartAt E p q))
    (m : ℕ∞ω) : ⇑(h.toDiffeomorphOfChartAt L hL m) = h :=
  (rfl)

/-- The inverse of `Homeomorph.toDiffeomorphOfChartAt` has the underlying map of `h.symm`. -/
@[simp]
theorem coe_toDiffeomorphOfChartAt_symm (h : X ≃ₜ Y) (L : E ≃L[𝕜] E')
    (hL : ∀ p, ∀ q ∈ (chartAt E p).source, chartAt E' (h p) (h q) = L (chartAt E p q))
    (m : ℕ∞ω) : ⇑(h.toDiffeomorphOfChartAt L hL m).symm = h.symm :=
  (rfl)

end Homeomorph

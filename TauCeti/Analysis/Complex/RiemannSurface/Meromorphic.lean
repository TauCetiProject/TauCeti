/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import TauCeti.Analysis.Complex.RiemannSurface.LocalMultiplicity
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Meromorphic functions on a Riemann surface and their orders

Let `X` be a Riemann surface, that is, a complex manifold modelled on `ℂ`, and let `f : X → E` be
a function valued in a complex normed space. Reading `f` in the chart `chartAt ℂ x` at `x` gives
the function `f ∘ (chartAt ℂ x).symm` of one complex variable. This file defines `f` to be
*meromorphic at `x`* (`TauCeti.RiemannSurface.MeromorphicAt`) when that representative is
meromorphic at `chartAt ℂ x x` in the sense of Mathlib's `MeromorphicAt`, and defines the
*order of `f` at `x`* (`TauCeti.RiemannSurface.meromorphicOrderAt`) as the meromorphic order of
the representative there, in `WithTop ℤ`: positive at a zero, negative at a pole, and `⊤` when
`f` vanishes on a punctured neighbourhood of `x`.

Since the transition maps between charts of the maximal atlas are holomorphic with nowhere
vanishing derivative, both notions may be computed in any chart of the maximal atlas at `x`
(`TauCeti.RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas` and
`TauCeti.RiemannSurface.meromorphicOrderAt_eq_of_mem_maximalAtlas`); they are invariants of the
function, not of the coordinate used to read it.

Pulling a meromorphic function back along a holomorphic map `φ : X → Y` gives a meromorphic
function (`TauCeti.RiemannSurface.MeromorphicAt.comp`), and when `φ` is nonconstant near `x` the
order is multiplied by the local multiplicity of `φ`:
`ord_x (F ∘ φ) = ord_{φ x} F * localMultiplicity φ x`
(`TauCeti.RiemannSurface.meromorphicOrderAt_comp`). This is the formula relating orders of a
function upstairs and downstairs along a branched covering.

## Main declarations

* `TauCeti.RiemannSurface.MeromorphicAt`: a function on a Riemann surface is meromorphic at `x`.
* `TauCeti.RiemannSurface.meromorphicOrderAt`: its order at `x`.
* `TauCeti.RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas` and
  `TauCeti.RiemannSurface.meromorphicOrderAt_eq_of_mem_maximalAtlas`: chart independence.
* `TauCeti.RiemannSurface.meromorphicAt_of_eventually_mdifferentiableAt`: a holomorphic function
  is meromorphic.
* `TauCeti.RiemannSurface.MeromorphicAt.comp` and `TauCeti.RiemannSurface.meromorphicOrderAt_comp`:
  pullback along a holomorphic map, with the order formula.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §1 (meromorphic functions) and §16 (divisors).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §§1 and 4.
-/

public noncomputable section

open Filter Function IsManifold Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X Y E : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
  [ChartedSpace ℂ Y] [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : X → E} {x : X}

/-! ### Definitions -/

/-- A function `f : X → E` on a Riemann surface is **meromorphic at `x`** if its representative
`f ∘ (chartAt ℂ x).symm` in the preferred chart at `x` is meromorphic at `chartAt ℂ x x`. Any
chart of the maximal atlas at `x` gives the same notion
(`TauCeti.RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas`). -/
def MeromorphicAt (f : X → E) (x : X) : Prop :=
  _root_.MeromorphicAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

theorem meromorphicAt_def (f : X → E) (x : X) :
    MeromorphicAt f x ↔ _root_.MeromorphicAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
  Iff.rfl

/-- The **order** of a function `f : X → E` on a Riemann surface at `x`: the meromorphic order of
its representative in the preferred chart at `x`. It is positive at a zero, negative at a pole,
and `⊤` when `f` vanishes on a punctured neighbourhood of `x`. Any chart of the maximal atlas at
`x` gives the same value (`TauCeti.RiemannSurface.meromorphicOrderAt_eq_of_mem_maximalAtlas`).
If `f` is not meromorphic at `x` the value is the junk value `0`, as for `meromorphicOrderAt`. -/
def meromorphicOrderAt (f : X → E) (x : X) : WithTop ℤ :=
  _root_.meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)

theorem meromorphicOrderAt_def (f : X → E) (x : X) :
    meromorphicOrderAt f x = _root_.meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) :=
  (rfl)

/-- The order of a function that is not meromorphic at `x` is the junk value `0`. -/
theorem meromorphicOrderAt_of_not_meromorphicAt (hf : ¬ MeromorphicAt f x) :
    meromorphicOrderAt f x = 0 :=
  _root_.meromorphicOrderAt_of_not_meromorphicAt hf

/-! ### Values on a punctured neighbourhood -/

/-- The inverse of the chart at `x` maps punctured neighbourhoods of `chartAt ℂ x x` into
punctured neighbourhoods of `x`. -/
private theorem tendsto_chartAt_symm_nhdsNE (x : X) :
    Tendsto (chartAt ℂ x).symm (𝓝[≠] (chartAt ℂ x x)) (𝓝[≠] x) := by
  have hx := mem_chart_source ℂ x
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (((chartAt ℂ x).tendsto_symm hx).mono_left nhdsWithin_le_nhds) ?_
  simpa [(chartAt ℂ x).left_inv hx] using
    (chartAt ℂ x).symm.eventually_ne_nhdsWithin ((chartAt ℂ x).map_source hx)

/-- Being meromorphic at `x` only depends on the values on a punctured neighbourhood of `x`. -/
theorem MeromorphicAt.congr (hf : MeromorphicAt f x) (h : f =ᶠ[𝓝[≠] x] g) :
    MeromorphicAt g x :=
  _root_.MeromorphicAt.congr hf (h.comp_tendsto (tendsto_chartAt_symm_nhdsNE x))

/-- Functions agreeing on a punctured neighbourhood of `x` are meromorphic at `x` together. -/
theorem meromorphicAt_congr (h : f =ᶠ[𝓝[≠] x] g) : MeromorphicAt f x ↔ MeromorphicAt g x :=
  ⟨fun hf ↦ hf.congr h, fun hg ↦ hg.congr h.symm⟩

/-- The order at `x` only depends on the values on a punctured neighbourhood of `x`. -/
theorem meromorphicOrderAt_congr (h : f =ᶠ[𝓝[≠] x] g) :
    meromorphicOrderAt f x = meromorphicOrderAt g x :=
  _root_.meromorphicOrderAt_congr (h.comp_tendsto (tendsto_chartAt_symm_nhdsNE x))

/-- Near `e x`, the representative of `k` in a chart `e` is its representative in the preferred
chart at `x`, composed with the transition map from `e` to that chart. -/
private theorem comp_symm_eventuallyEq_comp_symm_comp {α : Type*} (k : X → α)
    {e : OpenPartialHomeomorph X ℂ} (hx : x ∈ e.source) :
    k ∘ e.symm =ᶠ[𝓝 (e x)] (k ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x ∘ e.symm) := by
  filter_upwards [(e.tendsto_symm hx).eventually
    ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))] with z hz
  simp [(chartAt ℂ x).left_inv hz]

/-- Near `chartAt ℂ x x`, the representative of `k ∘ φ` is the representative of `k` composed with
the representative of `φ`. -/
private theorem comp_comp_chartAt_symm_eventuallyEq {α : Type*} (k : Y → α) {φ : X → Y}
    (hφ : ContinuousAt φ x) :
    (k ∘ φ) ∘ (chartAt ℂ x).symm =ᶠ[𝓝 (chartAt ℂ x x)]
      (k ∘ (chartAt ℂ (φ x)).symm) ∘ fun z ↦ chartAt ℂ (φ x) (φ ((chartAt ℂ x).symm z)) := by
  have hcont : Tendsto (fun z ↦ φ ((chartAt ℂ x).symm z)) (𝓝 (chartAt ℂ x x)) (𝓝 (φ x)) :=
    hφ.tendsto.comp ((chartAt ℂ x).tendsto_symm (mem_chart_source ℂ x))
  filter_upwards [hcont.eventually
    ((chartAt ℂ (φ x)).open_source.mem_nhds (mem_chart_source ℂ (φ x)))] with z hz
  simp [(chartAt ℂ (φ x)).left_inv hz]

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]

/-! ### Chart independence -/

section ChartIndependence

variable {e : OpenPartialHomeomorph X ℂ} (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (hx : x ∈ e.source)
include he hx

/-- **Chart independence of meromorphy.** A function is meromorphic at `x` exactly when its
representative in some (equivalently, any) chart of the maximal atlas at `x` is meromorphic at the
coordinate of `x`. -/
theorem meromorphicAt_iff_of_mem_maximalAtlas :
    MeromorphicAt f x ↔ _root_.MeromorphicAt (f ∘ e.symm) (e x) := by
  have hcx := mem_chart_source ℂ x
  rw [_root_.MeromorphicAt.meromorphicAt_congr
      ((comp_symm_eventuallyEq_comp_symm_comp f hx).filter_mono nhdsWithin_le_nhds),
    meromorphicAt_comp_iff_of_deriv_ne_zero
      (analyticAt_symm_trans he (chart_mem_maximalAtlas x) hx hcx)
      (deriv_symm_trans_ne_zero he (chart_mem_maximalAtlas x) hx hcx)]
  simp [MeromorphicAt, e.left_inv hx]

/-- **Chart independence of the order.** The order of a function at `x` is the meromorphic order
of its representative in any chart of the maximal atlas at `x`. -/
theorem meromorphicOrderAt_eq_of_mem_maximalAtlas :
    meromorphicOrderAt f x = _root_.meromorphicOrderAt (f ∘ e.symm) (e x) := by
  have hcx := mem_chart_source ℂ x
  rw [_root_.meromorphicOrderAt_congr
      ((comp_symm_eventuallyEq_comp_symm_comp f hx).filter_mono nhdsWithin_le_nhds),
    meromorphicOrderAt_comp_of_deriv_ne_zero
      (analyticAt_symm_trans he (chart_mem_maximalAtlas x) hx hcx)
      (deriv_symm_trans_ne_zero he (chart_mem_maximalAtlas x) hx hcx)]
  simp [meromorphicOrderAt, e.left_inv hx]

end ChartIndependence

/-- A function holomorphic near `x` is meromorphic at `x`. -/
theorem meromorphicAt_of_eventually_mdifferentiableAt [CompleteSpace E]
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ, E) f y) : MeromorphicAt f x := by
  have hcx := mem_chart_source ℂ x
  refine AnalyticAt.meromorphicAt ?_
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [(chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hcx),
    ((chartAt ℂ x).tendsto_symm hcx).eventually hf] with z hz hfz
  exact mdifferentiableAt_iff_differentiableAt.1
    (hfz.comp z (mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ x) hz))

/-! ### Pullback along a holomorphic map -/

section Comp

variable {F : Y → E} {φ : X → Y}

/-- **Pullback of a meromorphic function.** A function meromorphic at `φ x`, pulled back along a
map `φ` holomorphic near `x`, is meromorphic at `x`. -/
theorem MeromorphicAt.comp (hF : MeromorphicAt F (φ x))
    (hφ : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ y) : MeromorphicAt (F ∘ φ) x := by
  have hF' : _root_.MeromorphicAt (F ∘ (chartAt ℂ (φ x)).symm)
      (chartAt ℂ (φ x) (φ ((chartAt ℂ x).symm (chartAt ℂ x x)))) := by
    rwa [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  exact (hF'.comp_analyticAt (g := fun z ↦ chartAt ℂ (φ x) (φ ((chartAt ℂ x).symm z)))
    (analyticAt_chartAt_comp_comp_chartAt_symm hφ)).congr
    ((comp_comp_chartAt_symm_eventuallyEq F hφ.self_of_nhds.continuousAt).symm.filter_mono
      nhdsWithin_le_nhds)

/-- **The order formula for pullbacks.** Pulling a function meromorphic at `φ x` back along a map
`φ` holomorphic and nonconstant near `x` multiplies its order by the local multiplicity of `φ`
at `x`. -/
theorem meromorphicOrderAt_comp (hF : MeromorphicAt F (φ x))
    (hφ : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ y) (hnc : ¬ EventuallyConst φ (𝓝 x)) :
    meromorphicOrderAt (F ∘ φ) x = meromorphicOrderAt F (φ x) * localMultiplicity φ x := by
  have hcx := mem_chart_source ℂ x
  have hF' : _root_.MeromorphicAt (F ∘ (chartAt ℂ (φ x)).symm)
      (chartAt ℂ (φ x) (φ ((chartAt ℂ x).symm (chartAt ℂ x x)))) := by
    rwa [(chartAt ℂ x).left_inv hcx]
  have hmult := natCast_localMultiplicity hφ hnc
  -- The representative of `φ` is not constant near `chartAt ℂ x x`, since its recentred order of
  -- vanishing is the finite local multiplicity of `φ`.
  have hnc' : ¬ EventuallyConst (fun z ↦ chartAt ℂ (φ x) (φ ((chartAt ℂ x).symm z)))
      (𝓝 (chartAt ℂ x x)) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top]
    simp [(chartAt ℂ x).left_inv hcx, ← hmult]
  rw [meromorphicOrderAt, _root_.meromorphicOrderAt_congr
      ((comp_comp_chartAt_symm_eventuallyEq F hφ.self_of_nhds.continuousAt).filter_mono
        nhdsWithin_le_nhds),
    hF'.meromorphicOrderAt_comp (g := fun z ↦ chartAt ℂ (φ x) (φ ((chartAt ℂ x).symm z)))
      (analyticAt_chartAt_comp_comp_chartAt_symm hφ) hnc']
  simp [meromorphicOrderAt, (chartAt ℂ x).left_inv hcx, ← hmult]

end Comp

end TauCeti.RiemannSurface

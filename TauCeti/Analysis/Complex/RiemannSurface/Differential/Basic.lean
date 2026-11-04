/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Meromorphic
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Chart
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Meromorphic and holomorphic `1`-forms on a Riemann surface

A `1`-form on a Riemann surface `X` assigns to each point `x` a complex covector, a `ℂ`-linear map
`TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ`; these are the fibres of the holomorphic cotangent bundle
`TauCeti.CotangentBundle 𝓘(ℂ) X`. This file calls such a field of covectors, with no regularity
imposed, a `TauCeti.RiemannSurface.OneForm X`. In a chart `z = e` of the maximal atlas every
covector is a multiple of the differential `dz = de` of the chart
(`TauCeti.RiemannSurface.OneForm.coeff_smul_mvfderiv`), so `ω = f dz` locally, where the
**coefficient** `f = TauCeti.RiemannSurface.OneForm.coeff ω e` is `ω` evaluated on the coordinate
vector field `∂/∂z`. Changing to a second chart `w` multiplies the coefficient by the derivative of
the transition map: if `ω = f dz = g dw` then `g(w) = f(z(w)) · dz/dw`
(`TauCeti.RiemannSurface.OneForm.coeff_eq_coeff_mul_deriv`). This is the classical description of
a differential as a family of local expressions `f(z) dz` related by the chain rule.

Since transition maps are holomorphic with nowhere vanishing derivative, being meromorphic or
holomorphic at `x`, and the order `ord_x ω ∈ WithTop ℤ`, may be computed from the coefficient in any
chart of the maximal atlas at `x`
(`TauCeti.RiemannSurface.OneForm.meromorphicAt_iff_of_mem_maximalAtlas`,
`TauCeti.RiemannSurface.OneForm.holomorphicAt_iff_of_mem_maximalAtlas` and
`TauCeti.RiemannSurface.OneForm.order_eq_of_mem_maximalAtlas`). As for functions, meromorphy and the
order only see a punctured neighbourhood of `x`, so the value of a meromorphic `1`-form at a pole
is junk.

Meromorphic `1`-forms form a module over meromorphic functions, with
`ord_x (f ω) = ord_x f + ord_x ω` (`TauCeti.RiemannSurface.OneForm.order_smul`). The differential
`df` of a function `f : X → ℂ` is Mathlib's `mvfderiv 𝓘(ℂ) f`. Its coefficient in a chart is the
derivative of the chart representative of `f`, so `df` is meromorphic when `f` is, with
`ord_x df = ord_x f - 1` at the zeros and poles of `f`; at a point where `f` is holomorphic and
nonconstant, `ord_x df` is one less than the local multiplicity of `f`, the ramification index.

## Main definitions

* `TauCeti.RiemannSurface.OneForm X`: fields of complex covectors on `X`.
* `TauCeti.RiemannSurface.OneForm.coeff ω e`: the coefficient of `ω` in the chart `e`.
* `TauCeti.RiemannSurface.OneForm.MeromorphicAt`, `TauCeti.RiemannSurface.OneForm.HolomorphicAt`
  and `TauCeti.RiemannSurface.OneForm.order`: meromorphy, holomorphy and the order at a point.
* `TauCeti.RiemannSurface.holomorphicOneForms X`: the vector space of holomorphic `1`-forms.

## Main results

* `TauCeti.RiemannSurface.OneForm.coeff_smul_mvfderiv`: `ω = f dz` in a chart.
* `TauCeti.RiemannSurface.OneForm.coeff_eq_coeff_mul_deriv`: the transformation law.
* `TauCeti.RiemannSurface.OneForm.order_smul`: `ord_x (f ω) = ord_x f + ord_x ω`.
* `TauCeti.RiemannSurface.OneForm.order_mvfderiv`: `ord_x df = ord_x f - 1` at zeros and poles.
* `TauCeti.RiemannSurface.OneForm.order_mvfderiv_eq_localMultiplicity_sub_one`: `ord_x df` is the
  ramification index minus one.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §9 (holomorphic and meromorphic differential forms, their local expressions and orders).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter IV §1 (holomorphic and meromorphic `1`-forms, the
  transformation rule, and the order of a meromorphic `1`-form).
-/

public noncomputable section

open Filter Function IsManifold Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A **`1`-form** on a Riemann surface `X`, with no regularity imposed: a complex covector
`TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ` at each point `x`, the fibre of the holomorphic cotangent bundle
`TauCeti.CotangentBundle 𝓘(ℂ) X`. Meromorphic and holomorphic `1`-forms are the fields satisfying
`TauCeti.RiemannSurface.OneForm.MeromorphicAt` and `TauCeti.RiemannSurface.OneForm.HolomorphicAt`
at every point. -/
abbrev OneForm : Type _ := (x : X) → TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ

variable {X}

/-- A complex covector at a point of a Riemann surface is determined by its value on one nonzero
tangent vector, since the tangent space is one-dimensional. -/
theorem covector_ext {y : X} {p q : TangentSpace 𝓘(ℂ) y →L[ℂ] ℂ} {v : TangentSpace 𝓘(ℂ) y}
    (hv : v ≠ 0) (h : p v = q v) : p = q := by
  refine ContinuousLinearMap.ext fun w ↦ ?_
  have hw : w = (tangentSpaceCastModel 𝓘(ℂ) y w / tangentSpaceCastModel 𝓘(ℂ) y v) • v := by
    apply (tangentSpaceCastModel 𝓘(ℂ) y).injective
    rw [map_smul, smul_eq_mul, div_mul_cancel₀]
    simpa using hv
  rw [hw, map_smul, map_smul, h]

namespace OneForm

/-- The **coefficient** of a `1`-form `ω` in a chart `z = e`: the function `f` with `ω = f dz`,
that is, `ω` evaluated on the coordinate vector `∂/∂z = d(e⁻¹)(1)` at `e⁻¹ z`
(`TauCeti.RiemannSurface.OneForm.coeff_smul_mvfderiv`). -/
def coeff (ω : OneForm X) (e : OpenPartialHomeomorph X ℂ) (z : ℂ) : ℂ :=
  ω (e.symm z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) e.symm z ((NormedSpace.fromTangentSpace z).symm 1))

variable {ω : OneForm X} {e e' : OpenPartialHomeomorph X ℂ}

/-- The differential of a chart takes the value `1` on the coordinate vector `∂/∂z` of the
chart. -/
theorem mvfderiv_mfderiv_symm (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) {z : ℂ} (hz : z ∈ e.target) :
    mvfderiv 𝓘(ℂ) e (e.symm z)
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) e.symm z ((NormedSpace.fromTangentSpace z).symm 1)) = 1 := by
  have hd : e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) :=
    ⟨fun _ hx ↦ (mdifferentiableAt_of_mem_maximalAtlas he hx).mdifferentiableWithinAt,
      fun _ hz ↦ (mdifferentiableAt_symm_of_mem_maximalAtlas he hz).mdifferentiableWithinAt⟩
  have := congrArg (fun L ↦ L ((NormedSpace.fromTangentSpace (𝕜 := ℂ) z).symm 1))
    (hd.comp_symm_deriv hz)
  simp only [ContinuousLinearMap.comp_apply] at this
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, this]
  rfl

/-- The differential of a chart vanishes nowhere on its domain. -/
theorem mvfderiv_ne_zero (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) {y : X} (hy : y ∈ e.source) :
    mvfderiv 𝓘(ℂ) e y ≠ 0 := by
  have h := mvfderiv_mfderiv_symm he (e.map_source hy)
  intro h0
  rw [e.left_inv hy, h0] at h
  simp at h

/-- **`ω = f dz` in a chart.** At a point of the chart `e`, the covector `ω` is its coefficient in
`e` times the differential `de` of the chart. -/
theorem coeff_smul_mvfderiv (ω : OneForm X) (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) {z : ℂ}
    (hz : z ∈ e.target) :
    ω.coeff e z • mvfderiv 𝓘(ℂ) e (e.symm z) = ω (e.symm z) := by
  have hv := mvfderiv_mfderiv_symm he hz
  refine covector_ext (v := mfderiv 𝓘(ℂ) 𝓘(ℂ) e.symm z ((NormedSpace.fromTangentSpace z).symm 1))
    (fun h0 ↦ by rw [h0, map_zero] at hv; exact zero_ne_one hv) ?_
  rw [smul_apply, hv, smul_eq_mul, mul_one, coeff]

/-- The coefficient of `ω` in a chart is the unique scalar `c` with `ω = c de` at the
corresponding point. -/
theorem coeff_eq_iff (ω : OneForm X) (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) {y : X}
    (hy : y ∈ e.source) {c : ℂ} : ω.coeff e (e y) = c ↔ c • mvfderiv 𝓘(ℂ) e y = ω y := by
  have h := ω.coeff_smul_mvfderiv he (e.map_source hy)
  rw [e.left_inv hy] at h
  rw [← h]
  exact ⟨fun hc ↦ hc ▸ rfl, fun hc ↦ smul_left_injective ℂ (mvfderiv_ne_zero he hy) hc.symm⟩

/-- The differentials of two charts differ by the derivative of the transition map. -/
theorem mvfderiv_eq_deriv_smul (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X)
    (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 X) {y : X} (hy : y ∈ e.source) (hy' : y ∈ e'.source) :
    mvfderiv 𝓘(ℂ) e y = deriv (e ∘ e'.symm) (e' y) • mvfderiv 𝓘(ℂ) e' y := by
  have hev : (e : X → ℂ) =ᶠ[𝓝 y] (e ∘ e'.symm) ∘ e' := by
    filter_upwards [e'.open_source.mem_nhds hy'] with w hw
    simp [e'.left_inv hw]
  have hψ := TauCeti.analyticAt_symm_trans he' he hy' hy
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [hev.mvfderiv_eq, mvfderiv_comp_apply_of_differentiableAt hψ.differentiableAt
    (mdifferentiableAt_of_mem_maximalAtlas he' hy'), fderiv_eq_smul_deriv, smul_apply,
    smul_eq_mul, smul_eq_mul, mul_comm]

/-- **The transformation law of a `1`-form.** If `ω = f dz` in the chart `z = e` and
`ω = g dw` in the chart `w = e'`, then `g(w) = f(z(w)) · dz/dw`. -/
theorem coeff_eq_coeff_mul_deriv (ω : OneForm X) (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X)
    (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 X) {y : X} (hy : y ∈ e.source) (hy' : y ∈ e'.source) :
    ω.coeff e' (e' y) = ω.coeff e (e y) * deriv (e ∘ e'.symm) (e' y) := by
  rw [coeff_eq_iff ω he' hy', mul_smul, ← mvfderiv_eq_deriv_smul he he' hy hy',
    ← coeff_eq_iff ω he hy]

/-- Near a common point of two charts, the coefficients in the two charts are related by the
transformation law. -/
theorem coeff_eventuallyEq (ω : OneForm X) (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X)
    (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 X) {x : X} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ω.coeff e' =ᶠ[𝓝 (e' x)] (ω.coeff e ∘ (e ∘ e'.symm)) * deriv (e ∘ e'.symm) := by
  have hsrc : e'.symm (e' x) ∈ e.source := by rwa [e'.left_inv hx']
  filter_upwards [e'.open_target.mem_nhds (e'.map_source hx'),
    (e'.continuousAt_symm (e'.map_source hx')).preimage_mem_nhds (e.open_source.mem_nhds hsrc)]
    with w hw hw'
  have h := coeff_eq_coeff_mul_deriv ω he he' hw' (e'.map_target hw)
  rw [e'.right_inv hw] at h
  rw [h, Pi.mul_apply, comp_apply, comp_apply]

omit [ChartedSpace ℂ X] in
private theorem transition_apply {x : X} (hx' : x ∈ e'.source) : (e ∘ e'.symm) (e' x) = e x := by
  simp [e'.left_inv hx']

section ChartChange

variable (ω) (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 X) {x : X}
  (hx : x ∈ e.source) (hx' : x ∈ e'.source)
include he he' hx hx'

private theorem meromorphicAt_coeff_of_meromorphicAt
    (h : _root_.MeromorphicAt (ω.coeff e) (e x)) :
    _root_.MeromorphicAt (ω.coeff e') (e' x) := by
  have hψ := TauCeti.analyticAt_symm_trans he' he hx' hx
  rw [← transition_apply hx'] at h
  exact ((h.comp_analyticAt hψ).mul hψ.deriv.meromorphicAt).congr
    ((coeff_eventuallyEq ω he he' hx hx').symm.filter_mono nhdsWithin_le_nhds)

private theorem analyticAt_coeff_of_analyticAt (h : AnalyticAt ℂ (ω.coeff e) (e x)) :
    AnalyticAt ℂ (ω.coeff e') (e' x) := by
  have hψ := TauCeti.analyticAt_symm_trans he' he hx' hx
  rw [← transition_apply hx'] at h
  exact ((h.comp hψ).mul hψ.deriv).congr (coeff_eventuallyEq ω he he' hx hx').symm

private theorem meromorphicOrderAt_coeff_eq :
    _root_.meromorphicOrderAt (ω.coeff e') (e' x) =
      _root_.meromorphicOrderAt (ω.coeff e) (e x) := by
  by_cases h : _root_.MeromorphicAt (ω.coeff e) (e x)
  · have hψ := TauCeti.analyticAt_symm_trans he' he hx' hx
    have hψ' := TauCeti.deriv_symm_trans_ne_zero he' he hx' hx
    rw [← transition_apply hx'] at h
    rw [_root_.meromorphicOrderAt_congr ((coeff_eventuallyEq ω he he' hx hx').filter_mono
        nhdsWithin_le_nhds),
      _root_.meromorphicOrderAt_mul (h.comp_analyticAt hψ) hψ.deriv.meromorphicAt,
      meromorphicOrderAt_comp_of_deriv_ne_zero hψ hψ',
      hψ.deriv.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.2 (Or.inr hψ'),
      transition_apply hx']
    simp
  · rw [_root_.meromorphicOrderAt_of_not_meromorphicAt h,
      _root_.meromorphicOrderAt_of_not_meromorphicAt
        fun h' ↦ h (meromorphicAt_coeff_of_meromorphicAt ω he' he hx' hx h')]

end ChartChange

/-! ### Meromorphic and holomorphic `1`-forms -/

/-- A `1`-form is **meromorphic at `x`** if its coefficient in the preferred chart at `x` is
meromorphic at the coordinate of `x`. Any chart of the maximal atlas at `x` gives the same notion
(`TauCeti.RiemannSurface.OneForm.meromorphicAt_iff_of_mem_maximalAtlas`). -/
def MeromorphicAt (ω : OneForm X) (x : X) : Prop :=
  _root_.MeromorphicAt (ω.coeff (chartAt ℂ x)) (chartAt ℂ x x)

/-- A `1`-form is **holomorphic at `x`** if its coefficient in the preferred chart at `x` is
analytic at the coordinate of `x`. Any chart of the maximal atlas at `x` gives the same notion
(`TauCeti.RiemannSurface.OneForm.holomorphicAt_iff_of_mem_maximalAtlas`). -/
def HolomorphicAt (ω : OneForm X) (x : X) : Prop :=
  AnalyticAt ℂ (ω.coeff (chartAt ℂ x)) (chartAt ℂ x x)

/-- The **order** of a `1`-form at `x`: the meromorphic order of its coefficient in the preferred
chart at `x`. It is positive at a zero, negative at a pole, and `⊤` when `ω` vanishes on a punctured
neighbourhood of `x`. Any chart of the maximal atlas at `x` gives the same value
(`TauCeti.RiemannSurface.OneForm.order_eq_of_mem_maximalAtlas`). If `ω` is not meromorphic at `x`
the value is the junk value `0`, as for `meromorphicOrderAt`. -/
def order (ω : OneForm X) (x : X) : WithTop ℤ :=
  _root_.meromorphicOrderAt (ω.coeff (chartAt ℂ x)) (chartAt ℂ x x)

theorem meromorphicAt_def (ω : OneForm X) (x : X) :
    ω.MeromorphicAt x ↔ _root_.MeromorphicAt (ω.coeff (chartAt ℂ x)) (chartAt ℂ x x) :=
  Iff.rfl

theorem holomorphicAt_def (ω : OneForm X) (x : X) :
    ω.HolomorphicAt x ↔ AnalyticAt ℂ (ω.coeff (chartAt ℂ x)) (chartAt ℂ x x) :=
  Iff.rfl

theorem order_def (ω : OneForm X) (x : X) :
    ω.order x = _root_.meromorphicOrderAt (ω.coeff (chartAt ℂ x)) (chartAt ℂ x x) :=
  (rfl)

section IsManifold

variable [IsManifold 𝓘(ℂ) 1 X] {x : X}

/-- **Chart independence of meromorphy.** A `1`-form is meromorphic at `x` exactly when its
coefficient in some (equivalently, any) chart of the maximal atlas at `x` is meromorphic at the
coordinate of `x`. -/
theorem meromorphicAt_iff_of_mem_maximalAtlas (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X)
    (hx : x ∈ e.source) : ω.MeromorphicAt x ↔ _root_.MeromorphicAt (ω.coeff e) (e x) :=
  ⟨meromorphicAt_coeff_of_meromorphicAt ω (chart_mem_maximalAtlas x) he (mem_chart_source ℂ x) hx,
    meromorphicAt_coeff_of_meromorphicAt ω he (chart_mem_maximalAtlas x) hx (mem_chart_source ℂ x)⟩

/-- **Chart independence of holomorphy.** A `1`-form is holomorphic at `x` exactly when its
coefficient in some (equivalently, any) chart of the maximal atlas at `x` is analytic at the
coordinate of `x`. -/
theorem holomorphicAt_iff_of_mem_maximalAtlas (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X)
    (hx : x ∈ e.source) : ω.HolomorphicAt x ↔ AnalyticAt ℂ (ω.coeff e) (e x) :=
  ⟨analyticAt_coeff_of_analyticAt ω (chart_mem_maximalAtlas x) he (mem_chart_source ℂ x) hx,
    analyticAt_coeff_of_analyticAt ω he (chart_mem_maximalAtlas x) hx (mem_chart_source ℂ x)⟩

/-- **Chart independence of the order.** The order of a `1`-form at `x` is the meromorphic order of
its coefficient in any chart of the maximal atlas at `x`. -/
theorem order_eq_of_mem_maximalAtlas (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (hx : x ∈ e.source) :
    ω.order x = _root_.meromorphicOrderAt (ω.coeff e) (e x) :=
  (meromorphicOrderAt_coeff_eq ω (chart_mem_maximalAtlas x) he (mem_chart_source ℂ x) hx).symm

end IsManifold

/-! ### Local behaviour -/

section Local

variable {η : OneForm X} {x : X}

/-- A holomorphic `1`-form is meromorphic. -/
theorem HolomorphicAt.meromorphicAt (h : ω.HolomorphicAt x) : ω.MeromorphicAt x :=
  AnalyticAt.meromorphicAt h

/-- A holomorphic `1`-form has nonnegative order. -/
theorem HolomorphicAt.order_nonneg (h : ω.HolomorphicAt x) : 0 ≤ ω.order x :=
  AnalyticAt.meromorphicOrderAt_nonneg h

private theorem coeff_chartAt_eventuallyEq (h : ∀ᶠ y in 𝓝[≠] x, ω y = η y) :
    ω.coeff (chartAt ℂ x) =ᶠ[𝓝[≠] (chartAt ℂ x x)] η.coeff (chartAt ℂ x) :=
  ((tendsto_chartAt_symm_nhdsNE x).eventually h).mono fun z hz ↦ by rw [coeff, coeff, hz]

/-- Meromorphy at `x` only depends on the values on a punctured neighbourhood of `x`. -/
theorem MeromorphicAt.congr (hω : ω.MeromorphicAt x) (h : ∀ᶠ y in 𝓝[≠] x, ω y = η y) :
    η.MeromorphicAt x :=
  _root_.MeromorphicAt.congr hω (coeff_chartAt_eventuallyEq h)

/-- The order at `x` only depends on the values on a punctured neighbourhood of `x`. -/
theorem order_congr (h : ∀ᶠ y in 𝓝[≠] x, ω y = η y) : ω.order x = η.order x :=
  _root_.meromorphicOrderAt_congr (coeff_chartAt_eventuallyEq h)

/-- Holomorphy at `x` only depends on the values on a neighbourhood of `x`. -/
theorem HolomorphicAt.congr (hω : ω.HolomorphicAt x) (h : ∀ᶠ y in 𝓝 x, ω y = η y) :
    η.HolomorphicAt x :=
  AnalyticAt.congr hω ((((chartAt ℂ x).continuousAt_symm
    ((chartAt ℂ x).map_source (mem_chart_source ℂ x))).eventually
      (by rwa [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)])).mono
    fun z hz ↦ by rw [coeff, coeff, hz])

/-- **A holomorphic `1`-form is determined by its values off a point.** Two `1`-forms holomorphic
at `x` which agree on a punctured neighbourhood of `x` agree at `x`. -/
theorem HolomorphicAt.apply_eq_of_eventually [IsManifold 𝓘(ℂ) 1 X] (hω : ω.HolomorphicAt x)
    (hη : η.HolomorphicAt x) (h : ∀ᶠ y in 𝓝[≠] x, ω y = η y) : ω x = η x := by
  have hcx := mem_chart_source ℂ x
  have hc : ω.coeff (chartAt ℂ x) (chartAt ℂ x x) = η.coeff (chartAt ℂ x) (chartAt ℂ x x) :=
    tendsto_nhds_unique_of_eventuallyEq (hω.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hη.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (coeff_chartAt_eventuallyEq h)
  have h₁ := (coeff_eq_iff ω (chart_mem_maximalAtlas x) hcx).1 rfl
  have h₂ := (coeff_eq_iff η (chart_mem_maximalAtlas x) hcx).1 rfl
  rw [← h₁, ← h₂, hc]

end Local

/-! ### Algebra -/

section Algebra

variable {η : OneForm X} {x : X}

@[simp]
theorem coeff_zero (e : OpenPartialHomeomorph X ℂ) : (0 : OneForm X).coeff e = 0 :=
  (rfl)

@[simp]
theorem coeff_add (ω η : OneForm X) (e : OpenPartialHomeomorph X ℂ) :
    (ω + η).coeff e = ω.coeff e + η.coeff e :=
  (rfl)

@[simp]
theorem coeff_neg (ω : OneForm X) (e : OpenPartialHomeomorph X ℂ) :
    (-ω).coeff e = -ω.coeff e :=
  (rfl)

@[simp]
theorem coeff_sub (ω η : OneForm X) (e : OpenPartialHomeomorph X ℂ) :
    (ω - η).coeff e = ω.coeff e - η.coeff e :=
  (rfl)

@[simp]
theorem coeff_const_smul (c : ℂ) (ω : OneForm X) (e : OpenPartialHomeomorph X ℂ) :
    (c • ω).coeff e = c • ω.coeff e :=
  (rfl)

/-- The coefficient of `f ω` is `f` read in the chart times the coefficient of `ω`. -/
@[simp]
theorem coeff_smul (f : X → ℂ) (ω : OneForm X) (e : OpenPartialHomeomorph X ℂ) :
    (f • ω).coeff e = (f ∘ e.symm) * ω.coeff e :=
  (rfl)

/-- The zero `1`-form is holomorphic. -/
@[simp]
theorem holomorphicAt_zero (x : X) : (0 : OneForm X).HolomorphicAt x := by
  rw [holomorphicAt_def, coeff_zero]
  exact analyticAt_const

/-- The zero `1`-form has order `⊤` everywhere. -/
@[simp]
theorem order_zero (x : X) : (0 : OneForm X).order x = ⊤ := by
  rw [order_def, coeff_zero]
  exact _root_.meromorphicOrderAt_eq_top_iff.2 (Eventually.of_forall fun _ ↦ rfl)

/-- The zero `1`-form is meromorphic. -/
@[simp]
theorem meromorphicAt_zero (x : X) : (0 : OneForm X).MeromorphicAt x :=
  (holomorphicAt_zero x).meromorphicAt

theorem MeromorphicAt.add (hω : ω.MeromorphicAt x) (hη : η.MeromorphicAt x) :
    (ω + η).MeromorphicAt x :=
  _root_.MeromorphicAt.add hω hη

theorem MeromorphicAt.neg (hω : ω.MeromorphicAt x) : (-ω).MeromorphicAt x :=
  _root_.MeromorphicAt.neg hω

theorem MeromorphicAt.sub (hω : ω.MeromorphicAt x) (hη : η.MeromorphicAt x) :
    (ω - η).MeromorphicAt x :=
  _root_.MeromorphicAt.sub hω hη

theorem MeromorphicAt.const_smul (hω : ω.MeromorphicAt x) (c : ℂ) : (c • ω).MeromorphicAt x :=
  _root_.MeromorphicAt.const_smul hω c

/-- A meromorphic function times a meromorphic `1`-form is meromorphic. -/
theorem MeromorphicAt.smul {f : X → ℂ} (hf : RiemannSurface.MeromorphicAt f x)
    (hω : ω.MeromorphicAt x) : (f • ω).MeromorphicAt x := by
  rw [meromorphicAt_def, coeff_smul]
  exact ((RiemannSurface.meromorphicAt_def f x).1 hf).mul hω

theorem HolomorphicAt.add (hω : ω.HolomorphicAt x) (hη : η.HolomorphicAt x) :
    (ω + η).HolomorphicAt x :=
  AnalyticAt.add hω hη

theorem HolomorphicAt.neg (hω : ω.HolomorphicAt x) : (-ω).HolomorphicAt x :=
  AnalyticAt.neg hω

theorem HolomorphicAt.sub (hω : ω.HolomorphicAt x) (hη : η.HolomorphicAt x) :
    (ω - η).HolomorphicAt x :=
  AnalyticAt.sub hω hη

theorem HolomorphicAt.const_smul (hω : ω.HolomorphicAt x) (c : ℂ) :
    (c • ω).HolomorphicAt x := by
  rw [holomorphicAt_def, coeff_const_smul]
  exact AnalyticAt.const_smul hω

/-- The order of a sum of meromorphic `1`-forms is at least the minimum of their orders. -/
theorem order_add (hω : ω.MeromorphicAt x) (hη : η.MeromorphicAt x) :
    min (ω.order x) (η.order x) ≤ (ω + η).order x :=
  _root_.meromorphicOrderAt_add hω hη

/-- Negation does not change the order. -/
@[simp]
theorem order_neg : (-ω).order x = ω.order x :=
  (_root_.meromorphicOrderAt_neg).symm

/-- Multiplying by a nonzero constant does not change the order. -/
theorem order_const_smul {c : ℂ} (hc : c ≠ 0) : (c • ω).order x = ω.order x :=
  _root_.meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hc

/-- **`ord_x (f ω) = ord_x f + ord_x ω`.** The order of a meromorphic function times a meromorphic
`1`-form is the sum of their orders. -/
theorem order_smul {f : X → ℂ} (hf : RiemannSurface.MeromorphicAt f x) (hω : ω.MeromorphicAt x) :
    (f • ω).order x = RiemannSurface.meromorphicOrderAt f x + ω.order x := by
  rw [order_def, coeff_smul,
    _root_.meromorphicOrderAt_mul ((RiemannSurface.meromorphicAt_def f x).1 hf) hω,
    RiemannSurface.meromorphicOrderAt_def, order_def]

variable (X) in
/-- The complex vector space of **holomorphic `1`-forms** on a Riemann surface. -/
def _root_.TauCeti.RiemannSurface.holomorphicOneForms : Submodule ℂ (OneForm X) where
  carrier := {ω | ∀ x, ω.HolomorphicAt x}
  zero_mem' := holomorphicAt_zero
  add_mem' hω hη x := (hω x).add (hη x)
  smul_mem' c _ hω x := (hω x).const_smul c

@[simp]
theorem _root_.TauCeti.RiemannSurface.mem_holomorphicOneForms :
    ω ∈ holomorphicOneForms X ↔ ∀ x, ω.HolomorphicAt x :=
  Iff.rfl

end Algebra

/-! ### The differential of a function -/

section Differential

variable {f : X → ℂ} {x : X}

/-- **The coefficient of `df`** in a chart is the derivative of the chart representative of `f`. -/
theorem coeff_mvfderiv (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) {z : ℂ} (hz : z ∈ e.target)
    (hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (e.symm z)) :
    coeff (mvfderiv 𝓘(ℂ) f) e z = deriv (f ∘ e.symm) z := by
  rw [coeff, ← mvfderiv_comp_apply z hf (mdifferentiableAt_symm_of_mem_maximalAtlas he hz),
    mvfderiv_eq_fderiv]
  simp [fderiv_eq_smul_deriv]

variable [IsManifold 𝓘(ℂ) 1 X]

/-- Near a point where `f` is meromorphic, the coefficient of `df` in the chart at that point is
the derivative of the chart representative of `f`, away from the point itself. -/
private theorem coeff_mvfderiv_eventuallyEq (hf : RiemannSurface.MeromorphicAt f x) :
    coeff (mvfderiv 𝓘(ℂ) f) (chartAt ℂ x) =ᶠ[𝓝[≠] (chartAt ℂ x x)]
      deriv (f ∘ (chartAt ℂ x).symm) := by
  rw [RiemannSurface.meromorphicAt_def] at hf
  filter_upwards [hf.eventually_analyticAt, nhdsWithin_le_nhds ((chartAt ℂ x).open_target.mem_nhds
    ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))] with z hz hzt
  exact coeff_mvfderiv (chart_mem_maximalAtlas x) hzt
    (TauCeti.mdifferentiableAt_symm_of_differentiableAt_comp (chart_mem_maximalAtlas x) hzt
      hz.differentiableAt)

/-- Near a point where `f` is holomorphic, the coefficient of `df` in the chart at that point is
the derivative of the chart representative of `f`. -/
private theorem coeff_mvfderiv_eventuallyEq_nhds
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    coeff (mvfderiv 𝓘(ℂ) f) (chartAt ℂ x) =ᶠ[𝓝 (chartAt ℂ x x)]
      deriv (f ∘ (chartAt ℂ x).symm) := by
  have hcx := mem_chart_source ℂ x
  filter_upwards [(chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hcx),
    ((chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hcx)).eventually
      (by rwa [(chartAt ℂ x).left_inv hcx])] with z hzt hz
  exact coeff_mvfderiv (chart_mem_maximalAtlas x) hzt hz

/-- The differential of a meromorphic function is a meromorphic `1`-form. -/
theorem meromorphicAt_mvfderiv (hf : RiemannSurface.MeromorphicAt f x) :
    MeromorphicAt (mvfderiv 𝓘(ℂ) f) x :=
  ((RiemannSurface.meromorphicAt_def f x).1 hf).deriv.congr
    (coeff_mvfderiv_eventuallyEq hf).symm

/-- The differential of a holomorphic function is a holomorphic `1`-form. -/
theorem holomorphicAt_mvfderiv (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    HolomorphicAt (mvfderiv 𝓘(ℂ) f) x :=
  (TauCeti.analyticAt_comp_chartAt_symm hf).deriv.congr
    (coeff_mvfderiv_eventuallyEq_nhds hf).symm

/-- **`ord_x df = ord_x f - 1`** at a point where `f` has nonzero finite order, that is, at a zero
or a pole of `f`. -/
theorem order_mvfderiv {n : ℤ} (hn : n ≠ 0) (hf : RiemannSurface.meromorphicOrderAt f x = n) :
    order (mvfderiv 𝓘(ℂ) f) x = ↑(n - 1) := by
  have hm : RiemannSurface.MeromorphicAt f x := by
    rw [RiemannSurface.meromorphicAt_def]
    refine _root_.meromorphicAt_of_meromorphicOrderAt_ne_zero ?_
    rw [← RiemannSurface.meromorphicOrderAt_def, hf]
    exact_mod_cast hn
  rw [order_def, _root_.meromorphicOrderAt_congr (coeff_mvfderiv_eventuallyEq hm)]
  exact _root_.meromorphicOrderAt_deriv_eq_sub_one (by exact_mod_cast hn)
    ((RiemannSurface.meromorphicOrderAt_def f x).symm.trans hf)

/-- **`df` and ramification.** If `f` is holomorphic and nonconstant near `x`, the order of `df` at
`x` is one less than the local multiplicity of `f` at `x`. In particular `df` vanishes exactly at
the ramification points of `f`. -/
theorem order_mvfderiv_eq_localMultiplicity_sub_one
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) (hnc : ¬ EventuallyConst f (𝓝 x)) :
    order (mvfderiv 𝓘(ℂ) f) x = ((localMultiplicity f x : ℤ) - 1 : ℤ) := by
  set g : ℂ → ℂ := fun z ↦ f ((chartAt ℂ x).symm z) - f x
  have hg : AnalyticAt ℂ g (chartAt ℂ x x) :=
    (TauCeti.analyticAt_comp_chartAt_symm hf).sub analyticAt_const
  have hmult := natCast_localMultiplicity hf hnc
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq] at hmult
  have hord : _root_.meromorphicOrderAt g (chartAt ℂ x x) = (localMultiplicity f x : ℤ) := by
    rw [hg.meromorphicOrderAt_eq, ← hmult]
    rfl
  have hpos : (localMultiplicity f x : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.1 ((localMultiplicity_pos_iff hf).2 hnc))
  have hderiv : deriv g = deriv (f ∘ (chartAt ℂ x).symm) := by
    funext z
    exact deriv_sub_const (f x)
  rw [order_def, _root_.meromorphicOrderAt_congr
    ((coeff_mvfderiv_eventuallyEq_nhds hf).filter_mono nhdsWithin_le_nhds), ← hderiv]
  exact _root_.meromorphicOrderAt_deriv_eq_sub_one (by exact_mod_cast hpos) hord

end Differential

/-- The coordinate differential `dz` on `ℂ` is a holomorphic `1`-form. -/
example (x : ℂ) : HolomorphicAt (mvfderiv 𝓘(ℂ) (id : ℂ → ℂ)) x :=
  holomorphicAt_mvfderiv (Eventually.of_forall fun _ ↦ mdifferentiableAt_id)

end OneForm

end TauCeti.RiemannSurface

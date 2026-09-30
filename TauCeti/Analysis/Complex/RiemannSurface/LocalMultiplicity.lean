/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Chart
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Data.ENat.Monoid
import TauCeti.Analysis.Analytic.Order

/-!
# The local multiplicity of a holomorphic map between Riemann surfaces

Let `f : X → Y` be a map between Riemann surfaces, that is, complex manifolds modelled on `ℂ`, and
let `x : X`. Reading `f` in a chart `e` at `x` and a chart `e'` at `f x` gives the function
`e' ∘ f ∘ e.symm` of one complex variable, and the *local multiplicity* of `f` at `x` is the
order of vanishing of `e' ∘ f ∘ e.symm - e' (f x)` at `e x`, computed with Mathlib's
`analyticOrderNatAt`. This file defines `TauCeti.RiemannSurface.localMultiplicity` using the
preferred charts `chartAt ℂ x` and `chartAt ℂ (f x)`, and proves that any two charts of the
maximal atlases give the same value when `f` is holomorphic near `x`
(`TauCeti.RiemannSurface.localMultiplicity_eq_analyticOrderNatAt`). Chart independence makes the
local multiplicity an invariant of the map rather than of the coordinates used to read it, so it
may be computed in whichever charts are convenient; every result below is obtained by choosing
suitable charts.

For a map holomorphic near `x`, the local multiplicity vanishes exactly when `f` is constant
near `x`, and otherwise it is positive; it multiplies under composition; and it equals `1`
exactly when `f` is injective on a neighbourhood of `x`, so that a holomorphic map is a local
biholomorphism precisely at its points of multiplicity one. On the model space `ℂ` the local
multiplicity is the order of vanishing of `f - f z` at `z`, and the power map `z ↦ z ^ m` has
local multiplicity `m` at the origin.

For a map holomorphic and nonconstant near `x`, the local multiplicity `m ≥ 1` is the
ramification index of the map at `x`: near such a point the map is `z ↦ z ^ m` in suitable
coordinates, and the degree of a nonconstant holomorphic map between compact connected Riemann
surfaces is the sum of the local multiplicities over any fibre. Neither the local normal form nor
the degree is part of this file.

## Main declarations

* `TauCeti.RiemannSurface.localMultiplicity`: the local multiplicity of `f : X → Y` at `x`.
* `TauCeti.RiemannSurface.localMultiplicity_eq_analyticOrderNatAt`: it may be computed in any
  charts of the maximal atlases at `x` and `f x`.
* `TauCeti.RiemannSurface.localMultiplicity_eq_zero_iff` and
  `TauCeti.RiemannSurface.localMultiplicity_pos_iff`: it vanishes exactly at points near which
  `f` is constant; in particular a constant map has local multiplicity `0`
  (`TauCeti.RiemannSurface.localMultiplicity_const`).
* `TauCeti.RiemannSurface.localMultiplicity_comp_of_eventually_mdifferentiableAt`: it multiplies
  under composition.
* `TauCeti.RiemannSurface.localMultiplicity_eq_one_iff`: it is `1` exactly when `f` is
  injective near `x`.
* `TauCeti.RiemannSurface.localMultiplicity_pow_zero`: the power map `z ↦ z ^ m` has local
  multiplicity `m` at `0`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §2 and §4.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4.
-/

public noncomputable section

open Filter Function IsManifold Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X Y Z : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
  [ChartedSpace ℂ Y] [TopologicalSpace Z] [ChartedSpace ℂ Z] {f : X → Y} {x : X}

/-! ### The local multiplicity -/

/-- The **local multiplicity** of a map `f : X → Y` between Riemann surfaces at `x`: the order of
vanishing at `chartAt ℂ x x` of `f` read in the charts at `x` and `f x`, recentred at `f x`.

For `f` holomorphic near `x` this does not depend on the charts
(`TauCeti.RiemannSurface.localMultiplicity_eq_analyticOrderNatAt`) and vanishes exactly when `f`
is constant near `x` (`TauCeti.RiemannSurface.localMultiplicity_eq_zero_iff`). If `f` is not
holomorphic near `x`, the value is junk, as for `analyticOrderNatAt`. -/
def localMultiplicity (f : X → Y) (x : X) : ℕ :=
  analyticOrderNatAt
    (fun z ↦ chartAt ℂ (f x) (f ((chartAt ℂ x).symm z)) - chartAt ℂ (f x) (f x)) (chartAt ℂ x x)

theorem localMultiplicity_def (f : X → Y) (x : X) :
    localMultiplicity f x = analyticOrderNatAt
      (fun z ↦ chartAt ℂ (f x) (f ((chartAt ℂ x).symm z)) - chartAt ℂ (f x) (f x))
      (chartAt ℂ x x) :=
  (rfl)

/-- Two maps that agree near `x` have the same local multiplicity at `x`. -/
theorem localMultiplicity_congr {g : X → Y} (h : f =ᶠ[𝓝 x] g) :
    localMultiplicity f x = localMultiplicity g x := by
  have hx : f x = g x := h.self_of_nhds
  simp only [localMultiplicity_def, analyticOrderNatAt, hx]
  congr 1
  refine analyticOrderAt_congr ?_
  filter_upwards [((chartAt ℂ x).tendsto_symm (mem_chart_source ℂ x)).eventually h] with z hz
  simp only [hz]

/-- A map that is constant near `x` has local multiplicity `0` at `x`. -/
theorem localMultiplicity_eq_zero_of_eventuallyConst (h : EventuallyConst f (𝓝 x)) :
    localMultiplicity f x = 0 := by
  have hc : EventuallyConst (fun z ↦ chartAt ℂ (f x) (f ((chartAt ℂ x).symm z)))
      (𝓝 (chartAt ℂ x x)) :=
    (h.comp_tendsto ((chartAt ℂ x).tendsto_symm (mem_chart_source ℂ x))).comp (chartAt ℂ (f x))
  rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top] at hc
  simp only [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at hc
  rw [localMultiplicity_def, analyticOrderNatAt, hc, ENat.toNat_top]

/-- A constant map has local multiplicity `0` everywhere. -/
@[simp]
theorem localMultiplicity_const (y : Y) (x : X) : localMultiplicity (fun _ ↦ y) x = 0 :=
  localMultiplicity_eq_zero_of_eventuallyConst (.const y)

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y] [IsManifold 𝓘(ℂ) 1 Z]

/-- **Chart independence of the local multiplicity.** For a map holomorphic near `x`, the local
multiplicity is the order of vanishing of the recentred chart representative of `f` in any
charts of the maximal atlases at `x` and `f x`. -/
theorem localMultiplicity_eq_analyticOrderNatAt {e : OpenPartialHomeomorph X ℂ}
    {e' : OpenPartialHomeomorph Y ℂ} (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X)
    (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Y) (hx : x ∈ e.source) (hfx : f x ∈ e'.source)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    localMultiplicity f x = analyticOrderNatAt (fun z ↦ e' (f (e.symm z)) - e' (f x)) (e x) := by
  -- A transition map between charts of the maximal atlas is a holomorphic injection of an open
  -- set, so its derivative vanishes nowhere (`deriv_symm_trans_ne_zero`); Mathlib's
  -- `analyticOrderAt_comp_of_deriv_ne_zero` and `AnalyticAt.analyticOrderAt_comp` then show that
  -- reparametrising the source or the target leaves the order unchanged.
  rw [localMultiplicity_def]
  set c := chartAt ℂ x
  set c' := chartAt ℂ (f x)
  have hcx : x ∈ c.source := mem_chart_source ℂ x
  have hc'fx : f x ∈ c'.source := mem_chart_source ℂ (f x)
  -- The representative `F` of `f` in the preferred charts, and the two transition maps `g`
  -- (in the source) and `ψ` (in the target).
  set F : ℂ → ℂ := fun z ↦ c' (f (c.symm z)) with hF
  set g : ℂ → ℂ := c ∘ e.symm with hg
  set ψ : ℂ → ℂ := e' ∘ c'.symm with hψ
  have hFa : AnalyticAt ℂ F (c x) := analyticAt_chartAt_comp_comp_chartAt_symm hf
  have hFcx : F (c x) = c' (f x) := by simp [hF, c.left_inv hcx]
  have hga : AnalyticAt ℂ g (e x) := analyticAt_symm_trans he (chart_mem_maximalAtlas x) hx hcx
  have hg' : deriv g (e x) ≠ 0 := deriv_symm_trans_ne_zero he (chart_mem_maximalAtlas x) hx hcx
  have hgx : g (e x) = c x := by simp [hg, e.left_inv hx]
  have hψa : AnalyticAt ℂ ψ (c' (f x)) :=
    analyticAt_symm_trans (chart_mem_maximalAtlas (f x)) he' hc'fx hfx
  have hψ' : deriv ψ (c' (f x)) ≠ 0 :=
    deriv_symm_trans_ne_zero (chart_mem_maximalAtlas (f x)) he' hc'fx hfx
  have hψs : AnalyticAt ℂ (fun w ↦ ψ w - ψ (c' (f x))) (F (c x)) := by
    rw [hFcx]
    exact hψa.sub analyticAt_const
  -- Near `e x`, the representative of `f` in the charts `e` and `e'` is `ψ ∘ F ∘ g`, recentred.
  have hcont : Tendsto (fun z ↦ f (e.symm z)) (𝓝 (e x)) (𝓝 (f x)) :=
    hf.self_of_nhds.continuousAt.tendsto.comp (e.tendsto_symm hx)
  have heq : (fun z ↦ e' (f (e.symm z)) - e' (f x)) =ᶠ[𝓝 (e x)]
      ((fun w ↦ ψ w - ψ (c' (f x))) ∘ F) ∘ g := by
    filter_upwards [(e.tendsto_symm hx).eventually (c.open_source.mem_nhds hcx),
      hcont.eventually (c'.open_source.mem_nhds hc'fx)] with z hz hz'
    simp [hF, hg, hψ, c.left_inv hz, c'.left_inv hz', c'.left_inv hc'fx]
  have key : analyticOrderAt (fun z ↦ e' (f (e.symm z)) - e' (f x)) (e x) =
      analyticOrderAt (fun z ↦ F z - c' (f x)) (c x) := by
    calc analyticOrderAt (fun z ↦ e' (f (e.symm z)) - e' (f x)) (e x)
        = analyticOrderAt (((fun w ↦ ψ w - ψ (c' (f x))) ∘ F) ∘ g) (e x) :=
          analyticOrderAt_congr heq
      _ = analyticOrderAt ((fun w ↦ ψ w - ψ (c' (f x))) ∘ F) (g (e x)) :=
          analyticOrderAt_comp_of_deriv_ne_zero hga hg'
      _ = analyticOrderAt (fun w ↦ ψ w - ψ (c' (f x))) (F (c x)) *
            analyticOrderAt (fun z ↦ F z - F (c x)) (c x) := by
          rw [hgx, hψs.analyticOrderAt_comp hFa]
      _ = analyticOrderAt (fun z ↦ F z - c' (f x)) (c x) := by
          rw [hFcx, hψa.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hψ', one_mul]
  rw [analyticOrderNatAt, analyticOrderNatAt, key]

/-! ### Vanishing and positivity -/

/-- For a map holomorphic near `x`, the local multiplicity at `x` vanishes exactly when the map
is constant near `x`. -/
theorem localMultiplicity_eq_zero_iff (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    localMultiplicity f x = 0 ↔ EventuallyConst f (𝓝 x) := by
  refine ⟨fun h ↦ ?_, localMultiplicity_eq_zero_of_eventuallyConst⟩
  rw [localMultiplicity_def, analyticOrderNatAt, ENat.toNat_eq_zero] at h
  set c := chartAt ℂ x
  set c' := chartAt ℂ (f x)
  have hcx : x ∈ c.source := mem_chart_source ℂ x
  have hc'fx : f x ∈ c'.source := mem_chart_source ℂ (f x)
  have hFs : AnalyticAt ℂ (fun z ↦ c' (f (c.symm z)) - c' (f x)) (c x) :=
    (analyticAt_chartAt_comp_comp_chartAt_symm hf).sub analyticAt_const
  -- The recentred representative vanishes at `c x`, so its order is nonzero, and it has
  -- infinite order exactly when the representative is constant near `c x`.
  have hne : analyticOrderAt (fun z ↦ c' (f (c.symm z)) - c' (f x)) (c x) ≠ 0 := by
    rw [hFs.analyticOrderAt_ne_zero, c.left_inv hcx, sub_self]
  have htop : EventuallyConst (fun z ↦ c' (f (c.symm z))) (𝓝 (c x)) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top]
    simpa only [c.left_inv hcx] using h.resolve_left hne
  -- `f` agrees near `x` with `c'.symm ∘ (c' ∘ f ∘ c.symm) ∘ c`.
  refine ((htop.comp_tendsto (c.continuousAt hcx)).comp c'.symm).congr ?_
  filter_upwards [c.open_source.mem_nhds hcx,
    hf.self_of_nhds.continuousAt.eventually (c'.open_source.mem_nhds hc'fx)] with y hy hy'
  simp [c.left_inv hy, c'.left_inv hy']

/-- For a map holomorphic near `x`, the local multiplicity at `x` is positive exactly when the
map is not constant near `x`. -/
theorem localMultiplicity_pos_iff (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    0 < localMultiplicity f x ↔ ¬ EventuallyConst f (𝓝 x) := by
  rw [Nat.pos_iff_ne_zero, not_iff_not, localMultiplicity_eq_zero_iff hf]

/-- For a map holomorphic and nonconstant near `x`, the local multiplicity is the order of
vanishing, in `ℕ∞`, of the recentred chart representative in the charts at `x` and `f x`. -/
theorem natCast_localMultiplicity (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y)
    (hne : ¬ EventuallyConst f (𝓝 x)) :
    (localMultiplicity f x : ℕ∞) = analyticOrderAt
      (fun z ↦ chartAt ℂ (f x) (f ((chartAt ℂ x).symm z)) - chartAt ℂ (f x) (f x))
      (chartAt ℂ x x) := by
  rw [localMultiplicity_def]
  refine Nat.cast_analyticOrderNatAt fun htop ↦ hne ?_
  rw [← localMultiplicity_eq_zero_iff hf, localMultiplicity_def, analyticOrderNatAt, htop,
    ENat.toNat_top]

/-! ### Composition -/

/-- **Multiplicativity of the local multiplicity.** The local multiplicity of a composition of
maps holomorphic near the relevant points is the product of the local multiplicities. -/
theorem localMultiplicity_comp_of_eventually_mdifferentiableAt {g : Y → Z}
    (hg : ∀ᶠ y in 𝓝 (f x), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g y)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    localMultiplicity (g ∘ f) x = localMultiplicity g (f x) * localMultiplicity f x := by
  simp only [localMultiplicity_def, comp_apply]
  set c := chartAt ℂ x
  set c' := chartAt ℂ (f x)
  set c'' := chartAt ℂ (g (f x))
  have hcx : x ∈ c.source := mem_chart_source ℂ x
  have hc'fx : f x ∈ c'.source := mem_chart_source ℂ (f x)
  have hFa : AnalyticAt ℂ (fun z ↦ c' (f (c.symm z))) (c x) :=
    analyticAt_chartAt_comp_comp_chartAt_symm hf
  -- The representative of `g` is analytic at `c' (f x)`; it is stated at the unsimplified point
  -- `c' (f (c.symm (c x)))`, the value at `c x` of the representative of `f`, so that
  -- `AnalyticAt.analyticOrderAt_comp` below unifies without rewriting the goal.
  have hGa : AnalyticAt ℂ (fun w ↦ c'' (g (c'.symm w)) - c'' (g (f x)))
      (c' (f (c.symm (c x)))) := by
    rw [c.left_inv hcx]
    exact (analyticAt_chartAt_comp_comp_chartAt_symm hg).sub analyticAt_const
  have hcont : Tendsto (fun z ↦ f (c.symm z)) (𝓝 (c x)) (𝓝 (f x)) :=
    hf.self_of_nhds.continuousAt.tendsto.comp (c.tendsto_symm hcx)
  -- The representative of `g ∘ f` is the composition of the representatives of `g` and `f`.
  have heq : (fun z ↦ c'' (g (f (c.symm z))) - c'' (g (f x))) =ᶠ[𝓝 (c x)]
      (fun w ↦ c'' (g (c'.symm w)) - c'' (g (f x))) ∘ fun z ↦ c' (f (c.symm z)) := by
    filter_upwards [hcont.eventually (c'.open_source.mem_nhds hc'fx)] with z hz
    simp [c'.left_inv hz]
  rw [analyticOrderNatAt, analyticOrderNatAt, analyticOrderNatAt, analyticOrderAt_congr heq,
    hGa.analyticOrderAt_comp hFa, ENat.toNat_mul]
  simp only [c.left_inv hcx]

/-! ### Multiplicity one -/

/-- **Multiplicity one means local injectivity.** A map holomorphic near `x` has local
multiplicity `1` at `x` exactly when it is injective on a neighbourhood of `x`; by the inverse
function theorem, these are the points at which it is a local biholomorphism. -/
theorem localMultiplicity_eq_one_iff (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    localMultiplicity f x = 1 ↔ ∃ U ∈ 𝓝 x, InjOn f U := by
  rw [localMultiplicity_def]
  set c := chartAt ℂ x
  set c' := chartAt ℂ (f x)
  have hcx : x ∈ c.source := mem_chart_source ℂ x
  have hc'fx : f x ∈ c'.source := mem_chart_source ℂ (f x)
  have hFa : AnalyticAt ℂ (fun z ↦ c' (f (c.symm z))) (c x) :=
    analyticAt_chartAt_comp_comp_chartAt_symm hf
  -- The recentred representative has order `1` exactly when the derivative of the
  -- representative does not vanish, that is, exactly when the representative is injective near
  -- `c x`.
  have h1 : analyticOrderNatAt (fun z ↦ c' (f (c.symm z)) - c' (f x)) (c x) = 1 ↔
      ∃ V ∈ 𝓝 (c x), InjOn (fun z ↦ c' (f (c.symm z))) V := by
    rw [analyticOrderNatAt, ENat.toNat_eq_iff one_ne_zero, Nat.cast_one]
    simpa only [c.left_inv hcx] using hFa.analyticOrderAt_sub_eq_one_iff_deriv_ne_zero.trans
      (exists_injOn_nhds_iff_deriv_ne_zero hFa).symm
  rw [h1]
  constructor
  · rintro ⟨V, hV, hinj⟩
    refine ⟨c.source ∩ c ⁻¹' V, inter_mem (c.open_source.mem_nhds hcx)
      ((c.continuousAt hcx).preimage_mem_nhds hV), fun x₁ hx₁ x₂ hx₂ h ↦ ?_⟩
    refine c.injOn hx₁.1 hx₂.1 (hinj hx₁.2 hx₂.2 ?_)
    simp [c.left_inv hx₁.1, c.left_inv hx₂.1, h]
  · rintro ⟨U, hU, hinj⟩
    refine ⟨c.target ∩ c.symm ⁻¹' U ∩ (fun z ↦ f (c.symm z)) ⁻¹' c'.source,
      inter_mem (inter_mem (c.open_target.mem_nhds (c.map_source hcx))
        ((c.tendsto_symm hcx).eventually hU))
        ((hf.self_of_nhds.continuousAt.tendsto.comp (c.tendsto_symm hcx)).eventually
          (c'.open_source.mem_nhds hc'fx)),
      fun z₁ hz₁ z₂ hz₂ h ↦ ?_⟩
    exact c.symm.injOn hz₁.1.1 hz₂.1.1 (hinj hz₁.1.2 hz₂.1.2 (c'.injOn hz₁.2 hz₂.2 h))

/-- The identity has local multiplicity `1` everywhere. -/
@[simp]
theorem localMultiplicity_id (x : X) : localMultiplicity (id : X → X) x = 1 :=
  (localMultiplicity_eq_one_iff (.of_forall fun _ ↦ mdifferentiableAt_id)).2
    ⟨univ, univ_mem, injective_id.injOn⟩

/-- A chart of the maximal atlas has local multiplicity `1` at every point of its domain. -/
theorem localMultiplicity_eq_one_of_mem_maximalAtlas {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (hx : x ∈ e.source) : localMultiplicity e x = 1 :=
  (localMultiplicity_eq_one_iff ((e.open_source.eventually_mem hx).mono fun _ hy ↦
    (contMDiffAt_of_mem_maximalAtlas he hy).mdifferentiableAt one_ne_zero)).2
    ⟨e.source, e.open_source.mem_nhds hx, e.injOn⟩

/-! ### The model space -/

/-- On the model space `ℂ`, the local multiplicity of `f` at `z` is the order of vanishing of
`f - f z` at `z`. -/
@[simp]
theorem localMultiplicity_eq_analyticOrderNatAt_sub (f : ℂ → ℂ) (z : ℂ) :
    localMultiplicity f z = analyticOrderNatAt (fun w ↦ f w - f z) z := by
  simp [localMultiplicity_def, chartAt_self_eq, OpenPartialHomeomorph.refl_symm]

/-- The power map `z ↦ z ^ m` has local multiplicity `m` at the origin. -/
theorem localMultiplicity_pow_zero (m : ℕ) : localMultiplicity (fun z : ℂ ↦ z ^ m) 0 = m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [localMultiplicity_eq_analyticOrderNatAt_sub, analyticOrderNatAt,
      analyticOrderAt_pow_sub_zero_pow hm, ENat.toNat_natCast]

/-- If a holomorphic map has coordinate expression `z ↦ z ^ m` in charts that send the source
point and its image to zero, then its local multiplicity is `m`. -/
theorem localMultiplicity_eq_of_coordinate_eventuallyEq_pow_zero
    {e : OpenPartialHomeomorph X ℂ} {e' : OpenPartialHomeomorph Y ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Y)
    (hx : x ∈ e.source) (hfx : f x ∈ e'.source)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y)
    {m : ℕ} (hm : 0 < m) (hex : e x = 0) (hefx : e' (f x) = 0)
    (hpow : (fun z ↦ e' (f (e.symm z))) =ᶠ[𝓝 0] fun z : ℂ ↦ z ^ m) :
    localMultiplicity f x = m := by
  rw [localMultiplicity_eq_analyticOrderNatAt he he' hx hfx hf, hex, hefx]
  have hsub : (fun z ↦ e' (f (e.symm z)) - 0) =ᶠ[𝓝 0]
      fun z : ℂ ↦ z ^ m - 0 ^ m := by
    filter_upwards [hpow] with z hz
    simp [hz, hm.ne']
  calc
    analyticOrderNatAt (fun z ↦ e' (f (e.symm z)) - 0) 0 =
        analyticOrderNatAt (fun z : ℂ ↦ z ^ m - 0 ^ m) 0 :=
      TauCeti.analyticOrderNatAt_congr hsub
    _ = localMultiplicity (fun z : ℂ ↦ z ^ m) 0 := by
      rw [localMultiplicity_eq_analyticOrderNatAt_sub]
    _ = m := localMultiplicity_pow_zero m

end TauCeti.RiemannSurface

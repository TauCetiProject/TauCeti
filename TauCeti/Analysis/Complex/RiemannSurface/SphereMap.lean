/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Degree
public import TauCeti.Analysis.Complex.RiemannSurface.Meromorphic
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import TauCeti.Geometry.Manifold.ChartedSpace
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# Meromorphic functions as holomorphic maps to the Riemann sphere

A meromorphic function `f : X → ℂ` on a Riemann surface `X` is the same thing as a holomorphic map
`X → OnePoint ℂ` to the Riemann sphere which is not identically `∞`. This file constructs the
forward direction. The map `TauCeti.RiemannSurface.sphereMap f` sends `x` to the limit of `f y` in
`OnePoint ℂ` as `y` tends to `x` with `y ≠ x`. Thus it agrees with `f` at every point where `f` is
continuous (`TauCeti.RiemannSurface.sphereMap_of_continuousAt`). For a meromorphic `f` it is `∞`
exactly at the poles (`TauCeti.RiemannSurface.sphereMap_eq_infty_iff`). At a removable
singularity it takes the limiting value, whatever value `f` itself was given there
(`TauCeti.RiemannSurface.sphereMap_eq_coe_iff`).

Holomorphy is checked in the two charts of the sphere
(`TauCeti.RiemannSurface.mdifferentiableAt_sphereMap`). Away from the poles, the map read in the
affine chart is the normal form of `f`, which is holomorphic by the removable singularity theorem.
At a pole, it is read in the inverted chart as the normal form of the reciprocal `1 / f`. That
function vanishes at the pole and is again holomorphic there.

On a compact connected Riemann surface, a meromorphic function which is not constant near some
point therefore gives a finite holomorphic map to the sphere
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.ofMeromorphic`), with finite fibres. This is the
route from the existence of nonconstant meromorphic functions, as produced by the Riemann–Roch
theorem, to the degree theory of finite holomorphic maps.

## Main declarations

* `TauCeti.RiemannSurface.sphereMap`: the map to the Riemann sphere defined by `f : X → ℂ`.
* `TauCeti.RiemannSurface.sphereMap_of_continuousAt`,
  `TauCeti.RiemannSurface.eventually_sphereMap_eq`, `TauCeti.RiemannSurface.sphereMap_eq_coe_iff`
  and `TauCeti.RiemannSurface.sphereMap_eq_infty_iff`: its values.
* `TauCeti.RiemannSurface.mdifferentiableAt_sphereMap` and
  `TauCeti.RiemannSurface.mdifferentiable_sphereMap`: it is holomorphic when `f` is meromorphic.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.ofMeromorphic`: the finite holomorphic map to the
  sphere defined by a meromorphic function which is not constant near some point, on a compact
  connected Riemann surface.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §1, Theorem 1.15.
-/

public noncomputable section

open Filter Function OnePoint Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X : Type*} [TopologicalSpace X] {f : X → ℂ} {x : X}

/-- The map to the Riemann sphere `OnePoint ℂ` defined by a function `f : X → ℂ`, typically on a
Riemann surface: its value at `x` is the limit of `f y` in `OnePoint ℂ` as `y` tends to `x` with
`y ≠ x`. It agrees with `f` wherever `f` is continuous
(`TauCeti.RiemannSurface.sphereMap_of_continuousAt`). When `f` is meromorphic it is `∞` exactly
at the poles of `f` (`TauCeti.RiemannSurface.sphereMap_eq_infty_iff`), and it is holomorphic
(`TauCeti.RiemannSurface.mdifferentiable_sphereMap`). Where the limit does not exist, the value
is junk. -/
def sphereMap (f : X → ℂ) (x : X) : OnePoint ℂ :=
  limUnder (𝓝[≠] x) fun y ↦ (f y : OnePoint ℂ)

theorem sphereMap_def (f : X → ℂ) (x : X) :
    sphereMap f x = limUnder (𝓝[≠] x) fun y ↦ (f y : OnePoint ℂ) :=
  (rfl)

/-! ### Values -/

variable [ChartedSpace ℂ X]

/-- The value of `sphereMap f` at `x` is any limit of `f` at `x` in the Riemann sphere. -/
theorem sphereMap_eq_of_tendsto {c : OnePoint ℂ}
    (h : Tendsto (fun y ↦ (f y : OnePoint ℂ)) (𝓝[≠] x) (𝓝 c)) : sphereMap f x = c :=
  have := (chartAt ℂ x).nhdsNE_neBot (mem_chart_source ℂ x)
  h.limUnder_eq

/-- The value of `sphereMap f` at `x` is the value at `x` of any map continuous at `x` which agrees
with `f` on a punctured neighbourhood of `x`. -/
theorem sphereMap_eq_of_eventuallyEq {k : X → OnePoint ℂ}
    (h : (fun y ↦ (f y : OnePoint ℂ)) =ᶠ[𝓝[≠] x] k) (hk : ContinuousAt k x) :
    sphereMap f x = k x :=
  sphereMap_eq_of_tendsto ((hk.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

/-- `sphereMap f` agrees with `f` at every point where `f` is continuous. -/
theorem sphereMap_of_continuousAt (hf : ContinuousAt f x) : sphereMap f x = f x :=
  sphereMap_eq_of_tendsto ((continuous_coe.continuousAt.comp hf).tendsto.mono_left
    nhdsWithin_le_nhds)

/-- The map to the sphere defined by a constant function is that constant. -/
@[simp]
theorem sphereMap_const (c : ℂ) : sphereMap (fun _ : X ↦ c) = fun _ ↦ (c : OnePoint ℂ) :=
  funext fun _ ↦ sphereMap_of_continuousAt continuousAt_const

/-- If `f` agrees on a punctured neighbourhood of `x` with a map `k` which is continuous near
`x`, then `sphereMap f` agrees with `k` on a whole neighbourhood of `x`. -/
private theorem sphereMap_eventuallyEq {k : X → OnePoint ℂ}
    (h : (fun y ↦ (f y : OnePoint ℂ)) =ᶠ[𝓝[≠] x] k) (hk : ∀ᶠ y in 𝓝 x, ContinuousAt k y) :
    sphereMap f =ᶠ[𝓝 x] k := by
  have := ChartedSpace.t1Space ℂ X
  have h' : ∀ᶠ y in 𝓝 x, y ≠ x → (f y : OnePoint ℂ) = k y := eventually_nhdsWithin_iff.1 h
  filter_upwards [hk, h'.eventually_nhds] with y hky hy
  rcases eq_or_ne y x with rfl | hyx
  · exact sphereMap_eq_of_eventuallyEq h hky
  · refine sphereMap_eq_of_eventuallyEq ?_ hky
    filter_upwards [nhdsWithin_le_nhds hy, nhdsWithin_le_nhds (isOpen_ne.mem_nhds hyx)] with
      z hz hzx
    exact hz hzx

/-! ### The local picture in one variable -/

/-- A function `g` of one complex variable meromorphic at `z₀` agrees, on a punctured
neighbourhood of `z₀`, with a map to the sphere which is holomorphic near `z₀` and takes the value
`∞` at `z₀` exactly when `g` has a pole there. Away from a pole the map is the normal form of `g`;
at a pole it is the normal form of `1 / g`, read in the inverted chart. -/
private theorem exists_mdifferentiableAt_eventuallyEq {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : _root_.MeromorphicAt g z₀) :
    ∃ Φ : ℂ → OnePoint ℂ, (∀ᶠ w in 𝓝 z₀, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) Φ w) ∧
      (fun w ↦ (g w : OnePoint ℂ)) =ᶠ[𝓝[≠] z₀] Φ ∧
      (Φ z₀ = ∞ ↔ _root_.meromorphicOrderAt g z₀ < 0) := by
  rcases le_or_gt 0 (_root_.meromorphicOrderAt g z₀) with hord | hord
  · -- Away from a pole, the normal form of `g` is holomorphic at `z₀`.
    have han := hg.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.1 hord
    refine ⟨fun w ↦ ((toMeromorphicNFAt g z₀ w : ℂ) : OnePoint ℂ), ?_, ?_, ?_⟩
    · filter_upwards [han.eventually_analyticAt] with w hw
      exact mdifferentiableAt_coe_comp_iff.2
        (mdifferentiableAt_iff_differentiableAt.2 hw.differentiableAt)
    · filter_upwards [hg.eq_nhdsNE_toMeromorphicNFAt] with w hw
      rw [hw]
    · simp [not_lt.2 hord]
  · -- At a pole, the normal form of `1 / g` is holomorphic at `z₀` and vanishes there.
    have hinv : 0 < _root_.meromorphicOrderAt g⁻¹ z₀ := by
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hord.ne_top
      rw [← hn] at hord
      rw [meromorphicOrderAt_inv, ← hn]
      exact_mod_cast neg_pos.2 (WithTop.coe_lt_coe.1 hord)
    have han := hg.inv.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.1 hinv.le
    have hsymm : ∀ w, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (invChart.symm : ℂ → OnePoint ℂ) w := by
      intro w
      rw [← chartAt_infty (𝕜 := ℂ)]
      exact mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ _) (by simp [invChart_target])
    refine ⟨fun w ↦ invChart.symm (toMeromorphicNFAt g⁻¹ z₀ w), ?_, ?_, ?_⟩
    · filter_upwards [han.eventually_analyticAt] with w hw
      exact (hsymm _).comp w (mdifferentiableAt_iff_differentiableAt.2 hw.differentiableAt)
    · filter_upwards [hg.inv.eq_nhdsNE_toMeromorphicNFAt,
        (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hg).1 hord.ne_top] with w hw hw0
      simp [← hw, hw0]
    · simp [hord, toMeromorphicNFAt_of_meromorphicOrderAt_ne_zero hinv.ne']

/-! ### Holomorphy -/

variable [IsManifold 𝓘(ℂ) 1 X]

/-- Near a point where `f` is meromorphic, `sphereMap f` is the composite of the chart with a map
to the sphere which is holomorphic near the coordinate of the point, and `f` agrees with this
composite on a punctured neighbourhood. -/
private theorem exists_eventuallyEq_comp_chartAt (hf : MeromorphicAt f x) :
    ∃ Φ : ℂ → OnePoint ℂ, (∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Φ ∘ chartAt ℂ x) y) ∧
      (fun y ↦ (f y : OnePoint ℂ)) =ᶠ[𝓝[≠] x] Φ ∘ chartAt ℂ x ∧
      sphereMap f =ᶠ[𝓝 x] Φ ∘ chartAt ℂ x ∧
      (Φ (chartAt ℂ x x) = ∞ ↔ meromorphicOrderAt f x < 0) := by
  obtain ⟨Φ, hΦ, heq, hinf⟩ := exists_mdifferentiableAt_eventuallyEq ((meromorphicAt_def f x).1 hf)
  rw [← meromorphicOrderAt_def] at hinf
  have hx := mem_chart_source ℂ x
  have hsource : ∀ᶠ y in 𝓝 x, y ∈ (chartAt ℂ x).source :=
    (chartAt ℂ x).open_source.mem_nhds hx
  have hmd : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Φ ∘ chartAt ℂ x) y := by
    filter_upwards [hsource, ((chartAt ℂ x).continuousAt hx).eventually hΦ] with y hy hΦy
    exact hΦy.comp y (mdifferentiableAt_atlas (chart_mem_atlas ℂ x) hy)
  have hfeq : (fun y ↦ (f y : OnePoint ℂ)) =ᶠ[𝓝[≠] x] Φ ∘ chartAt ℂ x := by
    filter_upwards [nhdsWithin_le_nhds hsource, (tendsto_chartAt_nhdsNE x).eventually heq] with
      y hy hΦy
    simpa [(chartAt ℂ x).left_inv hy] using hΦy
  exact ⟨Φ, hmd, hfeq,
    sphereMap_eventuallyEq hfeq (hmd.mono fun _ h ↦ h.continuousAt), hinf⟩

/-- **Meromorphic functions are holomorphic maps to the Riemann sphere.** If `f` is meromorphic at
`x`, then `sphereMap f` is holomorphic at `x`. -/
theorem mdifferentiableAt_sphereMap (hf : MeromorphicAt f x) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (sphereMap f) x := by
  obtain ⟨Φ, hmd, -, heq, -⟩ := exists_eventuallyEq_comp_chartAt hf
  exact hmd.self_of_nhds.congr_of_eventuallyEq heq

/-- **Meromorphic functions are holomorphic maps to the Riemann sphere.** If `f` is meromorphic at
every point, then `sphereMap f` is holomorphic. -/
theorem mdifferentiable_sphereMap (hf : ∀ x, MeromorphicAt f x) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (sphereMap f) :=
  fun x ↦ mdifferentiableAt_sphereMap (hf x)

/-- Near a point where `f` is meromorphic, `sphereMap f` agrees with `f` away from the point. -/
theorem eventually_sphereMap_eq (hf : MeromorphicAt f x) :
    ∀ᶠ y in 𝓝[≠] x, sphereMap f y = f y := by
  obtain ⟨Φ, -, hfeq, heq, -⟩ := exists_eventuallyEq_comp_chartAt hf
  filter_upwards [hfeq, nhdsWithin_le_nhds heq] with y hy hy'
  rw [hy, hy']

/-- At a point where `f` is meromorphic, `sphereMap f` is `∞` exactly when `f` has a pole. -/
theorem sphereMap_eq_infty_iff (hf : MeromorphicAt f x) :
    sphereMap f x = ∞ ↔ meromorphicOrderAt f x < 0 := by
  obtain ⟨Φ, -, -, heq, hinf⟩ := exists_eventuallyEq_comp_chartAt hf
  rw [heq.self_of_nhds, comp_apply, hinf]

/-- At a point where `f` is meromorphic, `sphereMap f` takes a finite value `c` exactly when `f`
tends to `c` on punctured neighbourhoods of the point. -/
theorem sphereMap_eq_coe_iff (hf : MeromorphicAt f x) {c : ℂ} :
    sphereMap f x = c ↔ Tendsto f (𝓝[≠] x) (𝓝 c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ sphereMap_eq_of_tendsto ((continuous_coe.tendsto c).comp h)⟩
  rw [isOpenEmbedding_coe.isInducing.tendsto_nhds_iff, ← h]
  exact ((mdifferentiableAt_sphereMap hf).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).congr' ((eventually_sphereMap_eq hf).mono fun _ h ↦ h)

/-! ### Finite holomorphic maps to the sphere -/

/-- If `f` is meromorphic and not constant near `x₀`, then `sphereMap f` takes two distinct
values. -/
private theorem exists_sphereMap_ne (hf : ∀ x, MeromorphicAt f x) {x₀ : X}
    (hx₀ : ¬ EventuallyConst f (𝓝[≠] x₀)) : ∃ x x', sphereMap f x ≠ sphereMap f x' := by
  have := (chartAt ℂ x₀).nhdsNE_neBot (mem_chart_source ℂ x₀)
  by_contra! hconst
  obtain ⟨y₀, hy₀⟩ := (eventually_sphereMap_eq (hf x₀)).exists
  refine hx₀ (eventuallyConst_iff_exists_eventuallyEq.2 ⟨f y₀, ?_⟩)
  filter_upwards [eventually_sphereMap_eq (hf x₀)] with y hy
  exact coe_injective (by rw [← hy, ← hy₀, hconst y y₀])

variable [CompactSpace X] [PreconnectedSpace X]

/-- **The finite holomorphic map defined by a meromorphic function.** On a compact connected
Riemann surface, a meromorphic function which is not constant near some point `x₀` defines the
finite holomorphic map `TauCeti.RiemannSurface.sphereMap f` to the Riemann sphere. -/
def FiniteHolomorphicMap.ofMeromorphic (hf : ∀ x, MeromorphicAt f x) {x₀ : X}
    (hx₀ : ¬ EventuallyConst f (𝓝[≠] x₀)) : FiniteHolomorphicMap X (OnePoint ℂ) :=
  .ofMDifferentiable (mdifferentiable_sphereMap hf) (exists_sphereMap_ne hf hx₀)

@[simp]
theorem FiniteHolomorphicMap.coe_ofMeromorphic (hf : ∀ x, MeromorphicAt f x) {x₀ : X}
    (hx₀ : ¬ EventuallyConst f (𝓝[≠] x₀)) : ⇑(FiniteHolomorphicMap.ofMeromorphic hf hx₀) =
      sphereMap f :=
  FiniteHolomorphicMap.coe_ofMDifferentiable _ _

end TauCeti.RiemannSurface

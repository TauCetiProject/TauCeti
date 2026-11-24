/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Scaling
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Curvature
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Einstein metrics as explicit Ricci flows

A family of metrics `g τ = φ(τ) g₀`, a time-dependent constant multiple of a fixed metric `g₀`, has
the Ricci tensor of `g₀` at every time, because constant rescaling does not change the Ricci tensor.
Its time derivative is `φ'(τ) g₀`. Hence it satisfies the Ricci flow equation `∂_τ g = -2 Ric(g)`
when `Ric(g₀) = -(φ'/2) g₀`, that is, when `g₀` is Einstein with constant `-φ'/2`; conversely, at a
time where the time set has unique derivatives (for instance an interior time), the flow equation
forces this Einstein condition.

In particular, if `Ric(g₀) = c g₀` then the Einstein solution
`Bundle.ContMDiffRiemannianMetric.einsteinFlow`, which is `g τ = (1 - 2 c τ) g₀` on its
positive-scale interval `2 c τ < 1` and starts at `g₀`, is a Ricci flow on that interval. For
`c > 0` this interval ends at `T = 1 / (2 c)`, and there the flow dies: its scalar curvature
`Scal(g τ) = n c / (1 - 2 c τ)` tends to `+∞` as `τ → T⁻`, where `n ≥ 1` is the dimension. The
round unit `n`-sphere has `Ric = (n - 1) g`, so its Ricci flow lives for time `1 / (2 (n - 1))`
when `n ≥ 2`. For `φ = 1` the family is constant, and a constant family is a Ricci flow at a time
with unique derivatives exactly when `g₀` is Ricci-flat; in dimension at most one every metric is
Ricci-flat.

The flow equation is stated pointwise, as for
`TauCeti.hasDerivWithinAt_chartVolumeDensity_of_ricciFlow`. The general statements concern any
family known only through its inner products on a time set `s` (for the extinction statement, on
a punctured left neighbourhood of the extinction time), so the factor `φ` need not be positive off
`s`, and the flow equation is a derivative within `s`.

## Main results

* `TauCeti.hasDerivWithinAt_inner_neg_two_mul_ricciTensor_of_inner_eq_smul` and its converse
  `TauCeti.hasDerivWithinAt_inner_neg_two_mul_ricciTensor_iff_of_inner_eq_smul`: `τ ↦ φ(τ) g₀`
  satisfies the Ricci flow equation at `x` at a time `t` where `s` has unique derivatives exactly
  when `Ric(g₀) = -(φ'/2) g₀` at `x`.
* `TauCeti.hasDerivWithinAt_inner_neg_two_mul_ricciTensor_of_inner_eq_one_sub_two_mul_smul` and
  its converse
  `TauCeti.hasDerivWithinAt_inner_neg_two_mul_ricciTensor_iff_of_inner_eq_one_sub_two_mul_smul`: a
  family with `g τ = (1 - 2 c τ) g₀` on `s` is a Ricci flow on `s` when `Ric(g₀) = c g₀`, and
  conversely at each time `t ∈ s` where `s` has unique derivatives.
* `TauCeti.tendsto_scalarCurvature_nhdsLT_atTop_of_inner_eq_one_sub_two_mul_smul`: along
  `(1 - 2 c τ) g₀` with `Ric(g₀) = c g₀` and `c > 0`, the scalar curvature `n c / (1 - 2 c τ)` blows
  up at the extinction time `1 / (2 c)`.
* `Bundle.ContMDiffRiemannianMetric.einsteinFlow`, the Einstein solution itself, with, in the same
  namespace, `ricciTensor_leviCivitaConnection_einsteinFlow` and
  `ricciTensor_leviCivitaConnection_einsteinFlow_eq_smul_inner` (its Ricci tensor),
  `hasDerivAt_inner_einsteinFlow` and `hasDerivAt_inner_einsteinFlow_iff` (its flow equation),
  `scalarCurvature_einsteinFlow`, `scalarCurvature_einsteinFlow_of_ricciTensor_eq_smul_inner` and
  `tendsto_scalarCurvature_einsteinFlow_nhdsLT_atTop` (its scalar curvature and extinction).
* `TauCeti.hasDerivWithinAt_const_inner_neg_two_mul_ricciTensor_of_ricciTensor_eq_zero` and
  `TauCeti.hasDerivWithinAt_const_inner_neg_two_mul_ricciTensor_iff_ricciTensor_eq_zero`: a
  constant family is a Ricci flow at a time with unique derivatives exactly when the metric is
  Ricci-flat, and
  `TauCeti.hasDerivWithinAt_const_inner_neg_two_mul_ricciTensor_of_finrank_le_one` shows that every
  metric in dimension at most one is stationary.
* `TauCeti.hasDerivAt_inner_einsteinFlow_sphereRoundMetric`,
  `TauCeti.scalarCurvature_einsteinFlow_sphereRoundMetric` and
  `TauCeti.tendsto_scalarCurvature_einsteinFlow_sphereRoundMetric_nhdsLT_atTop`: the shrinking round
  sphere `(1 - 2 (n - 1) τ) g_round` and its extinction at `1 / (2 (n - 1))`.

## References

* P. Topping, *Lectures on the Ricci flow*, LMS Lecture Note Series 325, Cambridge University
  Press (2006), §1.2.1 (Einstein solutions and the round sphere).
-/

public section

open Bundle CovariantDerivative Filter Metric Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {c τ : ℝ}

/-- The **Einstein solution** `τ ↦ (1 - 2 c τ) g₀` starting at a metric `g₀`. It is defined as
`(1 - 2 c τ) g₀` on the positive-scale interval `2 c τ < 1`, and as `g₀` off it, where
`(1 - 2 c τ) g₀` is not a metric. When `Ric(g₀) = c g₀` it is a Ricci flow on its positive-scale
interval, see `Bundle.ContMDiffRiemannianMetric.hasDerivAt_inner_einsteinFlow`. -/
def einsteinFlow (g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) (c τ : ℝ) :
    ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) :=
  if h : 2 * c * τ < 1 then
    g₀.rescale (fun _ ↦ 1 - 2 * c * τ) contMDiff_const fun _ ↦ by linarith
  else g₀

/-- On its positive-scale interval `2 c τ < 1` the Einstein solution is the rescaled metric
`(1 - 2 c τ) g₀`. -/
theorem einsteinFlow_of_lt (h : 2 * c * τ < 1) :
    g₀.einsteinFlow c τ = g₀.rescale (fun _ ↦ 1 - 2 * c * τ) contMDiff_const
      (fun _ ↦ sub_pos.2 h) := by
  simp [einsteinFlow, h]

/-- Off its positive-scale interval, where `1 ≤ 2 c τ`, the Einstein solution is `g₀`. -/
@[simp]
theorem einsteinFlow_of_le (h : 1 ≤ 2 * c * τ) : g₀.einsteinFlow c τ = g₀ := by
  simp [einsteinFlow, h.not_gt]

/-- On its positive-scale interval `2 c τ < 1` the Einstein solution has inner products
`(1 - 2 c τ) g₀`. -/
@[simp]
theorem einsteinFlow_inner (h : 2 * c * τ < 1) (y : M) :
    (g₀.einsteinFlow c τ).inner y = (1 - 2 * c * τ) • g₀.inner y := by
  ext v w
  simp [einsteinFlow_of_lt h]

/-- The Einstein solution starts at `g₀`. -/
@[simp]
theorem einsteinFlow_zero : g₀.einsteinFlow c 0 = g₀ := by
  ext y v w
  simp

/-- The Einstein solution with constant `0` is the constant family `g₀`. -/
@[simp]
theorem einsteinFlow_zero_left : g₀.einsteinFlow 0 τ = g₀ := by
  ext y v w
  simp

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {s : Set ℝ} {t : ℝ} {x : M}

section Homothetic

variable {φ : ℝ → ℝ} {φ' : ℝ}

/-- **Homothetic Ricci flows.** Let `g τ = φ(τ) g₀` for `τ ∈ s`, and let `φ` have derivative `φ'`
at `t ∈ s` within `s`. If `Ric(g₀) = -(φ'/2) g₀` at `x`, then the family satisfies the Ricci flow
equation `∂_τ g = -2 Ric(g)` at `x` at time `t` within `s`. -/
theorem hasDerivWithinAt_inner_neg_two_mul_ricciTensor_of_inner_eq_smul
    (hg : ∀ τ ∈ s, ∀ y, (g τ).inner y = φ τ • g₀.inner y) (hφ : HasDerivWithinAt φ φ' s t)
    (ht : t ∈ s)
    (hRic : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = (-(φ' / 2)) • innerₗ (TangentSpace I x))
    (u v : TangentSpace I x) :
    HasDerivWithinAt (fun τ ↦ (g τ).inner x u v)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x u v)) s t := by
  have hd : HasDerivWithinAt (fun τ ↦ (g τ).inner x u v) (φ' * g₀.inner x u v) s t :=
    (hφ.mul_const _).congr_of_mem (fun τ hτ ↦ by simp [hg τ hτ]) ht
  convert hd using 1
  rw [ContMDiffRiemannianMetric.ricciTensor_leviCivitaConnection_eq_of_inner_eq_smul (hg t ht) x,
    hRic]
  simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul]
  rw [ContMDiffRiemannianMetric.inner_riemannianBundle]
  ring

/-- **Homothetic Ricci flows are Einstein.** Let `g τ = φ(τ) g₀` for `τ ∈ s`, let `φ` have
derivative `φ'` at `t ∈ s` within `s`, and let `s` have unique derivatives at `t`. Then the family
satisfies the Ricci flow equation `∂_τ g = -2 Ric(g)` at `x` at time `t` exactly when
`Ric(g₀) = -(φ'/2) g₀` at `x`. -/
theorem hasDerivWithinAt_inner_neg_two_mul_ricciTensor_iff_of_inner_eq_smul
    (hg : ∀ τ ∈ s, ∀ y, (g τ).inner y = φ τ • g₀.inner y) (hφ : HasDerivWithinAt φ φ' s t)
    (ht : t ∈ s) (hs : UniqueDiffWithinAt ℝ s t) :
    (∀ u v : TangentSpace I x, HasDerivWithinAt (fun τ ↦ (g τ).inner x u v)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x u v)) s t) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = (-(φ' / 2)) • innerₗ (TangentSpace I x)) := by
  refine ⟨fun hflow ↦ ?_,
    hasDerivWithinAt_inner_neg_two_mul_ricciTensor_of_inner_eq_smul hg hφ ht⟩
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
  refine LinearMap.ext₂ fun u v ↦ ?_
  have h := hs.eq_deriv _
    ((hφ.mul_const (g₀.inner x u v)).congr_of_mem (fun τ hτ ↦ by simp [hg τ hτ]) ht) (hflow u v)
  rw [ContMDiffRiemannianMetric.ricciTensor_leviCivitaConnection_eq_of_inner_eq_smul (hg t ht)
    x] at h
  simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul,
    ContMDiffRiemannianMetric.inner_riemannianBundle]
  linarith

end Homothetic

section Einstein

variable {c : ℝ}

/-- **Einstein solutions of the Ricci flow.** If `Ric(g₀) = c g₀` at `x` and
`g τ = (1 - 2 c τ) g₀` for `τ ∈ s`, then the family satisfies the Ricci flow equation
`∂_τ g = -2 Ric(g)` at `x` at every time `t ∈ s`, within `s`. -/
theorem hasDerivWithinAt_inner_neg_two_mul_ricciTensor_of_inner_eq_one_sub_two_mul_smul
    (hg : ∀ τ ∈ s, ∀ y, (g τ).inner y = (1 - 2 * c * τ) • g₀.inner y) (ht : t ∈ s)
    (hRic : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = c • innerₗ (TangentSpace I x))
    (u v : TangentSpace I x) :
    HasDerivWithinAt (fun τ ↦ (g τ).inner x u v)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x u v)) s t := by
  have hφ : HasDerivWithinAt (fun τ ↦ 1 - 2 * c * τ) (-(2 * c)) s t := by
    simpa using ((hasDerivWithinAt_id t s).const_mul (2 * c)).const_sub 1
  exact hasDerivWithinAt_inner_neg_two_mul_ricciTensor_of_inner_eq_smul hg hφ ht
    (by rw [hRic]; congr 1; ring) u v

/-- **Einstein solutions are the homothetic Ricci flows `(1 - 2 c τ) g₀`.** Let
`g τ = (1 - 2 c τ) g₀` for `τ ∈ s`, and let `s` have unique derivatives at `t ∈ s`. Then the family
satisfies the Ricci flow equation `∂_τ g = -2 Ric(g)` at `x` at time `t` within `s` exactly when
`Ric(g₀) = c g₀` at `x`. -/
theorem hasDerivWithinAt_inner_neg_two_mul_ricciTensor_iff_of_inner_eq_one_sub_two_mul_smul
    (hg : ∀ τ ∈ s, ∀ y, (g τ).inner y = (1 - 2 * c * τ) • g₀.inner y) (ht : t ∈ s)
    (hs : UniqueDiffWithinAt ℝ s t) :
    (∀ u v : TangentSpace I x, HasDerivWithinAt (fun τ ↦ (g τ).inner x u v)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x u v)) s t) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = c • innerₗ (TangentSpace I x)) := by
  have hφ : HasDerivWithinAt (fun τ ↦ 1 - 2 * c * τ) (-(2 * c)) s t := by
    simpa using ((hasDerivWithinAt_id t s).const_mul (2 * c)).const_sub 1
  rw [hasDerivWithinAt_inner_neg_two_mul_ricciTensor_iff_of_inner_eq_smul hg hφ ht hs]
  congr! 2
  ring

/-- **Extinction of an Einstein solution.** Let `Ric(g₀) = c g₀` at `x` with `c > 0`, in positive
dimension, and let `g τ = (1 - 2 c τ) g₀` for all `τ` in a punctured left neighbourhood of
`T = (2 c)⁻¹`. Then the scalar curvature `Scal(g τ)` at `x` tends to `+∞` as `τ → T⁻`. -/
theorem tendsto_scalarCurvature_nhdsLT_atTop_of_inner_eq_one_sub_two_mul_smul (hc : 0 < c)
    (hE : 0 < finrank ℝ E)
    (hg : ∀ᶠ τ in 𝓝[<] (2 * c)⁻¹, ∀ y, (g τ).inner y = (1 - 2 * c * τ) • g₀.inner y)
    (hRic : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = c • innerₗ (TangentSpace I x)) :
    Tendsto (fun τ ↦ (g τ).scalarCurvature x) (𝓝[<] (2 * c)⁻¹) atTop := by
  -- The scale factor `1 - 2 c τ` tends to `0` from above as `τ → (2 c)⁻¹` from below.
  have hscale : Tendsto (fun τ ↦ 1 - 2 * c * τ) (𝓝[<] (2 * c)⁻¹) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun τ hτ ↦ ?_⟩
    · have hcont : Continuous fun τ : ℝ ↦ 1 - 2 * c * τ := by fun_prop
      have h0 : 1 - 2 * c * (2 * c)⁻¹ = 0 := by field_simp; ring
      exact h0 ▸ hcont.continuousWithinAt.tendsto
    · have : 2 * c * τ < 1 := (lt_inv_mul_iff₀ (by positivity)).1 (by rwa [mul_one])
      simp only [mem_Ioi]
      linarith
  have hnc : 0 < finrank ℝ E * c := by positivity
  refine ((tendsto_inv_nhdsGT_zero.comp hscale).atTop_mul_const hnc).congr' ?_
  filter_upwards [hg] with τ hτ
  rw [ContMDiffRiemannianMetric.scalarCurvature_eq_of_inner_eq_smul_of_ricciTensor_eq_smul_inner
    hτ hRic, Function.comp_apply, div_eq_inv_mul]

end Einstein

section Stationary

/-- **Ricci-flat metrics are stationary Ricci flows.** If `g₀` is Ricci-flat at `x`, the constant
family `g₀` satisfies the Ricci flow equation `∂_τ g = -2 Ric(g)` at `x` at every time. -/
theorem hasDerivWithinAt_const_inner_neg_two_mul_ricciTensor_of_ricciTensor_eq_zero
    (hRic : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = 0)
    (u v : TangentSpace I x) :
    HasDerivWithinAt (fun _ : ℝ ↦ g₀.inner x u v)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x u v)) s t := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
  simpa [hRic] using hasDerivWithinAt_const t s (g₀.inner x u v)

/-- **Stationary Ricci flows.** If `s` has unique derivatives at `t`, the constant family `g₀`
satisfies the Ricci flow equation `∂_τ g = -2 Ric(g)` at `x` at time `t` within `s` exactly when
`g₀` is Ricci-flat at `x`. -/
theorem hasDerivWithinAt_const_inner_neg_two_mul_ricciTensor_iff_ricciTensor_eq_zero
    (hs : UniqueDiffWithinAt ℝ s t) :
    (∀ u v : TangentSpace I x, HasDerivWithinAt (fun _ : ℝ ↦ g₀.inner x u v)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x u v)) s t) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = 0) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
  refine ⟨fun hflow ↦ LinearMap.ext₂ fun u v ↦ ?_,
    hasDerivWithinAt_const_inner_neg_two_mul_ricciTensor_of_ricciTensor_eq_zero⟩
  have := hs.eq_deriv _ (hasDerivWithinAt_const t s _) (hflow u v)
  simp only [LinearMap.zero_apply]
  linarith

/-- **Ricci flow in dimension at most one.** In dimension at most one the Ricci tensor vanishes,
so the constant family of every metric is a Ricci flow. -/
theorem hasDerivWithinAt_const_inner_neg_two_mul_ricciTensor_of_finrank_le_one
    (hE : finrank ℝ E ≤ 1) (u v : TangentSpace I x) :
    HasDerivWithinAt (fun _ : ℝ ↦ g₀.inner x u v)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x u v)) s t :=
  hasDerivWithinAt_const_inner_neg_two_mul_ricciTensor_of_ricciTensor_eq_zero
    (ricciTensor_eq_zero_of_finrank_le_one _ x hE) u v

end Stationary

end TauCeti

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {c t : ℝ} {x : M}

section EinsteinFlow

/-- The Ricci tensor of the Einstein solution is the Ricci tensor of `g₀` at every time. -/
theorem ricciTensor_leviCivitaConnection_einsteinFlow (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g₀.einsteinFlow c t).toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x) := by
  by_cases ht : 2 * c * t < 1
  · exact ricciTensor_leviCivitaConnection_eq_of_inner_eq_smul (einsteinFlow_inner ht) x
  · rw [einsteinFlow_of_le (not_lt.1 ht)]

/-- If `Ric(g₀) = c g₀` at `x`, then the Einstein solution has `Ric(g t) = (c / (1 - 2 c t)) g t`
at `x` at every time `t` of its positive-scale interval `2 c t < 1`. -/
theorem ricciTensor_leviCivitaConnection_einsteinFlow_eq_smul_inner (ht : 2 * c * t < 1)
    (hRic : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = c • innerₗ (TangentSpace I x)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g₀.einsteinFlow c t).toRiemannianMetric⟩
    (leviCivitaConnection I M).ricciTensor x =
      (c / (1 - 2 * c * t)) • innerₗ (TangentSpace I x) :=
  ricciTensor_leviCivitaConnection_eq_smul_inner_of_inner_eq_smul (einsteinFlow_inner ht) hRic

/-- **The Einstein solution is a Ricci flow.** If `Ric(g₀) = c g₀` at `x`, then the Einstein
solution `g τ = (1 - 2 c τ) g₀` satisfies the Ricci flow equation `∂_τ g = -2 Ric(g)` at `x` at
every time `t` of its positive-scale interval `2 c t < 1`. -/
theorem hasDerivAt_inner_einsteinFlow (ht : 2 * c * t < 1)
    (hRic : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = c • innerₗ (TangentSpace I x))
    (u v : TangentSpace I x) :
    HasDerivAt (fun τ ↦ (g₀.einsteinFlow c τ).inner x u v)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g₀.einsteinFlow c t).toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x u v)) t :=
  (TauCeti.hasDerivWithinAt_inner_neg_two_mul_ricciTensor_of_inner_eq_one_sub_two_mul_smul
    (s := {τ | 2 * c * τ < 1}) (fun _ hτ ↦ einsteinFlow_inner hτ) ht
    hRic u v).hasDerivAt ((isOpen_lt (by fun_prop) continuous_const).mem_nhds ht)

/-- **The Einstein solution is a Ricci flow exactly for Einstein metrics.** At a time `t` of its
positive-scale interval `2 c t < 1`, the Einstein solution satisfies the Ricci flow equation
`∂_τ g = -2 Ric(g)` at `x` exactly when `Ric(g₀) = c g₀` at `x`. -/
theorem hasDerivAt_inner_einsteinFlow_iff (ht : 2 * c * t < 1) :
    (∀ u v : TangentSpace I x, HasDerivAt (fun τ ↦ (g₀.einsteinFlow c τ).inner x u v)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g₀.einsteinFlow c t).toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x u v)) t) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = c • innerₗ (TangentSpace I x)) :=
  ⟨fun hflow ↦
    (TauCeti.hasDerivWithinAt_inner_neg_two_mul_ricciTensor_iff_of_inner_eq_one_sub_two_mul_smul
      (s := {τ | 2 * c * τ < 1}) (fun _ hτ ↦ einsteinFlow_inner hτ) ht
      ((isOpen_lt (by fun_prop) continuous_const).uniqueDiffWithinAt ht)).1
      fun u v ↦ (hflow u v).hasDerivWithinAt,
    fun hRic ↦ hasDerivAt_inner_einsteinFlow ht hRic⟩

/-- On its positive-scale interval `2 c t < 1` the Einstein solution has scalar curvature
`Scal(g t) = (1 - 2 c t)⁻¹ Scal(g₀)`. -/
@[simp]
theorem scalarCurvature_einsteinFlow (ht : 2 * c * t < 1) (x : M) :
    (g₀.einsteinFlow c t).scalarCurvature x = (1 - 2 * c * t)⁻¹ * g₀.scalarCurvature x :=
  scalarCurvature_eq_inv_mul_of_inner_eq_smul (einsteinFlow_inner ht) x

/-- Along the Einstein solution of a metric with `Ric(g₀) = c g₀` at `x`, the scalar curvature at
`x` is `Scal(g τ) = n c / (1 - 2 c τ)` on the positive-scale interval, where `n` is the
dimension. -/
theorem scalarCurvature_einsteinFlow_of_ricciTensor_eq_smul_inner (ht : 2 * c * t < 1)
    (hRic : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = c • innerₗ (TangentSpace I x)) :
    (g₀.einsteinFlow c t).scalarCurvature x = finrank ℝ E * c / (1 - 2 * c * t) :=
  scalarCurvature_eq_of_inner_eq_smul_of_ricciTensor_eq_smul_inner
    (einsteinFlow_inner ht) hRic

/-- **Extinction of the Einstein solution.** Let `Ric(g₀) = c g₀` at `x` with `c > 0`, in positive
dimension. Then the scalar curvature at `x` of the Einstein solution tends to `+∞` as `τ` tends
from below to the end `T = (2 c)⁻¹` of its positive-scale interval. -/
theorem tendsto_scalarCurvature_einsteinFlow_nhdsLT_atTop (hc : 0 < c) (hE : 0 < finrank ℝ E)
    (hRic : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = c • innerₗ (TangentSpace I x)) :
    Tendsto (fun τ ↦ (g₀.einsteinFlow c τ).scalarCurvature x) (𝓝[<] (2 * c)⁻¹) atTop :=
  TauCeti.tendsto_scalarCurvature_nhdsLT_atTop_of_inner_eq_one_sub_two_mul_smul hc hE
    (eventually_nhdsWithin_of_forall fun τ (hτ : τ < (2 * c)⁻¹) ↦
      einsteinFlow_inner ((lt_inv_mul_iff₀ (by positivity)).1 (by rwa [mul_one])))
    hRic

end EinsteinFlow

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

section Sphere

variable {t : ℝ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ}
  [Fact (finrank ℝ F = n + 1)]

/-- **The shrinking round sphere.** The Einstein solution `g τ = (1 - 2 (n - 1) τ) g_round` of the
round metric on the unit `n`-sphere satisfies the Ricci flow equation `∂_τ g = -2 Ric(g)` at every
point and at every time `t` with `2 (n - 1) t < 1`. -/
theorem hasDerivAt_inner_einsteinFlow_sphereRoundMetric (ht : 2 * ((n : ℝ) - 1) * t < 1)
    (p : sphere (0 : F) 1) (u v : TangentSpace (𝓡 n) p) :
    HasDerivAt (fun τ ↦ ((sphereRoundMetric (E := F) (n := n)).ofLE (m := ∞) le_top
        |>.einsteinFlow ((n : ℝ) - 1) τ).inner p u v)
      (-2 * (letI : RiemannianBundle (fun p : sphere (0 : F) 1 ↦ TangentSpace (𝓡 n) p) :=
          ⟨((sphereRoundMetric (E := F) (n := n)).ofLE (m := ∞) le_top
            |>.einsteinFlow ((n : ℝ) - 1) t).toRiemannianMetric⟩;
        (leviCivitaConnection (𝓡 n) (sphere (0 : F) 1)).ricciTensor p u v)) t :=
  ContMDiffRiemannianMetric.hasDerivAt_inner_einsteinFlow ht (ricciTensor_sphereRoundMetric_ofLE p)
    u v

/-- Along the shrinking round sphere `g τ = (1 - 2 (n - 1) τ) g_round`, the scalar curvature is
`n (n - 1) / (1 - 2 (n - 1) τ)` at every point and at every time with `2 (n - 1) τ < 1`. -/
theorem scalarCurvature_einsteinFlow_sphereRoundMetric (ht : 2 * ((n : ℝ) - 1) * t < 1)
    (p : sphere (0 : F) 1) :
    ((sphereRoundMetric (E := F) (n := n)).ofLE (m := ∞) le_top
        |>.einsteinFlow ((n : ℝ) - 1) t).scalarCurvature p =
      n * ((n : ℝ) - 1) / (1 - 2 * ((n : ℝ) - 1) * t) := by
  rw [ContMDiffRiemannianMetric.scalarCurvature_einsteinFlow_of_ricciTensor_eq_smul_inner ht
    (ricciTensor_sphereRoundMetric_ofLE p), finrank_euclideanSpace_fin]

/-- **Extinction of the shrinking round sphere.** For `n ≥ 2`, along the Einstein solution
`g τ = (1 - 2 (n - 1) τ) g_round` of the unit `n`-sphere, the scalar curvature at every point tends
to `+∞` as `τ` tends to `T = (2 (n - 1))⁻¹` from below: the flow starting at the unit sphere
becomes extinct at time `1 / (2 (n - 1))`. -/
theorem tendsto_scalarCurvature_einsteinFlow_sphereRoundMetric_nhdsLT_atTop (hn : 2 ≤ n)
    (p : sphere (0 : F) 1) :
    Tendsto (fun τ ↦ ((sphereRoundMetric (E := F) (n := n)).ofLE (m := ∞) le_top
        |>.einsteinFlow ((n : ℝ) - 1) τ).scalarCurvature p)
      (𝓝[<] (2 * ((n : ℝ) - 1))⁻¹) atTop := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  refine ContMDiffRiemannianMetric.tendsto_scalarCurvature_einsteinFlow_nhdsLT_atTop
    (by linarith) ?_ (ricciTensor_sphereRoundMetric_ofLE p)
  rw [finrank_euclideanSpace_fin]
  omega

end Sphere

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.StripAction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Cylinder
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Homotopy
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Variation
import TauCeti.Geometry.Symplectic.Hamiltonian.LoopVariation

/-!
# The first variation of the action of paths between exact Lagrangians

Let `ω = dα` be a nondegenerate exact two-form on a finite-dimensional manifold `M`, and let
`i₀ : N₀ → M` and `i₁ : N₁ → M` be maps with `i₀^* α = d f₀` and `i₁^* α = d f₁`, for instance
exact Lagrangian maps with primitives `f₀` and `f₁`. A path `γ` from `L₀ = i₀(N₀)` to
`L₁ = i₁(N₁)` has the action

`A_H(γ) = -∫_γ α - ∫₀¹ H(t, γ(t)) dt + f₁(y₁) - f₀(y₀)`

of `TauCeti.lagrangianPathAction`, where `γ(0) = i₀(y₀)` and `γ(1) = i₁(y₁)`. A **variation
through paths from `L₀` to `L₁`** is a `C²` map `w : ℝ × ℝ → M` whose paths `γ_s = w(s, ·)` start
on `L₀` and end on `L₁`, through `C¹` lifts: `w(s, 0) = i₀(c₀(s))` and `w(s, 1) = i₁(c₁(s))`. This
file computes the derivative in `s` of `A_H(γ_s)`, with the endpoint data `c₀(s)` and `c₁(s)`.

* By Stokes' formula on the rectangle `[s₀, s] × [0, 1]`, the line integrals of `α` along the paths
  change by the area swept by the variation plus the line integrals of `α` along the two sides.
  The sides lie in the Lagrangians, where `α` is exact, so these are exactly the changes of `f₀`
  and `f₁`, which the action subtracts. Hence the primitives part of the action has derivative
  `-∫₀¹ ω(∂_s w, ∂_t w) dt`.
* Differentiating under the integral sign, the Hamiltonian term has derivative
  `-∫₀¹ dH_t(∂_s w) dt`.
* For Hamiltonian vector fields `ι_{X_{H_t}} ω = dH_t`, the two combine into the **first variation
  formula**
  `d/ds A_H(γ_s) = ∫₀¹ ω(∂_t w - X_{H_t}(w), ∂_s w) dt`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_lagrangianPathAction`).

For a metric `ω(·, J ·)` of an `ω`-compatible `J` the integrand is the inner product of
`J(∂_t w - X_H)` with `∂_s w`, so `J(∂_t γ - X_H(γ))` is the gradient of the action and its
negative gradient flow is the Floer equation `∂_s u + J(∂_t u - X_H(u)) = 0`, along which
`TauCeti.Geometry.Symplectic.Floer.StripAction` computes the energy.

A path is a **critical point of the action** (`TauCeti.IsLagrangianPathActionCritical`) when it is
a `C²` path from `i₀(y₀)` to `i₁(y₁)` and the derivative at `s = 0` of `A_H(γ_s)` vanishes for every
variation through paths from `L₀` to `L₁` starting at `γ`, with lifts starting at `y₀` and `y₁`.
The first variation formula shows that the **Hamiltonian chords** from `L₀` to `L₁`, the paths with
`γ'(t) = X_{H_t}(γ(t))` for `t ∈ [0, 1]`, are critical. Conversely, if `γ' ≠ X_H(γ)` at some time
`t₀ ∈ [0, 1]`, the pairing of `γ' - X_H` with a suitable chart direction stays positive near
`t₀`, and pushing `γ` in that direction near an interior time close to `t₀`, with the endpoints
fixed, gives a variation along which the action has a nonzero derivative. Hence, on a manifold
without boundary modelled on a finite-dimensional space, the critical paths are exactly the
Hamiltonian chords (`TauCeti.SmoothTwoForm.IsNondegenerate.isLagrangianPathActionCritical_iff`).
These are the generators of the Floer complex of the pair `(L₀, L₁)`. The converse applies the
chart-variation argument for paths of `TauCeti.Geometry.Symplectic.Hamiltonian.LoopVariation`,
shared with the action of seamed paths, to the chart variations
`TauCeti.Manifold.sinChartVariation`, which fix the endpoints.

## Main definitions

* `TauCeti.IsLagrangianPathActionCritical`: `γ` is a critical point of the action of paths from
  `L₀` to `L₁`.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `hasDerivAt_lagrangianPathAction`: the first variation formula.
* `isLagrangianPathActionCritical`: Hamiltonian chords are critical points of the action.
* `isLagrangianPathActionCritical_iff`: the critical points of the action are exactly the
  Hamiltonian chords.

In the namespace `TauCeti.IsLagrangianPathActionCritical`:

* `hasMFDerivAt`: critical points of the action are Hamiltonian chords.

## References

* D. Auroux, *A beginner's introduction to Fukaya categories*, arXiv:1301.7056, §1.2 (the action
  functional on paths between exact Lagrangians, whose critical points are the chords and whose
  gradient flow lines are the Floer strips).
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Zurich Lectures in Advanced
  Mathematics, EMS, 2008, Section 8.
-/

public section

noncomputable section

open Function Set Filter MeasureTheory Metric
open scoped Manifold Interval Topology

namespace TauCeti

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  {E₀ H₀ N₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀]
  {I₀ : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace N₀] [ChartedSpace H₀ N₀]
  {E₁ H₁ N₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
  {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace N₁] [ChartedSpace H₁ N₁]

/-! ### Critical paths of the action -/

variable (I₀ I₁) in
/-- A path `γ` is a **critical point of the action** `A_H` of paths from `L₀ = i₀(N₀)` to
`L₁ = i₁(N₁)`, for the primitive `α` and the primitives `f₀`, `f₁` along the Lagrangians, when it
is a `C²` path from `i₀(y₀)` to `i₁(y₁)` and, for every `C²` variation `w` through paths from `L₀`
to `L₁` starting at `γ`, with `C¹` lifts `c₀`, `c₁` of its sides starting at `y₀` and `y₁`, the
action `A_H(w (s, ·))` has derivative `0` at `s = 0`. -/
structure IsLagrangianPathActionCritical (α : RoughForm I M ℝ 1) (f₀ : N₀ → ℝ) (f₁ : N₁ → ℝ)
    (i₀ : N₀ → M) (i₁ : N₁ → M) (H : ℝ → M → ℝ) (γ : ℝ → M) (y₀ : N₀) (y₁ : N₁) : Prop where
  /-- A critical path is `C²`. -/
  contMDiff : ContMDiff 𝓘(ℝ, ℝ) I 2 γ
  /-- A critical path starts at `i₀(y₀)`. -/
  apply_zero : γ 0 = i₀ y₀
  /-- A critical path ends at `i₁(y₁)`. -/
  apply_one : γ 1 = i₁ y₁
  /-- The action is stationary along every variation through paths from `L₀` to `L₁`. -/
  hasDerivAt : ∀ ⦃w : ℝ × ℝ → M⦄ ⦃c₀ : ℝ → N₀⦄ ⦃c₁ : ℝ → N₁⦄,
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 w → ContMDiff 𝓘(ℝ, ℝ) I₀ 1 c₀ → ContMDiff 𝓘(ℝ, ℝ) I₁ 1 c₁ →
    (∀ s, w (s, 0) = i₀ (c₀ s)) → (∀ s, w (s, 1) = i₁ (c₁ s)) → (∀ t, w (0, t) = γ t) →
    c₀ 0 = y₀ → c₁ 0 = y₁ →
    HasDerivAt (fun s ↦ lagrangianPathAction α f₀ f₁ H (fun t ↦ w (s, t)) (c₀ s) (c₁ s)) 0 0

/-! ### The first variation formula -/

namespace SmoothTwoForm.IsNondegenerate

section FirstVariation

variable [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}
  {α : SmoothForm I M ℝ 1} {H : ℝ → M → ℝ} {w : ℝ × ℝ → M} {f₀ : N₀ → ℝ} {c₀ : ℝ → N₀}
  {f₁ : N₁ → ℝ} {c₁ : ℝ → N₁}

omit [TopologicalSpace N₀] [TopologicalSpace N₁] in
/-- The first variation formula, for any variation whose two sides have line integrals of `α`
given by the changes of `f₀ ∘ c₀` and `f₁ ∘ c₁`. -/
private theorem hasDerivAt_lagrangianPathAction_of_pathIntegral (hω : ω.IsNondegenerate)
    (hα : mextDeriv α.val = ω.val) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 w) {s₀ : ℝ}
    (h₀ : ∀ s, pathIntegral α.val (fun s ↦ w (s, 0)) s₀ s = f₀ (c₀ s) - f₀ (c₀ s₀))
    (h₁ : ∀ s, pathIntegral α.val (fun s ↦ w (s, 1)) s₀ s = f₁ (c₁ s) - f₁ (c₁ s₀)) :
    HasDerivAt (fun s ↦ lagrangianPathAction α.val f₀ f₁ H (fun t ↦ w (s, t)) (c₀ s) (c₁ s))
      (∫ t in 0..1, ω.val (w (s₀, t))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1) - ω.hamiltonianVectorField (H t) (w (s₀, t)),
          mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0)]) s₀ := by
  have hω₀ : IsSmoothForm I 0 ω.val := ω.isSmoothForm.of_le (by simp)
  have hw₁ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 w := hw.of_le one_le_two
  set g : ℝ → ℝ := fun s ↦ ∫ t in (0 : ℝ)..1,
    TauCeti.mpullback 𝓘(ℝ, ℝ × ℝ) I w ω.val (s, t) ![(1, 0), (0, 1)]
  have hg : Continuous g := continuous_integral_mpullback hω₀ hw₁ 0 1
  -- Stokes' formula on `[s₀, s] × [0, 1]`, with the sides in the Lagrangians
  have hstokes (s : ℝ) : ∫ x in s₀..s, g x =
      (pathIntegral α.val (fun t ↦ w (s, t)) 0 1 - pathIntegral α.val (fun t ↦ w (s₀, t)) 0 1) -
        ((f₁ (c₁ s) - f₁ (c₁ s₀)) - (f₀ (c₀ s) - f₀ (c₀ s₀))) := by
    have h := rectangleIntegral_mextDeriv (α.isSmoothForm.of_le (by simp)) hw (s₀, 0) (s, 1)
    rwa [hα, rectangleIntegral_def, h₀, h₁] at h
  have hfun : (fun s ↦ lagrangianPathAction α.val f₀ f₁ H (fun t ↦ w (s, t)) (c₀ s) (c₁ s)) =
      fun s ↦ (lagrangianPathAction α.val f₀ f₁ H (fun t ↦ w (s₀, t)) (c₀ s₀) (c₁ s₀) +
        ∫ t in 0..1, H t (w (s₀, t))) - (∫ x in s₀..s, g x) - ∫ t in 0..1, H t (w (s, t)) := by
    funext s
    rw [hstokes, lagrangianPathAction_def, lagrangianPathAction_def]
    ring
  rw [hfun]
  -- the primitives part of the action has the derivative of the swept area
  have hg₀ : g s₀ = ∫ t in 0..1, ω.val (w (s₀, t))
      ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1)] :=
    intervalIntegral.integral_congr fun t _ ↦ mpullback_apply_pair w ω.val (s₀, t) (1, 0) (0, 1)
  exact hω.hasDerivAt_sub_intervalIntegral hH hw₁
    (hg₀ ▸ (hg.integral_hasStrictDerivAt s₀ s₀).hasDerivAt.const_sub _)

/-- **The first variation of the action of paths between exact Lagrangians.** Let `ω = dα` be a
nondegenerate exact two-form on a finite-dimensional manifold, `H` a jointly `C¹` time-dependent
Hamiltonian, and `w` a `C²` variation through paths from `L₀` to `L₁`: its sides are
`w(s, 0) = i₀(c₀(s))` and `w(s, 1) = i₁(c₁(s))` for `C¹` curves `c₀` and `c₁`, where
`i₀^* α = d f₀` and `i₁^* α = d f₁`. Then the action of the paths `w (s, ·)` has derivative
`∫₀¹ ω(∂_t w - X_{H_t}(w), ∂_s w) dt` at `s₀`, with all terms taken at `(s₀, t)`. -/
theorem hasDerivAt_lagrangianPathAction (hω : ω.IsNondegenerate) (hα : mextDeriv α.val = ω.val)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 w)
    {i₀ : N₀ → M} (hi₀ : MDifferentiable I₀ I i₀) (hf₀ : ContMDiff I₀ 𝓘(ℝ) 1 f₀)
    (hL₀ : mpullback I₀ I i₀ α.val = mextDeriv (RoughForm.ofFunction I₀ f₀))
    (hc₀ : ContMDiff 𝓘(ℝ, ℝ) I₀ 1 c₀) {i₁ : N₁ → M} (hi₁ : MDifferentiable I₁ I i₁)
    (hf₁ : ContMDiff I₁ 𝓘(ℝ) 1 f₁)
    (hL₁ : mpullback I₁ I i₁ α.val = mextDeriv (RoughForm.ofFunction I₁ f₁))
    (hc₁ : ContMDiff 𝓘(ℝ, ℝ) I₁ 1 c₁) (hw₀ : ∀ s, w (s, 0) = i₀ (c₀ s))
    (hw₁ : ∀ s, w (s, 1) = i₁ (c₁ s)) (s₀ : ℝ) :
    HasDerivAt (fun s ↦ lagrangianPathAction α.val f₀ f₁ H (fun t ↦ w (s, t)) (c₀ s) (c₁ s))
      (∫ t in 0..1, ω.val (w (s₀, t))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1) - ω.hamiltonianVectorField (H t) (w (s₀, t)),
          mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0)]) s₀ :=
  -- the sides lie in the Lagrangians, where the line integrals of `α` are changes of primitives
  hω.hasDerivAt_lagrangianPathAction_of_pathIntegral hα hH hw
    (fun s ↦ (funext hw₀ : (fun s ↦ w (s, 0)) = i₀ ∘ c₀) ▸
      pathIntegral_comp_eq_sub_of_mpullback_eq hi₀ hf₀ hL₀ hc₀ s₀ s)
    (fun s ↦ (funext hw₁ : (fun s ↦ w (s, 1)) = i₁ ∘ c₁) ▸
      pathIntegral_comp_eq_sub_of_mpullback_eq hi₁ hf₁ hL₁ hc₁ s₀ s)

/-- **Hamiltonian chords are critical points of the action.** For a nondegenerate exact two-form
`ω = dα` on a finite-dimensional manifold, maps `i₀`, `i₁` with `i₀^* α = d f₀` and
`i₁^* α = d f₁`, and a jointly `C¹` Hamiltonian, a `C²` path from `i₀(y₀)` to `i₁(y₁)` with
`γ'(t) = X_{H_t}(γ(t))` for `t ∈ [0, 1]` is a critical point of the action. -/
theorem isLagrangianPathActionCritical (hω : ω.IsNondegenerate) (hα : mextDeriv α.val = ω.val)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) {i₀ : N₀ → M}
    (hi₀ : MDifferentiable I₀ I i₀) (hf₀ : ContMDiff I₀ 𝓘(ℝ) 1 f₀)
    (hL₀ : mpullback I₀ I i₀ α.val = mextDeriv (RoughForm.ofFunction I₀ f₀)) {i₁ : N₁ → M}
    (hi₁ : MDifferentiable I₁ I i₁) (hf₁ : ContMDiff I₁ 𝓘(ℝ) 1 f₁)
    (hL₁ : mpullback I₁ I i₁ α.val = mextDeriv (RoughForm.ofFunction I₁ f₁)) {γ : ℝ → M}
    {y₀ : N₀} {y₁ : N₁} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) (h₀ : γ 0 = i₀ y₀) (h₁ : γ 1 = i₁ y₁)
    (hchord : ∀ t ∈ Icc (0 : ℝ) 1, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H t) (γ t)))) :
    IsLagrangianPathActionCritical I₀ I₁ α.val f₀ f₁ i₀ i₁ H γ y₀ y₁ where
  contMDiff := hγ
  apply_zero := h₀
  apply_one := h₁
  hasDerivAt w c₀ c₁ hw hc₀ hc₁ hw₀ hw₁ hwγ _ _ := by
    convert hω.hasDerivAt_lagrangianPathAction hα hH hw hi₀ hf₀ hL₀ hc₀ hi₁ hf₁ hL₁ hc₁ hw₀ hw₁ 0
      using 1
    refine (intervalIntegral.integral_congr fun t ht ↦ ?_).trans intervalIntegral.integral_zero
      |>.symm
    rw [uIcc_of_le zero_le_one] at ht
    -- along the chord, `∂_t w (0, t) = γ'(t) = X_{H_t}(γ(t))`
    have hγw : (fun t ↦ w (0, t)) = γ := funext hwγ
    have hv : mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (0, 1) =
        ω.hamiltonianVectorField (H t) (w (0, t)) := by
      rw [← Manifold.curveVelocity_eq_mfderiv_snd (f := fun a b ↦ w (a, b))
          ((hw (0, t)).mdifferentiableAt two_ne_zero), hγw, hwγ t,
        ← Manifold.curveVelocityWithin_univ]
      exact Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt
        (hchord t ht).hasMFDerivWithinAt uniqueDiffWithinAt_univ
    rw [hv, sub_self]
    exact (ω.val (w (0, t))).map_coord_zero 0 rfl

end FirstVariation

/-! ### Critical paths are Hamiltonian chords -/

section CriticalPaths

variable [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] [I.Boundaryless] {ω : SmoothTwoForm I M}
  {H : ℝ → M → ℝ} {γ : ℝ → M} {x₀ : M} {J : Set ℝ} {φ : ℝ → ℝ} {e : E}

variable {α : SmoothForm I M ℝ 1} {f₀ : N₀ → ℝ} {f₁ : N₁ → ℝ} {i₀ : N₀ → M} {i₁ : N₁ → M}
  {y₀ : N₀} {y₁ : N₁}

/-- **The chart variations of a critical path.** Let `γ` be a critical point of the action, and
`J ⊆ (0, 1)` an open set of times on which `γ` stays in the chart at `x₀`, and `φ` a `C²` profile
supported in `J` such that the points `ψ (γ t) + (c φ(t)) • e`, `|c| ≤ 1`, stay in the chart
target. The chart variation fixes the endpoints, so it is a variation through paths from `L₀` to
`L₁` with constant lifts, and the first variation formula along it gives `∫₀¹ φ g = 0` for the
pairing `g` of `γ' - X_H` with the tangent vectors of chart coordinates `e`. -/
private theorem _root_.TauCeti.IsLagrangianPathActionCritical.integral_mul_apply_eq_zero
    (hc : IsLagrangianPathActionCritical I₀ I₁ α.val f₀ f₁ i₀ i₁ H γ y₀ y₁)
    (hω : ω.IsNondegenerate) (hα : mextDeriv α.val = ω.val)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hJo : IsOpen J) (hJ01 : J ⊆ Ioo 0 1)
    (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source)
    (hT : ∀ t ∈ J, ∀ c : ℝ, |c| ≤ 1 →
      extChartAt I x₀ (γ t) + (c * φ t) • e ∈ (extChartAt I x₀).target)
    (hφ : ContDiff ℝ 2 φ) (hφJ : tsupport φ ⊆ J) :
    (∫ t in 0..1, φ t * ω.val (γ t) ![Manifold.curveVelocity I γ t -
      ω.hamiltonianVectorField (H t) (γ t), (trivializationAt E (TangentSpace I) x₀).symmL ℝ
        (γ t) e]) = 0 := by
  have hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 (Manifold.sinChartVariation I γ x₀ J φ e) :=
    Manifold.contMDiff_sinChartVariation hJo hJ hT hφ hφJ hc.contMDiff
  -- the variation fixes the endpoints `γ 0` and `γ 1`
  have hend : ∀ s t, t ∉ J → Manifold.sinChartVariation I γ x₀ J φ e (s, t) = γ t :=
    fun s _ ht ↦ Manifold.sinChartVariation_of_notMem ht s
  have h0J : (0 : ℝ) ∉ J := fun h ↦ lt_irrefl _ (hJ01 h).1
  have h1J : (1 : ℝ) ∉ J := fun h ↦ lt_irrefl _ (hJ01 h).2
  have hd := hω.hasDerivAt_lagrangianPathAction_of_pathIntegral (c₀ := fun _ ↦ y₀)
    (c₁ := fun _ ↦ y₁) (f₀ := f₀) (f₁ := f₁) hα hH hwc (s₀ := 0)
    (fun s ↦ by simp only [hend _ 0 h0J, pathIntegral_const_curve, sub_self])
    (fun s ↦ by simp only [hend _ 1 h1J, pathIntegral_const_curve, sub_self])
  have hd' := hc.hasDerivAt hwc contMDiff_const contMDiff_const
    (fun s ↦ by rw [hend s 0 h0J, hc.apply_zero]) (fun s ↦ by rw [hend s 1 h1J, hc.apply_one])
    (Manifold.sinChartVariation_zero hJ) rfl rfl
  exact (intervalIntegral.integral_congr fun t _ ↦ (SmoothTwoForm.apply_mfderiv_sinChartVariation
    (σ := ω) (n := 2) (by norm_num) hJo hJ hT hφ hφJ hc.contMDiff t).symm).trans (hd.unique hd')

/-- **Critical points of the action are Hamiltonian chords.** Let `ω = dα` be a nondegenerate
exact two-form on a manifold without boundary modelled on a finite-dimensional space, and `H` a
jointly `C¹` Hamiltonian. Then a critical point `γ` of the action of paths between two exact
Lagrangians satisfies `γ'(t) = X_{H_t}(γ(t))` for `t ∈ [0, 1]`. -/
theorem _root_.TauCeti.IsLagrangianPathActionCritical.hasMFDerivAt
    (hc : IsLagrangianPathActionCritical I₀ I₁ α.val f₀ f₁ i₀ i₁ H γ y₀ y₁)
    (hω : ω.IsNondegenerate) (hα : mextDeriv α.val = ω.val)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I γ t₀
      ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H t₀) (γ t₀))) := by
  rw [← hω.curveVelocity_eq_hamiltonianVectorField_of_forall_integral_mul_eq_zero hH (n := 2)
    (by norm_num) hc.contMDiff (fun _ _ _ _ hJo hJ01 hJ hT hφ hφJ ↦
      hc.integral_mul_apply_eq_zero hω hα hH hJo hJ01 hJ hT hφ hφJ) ht₀]
  exact Manifold.hasMFDerivAt_curveVelocity
    ((hc.contMDiff t₀).mdifferentiableAt two_ne_zero)

/-- **The critical points of the action are the Hamiltonian chords.** Let `ω = dα` be a
nondegenerate exact two-form on a manifold without boundary modelled on a finite-dimensional
space, `i₀`, `i₁` maps with `i₀^* α = d f₀` and `i₁^* α = d f₁`, and `H` a jointly `C¹`
Hamiltonian. A `C²` path `γ` from `i₀(y₀)` to `i₁(y₁)` is a critical point of the action exactly
when it is a Hamiltonian chord, `γ'(t) = X_{H_t}(γ(t))` for `t ∈ [0, 1]`. -/
theorem isLagrangianPathActionCritical_iff (hω : ω.IsNondegenerate) (hα : mextDeriv α.val = ω.val)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hi₀ : MDifferentiable I₀ I i₀) (hf₀ : ContMDiff I₀ 𝓘(ℝ) 1 f₀)
    (hL₀ : mpullback I₀ I i₀ α.val = mextDeriv (RoughForm.ofFunction I₀ f₀))
    (hi₁ : MDifferentiable I₁ I i₁) (hf₁ : ContMDiff I₁ 𝓘(ℝ) 1 f₁)
    (hL₁ : mpullback I₁ I i₁ α.val = mextDeriv (RoughForm.ofFunction I₁ f₁))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 2 γ) (h₀ : γ 0 = i₀ y₀) (h₁ : γ 1 = i₁ y₁) :
    IsLagrangianPathActionCritical I₀ I₁ α.val f₀ f₁ i₀ i₁ H γ y₀ y₁ ↔
      ∀ t ∈ Icc (0 : ℝ) 1, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H t) (γ t))) :=
  ⟨fun hc _ ht ↦ hc.hasMFDerivAt hω hα hH ht,
    hω.isLagrangianPathActionCritical hα hH hi₀ hf₀ hL₀ hi₁ hf₁ hL₁ hγ h₀ h₁⟩

end CriticalPaths

end SmoothTwoForm.IsNondegenerate

end TauCeti

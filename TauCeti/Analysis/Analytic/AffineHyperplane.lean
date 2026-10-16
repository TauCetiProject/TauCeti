/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import TauCeti.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Local equations of an affine hyperplane along an analytic curve

Let `ℓ` be a continuous linear functional on a normed space `E`, and `γ` an analytic curve passing
at `w` through a point `p` of the affine hyperplane `ℓ = b`. Any function `H` analytic at `p` with
nonzero differential at `p`, vanishing on the hyperplane near `p`, is a local equation of the
hyperplane in the same sense as `ℓ - b`, and the two equations meet `γ` to the same order:
`H ∘ γ` and `ℓ ∘ γ - b` have the same order of vanishing at `w`
(`AnalyticAt.analyticOrderAt_comp_eq_analyticOrderAt_sub`).

The first step is that a function vanishing on the hyperplane near `p` has differential at `p`
vanishing on its direction `ker ℓ` (`DifferentiableAt.fderiv_apply_eq_zero_of_eventually_eq_zero`).

This is what makes the intersection order of a holomorphic curve with a smooth complex hypersurface
independent of the coordinates in which it is computed: after a change of analytic coordinates an
affine equation of the hypersurface becomes a nonlinear one, still with nonzero differential.

## Implementation notes

The proof compares the two functions directly. Writing `γ t = q t + g t • v`, where
`g = ℓ ∘ γ - b`, `ℓ v = 1` and `q t` lies on the hyperplane, strict differentiability of `H` at `p`
gives `H (γ t) = H (γ t) - H (q t) = c * g t + o (g t)` with `c = DH(p) v`. Since `DH(p)` vanishes
on the kernel of `ℓ` but not identically, `c ≠ 0`, so `H ∘ γ` and `g` are equivalent up to constant
factors and have the same order (`AnalyticAt.analyticOrderAt_eq_of_isTheta`).
-/

public section

open Asymptotics Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- A function differentiable at a point `p` of an affine hyperplane `ℓ = b` and vanishing on the
hyperplane near `p` has differential at `p` vanishing on the kernel of `ℓ`, the direction of the
hyperplane. -/
theorem _root_.DifferentiableAt.fderiv_apply_eq_zero_of_eventually_eq_zero {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : E → F} {ℓ : E →L[𝕜] 𝕜} {b : 𝕜} {p : E}
    (hH : DifferentiableAt 𝕜 H p) (hp : ℓ p = b) (hzero : ∀ᶠ x in 𝓝 p, ℓ x = b → H x = 0)
    {u : E} (hu : ℓ u = 0) : fderiv 𝕜 H p u = 0 := by
  have hl : HasDerivAt (fun s : 𝕜 => p + s • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : 𝕜)).smul_const u).const_add p
  have hd : HasDerivAt (fun s : 𝕜 => H (p + s • u)) (fderiv 𝕜 H p u) 0 :=
    hH.hasFDerivAt.comp_hasDerivAt_of_eq (0 : 𝕜) hl (by simp)
  have h0 : (fun s : 𝕜 => H (p + s • u)) =ᶠ[𝓝 0] fun _ => 0 := by
    have ht : Tendsto (fun s : 𝕜 => p + s • u) (𝓝 0) (𝓝 p) := by
      simpa using hl.continuousAt.tendsto
    filter_upwards [ht.eventually hzero] with s hs
    exact hs (by simp [hu, hp])
  exact hd.unique ((hasDerivAt_const (0 : 𝕜) (0 : F)).congr_of_eventuallyEq h0)

/-- **Two local equations of an affine hyperplane meet an analytic curve to the same order.** Let
`γ` be analytic at `w` with `γ w` on the hyperplane `ℓ = b`, and let `H` be analytic at `γ w` with
nonzero differential there and vanishing on the hyperplane near `γ w`. Then `H ∘ γ` and `ℓ ∘ γ - b`
have the same order of vanishing at `w`. -/
theorem _root_.AnalyticAt.analyticOrderAt_comp_eq_analyticOrderAt_sub {H : E → 𝕜} {γ : 𝕜 → E}
    {ℓ : E →L[𝕜] 𝕜} {b w : 𝕜} (hH : AnalyticAt 𝕜 H (γ w)) (hH' : fderiv 𝕜 H (γ w) ≠ 0)
    (hγ : AnalyticAt 𝕜 γ w) (hw : ℓ (γ w) = b) (hzero : ∀ᶠ x in 𝓝 (γ w), ℓ x = b → H x = 0) :
    analyticOrderAt (fun t => H (γ t)) w = analyticOrderAt (fun t => ℓ (γ t) - b) w := by
  have hker (u : E) : ℓ u = 0 → fderiv 𝕜 H (γ w) u = 0 :=
    hH.differentiableAt.fderiv_apply_eq_zero_of_eventually_eq_zero hw hzero
  -- `ℓ ≠ 0`, since otherwise the differential of `H` would vanish on all of `E`
  obtain ⟨v, hv⟩ : ∃ v, ℓ v = 1 := by
    by_contra! hv
    have hℓ (x : E) : ℓ x = 0 := by
      by_contra hx
      exact hv ((ℓ x)⁻¹ • x) (by simp [hx])
    exact hH' (ContinuousLinearMap.ext fun x => by simpa using hker x (hℓ x))
  -- the differential of `H` is `c • ℓ` with `c ≠ 0`
  set c := fderiv 𝕜 H (γ w) v
  have hD (x : E) : fderiv 𝕜 H (γ w) x = ℓ x * c := by
    have h := hker (x - ℓ x • v) (by simp [hv])
    rwa [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h
  have hc : c ≠ 0 := fun hc => hH' (ContinuousLinearMap.ext fun x => by simp [hD, hc])
  -- the projection `q t = γ t - g t • v` of `γ t` to the hyperplane, along `v`
  set g : 𝕜 → 𝕜 := fun t => ℓ (γ t) - b
  have hgw : g w = 0 := sub_eq_zero.2 hw
  have hq : Tendsto (fun t => (γ t, γ t - g t • v)) (𝓝 w) (𝓝 (γ w, γ w)) := by
    have hcont : ContinuousAt (fun t => (γ t, γ t - g t • v)) w :=
      hγ.continuousAt.prodMk (hγ.continuousAt.sub
        (((ℓ.continuous.continuousAt.comp hγ.continuousAt).sub continuousAt_const).smul
          continuousAt_const))
    simpa [hgw] using hcont.tendsto
  have hHq : ∀ᶠ t in 𝓝 w, H (γ t - g t • v) = 0 := by
    filter_upwards [(continuous_snd.tendsto _).comp hq |>.eventually hzero] with t ht
    exact ht (by simp [g, hv])
  -- strict differentiability: `H (γ t) - H (q t) = c * g t + o (g t)`
  have hsmall : (fun t => H (γ t) - c * g t) =o[𝓝 w] g := by
    have ho := hH.hasStrictFDerivAt.isLittleO.comp_tendsto hq
    have hO : (fun t => γ t - (γ t - g t • v)) =O[𝓝 w] g :=
      IsBigO.of_bound ‖v‖ (Eventually.of_forall fun t => by simp [norm_smul, mul_comm])
    refine (ho.trans_isBigO hO).congr' ?_ EventuallyEq.rfl
    filter_upwards [hHq] with t ht
    simp [ht, hD, hv, mul_comm]
  have hΘ : (fun t => H (γ t)) =Θ[𝓝 w] g := by
    have h := hsmall.add_isTheta ((isTheta_const_mul_left hc).2 (isTheta_refl g (𝓝 w)))
    simpa only [Pi.add_def, sub_add_cancel] using h
  exact (hH.comp hγ).analyticOrderAt_eq_of_isTheta
    (((ℓ.analyticAt _).comp hγ).sub analyticAt_const) hΘ

end TauCeti

end

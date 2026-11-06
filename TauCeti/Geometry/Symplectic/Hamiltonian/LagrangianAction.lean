/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Variation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The action of a Lagrangian and the principle of stationary action

Let `E` be a real normed space, the configuration space of a mechanical system, and let
`L : ℝ → E × E → ℝ` be a possibly time-dependent Lagrangian, a function `L t (q, v)` of time,
positions and velocities. The **action** of a curve `q : ℝ → E` between the times `a` and `b` is

`S(q) = ∫_a^b L(t, q(t), q'(t)) dt` (`TauCeti.lagrangianAction`).

A variation of `q` is a two-parameter family `Q s t` with `Q 0 = q`, and its variation field is
`η(t) = ∂_s Q(0, t)`. This file computes the derivative of the action along a variation. When the
uncurried family `(s, t) ↦ Q s t` is `C²` and `L` is `C¹` along `q`, differentiation under the
integral sign and the symmetry of the mixed partial derivatives of `Q` give

`d/ds S(Q s)|₀ = ∫_a^b DL_t(q, q')(η, η') dt` (`TauCeti.hasDerivAt_lagrangianAction`),

the integral of the derivative of `L` along the first prolongation `(η, η')` of the variation
field. Along a `C¹` curve `q`, the force `∂_q L(t, q, q')` is continuous
(`TauCeti.continuousAt_force`). When `L` is moreover `C²`, the momentum `p(t) = ∂_v L(t, q, q')` is
`C¹` (`TauCeti.contDiffAt_momentum`), and an integration by parts produces the **first variation
formula with its endpoint boundary term**

`d/ds S(Q s)|₀ = p(b)(η(b)) - p(a)(η(a)) + ∫_a^b (∂_q L(t, q, q') - p'(t))(η(t)) dt`

(`TauCeti.hasDerivAt_lagrangianAction_of_contDiffAt_two`). For a variation with fixed endpoints
(`TauCeti.Manifold.IsFixedEndpointVariation`, in the normed space `E`) the variation field vanishes
at `a` and `b`, so only the integral of the Euler–Lagrange expression `∂_q L - p'` remains
(`TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_lagrangianAction`).

A curve is a **stationary point of the action** among `C^n` variations
(`TauCeti.IsActionStationary`) when it is `C^n` on `[a, b]` and the action of every `C^n`
variation with fixed endpoints has derivative zero at `s = 0`. **Hamilton's principle of
stationary action** says that, for `2 ≤ n ≤ ∞`, a `C^n` curve along which `L` is `C²` is
stationary exactly when it solves the Euler–Lagrange equations

`d/dt ∂_v L(t, q, q') = ∂_q L(t, q, q')`

on the open interval between `a` and `b` (`TauCeti.isActionStationary_iff_eulerLagrange`). The
forward direction tests the first variation formula against the variations
`q + s ψ e`, with `ψ` a smooth function supported in the open interval and `e ∈ E`, and applies the
fundamental lemma of the calculus of variations
(`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`). The Euler–Lagrange equations are stated
in the form of the hypothesis of Noether's theorem `TauCeti.hasDerivAt_noetherCharge`, with the
velocity `deriv q`, so stationary curves feed it directly.

No finite dimensionality of `E` is needed, and the endpoints `a` and `b` may come in either order.
When `a = b` every curve that is `C^n` at `a` is stationary and the open interval is empty.

The structure of the variation computation, and of the stationarity predicate carrying the
regularity of the curve as a field, follows the Riemannian first variation of energy
`TauCeti.Manifold.hasDerivAt_energy` and `TauCeti.Manifold.IsEnergyCritical` in
`TauCeti.Geometry.Manifold.Riemannian.FirstVariation`.

## Main definitions

* `TauCeti.lagrangianAction L q a b`: the action `∫_a^b L(t, q(t), q'(t)) dt`.
* `TauCeti.IsActionStationary n L q a b`: `q` is a stationary point of the action among `C^n`
  variations with fixed endpoints.

## Main results

* `TauCeti.contDiffAt_momentum`, `TauCeti.continuousAt_force`: regularity of the momentum along a
  `C²` curve and of the force along a `C¹` curve.
* `TauCeti.hasDerivAt_lagrangianAction`: the derivative of the action along a variation.
* `TauCeti.hasDerivAt_lagrangianAction_of_contDiffAt_two`: the first variation formula with the
  endpoint boundary term.
* `TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_lagrangianAction`: the first variation
  formula for a variation with fixed endpoints.
* `TauCeti.isActionStationary_iff_eulerLagrange`: Hamilton's principle of stationary action.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 12.
* I. M. Gelfand, S. V. Fomin, *Calculus of Variations*, Prentice–Hall, 1963, Sections 3 and 4.
* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Section 8.1.
-/

public section

open ContinuousLinearMap Filter Function MeasureTheory Set
open scoped ContDiff Interval Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The action -/

/-- The **action** of a time-dependent Lagrangian `L` along a curve `q` between the times `a` and
`b`: the integral `∫_a^b L(t, q(t), q'(t)) dt`. -/
noncomputable def lagrangianAction (L : ℝ → E × E → ℝ) (q : ℝ → E) (a b : ℝ) : ℝ :=
  ∫ t in a..b, L t (q t, deriv q t)

theorem lagrangianAction_def (L : ℝ → E × E → ℝ) (q : ℝ → E) (a b : ℝ) :
    lagrangianAction L q a b = ∫ t in a..b, L t (q t, deriv q t) :=
  (rfl)

@[simp]
theorem lagrangianAction_same (L : ℝ → E × E → ℝ) (q : ℝ → E) (a : ℝ) :
    lagrangianAction L q a a = 0 :=
  intervalIntegral.integral_same

theorem lagrangianAction_symm (L : ℝ → E × E → ℝ) (q : ℝ → E) (a b : ℝ) :
    lagrangianAction L q b a = -lagrangianAction L q a b :=
  intervalIntegral.integral_symm a b

/-- The action is additive over consecutive time intervals. -/
theorem lagrangianAction_add_lagrangianAction {L : ℝ → E × E → ℝ} {q : ℝ → E} {a b c : ℝ}
    (hab : IntervalIntegrable (fun t ↦ L t (q t, deriv q t)) volume a b)
    (hbc : IntervalIntegrable (fun t ↦ L t (q t, deriv q t)) volume b c) :
    lagrangianAction L q a b + lagrangianAction L q b c = lagrangianAction L q a c :=
  intervalIntegral.integral_add_adjacent_intervals hab hbc

/-! ### The momentum and the force along a curve -/

section Curve

variable {L : ℝ → E × E → ℝ} {q : ℝ → E} {t : ℝ}

/-- Along a `C²` curve, where `L` is `C²`, the momentum `t ↦ ∂_v L(t, q, q')` is `C¹`. -/
theorem contDiffAt_momentum (hq : ContDiffAt ℝ 2 q t)
    (hL : ContDiffAt ℝ 2 (uncurry L) (t, (q t, deriv q t))) :
    ContDiffAt ℝ 1 (fun r ↦ fderiv ℝ (fun u ↦ L r (q r, u)) (deriv q r)) t := by
  refine ContDiffAt.fderiv (f := fun r u ↦ L r (q r, u)) ?_
    (hq.derivWithin le_rfl) le_rfl
  exact hL.comp (t, deriv q t)
    (contDiffAt_fst.prodMk ((hq.comp _ contDiffAt_fst).prodMk contDiffAt_snd))

/-- Along a `C¹` curve, where `L` is `C¹`, the force `t ↦ ∂_q L(t, q, q')` is continuous. -/
theorem continuousAt_force (hq : ContDiffAt ℝ 1 q t)
    (hL : ContDiffAt ℝ 1 (uncurry L) (t, (q t, deriv q t))) :
    ContinuousAt (fun r ↦ fderiv ℝ (fun y ↦ L r (y, deriv q r)) (q r)) t := by
  -- The partial derivative of `L` in position is continuous in `(t, q, v)`; compose it with the
  -- continuous curve `t ↦ (t, q, q')`.
  have hF : ContinuousAt (fun z : ℝ × E × E ↦ fderiv ℝ (fun y ↦ L z.1 (y, z.2.2)) z.2.1)
      (t, (q t, deriv q t)) :=
    (ContDiffAt.fderiv (f := fun z y ↦ L z.1 (y, z.2.2)) (m := 0)
      (hL.comp ((t, (q t, deriv q t)), q t)
        (contDiffAt_fst.fst.prodMk (contDiffAt_snd.prodMk contDiffAt_fst.snd.snd)))
      contDiffAt_snd.fst le_rfl).continuousAt
  exact hF.comp (f := fun r ↦ (r, (q r, deriv q r)))
    (continuousAt_id.prodMk (hq.continuousAt.prodMk (hq.derivWithin (m := 0) le_rfl).continuousAt))

end Curve

/-! ### The first variation of the action -/

variable {L : ℝ → E × E → ℝ} {Q : ℝ → ℝ → E} {a b : ℝ}

/-- **The derivative of the action along a variation.** Let the uncurried family
`(s, t) ↦ Q s t` be `C²` at every point of `{0} × [a, b]`, and let `L` be jointly `C¹` in time,
position and velocity along the central curve `Q 0`. Then the action of `Q s` between `a` and `b`
is differentiable at `s = 0`, with derivative the integral of the derivative of `L` along the first
prolongation `(η, η')` of the variation field `η(t) = ∂_s Q(0, t)`. -/
theorem hasDerivAt_lagrangianAction
    (hQ : ∀ t ∈ uIcc a b, ContDiffAt ℝ 2 (uncurry Q) (0, t))
    (hL : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 (uncurry L) (t, (Q 0 t, deriv (Q 0) t))) :
    HasDerivAt (fun s ↦ lagrangianAction L (Q s) a b)
      (∫ t in a..b, fderiv ℝ (L t) (Q 0 t, deriv (Q 0) t)
        (deriv (fun s ↦ Q s t) 0, deriv (fun r ↦ deriv (fun s ↦ Q s r) 0) t)) 0 := by
  -- The integrand of the action of `Q s` is `L ∘ ι`, with the velocity written through the
  -- partial derivative of the family in the curve parameter, so that it is jointly `C¹`.
  obtain ⟨ι, hι⟩ : ∃ ι : ℝ × ℝ → ℝ × (E × E),
      ι = fun z ↦ (z.2, (uncurry Q z, fderiv ℝ (uncurry Q) z (0, 1))) := ⟨_, rfl⟩
  have hιapp : ∀ {s t : ℝ}, DifferentiableAt ℝ (uncurry Q) (s, t) →
      ι (s, t) = (t, (Q s t, deriv (Q s) t)) := fun {s t} h ↦ by
    have hQs : HasDerivAt (Q s) (fderiv ℝ (uncurry Q) (s, t) (0, 1)) t :=
      hasDerivAt_slice_right h
    simp only [hι, hQs.deriv, uncurry_apply_pair]
  have hιt : ∀ t ∈ uIcc a b, ι (0, t) = (t, (Q 0 t, deriv (Q 0) t)) := fun t ht ↦
    hιapp ((hQ t ht).differentiableAt two_ne_zero)
  have hG : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 (uncurry L ∘ ι) (0, t) := by
    intro t ht
    have hιc : ContDiffAt ℝ 1 ι (0, t) := by
      rw [hι]
      exact contDiffAt_snd.prodMk (((hQ t ht).of_le one_le_two).prodMk
        (((hQ t ht).fderiv_right (m := 1) le_rfl).clm_apply contDiffAt_const))
    exact ContDiffAt.comp (0, t) (hιt t ht ▸ hL t ht) hιc
  -- Differentiation under the integral sign, on the open set where the integrand is `C¹`.
  have hWo : IsOpen {z : ℝ × ℝ | ContDiffAt ℝ 1 (uncurry L ∘ ι) z} :=
    isOpen_iff_mem_nhds.2 fun z hz ↦ hz.eventually (by simp)
  obtain ⟨-, hGderiv⟩ := hasDerivAt_intervalIntegral_of_contDiffOn hWo
    (fun z hz ↦ (hz : ContDiffAt ℝ 1 (uncurry L ∘ ι) z).contDiffWithinAt) (x₀ := 0)
    (by rintro ⟨s, t⟩ ⟨hs, ht⟩; obtain rfl : s = 0 := hs; exact hG t ht)
  -- Near `s = 0`, the action of `Q s` is the integral of the integrand at `s`.
  have hVo : IsOpen {z : ℝ × ℝ | ContDiffAt ℝ 2 (uncurry Q) z} :=
    isOpen_iff_mem_nhds.2 fun z hz ↦ hz.eventually (by simp)
  obtain ⟨U, V, hUo, -, h0U, hV, hUV⟩ := generalized_tube_lemma isCompact_singleton
    isCompact_uIcc hVo (by rintro ⟨s, t⟩ ⟨hs, ht⟩; obtain rfl : s = 0 := hs; exact hQ t ht)
  have haction : (fun s ↦ lagrangianAction L (Q s) a b) =ᶠ[𝓝 0]
      fun s ↦ ∫ t in a..b, (uncurry L ∘ ι) (s, t) := by
    filter_upwards [hUo.mem_nhds (h0U rfl)] with s hs
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    have hst : ContDiffAt ℝ 2 (uncurry Q) (s, t) := hUV ⟨hs, hV ht⟩
    simp only [Function.comp_apply, hιapp (hst.differentiableAt two_ne_zero), uncurry_apply_pair]
  refine (hGderiv.congr_of_eventuallyEq haction).congr_deriv
    (intervalIntegral.integral_congr fun t ht ↦ ?_)
  -- Pointwise, the derivative of the integrand in `s` is computed by the chain rule along
  -- `s ↦ (s, t)`; the symmetry of the second derivative of the family identifies the result.
  have hQt := hQ t ht
  have hD : DifferentiableAt ℝ (fderiv ℝ (uncurry Q)) (0, t) :=
    (hQt.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hpath : HasDerivAt (fun s : ℝ ↦ (s, t)) ((1 : ℝ), (0 : ℝ)) 0 := hasDerivAt_prodMk_left 0 t
  have hη : HasDerivAt (fun s ↦ Q s t) (fderiv ℝ (uncurry Q) (0, t) (1, 0)) 0 := by
    simpa only [timeFDeriv_apply, uncurry_apply_pair] using
      hasDerivAt_parameterCurve (hQt.differentiableAt two_ne_zero)
  have hcurve : HasDerivAt (fun s ↦ ι (s, t))
      ((0 : ℝ), (fderiv ℝ (uncurry Q) (0, t) (1, 0),
        fderiv ℝ (fderiv ℝ (uncurry Q)) (0, t) (1, 0) (0, 1))) 0 := by
    have hΦ := hasDerivAt_fderiv_apply_fst hD ((0 : ℝ), (1 : ℝ))
    rw [hι]
    exact HasDerivAt.prodMk (hasDerivAt_const 0 t) (HasDerivAt.prodMk hη hΦ)
  have hLd : DifferentiableAt ℝ (uncurry L) (t, (Q 0 t, deriv (Q 0) t)) :=
    (hL t ht).differentiableAt one_ne_zero
  have hGs : HasDerivAt (fun s ↦ (uncurry L ∘ ι) (s, t))
      (fderiv ℝ (uncurry L) (ι (0, t)) ((0 : ℝ), (fderiv ℝ (uncurry Q) (0, t) (1, 0),
        fderiv ℝ (fderiv ℝ (uncurry Q)) (0, t) (1, 0) (0, 1)))) 0 :=
    (hιt t ht ▸ hLd).hasFDerivAt.comp_hasDerivAt 0 hcurve
  have hGs' : HasDerivAt (fun s ↦ (uncurry L ∘ ι) (s, t))
      (fderiv ℝ (uncurry L ∘ ι) (0, t) (1, 0)) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ ↦ (s, t)) 0
      ((hG t ht).differentiableAt one_ne_zero).hasFDerivAt hpath
  have hslice : fderiv ℝ (L t) (Q 0 t, deriv (Q 0) t) =
      (fderiv ℝ (uncurry L) (t, (Q 0 t, deriv (Q 0) t))).comp (inr ℝ ℝ (E × E)) :=
    fderiv_slice_right hLd
  have hη' : deriv (fun r ↦ deriv (fun s ↦ Q s r) 0) t =
      fderiv ℝ (fderiv ℝ (uncurry Q)) (0, t) (1, 0) (0, 1) :=
    deriv_deriv_slice_left hQt (by simp)
  rw [hGs'.unique hGs, hslice, hιt t ht, hη.deriv, hη', coe_comp, Function.comp_apply, inr_apply]

/-- **The first variation formula, with the endpoint boundary term.** Let the uncurried family
`(s, t) ↦ Q s t` be `C²` at every point of `{0} × [a, b]`, and let `L` be jointly `C²` along the
central curve `q = Q 0`. Then the action of `Q s` between `a` and `b` is differentiable at `s = 0`,
with derivative

`p(b)(η(b)) - p(a)(η(a)) + ∫_a^b (∂_q L(t, q, q') - p'(t))(η(t)) dt`,

where `η(t) = ∂_s Q(0, t)` is the variation field and `p(t) = ∂_v L(t, q, q')` the momentum. -/
theorem hasDerivAt_lagrangianAction_of_contDiffAt_two
    (hQ : ∀ t ∈ uIcc a b, ContDiffAt ℝ 2 (uncurry Q) (0, t))
    (hL : ∀ t ∈ uIcc a b, ContDiffAt ℝ 2 (uncurry L) (t, (Q 0 t, deriv (Q 0) t))) :
    HasDerivAt (fun s ↦ lagrangianAction L (Q s) a b)
      (fderiv ℝ (fun u ↦ L b (Q 0 b, u)) (deriv (Q 0) b) (deriv (fun s ↦ Q s b) 0) -
        fderiv ℝ (fun u ↦ L a (Q 0 a, u)) (deriv (Q 0) a) (deriv (fun s ↦ Q s a) 0) +
        ∫ t in a..b, (fderiv ℝ (fun y ↦ L t (y, deriv (Q 0) t)) (Q 0 t) -
          deriv (fun r ↦ fderiv ℝ (fun u ↦ L r (Q 0 r, u)) (deriv (Q 0) r)) t)
            (deriv (fun s ↦ Q s t) 0)) 0 := by
  refine (hasDerivAt_lagrangianAction hQ fun t ht ↦ (hL t ht).of_le one_le_two).congr_deriv ?_
  have hq : ∀ t ∈ uIcc a b, ContDiffAt ℝ 2 (Q 0) t := fun t ht ↦
    (hQ t ht).comp t (contDiff_prodMk_right (0 : ℝ)).contDiffAt
  have hp : ∀ t ∈ uIcc a b,
      ContDiffAt ℝ 1 (fun r ↦ fderiv ℝ (fun u ↦ L r (Q 0 r, u)) (deriv (Q 0) r)) t :=
    fun t ht ↦ contDiffAt_momentum (hq t ht) (hL t ht)
  have hη : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 (fun r ↦ deriv (fun s ↦ Q s r) 0) t :=
    fun t ht ↦ contDiffAt_deriv_slice_left (n := 1) (hQ t ht)
  -- The product `p(t)(η(t))` has derivative `p'(t)(η(t)) + p(t)(η'(t))`, which is continuous.
  have hFTC : ∀ t ∈ uIcc a b, HasDerivAt
      (fun r ↦ fderiv ℝ (fun u ↦ L r (Q 0 r, u)) (deriv (Q 0) r) (deriv (fun s ↦ Q s r) 0))
      (deriv (fun r ↦ fderiv ℝ (fun u ↦ L r (Q 0 r, u)) (deriv (Q 0) r)) t
          (deriv (fun s ↦ Q s t) 0) +
        fderiv ℝ (fun u ↦ L t (Q 0 t, u)) (deriv (Q 0) t)
          (deriv (fun r ↦ deriv (fun s ↦ Q s r) 0) t)) t := fun t ht ↦
    ((hp t ht).differentiableAt one_ne_zero).hasDerivAt.clm_apply
      ((hη t ht).differentiableAt one_ne_zero).hasDerivAt
  have hint₁ : IntervalIntegrable (fun t ↦ (fderiv ℝ (fun y ↦ L t (y, deriv (Q 0) t)) (Q 0 t) -
      deriv (fun r ↦ fderiv ℝ (fun u ↦ L r (Q 0 r, u)) (deriv (Q 0) r)) t)
        (deriv (fun s ↦ Q s t) 0)) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      (((continuousAt_force ((hq t ht).of_le one_le_two) ((hL t ht).of_le one_le_two)).sub
        (((hp t ht).derivWithin (m := 0) (by norm_num)).continuousAt)).clm_apply
          (hη t ht).continuousAt).continuousWithinAt
  have hint₂ : IntervalIntegrable (fun t ↦
      deriv (fun r ↦ fderiv ℝ (fun u ↦ L r (Q 0 r, u)) (deriv (Q 0) r)) t
          (deriv (fun s ↦ Q s t) 0) +
        fderiv ℝ (fun u ↦ L t (Q 0 t, u)) (deriv (Q 0) t)
          (deriv (fun r ↦ deriv (fun s ↦ Q s r) 0) t)) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      ((((hp t ht).derivWithin (m := 0) (by norm_num)).continuousAt.clm_apply
        (hη t ht).continuousAt).add
        ((hp t ht).continuousAt.clm_apply
          (((hη t ht).derivWithin (m := 0) (by norm_num)).continuousAt))).continuousWithinAt
  -- Split the integrand into the Euler–Lagrange term and the derivative of `p(t)(η(t))`.
  rw [intervalIntegral.integral_congr (g := fun t ↦
      (fderiv ℝ (fun y ↦ L t (y, deriv (Q 0) t)) (Q 0 t) -
        deriv (fun r ↦ fderiv ℝ (fun u ↦ L r (Q 0 r, u)) (deriv (Q 0) r)) t)
          (deriv (fun s ↦ Q s t) 0) +
      (deriv (fun r ↦ fderiv ℝ (fun u ↦ L r (Q 0 r, u)) (deriv (Q 0) r)) t
          (deriv (fun s ↦ Q s t) 0) +
        fderiv ℝ (fun u ↦ L t (Q 0 t, u)) (deriv (Q 0) t)
          (deriv (fun r ↦ deriv (fun s ↦ Q s r) 0) t))) fun t ht ↦ ?_,
    intervalIntegral.integral_add hint₁ hint₂,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hFTC hint₂]
  · ring
  · have hLt : DifferentiableAt ℝ (L t) (Q 0 t, deriv (Q 0) t) :=
      ((hL t ht).differentiableAt two_ne_zero).comp (Q 0 t, deriv (Q 0) t)
        ((differentiableAt_const t).prodMk differentiableAt_id)
    simp only [fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right hLt, sub_apply]
    ring

/-- **The first variation formula for a variation with fixed endpoints.** For a `C²` variation `Q`
of `q = Q 0` with fixed endpoints between `a` and `b`, along which `L` is `C²`, the derivative at
`s = 0` of the action of `Q s` is the integral of the Euler–Lagrange expression
`∂_q L(t, q, q') - d/dt ∂_v L(t, q, q')` against the variation field `η(t) = ∂_s Q(0, t)`. -/
theorem Manifold.IsFixedEndpointVariation.hasDerivAt_lagrangianAction
    (hQ : Manifold.IsFixedEndpointVariation 𝓘(ℝ, E) 2 Q a b)
    (hL : ∀ t ∈ uIcc a b, ContDiffAt ℝ 2 (uncurry L) (t, (Q 0 t, deriv (Q 0) t))) :
    HasDerivAt (fun s ↦ lagrangianAction L (Q s) a b)
      (∫ t in a..b, (fderiv ℝ (fun y ↦ L t (y, deriv (Q 0) t)) (Q 0 t) -
          deriv (fun r ↦ fderiv ℝ (fun u ↦ L r (Q 0 r, u)) (deriv (Q 0) r)) t)
            (deriv (fun s ↦ Q s t) 0)) 0 := by
  have hQ' : ∀ t ∈ uIcc a b, ContDiffAt ℝ 2 (uncurry Q) (0, t) := fun t ht ↦
    contMDiffAt_iff_contDiffAt.mp (hQ.contMDiffAt t ht)
  refine (hasDerivAt_lagrangianAction_of_contDiffAt_two hQ' hL).congr_deriv ?_
  have ha : (fun s ↦ Q s a) =ᶠ[𝓝 0] fun _ ↦ Q 0 a := hQ.eventually_apply_left
  have hb : (fun s ↦ Q s b) =ᶠ[𝓝 0] fun _ ↦ Q 0 b := hQ.eventually_apply_right
  rw [ha.deriv_eq, hb.deriv_eq]
  simp

/-! ### Hamilton's principle of stationary action -/

/-- A curve `q` is a **stationary point of the action** of `L` among `C^n` variations between the
times `a` and `b` when it is `C^n` at every point of `[a, b]` and every `C^n` variation of `q` with
fixed endpoints (`TauCeti.Manifold.IsFixedEndpointVariation`, in the normed space `E`) leaves the
action stationary to first order: the action of `Q s` has derivative `0` at `s = 0`. The regularity
of `q` is part of the definition, since a curve which is not `C^n` admits no `C^n` variation. -/
structure IsActionStationary (n : WithTop ℕ∞) (L : ℝ → E × E → ℝ) (q : ℝ → E) (a b : ℝ) :
    Prop where
  /-- A stationary point of the action among `C^n` variations is `C^n` on `[a, b]`. -/
  contDiffAt : ∀ t ∈ uIcc a b, ContDiffAt ℝ n q t
  /-- The action of a `C^n` fixed-endpoint variation of a stationary point has derivative `0` at
  `s = 0`. -/
  hasDerivAt : ∀ {Q : ℝ → ℝ → E}, Q 0 = q → Manifold.IsFixedEndpointVariation 𝓘(ℝ, E) n Q a b →
    HasDerivAt (fun s ↦ lagrangianAction L (Q s) a b) 0 0

variable {n : WithTop ℕ∞} {q : ℝ → E}

/-- Testing stationarity against the fixed-endpoint variations `q + s ψ e`, for a smooth `ψ`
supported in the open interval between `a` and `b` and a direction `e`, shows that the
Euler–Lagrange expression of `q` in the direction `e` integrates to zero against `ψ`. -/
private theorem integral_smul_eulerLagrange_eq_zero (h : IsActionStationary n L q a b)
    (hn : 2 ≤ n) (hn' : n ≤ ∞)
    (hL : ∀ t ∈ uIcc a b, ContDiffAt ℝ 2 (uncurry L) (t, (q t, deriv q t))) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ uIoo a b) (e : E) :
    ∫ t in a..b, ψ t • (fderiv ℝ (fun y ↦ L t (y, deriv q t)) (q t) -
      deriv (fun r ↦ fderiv ℝ (fun u ↦ L r (q r, u)) (deriv q r)) t) e = 0 := by
  have hψ0 : ∀ x ∉ uIoo a b, ψ x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hψU h)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ → ℝ → E, Q = fun s t ↦ q t + s • (ψ t • e) := ⟨_, rfl⟩
  have hQ0 : Q 0 = q := by
    rw [hQ]
    funext t
    simp
  have hη : ∀ t, deriv (fun s ↦ Q s t) 0 = ψ t • e := fun t ↦ by
    simp only [hQ]
    simpa using (((hasDerivAt_id' (0 : ℝ)).smul_const (ψ t • e)).const_add (q t)).deriv
  have hvar : Manifold.IsFixedEndpointVariation 𝓘(ℝ, E) n Q a b := by
    refine ⟨fun t ht ↦ contMDiffAt_iff_contDiffAt.mpr ?_, .of_forall fun s ↦ ?_,
      .of_forall fun s ↦ ?_⟩
    · rw [hQ]
      exact ((h.contDiffAt t ht).comp (0, t) contDiffAt_snd).add (contDiffAt_fst.smul
        (((hψ.of_le hn').contDiffAt.comp (0, t) contDiffAt_snd).smul contDiffAt_const))
    · simp [hQ, hψ0 a left_notMem_uIoo]
    · simp [hQ, hψ0 b right_notMem_uIoo]
  have hform := (hvar.of_le hn).hasDerivAt_lagrangianAction (L := L) (by rw [hQ0]; exact hL)
  rw [hQ0] at hform
  simp only [hη] at hform
  rw [← hform.unique (h.hasDerivAt hQ0 hvar)]
  exact intervalIntegral.integral_congr fun t _ ↦ by simp

/-- **Hamilton's principle of stationary action.** For `2 ≤ n ≤ ∞`, let `q` be `C^n` at every
point of `[a, b]` and let `L` be jointly `C²` along `q`. Then `q` is a stationary point of the
action of `L` among `C^n` variations with fixed endpoints between `a` and `b` exactly when it
solves the Euler–Lagrange equations `d/dt ∂_v L(t, q, q') = ∂_q L(t, q, q')` at every time strictly
between `a` and `b`. -/
theorem isActionStationary_iff_eulerLagrange (hn : 2 ≤ n) (hn' : n ≤ ∞)
    (hq : ∀ t ∈ uIcc a b, ContDiffAt ℝ n q t)
    (hL : ∀ t ∈ uIcc a b, ContDiffAt ℝ 2 (uncurry L) (t, (q t, deriv q t))) :
    IsActionStationary n L q a b ↔ ∀ t ∈ uIoo a b,
      HasDerivAt (fun s ↦ fderiv ℝ (fun u ↦ L s (q s, u)) (deriv q s))
        (fderiv ℝ (fun y ↦ L t (y, deriv q t)) (q t)) t := by
  have hq₂ : ∀ t ∈ uIcc a b, ContDiffAt ℝ 2 q t := fun t ht ↦ (hq t ht).of_le hn
  have hp : ∀ t ∈ uIcc a b,
      ContDiffAt ℝ 1 (fun r ↦ fderiv ℝ (fun u ↦ L r (q r, u)) (deriv q r)) t :=
    fun t ht ↦ contDiffAt_momentum (hq₂ t ht) (hL t ht)
  constructor
  · intro h t₀ ht₀
    -- It suffices that the Euler–Lagrange expression vanishes at `t₀` in every direction `e`.
    suffices hres : ∀ e : E, (fderiv ℝ (fun y ↦ L t₀ (y, deriv q t₀)) (q t₀) -
        deriv (fun r ↦ fderiv ℝ (fun u ↦ L r (q r, u)) (deriv q r)) t₀) e = 0 by
      refine ((hp t₀ (uIoo_subset_uIcc_self ht₀)).differentiableAt
        one_ne_zero).hasDerivAt.congr_deriv ?_
      exact (sub_eq_zero.mp (ContinuousLinearMap.ext hres)).symm
    intro e
    obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun t ↦ (fderiv ℝ (fun y ↦ L t (y, deriv q t)) (q t) -
        deriv (fun r ↦ fderiv ℝ (fun u ↦ L r (q r, u)) (deriv q r)) t) e := ⟨_, rfl⟩
    have hgcont : ContinuousOn g (uIoo a b) := fun t ht ↦ by
      have ht' := uIoo_subset_uIcc_self ht
      rw [hg]
      exact (((continuousAt_force ((hq₂ t ht').of_le one_le_two) ((hL t ht').of_le one_le_two)).sub
        ((hp t ht').derivWithin (m := 0) (by norm_num)).continuousAt).clm_apply
          continuousAt_const).continuousWithinAt
    -- The integrals of `g` against test functions on the open interval vanish.
    have htest : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ uIoo a b →
        ∫ x, ψ x • g x = 0 := by
      intro ψ hψ _ hψU
      have h₁ : ∫ x in a..b, ψ x • g x = 0 := by
        rw [hg]
        exact integral_smul_eulerLagrange_eq_zero h hn hn' hL hψ hψU e
      have h₂ := intervalIntegral.abs_integral_eq_abs_integral_uIoc (fun x ↦ ψ x • g x)
        (a := a) (b := b) (μ := volume)
      rw [h₁, abs_zero, eq_comm, abs_eq_zero] at h₂
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_, h₂]
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx (Ioo_subset_Ioc_self (hψU h)), zero_smul]
    -- By the fundamental lemma of the calculus of variations, `g` vanishes on the open interval.
    have hae := (isOpen_Ioo : IsOpen (uIoo a b)).ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hgcont.locallyIntegrableOn measurableSet_Ioo) htest
    have hEq := Measure.eqOn_open_of_ae_eq (f := g) (g := 0)
      ((ae_restrict_iff' measurableSet_Ioo).mpr hae) isOpen_Ioo hgcont continuousOn_const ht₀
    simpa [hg] using hEq
  · intro hEL
    refine ⟨hq, fun {Q} hQ0 hQ ↦ ?_⟩
    subst hQ0
    refine ((hQ.of_le hn).hasDerivAt_lagrangianAction hL).congr_deriv ?_
    refine intervalIntegral.integral_zero_ae ?_
    filter_upwards [(Ioo_ae_eq_Ioc (μ := volume) (a := a ⊓ b) (b := a ⊔ b)).mem_iff] with t ht htI
    rw [(hEL t (ht.mpr htI)).deriv, sub_self, zero_apply]

end TauCeti

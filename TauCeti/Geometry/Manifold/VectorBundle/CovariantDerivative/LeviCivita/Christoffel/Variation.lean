/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.Calculus.ParametricFDeriv
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Variation of the Christoffel symbols of a family of metrics

Let `g : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ` be a one-parameter family of fields of bilinear forms on a
finite-dimensional real normed space `E`, as a family of metrics `g_t` reads in a chart, and let
`h = ∂ₜ g` be its parameter derivative at `t`. No positivity is assumed. This file computes the
parameter derivative of the Christoffel symbols of `g_t`.

For the Christoffel symbols of the first kind the variation is linear: `∂ₜ Γ₁(g) = Γ₁(h)`. This
is where the joint `C²` regularity of `(t, x) ↦ g_t(x)` is used, to commute the parameter
derivative with the spatial derivative of the metric. Raising the index with the nondegenerate
metric `g_t(x)` then gives, for `Γ` the Christoffel symbols of the second kind of `g_t`,

`g(∂ₜΓ(u, v), w) = Γ₁(h)(u, v)(w) - h(Γ(u, v), w)`.

When `g` is symmetric, this is the coordinate form of the variation formula for the Levi-Civita
connection: writing `(∇_u h)(v, w) = Dh(u)(v, w) - h(Γ(u, v), w) - h(v, Γ(u, w))` for the
covariant derivative of `h` in linear coordinates,

`2 g(∂ₜΓ(u, v), w) = (∇_u h)(v, w) + (∇_v h)(u, w) - (∇_w h)(u, v)`.

For vector fields independent of `t`, the parameter derivative of `∇_X Y = DY(X) + Γ(X, Y)` is
`∂ₜΓ(X, Y)`, so this is the identity `2 g((∂ₜ∇)_X Y, Z) = (∇_X h)(Y, Z) + (∇_Y h)(X, Z) -
(∇_Z h)(X, Y)` read in a chart.

## Main results

* `TauCeti.Manifold.hasDerivAt_christoffelFirstKind_family`: the variation of the Christoffel
  symbols of the first kind is the Christoffel symbols of the first kind of `h`.
* `TauCeti.Manifold.hasDerivAt_christoffelSecondKind_family`: the variation of the Christoffel
  symbols of the second kind at a point where the metric is nondegenerate.
* `TauCeti.Manifold.two_mul_apply_deriv_christoffelSecondKind_family`: the variation formula in
  terms of the covariant derivative of `h`.

The commutation of the parameter and spatial derivatives is `hasDerivAt_spatialFDeriv`, a
consequence of the symmetry of second derivatives.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.K, Theorem 1.174: the first
  variation of the Levi-Civita connection.
* B. Chow and D. Knopf, *The Ricci Flow: An Introduction*, AMS (2004), Chapter 3, Lemma 3.2: the
  variation of the Christoffel symbols in index notation.
-/

public section

noncomputable section

open Filter ContinuousLinearMap
open scoped Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {g : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ} {t : ℝ} {x : E}

/-- **The variation of the Christoffel symbols of the first kind.** For a jointly `C²` family of
fields of bilinear forms `g_t`, the parameter derivative of the Christoffel symbols of the first
kind of `g_t` is the Christoffel symbols of the first kind of the parameter derivative
`h = ∂ₜ g`. -/
theorem hasDerivAt_christoffelFirstKind_family (hg : ContDiffAt ℝ 2 (Function.uncurry g) (t, x))
    (u v : E) :
    HasDerivAt (fun s ↦ christoffelFirstKind (g s) x u v)
      (christoffelFirstKind (fun y ↦ deriv (fun s ↦ g s y) t) x u v) t := by
  set F := Function.uncurry g
  -- The scalar coefficient `(s, y) ↦ g_s(y)(u, v)`, whose spatial derivative is the last term.
  set G : ℝ × E → ℝ := fun p ↦ F p u v
  have hG : ContDiffAt ℝ 2 G (t, x) := (hg.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  have hdiff : ∀ᶠ p in 𝓝 (t, x), DifferentiableAt ℝ F p :=
    (hg.eventually (by simp)).mono fun _ hp ↦ hp.differentiableAt two_ne_zero
  -- Near `t`, the Christoffel symbols of `g_s` are built from spatial derivatives of `F` and `G`.
  have hslice : (fun s ↦ christoffelFirstKind (g s) x u v) =ᶠ[𝓝 t]
      fun s ↦ (2⁻¹ : ℝ) • (spatialFDeriv F x s u v + spatialFDeriv F x s v u -
        spatialFDeriv G x s) := by
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually hdiff] with s hs
    rw [id_eq] at hs
    have hGs : DifferentiableAt ℝ G (s, x) :=
      (hs.clm_apply (differentiableAt_const u)).clm_apply (differentiableAt_const v)
    have hgs : DifferentiableAt ℝ (g s) x := by
      simpa [F, Function.uncurry_apply_pair] using
        (hasFDerivAt_timeSlice (F := F) hs).differentiableAt
    rw [christoffelFirstKind_eq_of_differentiableAt hgs, ← fderiv_timeSlice (F := F) hs,
      ← fderiv_timeSlice (F := G) hGs]
    simp only [F, G, Function.uncurry_apply_pair]
  -- Near `x`, the parameter derivative of `g` is the parameter part of the joint derivative.
  have htime : (fun y ↦ deriv (fun s ↦ g s y) t) =ᶠ[𝓝 x] timeFDeriv F t :=
    (hg.of_le (by norm_num)).deriv_parameterCurve_eventuallyEq_timeFDeriv
  have hGtime : (fun y ↦ deriv (fun s ↦ g s y) t u v) =ᶠ[𝓝 x] timeFDeriv G t := by
    filter_upwards [htime, (continuousAt_const.prodMk continuousAt_id).eventually hdiff]
      with y hy hdy
    rw [id_eq] at hdy
    rw [hy, timeFDeriv_apply, timeFDeriv_apply, ← fderiv_clm_apply_const_apply hdy u,
      ← fderiv_clm_apply_const_apply (hdy.clm_apply (differentiableAt_const u)) v]
  -- The parameter derivative `h` of `g` is differentiable in the base point.
  have hh : DifferentiableAt ℝ (fun y ↦ deriv (fun s ↦ g s y) t) x :=
    hg.differentiableAt_timeFDeriv.congr_of_eventuallyEq htime
  rw [christoffelFirstKind_eq_of_differentiableAt hh, htime.fderiv_eq, hGtime.fderiv_eq]
  have hD := hasDerivAt_spatialFDeriv (by simpa using hg : ContDiffAt ℝ (minSmoothness ℝ 2) F _)
  have hDG := hasDerivAt_spatialFDeriv (by simpa using hG : ContDiffAt ℝ (minSmoothness ℝ 2) G _)
  have huv := (hD.clm_apply (hasDerivAt_const t u)).clm_apply (hasDerivAt_const t v)
  have hvu := (hD.clm_apply (hasDerivAt_const t v)).clm_apply (hasDerivAt_const t u)
  refine ((((huv.add hvu).sub hDG).const_smul (2⁻¹ : ℝ)).congr_of_eventuallyEq
    hslice).congr_deriv ?_
  simp [Prod.mk_zero_zero]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **The variation of the Christoffel symbols of the second kind.** For a jointly `C²` family of
fields of bilinear forms `g_t` with `g_t(x)` nondegenerate, the parameter derivative of the
Christoffel symbols `Γ` of `g_t` at `x` is obtained by raising the index of
`Γ₁(h)(u, v) - h(Γ(u, v), ·)`, where `h = ∂ₜ g` and `Γ₁` denotes the Christoffel symbols of the
first kind. -/
theorem hasDerivAt_christoffelSecondKind_family
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (t, x))
    (hnd : (g t x).toBilinForm.Nondegenerate) (u v : E) :
    HasDerivAt (fun s ↦ christoffelSecondKind (g s) x u v)
      ((g t x).inverse (christoffelFirstKind (fun y ↦ deriv (fun s ↦ g s y) t) x u v -
        deriv (fun s ↦ g s x) t (christoffelSecondKind (g t) x u v))) t := by
  have hinv := ContinuousLinearMap.isInvertible_of_separatingLeft hnd.1
  have hgx := hasDerivAt_parameterCurve (F := Function.uncurry g) (hg.differentiableAt two_ne_zero)
  have hgd : deriv (fun s ↦ g s x) t = timeFDeriv (Function.uncurry g) t x := hgx.deriv
  have hΓ₁ := hasDerivAt_christoffelFirstKind_family hg u v
  -- `Γ = (g_s(x))⁻¹ Γ₁` is differentiable in `s`, since inversion is smooth at `g_t(x)`.
  have hdiff := ((((hinv.contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero).comp t
      hgx.differentiableAt).clm_apply hΓ₁.differentiableAt).hasDerivAt.congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦ christoffelSecondKind_apply (g s) x u v)
  -- Differentiate `g_s(Γ_s(u, v)) = Γ₁(g_s)(u, v)`, valid while `g_s(x)` stays invertible.
  have hlower : (fun s ↦ g s x (christoffelSecondKind (g s) x u v)) =ᶠ[𝓝 t]
      fun s ↦ christoffelFirstKind (g s) x u v := by
    filter_upwards [hgx.continuousAt.tendsto.eventually hinv.eventually_nhds] with s hs
    rw [christoffelSecondKind_apply]
    exact hs.self_apply_inverse _
  have heq := (hgx.clm_apply hdiff).unique (hΓ₁.congr_of_eventuallyEq hlower)
  convert hdiff using 1
  rw [hgd, ← eq_sub_of_add_eq' heq]
  exact hinv.inverse_apply_self _

/-- **The variation formula for the Christoffel symbols.** Let `g_t` be a jointly `C²` family of
symmetric bilinear forms with `g_t(x)` nondegenerate, let `h = ∂ₜ g`, and let `Γ` be the
Christoffel symbols of `g_t`. Writing `(∇_u h)(v, w) = Dh(u)(v, w) - h(Γ(u, v), w) -
h(v, Γ(u, w))` for the covariant derivative of `h` in linear coordinates,

`2 g(∂ₜΓ(u, v), w) = (∇_u h)(v, w) + (∇_v h)(u, w) - (∇_w h)(u, v)`.

This is the first variation formula for the Levi-Civita connection read in a chart. -/
theorem two_mul_apply_deriv_christoffelSecondKind_family
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (t, x))
    (hsymm : ∀ᶠ p : ℝ × E in 𝓝 (t, x), (g p.1 p.2).toBilinForm.IsSymm)
    (hnd : (g t x).toBilinForm.Nondegenerate) (u v w : E) :
    2 * g t x (deriv (fun s ↦ christoffelSecondKind (g s) x u v) t) w =
      (fderiv ℝ (fun y ↦ deriv (fun s ↦ g s y) t) x u v w -
          deriv (fun s ↦ g s x) t (christoffelSecondKind (g t) x u v) w -
          deriv (fun s ↦ g s x) t v (christoffelSecondKind (g t) x u w)) +
        (fderiv ℝ (fun y ↦ deriv (fun s ↦ g s y) t) x v u w -
          deriv (fun s ↦ g s x) t (christoffelSecondKind (g t) x v u) w -
          deriv (fun s ↦ g s x) t u (christoffelSecondKind (g t) x v w)) -
        (fderiv ℝ (fun y ↦ deriv (fun s ↦ g s y) t) x w u v -
          deriv (fun s ↦ g s x) t (christoffelSecondKind (g t) x w u) v -
          deriv (fun s ↦ g s x) t u (christoffelSecondKind (g t) x w v)) := by
  have hgx := hasDerivAt_parameterCurve (F := Function.uncurry g) (hg.differentiableAt two_ne_zero)
  have hgd : deriv (fun s ↦ g s x) t = timeFDeriv (Function.uncurry g) t x := hgx.deriv
  -- The variation `h(x)` of a family of symmetric forms is symmetric.
  have hsymm_h (a b : E) :
      timeFDeriv (Function.uncurry g) t x a b = timeFDeriv (Function.uncurry g) t x b a := by
    rw [timeFDeriv_apply]
    exact fderiv_apply_apply_comm (hsymm.mono fun _ hp ↦ isSymm_toBilinForm_iff.1 hp) (1, 0) a b
  -- The Christoffel symbols of the symmetric metric `g_t` are symmetric.
  have hΓ (a b : E) : christoffelSecondKind (g t) x a b = christoffelSecondKind (g t) x b a :=
    christoffelSecondKind_comm ((continuousAt_const.prodMk continuousAt_id).eventually hsymm) a b
  rw [(hasDerivAt_christoffelSecondKind_family hg hnd u v).deriv,
    (ContinuousLinearMap.isInvertible_of_separatingLeft hnd.1).self_apply_inverse, hgd]
  simp only [sub_apply, christoffelFirstKind_apply, hΓ v u, hΓ w u, hΓ w v,
    hsymm_h v (christoffelSecondKind (g t) x u w)]
  ring

end FiniteDimensional

end TauCeti.Manifold

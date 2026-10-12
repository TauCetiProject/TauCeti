/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Analysis.Complex.UpperHalfPlane.Affine
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Primitive
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.Conformal.PreSchwarzian
public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
import TauCeti.Analysis.SpecialFunctions.Pow.LogDeriv

/-!
# The Schwarz--Christoffel formula on the unit disc

The disc form of the Schwarz--Christoffel formula writes a conformal map of the open unit disc
onto a polygon as

`f ζ = A * ∫₀^ζ ∏ i, (1 - ξ / w i) ^ e i dξ + B`,

with prevertices `w i` on the unit circle and turning exponents `e i`, the interior angle at the
corresponding vertex being `(e i + 1) * π`.  This file defines the integrand and its primitive
normalized at the centre of the disc, and relates them to the upper-half-plane form of
`TauCeti.schwarzChristoffelPrimitive` through the inverse Cayley transform
`ζ ↦ i (1 + ζ) / (1 - ζ)`.

On the open disc each factor `1 - ζ / w i` has positive real part, so the principal powers are
holomorphic and nowhere zero, and the logarithmic derivative of the integrand is
`∑ i, e i / (ζ - w i)`.  Composing a half-plane Schwarz--Christoffel map with the inverse Cayley
transform turns the pre-Schwarzian `∑ i, e i / (z - a i)` into
`∑ i, e i / (ζ - w i) + (∑ i, e i + 2) / (1 - ζ)`, where `w i` is the Cayley image
`(a i - i) / (a i + i)` of the prevertex `a i`.  The spurious pole at `1`, the image of `∞`,
disappears when the turning exponents sum to `-2`, which is the closing condition of a bounded
polygon.  Under that condition the two forms of the formula differ by an affine map, so
every half-plane Schwarz--Christoffel representation of a domain yields a disc representation,
with the prevertex limits carried along. Without the closing condition, the pole is retained as
an additional prevertex at `1`, with exponent `-∑ i, e i - 2`. This gives the disc form for
unbounded polygons as well, including divergence at their vertex at infinity.

## Main definitions

* `TauCeti.schwarzChristoffelDiscIntegrand` -- the product `∏ i, (1 - ζ / w i) ^ e i`.
* `TauCeti.schwarzChristoffelDiscPrimitive` -- its primitive on the disc vanishing at `0`.

## Main results

* `TauCeti.hasDerivAt_schwarzChristoffelDiscPrimitive` -- the primitive has the integrand as its
  derivative throughout the open unit disc.
* `TauCeti.logDeriv_deriv_schwarzChristoffelDiscPrimitive` -- the Schwarz--Christoffel differential
  equation on the disc.
* `TauCeti.eqOn_schwarzChristoffelDiscPrimitive` -- the derivative and normalization characterize
  the primitive on the disc.
* `TauCeti.eqOn_schwarzChristoffelPrimitive_comp_I_mul_one_add_div_one_sub_with_infty` --
  unrestricted Cayley transport with the additional prevertex at infinity.
* `TauCeti.exists_bijOn_const_mul_schwarzChristoffelDiscPrimitive_add_with_infty_of_bijOn` --
  unrestricted transport of a bijection, its finite boundary limits, and divergence at infinity.

## References

* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
-/

public section

noncomputable section

namespace TauCeti

open Bornology _root_.Complex Filter Metric Set Topology
open UpperHalfPlane (upperHalfPlaneSet isOpen_upperHalfPlaneSet)

variable {ι : Type*} [Fintype ι]

/-- The **disc Schwarz--Christoffel integrand** with prevertices `w i` on the unit circle and
turning exponents `e i`, namely `∏ i, (1 - ζ / w i) ^ e i` with principal powers.  For a polygon
with interior angle `α i` at the vertex corresponding to `w i`, the classical choice is
`e i = α i / π - 1`; the definition itself imposes no condition on the exponents. -/
noncomputable def schwarzChristoffelDiscIntegrand (w : ι → Circle) (e : ι → ℝ) (ζ : ℂ) : ℂ :=
  ∏ i, (1 - ζ / w i) ^ (e i : ℂ)

/-- The disc Schwarz--Christoffel integrand is the product of its principal-power factors. -/
theorem schwarzChristoffelDiscIntegrand_def (w : ι → Circle) (e : ι → ℝ) (ζ : ℂ) :
    schwarzChristoffelDiscIntegrand w e ζ = ∏ i, (1 - ζ / w i) ^ (e i : ℂ) :=
  (rfl)

/-- With every turning exponent zero, the disc Schwarz--Christoffel integrand is constant one. -/
@[simp]
theorem schwarzChristoffelDiscIntegrand_zero (w : ι → Circle) :
    schwarzChristoffelDiscIntegrand w 0 = 1 := by
  ext ζ
  simp [schwarzChristoffelDiscIntegrand]

/-- The disc Schwarz--Christoffel integrand takes the value one at the centre of the disc. -/
@[simp]
theorem schwarzChristoffelDiscIntegrand_apply_zero (w : ι → Circle) (e : ι → ℝ) :
    schwarzChristoffelDiscIntegrand w e 0 = 1 := by
  simp [schwarzChristoffelDiscIntegrand]

/-- Adding a prevertex with exponent zero does not change the disc integrand. -/
@[simp]
theorem schwarzChristoffelDiscIntegrand_option_zero (v : Circle) (w : ι → Circle) (e : ι → ℝ) :
    schwarzChristoffelDiscIntegrand (Option.elim' v w) (Option.elim' 0 e) =
      schwarzChristoffelDiscIntegrand w e := by
  funext ζ
  simp [schwarzChristoffelDiscIntegrand, Fintype.prod_option]

/-- The disc Schwarz--Christoffel integrand is holomorphic on the open unit disc. -/
theorem differentiableOn_schwarzChristoffelDiscIntegrand (w : ι → Circle) (e : ι → ℝ) :
    DifferentiableOn ℂ (schwarzChristoffelDiscIntegrand w e) (ball 0 1) := by
  intro ζ hζ
  exact DifferentiableWithinAt.fun_finsetProd fun i _ =>
    ((hasDerivAt_one_sub_div (w i : ℂ) ζ).differentiableAt.cpow_const
      (one_sub_div_mem_slitPlane (w i) hζ)).differentiableWithinAt

/-- The disc Schwarz--Christoffel integrand has no zero in the open unit disc. -/
theorem schwarzChristoffelDiscIntegrand_ne_zero (w : ι → Circle) (e : ι → ℝ) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) : schwarzChristoffelDiscIntegrand w e ζ ≠ 0 := by
  rw [schwarzChristoffelDiscIntegrand_def]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => cpow_ne_zero_iff.mpr
    (Or.inl (slitPlane_ne_zero (one_sub_div_mem_slitPlane (w i) hζ)))

/-- The logarithmic derivative of the disc Schwarz--Christoffel integrand is the sum of the simple
fractions `e i / (ζ - w i)`, whose poles lie on the unit circle. -/
theorem logDeriv_schwarzChristoffelDiscIntegrand (w : ι → Circle) (e : ι → ℝ) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) :
    logDeriv (schwarzChristoffelDiscIntegrand w e) ζ = ∑ i, (e i : ℂ) / (ζ - w i) := by
  -- `logDeriv_fun_prod` rewrites a syntactic product of functions, so present the integrand
  -- as one before rewriting with it.
  have hfun : schwarzChristoffelDiscIntegrand w e =
      fun ξ : ℂ => ∏ i, (1 - ξ / w i) ^ (e i : ℂ) :=
    funext (schwarzChristoffelDiscIntegrand_def w e)
  rw [hfun, logDeriv_fun_prod]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [logDeriv_fun_cpow (hasDerivAt_one_sub_div (w i : ℂ) ζ).differentiableAt
      (one_sub_div_mem_slitPlane (w i) hζ), logDeriv_apply,
      (hasDerivAt_one_sub_div (w i : ℂ) ζ).deriv]
    have hw : (w i : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hζw : (w i : ℂ) - ζ ≠ 0 := sub_ne_zero.mpr
      (ne_of_mem_ball_of_norm_eq_one hζ (Circle.norm_coe (w i))).symm
    have hζw' : ζ - (w i : ℂ) ≠ 0 := by rwa [← neg_sub, neg_ne_zero]
    rw [one_sub_div hw]
    field_simp
    ring
  · exact fun i _ => cpow_ne_zero_iff.mpr
      (Or.inl (slitPlane_ne_zero (one_sub_div_mem_slitPlane (w i) hζ)))
  · exact fun i _ => (hasDerivAt_one_sub_div (w i : ℂ) ζ).differentiableAt.cpow_const
      (one_sub_div_mem_slitPlane (w i) hζ)

/-- The **normalized disc Schwarz--Christoffel primitive**: the integral of
`schwarzChristoffelDiscIntegrand w e` from the centre `0` of the disc to `ζ`, along a horizontal
segment followed by a vertical one.  The definition is total on `ℂ`, but its analytic
interpretation is asserted on the open unit disc. -/
noncomputable def schwarzChristoffelDiscPrimitive (w : ι → Circle) (e : ι → ℝ) (ζ : ℂ) : ℂ :=
  wedgeIntegral 0 ζ (schwarzChristoffelDiscIntegrand w e)

/-- The normalized disc primitive as a wedge integral from the disc centre. -/
theorem schwarzChristoffelDiscPrimitive_def (w : ι → Circle) (e : ι → ℝ) (ζ : ℂ) :
    schwarzChristoffelDiscPrimitive w e ζ =
      wedgeIntegral 0 ζ (schwarzChristoffelDiscIntegrand w e) := by
  unfold schwarzChristoffelDiscPrimitive
  exact Eq.refl _

/-- The normalized disc Schwarz--Christoffel primitive vanishes at the centre of the disc. -/
@[simp]
theorem schwarzChristoffelDiscPrimitive_apply_zero (w : ι → Circle) (e : ι → ℝ) :
    schwarzChristoffelDiscPrimitive w e 0 = 0 := by
  simp [schwarzChristoffelDiscPrimitive, wedgeIntegral]

/-- Adding a prevertex with exponent zero does not change the disc primitive. -/
@[simp]
theorem schwarzChristoffelDiscPrimitive_option_zero (v : Circle) (w : ι → Circle) (e : ι → ℝ) :
    schwarzChristoffelDiscPrimitive (Option.elim' v w) (Option.elim' 0 e) =
      schwarzChristoffelDiscPrimitive w e := by
  funext ζ
  simp [schwarzChristoffelDiscPrimitive]

/-- The derivative of the normalized disc Schwarz--Christoffel primitive is its integrand
throughout the open unit disc. -/
theorem hasDerivAt_schwarzChristoffelDiscPrimitive (w : ι → Circle) (e : ι → ℝ) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) :
    HasDerivAt (schwarzChristoffelDiscPrimitive w e) (schwarzChristoffelDiscIntegrand w e ζ) ζ :=
  (differentiableOn_schwarzChristoffelDiscIntegrand w e).isConservativeOn.hasDerivAt_wedgeIntegral
    (differentiableOn_schwarzChristoffelDiscIntegrand w e).continuousOn hζ

/-- The derivative of the normalized disc Schwarz--Christoffel primitive on the open unit disc. -/
@[simp] theorem deriv_schwarzChristoffelDiscPrimitive (w : ι → Circle) (e : ι → ℝ) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) :
    deriv (schwarzChristoffelDiscPrimitive w e) ζ = schwarzChristoffelDiscIntegrand w e ζ :=
  (hasDerivAt_schwarzChristoffelDiscPrimitive w e hζ).deriv

/-- The normalized disc Schwarz--Christoffel primitive is holomorphic on the open unit disc. -/
theorem differentiableOn_schwarzChristoffelDiscPrimitive (w : ι → Circle) (e : ι → ℝ) :
    DifferentiableOn ℂ (schwarzChristoffelDiscPrimitive w e) (ball 0 1) := fun _ hζ =>
  (hasDerivAt_schwarzChristoffelDiscPrimitive w e hζ).differentiableAt.differentiableWithinAt

/-- The normalized disc Schwarz--Christoffel primitive is conformal at every point of the open
unit disc. -/
theorem conformalAt_schwarzChristoffelDiscPrimitive (w : ι → Circle) (e : ι → ℝ) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) : ConformalAt (schwarzChristoffelDiscPrimitive w e) ζ :=
  (hasDerivAt_schwarzChristoffelDiscPrimitive w e hζ).differentiableAt.conformalAt
    (deriv_schwarzChristoffelDiscPrimitive w e hζ ▸
      schwarzChristoffelDiscIntegrand_ne_zero w e hζ)

/-- **The Schwarz--Christoffel differential equation on the disc.**  Throughout the open unit disc
the pre-Schwarzian `F'' / F'` of the normalized disc primitive `F` is the sum of simple fractions
`∑ i, e i / (ζ - w i)`. -/
theorem logDeriv_deriv_schwarzChristoffelDiscPrimitive (w : ι → Circle) (e : ι → ℝ) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) 1) :
    logDeriv (deriv (schwarzChristoffelDiscPrimitive w e)) ζ = ∑ i, (e i : ℂ) / (ζ - w i) := by
  have heq : deriv (schwarzChristoffelDiscPrimitive w e) =ᶠ[𝓝 ζ]
      schwarzChristoffelDiscIntegrand w e :=
    eventuallyEq_of_mem (isOpen_ball.mem_nhds hζ) fun _ hξ =>
      deriv_schwarzChristoffelDiscPrimitive w e hξ
  rw [(logDeriv_congr_nhds heq).eq_of_nhds, logDeriv_schwarzChristoffelDiscIntegrand w e hζ]

/-- A primitive of the disc Schwarz--Christoffel integrand vanishing at the centre agrees with
`schwarzChristoffelDiscPrimitive` throughout the open unit disc. -/
theorem eqOn_schwarzChristoffelDiscPrimitive (w : ι → Circle) (e : ι → ℝ) {g : ℂ → ℂ}
    (hg : ∀ ζ ∈ ball (0 : ℂ) 1, HasDerivAt g (schwarzChristoffelDiscIntegrand w e ζ) ζ)
    (hg₀ : g 0 = 0) :
    EqOn g (schwarzChristoffelDiscPrimitive w e) (ball 0 1) := by
  apply isOpen_ball.eqOn_of_deriv_eq (convex_ball 0 1).isPreconnected
    (fun ζ hζ => (hg ζ hζ).differentiableAt.differentiableWithinAt)
    (differentiableOn_schwarzChristoffelDiscPrimitive w e)
    (fun ζ hζ => (hg ζ hζ).deriv.trans (deriv_schwarzChristoffelDiscPrimitive w e hζ).symm)
    (mem_ball_self one_pos)
  simpa using hg₀

/-! ### Comparison with the upper-half-plane form -/

/-- The half-plane primitive in inverse Cayley coordinates differs by an affine map from
its disc primitive, with the additional exponent `-∑ i, e i - 2` at the prevertex `1`. -/
private theorem exists_affine_transport_with_infty
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {w : Option ι → Circle}
    (hw₀ : w none = 1) (hw : ∀ i, (w (some i) : ℂ) = (a i - I) / (a i + I)) :
    ∃ A : ℂ, A ≠ 0 ∧ ∃ B : ℂ,
      EqOn (fun ζ => schwarzChristoffelPrimitive a e z₀ (I * (1 + ζ) / (1 - ζ)))
        (fun ζ => A * schwarzChristoffelDiscPrimitive w
          (Option.elim' (-∑ i, e i - 2) e) ζ + B) (ball 0 1) := by
  set F := schwarzChristoffelPrimitive a e z₀
  set c : ℂ → ℂ := fun ζ => I * (1 + ζ) / (1 - ζ) with hc_def
  have hmaps : MapsTo c (ball 0 1) upperHalfPlaneSet := bijOn_I_mul_one_add_div_one_sub_ball.mapsTo
  have hne : ∀ ζ ∈ ball (0 : ℂ) 1, ζ ≠ 1 := fun _ hζ =>
    ne_of_mem_ball_of_norm_eq_one hζ norm_one
  have hcd : ∀ ζ ∈ ball (0 : ℂ) 1, HasDerivAt c (2 * I / (1 - ζ) ^ 2) ζ := fun ζ hζ =>
    hasDerivAt_I_mul_one_add_div_one_sub (hne ζ hζ)
  have hcne : ∀ ζ ∈ ball (0 : ℂ) 1, 2 * I / (1 - ζ) ^ 2 ≠ 0 := fun ζ hζ =>
    div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (pow_ne_zero 2 (sub_ne_zero.mpr (hne ζ hζ).symm))
  have hcdiff : DifferentiableOn ℂ c (ball 0 1) := fun ζ hζ =>
    (hcd ζ hζ).differentiableAt.differentiableWithinAt
  have hFdiff := differentiableOn_schwarzChristoffelPrimitive a e z₀
  have hFn : ∀ z ∈ upperHalfPlaneSet, deriv F z ≠ 0 := fun z hz =>
    deriv_schwarzChristoffelPrimitive a e z₀ hz ▸ schwarzChristoffelIntegrand_ne_zero a e hz
  have hderiv : ∀ ζ ∈ ball (0 : ℂ) 1, deriv (fun ζ => F (c ζ)) ζ =
      deriv F (c ζ) * (2 * I / (1 - ζ) ^ 2) := fun ζ hζ =>
    (((hasDerivAt_schwarzChristoffelPrimitive a e z₀ (hmaps hζ)).comp ζ (hcd ζ hζ)).deriv).trans
      (by rw [deriv_schwarzChristoffelPrimitive a e z₀ (hmaps hζ)])
  refine (exists_eqOn_const_mul_add_iff_logDeriv_deriv_eqOn isOpen_ball
    (convex_ball 0 1).isPreconnected (hFdiff.comp hcdiff hmaps)
    (differentiableOn_schwarzChristoffelDiscPrimitive w (Option.elim' (-∑ i, e i - 2) e))
    (fun ζ hζ => hderiv ζ hζ ▸ mul_ne_zero (hFn _ (hmaps hζ)) (hcne ζ hζ))
    (fun ζ hζ => deriv_schwarzChristoffelDiscPrimitive w (Option.elim' (-∑ i, e i - 2) e) hζ ▸
      schwarzChristoffelDiscIntegrand_ne_zero w
        (Option.elim' (-∑ i, e i - 2) e) hζ)).mpr fun ζ hζ => ?_
  -- the pre-Schwarzian chain rule for `F ∘ c`
  refine (logDeriv_deriv_comp (hFdiff.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds (hmaps hζ)))
    (hcdiff.analyticAt (isOpen_ball.mem_nhds hζ)) (hFn _ (hmaps hζ))
    ((hcd ζ hζ).deriv ▸ hcne ζ hζ)).trans ?_
  rw [logDeriv_deriv_schwarzChristoffelPrimitive a e z₀ (hmaps hζ), (hcd ζ hζ).deriv,
    logDeriv_deriv_I_mul_one_add_div_one_sub (hne ζ hζ),
    logDeriv_deriv_schwarzChristoffelDiscPrimitive w (Option.elim' (-∑ i, e i - 2) e) hζ]
  -- The pole at `1` records the half-plane's point at infinity instead of requiring
  -- a closing condition on the finite exponents.
  rw [Fintype.sum_option]
  simp only [Option.elim'_none, Option.elim'_some, hw₀, Circle.coe_one]
  have hfrac (i : ι) :
      (e i : ℂ) / (c ζ - a i) * (2 * I / (1 - ζ) ^ 2) =
        (e i : ℂ) / (ζ - w (some i)) + (e i : ℂ) / (1 - ζ) := by
    rw [hw i, hc_def]
    have hζa : ζ ≠ (a i - I) / (a i + I) := by
      rw [← hw i]
      exact ne_of_mem_ball_of_norm_eq_one hζ (Circle.norm_coe (w (some i)))
    linear_combination (e i : ℂ) * cayley_simple_fraction (a i) (hne ζ hζ) hζa
  rw [Finset.sum_mul]
  simp_rw [hfrac]
  have hden : ζ - 1 = -(1 - ζ) := by ring
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← ofReal_sum, hden, div_neg]
  push_cast
  ring

/-- **Cayley transport with a prevertex at infinity.** For arbitrary real exponents, the
half-plane primitive in disc coordinates equals the disc primitive with the finite Cayley
prevertices and an additional prevertex `1` of exponent `-∑ i, e i - 2`, up to explicit affine
constants. For an unbounded polygon with sector opening `β * π` at infinity, that exponent is
`-β - 1`. No closing or angle restriction is required for this analytic identity. -/
theorem eqOn_schwarzChristoffelPrimitive_comp_I_mul_one_add_div_one_sub_with_infty
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) :
    EqOn (fun ζ => schwarzChristoffelPrimitive a e z₀ (I * (1 + ζ) / (1 - ζ)))
      (fun ζ => 2 * I * schwarzChristoffelIntegrand a e I *
        schwarzChristoffelDiscPrimitive (Option.elim' 1 (fun i => boundaryCayley (a i)))
          (Option.elim' (-∑ i, e i - 2) e) ζ +
        schwarzChristoffelPrimitive a e z₀ I) (ball 0 1) := by
  let w : Option ι → Circle := Option.elim' 1 (fun i => boundaryCayley (a i))
  have hw (i : ι) : (w (some i) : ℂ) = (a i - I) / (a i + I) := coe_boundaryCayley (a i)
  obtain ⟨K, _, D, hKD⟩ := exists_affine_transport_with_infty a e z₀ (by rfl) hw
  have h0 : (0 : ℂ) ∈ ball 0 1 := mem_ball_self one_pos
  have hD : D = schwarzChristoffelPrimitive a e z₀ I := by
    have h := hKD h0
    simpa using h.symm
  have hI : I ∈ upperHalfPlaneSet := by simp [upperHalfPlaneSet]
  have hleft : HasDerivAt
      (fun ζ => schwarzChristoffelPrimitive a e z₀ (I * (1 + ζ) / (1 - ζ)))
      (schwarzChristoffelIntegrand a e I * (2 * I)) 0 := by
    have hF0 : HasDerivAt (schwarzChristoffelPrimitive a e z₀)
        (schwarzChristoffelIntegrand a e I) (I * (1 + (0 : ℂ)) / (1 - 0)) := by
      simpa using hasDerivAt_schwarzChristoffelPrimitive a e z₀ hI
    simpa only [Function.comp_def, sub_zero, one_pow, div_one] using hF0.comp 0
      (hasDerivAt_I_mul_one_add_div_one_sub (by norm_num : (0 : ℂ) ≠ 1))
  have hright := ((hasDerivAt_schwarzChristoffelDiscPrimitive w
    (Option.elim' (-∑ i, e i - 2) e) h0).const_mul K).add_const D
  have hderivEq := (eventuallyEq_of_mem (isOpen_ball.mem_nhds h0)
    (fun ζ hζ => hKD hζ)).deriv_eq
  rw [hleft.deriv, hright.deriv] at hderivEq
  have hKexpr : K = 2 * I * schwarzChristoffelIntegrand a e I := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hderivEq.symm
  simpa only [hKexpr, hD] using hKD

/-- **Disc transport including the point at infinity.** A half-plane Schwarz--Christoffel
bijection gives a disc Schwarz--Christoffel bijection after adding the prevertex `1` with
exponent `-∑ i, e i - 2`. Finite boundary limits pass to their Cayley prevertices, and divergence
at infinity passes to divergence at `1`. -/
theorem exists_bijOn_const_mul_schwarzChristoffelDiscPrimitive_add_with_infty_of_bijOn
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) {U : Set ℂ} {A B : ℂ}
    (hAB : BijOn (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet U) :
    ∃ A' : ℂ, A' ≠ 0 ∧ ∃ B' : ℂ,
      BijOn (fun ζ => A' * schwarzChristoffelDiscPrimitive
        (Option.elim' 1 (fun i => boundaryCayley (a i)))
          (Option.elim' (-∑ i, e i - 2) e) ζ + B') (ball 0 1) U ∧
      (∀ (x : ℝ) (v : ℂ),
        Tendsto (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B)
          (𝓝[upperHalfPlaneSet] (x : ℂ)) (𝓝 v) →
        Tendsto (fun ζ => A' * schwarzChristoffelDiscPrimitive
          (Option.elim' 1 (fun i => boundaryCayley (a i)))
          (Option.elim' (-∑ i, e i - 2) e) ζ + B')
          (𝓝[ball 0 1] (boundaryCayley x : ℂ)) (𝓝 v)) ∧
      (Tendsto (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B)
        (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (cobounded ℂ) →
      Tendsto (fun ζ => A' * schwarzChristoffelDiscPrimitive
        (Option.elim' 1 (fun i => boundaryCayley (a i)))
        (Option.elim' (-∑ i, e i - 2) e) ζ + B') (𝓝[ball 0 1] 1) (cobounded ℂ)) := by
  have hxI (x : ℝ) : (x : ℂ) + I ≠ 0 := add_I_ne_zero_of_im_nonneg (by simp)
  let w : Option ι → Circle := Option.elim' 1 (fun i => boundaryCayley (a i))
  let e' : Option ι → ℝ := Option.elim' (-∑ i, e i - 2) e
  let K : ℂ := 2 * I * schwarzChristoffelIntegrand a e I
  let D : ℂ := schwarzChristoffelPrimitive a e z₀ I
  have hKD := eqOn_schwarzChristoffelPrimitive_comp_I_mul_one_add_div_one_sub_with_infty a e z₀
  have hK : K ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
    (schwarzChristoffelIntegrand_ne_zero a e (by simp [upperHalfPlaneSet]))
  have hA : A ≠ 0 := ne_zero_of_injOn_const_mul_add hAB.injOn
  have heq : EqOn (fun ζ => A * schwarzChristoffelPrimitive a e z₀ (I * (1 + ζ) / (1 - ζ)) + B)
      (fun ζ => A * K * schwarzChristoffelDiscPrimitive w e' ζ + (A * D + B)) (ball 0 1) :=
    fun ζ hζ => by
      have h := hKD hζ
      dsimp only at h ⊢
      rw [h]
      ring
  refine ⟨A * K, mul_ne_zero hA hK, A * D + B,
    (hAB.comp bijOn_I_mul_one_add_div_one_sub_ball).congr heq, ?_, ?_⟩
  · intro x v hv
    -- the inverse Cayley transform carries the disc near `(x - i) / (x + i)` to the upper
    -- half-plane near `x`
    have hp1 : (boundaryCayley x : ℂ) ≠ 1 := by
      intro h
      exact boundaryCayley_ne_one x (Circle.coe_injective (by simpa using h))
    have hcx : I * (1 + (boundaryCayley x : ℂ)) / (1 - (boundaryCayley x : ℂ)) = x := by
      rw [coe_boundaryCayley]
      exact I_mul_one_add_sub_I_div_add_I_div_one_sub (hxI x)
    have hc : Tendsto (fun ζ : ℂ => I * (1 + ζ) / (1 - ζ))
        (𝓝[ball 0 1] (boundaryCayley x : ℂ)) (𝓝[upperHalfPlaneSet] (x : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_nhdsWithin_of_forall fun ζ hζ =>
        bijOn_I_mul_one_add_div_one_sub_ball.mapsTo hζ⟩
      have := (hasDerivAt_I_mul_one_add_div_one_sub hp1).continuousAt.tendsto
      rw [hcx] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact (hv.comp hc).congr' (eventually_nhdsWithin_of_forall heq)
  · intro hv
    exact (hv.comp tendsto_I_mul_one_add_div_one_sub_nhdsWithin_one).congr'
      (eventually_nhdsWithin_of_forall heq)

end TauCeti

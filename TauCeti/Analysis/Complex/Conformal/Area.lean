/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.Complex.Determinant

/-!
# Area and change of variables for a holomorphic map

Where its derivative does not vanish a holomorphic map is conformal: at such a point `z` it acts on
the plane as a rotation followed by a dilation of ratio `‖deriv f z‖`. At every point, critical or
not, it multiplies infinitesimal area by `‖deriv f z‖ ^ 2`. Integrating that pointwise distortion
over a set on which `f` is injective gives the **area formula**,
`volume (f '' s) = ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2`,
and its immediate corollary that a holomorphic injection whose image has finite area has a finite
Dirichlet integral `∫⁻ z in s, ‖deriv f z‖ₑ ^ 2`.

That finiteness is the analytic input of the *length–area method*, the classical route to
Carathéodory's boundary correspondence: for a conformal map of the disc onto a bounded domain, the
finite Dirichlet integral is spent along the circular arcs `{z ∈ ball 0 1 | ‖z - ζ‖ = ρ}`
approaching a boundary point `ζ`, so by Cauchy–Schwarz the images of those arcs must be short for
some arbitrarily small `ρ`, which is what forces the boundary cluster set at `ζ` to degenerate to a
point. The topological half of that argument is `TauCeti.exists_continuousOn_closure_eqOn`, which
turns a subsingleton cluster set into a continuous extension. The area formula is the first
component of the analytic half; the degeneracy itself is not proved here.

Weighting that same distortion by an arbitrary integrand generalises the area formula to the
**change of variables formula** for a holomorphic injection,
`∫⁻ w in f '' s, g w = ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 * g (f z)`,
of which the area formula is the case `g = 1`. (The area formula is nevertheless kept separate: it
holds for a merely null measurable `s`, while the weight forces the measurability that Mathlib's
change of variables asks for.) The integrability and Bochner forms generalise
`TauCeti.integrableOn_norm_deriv_sq` and `TauCeti.integral_norm_deriv_sq_eq_toReal_volume_image`
the same way, and are stated for an integrand valued in an arbitrary real normed space, as
Mathlib's are.

The proof is Mathlib's change-of-variables formula
`MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image₀` for an injective differentiable map,
applied to `f` viewed as a map of the real plane. The only complex-analytic input is the value of
the Jacobian determinant: the `ℝ`-linear map underlying multiplication by `c : ℂ` has determinant
`Complex.normSq c = ‖c‖ ^ 2`, which is `ContinuousLinearMap.det_restrictScalars_smulRight_one`.
Injectivity is what makes the formula an equality rather than the inequality
`TauCeti.volume_image_le_lintegral_enorm_deriv_sq`, which holds for any holomorphic map because a
non-injective map covers parts of its image more than once.

The results below are stated for maps of `ℂ`, with hypotheses that `f` is complex differentiable
at every point of a set `s` (`∀ z ∈ s, DifferentiableAt ℂ f z`) and `Set.InjOn f s`. Mathlib's
change of variables asks only for a real derivative of `f` within `s` at each point of `s`; the
pointwise complex differentiability is the input from which the private
`hasFDerivWithinAt_smulRight_deriv` produces that `HasFDerivWithinAt … s` hypothesis, with the
derivative in the form whose determinant is computed above. It is implied by the usual
complex-analytic setting: if `f` is holomorphic on an open set `U` and `s ⊆ U`, then
`fun z hz => hf.differentiableAt (hUo.mem_nhds (hsU hz))` supplies it. Statements are made for an
arbitrary `s` rather than a domain of holomorphy, because the length–area argument integrates over
the sub-annuli `U ∩ {z | ρ₁ < ‖z - ζ‖ < ρ₂}`, not over `U`. Since `deriv f` is measurable for
every `f`, the area formula and everything deduced from it (the finiteness, integrability and
Bochner forms, the null set criterion and the Dirichlet integral of a Riemann map) ask only for
`MeasureTheory.NullMeasurableSet s volume`, as Mathlib's null-measurable change of variables does.
The area inequality and the three weighted change-of-variables forms ask for `MeasurableSet s`,
because that is what Mathlib's versions of them ask for.

## Main results

* `TauCeti.volume_image_eq_lintegral_enorm_deriv_sq` — the area formula: the area of the image of
  a set on which a holomorphic map is injective is the integral of `‖deriv f‖ ^ 2` over it.
* `TauCeti.volume_image_le_lintegral_enorm_deriv_sq` — the inequality form, with no injectivity.
* `TauCeti.lintegral_enorm_deriv_sq_ne_top` and `TauCeti.integrableOn_norm_deriv_sq` — a
  holomorphic injection whose image has finite area has a finite Dirichlet integral;
  `TauCeti.lintegral_enorm_deriv_sq_ne_top_of_isBounded` and
  `TauCeti.integrableOn_norm_deriv_sq_of_isBounded` are the forms taking a bounded image.
* `TauCeti.integral_norm_deriv_sq_eq_toReal_volume_image` — the Bochner-integral form of the area
  formula.
* `TauCeti.volume_image_eq_zero_iff` — a holomorphic injection whose derivative is almost
  everywhere nonzero carries null sets to null sets and back.
* `TauCeti.lintegral_enorm_deriv_sq_eq_pi_of_image_eq_ball` — the Dirichlet integral of a Riemann
  map is exactly `π`.
* `TauCeti.lintegral_image_eq_lintegral_enorm_deriv_sq_mul`,
  `TauCeti.integrableOn_image_iff_integrableOn_norm_deriv_sq_smul` and
  `TauCeti.integral_image_eq_integral_norm_deriv_sq_smul` — the change of variables formula for a
  holomorphic injection, in Lebesgue, integrability and Bochner form.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2 (the length–area method).
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX.
* P. L. Duren, *Univalent Functions*, Ch. 2 (the area theorem).
-/

public section

namespace TauCeti

open Bornology Complex MeasureTheory Metric Set
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {s : Set ℂ} {f : ℂ → ℂ}

/-- At each point of a set `s` at which `f` is complex differentiable, the `ℝ`-linear derivative of
`f` relative to `s` is multiplication by `deriv f z`. This is the family of derivatives the
change-of-variables formula is applied to. -/
private theorem hasFDerivWithinAt_smulRight_deriv (hf : ∀ z ∈ s, DifferentiableAt ℂ f z) :
    ∀ z ∈ s, HasFDerivWithinAt f
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv f z)).restrictScalars ℝ) s z :=
  fun z hz => ((hf z hz).hasDerivAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt

/-- The pointwise area distortion, in the form the change-of-variables formula produces it for
Bochner integrals. -/
private theorem abs_det_restrictScalars_smulRight_one (c : ℂ) :
    |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det| = ‖c‖ ^ 2 := by
  rw [ContinuousLinearMap.det_restrictScalars_smulRight_one, abs_of_nonneg (by positivity)]

/-- The pointwise area distortion, in the form the change-of-variables formula produces it for
Lebesgue integrals. -/
private theorem ofReal_abs_det_eq (c : ℂ) :
    ENNReal.ofReal
        |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det| = ‖c‖ₑ ^ 2 := by
  rw [abs_det_restrictScalars_smulRight_one, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- **The area formula.** If `f` is complex differentiable at every point of a null measurable set
`s` and injective on `s`, then the area of `f '' s` is the integral over `s` of the area distortion
`‖deriv f z‖ ^ 2`.

Injectivity is essential: without it the map covers part of its image more than once and only the
inequality `TauCeti.volume_image_le_lintegral_enorm_deriv_sq` survives. -/
theorem volume_image_eq_lintegral_enorm_deriv_sq (hf : ∀ z ∈ s, DifferentiableAt ℂ f z)
    (hs : NullMeasurableSet s volume) (hinj : InjOn f s) :
    volume (f '' s) = ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image₀ volume hs
    (hasFDerivWithinAt_smulRight_deriv hf) hinj]
  exact lintegral_congr fun z => ofReal_abs_det_eq (deriv f z)

/-- **The area inequality for a holomorphic map.** Dropping injectivity from the area formula
leaves an inequality, since a map that covers a part of its image several times spends more of the
integral `∫⁻ z in s, ‖deriv f z‖ₑ ^ 2` than the area of the image accounts for. -/
theorem volume_image_le_lintegral_enorm_deriv_sq (hf : ∀ z ∈ s, DifferentiableAt ℂ f z)
    (hs : MeasurableSet s) :
    volume (f '' s) ≤ ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 :=
  (addHaar_image_le_lintegral_abs_det_fderiv volume hs
    (hasFDerivWithinAt_smulRight_deriv hf)).trans_eq
    (lintegral_congr fun z => ofReal_abs_det_eq (deriv f z))

/-- **A holomorphic injection whose image has finite area has a finite Dirichlet integral.** This is
the finiteness that the length–area method spends: the whole of `∫⁻ z in s, ‖deriv f z‖ₑ ^ 2` is
available to bound the lengths of the images of the circular arcs approaching a boundary point, so
all but finitely much of it must be spread thinly. -/
theorem lintegral_enorm_deriv_sq_ne_top (hf : ∀ z ∈ s, DifferentiableAt ℂ f z)
    (hs : NullMeasurableSet s volume) (hinj : InjOn f s) (hfin : volume (f '' s) ≠ ⊤) :
    ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 ≠ ⊤ := by
  rwa [← volume_image_eq_lintegral_enorm_deriv_sq hf hs hinj]

/-- The bounded-image form of `TauCeti.lintegral_enorm_deriv_sq_ne_top`: a holomorphic injection
with bounded image has a finite Dirichlet integral. -/
theorem lintegral_enorm_deriv_sq_ne_top_of_isBounded (hf : ∀ z ∈ s, DifferentiableAt ℂ f z)
    (hs : NullMeasurableSet s volume) (hinj : InjOn f s) (hb : IsBounded (f '' s)) :
    ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 ≠ ⊤ :=
  lintegral_enorm_deriv_sq_ne_top hf hs hinj hb.measure_lt_top.ne

/-- The Bochner-integrability form of `TauCeti.lintegral_enorm_deriv_sq_ne_top`: the area distortion
of a holomorphic injection whose image has finite area is integrable. Measurability is free because
the derivative of any function `ℂ → ℂ` is measurable. -/
theorem integrableOn_norm_deriv_sq (hf : ∀ z ∈ s, DifferentiableAt ℂ f z)
    (hs : NullMeasurableSet s volume) (hinj : InjOn f s) (hfin : volume (f '' s) ≠ ⊤) :
    IntegrableOn (fun z => ‖deriv f z‖ ^ 2) s := by
  simpa [IntegrableOn] using integrable_toReal_of_lintegral_ne_top
    ((measurable_deriv f).enorm.pow_const 2).aemeasurable
    (lintegral_enorm_deriv_sq_ne_top hf hs hinj hfin)

/-- The bounded-image form of `TauCeti.integrableOn_norm_deriv_sq`: the area distortion of a
holomorphic injection with bounded image is integrable. -/
theorem integrableOn_norm_deriv_sq_of_isBounded (hf : ∀ z ∈ s, DifferentiableAt ℂ f z)
    (hs : NullMeasurableSet s volume) (hinj : InjOn f s) (hb : IsBounded (f '' s)) :
    IntegrableOn (fun z => ‖deriv f z‖ ^ 2) s :=
  integrableOn_norm_deriv_sq hf hs hinj hb.measure_lt_top.ne

/-- **The area formula, Bochner form.** The area of the image of a holomorphic injection is the
ordinary integral of the area distortion.

No finiteness is needed: if the area distortion is not integrable then both sides are `0`, the
Bochner integral by convention and the right-hand side because `(⊤ : ℝ≥0∞).toReal = 0`. -/
theorem integral_norm_deriv_sq_eq_toReal_volume_image (hf : ∀ z ∈ s, DifferentiableAt ℂ f z)
    (hs : NullMeasurableSet s volume) (hinj : InjOn f s) :
    ∫ z in s, ‖deriv f z‖ ^ 2 = (volume (f '' s)).toReal := by
  rw [volume_image_eq_lintegral_enorm_deriv_sq hf hs hinj,
    ← integral_toReal ((measurable_deriv f).enorm.pow_const 2).aemeasurable
      (.of_forall fun _ => by finiteness)]
  simp

/-- **A holomorphic injection carries null sets to null sets and back.** Where the derivative is
almost everywhere nonzero, the image of a null measurable set is null exactly when the set is.

The nonvanishing is not an extra assumption in the intended case of an open set `s` on which `f`
is holomorphic: a holomorphic map injective on an open set has nonvanishing derivative throughout
it, by `TauCeti.not_injOn_of_deriv_eq_zero`, so `MeasureTheory.ae_restrict_of_forall_mem` supplies
`hd`. It is kept as a hypothesis so that the statement also covers a set `s` that need not be a
neighbourhood of its points.

Only the forward implication needs the derivative: a differentiable map carries null sets to null
sets whatever its derivative does, whereas a set of positive measure has a null image only if the
area distortion `‖deriv f‖ ^ 2` vanishes on much of it. -/
theorem volume_image_eq_zero_iff (hf : ∀ z ∈ s, DifferentiableAt ℂ f z)
    (hs : NullMeasurableSet s volume) (hinj : InjOn f s)
    (hd : ∀ᵐ z ∂volume.restrict s, deriv f z ≠ 0) :
    volume (f '' s) = 0 ↔ volume s = 0 := by
  rw [volume_image_eq_lintegral_enorm_deriv_sq hf hs hinj,
    lintegral_eq_zero_iff ((measurable_deriv f).enorm.pow_const 2)]
  refine ⟨fun h => ?_, fun h => by simp [Measure.restrict_eq_zero.mpr h, Filter.EventuallyEq]⟩
  have hfalse : ∀ᵐ _ ∂volume.restrict s, False := by
    filter_upwards [h, hd] with z hz hz0
    exact hz0 (by simpa using hz)
  simpa [ae_iff, Measure.restrict_apply_univ] using hfalse

/-- **The Dirichlet integral of a Riemann map is `π`.** A holomorphic injection onto the unit disc
spends exactly the area of the disc.

The hypotheses are those of the conclusion of the Riemann mapping theorem
`TauCeti.riemannMapping` for an open `s`, so the statement is not vacuous: every nonempty simply
connected proper open subset of `ℂ` carries such an `f`. -/
theorem lintegral_enorm_deriv_sq_eq_pi_of_image_eq_ball (hf : ∀ z ∈ s, DifferentiableAt ℂ f z)
    (hs : NullMeasurableSet s volume) (hinj : InjOn f s) (himg : f '' s = ball 0 1) :
    ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 = ENNReal.ofReal Real.pi := by
  rw [← volume_image_eq_lintegral_enorm_deriv_sq hf hs hinj, himg, Complex.volume_ball]
  simp [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

/-! ### The change of variables formula -/

/-- **The change of variables formula for a holomorphic injection.** Integrating over the image
`f '' s` is the same as integrating the pulled-back integrand against the area distortion
`‖deriv f z‖ ^ 2` over `s`.

Taking `g = 1` recovers `TauCeti.volume_image_eq_lintegral_enorm_deriv_sq`; that statement is not
deduced from this one, because it needs `s` only null measurable, while the weight forces the
measurability that Mathlib's `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`
asks for. -/
theorem lintegral_image_eq_lintegral_enorm_deriv_sq_mul (hf : ∀ z ∈ s, DifferentiableAt ℂ f z)
    (hs : MeasurableSet s) (hinj : InjOn f s) (g : ℂ → ℝ≥0∞) :
    ∫⁻ w in f '' s, g w = ∫⁻ z in s, ‖deriv f z‖ₑ ^ 2 * g (f z) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (hasFDerivWithinAt_smulRight_deriv hf) hinj g]
  exact lintegral_congr fun z => by rw [ofReal_abs_det_eq]

/-- **Integrability under the change of variables formula.** A function is integrable on the image
of a holomorphic injection exactly when its pullback, weighted by the area distortion, is
integrable on the source.

This is what makes `TauCeti.integral_image_eq_integral_norm_deriv_sq_smul` more than a statement
about the junk value `0` that the Bochner integral takes on non-integrable functions. -/
theorem integrableOn_image_iff_integrableOn_norm_deriv_sq_smul
    (hf : ∀ z ∈ s, DifferentiableAt ℂ f z) (hs : MeasurableSet s) (hinj : InjOn f s)
    (g : ℂ → E) :
    IntegrableOn g (f '' s) ↔ IntegrableOn (fun z => ‖deriv f z‖ ^ 2 • g (f z)) s := by
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs
    (hasFDerivWithinAt_smulRight_deriv hf) hinj g]
  exact integrableOn_congr_fun (fun z _ => by rw [abs_det_restrictScalars_smulRight_one]) hs

/-- **The change of variables formula, Bochner form.**

No integrability hypothesis is needed: if either side fails to be integrable then so does the
other, by `TauCeti.integrableOn_image_iff_integrableOn_norm_deriv_sq_smul`, and both Bochner
integrals are `0`. -/
theorem integral_image_eq_integral_norm_deriv_sq_smul (hf : ∀ z ∈ s, DifferentiableAt ℂ f z)
    (hs : MeasurableSet s) (hinj : InjOn f s) (g : ℂ → E) :
    ∫ w in f '' s, g w = ∫ z in s, ‖deriv f z‖ ^ 2 • g (f z) := by
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (hasFDerivWithinAt_smulRight_deriv hf) hinj g]
  exact setIntegral_congr_fun hs fun z _ => by rw [abs_det_restrictScalars_smulRight_one]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Analysis.Calculus.FDeriv.Inv
import TauCeti.Analysis.Complex.Determinant
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Analysis.Normed.Field.Inversion
import TauCeti.Analysis.RCLike.OperatorNorm

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
* `TauCeti.integrableOn_norm_fderiv_comp_inv_sq_iff` — inversion preserves finite energy: on any
  measurable set `s`, the squared norm of the derivative of `w ↦ u w⁻¹` is integrable on `s`
  exactly when that of `u` is integrable on `s⁻¹`.
* `TauCeti.integral_inv_sq_norm_sq_smul_eq` — the change of variables formula for the inversion:
  `∫ |w|⁻⁴ • g w = ∫ g z⁻¹`.
* `TauCeti.integral_norm_fderiv_comp_inv_apply_sq_le` — each directional energy after the
  inversion is bounded by the Dirichlet energy:
  `∫ ‖∂_v (f ∘ (·⁻¹))‖² ≤ ‖v‖² ∫ (‖∂₁ f‖² + ‖∂_i f‖²)`.
* `TauCeti.integrableOn_norm_fderiv_comp_inv_apply_one_sq` — for a solution of the
  Cauchy--Riemann equation `∂ₜu = J(u) ∂ₛu` with `‖J‖` bounded along it, integrability of
  `‖∂ₛu‖ ^ 2` outside a disc gives integrability of the same density for `w ↦ u w⁻¹` near `0`.

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
    ((measurable_deriv f).eNorm.pow_const 2).aemeasurable
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
    ← integral_toReal ((measurable_deriv f).eNorm.pow_const 2).aemeasurable
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
    lintegral_eq_zero_iff ((measurable_deriv f).eNorm.pow_const 2)]
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


/-! ### Inversion -/

/-- **Inversion preserves finite energy.** On a measurable set `s`, the squared norm of the
derivative of `w ↦ u w⁻¹` is integrable on `s` exactly when that of `u` is integrable on the image
`s⁻¹` of `s` under inversion: the area distortion `‖w‖⁻⁴` of the inversion is the square of the
factor `‖w‖⁻²` by which it scales derivatives. -/
theorem integrableOn_norm_fderiv_comp_inv_sq_iff {u : ℂ → E} (hs : MeasurableSet s) :
    IntegrableOn (fun w ↦ ‖fderiv ℝ (fun w ↦ u w⁻¹) w‖ ^ 2) s ↔
      IntegrableOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2) ((·⁻¹) '' s) := by
  -- Removing the origin, a null set fixed by the inversion, changes neither side.
  have hs0 : MeasurableSet (s \ {0}) := hs.diff (measurableSet_singleton 0)
  have himage : (·⁻¹) '' (s \ {0}) = (·⁻¹) '' s \ {(0 : ℂ)} := by
    rw [image_sdiff inv_injective, image_singleton, inv_zero]
  rw [← integrableOn_congr_set_ae (sdiff_null_ae_eq_self (measure_singleton 0)),
    ← integrableOn_congr_set_ae (s := (·⁻¹) '' s \ {(0 : ℂ)})
      (sdiff_null_ae_eq_self (measure_singleton 0)), ← himage,
    integrableOn_image_iff_integrableOn_norm_deriv_sq_smul
      (fun w (hw : w ∈ s \ {0}) ↦ differentiableAt_inv_iff.2 hw.2) hs0 inv_injective.injOn]
  refine integrableOn_congr_fun (fun w hw ↦ ?_) hs0
  have hw : (w : ℂ) ≠ 0 := hw.2
  rw [norm_fderiv_comp_inv hw, deriv_inv, smul_eq_mul, norm_neg, norm_inv, norm_pow]
  field_simp

/-- **The change of variables formula for the inversion.** The area distortion of `z ↦ z⁻¹` is
`‖z‖⁻⁴`, so the integral over `ℂ` of `g` weighted by `|w|⁻⁴` is the integral of `g` read in the
coordinate `z = w⁻¹`. As in `TauCeti.integral_image_eq_integral_norm_deriv_sq_smul`, no
integrability hypothesis is needed. -/
theorem integral_inv_sq_norm_sq_smul_eq (g : ℂ → E) :
    ∫ w, ((‖w‖ ^ 2) ^ 2)⁻¹ • g w = ∫ z, g z⁻¹ := by
  have h := integral_image_eq_integral_norm_deriv_sq_smul (f := (·⁻¹))
    (fun z (hz : z ∈ ({0}ᶜ : Set ℂ)) ↦ differentiableAt_inv hz)
    (measurableSet_singleton 0).compl inv_injective.injOn fun w ↦ g w⁻¹
  rw [image_inv_eq_inv, compl_inv, inv_singleton, inv_zero, restrict_compl_singleton] at h
  rw [h]
  congr 1
  ext z
  simp [deriv_inv]

/-- **Each directional energy after the inversion is bounded by the Dirichlet energy.** For a map
`f` of `ℂ` with integrable Dirichlet energy, the energy of the derivative of `z ↦ f z⁻¹` in a
direction `v` is at most `‖v‖ ^ 2` times the Dirichlet energy of `f`. The target norm is
arbitrary, so the bound comes from Cauchy–Schwarz (`TauCeti.norm_smul_add_smul_sq_le`) rather than
from conformal invariance. -/
theorem integral_norm_fderiv_comp_inv_apply_sq_le {f : ℂ → E} (v : ℂ)
    (hE : Integrable fun w ↦ ‖fderiv ℝ f w 1‖ ^ 2 + ‖fderiv ℝ f w I‖ ^ 2) :
    ∫ z, ‖fderiv ℝ (fun z ↦ f z⁻¹) z v‖ ^ 2 ≤
      ‖v‖ ^ 2 * ∫ w, (‖fderiv ℝ f w 1‖ ^ 2 + ‖fderiv ℝ f w I‖ ^ 2) := by
  set G : ℂ → ℝ := fun w ↦ ‖fderiv ℝ f w 1‖ ^ 2 + ‖fderiv ℝ f w I‖ ^ 2
  have hs : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton 0).compl
  have hd (z : ℂ) (hz : z ∈ ({0}ᶜ : Set ℂ)) : DifferentiableAt ℂ (·⁻¹) z := differentiableAt_inv hz
  have himage : (·⁻¹) '' ({0}ᶜ : Set ℂ) = {0}ᶜ := by
    rw [image_inv_eq_inv, compl_inv, inv_singleton, inv_zero]
  -- Pointwise, `‖∂_v (f ∘ inv)‖² ≤ ‖v‖² ‖(z⁻¹)'‖² G(z⁻¹)`, by Cauchy–Schwarz in the real
  -- coordinates of the direction `-(z²)⁻¹ v`.
  have hpt (z : ℂ) (hz : z ∈ ({0}ᶜ : Set ℂ)) :
      ‖fderiv ℝ (fun z ↦ f z⁻¹) z v‖ ^ 2 ≤ ‖v‖ ^ 2 * ‖deriv (·⁻¹) z‖ ^ 2 • G z⁻¹ := by
    have hc : -(z ^ 2)⁻¹ * v = (-(z ^ 2)⁻¹ * v).re • (1 : ℂ) + (-(z ^ 2)⁻¹ * v).im • I := by
      rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
    have hn : (-(z ^ 2)⁻¹ * v).re ^ 2 + (-(z ^ 2)⁻¹ * v).im ^ 2 =
        ‖v‖ ^ 2 * ‖deriv (·⁻¹) z‖ ^ 2 := by
      rw [deriv_inv, ← mul_pow, ← norm_mul, mul_comm, Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [fderiv_comp_inv_apply hz, hc, map_add, map_smul, map_smul, smul_eq_mul, ← mul_assoc,
      ← hn]
    exact norm_smul_add_smul_sq_le _ _ _ _
  have hGi : IntegrableOn (fun z ↦ ‖deriv (·⁻¹) z‖ ^ 2 • G z⁻¹) {0}ᶜ :=
    (integrableOn_image_iff_integrableOn_norm_deriv_sq_smul hd hs inv_injective.injOn G).1
      (himage ▸ hE.integrableOn)
  calc ∫ z, ‖fderiv ℝ (fun z ↦ f z⁻¹) z v‖ ^ 2
      = ∫ z in {0}ᶜ, ‖fderiv ℝ (fun z ↦ f z⁻¹) z v‖ ^ 2 := by
        rw [restrict_compl_singleton]
    _ ≤ ∫ z in {0}ᶜ, ‖v‖ ^ 2 * ‖deriv (·⁻¹) z‖ ^ 2 • G z⁻¹ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _) (hGi.const_mul _)
          ((ae_restrict_iff' hs).2 (Filter.Eventually.of_forall hpt))
    _ = ‖v‖ ^ 2 * ∫ w in (·⁻¹) '' {0}ᶜ, G w := by
        rw [integral_const_mul, integral_image_eq_integral_norm_deriv_sq_smul hd hs
          inv_injective.injOn G]
    _ = ‖v‖ ^ 2 * ∫ w, G w := by rw [himage, restrict_compl_singleton]

/-- **The energy near infinity is the energy of the inverted map near zero**, up to a constant:
for a solution of `∂ₜu = J(u) ∂ₛu` outside the disc of radius `R`, with `‖J‖ ≤ M` along it, the
map `w ↦ u w⁻¹` has integrable energy density on the disc of radius `R⁻¹` whenever `u` has
integrable energy density outside the disc of radius `R`. The Cauchy--Riemann equation bounds
`‖du‖` by `(1 + M) ‖∂ₛu‖`, and inversion preserves finite energy
(`TauCeti.integrableOn_norm_fderiv_comp_inv_sq_iff`). -/
theorem integrableOn_norm_fderiv_comp_inv_apply_one_sq [CompleteSpace E] {u : ℂ → E}
    {J : E → E →L[ℝ] E} {R M : ℝ}
    (hCR : ∀ z ∈ (closedBall (0 : ℂ) R)ᶜ, fderiv ℝ u z I = J (u z) (fderiv ℝ u z 1))
    (hM : ∀ z ∈ (closedBall (0 : ℂ) R)ᶜ, ‖J (u z)‖ ≤ M)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (closedBall 0 R)ᶜ) :
    IntegrableOn (fun w ↦ ‖fderiv ℝ (fun w ↦ u w⁻¹) w 1‖ ^ 2) (ball 0 R⁻¹) := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  set D : Set ℂ := ball 0 R⁻¹ \ {0}
  have hDE := mapsTo_inv_ball_diff_singleton_compl_closedBall (𝕜 := ℂ) R
  have hDm : MeasurableSet D := measurableSet_ball.diff (measurableSet_singleton 0)
  -- By the Cauchy--Riemann equation, `‖du‖ ≤ (1 + M) ‖∂ₛu‖` outside the disc of radius `R`.
  have hfull : IntegrableOn (fun z ↦ ‖fderiv ℝ u z‖ ^ 2) (closedBall 0 R)ᶜ := by
    refine (henergy.const_mul ((1 + M) ^ 2)).mono'
      ((measurable_fderiv ℝ u).norm.pow_const 2).aestronglyMeasurable
      (ae_restrict_of_forall_mem isClosed_closedBall.isOpen_compl.measurableSet fun z hz ↦ ?_)
    rw [norm_pow, norm_norm, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((fderiv ℝ u z).norm_le_of_apply_I_eq (hCR z hz) (hM z hz) le_rfl) 2
  -- Inversion preserves finite energy.
  have hD : IntegrableOn (fun w ↦ ‖fderiv ℝ (fun w ↦ u w⁻¹) w‖ ^ 2) D :=
    (integrableOn_norm_fderiv_comp_inv_sq_iff hDm).2 (hfull.mono_set hDE.image_subset)
  have hD1 : IntegrableOn (fun w ↦ ‖fderiv ℝ (fun w ↦ u w⁻¹) w 1‖ ^ 2) D := by
    refine hD.mono' ((measurable_fderiv_apply_const ℝ _ 1).norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun w ↦ ?_)
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (by simpa using (fderiv ℝ (fun w ↦ u w⁻¹) w).le_opNorm (1 : ℂ)) 2
  exact hD1.congr_set_ae (sdiff_null_ae_eq_self (measure_singleton 0)).symm

end TauCeti

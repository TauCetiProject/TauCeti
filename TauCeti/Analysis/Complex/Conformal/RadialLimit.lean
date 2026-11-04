/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Area
public import TauCeti.MeasureTheory.Integral.Circle.LIntegral
import Mathlib.Algebra.Order.ToIntervalMod
import TauCeti.Analysis.Complex.Conformal.LengthArea
import TauCeti.MeasureTheory.Integral.DominatedIncrement

/-!
# Radial limits of a holomorphic map of finite length–area

A holomorphic map `f` of the disc `ball c R` has a **radial limit** at the angle `θ` when
`f (circleMap c r θ)` converges as `r` increases to `R`. This file proves that radial limits exist
at almost every angle as soon as `‖deriv f‖` is integrable on the disc, and in particular as soon
as `f` has a finite Dirichlet integral `∫⁻ z in ball c R, ‖deriv f z‖ₑ ^ 2`. By the area formula of
`Conformal/Area.lean` this covers every holomorphic injection of the disc whose image has finite
area, for instance a Riemann map onto a bounded domain.

This is the radial half of the length–area method. Its circular half, in
`Conformal/LengthArea.lean`, makes the images of some circular arcs short; here the same plane
integral, taken in polar coordinates with the angle outside, makes almost every *radius* have an
image of finite length.

## The argument

Fix `0 < a < R`. Along the radius at angle `θ` the derivative of `r ↦ f (circleMap c r θ)` has norm
`‖deriv f (circleMap c r θ)‖`, so by the fundamental theorem of calculus the increments of `f` along
the radius are dominated by the **radial length density** `r ↦ ‖deriv f (circleMap c r θ)‖ₑ`
(`TauCeti.edist_comp_circleMap_le_lintegral_Ioc`, the chord bound
`TauCeti.edist_comp_le_lintegral_Ioc` of `Conformal/LengthArea.lean` along the ray). On `Ioo a R`
the factor `r / a` is at least `1`, so integrating the radial lengths over one period of angles is
bounded, through polar Fubini `TauCeti.lintegral_Ioc_lintegral_Ioi_circleMap_eq_lintegral`, by `a⁻¹`
times the plane integral of `‖deriv f‖ₑ` over the disc
(`TauCeti.lintegral_Ioc_lintegral_Ioo_enorm_deriv_circleMap_le`). If that is finite, almost every
radius has image of finite length; along such a radius `f` is uniformly continuous
(`Set.OrdConnected.uniformContinuousOn_of_edist_le_setLIntegral`), hence Cauchy as `r → R`, and `ℂ`
is complete.

## Main results

* `TauCeti.edist_comp_circleMap_le_lintegral_Ioc` — the radial chord bound.
* `TauCeti.ae_exists_tendsto_circleMap_of_lintegral_enorm_deriv_ne_top` — radial limits exist at
  almost every angle when `‖deriv f‖` is integrable on the disc.
* `TauCeti.ae_exists_tendsto_circleMap_of_lintegral_enorm_deriv_sq_ne_top` — the same for a finite
  Dirichlet integral.
* `TauCeti.ae_exists_tendsto_circleMap_of_injOn_of_volume_image_ne_top` — the same for a
  holomorphic injection of the disc whose image has finite area, such as a bounded image.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2 (the length–area method).
-/

public section

namespace TauCeti

open Complex Filter MeasureTheory Metric Set Topology
open scoped ENNReal Real

variable {U : Set ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ}

/-- **The radial chord bound.** If the segment of the ray at angle `θ` between the radii `a ≤ b`
lies in an open set on which `f` is holomorphic, the images of its endpoints are at distance at
most the integral of `‖deriv f‖` along it. -/
theorem edist_comp_circleMap_le_lintegral_Ioc (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (c : ℂ) (θ : ℝ) {a b : ℝ} (hab : a ≤ b) (hmemU : ∀ r ∈ Icc a b, circleMap c r θ ∈ U) :
    edist (f (circleMap c a θ)) (f (circleMap c b θ)) ≤
      ∫⁻ r in Ioc a b, ‖deriv f (circleMap c r θ)‖ₑ := by
  have hray : ∀ r, HasDerivAt (fun r : ℝ => circleMap c r θ) (exp (θ * I)) r := fun r => by
    simpa [circleMap] using ((hasDerivAt_id r).ofReal_comp.mul_const (exp (θ * I))).const_add c
  -- the ray has constant velocity `exp (θ * I)`, of norm `1`, so it is `C¹`
  have hrayC : ContDiff ℝ 1 (fun r : ℝ => circleMap c r θ) := by
    refine contDiff_one_iff_deriv.2 ⟨fun r => (hray r).differentiableAt, ?_⟩
    rw [funext fun r => (hray r).deriv]
    exact continuous_const
  simpa [(hray _).deriv] using edist_comp_le_lintegral_Ioc hUo hf hrayC.contDiffOn hab hmemU

/-- **The radial length–area inequality.** For `0 < a`, the lengths of the images of the radial
segments from radius `a` to radius `R`, integrated over one period of angles, are at most `a⁻¹`
times the plane integral of `‖deriv f‖ₑ` over the disc `ball c R`. -/
theorem lintegral_Ioc_lintegral_Ioo_enorm_deriv_circleMap_le (c : ℂ) {a : ℝ} (ha : 0 < a)
    (R t : ℝ) :
    ∫⁻ θ in Ioc t (t + 2 * π), ∫⁻ r in Ioo a R, ‖deriv f (circleMap c r θ)‖ₑ ≤
      ENNReal.ofReal a⁻¹ * ∫⁻ z in ball c R, ‖deriv f z‖ₑ := by
  have hg : Measurable ((ball c R).indicator fun z => ‖deriv f z‖ₑ) :=
    (measurable_deriv f).enorm.indicator measurableSet_ball
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_Ioc_lintegral_Ioi_circleMap_eq_lintegral
    hg c t, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun θ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ r in Ioo a R, ‖deriv f (circleMap c r θ)‖ₑ
      ≤ ∫⁻ r in Ioo a R, ENNReal.ofReal a⁻¹ * (ENNReal.ofReal r *
          (ball c R).indicator (fun z => ‖deriv f z‖ₑ) (circleMap c r θ)) := by
        refine setLIntegral_mono' measurableSet_Ioo fun r hr => ?_
        have hmem : circleMap c r θ ∈ ball c R :=
          sphere_subset_ball hr.2 (circleMap_mem_sphere c (ha.trans hr.1).le θ)
        -- on `Ioo a R` the factor `a⁻¹ * r` is at least `1`
        have h1 : (1 : ℝ) ≤ a⁻¹ * r := (one_le_div ha).2 hr.1.le |>.trans_eq (div_eq_inv_mul r a)
        rw [indicator_of_mem hmem, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 ha.le)]
        exact le_mul_of_one_le_left zero_le (ENNReal.one_le_ofReal.2 h1)
    _ ≤ ∫⁻ r in Ioi 0, ENNReal.ofReal a⁻¹ * (ENNReal.ofReal r *
          (ball c R).indicator (fun z => ‖deriv f z‖ₑ) (circleMap c r θ)) :=
        lintegral_mono_set fun r hr => ha.trans hr.1

/-- **Radial limits exist almost everywhere** for a holomorphic map of a disc whose derivative is
integrable on it: for almost every angle `θ`, `f (circleMap c r θ)` converges as `r` increases to
`R`. -/
theorem ae_exists_tendsto_circleMap_of_lintegral_enorm_deriv_ne_top
    (hf : DifferentiableOn ℂ f (ball c R)) (hR : 0 < R)
    (hfin : ∫⁻ z in ball c R, ‖deriv f z‖ₑ ≠ ⊤) :
    ∀ᵐ θ, ∃ L, Tendsto (fun r => f (circleMap c r θ)) (𝓝[<] R) (𝓝 L) := by
  set a := R / 2
  have ha : 0 < a := half_pos hR
  have haR : a < R := half_lt_self hR
  -- Almost every radius has an image of finite length.
  have hlen : ∀ t : ℝ, ∀ᵐ θ ∂volume.restrict (Ioc t (t + 2 * π)),
      ∫⁻ r in Ioo a R, ‖deriv f (circleMap c r θ)‖ₑ ≠ ⊤ := fun t => by
    have hmeas : Measurable fun θ => ∫⁻ r in Ioo a R, ‖deriv f (circleMap c r θ)‖ₑ :=
      ((measurable_deriv f).enorm.comp (by simp only [circleMap]; fun_prop :
        Continuous fun p : ℝ × ℝ => circleMap c p.2 p.1).measurable).lintegral_prod_right'
    refine ae_lt_top hmeas (ne_top_of_le_ne_top ?_
      (lintegral_Ioc_lintegral_Ioo_enorm_deriv_circleMap_le c ha R t)) |>.mono fun _ h => h.ne
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hall : ∀ᵐ θ, ∫⁻ r in Ioo a R, ‖deriv f (circleMap c r θ)‖ₑ ≠ ⊤ := by
    have h := (ae_restrict_iUnion_iff (fun n : ℤ => Ioc (0 + n • (2 * π)) (0 + (n + 1) • (2 * π)))
      _).2 fun n => by simpa only [zero_add, add_smul, one_smul] using hlen (n • (2 * π))
    rwa [iUnion_Ioc_add_zsmul Real.two_pi_pos 0, Measure.restrict_univ] at h
  -- Along such a radius `f` is uniformly continuous, hence has a limit at the end.
  filter_upwards [hall] with θ hθ
  have hmem : ∀ r ∈ Ioo a R, circleMap c r θ ∈ ball c R := fun r hr =>
    sphere_subset_ball hr.2 (circleMap_mem_sphere c (ha.trans hr.1).le θ)
  have huc : UniformContinuousOn (fun r => f (circleMap c r θ)) (Ioo a R) :=
    ordConnected_Ioo.uniformContinuousOn_of_edist_le_setLIntegral
      (fun x hx y hy hxy => edist_comp_circleMap_le_lintegral_Ioc isOpen_ball hf c θ hxy
        fun r hr => hmem r ⟨hx.1.trans_le hr.1, hr.2.trans_lt hy.2⟩) hθ
  have hcau : Cauchy (map (fun r => f (circleMap c r θ)) (𝓝[<] R)) :=
    (cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le huc (le_principal_iff.2 (Ioo_mem_nhdsLT haR))
  exact cauchy_map_iff_exists_tendsto.1 hcau

/-- **Radial limits exist almost everywhere** for a holomorphic map of a disc with a finite
Dirichlet integral. On the disc, of finite area, square integrability of `‖deriv f‖` implies its
integrability. -/
theorem ae_exists_tendsto_circleMap_of_lintegral_enorm_deriv_sq_ne_top
    (hf : DifferentiableOn ℂ f (ball c R)) (hR : 0 < R)
    (hfin : ∫⁻ z in ball c R, ‖deriv f z‖ₑ ^ 2 ≠ ⊤) :
    ∀ᵐ θ, ∃ L, Tendsto (fun r => f (circleMap c r θ)) (𝓝[<] R) (𝓝 L) := by
  -- pointwise `x ≤ 1 + x ^ 2`, and the disc has finite area
  have hsq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
    rcases le_total x 1 with hx | hx
    · exact hx.trans le_self_add
    · exact (le_mul_of_one_le_right zero_le hx).trans ((sq x).ge.trans le_add_self)
  refine ae_exists_tendsto_circleMap_of_lintegral_enorm_deriv_ne_top hf hR
    (ne_top_of_le_ne_top ?_ (lintegral_mono fun z => hsq ‖deriv f z‖ₑ))
  rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul]
  exact ENNReal.add_ne_top.2 ⟨measure_ball_lt_top.ne, hfin⟩

/-- **A conformal map of a disc onto a region of finite area has radial limits almost
everywhere.** For a holomorphic injection `f` of `ball c R` whose image has finite area, in
particular one with bounded image, `f (circleMap c r θ)` converges as `r` increases to `R` for
almost every angle `θ`. -/
theorem ae_exists_tendsto_circleMap_of_injOn_of_volume_image_ne_top
    (hf : DifferentiableOn ℂ f (ball c R)) (hR : 0 < R) (hinj : InjOn f (ball c R))
    (hvol : volume (f '' ball c R) ≠ ⊤) :
    ∀ᵐ θ, ∃ L, Tendsto (fun r => f (circleMap c r θ)) (𝓝[<] R) (𝓝 L) :=
  ae_exists_tendsto_circleMap_of_lintegral_enorm_deriv_sq_ne_top hf hR
    (lintegral_enorm_deriv_sq_ne_top isOpen_ball hf measurableSet_ball.nullMeasurableSet
      subset_rfl hinj hvol)

end TauCeti

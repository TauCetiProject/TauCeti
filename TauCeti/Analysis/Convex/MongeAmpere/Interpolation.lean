/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Decomposition
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import TauCeti.MeasureTheory.Measure.ChangeOfVariables

/-!
# The Jacobian equation along the interpolation of a convex gradient

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `ρ`, and
let `f : E → EReal` be convex (convex real epigraph, never `⊥`), with real representative
`F x = (f x).toReal` and `D` the interior of its effective domain. For `0 ≤ t ≤ 1` the
*interpolating map* `Tₜ x = (1 - t) • x + t • ∇F x` moves each point a fraction `t` of the way
to its image under the gradient. For a law `μ`, the laws `μₜ = (Tₜ)₊ μ` form McCann's
displacement interpolation from `μ₀ = μ` to `μ₁ = (∇F)₊ μ`; when `∇F` is the Brenier map of `μ`
they trace the quadratic Wasserstein geodesic from `μ` to its target.

This file shows that for `t < 1` the interpolating map never concentrates mass, however
degenerate `∇F` is. At a point `x` where the subdifferential of `f` is the
single gradient `∇F x` with a first-order expansion `y' = ∇F x + H x (x' - x) + o(‖x' - x‖)`
(by Alexandrov's theorem, almost every point of `D`), the interpolating map has derivative
`Jₜ x = (1 - t) • 1 + t • H x` within the set of such points. Since `H x` is a positive operator,
`det (Jₜ x) > 0` for `t < 1`. Monotonicity of the subdifferential gives
`(1 - t) ‖x₁ - x₂‖ ≤ ‖Tₜ x₁ - Tₜ x₂‖`, so `Tₜ` is injective there. Mathlib's change of variables
formula therefore applies with no degenerate part:

  `∫_{Tₜ(s)} g dρ = ∫_s det (Jₜ x) g (Tₜ x) dρ`.

Consequently, for `0 ≤ t < 1` and every measure `μ ≪ ρ` carried by `D` (s-finite for the last
two statements):

* `μₜ` is absolutely continuous with respect to `ρ`, even when `μ₁` is not;
* the densities satisfy the **Jacobian equation** `dμ/dρ (x) = det (Jₜ x) * dμₜ/dρ (Tₜ x)` for
  `ρ`-almost every `x ∈ D`, and `dμ/dρ = 0` almost everywhere off `D`;
* integrals of the density of `μₜ` are integrals over the source:
  `∫ Φ (dμₜ/dρ) dρ = ∫_D det (Jₜ x) Φ (dμ/dρ (x) / det (Jₜ x)) dρ` whenever `Φ 0 = 0`.

The last formula, applied to the positive and negative parts of `U`, rewrites the internal energy
`∫ U (dμₜ/dρ) dρ` of the interpolant as an integral against the fixed source, in which `t` enters
only through `det (Jₜ x)`. Since `A ↦ det A ^ (1 / n)` is concave on positive operators
(`LinearMap.concaveOn_det_rpow`), this is the formula behind McCann's displacement convexity of
internal energies.

At `t = 1` the interpolating map is the gradient itself, whose Jacobian `det (H x)` may vanish.
The gradient is injective where `det (H x) ≠ 0` and maps the degenerate set `{det (H x) = 0}` to a
null set, so the endpoint `μ₁ = (∇F)₊ μ` splits into an absolutely continuous part, the image of
`μ` restricted to the nondegenerate set, and a singular part of total mass `μ {det (H x) = 0}`.
The integral formula above then holds at `t = 1` for the absolutely continuous part.

## Main statements

* `TauCeti.withDensity_image_smul_add_smul_gradient_eq_setLIntegral` — the change of variables
  formula along the interpolating map;
* `TauCeti.map_smul_add_smul_gradient_absolutelyContinuous` — the interpolants of an absolutely
  continuous law are absolutely continuous;
* `TauCeti.rnDeriv_ae_eq_indicator_ofReal_det_mul_rnDeriv_map_smul_add_smul_gradient` — the
  Jacobian equation of the interpolating map;
* `TauCeti.lintegral_comp_rnDeriv_map_smul_add_smul_gradient` — integrals of functions of the
  density of an interpolant, as integrals over the source;
* `TauCeti.singularPart_map_gradient_apply_univ` — the singular part of the endpoint `(∇F)₊ μ` has
  total mass `μ {det (H x) = 0}`;
* `TauCeti.lintegral_comp_rnDeriv_map_gradient` — integrals of functions of the density of the
  endpoint, as integrals over the source.

## References

* R. J. McCann, *A convexity principle for interacting gases*, Adv. Math. 128 (1997), 153–179,
  Section 4, for the Jacobian equation along the interpolation of a convex gradient and its use
  in displacement convexity.
* C. Villani, *Topics in Optimal Transportation*, Graduate Studies in Mathematics 58, American
  Mathematical Society, 2003, Chapters 4 and 5.
-/

public section

namespace TauCeti

open MeasureTheory Measure Set Filter
open scoped Topology ENNReal InnerProductSpace Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → EReal}

/-- The interpolating map `x ↦ (1 - t) • x + t • ∇F x` is measurable. -/
private theorem measurable_smul_add_smul_gradient [MeasurableSpace E] [BorelSpace E] (t : ℝ) :
    Measurable fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x :=
  (measurable_id.const_smul _).add ((measurable_gradient _).const_smul _)

/-- The interpolating map `x ↦ (1 - t) • x + t • ∇F x` has derivative `(1 - t) • 1 + t • H x`
within a set `s` at each point of which the subdifferential of `f` is the single gradient with
the expansion `y' = ∇F x + H x (x' - x) + o(‖x' - x‖)`. -/
private theorem hasFDerivWithinAt_smul_add_smul_gradient {H : E → E →L[ℝ] E} {s : Set E}
    (hP : ∀ x ∈ s, subdifferential (innerₗ E) f x = {(∇ fun x' => (f x').toReal) x} ∧
      (H x).IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
        ‖y' - (∇ fun x' => (f x').toReal) x - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    (t : ℝ) {x : E} (hx : x ∈ s) :
    HasFDerivWithinAt (fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x)
      ((1 - t) • ContinuousLinearMap.id ℝ E + t • H x) s x :=
  ((hasFDerivWithinAt_id x s).const_smul (1 - t)).add
    ((hasFDerivWithinAt_gradient_toReal_of_forall_mem_subdifferential_norm_sub_le
      (fun x' hx' => by rw [(hP x' hx').1]; exact mem_singleton _) (hP x hx).2.2).const_smul t)

/-- For `0 ≤ t < 1`, the interpolating map `x ↦ (1 - t) • x + t • ∇F x` is injective on a set
at each point of which the subdifferential of `f` is the single gradient. -/
private theorem injOn_smul_add_smul_gradient {H : E → E →L[ℝ] E} {s : Set E}
    (hP : ∀ x ∈ s, subdifferential (innerₗ E) f x = {(∇ fun x' => (f x').toReal) x} ∧
      (H x).IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
        ‖y' - (∇ fun x' => (f x').toReal) x - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    InjOn (fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x) s := by
  have hs : ∀ x ∈ s, (∇ fun x' => (f x').toReal) x ∈ subdifferential (innerₗ E) f x :=
    fun x hx => by rw [(hP x hx).1]; exact mem_singleton _
  intro x₁ hx₁ x₂ hx₂ h
  have hle := mul_norm_sub_le_norm_smul_add_smul_sub_of_mem_subdifferential ht₀ (hs x₁ hx₁)
    (hs x₂ hx₂)
  simp only at h
  rw [h, sub_self, norm_zero] at hle
  have : ‖x₁ - x₂‖ = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right hle (by linarith)) (norm_nonneg _)
  rwa [norm_eq_zero, sub_eq_zero] at this

/-- The Jacobian `x ↦ det ((1 - t) • 1 + t • H x)` of the interpolating map is measurable when
`H` is. -/
private theorem measurable_ofReal_det_one_sub_smul_id_add_smul [MeasurableSpace E]
    {H : E → E →L[ℝ] E} (hH : Measurable H) (t : ℝ) :
    Measurable fun x => ENNReal.ofReal ((1 - t) • ContinuousLinearMap.id ℝ E + t • H x).det :=
  ENNReal.measurable_ofReal.comp (ContinuousLinearMap.continuous_det.measurable.comp
    (measurable_const.add (hH.const_smul t)))

/-- For `0 ≤ t < 1`, the interpolating map `x ↦ (1 - t) • x + t • ∇F x` sends a measurable set at
each point of which the subdifferential of `f` is the single gradient with a first-order expansion
to a measurable set. -/
private theorem measurableSet_image_smul_add_smul_gradient [MeasurableSpace E] [BorelSpace E]
    {H : E → E →L[ℝ] E} {s : Set E} (hs : MeasurableSet s)
    (hP : ∀ x ∈ s, subdifferential (innerₗ E) f x = {(∇ fun x' => (f x').toReal) x} ∧
      (H x).IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
        ‖y' - (∇ fun x' => (f x').toReal) x - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    MeasurableSet ((fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x) '' s) :=
  measurable_image_of_fderivWithin hs (fun _ hx => hasFDerivWithinAt_smul_add_smul_gradient hP t hx)
    (injOn_smul_add_smul_gradient hP ht₀ ht₁)

variable [MeasurableSpace E] [BorelSpace E] (ρ : Measure E) [ρ.IsAddHaarMeasure]

/-- If almost every point of the interior `D` of the effective domain of a convex `f` has a
first-order expansion of the subdifferential with derivative `H x`, then every measure `μ ≪ ρ`
carried by `D` is carried by the measurable set of points supplied by
`exists_measurableSet_ae_eq_interior_subdifferential_eq_gradient`, on which `H` agrees with a
measurable `H'`; the expansion is stated for `H'`. -/
private theorem exists_measurableSet_restrict_eq_self
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂ρ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {μ : Measure E} (hμ : μ ≪ ρ) (hμD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤}) :
    ∃ S, MeasurableSet S ∧ S ⊆ interior {x | f x ≠ ⊤} ∧ interior {x | f x ≠ ⊤} =ᵐ[ρ] S ∧
      μ.restrict S = μ ∧ ∃ H' : E → E →L[ℝ] E, Measurable H' ∧ (∀ x ∈ S, H x = H' x) ∧
      ∀ x ∈ S, subdifferential (innerₗ E) f x = {(∇ fun x' => (f x').toReal) x} ∧
        (H' x).IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
          ‖y' - (∇ fun x' => (f x').toReal) x - H' x (x' - x)‖ ≤ ε * ‖x' - x‖ := by
  obtain ⟨S, hSm, hSD, hDS, hS, H', hH'm, hHS⟩ :=
    exists_measurableSet_ae_eq_interior_subdifferential_eq_gradient ρ hf hbot hH
  exact ⟨S, hSm, hSD, hDS, restrict_eq_self_of_ae_mem (mem_ae_iff.2
    ((measure_congr (EventuallyEqSet.compl (hμ.ae_eq hDS))).symm.trans (mem_ae_iff.1 hμD))),
    H', hH'm, hHS, fun x hx => hHS x hx ▸ hS x hx⟩

/-- **Change of variables along the interpolating map.** Let `s` be a measurable set at each point
of which the subdifferential of `f : E → EReal` is the single gradient `∇F x` of its real
representative, with the expansion `y' = ∇F x + H x (x' - x) + o(‖x' - x‖)` for a positive
`H x`. For `0 ≤ t < 1` the interpolating map `Tₜ x = (1 - t) • x + t • ∇F x` is injective on `s`,
with derivative `(1 - t) • 1 + t • H x` of positive determinant, so for every additive Haar
measure `ρ` and every `g`,
`∫_{Tₜ(s)} g dρ = ∫_s det ((1 - t) • 1 + t • H x) g (Tₜ x) dρ`. -/
theorem withDensity_image_smul_add_smul_gradient_eq_setLIntegral {H : E → E →L[ℝ] E}
    {s : Set E} (hs : MeasurableSet s)
    (hP : ∀ x ∈ s, subdifferential (innerₗ E) f x = {(∇ fun x' => (f x').toReal) x} ∧
      (H x).IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
        ‖y' - (∇ fun x' => (f x').toReal) x - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) (g : E → ℝ≥0∞) :
    ρ.withDensity g ((fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x) '' s) =
      ∫⁻ x in s, ENNReal.ofReal ((1 - t) • ContinuousLinearMap.id ℝ E + t • H x).det *
        g ((1 - t) • x + t • (∇ fun x' => (f x').toReal) x) ∂ρ := by
  rw [withDensity_apply',
    lintegral_image_eq_lintegral_abs_det_fderiv_mul ρ hs
      (fun _ hx => hasFDerivWithinAt_smul_add_smul_gradient hP t hx)
      (injOn_smul_add_smul_gradient hP ht₀ ht₁) g]
  refine setLIntegral_congr_fun hs fun x hx => ?_
  rw [abs_of_pos ((hP x hx).2.1.det_one_sub_smul_id_add_smul_pos ht₀ ht₁)]

/-- `withDensity_image_smul_add_smul_gradient_eq_setLIntegral` on every measurable subset of a set
`S` of points with a first-order expansion, in the form taken by the lemmas of
`TauCeti.MeasureTheory.Measure.ChangeOfVariables`. -/
private theorem withDensity_image_smul_add_smul_gradient_eq_setLIntegral_of_subset
    {H : E → E →L[ℝ] E} {S : Set E}
    (hS : ∀ x ∈ S, subdifferential (innerₗ E) f x = {(∇ fun x' => (f x').toReal) x} ∧
      (H x).IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
        ‖y' - (∇ fun x' => (f x').toReal) x - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    ∀ s, MeasurableSet s → s ⊆ S → ∀ g : E → ℝ≥0∞,
      ρ.withDensity g ((fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x) '' s) =
        ∫⁻ x in s, ENNReal.ofReal ((1 - t) • ContinuousLinearMap.id ℝ E + t • H x).det *
          g ((1 - t) • x + t • (∇ fun x' => (f x').toReal) x) ∂ρ :=
  fun _ hs hsS => withDensity_image_smul_add_smul_gradient_eq_setLIntegral ρ hs
    (fun x hx => hS x (hsS hx)) ht₀ ht₁

/-- **Interpolants of an absolutely continuous law are absolutely continuous.** Let `f : E → EReal`
be convex (convex real epigraph, never `⊥`), with real representative `F`, and let `μ` be a measure
absolutely continuous with respect to an additive Haar measure `ρ` and carried by the interior of
the effective domain of `f`. For `0 ≤ t < 1`, the pushforward of `μ` by the interpolating map
`x ↦ (1 - t) • x + t • ∇F x` is absolutely continuous with respect to `ρ`. This holds whether or not
the pushforward `(∇F)₊ μ` at `t = 1` is absolutely continuous. -/
theorem map_smul_add_smul_gradient_absolutelyContinuous (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) {μ : Measure E} (hμ : μ ≪ ρ)
    (hμD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤}) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    μ.map (fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x) ≪ ρ := by
  obtain ⟨H, hH, -⟩ := exists_mongeAmpereMeasure_eq_singularPart_add_withDensity ρ hf hbot
  obtain ⟨S, hSm, -, -, hμS, H', hH'm, -, hS⟩ := exists_measurableSet_restrict_eq_self ρ hf
    hbot (H := H) (by filter_upwards [hH] with x hx hxD; exact ⟨_, (hx (interior_subset hxD)).2⟩)
    hμ hμD
  -- Change variables on `S`, with the positive Jacobian `det ((1 - t) • 1 + t • H' x)`.
  rw [← hμS]
  exact map_restrict_absolutelyContinuous_of_withDensity_image_eq ρ
    (measurable_smul_add_smul_gradient t) hSm
    (measurable_ofReal_det_one_sub_smul_id_add_smul hH'm t)
    (fun x hx => (ENNReal.ofReal_pos.2
      ((hS x hx).2.1.det_one_sub_smul_id_add_smul_pos ht₀ ht₁)).ne')
    (withDensity_image_smul_add_smul_gradient_eq_setLIntegral_of_subset ρ hS ht₀ ht₁) hμ

/-- **The Jacobian equation along the interpolation of a convex gradient.** Let `f : E → EReal` be
convex (convex real epigraph, never `⊥`), with real representative `F` and `D` the interior of its
effective domain, and let `H x` be, for almost every `x ∈ D`, a first-order expansion of the
subdifferential of `f` at `x` (the Alexandrov Hessian, see
`rnDeriv_mongeAmpereMeasure_withDensity_ae_eq`). Let `μ` be an s-finite measure, absolutely
continuous with respect to an additive Haar measure `ρ` and carried by `D`, and let `0 ≤ t < 1`.
Then the density of `μ` and the density of its interpolant `μₜ = (Tₜ)₊ μ`, with
`Tₜ x = (1 - t) • x + t • ∇F x`, satisfy
`dμ/dρ (x) = det ((1 - t) • 1 + t • H x) * dμₜ/dρ (Tₜ x)` for almost every `x ∈ D`, and
`dμ/dρ = 0` almost everywhere off `D`. -/
theorem rnDeriv_ae_eq_indicator_ofReal_det_mul_rnDeriv_map_smul_add_smul_gradient
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂ρ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {μ : Measure E} [SFinite μ] (hμ : μ ≪ ρ) (hμD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤})
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    μ.rnDeriv ρ =ᵐ[ρ] (interior {x | f x ≠ ⊤}).indicator fun x =>
      ENNReal.ofReal ((1 - t) • ContinuousLinearMap.id ℝ E + t • H x).det *
        (μ.map fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x).rnDeriv ρ
          ((1 - t) • x + t • (∇ fun x' => (f x').toReal) x) := by
  set T := fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x
  set g := (μ.map T).rnDeriv ρ
  have hT : Measurable T := measurable_smul_add_smul_gradient t
  obtain ⟨S, hSm, -, hDS, hμS, H', hH'm, hHS, hS⟩ :=
    exists_measurableSet_restrict_eq_self ρ hf hbot hH hμ hμD
  set φ : E → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((1 - t) • ContinuousLinearMap.id ℝ E + t • H' x).det * g (T x)
  have hφ : Measurable φ := (measurable_ofReal_det_one_sub_smul_id_add_smul hH'm t).mul
    ((measurable_rnDeriv (μ.map T) ρ).comp hT)
  -- `μ` has density `φ` on `S`, by the change of variables along the injective map `T`.
  have hμφ : μ = ρ.withDensity (S.indicator φ) := by
    have := restrict_eq_withDensity_indicator_rnDeriv_map_restrict ρ hT hSm
      (injOn_smul_add_smul_gradient hS ht₀ ht₁)
      (fun s hs hsS => measurableSet_image_smul_add_smul_gradient hs (fun x hx => hS x (hsS hx))
        ht₀ ht₁) (withDensity_image_smul_add_smul_gradient_eq_setLIntegral_of_subset ρ hS ht₀ ht₁)
      (hμS ▸ map_smul_add_smul_gradient_absolutelyContinuous ρ hf hbot hμ hμD ht₀ ht₁)
    rwa [hμS] at this
  calc μ.rnDeriv ρ =ᵐ[ρ] S.indicator φ := by
        rw [hμφ]
        exact rnDeriv_withDensity ρ (hφ.indicator hSm)
    _ = S.indicator fun x =>
          ENNReal.ofReal ((1 - t) • ContinuousLinearMap.id ℝ E + t • H x).det * g (T x) :=
        indicator_congr fun x hx => by rw [hHS x hx]
    _ =ᵐ[ρ] _ := indicator_ae_eq_of_ae_eq_set hDS.symm

/-- **Integrals of the density of an interpolant, as integrals over the source.** Under the
hypotheses of `rnDeriv_ae_eq_indicator_ofReal_det_mul_rnDeriv_map_smul_add_smul_gradient`, let
`μₜ = (Tₜ)₊ μ` with `Tₜ x = (1 - t) • x + t • ∇F x` and `0 ≤ t < 1`, and write
`Jₜ x = (1 - t) • 1 + t • H x`. For every `Φ : ℝ≥0∞ → ℝ≥0∞` with `Φ 0 = 0`,
`∫ Φ (dμₜ/dρ) dρ = ∫_D det (Jₜ x) * Φ (dμ/dρ (x) / det (Jₜ x)) dρ`, where `D` is the interior of
the effective domain of `f`. For an internal energy `∫ U (dμₜ/dρ) dρ` with `U 0 = 0`, applied to the
positive and negative parts of `U`, this moves the time dependence from the density into the
Jacobian `det (Jₜ x)`. -/
theorem lintegral_comp_rnDeriv_map_smul_add_smul_gradient
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂ρ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {μ : Measure E} [SFinite μ] (hμ : μ ≪ ρ) (hμD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤})
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) {Φ : ℝ≥0∞ → ℝ≥0∞} (hΦ : Φ 0 = 0) :
    ∫⁻ y, Φ ((μ.map fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x).rnDeriv ρ y) ∂ρ =
      ∫⁻ x in interior {x | f x ≠ ⊤},
        ENNReal.ofReal ((1 - t) • ContinuousLinearMap.id ℝ E + t • H x).det *
          Φ (μ.rnDeriv ρ x /
            ENNReal.ofReal ((1 - t) • ContinuousLinearMap.id ℝ E + t • H x).det) ∂ρ := by
  set T := fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x
  have hT : Measurable T := measurable_smul_add_smul_gradient t
  obtain ⟨S, hSm, -, hDS, hμS, H', hH'm, hHS, hS⟩ :=
    exists_measurableSet_restrict_eq_self ρ hf hbot hH hμ hμD
  -- Change variables along the injective map `T` on `S`, which carries `μ` and is `D` up to a
  -- null set.
  have h := lintegral_comp_rnDeriv_map_restrict ρ hT hSm (injOn_smul_add_smul_gradient hS ht₀ ht₁)
    (fun s hs hsS => measurableSet_image_smul_add_smul_gradient hs (fun x hx => hS x (hsS hx))
      ht₀ ht₁) (measurable_ofReal_det_one_sub_smul_id_add_smul hH'm t)
    (fun x hx => ⟨(ENNReal.ofReal_pos.2
      ((hS x hx).2.1.det_one_sub_smul_id_add_smul_pos ht₀ ht₁)).ne', ENNReal.ofReal_ne_top⟩)
    (withDensity_image_smul_add_smul_gradient_eq_setLIntegral_of_subset ρ hS ht₀ ht₁)
    (hμS ▸ map_smul_add_smul_gradient_absolutelyContinuous ρ hf hbot hμ hμD ht₀ ht₁) hΦ
  rw [hμS] at h
  rw [h, setLIntegral_congr hDS]
  exact setLIntegral_congr_fun hSm fun x hx => by rw [hHS x hx]

/-! ### The endpoint `t = 1` -/

/-- The gradient `∇F` pushes any measure restricted to a measurable set `Z`, at each point of which
the subdifferential of `f` is the single gradient with a first-order expansion of zero
determinant, to a measure singular with respect to `ρ`: it maps `Z` to a `ρ`-null set. -/
private theorem map_restrict_gradient_mutuallySingular
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) {H : E → E →L[ℝ] E} {Z : Set E}
    (hZm : MeasurableSet Z)
    (hZ : ∀ x ∈ Z, subdifferential (innerₗ E) f x = {(∇ fun x' => (f x').toReal) x} ∧
      (H x).IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
        ‖y' - (∇ fun x' => (f x').toReal) x - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    (hdet : ∀ x ∈ Z, (H x).det = 0) (μ : Measure E) :
    (μ.restrict Z).map (∇ fun x' => (f x').toReal) ⟂ₘ ρ := by
  set G := ∇ fun x' => (f x').toReal
  have hG : Measurable G := measurable_gradient _
  have hρ : ρ (G '' Z) = 0 := by
    have hZ0 : Z ∩ {x | (H x).det ≠ 0} = ∅ :=
      eq_empty_iff_forall_notMem.2 fun x hx => hx.2 (hdet x hx.1)
    have := withDensity_image_gradient_eq_setLIntegral ρ hf hZm (by rw [hZ0]; exact .empty) hZ 1
    rw [withDensity_one] at this
    rw [this]
    exact (setLIntegral_congr_fun hZm fun x hx => by simp [hdet x hx]).trans lintegral_zero
  have hN := (measurableSet_toMeasurable ρ (G '' Z)).compl
  refine ⟨(toMeasurable ρ (G '' Z))ᶜ, hN, ?_, by rw [compl_compl, measure_toMeasurable, hρ]⟩
  rw [map_apply hG hN, restrict_apply (hG hN)]
  exact measure_mono_null (fun x hx =>
    (hx.1 (subset_toMeasurable _ _ (mem_image_of_mem G hx.2))).elim) measure_empty

/-- The decomposition behind the endpoint `t = 1`. If `μ ≪ ρ` is s-finite and carried by the
interior `D` of the effective domain, there is a measurable `Z ⊆ D` on which `det (H x) > 0` and
`∇F` is injective with measurable images of measurable sets, on which `H` agrees with a measurable
`H'` giving the change of variables along `∇F` with Jacobian `det (H' x)`, and such that
`det (H x) = 0` at almost every point of `D \ Z`. The gradient pushes `μ` restricted to `Z` to a
measure absolutely continuous with respect to `ρ`, and `μ` restricted to `Zᶜ`, which is `μ`
restricted to `{x | det (H x) = 0}`, to a measure singular with respect to `ρ`. -/
private theorem exists_map_gradient_restrict_decomposition
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂ρ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {μ : Measure E} (hμ : μ ≪ ρ) (hμD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤}) :
    ∃ Z, MeasurableSet Z ∧ Z ⊆ interior {x | f x ≠ ⊤} ∧
      (∀ s, MeasurableSet s → s ⊆ Z → MeasurableSet ((∇ fun x' => (f x').toReal) '' s)) ∧
      (∀ x ∈ Z, 0 < (H x).det) ∧ InjOn (∇ fun x' => (f x').toReal) Z ∧
      (∃ H' : E → E →L[ℝ] E, Measurable H' ∧ (∀ x ∈ Z, H x = H' x) ∧
        ∀ s, MeasurableSet s → s ⊆ Z → ∀ g : E → ℝ≥0∞,
          ρ.withDensity g ((∇ fun x' => (f x').toReal) '' s) =
            ∫⁻ x in s, ENNReal.ofReal (H' x).det * g ((∇ fun x' => (f x').toReal) x) ∂ρ) ∧
      (∀ᵐ x ∂ρ, x ∈ interior {x | f x ≠ ⊤} → x ∉ Z → (H x).det = 0) ∧
      Zᶜ =ᵐ[μ] {x | (H x).det = 0} ∧
      (μ.restrict Z).map (∇ fun x' => (f x').toReal) ≪ ρ ∧
      (μ.restrict Zᶜ).map (∇ fun x' => (f x').toReal) ⟂ₘ ρ := by
  obtain ⟨S, hSm, hSD, hDS, hμS, H', hH'm, hHS, hS⟩ :=
    exists_measurableSet_restrict_eq_self ρ hf hbot hH hμ hμD
  set Z := S ∩ {x | (H' x).det ≠ 0}
  have hZm : MeasurableSet Z :=
    hSm.inter ((measurableSet_singleton 0).compl.preimage
      (ContinuousLinearMap.continuous_det.measurable.comp hH'm))
  have hpos (x : E) (hx : x ∈ Z) : 0 < (H' x).det :=
    lt_of_le_of_ne ((ContinuousLinearMap.isPositive_toLinearMap_iff _).2 (hS x hx.1).2.1).det_nonneg
      (Ne.symm hx.2)
  have hinj : InjOn (∇ fun x' => (f x').toReal) Z := by
    have := injOn_gradient_inter_setOf_det_ne_zero hf (H := H') (t := Z)
      fun x hx => ⟨(hS x hx.1).1, (hS x hx.1).2.2⟩
    rwa [inter_eq_left.2 fun x (hx : x ∈ Z) => hx.2] at this
  have hcov (s : Set E) (hs : MeasurableSet s) (hsZ : s ⊆ Z) :=
    withDensity_image_gradient_eq_setLIntegral ρ hf hs
      (by rwa [inter_eq_left.2 fun x (hx : x ∈ s) => (hsZ hx).2]) fun x hx => hS x (hsZ hx).1
  -- On `S`, the complement of `Z` is the degenerate set.
  have hSZ (x : E) (hx : x ∈ S) : x ∉ Z ↔ (H x).det = 0 := by
    simp [Z, hx, hHS x hx]
  have hμS' : ∀ᵐ x ∂μ, x ∈ S := hμS ▸ ae_restrict_mem hSm
  have hZc' : Zᶜ =ᵐ[μ] S \ Z :=
    eventuallyEqSet_iff.2 (hμS'.mono fun x hx => by simp [hx])
  refine ⟨Z, hZm, inter_subset_left.trans hSD, fun s hs hsZ => ?_,
    fun x hx => hHS x hx.1 ▸ hpos x hx, hinj, ⟨H', hH'm, fun x hx => hHS x hx.1, hcov⟩, ?_,
    eventuallyEqSet_iff.2 (hμS'.mono fun x hx => hSZ x hx), ?_, ?_⟩
  · exact measurable_image_of_fderivWithin hs (fun x hx =>
      hasFDerivWithinAt_gradient_toReal_of_forall_mem_subdifferential_norm_sub_le
        (fun x' hx' => by rw [(hS x' (hsZ hx').1).1]; exact mem_singleton _)
        (hS x (hsZ hx).1).2.2) (hinj.mono hsZ)
  · filter_upwards [hDS.mem_iff] with x hx hxD hxZ
    exact (hSZ x (hx.1 hxD)).1 hxZ
  · exact map_restrict_absolutelyContinuous_of_withDensity_image_eq ρ (measurable_gradient _) hZm
      (ENNReal.measurable_ofReal.comp (ContinuousLinearMap.continuous_det.measurable.comp hH'm))
      (fun x hx => (ENNReal.ofReal_pos.2 (hpos x hx)).ne') hcov hμ
  · rw [restrict_congr_set hZc']
    exact map_restrict_gradient_mutuallySingular ρ hf (H := H') (hSm.diff hZm)
      (fun x hx => hS x hx.1) (fun x hx => not_not.1 fun h => hx.2 ⟨hx.1, h⟩) μ

/-- **The singular part of the pushforward by the gradient.** Let `f : E → EReal` be convex (convex
real epigraph, never `⊥`), with real representative `F` and `D` the interior of its effective
domain, and let `H x` be, for almost every `x ∈ D`, a first-order expansion of the subdifferential
of `f` at `x` (the Alexandrov Hessian, see `rnDeriv_mongeAmpereMeasure_withDensity_ae_eq`). Let `μ`
be an s-finite measure, absolutely continuous with respect to an additive Haar measure `ρ` and
carried by `D`. Then the singular part of the endpoint `μ₁ = (∇F)₊ μ` of the interpolation with
respect to `ρ` has total mass `μ {x | det (H x) = 0}`: the gradient collapses the degenerate set,
and only it, to a null set. -/
theorem singularPart_map_gradient_apply_univ (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂ρ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {μ : Measure E} [SFinite μ] (hμ : μ ≪ ρ) (hμD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤}) :
    (μ.map (∇ fun x' => (f x').toReal)).singularPart ρ univ = μ {x | (H x).det = 0} := by
  set G := ∇ fun x' => (f x').toReal
  have hG : Measurable G := measurable_gradient _
  obtain ⟨Z, hZm, -, -, -, -, -, -, hZc, hac, hsing⟩ :=
    exists_map_gradient_restrict_decomposition ρ hf hbot hH hμ hμD
  have hadd : μ.map G = (μ.restrict Zᶜ).map G +
      ρ.withDensity (((μ.restrict Z).map G).rnDeriv ρ) := by
    rw [withDensity_rnDeriv_eq _ _ hac, ← Measure.map_add _ _ hG, add_comm,
      restrict_add_restrict_compl hZm]
  rw [← eq_singularPart (measurable_rnDeriv _ _) hsing hadd, map_apply hG MeasurableSet.univ,
    preimage_univ, restrict_apply_univ]
  exact measure_congr hZc

/-- **Integrals of the density of the pushforward by the gradient, as integrals over the source.**
Under the hypotheses of `singularPart_map_gradient_apply_univ`, for every `Φ : ℝ≥0∞ → ℝ≥0∞` with
`Φ 0 = 0`, the absolutely continuous part of the endpoint `μ₁ = (∇F)₊ μ` satisfies
`∫ Φ (dμ₁/dρ) dρ = ∫_D det (H x) * Φ (dμ/dρ (x) / det (H x)) dρ`. This is the formula of
`lintegral_comp_rnDeriv_map_smul_add_smul_gradient` at `t = 1`, where the Jacobian `det (H x)` may
vanish: the degenerate set contributes nothing to the right side, and its image carries the singular
part of `μ₁`. -/
theorem lintegral_comp_rnDeriv_map_gradient (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂ρ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {μ : Measure E} [SFinite μ] (hμ : μ ≪ ρ) (hμD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤})
    {Φ : ℝ≥0∞ → ℝ≥0∞} (hΦ : Φ 0 = 0) :
    ∫⁻ y, Φ ((μ.map (∇ fun x' => (f x').toReal)).rnDeriv ρ y) ∂ρ =
      ∫⁻ x in interior {x | f x ≠ ⊤},
        ENNReal.ofReal (H x).det * Φ (μ.rnDeriv ρ x / ENNReal.ofReal (H x).det) ∂ρ := by
  set G := ∇ fun x' => (f x').toReal
  set D := interior {x | f x ≠ ⊤}
  have hG : Measurable G := measurable_gradient _
  obtain ⟨Z, hZm, hZD, himage, hpos, hinj, ⟨H', hH'm, hHZ, hcov⟩, hdeg, -, hac, hsing⟩ :=
    exists_map_gradient_restrict_decomposition ρ hf hbot hH hμ hμD
  set ν := (μ.restrict Z).map G
  -- The absolutely continuous part of `μ₁` is `ν`, so its density is that of `ν`.
  have hg : ν.rnDeriv ρ =ᵐ[ρ] (μ.map G).rnDeriv ρ := by
    refine eq_rnDeriv (measurable_rnDeriv _ _) hsing ?_
    rw [withDensity_rnDeriv_eq _ _ hac, ← Measure.map_add _ _ hG, add_comm,
      restrict_add_restrict_compl hZm]
  calc ∫⁻ y, Φ ((μ.map G).rnDeriv ρ y) ∂ρ = ∫⁻ y, Φ (ν.rnDeriv ρ y) ∂ρ :=
        lintegral_congr_ae (hg.mono fun y hy => congrArg Φ hy.symm)
    _ = ∫⁻ x in Z, ENNReal.ofReal (H' x).det * Φ (μ.rnDeriv ρ x / ENNReal.ofReal (H' x).det) ∂ρ :=
        lintegral_comp_rnDeriv_map_restrict ρ hG hZm hinj himage
          (J := fun x => ENNReal.ofReal (H' x).det)
          (ENNReal.measurable_ofReal.comp (ContinuousLinearMap.continuous_det.measurable.comp hH'm))
          (fun x hx => ⟨(ENNReal.ofReal_pos.2 (hHZ x hx ▸ hpos x hx)).ne', ENNReal.ofReal_ne_top⟩)
          hcov hac hΦ
    _ = ∫⁻ x in Z, ENNReal.ofReal (H x).det * Φ (μ.rnDeriv ρ x / ENNReal.ofReal (H x).det) ∂ρ :=
        setLIntegral_congr_fun hZm fun x hx => by rw [hHZ x hx]
    _ = ∫⁻ x in D, ENNReal.ofReal (H x).det * Φ (μ.rnDeriv ρ x / ENNReal.ofReal (H x).det) ∂ρ := by
        -- Off `Z`, the Jacobian vanishes almost everywhere in `D`.
        rw [← inter_eq_left.2 hZD, ← setLIntegral_indicator hZm]
        refine setLIntegral_congr_fun_ae measurableSet_interior (hdeg.mono fun x hx hxD => ?_)
        by_cases hxZ : x ∈ Z
        · rw [indicator_of_mem hxZ]
        · rw [indicator_of_notMem hxZ, hx hxD hxZ, ENNReal.ofReal_zero, zero_mul]

end TauCeti

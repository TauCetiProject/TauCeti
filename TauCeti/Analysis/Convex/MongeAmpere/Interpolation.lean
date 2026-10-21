/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.MongeAmpere.Decomposition
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

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
`exists_measurableSet_ae_eq_interior_subdifferential_eq_gradient`. -/
private theorem exists_measurableSet_measure_compl_eq_zero
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂ρ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {μ : Measure E} (hμ : μ ≪ ρ) (hμD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤}) :
    ∃ S, MeasurableSet S ∧ S ⊆ interior {x | f x ≠ ⊤} ∧ interior {x | f x ≠ ⊤} =ᵐ[ρ] S ∧
      μ Sᶜ = 0 ∧
      (∀ x ∈ S, subdifferential (innerₗ E) f x = {(∇ fun x' => (f x').toReal) x} ∧
        (H x).IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
          ‖y' - (∇ fun x' => (f x').toReal) x - H x (x' - x)‖ ≤ ε * ‖x' - x‖) ∧
      ∃ H' : E → E →L[ℝ] E, Measurable H' ∧ ∀ x ∈ S, H x = H' x := by
  obtain ⟨S, hSm, hSD, hDS, hS, hH'⟩ :=
    exists_measurableSet_ae_eq_interior_subdifferential_eq_gradient ρ hf hbot hH
  exact ⟨S, hSm, hSD, hDS,
    (measure_congr (EventuallyEqSet.compl (hμ.ae_eq hDS))).symm.trans (mem_ae_iff.1 hμD), hS, hH'⟩

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

/-- If `μ` is carried by a measurable set `S` of points at which the subdifferential of `f` is the
single gradient with a first-order expansion, then for `0 ≤ t < 1` the interpolant `(Tₜ)₊ μ` gives
the image `Tₜ '' (s ∩ S)` the mass `μ (s ∩ S)`, because `Tₜ` is injective on `S`. -/
private theorem measure_inter_eq_map_image {H : E → E →L[ℝ] E} {S : Set E} (hSm : MeasurableSet S)
    (hS : ∀ x ∈ S, subdifferential (innerₗ E) f x = {(∇ fun x' => (f x').toReal) x} ∧
      (H x).IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
        ‖y' - (∇ fun x' => (f x').toReal) x - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {μ : Measure E} (hμS : μ Sᶜ = 0) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) {s : Set E}
    (hs : MeasurableSet s) :
    μ (s ∩ S) = μ.map (fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x)
      ((fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x) '' (s ∩ S)) := by
  set T := fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x
  have hT : Measurable T := measurable_smul_add_smul_gradient t
  have hinj : InjOn T S := injOn_smul_add_smul_gradient hS ht₀ ht₁
  have hmeas : MeasurableSet (T '' (s ∩ S)) :=
    measurableSet_image_smul_add_smul_gradient (hs.inter hSm) (fun x hx => hS x hx.2) ht₀ ht₁
  rw [map_apply hT hmeas, ← measure_inter_conull (s := T ⁻¹' (T '' (s ∩ S))) hμS,
    hinj.preimage_image_inter inter_subset_right]

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
  set T := fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x
  have hT : Measurable T := measurable_smul_add_smul_gradient t
  obtain ⟨H, hH, -⟩ := exists_mongeAmpereMeasure_eq_singularPart_add_withDensity ρ hf hbot
  obtain ⟨S, hSm, -, -, hμS, hS, H', hH'm, hHS⟩ := exists_measurableSet_measure_compl_eq_zero ρ hf
    hbot (H := H) (by filter_upwards [hH] with x hx hxD; exact ⟨_, (hx (interior_subset hxD)).2⟩)
    hμ hμD
  refine AbsolutelyContinuous.mk fun A hA hρA => ?_
  set s := T ⁻¹' A ∩ S
  have hs : MeasurableSet s := (hT hA).inter hSm
  -- The image of `s` lies in the null set `A`, and the change of variables formula with the
  -- positive Jacobian `det ((1 - t) • 1 + t • H x)` shows that `s` itself is null.
  have hdet := measurable_ofReal_det_one_sub_smul_id_add_smul hH'm t
  have hint : ∫⁻ x in s, ENNReal.ofReal ((1 - t) • ContinuousLinearMap.id ℝ E + t • H' x).det ∂ρ
      = 0 := by
    have himage := withDensity_image_smul_add_smul_gradient_eq_setLIntegral ρ hs
      (fun x hx => hS x hx.2) ht₀ ht₁ 1
    rw [withDensity_one, measure_mono_null (image_preimage_subset T A |>.trans' (image_mono
      inter_subset_left)) hρA] at himage
    rw [himage.trans (setLIntegral_congr_fun hs fun x hx => by rw [hHS x hx.2, Pi.one_apply,
      mul_one])]
  have hρs : ρ s = 0 := by
    refine measure_eq_zero_iff_ae_notMem.2 (((setLIntegral_eq_zero_iff hs hdet).1 hint).mono
      fun x hx hxs => ?_)
    refine (ENNReal.ofReal_pos.2 ?_).ne' (hx hxs)
    exact hHS x hxs.2 ▸ (hS x hxs.2).2.1.det_one_sub_smul_id_add_smul_pos ht₀ ht₁
  rw [map_apply hT hA, ← measure_inter_conull hμS]
  exact hμ hρs

/-- For `0 ≤ t < 1`, the interpolant of an s-finite measure `μ ≪ ρ` carried by the interior of the
effective domain is the measure with density its Radon–Nikodym derivative with respect to `ρ`. -/
private theorem withDensity_rnDeriv_map_smul_add_smul_gradient
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {μ : Measure E} [SFinite μ]
    (hμ : μ ≪ ρ) (hμD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤}) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    ρ.withDensity ((μ.map fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x).rnDeriv ρ) =
      μ.map fun x => (1 - t) • x + t • (∇ fun x' => (f x').toReal) x :=
  withDensity_rnDeriv_eq _ ρ
    (map_smul_add_smul_gradient_absolutelyContinuous ρ hf hbot hμ hμD ht₀ ht₁)

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
    with hTdef
  set g := (μ.map T).rnDeriv ρ
  have hT : Measurable T := measurable_smul_add_smul_gradient t
  have hν : ρ.withDensity g = μ.map T :=
    withDensity_rnDeriv_map_smul_add_smul_gradient ρ hf hbot hμ hμD ht₀ ht₁
  obtain ⟨S, hSm, -, hDS, hμS, hS, H', hH'm, hHS⟩ :=
    exists_measurableSet_measure_compl_eq_zero ρ hf hbot hH hμ hμD
  set φ : E → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((1 - t) • ContinuousLinearMap.id ℝ E + t • H' x).det * g (T x)
  have hφ : Measurable φ := (measurable_ofReal_det_one_sub_smul_id_add_smul hH'm t).mul
    ((measurable_rnDeriv (μ.map T) ρ).comp hT)
  -- `μ` has density `φ` on `S`: on each measurable `s ∩ S`, transport `μ` to `ν` by the
  -- injective map `T` and change variables back.
  have hμφ : μ = ρ.withDensity (S.indicator φ) := by
    ext s hs
    rw [← measure_inter_conull hμS, measure_inter_eq_map_image hSm hS hμS ht₀ ht₁ hs, ← hTdef, ← hν,
      withDensity_image_smul_add_smul_gradient_eq_setLIntegral ρ (hs.inter hSm)
        (fun x hx => hS x hx.2) ht₀ ht₁, withDensity_apply _ hs,
      setLIntegral_indicator hSm, inter_comm S s]
    exact setLIntegral_congr_fun (hs.inter hSm) fun x hx => by rw [hHS x hx.2]
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
    with hTdef
  set g := (μ.map T).rnDeriv ρ
  set J : E → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((1 - t) • ContinuousLinearMap.id ℝ E + t • H x).det
  have hT : Measurable T := measurable_smul_add_smul_gradient t
  have hν : ρ.withDensity g = μ.map T :=
    withDensity_rnDeriv_map_smul_add_smul_gradient ρ hf hbot hμ hμD ht₀ ht₁
  obtain ⟨S, hSm, hSD, hDS, hμS, hS, -⟩ :=
    exists_measurableSet_measure_compl_eq_zero ρ hf hbot hH hμ hμD
  have hTS : MeasurableSet (T '' S) := measurableSet_image_smul_add_smul_gradient hSm hS ht₀ ht₁
  -- The interpolant is carried by `T '' S`, so its density vanishes almost everywhere off it.
  have hνS : μ.map T (T '' S)ᶜ = 0 := by
    rw [map_apply hT hTS.compl]
    exact measure_mono_null (t := Sᶜ) (fun x hx hxS => hx (mem_image_of_mem T hxS)) hμS
  have hg0 : ∀ᵐ y ∂ρ, y ∈ (T '' S)ᶜ → g y = 0 := by
    rw [← setLIntegral_eq_zero_iff hTS.compl (measurable_rnDeriv (μ.map T) ρ), ← withDensity_apply _
      hTS.compl, hν, hνS]
  -- On `S`, the Jacobian equation gives `g (T x) = dμ/dρ (x) / J x`.
  have hJac : ∀ᵐ x ∂ρ, x ∈ S → g (T x) = μ.rnDeriv ρ x / J x := by
    filter_upwards [rnDeriv_ae_eq_indicator_ofReal_det_mul_rnDeriv_map_smul_add_smul_gradient ρ
      hf hbot hH hμ hμD ht₀ ht₁] with x hx hxS
    have hJ : 0 < ((1 - t) • ContinuousLinearMap.id ℝ E + t • H x).det :=
      (hS x hxS).2.1.det_one_sub_smul_id_add_smul_pos ht₀ ht₁
    rw [hx, indicator_of_mem (hSD hxS), ENNReal.eq_div_iff (ENNReal.ofReal_pos.2 hJ).ne'
      ENNReal.ofReal_ne_top]
  calc ∫⁻ y, Φ (g y) ∂ρ = ∫⁻ y, (T '' S).indicator (fun y => Φ (g y)) y ∂ρ := by
        refine lintegral_congr_ae (hg0.mono fun y hy => ?_)
        by_cases hyS : y ∈ T '' S
        · rw [indicator_of_mem hyS]
        · simp [indicator_of_notMem hyS, hy hyS, hΦ]
    _ = ∫⁻ x in S, J x * Φ (g (T x)) ∂ρ := by
        rw [lintegral_indicator hTS, ← withDensity_apply' _ (T '' S),
          withDensity_image_smul_add_smul_gradient_eq_setLIntegral ρ hSm hS ht₀ ht₁]
    _ = ∫⁻ x in S, J x * Φ (μ.rnDeriv ρ x / J x) ∂ρ :=
        setLIntegral_congr_fun_ae hSm (hJac.mono fun x hx hxS => by rw [hx hxS])
    _ = _ := setLIntegral_congr hDS.symm

/-! ### The endpoint `t = 1` -/

/-- The gradient `∇F` pushes `μ ≪ ρ`, restricted to a measurable set `Z` at each point of which the
subdifferential of `f` is the single gradient with a first-order expansion of nonzero
determinant, to a measure absolutely continuous with respect to `ρ`. -/
private theorem map_restrict_gradient_absolutelyContinuous
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) {H : E → E →L[ℝ] E} (hHm : Measurable H)
    {Z : Set E} (hZm : MeasurableSet Z)
    (hZ : ∀ x ∈ Z, subdifferential (innerₗ E) f x = {(∇ fun x' => (f x').toReal) x} ∧
      (H x).IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
        ‖y' - (∇ fun x' => (f x').toReal) x - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    (hdet : ∀ x ∈ Z, (H x).det ≠ 0) {μ : Measure E} (hμ : μ ≪ ρ) :
    (μ.restrict Z).map (∇ fun x' => (f x').toReal) ≪ ρ := by
  set G := ∇ fun x' => (f x').toReal
  have hG : Measurable G := measurable_gradient _
  refine AbsolutelyContinuous.mk fun A hA hρA => ?_
  set s := G ⁻¹' A ∩ Z
  have hs : MeasurableSet s := (hG hA).inter hZm
  have hsZ : MeasurableSet (s ∩ {x | (H x).det ≠ 0}) := by
    rwa [inter_eq_left.2 fun x (hx : x ∈ s) => hdet x hx.2]
  -- The image of `s` lies in the null set `A`, so the positive Jacobian `det (H x)` integrates to
  -- `0` over `s`, which is therefore null.
  have hint : ∫⁻ x in s, ENNReal.ofReal (H x).det ∂ρ = 0 := by
    have himage := withDensity_image_gradient_eq_setLIntegral ρ hf hs hsZ (fun x hx => hZ x hx.2) 1
    rw [withDensity_one, measure_mono_null ((image_preimage_subset G A).trans' (image_mono
      inter_subset_left)) hρA] at himage
    simpa using himage.symm
  have hρs : ρ s = 0 := by
    have hdetm : Measurable fun x => ENNReal.ofReal (H x).det :=
      ENNReal.measurable_ofReal.comp (ContinuousLinearMap.continuous_det.measurable.comp hHm)
    refine measure_eq_zero_iff_ae_notMem.2 (((setLIntegral_eq_zero_iff hs hdetm).1 hint).mono
      fun x hx hxs => ?_)
    refine (ENNReal.ofReal_pos.2 (lt_of_le_of_ne ?_ (hdet x hxs.2).symm)).ne' (hx hxs)
    exact ((ContinuousLinearMap.isPositive_toLinearMap_iff _).2 (hZ x hxs.2).2.1).det_nonneg
  rw [map_apply hG hA, restrict_apply (hG hA)]
  exact hμ hρs

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
interior `D` of the effective domain, there is a measurable `Z ⊆ D` on which the subdifferential of
`f` is the single gradient with a first-order expansion of positive determinant, on which `∇F` is
injective and `H` agrees with a measurable map, and such that `det (H x) = 0` at almost every
point of `D \ Z`. The gradient pushes `μ` restricted to `Z` to a measure absolutely continuous with
respect to `ρ`, and `μ` restricted to `Zᶜ`, which is `μ` restricted to `{x | det (H x) = 0}`, to a
measure singular with respect to `ρ`. -/
private theorem exists_map_gradient_restrict_decomposition
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hbot : ∀ x, f x ≠ ⊥) {H : E → E →L[ℝ] E}
    (hH : ∀ᵐ x ∂ρ, x ∈ interior {x | f x ≠ ⊤} → ∃ y, ∀ ε > 0, ∀ᶠ x' in 𝓝 x,
      ∀ y' ∈ subdifferential (innerₗ E) f x', ‖y' - y - H x (x' - x)‖ ≤ ε * ‖x' - x‖)
    {μ : Measure E} (hμ : μ ≪ ρ) (hμD : ∀ᵐ x ∂μ, x ∈ interior {x | f x ≠ ⊤}) :
    ∃ Z, MeasurableSet Z ∧ Z ⊆ interior {x | f x ≠ ⊤} ∧
      (∀ x ∈ Z, subdifferential (innerₗ E) f x = {(∇ fun x' => (f x').toReal) x} ∧
        (H x).IsPositive ∧ ∀ ε > 0, ∀ᶠ x' in 𝓝 x, ∀ y' ∈ subdifferential (innerₗ E) f x',
          ‖y' - (∇ fun x' => (f x').toReal) x - H x (x' - x)‖ ≤ ε * ‖x' - x‖) ∧
      (∀ x ∈ Z, 0 < (H x).det) ∧ InjOn (∇ fun x' => (f x').toReal) Z ∧
      (∃ H' : E → E →L[ℝ] E, Measurable H' ∧ ∀ x ∈ Z, H x = H' x) ∧
      (∀ᵐ x ∂ρ, x ∈ interior {x | f x ≠ ⊤} → x ∉ Z → (H x).det = 0) ∧
      Zᶜ =ᵐ[μ] {x | (H x).det = 0} ∧
      (μ.restrict Z).map (∇ fun x' => (f x').toReal) ≪ ρ ∧
      (μ.restrict Zᶜ).map (∇ fun x' => (f x').toReal) ⟂ₘ ρ := by
  obtain ⟨S, hSm, hSD, hDS, hμS, hS, H', hH'm, hHS⟩ :=
    exists_measurableSet_measure_compl_eq_zero ρ hf hbot hH hμ hμD
  set Z := S ∩ {x | (H' x).det ≠ 0}
  have hZm : MeasurableSet Z :=
    hSm.inter ((measurableSet_singleton 0).compl.preimage
      (ContinuousLinearMap.continuous_det.measurable.comp hH'm))
  have hdetZ (x : E) (hx : x ∈ Z) : (H x).det ≠ 0 := by rw [hHS x hx.1]; exact hx.2
  have hZ (x : E) (hx : x ∈ Z) := hS x hx.1
  -- On `S`, the complement of `Z` is the degenerate set.
  have hSZ (x : E) (hx : x ∈ S) : x ∉ Z ↔ (H x).det = 0 := by
    simp [Z, hx, hHS x hx]
  have hμS' : ∀ᵐ x ∂μ, x ∈ S := measure_eq_zero_iff_ae_notMem.1 hμS |>.mono fun x hx => not_not.1 hx
  have hZc : Zᶜ =ᵐ[μ] {x | (H x).det = 0} :=
    eventuallyEqSet_iff.2 (hμS'.mono fun x hx => hSZ x hx)
  have hZc' : Zᶜ =ᵐ[μ] S \ Z :=
    eventuallyEqSet_iff.2 (hμS'.mono fun x hx => by simp [hx])
  refine ⟨Z, hZm, inter_subset_left.trans hSD, hZ, fun x hx => lt_of_le_of_ne
      ((ContinuousLinearMap.isPositive_toLinearMap_iff _).2 (hZ x hx).2.1).det_nonneg
      (hdetZ x hx).symm, ?_, ⟨H', hH'm, fun x hx => hHS x hx.1⟩, ?_, hZc, ?_, ?_⟩
  · have := injOn_gradient_inter_setOf_det_ne_zero hf (H := H) (t := Z)
      fun x hx => ⟨(hZ x hx).1, (hZ x hx).2.2⟩
    rwa [inter_eq_left.2 fun x hx => hdetZ x hx] at this
  · filter_upwards [hDS.mem_iff] with x hx hxD hxZ
    exact (hSZ x (hx.1 hxD)).1 hxZ
  · refine map_restrict_gradient_absolutelyContinuous ρ hf hH'm hZm (fun x hx => ?_)
      (fun x hx => hx.2) hμ
    rw [← hHS x hx.1]
    exact hZ x hx
  · rw [restrict_congr_set hZc']
    exact map_restrict_gradient_mutuallySingular ρ hf (H := H) (hSm.diff hZm)
      (fun x hx => hS x hx.1) (fun x hx => (hSZ x hx.1).1 hx.2) μ

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
  obtain ⟨Z, hZm, hZD, hZ, hpos, hinj, ⟨H', hH'm, hHZ⟩, hdeg, -, hac, hsing⟩ :=
    exists_map_gradient_restrict_decomposition ρ hf hbot hH hμ hμD
  set ν := (μ.restrict Z).map G
  set g := ν.rnDeriv ρ
  have hν : ρ.withDensity g = ν := withDensity_rnDeriv_eq _ _ hac
  -- The absolutely continuous part of `μ₁` is `ν`, so its density is `g`.
  have hg : g =ᵐ[ρ] (μ.map G).rnDeriv ρ := by
    refine eq_rnDeriv (measurable_rnDeriv _ _) hsing ?_
    rw [hν, ← Measure.map_add _ _ hG, add_comm, restrict_add_restrict_compl hZm]
  have hGZ : MeasurableSet (G '' Z) :=
    measurable_image_of_fderivWithin hZm (fun x hx =>
      hasFDerivWithinAt_gradient_toReal_of_forall_mem_subdifferential_norm_sub_le
        (fun x' hx' => by rw [(hZ x' hx').1]; exact mem_singleton _) (hZ x hx).2.2) hinj
  -- `ν` is carried by `∇F '' Z`, so `g` vanishes almost everywhere off it.
  have hg0 : ∀ᵐ y ∂ρ, y ∈ (G '' Z)ᶜ → g y = 0 := by
    have hνc : ν (G '' Z)ᶜ = 0 := by
      rw [map_apply hG hGZ.compl, restrict_apply (hG hGZ.compl)]
      exact measure_mono_null (fun x hx => (hx.1 (mem_image_of_mem G hx.2)).elim) measure_empty
    rw [← setLIntegral_eq_zero_iff hGZ.compl (measurable_rnDeriv ν ρ), ← withDensity_apply _
      hGZ.compl, hν, hνc]
  -- The Jacobian equation on `Z`: `dμ/dρ (x) = det (H x) * g (∇F x)`.
  set φ : E → ℝ≥0∞ := fun x => ENNReal.ofReal (H' x).det * g (G x)
  have hφ : Measurable φ := (ENNReal.measurable_ofReal.comp
    (ContinuousLinearMap.continuous_det.measurable.comp hH'm)).mul
    ((measurable_rnDeriv ν ρ).comp hG)
  have hμZ : μ.restrict Z = ρ.withDensity (Z.indicator φ) := by
    ext s hs
    have hsZ : MeasurableSet (s ∩ Z ∩ {x | (H x).det ≠ 0}) := by
      rw [inter_eq_left.2 fun x (hx : x ∈ s ∩ Z) => (hpos x hx.2).ne']
      exact hs.inter hZm
    have hGs : MeasurableSet (G '' (s ∩ Z)) :=
      measurable_image_of_fderivWithin (hs.inter hZm) (fun x hx =>
        hasFDerivWithinAt_gradient_toReal_of_forall_mem_subdifferential_norm_sub_le
          (fun x' hx' => by rw [(hZ x' hx'.2).1]; exact mem_singleton _) (hZ x hx.2).2.2)
        (hinj.mono inter_subset_right)
    have hmap : ν (G '' (s ∩ Z)) = μ (s ∩ Z) := by
      rw [map_apply hG hGs, restrict_apply (hG hGs), hinj.preimage_image_inter inter_subset_right]
    rw [restrict_apply hs, ← hmap, ← hν, withDensity_image_gradient_eq_setLIntegral ρ hf
      (hs.inter hZm) hsZ (fun x hx => hZ x hx.2) g, withDensity_apply _ hs,
      setLIntegral_indicator hZm, inter_comm s Z]
    exact setLIntegral_congr_fun (hZm.inter hs) fun x hx => by rw [hHZ x hx.1]
  have hJac : ∀ᵐ x ∂ρ, x ∈ Z → g (G x) = μ.rnDeriv ρ x / ENNReal.ofReal (H x).det := by
    have h₁ := rnDeriv_restrict μ ρ hZm
    rw [hμZ] at h₁
    filter_upwards [h₁.symm.trans (rnDeriv_withDensity ρ (hφ.indicator hZm))] with x hx hxZ
    rw [indicator_of_mem hxZ, indicator_of_mem hxZ] at hx
    rw [ENNReal.eq_div_iff (ENNReal.ofReal_pos.2 (hpos x hxZ)).ne' ENNReal.ofReal_ne_top, hx,
      hHZ x hxZ]
  calc ∫⁻ y, Φ ((μ.map G).rnDeriv ρ y) ∂ρ = ∫⁻ y, (G '' Z).indicator (fun y => Φ (g y)) y ∂ρ := by
        refine lintegral_congr_ae ((hg.and hg0).mono fun y hy => ?_)
        dsimp only
        by_cases hyZ : y ∈ G '' Z
        · rw [indicator_of_mem hyZ, hy.1]
        · rw [indicator_of_notMem hyZ, ← hy.1, hy.2 hyZ, hΦ]
    _ = ∫⁻ x in Z, ENNReal.ofReal (H x).det * Φ (g (G x)) ∂ρ := by
        rw [lintegral_indicator hGZ, ← withDensity_apply' _ (G '' Z),
          withDensity_image_gradient_eq_setLIntegral ρ hf hZm
            (by rwa [inter_eq_left.2 fun x (hx : x ∈ Z) => (hpos x hx).ne']) hZ]
    _ = ∫⁻ x in Z, ENNReal.ofReal (H x).det * Φ (μ.rnDeriv ρ x / ENNReal.ofReal (H x).det) ∂ρ :=
        setLIntegral_congr_fun_ae hZm (hJac.mono fun x hx hxZ => by rw [hx hxZ])
    _ = ∫⁻ x in D, ENNReal.ofReal (H x).det * Φ (μ.rnDeriv ρ x / ENNReal.ofReal (H x).det) ∂ρ := by
        -- Off `Z`, the Jacobian vanishes almost everywhere in `D`.
        rw [← inter_eq_left.2 hZD, ← setLIntegral_indicator hZm]
        refine setLIntegral_congr_fun_ae measurableSet_interior (hdeg.mono fun x hx hxD => ?_)
        by_cases hxZ : x ∈ Z
        · rw [indicator_of_mem hxZ]
        · rw [indicator_of_notMem hxZ, hx hxD hxZ, ENNReal.ofReal_zero, zero_mul]

end TauCeti

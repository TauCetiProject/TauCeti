/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.HyperplaneReflection
public import TauCeti.Analysis.PDE.Regularity.SmallMeanOscillation
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The `W^{1,p}` estimate up to a flat boundary

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space in `ℝ^{n+1}`, let `ρ` be the reflection in its
boundary hyperplane, with linear part `R`, and let `u ∈ H¹(ℝ^{n+1})` vanish off `H` and solve

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in `H`,

that is `∫_H ⟨a ∇u, ∇v⟩ = ∫_H ⟨G, ∇v⟩` for every `v ∈ H¹₀(H)`. So `u` is a weak solution in the
half-space with zero boundary values on the hyperplane. This file proves the `W^{1,p}` estimate up
to the boundary,

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ(H)}`, `2 < p < ∞`,

for every such `u` whose gradient lies in `Lᵖ` and is integrable, with `C` depending only on `n`,
`p` and the ellipticity constants. It is the boundary counterpart of the whole-space estimate for
coefficients of small mean oscillation,
`TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`.

The hypothesis on the coefficients is placed on the reflected coefficient `a'`, which is `a` on
the closed half-space `{c₀ ≤ ⟪x, ν⟫}` and `R a(ρ x) R` below it (`TauCeti.PDE.reflectPrincipal`):
it has small mean oscillation at every scale
(`TauCeti.PDE.exists_eLpNorm_gradient_le_of_setAverage_reflectPrincipal_le`). Coefficients that
are close to a single constant matrix `A` invariant under the reflection, `A = R A R`, have this
property near the boundary, and the estimate holds for them when `∇u` vanishes off the set where
they are close to `A`
(`TauCeti.PDE.exists_eLpNorm_gradient_le_of_norm_sub_le_of_ae_gradient_eq_zero`). This is the
form a frozen-coefficient argument at a boundary point uses: for continuous coefficients, `a` is
close to its value at the point on a small half-ball. For symmetric `A`, invariance says that the
normal `ν` is an eigenvector of `A`, so that the conormal `A ν` is normal to the boundary.

## The argument

The odd reflection `w = u - u ∘ ρ` agrees with `u` on `H` and is a weak solution on the whole
space of the equation with the reflected coefficient `a'` and the reflected datum
`G' = 1_H G - 1_H (R G) ∘ ρ`
(`energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral_sub_setIntegral`, in
the `TauCeti.PDE` namespace).
Its gradient is `∇u - R (∇u ∘ ρ)`, again integrable and in `Lᵖ`, and `‖G'‖_{Lᵖ} ≤ 2 ‖G‖_{Lᵖ(H)}`.
The whole-space estimate applied to `w` bounds `‖∇w‖_{Lᵖ}`, which dominates `‖∇u‖_{Lᵖ}`, since
`∇u` vanishes off `H` and agrees with `∇w` on `H`.

If `a` is within `δ` of a reflection-invariant `A` wherever `∇u` does not vanish, then `u` solves
the same equation with `a` replaced by the field `b` equal to `a` there and to `A` elsewhere, and
the reflected coefficient of `b` is within `δ` of `A` everywhere
(`TauCeti.PDE.norm_matrixBilinearForm_reflectPrincipal_sub_le`), so its mean deviation from `A`
is at most `δ` on every ball.

## References

* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, Graduate Studies
  in Mathematics 96, American Mathematical Society, 2008 (`Lᵖ` estimates for divergence-form
  equations, and half-space problems with zero boundary values reduced to whole-space problems by
  odd extension).
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Lemma 9.2 (reflection across a hyperplane).
-/

public section

noncomputable section

open MeasureTheory Metric Set TopologicalSpace InnerProductSpace
open scoped Distributions ENNReal Gradient NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The whole space is invariant under every hyperplane reflection. -/
private theorem mapsTo_hyperplaneReflection_top (ν : E) (c₀ : ℝ) :
    MapsTo (hyperplaneReflection ν c₀) ((⊤ : Opens E) : Set E) ((⊤ : Opens E) : Set E) :=
  fun _ _ => trivial

/-- The reflected datum `G' = 1_H G - 1_H (R G) ∘ ρ` of a field `G ∈ Lᵖ(H)` lies in `Lᵖ`, with
`‖G'‖_{Lᵖ} ≤ 2 ‖G‖_{Lᵖ(H)}`. -/
private theorem memLp_reflectDatum {p : ℝ≥0∞} (hp : 1 ≤ p) {H : Opens E} (ν : E) (c₀ : ℝ)
    {G : E → E} (hGp : MemLp G p (volume.restrict H)) :
    MemLp (fun x => (H : Set E).indicator G x -
        (H : Set E).indicator (fun y => (ℝ ∙ ν)ᗮ.reflection (G y)) (hyperplaneReflection ν c₀ x))
        p volume ∧
      eLpNorm (fun x => (H : Set E).indicator G x -
        (H : Set E).indicator (fun y => (ℝ ∙ ν)ᗮ.reflection (G y)) (hyperplaneReflection ν c₀ x))
        p volume ≤ 2 * eLpNorm G p (volume.restrict H) := by
  set R : E ≃ₗᵢ[ℝ] E := (ℝ ∙ ν)ᗮ.reflection
  have hRGm : MemLp (fun y => R (G y)) p (volume.restrict H) :=
    R.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hGp
  have hRG : eLpNorm (fun y => R (G y)) p (volume.restrict H) =
      eLpNorm G p (volume.restrict H) :=
    eLpNorm_congr_norm_ae hRGm.aestronglyMeasurable hGp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => R.norm_map (G y))
  constructor
  · simpa only [Measure.restrict_univ] using
      memLp_indicator_sub_indicator_comp_hyperplaneReflection (μ := (volume : Measure E))
        (ν := ν) (c := c₀) H.isOpen.measurableSet MeasurableSet.univ (mapsTo_univ _ _)
        (f := G) (g := fun y => R (G y)) (by rwa [univ_inter]) (by rwa [univ_inter])
  · have h' := eLpNorm_indicator_sub_indicator_comp_hyperplaneReflection_le
      (μ := (volume : Measure E)) (ν := ν) (c := c₀) hp H.isOpen.measurableSet
      MeasurableSet.univ (mapsTo_univ _ _) (f := G) (g := fun y => R (G y))
    simp only [Measure.restrict_univ, univ_inter, hRG] at h'
    exact h'.trans_eq (two_mul _).symm

/-- The odd reflection `u - u ∘ ρ` of a weak solution `u` of `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in `H`
vanishing off `H` solves `-∂ᵢ(a'ⁱʲ ∂ⱼw) = -div G'` on the whole space, tested against test
functions, where `a'` is the reflected coefficient and `G' = 1_H G - 1_H (R G) ∘ ρ`. -/
private theorem energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_top_eq {H : Opens E}
    {ν : E} {c₀ : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {Lam : ℝ} (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hãm : AEStronglyMeasurable (reflectPrincipal ν c₀ a) volume)
    (hãbd : ∀ x, ‖matrixBilinearForm (reflectPrincipal ν c₀ a x)‖ ≤ Lam)
    {u : W1p volume (⊤ : Opens E) 2} {G : E → E} (hu0 : ∀ᵐ x, x ∉ H → W1p.value u x = 0)
    (hu : ∀ v : W1p0 volume H 2,
      energyFormH1 a 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u) (v : W1p volume H 2) =
        ∫ x in H, ⟪G x, W1p.gradient (v : W1p volume H 2) x⟫_ℝ)
    (hG2 : MemLp G 2 (volume.restrict H)) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    energyFormH1 (reflectPrincipal ν c₀ a) 0 0
        (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀
          (mapsTo_hyperplaneReflection_top ν c₀) u) (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
      ∫ x, ⟪(H : Set E).indicator G x - (H : Set E).indicator
        (fun y => (ℝ ∙ ν)ᗮ.reflection (G y)) (hyperplaneReflection ν c₀ x), ∇ (φ : E → ℝ) x⟫_ℝ := by
  -- Transport the weak formulation from `H` to `⊤ ⊓ H`, in the form the reflection lemma uses.
  have hu' : ∀ V : Opens E, V = H → ∀ hV : V ≤ ⊤, ∀ v : W1p0 volume V 2,
      energyFormH1 a 0 0 (W1p.restrictL hV u) (v : W1p volume V 2) =
        (∫ x in V, (0 : E → ℝ) x * W1p.value (v : W1p volume V 2) x) -
          ∫ x in V, ⟪(-G) x, W1p.gradient (v : W1p volume V 2) x⟫_ℝ := by
    rintro V rfl hV v
    rw [hu v]
    simp only [Pi.zero_apply, zero_mul, integral_zero, Pi.neg_apply, inner_neg_left, integral_neg,
      zero_sub, neg_neg]
  have hcoeff : MemLp (fun x => energyIntegrand (reflectPrincipal ν c₀ a x)
      (reflectDrift ν c₀ 0 x) (reflectDensity ν c₀ 0 x)) ⊤
      (volume.restrict ((⊤ : Opens E) : Set E)) := by
    rw [reflectDrift_zero, reflectDensity_zero]
    refine memLp_energyIntegrand_of_bounds (beta := 0) (gamma := 0)
      ((by positivity : (0 : ℝ) ≤ ‖matrixBilinearForm (reflectPrincipal ν c₀ a 0)‖).trans
        (hãbd 0)) hãm.restrict aestronglyMeasurable_const aestronglyMeasurable_const
      (fun x _ η ξ => ?_) (fun _ _ => by simp) (fun _ _ => by simp)
    rw [← matrixBilinearForm_apply, ← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm₂ _ _ _).trans (by gcongr; exact hãbd x)
  have h' :=
    energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral_sub_setIntegral
      (b := 0) (c := 0) (f := 0) hν hH (mapsTo_hyperplaneReflection_top ν c₀) hcoeff
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using hu0) MemLp.zero
      (by simpa only [Opens.coe_top, univ_inter] using hG2.neg)
      (hu' _ (top_inf_eq H) inf_le_left) ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩
  rw [reflectDrift_zero, reflectDensity_zero] at h'
  refine h'.trans ?_
  simp only [Opens.coe_top, Measure.restrict_univ, indicator_zero', Pi.zero_apply, sub_zero,
    zero_mul, integral_zero, zero_sub, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [W1p.gradient_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ] with x hx
  rw [hx, ← inner_neg_left]
  congr 1
  simp only [Pi.neg_apply, map_neg]
  rw [Set.indicator_neg', Set.indicator_neg, Pi.neg_apply, neg_sub_neg, neg_sub]

/-- The gradient of the odd reflection `u - u ∘ ρ` of `u ∈ H¹(ℝ^{n+1})` is integrable and in `Lᵖ`
when that of `u` is. -/
private theorem integrable_and_memLp_gradient_sub_compHyperplaneReflectionL {p : ℝ≥0∞}
    (ν : E) (c₀ : ℝ) {u : W1p volume (⊤ : Opens E) 2} (hint : Integrable (W1p.gradient u : E → E))
    (hgp : MemLp (W1p.gradient u : E → E) p volume) :
    Integrable (W1p.gradient (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀
        (mapsTo_hyperplaneReflection_top ν c₀) u) : E → E) ∧
      MemLp (W1p.gradient (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀
        (mapsTo_hyperplaneReflection_top ν c₀) u) : E → E) p volume := by
  set R : E ≃ₗᵢ[ℝ] E := (ℝ ∙ ν)ᗮ.reflection
  have hρ := measurePreserving_hyperplaneReflection (volume : Measure E) ν c₀
  have hgw : W1p.gradient (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀
      (mapsTo_hyperplaneReflection_top ν c₀) u) =ᵐ[volume]
        fun x => W1p.gradient u x - R (W1p.gradient u (hyperplaneReflection ν c₀ x)) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      W1p.gradient_sub_compHyperplaneReflectionL_ae ENNReal.ofNat_ne_top
        (mapsTo_hyperplaneReflection_top ν c₀) u
  -- Composing with `ρ` and with `R` preserves integrability and `Lᵖ` membership.
  have hR : ∀ {q : ℝ≥0∞}, MemLp (W1p.gradient u : E → E) q volume →
      MemLp (fun x => R (W1p.gradient u (hyperplaneReflection ν c₀ x))) q volume := fun hq =>
    R.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' (hq.comp_measurePreserving hρ)
  exact ⟨(hint.sub (memLp_one_iff_integrable.1 (hR (memLp_one_iff_integrable.2 hint)))).congr
    hgw.symm, (hgp.sub (hR hgp)).ae_eq hgw.symm⟩

/-- If `u ∈ H¹(ℝ^{n+1})` vanishes off `H`, then `|∇u|` is almost everywhere at most the gradient
norm of its odd reflection `u - u ∘ ρ`: the two gradients agree on `H`, and `∇u` vanishes below
the hyperplane. -/
private theorem ae_norm_gradient_le_norm_gradient_sub_compHyperplaneReflectionL {H : Opens E}
    {ν : E} {c₀ : ℝ} (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    {u : W1p volume (⊤ : Opens E) 2} (hu0 : ∀ᵐ x, x ∉ H → W1p.value u x = 0) :
    ∀ᵐ x, ‖W1p.gradient u x‖ ≤ ‖W1p.gradient (u - W1p.compHyperplaneReflectionL
      ENNReal.ofNat_ne_top ν c₀ (mapsTo_hyperplaneReflection_top ν c₀) u) x‖ := by
  have hgw := W1p.gradient_sub_compHyperplaneReflectionL_ae ENNReal.ofNat_ne_top
    (mapsTo_hyperplaneReflection_top ν c₀) u
  have hu0' : ∀ᵐ x ∂volume.restrict ((⊤ : Opens E) : Set E), x ∉ H → W1p.value u x = 0 := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hu0
  have h0 := W1p.gradient_ae_eq_zero_of_value_ae_eq_zero_of_inner_lt hH hu0'
  simp only [Opens.coe_top, Measure.restrict_univ] at hgw h0
  filter_upwards [hgw, h0,
    (measurePreserving_hyperplaneReflection (volume : Measure E) ν c₀).quasiMeasurePreserving.ae h0,
    measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_setOf_inner_eq volume hν c₀)]
    with x h1 h2 h3 h4
  rcases lt_or_gt_of_ne h4 with hlt | hgt
  · rw [h2 hlt, norm_zero]
    exact norm_nonneg _
  · rw [h1, h3 ((inner_hyperplaneReflection_lt_iff hν c₀).2 hgt), map_zero, sub_zero]

/-- **The `W^{1,p}` estimate up to a flat boundary.** Let `2 < p < ∞` and `0 < λ ≤ Λ`. There are
constants `C` and `δ > 0`, depending only on `n`, `p`, `λ` and `Λ`, with the following property.
Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, and let `a` be a coefficient matrix, measurable on `H`
and bounded by `Λ` on the closed half-space `{c₀ ≤ ⟪x, ν⟫}`, whose reflected coefficient `a'`
(`TauCeti.PDE.reflectPrincipal`) has small mean oscillation at every scale: on every ball `B` some
constant matrix `A`, uniformly elliptic with constants `λ, Λ`, has `⨍_B ‖a' - A‖ ≤ δ`. Let
`u ∈ H¹(ℝ^{n+1})` vanish off `H` and solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in `H`, that is
`∫_H ⟨a ∇u, ∇v⟩ = ∫_H ⟨G, ∇v⟩` for every `v ∈ H¹₀(H)`, with `G ∈ L²(H) ∩ Lᵖ(H)`, and let `∇u` be
integrable and in `Lᵖ`. Then

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ(H)}`. -/
theorem exists_eLpNorm_gradient_le_of_setAverage_reflectPrincipal_le {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {H : Opens E} {ν : E} {c₀ : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) →
        AEStronglyMeasurable a (volume.restrict H) →
        (∀ x, c₀ ≤ ⟪x, ν⟫_ℝ → ‖matrixBilinearForm (a x)‖ ≤ Lam) →
        (∀ (c : E) (r : ℝ), 0 < r →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r,
                ‖matrixBilinearForm (reflectPrincipal ν c₀ a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : W1p volume (⊤ : Opens E) 2) (G : E → E),
          (∀ᵐ x, x ∉ H → W1p.value u x = 0) →
          (∀ v : W1p0 volume H 2,
            energyFormH1 a 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u) (v : W1p volume H 2) =
              ∫ x in H, ⟪G x, W1p.gradient (v : W1p volume H 2) x⟫_ℝ) →
          Integrable (W1p.gradient u : E → E) → MemLp (W1p.gradient u : E → E) p volume →
          MemLp G 2 (volume.restrict H) → MemLp G p (volume.restrict H) →
          eLpNorm (W1p.gradient u : E → E) p volume ≤ C * eLpNorm G p (volume.restrict H) := by
  obtain ⟨C, δ, hδ, h⟩ :=
    exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le (n := n) hp hp_top
      lam Lam
  refine ⟨2 * C, δ, hδ, ?_⟩
  intro H ν c₀ a hν hH ham hbd hosc u G hu0 hu hint hgp hG2 hGp
  obtain ⟨hG'p, hG'le⟩ := memLp_reflectDatum (one_le_two.trans hp.le) ν c₀ hGp
  obtain ⟨hwint, hwgp⟩ := integrable_and_memLp_gradient_sub_compHyperplaneReflectionL ν c₀ hint hgp
  -- The reflected coefficient is measurable and bounded.
  have hãm : AEStronglyMeasurable (reflectPrincipal ν c₀ a) volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      aestronglyMeasurable_reflectPrincipal (mu := volume) hν hH
        (mapsTo_hyperplaneReflection_top ν c₀)
        (by simpa only [Opens.coe_inf, Opens.coe_top, univ_inter] using ham)
  have hãbd := norm_matrixBilinearForm_reflectPrincipal_le hν hbd
  -- The whole-space estimate for the odd reflection `w = u - u ∘ ρ`, whose gradient dominates.
  have hw := h hãm hãbd hosc _ _
    (energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_top_eq hν hH hãm hãbd hu0 hu hG2)
    hwint hwgp hG'p
  calc eLpNorm (W1p.gradient u : E → E) p volume
      ≤ eLpNorm (W1p.gradient (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀
          (mapsTo_hyperplaneReflection_top ν c₀) u) : E → E) p volume :=
        eLpNorm_mono_ae hgp.aestronglyMeasurable
          (ae_norm_gradient_le_norm_gradient_sub_compHyperplaneReflectionL hν hH hu0)
    _ ≤ C * (2 * eLpNorm G p (volume.restrict H)) := hw.trans (by gcongr)
    _ = ((2 * C : ℝ≥0) : ℝ≥0∞) * eLpNorm G p (volume.restrict H) := by
      push_cast
      ring

/-- **The `W^{1,p}` estimate up to a flat boundary, near a reflection-invariant matrix.** Let
`2 < p < ∞` and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ`
and `Λ`, with the following property. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `R` be the
linear part of the reflection in its boundary hyperplane, and let `A` be a constant matrix,
uniformly elliptic with constants `λ, Λ` and invariant under the reflection, `A = R A R`. Let `a`
be a coefficient matrix measurable on `H` whose bilinear form is within `δ` of that of `A`, in
operator norm, on `s ∩ H` for a measurable set `s`. Let `u ∈ H¹(ℝ^{n+1})` vanish off `H`, let `∇u`
vanish off `s`, and let `u` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in `H`, that is
`∫_H ⟨a ∇u, ∇v⟩ = ∫_H ⟨G, ∇v⟩` for every `v ∈ H¹₀(H)`, with `G ∈ L²(H) ∩ Lᵖ(H)`. If `∇u` is
integrable and in `Lᵖ`, then

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ(H)}`.

No continuity of `a` and no bound on `a` off `s` are assumed. For coefficients continuous up to
the boundary whose value `A` at a boundary point is invariant under the reflection, `s` can be a
small ball centred at that point. -/
theorem exists_eLpNorm_gradient_le_of_norm_sub_le_of_ae_gradient_eq_zero {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {H : Opens E} {ν : E} {c₀ : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {s : Set E},
        ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → MeasurableSet s →
        AEStronglyMeasurable a (volume.restrict H) →
        UniformlyEllipticOn univ (fun _ : E => A) lam Lam →
        (∀ η ξ, matrixBilinearForm A ((ℝ ∙ ν)ᗮ.reflection η) ((ℝ ∙ ν)ᗮ.reflection ξ) =
          matrixBilinearForm A η ξ) →
        (∀ x ∈ s, x ∈ H → ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : W1p volume (⊤ : Opens E) 2) (G : E → E),
          (∀ᵐ x, x ∉ H → W1p.value u x = 0) → (∀ᵐ x, x ∉ s → W1p.gradient u x = 0) →
          (∀ v : W1p0 volume H 2,
            energyFormH1 a 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u) (v : W1p volume H 2) =
              ∫ x in H, ⟪G x, W1p.gradient (v : W1p volume H 2) x⟫_ℝ) →
          Integrable (W1p.gradient u : E → E) → MemLp (W1p.gradient u : E → E) p volume →
          MemLp G 2 (volume.restrict H) → MemLp G p (volume.restrict H) →
          eLpNorm (W1p.gradient u : E → E) p volume ≤ C * eLpNorm G p (volume.restrict H) := by
  obtain ⟨C, δ, hδ, h⟩ :=
    exists_eLpNorm_gradient_le_of_setAverage_reflectPrincipal_le (n := n) hp hp_top lam (Lam + 1)
  refine ⟨C, min δ 1, lt_min hδ one_pos, ?_⟩
  intro H ν c₀ a A s hν hH hs ham hA hAinv hsA u G hu0 hus hu hint hgp hG2 hGp
  classical
  -- Replace `a` by `A` off `s ∩ H`, where `∇u` vanishes.
  set b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := (s ∩ H).piecewise a (fun _ => A) with hbdef
  have hm : 0 ≤ min δ 1 := (lt_min hδ one_pos).le
  have hb : ∀ y, ‖matrixBilinearForm (b y) - matrixBilinearForm A‖ ≤ min δ 1 := fun y => by
    by_cases hy : y ∈ s ∩ H
    · rw [hbdef, piecewise_eq_of_mem _ _ _ hy]
      exact hsA y hy.1 hy.2
    · rw [hbdef, piecewise_eq_of_notMem _ _ _ hy]
      refine ContinuousLinearMap.opNorm_le_bound₂ _ hm fun η ξ => ?_
      simp only [FunLike.coe_sub, Pi.sub_apply, sub_self, zero_apply, norm_zero]
      positivity
  have hb' := norm_matrixBilinearForm_reflectPrincipal_sub_le (c₀ := c₀) (a := b) hν hAinv
    (fun y _ => hb y)
  have hAn : ‖matrixBilinearForm A‖ ≤ Lam := hA.opNorm_matrixBilinearForm_le (mem_univ 0)
  refine h (a := b) hν hH ?_ (fun x _ => ?_) (fun c r _ => ⟨A, ?_, ?_⟩) u G hu0 (fun v => ?_)
    hint hgp hG2 hGp
  · exact ham.restrict.piecewise (hs.inter H.isOpen.measurableSet).nullMeasurableSet
      aestronglyMeasurable_const
  · -- `b x` is within `1` of `A`, whose form has norm at most `Λ`.
    exact (norm_le_insert' (matrixBilinearForm (b x)) (matrixBilinearForm A)).trans
      (add_le_add hAn ((hb x).trans (min_le_right _ _)))
  · exact (hA.mono_set (subset_univ _)).mono_constants hA.pos le_rfl (by linarith)
  · -- The reflected coefficient of `b` is within `min δ 1` of `A` everywhere.
    refine (Real.le_norm_self _).trans
      ((norm_setAverage_le_of_norm_le_const hm fun x _ => ?_).trans (min_le_left _ _))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hb' x
  · -- `u` solves the equation with `b`, which agrees with `a` where `∇u` does not vanish.
    rw [← hu v]
    refine energyFormH1_eq_of_eqOn_of_ae_gradient_eq_zero (s := s ∩ H)
      (fun y hy => by rw [hbdef, piecewise_eq_of_mem _ _ _ hy]) 0 0 ?_ _
    filter_upwards [W1p.gradient_restrictL_ae (le_top : H ≤ ⊤) u,
      ae_restrict_of_ae (μ := volume) (s := (H : Set E)) hus,
      ae_restrict_mem H.isOpen.measurableSet]
      with x h1 h2 h3 hx
    rw [h1]
    exact h2 fun hxs => hx ⟨hxs, h3⟩

end PDE

end TauCeti

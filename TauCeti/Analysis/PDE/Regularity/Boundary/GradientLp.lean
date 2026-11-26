/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.HyperplaneReflection
public import TauCeti.Analysis.PDE.Regularity.SmallMeanOscillation
import Mathlib.LinearAlgebra.Transvection.Basic
import TauCeti.Analysis.PDE.EnergyForm.Antisymmetric
import TauCeti.Analysis.PDE.EnergyForm.ChangeOfVariables
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
are close to a single constant matrix `A`, uniformly elliptic and not necessarily symmetric,
satisfy the estimate when `∇u` vanishes off the set where they are close to `A`
(`TauCeti.PDE.exists_eLpNorm_gradient_le_of_norm_sub_le_of_ae_gradient_eq_zero`). This is the
form a frozen-coefficient argument at a boundary point uses: for continuous coefficients, `a` is
close to its value at the point on a small half-ball, and that value can be any elliptic matrix.

## The argument

The odd reflection `w = u - u ∘ ρ` agrees with `u` on `H` and is a weak solution on the whole
space of the equation with the reflected coefficient `a'` and the reflected datum
`G' = 1_H G - 1_H (R G) ∘ ρ`
(`energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral_sub_setIntegral`, in
the `TauCeti.PDE` namespace).
Its gradient is `∇u - R (∇u ∘ ρ)`, again integrable and in `Lᵖ`, and `‖G'‖_{Lᵖ} ≤ 2 ‖G‖_{Lᵖ(H)}`.
The whole-space estimate applied to `w` bounds `‖∇w‖_{Lᵖ}`, which dominates `‖∇u‖_{Lᵖ}`, since
`∇u` vanishes off `H` and agrees with `∇w` on `H`.

If `a` is within `δ` of a reflection-invariant `A`, `A = R A R`, wherever `∇u` does not vanish,
then `u` solves the same equation with `a` replaced by the field `b` equal to `a` there and to `A`
elsewhere, and the reflected coefficient of `b` is within `δ` of `A` everywhere
(`TauCeti.PDE.norm_matrixBilinearForm_reflectPrincipal_sub_le`), so its mean deviation from `A`
is at most `δ` on every ball. A general elliptic `A` is reduced to this case in two steps.

* The constant antisymmetric part `K = (A - Aᵀ) / 2` does not change the energy form on
  `H¹(H) × H¹₀(H)` (`TauCeti.PDE.energyFormH1_add_const_eq_of_transpose_eq_neg`), so `a - K`
  gives the same equation and is close to the symmetric part `Aₛ` of `A`.
* With `e = ν / ‖ν‖`, `α = ⟪e, Aₛ e⟫ > 0` and `w = e - Aₛ e / α`, which is orthogonal to `ν`, the
  shear `T x = x + ⟪e, x⟫ w` maps `H` onto itself, has determinant one and sends `Aₛ e` to `α e`.
  Its inverse `Φ` transforms the equation for `u` into one for `u ∘ Φ` with the coefficient
  `T (a - K) Tᵀ` (`TauCeti.PDE.energyFormH1_compL_eq_setIntegral_add_setIntegral_inner`), close to
  `T Aₛ Tᵀ`, whose conormal at the boundary is normal: `T Aₛ Tᵀ e = α e`. So `T Aₛ Tᵀ` is invariant
  under the reflection, and the norms of `∇u` and `G` change at most by the factor `‖T‖`.

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

/-! ### Coefficients close to a reflection-invariant matrix -/

/-- The `W^{1,p}` estimate up to a flat boundary for coefficients within `δ` of a
reflection-invariant elliptic matrix everywhere. -/
private theorem exists_eLpNorm_gradient_le_of_norm_sub_le_of_reflection {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {H : Opens E} {ν : E} {c₀ : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) →
        AEStronglyMeasurable a (volume.restrict H) →
        UniformlyEllipticOn univ (fun _ : E => A) lam Lam →
        (∀ η ξ, matrixBilinearForm A ((ℝ ∙ ν)ᗮ.reflection η) ((ℝ ∙ ν)ᗮ.reflection ξ) =
          matrixBilinearForm A η ξ) →
        (∀ x, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : W1p volume (⊤ : Opens E) 2) (G : E → E),
          (∀ᵐ x, x ∉ H → W1p.value u x = 0) →
          (∀ v : W1p0 volume H 2,
            energyFormH1 a 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u) (v : W1p volume H 2) =
              ∫ x in H, ⟪G x, W1p.gradient (v : W1p volume H 2) x⟫_ℝ) →
          Integrable (W1p.gradient u : E → E) → MemLp (W1p.gradient u : E → E) p volume →
          MemLp G 2 (volume.restrict H) → MemLp G p (volume.restrict H) →
          eLpNorm (W1p.gradient u : E → E) p volume ≤ C * eLpNorm G p (volume.restrict H) := by
  obtain ⟨C, δ, hδ, h⟩ :=
    exists_eLpNorm_gradient_le_of_setAverage_reflectPrincipal_le (n := n) hp hp_top lam (Lam + 1)
  refine ⟨C, min δ 1, lt_min hδ one_pos, ?_⟩
  intro H ν c₀ a A hν hH ham hA hAinv ha u G hu0 hu hint hgp hG2 hGp
  have hm : 0 ≤ min δ 1 := (lt_min hδ one_pos).le
  have ha' := norm_matrixBilinearForm_reflectPrincipal_sub_le (c₀ := c₀) (a := a) hν hAinv
    (fun y _ => ha y)
  refine h (a := a) hν hH ham (fun x _ => ?_) (fun c r _ => ⟨A, ?_, ?_⟩) u G hu0 hu hint hgp hG2
    hGp
  · -- `a x` is within `1` of `A`, whose form has norm at most `Λ`.
    exact (norm_le_insert' (matrixBilinearForm (a x)) (matrixBilinearForm A)).trans
      (add_le_add (hA.opNorm_matrixBilinearForm_le (mem_univ 0)) ((ha x).trans (min_le_right _ _)))
  · exact (hA.mono_set (subset_univ _)).mono_constants hA.pos le_rfl (by linarith)
  · -- The reflected coefficient of `a` is within `min δ 1` of `A` everywhere.
    refine (Real.le_norm_self _).trans
      ((norm_setAverage_le_of_norm_le_const hm fun x _ => ?_).trans (min_le_left _ _))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact ha' x

/-! ### Shears along the boundary hyperplane

For `⟪e, w⟫ = 0`, the shear `x ↦ x + ⟪e, x⟫ w` has determinant one, and its inverse is the shear
by `-w`. When moreover `w ⊥ ν`, it maps the half-space `{c₀ < ⟪x, ν⟫}` onto itself. -/

/-- The shear `x ↦ x + ⟪e, x⟫ w`: the transvection of the linear form `⟪e, ·⟫` and the vector `w`,
as a continuous linear map. -/
private noncomputable def shear (e w : E) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    (LinearMap.transvection ((innerSL ℝ e : E →L[ℝ] ℝ) : E →ₗ[ℝ] ℝ) w)

private theorem shear_apply (e w x : E) : shear e w x = x + ⟪e, x⟫_ℝ • w := by
  simp [shear, LinearMap.transvection.apply]

private theorem shear_shear_neg {e w : E} (h : ⟪e, w⟫_ℝ = 0) (x : E) :
    shear e w (shear e (-w) x) = x := by
  simp only [shear_apply, inner_add_right, inner_smul_right, inner_neg_right, h]
  module

private theorem inner_shear_left {e w ν : E} (h : ⟪w, ν⟫_ℝ = 0) (x : E) :
    ⟪shear e w x, ν⟫_ℝ = ⟪x, ν⟫_ℝ := by
  simp [shear_apply, inner_add_left, inner_smul_left, h]

private theorem norm_shear_le {e : E} (he : ‖e‖ = 1) (w : E) : ‖shear e w‖ ≤ 1 + ‖w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rw [shear_apply]
  calc ‖x + ⟪e, x⟫_ℝ • w‖ ≤ ‖x‖ + |⟪e, x⟫_ℝ| * ‖w‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖x‖ + ‖x‖ * ‖w‖ := by
        gcongr
        exact (abs_real_inner_le_norm e x).trans (by rw [he, one_mul])
    _ = (1 + ‖w‖) * ‖x‖ := by ring

private theorem adjoint_shear (e w : E) : (shear e w).adjoint = shear w e := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [shear_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real]
  rw [real_inner_comm x w]
  ring

private theorem det_shear {e w : E} (h : ⟪e, w⟫_ℝ = 0) :
    (shear e w).det = 1 := by
  rw [shear, LinearMap.det_toContinuousLinearMap, LinearMap.transvection.det]
  simp [h]

private theorem neg_inner_eq_zero {e w : E} (hew : ⟪e, w⟫_ℝ = 0) : ⟪e, -w⟫_ℝ = 0 := by
  rw [inner_neg_right, hew, neg_zero]

private theorem shear_neg_shear {e w : E} (hew : ⟪e, w⟫_ℝ = 0) (x : E) :
    shear e (-w) (shear e w x) = x := by
  simpa using shear_shear_neg (neg_inner_eq_zero hew) x

private theorem shear_comp_shear_neg {e w : E} (hew : ⟪e, w⟫_ℝ = 0) :
    shear e w ∘L shear e (-w) = ContinuousLinearMap.id ℝ E :=
  ContinuousLinearMap.ext fun x => by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, shear_shear_neg hew]

private theorem shear_neg_comp_shear {e w : E} (hew : ⟪e, w⟫_ℝ = 0) :
    shear e (-w) ∘L shear e w = ContinuousLinearMap.id ℝ E :=
  ContinuousLinearMap.ext fun x => by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, shear_neg_shear hew]

private theorem measurePreserving_shear {e w : E} (hew : ⟪e, w⟫_ℝ = 0) :
    MeasurePreserving (shear e w) volume volume := by
  simpa using ContinuousAffineMap.measurePreserving_of_abs_det_eq_one volume
    (shear e w).toContinuousAffineMap (by simp [det_shear hew])

private theorem shear_mem_iff {H : Opens E} {ν e w : E} {c₀ : ℝ}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hwν : ⟪w, ν⟫_ℝ = 0) (x : E) :
    shear e w x ∈ H ↔ x ∈ H := by
  rw [hH, hH, inner_shear_left hwν]

private theorem measurePreserving_shear_restrict {H : Opens E} {ν e w : E} {c₀ : ℝ}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hew : ⟪e, w⟫_ℝ = 0) (hwν : ⟪w, ν⟫_ℝ = 0) :
    MeasurePreserving (shear e w) (volume.restrict H) (volume.restrict H) := by
  have h := (measurePreserving_shear hew).restrict_preimage H.isOpen.measurableSet
  rwa [show (shear e w) ⁻¹' (H : Set E) = H from Set.ext (shear_mem_iff hH hwν)] at h

private theorem mapsTo_shear {H : Opens E} {ν e w : E} {c₀ : ℝ}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hwν : ⟪w, ν⟫_ℝ = 0) :
    MapsTo (shear e w) (H : Set E) (H : Set E) :=
  fun x hx => (shear_mem_iff hH hwν x).2 hx

/-! ### The shear adapted to a symmetric matrix -/

/-- For a symmetric bilinear form `B` with `B e e ≠ 0` and `w = e - (B e e)⁻¹ v`, where `v`
represents `B e`, the sheared form `B (S ·) (S ·)`, `S ξ = ξ + ⟪w, ξ⟫ e`, satisfies
`B (e, S ξ) = B e e ⟪e, ξ⟫`. -/
private theorem apply_shear_eq {B : E →L[ℝ] E →L[ℝ] ℝ} {e w : E} (hα : B e e ≠ 0)
    (hw : w = e - (B e e)⁻¹ • (toDual ℝ E).symm (B e)) (ξ : E) :
    B e (shear w e ξ) = B e e * ⟪e, ξ⟫_ℝ := by
  rw [shear_apply, map_add, map_smul, hw, inner_sub_left, inner_smul_left, toDual_symm_apply,
    RCLike.conj_to_real, smul_eq_mul]
  field_simp
  ring

private theorem inner_shearVector {B : E →L[ℝ] E →L[ℝ] ℝ} {e w : E}
    (he : ‖e‖ = 1) (hα : B e e ≠ 0) (hw : w = e - (B e e)⁻¹ • (toDual ℝ E).symm (B e)) :
    ⟪e, w⟫_ℝ = 0 := by
  rw [hw, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, he, real_inner_comm,
    toDual_symm_apply]
  field_simp
  ring

/-- With `w` as in `apply_shear_eq`, the sheared form `B (S ·) (S ·)` of a symmetric form is
invariant under the reflection `x ↦ x - 2 ⟪e, x⟫ e` in the hyperplane `e^⊥`. -/
private theorem apply_shear_reflection {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : ∀ η ξ, B η ξ = B ξ η)
    {e w : E} (he : ‖e‖ = 1) (hα : B e e ≠ 0)
    (hw : w = e - (B e e)⁻¹ • (toDual ℝ E).symm (B e)) (η ξ : E) :
    B (shear w e (η - (2 * ⟪e, η⟫_ℝ) • e)) (shear w e (ξ - (2 * ⟪e, ξ⟫_ℝ) • e)) =
      B (shear w e η) (shear w e ξ) := by
  have hwe : ⟪w, e⟫_ℝ = 0 := by rw [real_inner_comm]; exact inner_shearVector he hα hw
  have hS (x : E) : shear w e (x - (2 * ⟪e, x⟫_ℝ) • e) = shear w e x - (2 * ⟪e, x⟫_ℝ) • e := by
    simp only [shear_apply, inner_sub_right, inner_smul_right, hwe]
    module
  rw [hS, hS]
  simp only [map_sub, map_smul, FunLike.coe_sub, Pi.sub_apply,
    FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [hB (shear w e η) e, apply_shear_eq hα hw, apply_shear_eq hα hw]
  ring

/-- **The shear adapted to a symmetric elliptic matrix.** For a symmetric matrix `A`, uniformly
elliptic with constants `λ, Λ`, and the unit normal `e = ‖ν‖⁻¹ ν`, there is `w ⊥ ν` with
`‖w‖ ≤ 1 + Λ / λ` such that the form `(η, ξ) ↦ ηᵀ A ξ`, read through `S ξ = ξ + ⟪w, ξ⟫ e`, is
invariant under the reflection in `ν^⊥`. -/
private theorem exists_shear_of_isSymm {ν : E} (hν : ν ≠ 0)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (hA : UniformlyEllipticOn univ (fun _ : E => A) lam Lam) (hAs : A.IsSymm) :
    ∃ w : E, ⟪‖ν‖⁻¹ • ν, w⟫_ℝ = 0 ∧ ⟪w, ν⟫_ℝ = 0 ∧ ‖w‖ ≤ 1 + Lam / lam ∧
      ∀ η ξ, matrixBilinearForm A (shear w (‖ν‖⁻¹ • ν) ((ℝ ∙ ν)ᗮ.reflection η))
          (shear w (‖ν‖⁻¹ • ν) ((ℝ ∙ ν)ᗮ.reflection ξ)) =
        matrixBilinearForm A (shear w (‖ν‖⁻¹ • ν) η) (shear w (‖ν‖⁻¹ • ν) ξ) := by
  set e : E := ‖ν‖⁻¹ • ν with hedef
  set B := matrixBilinearForm A
  have he : ‖e‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hν)]
  have hB (η ξ : E) : B η ξ = B ξ η := by
    rw [← matrixBilinearForm_transpose_apply, hAs.eq]
  have hlam : lam ≤ B e e := by
    simpa [B, he, Matrix.toQuadraticForm'_apply] using hA.lower_bound (mem_univ 0) e
  have hα : B e e ≠ 0 := (hA.pos.trans_le hlam).ne'
  set w := e - (B e e)⁻¹ • (toDual ℝ E).symm (B e) with hw
  have hew : ⟪e, w⟫_ℝ = 0 := inner_shearVector he hα hw
  refine ⟨w, hew, ?_, ?_, fun η ξ => ?_⟩
  · have hν' : ν = ‖ν‖ • e := by rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hν), one_smul]
    rw [hν', inner_smul_right, real_inner_comm, hew, mul_zero]
  · have hBe : ‖B e‖ ≤ Lam :=
      (B.le_opNorm e).trans
        (by rw [he, mul_one]; exact hA.opNorm_matrixBilinearForm_le (mem_univ 0))
    calc ‖w‖ ≤ ‖e‖ + ‖(B e e)⁻¹ • (toDual ℝ E).symm (B e)‖ := norm_sub_le _ _
      _ = 1 + (B e e)⁻¹ * ‖B e‖ := by
        rw [he, norm_smul, LinearIsometryEquiv.norm_map, Real.norm_of_nonneg
          (inv_nonneg.2 (hA.pos.le.trans hlam))]
      _ ≤ 1 + Lam / lam := by
        rw [div_eq_inv_mul]
        have := hA.pos
        gcongr
  · -- The reflection in `ν^⊥` is `x ↦ x - 2 ⟪e, x⟫ e`.
    have hR (x : E) : (ℝ ∙ ν)ᗮ.reflection x = x - (2 * ⟪e, x⟫_ℝ) • e := by
      rw [reflection_orthogonal_singleton_apply_div_norm_sq, hedef,
        inner_smul_left, RCLike.conj_to_real, smul_smul]
      module
    rw [hR, hR]
    exact apply_shear_reflection hB he hα hw η ξ

/-! ### Transporting the problem along the shear -/

/-- Precomposition with the shear `x ↦ x - ⟪e, x⟫ w`, for `⟪e, w⟫ = 0`, as an operator on
`H¹(ℝ^{n+1})`. -/
private noncomputable def shearCompL (e w : E) (hew : ⟪e, w⟫_ℝ = 0) :
    W1p volume (⊤ : Opens E) 2 →L[ℝ] W1p volume (⊤ : Opens E) 2 :=
  W1p.compL (shear e (-w)) ENNReal.ofNat_ne_top (shear e (-w)).differentiableOn
    (Function.LeftInverse.injective (g := shear e w) (shear_shear_neg hew)).injOn
    (fun _ _ => trivial) (fun x _ => by rw [ContinuousLinearMap.fderiv]) one_pos
    (fun x _ => by rw [ContinuousLinearMap.fderiv, det_shear (neg_inner_eq_zero hew), abs_one])

private theorem value_shearCompL_ae {e w : E} (hew : ⟪e, w⟫_ℝ = 0)
    (u : W1p volume (⊤ : Opens E) 2) :
    W1p.value (shearCompL e w hew u) =ᵐ[volume] fun x => W1p.value u (shear e (-w) x) := by
  have h := W1p.value_compL_ae (U := ⊤) (V := ⊤) (shear e (-w)) ENNReal.ofNat_ne_top
    (shear e (-w)).differentiableOn
    (Function.LeftInverse.injective (g := shear e w) (shear_shear_neg hew)).injOn
    (fun _ _ => trivial) (fun x _ => by rw [ContinuousLinearMap.fderiv]) one_pos
    (fun x _ => by rw [ContinuousLinearMap.fderiv, det_shear (neg_inner_eq_zero hew), abs_one]) u
  simp only [Opens.coe_top, Measure.restrict_univ] at h
  exact h

private theorem gradient_shearCompL_ae {e w : E} (hew : ⟪e, w⟫_ℝ = 0)
    (u : W1p volume (⊤ : Opens E) 2) :
    W1p.gradient (shearCompL e w hew u) =ᵐ[volume]
      fun x => (shear e (-w)).adjoint (W1p.gradient u (shear e (-w) x)) := by
  have h := W1p.gradient_compL_ae (U := ⊤) (V := ⊤) (shear e (-w)) ENNReal.ofNat_ne_top
    (shear e (-w)).differentiableOn
    (Function.LeftInverse.injective (g := shear e w) (shear_shear_neg hew)).injOn
    (fun _ _ => trivial) (fun x _ => by rw [ContinuousLinearMap.fderiv]) one_pos
    (fun x _ => by rw [ContinuousLinearMap.fderiv, det_shear (neg_inner_eq_zero hew), abs_one]) u
  simp only [Opens.coe_top, Measure.restrict_univ, ContinuousLinearMap.fderiv] at h
  exact h

/-- On `H`, the restriction of `u ∘ Φ` is the change of variables `Φ` applied to the restriction
of `u`, where `Φ x = x - ⟪e, x⟫ w` maps `H` onto itself. -/
private theorem restrictL_shearCompL {H : Opens E} {ν e w : E} {c₀ : ℝ}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hew : ⟪e, w⟫_ℝ = 0) (hwν : ⟪w, ν⟫_ℝ = 0)
    (u : W1p volume (⊤ : Opens E) 2) :
    W1p.restrictL (le_top : H ≤ ⊤) (shearCompL e w hew u) =
      W1p.compL (U := H) (V := H) (shear e (-w)) ENNReal.ofNat_ne_top
        (shear e (-w)).differentiableOn
        (Function.LeftInverse.injective (g := shear e w) (shear_shear_neg hew)).injOn
        (mapsTo_shear hH (by rw [inner_neg_left, hwν, neg_zero]))
        (fun x _ => by rw [ContinuousLinearMap.fderiv]) one_pos
        (fun x _ => by rw [ContinuousLinearMap.fderiv, det_shear (neg_inner_eq_zero hew), abs_one])
        (W1p.restrictL (le_top : H ≤ ⊤) u) := by
  have hmp := measurePreserving_shear_restrict hH (neg_inner_eq_zero hew)
    (by rw [inner_neg_left, hwν, neg_zero])
  refine W1p.ext_value (Lp.ext ?_)
  filter_upwards [W1p.value_restrictL_ae (le_top : H ≤ ⊤) (shearCompL e w hew u),
    ae_restrict_of_ae (s := (H : Set E)) (value_shearCompL_ae hew u),
    W1p.value_compL_ae _ _ _ _ _ _ _ _ (W1p.restrictL (le_top : H ≤ ⊤) u),
    hmp.quasiMeasurePreserving.ae_eq_comp (W1p.value_restrictL_ae (le_top : H ≤ ⊤) u)]
    with x h1 h2 h3 h4
  rw [h1, h2]
  exact (h3.trans h4).symm

/-- **The weak equation along the shear.** If `u` solves `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in `H`,
then `u ∘ Φ`, `Φ x = x - ⟪e, x⟫ w`, solves the transformed equation in `H`. -/
private theorem energyFormH1_shearCompL_eq {H : Opens E} {ν e w : E} {c₀ : ℝ}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hew : ⟪e, w⟫_ℝ = 0) (hwν : ⟪w, ν⟫_ℝ = 0)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {G : E → E} {u : W1p volume (⊤ : Opens E) 2}
    (hu : ∀ v : W1p0 volume H 2,
      energyFormH1 a 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u) (v : W1p volume H 2) =
        ∫ x in H, ⟪G x, W1p.gradient (v : W1p volume H 2) x⟫_ℝ)
    (v : W1p0 volume H 2) :
    energyFormH1 (pullbackPrincipal (shear e (-w)) a) 0 0
        (W1p.restrictL (le_top : H ≤ ⊤) (shearCompL e w hew u)) (v : W1p volume H 2) =
      ∫ x in H, ⟪pullbackDrift (shear e (-w)) G x, W1p.gradient (v : W1p volume H 2) x⟫_ℝ := by
  have hwν' : ⟪-w, ν⟫_ℝ = 0 := by rw [inner_neg_left, hwν, neg_zero]
  have key := energyFormH1_compL_eq_setIntegral_add_setIntegral_inner (U := H) (V := H)
    (shear e (-w)).differentiableOn
    (Function.LeftInverse.injective (g := shear e w) (shear_shear_neg hew)).injOn
    (mapsTo_shear hH hwν')
    (fun x _ => by rw [ContinuousLinearMap.fderiv]) one_pos
    (fun x _ => by rw [ContinuousLinearMap.fderiv, det_shear (neg_inner_eq_zero hew), abs_one])
    (Ψ := shear e w) (shear e w).differentiableOn (mapsTo_shear hH hwν)
    (fun x _ => by rw [ContinuousLinearMap.fderiv]) one_pos
    (fun x _ => by rw [ContinuousLinearMap.fderiv, det_shear hew, abs_one])
    (fun x _ => shear_shear_neg hew x)
    (fun x _ => by simpa using shear_shear_neg (neg_inner_eq_zero hew) x)
    (a := a) (b := 0) (c := 0) (f := 0) (G := G) (u := W1p.restrictL (le_top : H ≤ ⊤) u)
    (fun w => by rw [hu w]; simp) v
  rw [restrictL_shearCompL hH hew hwν]
  simpa [pullbackDrift_zero, pullbackDensity_zero] using key

/-- `u ∘ Φ` vanishes off `H` when `u` does, since `Φ x = x - ⟪e, x⟫ w` maps `H` onto itself. -/
private theorem value_shearCompL_ae_eq_zero {H : Opens E} {ν e w : E} {c₀ : ℝ}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hew : ⟪e, w⟫_ℝ = 0) (hwν : ⟪w, ν⟫_ℝ = 0)
    {u : W1p volume (⊤ : Opens E) 2} (hu0 : ∀ᵐ x, x ∉ H → W1p.value u x = 0) :
    ∀ᵐ x, x ∉ H → W1p.value (shearCompL e w hew u) x = 0 := by
  filter_upwards [value_shearCompL_ae hew u,
    (measurePreserving_shear (neg_inner_eq_zero hew)).quasiMeasurePreserving.ae hu0] with x h1 h2 hx
  rw [h1]
  exact h2 fun h => hx ((shear_mem_iff hH (by rw [inner_neg_left, hwν, neg_zero]) x).1 h)

/-- The gradient of `u ∘ Φ` is integrable and in `Lᵖ` when that of `u` is, and controls it:
`‖∇u‖_{Lᵖ} ≤ ‖T‖ ‖∇(u ∘ Φ)‖_{Lᵖ}` for the inverse shear `T x = x + ⟪e, x⟫ w`. -/
private theorem gradient_shearCompL_memLp {e w : E} (hew : ⟪e, w⟫_ℝ = 0) {p : ℝ≥0∞}
    {u : W1p volume (⊤ : Opens E) 2} (hint : Integrable (W1p.gradient u : E → E))
    (hgp : MemLp (W1p.gradient u : E → E) p volume) {κ : ℝ≥0} (hκ : ‖shear e w‖ ≤ κ) :
    Integrable (W1p.gradient (shearCompL e w hew u) : E → E) ∧
      MemLp (W1p.gradient (shearCompL e w hew u) : E → E) p volume ∧
      eLpNorm (W1p.gradient u : E → E) p volume ≤
        κ * eLpNorm (W1p.gradient (shearCompL e w hew u) : E → E) p volume := by
  have hmp := measurePreserving_shear (neg_inner_eq_zero hew)
  have hg := gradient_shearCompL_ae hew u
  refine ⟨((shear e (-w)).adjoint.integrable_comp
      ((hmp.integrable_comp hint.aestronglyMeasurable).2 hint)).congr hg.symm,
    ((shear e (-w)).adjoint.comp_memLp' (hgp.comp_measurePreserving hmp)).ae_eq hg.symm, ?_⟩
  -- `∇u ∘ Φ = T* ∇(u ∘ Φ)`, since `T* Φ* = (Φ T)* = 1`.
  have hTΦ : (shear e w).adjoint ∘L (shear e (-w)).adjoint = ContinuousLinearMap.id ℝ E := by
    rw [← ContinuousLinearMap.adjoint_comp, shear_neg_comp_shear hew,
      ContinuousLinearMap.adjoint_id]
  rw [← eLpNorm_comp_measurePreserving hgp.aestronglyMeasurable hmp]
  refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (hgp.aestronglyMeasurable.comp_measurePreserving hmp) ?_ p
  filter_upwards [hg] with x hx
  have h : (W1p.gradient u : E → E) (shear e (-w) x) =
      (shear e w).adjoint ((W1p.gradient (shearCompL e w hew u) : E → E) x) := by
    rw [hx, ← ContinuousLinearMap.comp_apply, hTΦ, ContinuousLinearMap.id_apply]
  rw [Function.comp_apply, h, ← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_mul, coe_nnNorm]
  refine ((shear e w).adjoint.le_opNorm _).trans ?_
  rw [LinearIsometryEquiv.norm_map]
  gcongr

/-- The transformed datum `G'(x) = T G(Φ x)` of a field `G ∈ Lᵖ(H)` lies in `Lᵖ(H)`, with
`‖G'‖_{Lᵖ(H)} ≤ ‖T‖ ‖G‖_{Lᵖ(H)}`. -/
private theorem pullbackDrift_shear_memLp {H : Opens E} {ν e w : E} {c₀ : ℝ}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hew : ⟪e, w⟫_ℝ = 0) (hwν : ⟪w, ν⟫_ℝ = 0) {p : ℝ≥0∞}
    {G : E → E} (hG : MemLp G p (volume.restrict H)) {κ : ℝ≥0} (hκ : ‖shear e w‖ ≤ κ) :
    MemLp (pullbackDrift (shear e (-w)) G) p (volume.restrict H) ∧
      eLpNorm (pullbackDrift (shear e (-w)) G) p (volume.restrict H) ≤
        κ * eLpNorm G p (volume.restrict H) := by
  have hmp := measurePreserving_shear_restrict hH (neg_inner_eq_zero hew)
    (by rw [inner_neg_left, hwν, neg_zero])
  have hG' : pullbackDrift (shear e (-w)) G = fun x => shear e w (G (shear e (-w) x)) := by
    funext x
    rw [pullbackDrift_eq_smul_apply G (T := shear e w)
      (by rw [ContinuousLinearMap.fderiv, shear_comp_shear_neg hew]),
      ContinuousLinearMap.fderiv, det_shear (neg_inner_eq_zero hew), abs_one, one_smul]
  have hm := (hG.comp_measurePreserving hmp)
  rw [hG']
  refine ⟨(shear e w).comp_memLp' hm, ?_⟩
  rw [← eLpNorm_comp_measurePreserving hG.aestronglyMeasurable hmp]
  refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    ((shear e w).continuous.comp_aestronglyMeasurable hm.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_) p
  rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_mul, coe_nnNorm]
  exact ((shear e w).le_opNorm _).trans (by gcongr)

/-- The bilinear form of the coefficient transformed by `Φ x = x - ⟪e, x⟫ w` is the original one
read through the adjoint `S ξ = ξ + ⟪w, ξ⟫ e` of the inverse shear. -/
private theorem matrixBilinearForm_pullbackPrincipal_shear {e w : E} (hew : ⟪e, w⟫_ℝ = 0)
    (b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (x : E) :
    matrixBilinearForm (pullbackPrincipal (shear e (-w)) b x) =
      (matrixBilinearForm (b (shear e (-w) x))).bilinearComp (shear w e) (shear w e) := by
  rw [matrixBilinearForm_pullbackPrincipal_eq_bilinearComp b (T := shear e w)
      (by rw [ContinuousLinearMap.fderiv, shear_comp_shear_neg hew]),
    ContinuousLinearMap.fderiv, det_shear (neg_inner_eq_zero hew), abs_one, one_smul,
    adjoint_shear]

/-- The matrix `A` transformed by the shear `Φ x = x - ⟪e, x⟫ w`, with `‖Φ‖, ‖Φ⁻¹‖ ≤ κ`, is
uniformly elliptic with constants `λ / κ²` and `κⁿ⁺³ Λ`. -/
private theorem uniformlyEllipticOn_pullbackPrincipal_shear {e w : E} (hew : ⟪e, w⟫_ℝ = 0)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam κ : ℝ}
    (hA : UniformlyEllipticOn univ (fun _ : E => A) lam Lam) (hT : ‖shear e w‖ ≤ κ)
    (hΦ : ‖shear e (-w)‖ ≤ κ) :
    UniformlyEllipticOn univ (fun _ : E => pullbackPrincipal (shear e (-w)) (fun _ => A) 0)
      (lam / κ ^ 2) (κ ^ (n + 1) * κ ^ 2 * Lam) := by
  have h := hA.pullbackPrincipal (Φ := shear e (-w)) (L := κ) (L' := κ) (c := 1) (s := univ)
    (mapsTo_univ _ _) univ_nonempty (fun x _ => by rwa [ContinuousLinearMap.fderiv])
    (fun x _ v => by
      rw [ContinuousLinearMap.fderiv]
      calc ‖v‖ = ‖shear e w (shear e (-w) v)‖ := by rw [shear_shear_neg hew]
        _ ≤ κ * ‖shear e (-w) v‖ := ((shear e w).le_opNorm _).trans (by gcongr))
    one_pos (fun x _ => by
      rw [ContinuousLinearMap.fderiv, det_shear (neg_inner_eq_zero hew), abs_one])
  simp only [one_mul, Fintype.card_fin] at h
  exact h.congr fun x _ => by simp [pullbackPrincipal_apply, ContinuousLinearMap.fderiv]

/-- The coefficient `a ∘ Φ` read through the shear: its bilinear form is within `‖T‖² δ` of that
of the sheared matrix wherever `a` is within `δ` of `A`. -/
private theorem norm_matrixBilinearForm_pullbackPrincipal_shear_sub_le {e w : E}
    (hew : ⟪e, w⟫_ℝ = 0) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {δ : ℝ}
    (ha : ∀ x, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) (x y : E) :
    ‖matrixBilinearForm (pullbackPrincipal (shear e (-w)) a x) -
        matrixBilinearForm (pullbackPrincipal (shear e (-w)) (fun _ => A) y)‖ ≤
      δ * ‖shear e w‖ * ‖shear e w‖ := by
  have hδ : 0 ≤ δ := (norm_nonneg (matrixBilinearForm (a x) - matrixBilinearForm A)).trans (ha x)
  rw [matrixBilinearForm_pullbackPrincipal_shear hew,
    matrixBilinearForm_pullbackPrincipal_shear hew]
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun η ξ => ?_
  have h := (matrixBilinearForm (a (shear e (-w) x)) - matrixBilinearForm A).le_opNorm₂
    (shear w e η) (shear w e ξ)
  simp only [FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.bilinearComp_apply] at h ⊢
  refine h.trans ?_
  have hS (ζ : E) : ‖shear w e ζ‖ ≤ ‖shear e w‖ * ‖ζ‖ := by
    rw [← adjoint_shear, ← LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint (shear e w)]
    exact (shear e w).adjoint.le_opNorm ζ
  calc ‖matrixBilinearForm (a (shear e (-w) x)) - matrixBilinearForm A‖ * ‖shear w e η‖ *
        ‖shear w e ξ‖ ≤ δ * (‖shear e w‖ * ‖η‖) * (‖shear e w‖ * ‖ξ‖) := by
        gcongr
        exacts [ha _, hS η, hS ξ]
    _ = δ * ‖shear e w‖ * ‖shear e w‖ * ‖η‖ * ‖ξ‖ := by ring


/-- The transformed coefficient `a ∘ Φ`, conjugated by the shear, is measurable on `H`. -/
private theorem aestronglyMeasurable_pullbackPrincipal_shear {H : Opens E} {ν e w : E} {c₀ : ℝ}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hew : ⟪e, w⟫_ℝ = 0) (hwν : ⟪w, ν⟫_ℝ = 0)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict H)) :
    AEStronglyMeasurable (pullbackPrincipal (shear e (-w)) a) (volume.restrict H) := by
  have h := ha.comp_measurePreserving (measurePreserving_shear_restrict hH (neg_inner_eq_zero hew)
    (by rw [inner_neg_left, hwν, neg_zero]))
  set M := (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (shear e (-w))
  have hF : Continuous fun X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      |(shear e (-w)).det| • (M⁻¹ * X * Matrix.transpose M⁻¹) :=
    (((continuous_const (y := M⁻¹)).matrix_mul continuous_id).matrix_mul
      (continuous_const (y := Matrix.transpose M⁻¹))).const_smul |(shear e (-w)).det|
  refine (hF.comp_aestronglyMeasurable h).congr (Filter.Eventually.of_forall fun x => ?_)
  simp [M, pullbackPrincipal_apply, ContinuousLinearMap.fderiv]

/-! ### The estimate -/

/-- The `W^{1,p}` estimate up to a flat boundary for coefficients within `δ` of a symmetric
elliptic matrix everywhere, obtained from the reflection-invariant case by a shear along the
boundary. -/
private theorem exists_eLpNorm_gradient_le_of_norm_sub_le_of_isSymm {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {H : Opens E} {ν : E} {c₀ : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) →
        AEStronglyMeasurable a (volume.restrict H) →
        UniformlyEllipticOn univ (fun _ : E => A) lam Lam → A.IsSymm →
        (∀ x, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : W1p volume (⊤ : Opens E) 2) (G : E → E),
          (∀ᵐ x, x ∉ H → W1p.value u x = 0) →
          (∀ v : W1p0 volume H 2,
            energyFormH1 a 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u) (v : W1p volume H 2) =
              ∫ x in H, ⟪G x, W1p.gradient (v : W1p volume H 2) x⟫_ℝ) →
          Integrable (W1p.gradient u : E → E) → MemLp (W1p.gradient u : E → E) p volume →
          MemLp G 2 (volume.restrict H) → MemLp G p (volume.restrict H) →
          eLpNorm (W1p.gradient u : E → E) p volume ≤ C * eLpNorm G p (volume.restrict H) := by
  -- `κ` bounds the shear and its inverse; the sheared problem has ellipticity `λ / κ², κⁿ⁺³ Λ`.
  set κ : ℝ≥0 := ⟨2 + |Lam / lam|, by positivity⟩ with hκ'
  have hκdef : (κ : ℝ) = 2 + |Lam / lam| := by rw [hκ']; rfl
  have hκ : (0 : ℝ) < κ := by rw [hκdef]; positivity
  obtain ⟨C₀, δ₀, hδ₀, h₀⟩ := exists_eLpNorm_gradient_le_of_norm_sub_le_of_reflection (n := n) hp
    hp_top (lam / (κ : ℝ) ^ 2) ((κ : ℝ) ^ (n + 1) * (κ : ℝ) ^ 2 * Lam)
  refine ⟨κ * C₀ * κ, δ₀ / (κ : ℝ) ^ 2, div_pos hδ₀ (pow_pos hκ 2), ?_⟩
  intro H ν c₀ a A hν hH ham hA hAs ha u G hu0 hu hint hgp hG2 hGp
  obtain ⟨w, hew, hwν, hw, hinv⟩ := exists_shear_of_isSymm hν hA hAs
  set e : E := ‖ν‖⁻¹ • ν
  have he : ‖e‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hν)]
  have hκw : 1 + ‖w‖ ≤ κ := by
    rw [hκdef]
    linarith [le_abs_self (Lam / lam)]
  have hT : ‖shear e w‖ ≤ κ := (norm_shear_le he w).trans hκw
  have hΦ : ‖shear e (-w)‖ ≤ κ := (norm_shear_le he (-w)).trans (by rwa [norm_neg])
  -- The sheared problem satisfies the hypotheses of the reflection-invariant case.
  have hÃ := uniformlyEllipticOn_pullbackPrincipal_shear hew hA hT hΦ
  have hãÃ (x : E) : ‖matrixBilinearForm (pullbackPrincipal (shear e (-w)) a x) -
      matrixBilinearForm (pullbackPrincipal (shear e (-w)) (fun _ => A) 0)‖ ≤ δ₀ := by
    refine (norm_matrixBilinearForm_pullbackPrincipal_shear_sub_le hew ha x 0).trans ?_
    calc δ₀ / (κ : ℝ) ^ 2 * ‖shear e w‖ * ‖shear e w‖ ≤ δ₀ / (κ : ℝ) ^ 2 * κ * κ := by gcongr
      _ = δ₀ := by field_simp
  have hÃinv (η ξ : E) : matrixBilinearForm (pullbackPrincipal (shear e (-w)) (fun _ => A) 0)
      ((ℝ ∙ ν)ᗮ.reflection η) ((ℝ ∙ ν)ᗮ.reflection ξ) =
      matrixBilinearForm (pullbackPrincipal (shear e (-w)) (fun _ => A) 0) η ξ := by
    simp only [matrixBilinearForm_pullbackPrincipal_shear hew,
      ContinuousLinearMap.bilinearComp_apply]
    exact hinv η ξ
  -- Apply the reflection-invariant estimate to `u ∘ Φ` and transform back.
  obtain ⟨hgi, hgp', hgu⟩ := gradient_shearCompL_memLp hew hint hgp hT
  obtain ⟨hG2', -⟩ := pullbackDrift_shear_memLp hH hew hwν hG2 hT
  obtain ⟨hGp', hGle⟩ := pullbackDrift_shear_memLp hH hew hwν hGp hT
  have h := h₀ hν hH (aestronglyMeasurable_pullbackPrincipal_shear hH hew hwν ham) hÃ hÃinv hãÃ
    (shearCompL e w hew u) _ (value_shearCompL_ae_eq_zero hH hew hwν hu0)
    (energyFormH1_shearCompL_eq hH hew hwν hu) hgi hgp' hG2' hGp'
  calc eLpNorm (W1p.gradient u : E → E) p volume
      ≤ κ * (C₀ * (κ * eLpNorm G p (volume.restrict H))) :=
        hgu.trans (by gcongr; exact h.trans (by gcongr))
    _ = ((κ * C₀ * κ : ℝ≥0) : ℝ≥0∞) * eLpNorm G p (volume.restrict H) := by
      push_cast
      ring

/-- The `W^{1,p}` estimate up to a flat boundary for coefficients within `δ` of an elliptic matrix
everywhere: the constant antisymmetric part `K` of the matrix does not change the energy form on
`H¹(H) × H¹₀(H)`, so subtracting it reduces the estimate to the symmetric case. -/
private theorem exists_eLpNorm_gradient_le_of_norm_sub_le {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {H : Opens E} {ν : E} {c₀ : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) →
        AEStronglyMeasurable a (volume.restrict H) →
        UniformlyEllipticOn univ (fun _ : E => A) lam Lam →
        (∀ x, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : W1p volume (⊤ : Opens E) 2) (G : E → E),
          (∀ᵐ x, x ∉ H → W1p.value u x = 0) →
          (∀ v : W1p0 volume H 2,
            energyFormH1 a 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u) (v : W1p volume H 2) =
              ∫ x in H, ⟪G x, W1p.gradient (v : W1p volume H 2) x⟫_ℝ) →
          Integrable (W1p.gradient u : E → E) → MemLp (W1p.gradient u : E → E) p volume →
          MemLp G 2 (volume.restrict H) → MemLp G p (volume.restrict H) →
          eLpNorm (W1p.gradient u : E → E) p volume ≤ C * eLpNorm G p (volume.restrict H) := by
  obtain ⟨C, δ, hδ, h⟩ := exists_eLpNorm_gradient_le_of_norm_sub_le_of_isSymm (n := n) hp hp_top
    lam Lam
  refine ⟨C, δ, hδ, ?_⟩
  intro H ν c₀ a A hν hH ham hA ha u G hu0 hu hint hgp hG2 hGp
  set K := A - coefficientSymmetricPart A with hK
  have hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (volume.restrict H) := by
    refine memLp_energyIntegrand_of_bounds (Lam := Lam + δ) (beta := 0) (gamma := 0)
      (by linarith [hA.upper_nonneg]) ham aestronglyMeasurable_const aestronglyMeasurable_const
      (fun x _ η ξ => ?_) (fun _ _ => by simp) (fun _ _ => by simp)
    have hax : ‖matrixBilinearForm (a x)‖ ≤ Lam + δ :=
      (norm_le_insert' _ (matrixBilinearForm A)).trans
        (add_le_add (hA.opNorm_matrixBilinearForm_le (mem_univ 0)) (ha x))
    rw [← matrixBilinearForm_apply, ← Real.norm_eq_abs]
    exact ((matrixBilinearForm (a x)).le_opNorm₂ η ξ).trans (by gcongr)
  have hKt : Matrix.transpose (-K) = -(-K) := by
    ext i j
    simp only [hK, Matrix.transpose_apply, Matrix.neg_apply, Matrix.sub_apply,
      coefficientSymmetricPart_apply]
    ring
  refine h (a := fun x => a x + -K) hν hH (ham.add aestronglyMeasurable_const)
    hA.coefficientSymmetricPart (coefficientSymmetricPart_isSymm A) (fun y => ?_) u G hu0
    (fun v => ?_) hint hgp hG2 hGp
  · rw [← matrixBilinearForm_sub,
      show a y + -K - coefficientSymmetricPart A = a y - A by rw [hK]; abel,
      matrixBilinearForm_sub]
    exact ha y
  · rw [energyFormH1_add_const_eq_of_transpose_eq_neg (b := 0) (c := 0) hcoeff hKt, hu v]

/-- **The `W^{1,p}` estimate up to a flat boundary, near an elliptic matrix.** Let `2 < p < ∞`
and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ` and `Λ`,
with the following property. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, and let `A` be a constant
matrix, uniformly elliptic with constants `λ, Λ` and not necessarily symmetric. Let `a` be a
coefficient matrix measurable on `H` whose bilinear form is within `δ` of that of `A`, in operator
norm, on `s ∩ H` for a measurable set `s`. Let `u ∈ H¹(ℝ^{n+1})` vanish off `H`, let `∇u` vanish
off `s`, and let `u` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in `H`, that is
`∫_H ⟨a ∇u, ∇v⟩ = ∫_H ⟨G, ∇v⟩` for every `v ∈ H¹₀(H)`, with `G ∈ L²(H) ∩ Lᵖ(H)`. If `∇u` is
integrable and in `Lᵖ`, then

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ(H)}`.

No continuity of `a` and no bound on `a` off `s` are assumed. For coefficients continuous up to
the boundary, `A` can be their value at a boundary point and `s` a small ball centred at it. -/
theorem exists_eLpNorm_gradient_le_of_norm_sub_le_of_ae_gradient_eq_zero {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {H : Opens E} {ν : E} {c₀ : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {s : Set E},
        ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → MeasurableSet s →
        AEStronglyMeasurable a (volume.restrict H) →
        UniformlyEllipticOn univ (fun _ : E => A) lam Lam →
        (∀ x ∈ s, x ∈ H → ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : W1p volume (⊤ : Opens E) 2) (G : E → E),
          (∀ᵐ x, x ∉ H → W1p.value u x = 0) → (∀ᵐ x, x ∉ s → W1p.gradient u x = 0) →
          (∀ v : W1p0 volume H 2,
            energyFormH1 a 0 0 (W1p.restrictL (le_top : H ≤ ⊤) u) (v : W1p volume H 2) =
              ∫ x in H, ⟪G x, W1p.gradient (v : W1p volume H 2) x⟫_ℝ) →
          Integrable (W1p.gradient u : E → E) → MemLp (W1p.gradient u : E → E) p volume →
          MemLp G 2 (volume.restrict H) → MemLp G p (volume.restrict H) →
          eLpNorm (W1p.gradient u : E → E) p volume ≤ C * eLpNorm G p (volume.restrict H) := by
  obtain ⟨C, δ, hδ, h⟩ := exists_eLpNorm_gradient_le_of_norm_sub_le (n := n) hp hp_top lam Lam
  refine ⟨C, δ, hδ, ?_⟩
  intro H ν c₀ a A s hν hH hs ham hA hsA u G hu0 hus hu hint hgp hG2 hGp
  classical
  -- Replace `a` by `A` off `s ∩ H`, where `∇u` vanishes.
  set b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := (s ∩ H).piecewise a (fun _ => A) with hbdef
  refine h (a := b) hν hH
    (ham.restrict.piecewise (hs.inter H.isOpen.measurableSet).nullMeasurableSet
      aestronglyMeasurable_const) hA (fun y => ?_) u G hu0 (fun v => ?_) hint hgp hG2 hGp
  · by_cases hy : y ∈ s ∩ H
    · rw [hbdef, piecewise_eq_of_mem _ _ _ hy]
      exact hsA y hy.1 hy.2
    · rw [hbdef, piecewise_eq_of_notMem _ _ _ hy]
      refine ContinuousLinearMap.opNorm_le_bound₂ _ hδ.le fun η ξ => ?_
      simp only [FunLike.coe_sub, Pi.sub_apply, sub_self, zero_apply, norm_zero]
      positivity
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

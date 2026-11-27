/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.HyperplaneReflection
public import TauCeti.Analysis.PDE.Regularity.SmallMeanOscillation
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.InnerProductSpace.Transvection
import TauCeti.Analysis.PDE.EnergyForm.Antisymmetric
import TauCeti.Analysis.PDE.EnergyForm.ChangeOfVariables
import TauCeti.Analysis.PDE.Ellipticity.ConormalShear
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.PDE.Regularity.VanishingMeanOscillation.Basic
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.InterBall

/-!
# The `W^{1,p}` estimate up to a flat boundary

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space in `ℝ^{n+1}`, let `ρ` be the reflection in its
boundary hyperplane, with linear part `R`, and let `u ∈ H¹(ℝ^{n+1})` vanish off `H` and solve

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in `H`,

that is `∫_H ⟨a ∇u, ∇v⟩ = ∫_H ⟨G, ∇v⟩` for every `v ∈ H¹₀(H)`. So `u` is a weak solution in the
half-space with zero boundary values on the hyperplane. This file proves the `W^{1,p}` estimate up
to the boundary,

`‖∇u‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ(H)}`, `2 < p < ∞`,

for every such `u` whose gradient lies in `Lᵖ`, with `C` depending only on `n`, `p` and the
ellipticity constants. It is the boundary counterpart of the whole-space estimate for
coefficients of small mean oscillation,
`TauCeti.PDE.exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le`.

The estimate also holds near a flat portion `∂Ω ∩ B(y₀, 2R)` of the boundary of any open `Ω`,
for local solutions vanishing there and coefficients close to an elliptic matrix on `B(y₀, R)`
(`TauCeti.PDE.exists_eLpNorm_gradient_inter_ball_le_eLpNorm_two_of_norm_sub_le`). This is the step
from frozen coefficients at a boundary point to the estimate on domains flattened by charts.

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
Its gradient is `∇u - R (∇u ∘ ρ)`, again in `Lᵖ`, and `‖G'‖_{Lᵖ} ≤ 2 ‖G‖_{Lᵖ(H)}`.
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
* With the conormal shear vector `s` of `Aₛ` and `ν` (`TauCeti.PDE.conormalShearVector`), which
  is orthogonal to `ν`, the shear `T x = x - ⟪ν, x⟫ s` maps `H` onto itself, has determinant one
  and sends `Aₛ ν` to a multiple of `ν`. Its inverse `Φ x = x + ⟪ν, x⟫ s` transforms the equation
  for `u` into one for `u ∘ Φ` with the coefficient `T (a - K) Tᵀ`
  (`TauCeti.PDE.energyFormH1_compL_eq_setIntegral_add_setIntegral_inner`), close to `T Aₛ Tᵀ`,
  whose conormal at the boundary is normal. So `T Aₛ Tᵀ` is invariant under the reflection
  (`TauCeti.PDE.matrixBilinearForm_pullbackPrincipal_reflection_of_fderiv_eq`), and the norms of
  `∇u` and `G` change at most by the factor `‖T‖`.

For the local estimate, a cutoff extends `u` by zero to `w ∈ H¹(B(y₀, R))` vanishing off `H`. For a
reflection-invariant `A`, the odd reflection of `w` solves an equation in the whole ball, and the
interior estimate `TauCeti.PDE.exists_eLpNorm_gradient_ball_le_eLpNorm_two_of_setAverage_le`
applies. A general `A` is reduced to this case as above; the shear maps `B(T y₀, R / ‖Φ‖)` into
`B(y₀, R)`, so the estimate holds on a smaller ball `B(y₀, θR)`.

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

/-- A coefficient field within `δ ≥ 0` of a matrix `A` everywhere has mean deviation at most `δ`
from `A` on every ball. -/
private theorem setAverage_norm_matrixBilinearForm_sub_le
    {b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {δ : ℝ} (hδ : 0 ≤ δ) (h : ∀ x, ‖matrixBilinearForm (b x) - matrixBilinearForm A‖ ≤ δ)
    (c : E) (r : ℝ) : ⨍ x in ball c r, ‖matrixBilinearForm (b x) - matrixBilinearForm A‖ ≤ δ :=
  (Real.le_norm_self _).trans
    (norm_setAverage_le_of_norm_le_const hδ fun x _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact h x)

/-- The odd reflection `u - u ∘ ρ` of a weak solution `u` of `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in `U ∩ H`
vanishing on `U ∖ H`, for an open `U` mapped into itself by `ρ`, solves `-∂ᵢ(a'ⁱʲ ∂ⱼw) = -div G'` in
`U`, tested against test functions, where `a'` is the reflected coefficient and
`G' = 1_H G - 1_H (R G) ∘ ρ`. -/
private theorem energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq {U H : Opens E}
    {ν : E} {c₀ : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {Lam : ℝ} (hν : ν ≠ 0)
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hU : MapsTo (hyperplaneReflection ν c₀) U U)
    (hãm : AEStronglyMeasurable (reflectPrincipal ν c₀ a) (volume.restrict U))
    (hãbd : ∀ x, ‖matrixBilinearForm (reflectPrincipal ν c₀ a x)‖ ≤ Lam)
    {u : W1p volume U 2} {G : E → E} (hu0 : ∀ᵐ x ∂volume.restrict U, x ∉ H → W1p.value u x = 0)
    (hu : ∀ v : W1p0 volume (U ⊓ H) 2,
      energyFormH1 a 0 0 (W1p.restrictL (inf_le_left : U ⊓ H ≤ U) u)
        (v : W1p volume (U ⊓ H) 2) =
          ∫ x in U ⊓ H, ⟪G x, W1p.gradient (v : W1p volume (U ⊓ H) 2) x⟫_ℝ)
    (hG2 : MemLp G 2 (volume.restrict (U ⊓ H))) (φ : 𝓓(U, ℝ)) :
    energyFormH1 (reflectPrincipal ν c₀ a) 0 0
        (u - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU u)
        (W1p.ofTestFunctionₗ volume U 2 φ) =
      ∫ x in U, ⟪(H : Set E).indicator G x - (H : Set E).indicator
        (fun y => (ℝ ∙ ν)ᗮ.reflection (G y)) (hyperplaneReflection ν c₀ x), ∇ (φ : E → ℝ) x⟫_ℝ := by
  have hcoeff : MemLp (fun x => energyIntegrand (reflectPrincipal ν c₀ a x)
      (reflectDrift ν c₀ 0 x) (reflectDensity ν c₀ 0 x)) ⊤ (volume.restrict U) := by
    rw [reflectDrift_zero, reflectDensity_zero]
    exact memLp_energyIntegrand_zero_zero_of_norm_le
      ((norm_nonneg (matrixBilinearForm (reflectPrincipal ν c₀ a 0))).trans (hãbd 0)) hãm
      fun x _ => hãbd x
  -- The weak formulation in the form of the reflection lemma: `f = 0` and `F = -G`.
  have h' :=
    energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq_setIntegral_sub_setIntegral
      (b := 0) (c := 0) (f := 0) hν hH hU hcoeff hu0 MemLp.zero hG2.neg (fun v => by
        rw [hu v]
        simp only [Pi.zero_apply, zero_mul, integral_zero, Pi.neg_apply, inner_neg_left,
          integral_neg, zero_sub, neg_neg]) ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩
  rw [reflectDrift_zero, reflectDensity_zero] at h'
  refine h'.trans ?_
  simp only [indicator_zero', Pi.zero_apply, sub_zero, zero_mul, integral_zero, zero_sub,
    ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) 2 φ] with x hx
  rw [W1p.gradient_ofTestFunctionₗ, hx, ← inner_neg_left]
  congr 1
  simp only [Pi.neg_apply, map_neg]
  rw [Set.indicator_neg', Set.indicator_neg, Pi.neg_apply, neg_sub_neg, neg_sub]

/-- The case `U = ℝ^{n+1}` of
`energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq`, for `u ∈ H¹(ℝ^{n+1})` vanishing
off `H`. -/
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
  -- Transport the weak formulation from `H` to `⊤ ⊓ H`.
  have hu' : ∀ V : Opens E, V = H → ∀ hV : V ≤ ⊤, ∀ v : W1p0 volume V 2,
      energyFormH1 a 0 0 (W1p.restrictL hV u) (v : W1p volume V 2) =
        ∫ x in V, ⟪G x, W1p.gradient (v : W1p volume V 2) x⟫_ℝ := by
    rintro V rfl _ v
    exact hu v
  have h := energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq hν hH
    (mapsTo_hyperplaneReflection_top ν c₀) hãm.restrict hãbd
    (by simpa only [Opens.coe_top, Measure.restrict_univ] using hu0)
    (hu' _ (top_inf_eq H) inf_le_left)
    (by simpa only [Opens.coe_inf, Opens.coe_top, univ_inter] using hG2) φ
  simpa only [Opens.coe_top, Measure.restrict_univ] using h

/-- The gradient of the odd reflection `u - u ∘ ρ` of `u ∈ H¹(ℝ^{n+1})` is in `Lᵖ` when that of
`u` is. -/
private theorem memLp_gradient_sub_compHyperplaneReflectionL {p : ℝ≥0∞}
    (ν : E) (c₀ : ℝ) {u : W1p volume (⊤ : Opens E) 2}
    (hgp : MemLp (W1p.gradient u : E → E) p volume) :
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
  -- Composing with `ρ` and with `R` preserves `Lᵖ` membership.
  have hR : MemLp (fun x => R (W1p.gradient u (hyperplaneReflection ν c₀ x))) p volume :=
    R.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' (hgp.comp_measurePreserving hρ)
  exact (hgp.sub hR).ae_eq hgw.symm

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
`∫_H ⟨a ∇u, ∇v⟩ = ∫_H ⟨G, ∇v⟩` for every `v ∈ H¹₀(H)`, with `G ∈ L²(H) ∩ Lᵖ(H)`, and let `∇u` lie
in `Lᵖ`. Then

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
          MemLp (W1p.gradient u : E → E) p volume →
          MemLp G 2 (volume.restrict H) → MemLp G p (volume.restrict H) →
          eLpNorm (W1p.gradient u : E → E) p volume ≤ C * eLpNorm G p (volume.restrict H) := by
  obtain ⟨C, δ, hδ, h⟩ :=
    exists_eLpNorm_gradient_le_of_forall_energyFormH1_eq_of_setAverage_le (n := n) hp hp_top
      lam Lam
  refine ⟨2 * C, δ, hδ, ?_⟩
  intro H ν c₀ a hν hH ham hbd hosc u G hu0 hu hgp hG2 hGp
  obtain ⟨hG'p, hG'le⟩ :=
    memLp_indicator_sub_indicator_linearIsometryEquiv_comp_hyperplaneReflection
      (one_le_two.trans hp.le) H.isOpen.measurableSet MeasurableSet.univ
      (mapsTo_univ (hyperplaneReflection ν c₀) univ) (ℝ ∙ ν)ᗮ.reflection (by rwa [univ_inter])
  simp only [Measure.restrict_univ, univ_inter] at hG'p hG'le
  have hwgp := memLp_gradient_sub_compHyperplaneReflectionL ν c₀ hgp
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
    hwgp hG'p
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
          MemLp (W1p.gradient u : E → E) p volume →
          MemLp G 2 (volume.restrict H) → MemLp G p (volume.restrict H) →
          eLpNorm (W1p.gradient u : E → E) p volume ≤ C * eLpNorm G p (volume.restrict H) := by
  obtain ⟨C, δ, hδ, h⟩ :=
    exists_eLpNorm_gradient_le_of_setAverage_reflectPrincipal_le (n := n) hp hp_top lam (Lam + 1)
  refine ⟨C, min δ 1, lt_min hδ one_pos, ?_⟩
  intro H ν c₀ a A hν hH ham hA hAinv ha u G hu0 hu hgp hG2 hGp
  have ha' := norm_matrixBilinearForm_reflectPrincipal_sub_le (c₀ := c₀) (a := a) hν hAinv
    (fun y _ => ha y)
  refine h (a := a) hν hH ham (fun x _ => ?_) (fun c r _ => ⟨A, ?_, ?_⟩) u G hu0 hu hgp hG2 hGp
  · -- `a x` is within `1` of `A`, whose form has norm at most `Λ`.
    exact hA.opNorm_matrixBilinearForm_le_add (mem_univ 0) ((ha x).trans (min_le_right _ _))
  · exact (hA.mono_set (subset_univ _)).mono_constants hA.pos le_rfl (by linarith)
  · -- The reflected coefficient of `a` is within `min δ 1` of `A` everywhere.
    exact setAverage_norm_matrixBilinearForm_sub_le hδ.le
      (fun x => (ha' x).trans (min_le_left _ _)) c r

/-! ### Shears along the boundary hyperplane

For `⟪e, w⟫ = 0`, the shear `TauCeti.transvectionL e w`, `x ↦ x + ⟪e, x⟫ w`, has determinant one,
and its inverse is the shear by `-w`. When moreover `w ⊥ ν`, it maps the half-space
`{c₀ < ⟪x, ν⟫}` onto itself. -/

private theorem inner_neg_right_eq_zero {x y : E} (h : ⟪x, y⟫_ℝ = 0) : ⟪x, -y⟫_ℝ = 0 := by
  rw [inner_neg_right, h, neg_zero]

private theorem transvectionL_mem_iff {H : Opens E} {ν e w : E} {c₀ : ℝ}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hνw : ⟪ν, w⟫_ℝ = 0) (x : E) :
    transvectionL e w x ∈ H ↔ x ∈ H := by
  rw [hH, hH, real_inner_comm, inner_transvectionL hνw, real_inner_comm]

private theorem mapsTo_transvectionL {H : Opens E} {ν e w : E} {c₀ : ℝ}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hνw : ⟪ν, w⟫_ℝ = 0) :
    MapsTo (transvectionL e w) (H : Set E) (H : Set E) :=
  fun x hx => (transvectionL_mem_iff hH hνw x).2 hx

/-! ### Transporting the problem along the shear

The lemmas below state once the derivative and determinant hypotheses of `TauCeti.W1p.compL` for
a shear, and the operator `TauCeti.W1p.compL` of the inverse shear on any pair of open sets. -/

/-- The derivative of the shear `transvectionL e w` is the shear itself, so on every set its norm
is at most that of the shear: the derivative bound of `TauCeti.W1p.compL`. -/
private theorem norm_fderiv_transvectionL_le (e w : E) {s : Set E} :
    ∀ x ∈ s, ‖fderiv ℝ (transvectionL e w) x‖ ≤ ‖transvectionL e w‖ :=
  fun _ _ => (congrArg norm (transvectionL e w).fderiv).le

/-- For `⟪e, w⟫ = 0`, the derivative of the shear `transvectionL e w` has determinant of absolute
value one on every set: the determinant bound of `TauCeti.W1p.compL`. -/
private theorem one_le_abs_det_fderiv_transvectionL {e w : E} (hew : ⟪e, w⟫_ℝ = 0) {s : Set E} :
    ∀ x ∈ s, 1 ≤ |(fderiv ℝ (transvectionL e w) x).det| :=
  fun x _ => (abs_det_fderiv_transvectionL hew x).ge

/-- Precomposition with the shear `Φ x = x - ⟪e, x⟫ w`, for `⟪e, w⟫ = 0`, as an operator from
`H¹(V)` to `H¹(U)` for open sets `U, V` with `Φ(U) ⊆ V`. -/
private noncomputable def shearCompOnL {U V : Opens E} (e w : E) (hew : ⟪e, w⟫_ℝ = 0)
    (hmaps : MapsTo (transvectionL e (-w)) U V) : W1p volume V 2 →L[ℝ] W1p volume U 2 :=
  W1p.compL (transvectionL e (-w)) ENNReal.ofNat_ne_top (transvectionL e (-w)).differentiableOn
    (transvectionL_injective (inner_neg_right_eq_zero hew)).injOn hmaps
    (norm_fderiv_transvectionL_le e (-w)) one_pos
    (one_le_abs_det_fderiv_transvectionL (inner_neg_right_eq_zero hew))

/-- Precomposition with the shear `x ↦ x - ⟪e, x⟫ w`, for `⟪e, w⟫ = 0`, as an operator on
`H¹(ℝ^{n+1})`. -/
private noncomputable def shearCompL (e w : E) (hew : ⟪e, w⟫_ℝ = 0) :
    W1p volume (⊤ : Opens E) 2 →L[ℝ] W1p volume (⊤ : Opens E) 2 :=
  shearCompOnL e w hew fun _ _ => trivial

/-- The value of `u ∘ Φ`, for the shear `Φ x = x - ⟪e, x⟫ w`. -/
private theorem value_shearCompOnL_ae {U V : Opens E} {e w : E} (hew : ⟪e, w⟫_ℝ = 0)
    (hmaps : MapsTo (transvectionL e (-w)) U V) (u : W1p volume V 2) :
    W1p.value (shearCompOnL e w hew hmaps u) =ᵐ[volume.restrict U]
      fun x => W1p.value u (transvectionL e (-w) x) :=
  W1p.value_compL_ae _ _ _ _ _ _ _ _ u

/-- The gradient of `u ∘ Φ`, for the shear `Φ x = x - ⟪e, x⟫ w`: `∇(u ∘ Φ) = Φ* (∇u ∘ Φ)`. -/
private theorem gradient_shearCompOnL_ae {U V : Opens E} {e w : E} (hew : ⟪e, w⟫_ℝ = 0)
    (hmaps : MapsTo (transvectionL e (-w)) U V) (u : W1p volume V 2) :
    W1p.gradient (shearCompOnL e w hew hmaps u) =ᵐ[volume.restrict U]
      fun x => (transvectionL e (-w)).adjoint (W1p.gradient u (transvectionL e (-w) x)) := by
  have h : W1p.gradient (shearCompOnL e w hew hmaps u) =ᵐ[volume.restrict U] _ :=
    W1p.gradient_compL_ae _ _ _ _ _ _ _ _ u
  simpa only [ContinuousLinearMap.fderiv] using h

/-- Restricting `u ∘ Φ` to `U₁` is composing the restriction of `u` to `V₁` with `Φ`, for the
shear `Φ` mapping `U` into `V` and `U₁` into `V₁`. -/
private theorem restrictL_shearCompOnL {U V U₁ V₁ : Opens E} {e w : E} (hew : ⟪e, w⟫_ℝ = 0)
    (hU : U₁ ≤ U) (hV : V₁ ≤ V) (hmaps : MapsTo (transvectionL e (-w)) U V)
    (hmaps₁ : MapsTo (transvectionL e (-w)) U₁ V₁) (u : W1p volume V 2) :
    W1p.restrictL hU (shearCompOnL e w hew hmaps u) =
      shearCompOnL e w hew hmaps₁ (W1p.restrictL hV u) := by
  have hq := (measurePreserving_transvectionL volume
    (inner_neg_right_eq_zero hew)).quasiMeasurePreserving.restrict hmaps₁
  refine W1p.ext_value (Lp.ext ?_)
  filter_upwards [W1p.value_restrictL_ae hU (shearCompOnL e w hew hmaps u),
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hU)
      (value_shearCompOnL_ae hew hmaps u), value_shearCompOnL_ae hew hmaps₁ (W1p.restrictL hV u),
    hq.ae_eq_comp (W1p.value_restrictL_ae hV u)] with x h1 h2 h3 h4
  rw [h1, h2, h3]
  exact h4.symm

/-- **The weak equation along the shear.** If `u` solves `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in `V`, tested
against `H¹₀(V)`, then `u ∘ Φ`, `Φ x = x - ⟪e, x⟫ w`, solves the transformed equation in `U`, for
open `U`, `V` with `Φ(U) ⊆ V` and `Φ⁻¹(V) ⊆ U`. -/
private theorem energyFormH1_shearCompOnL_eq {U V : Opens E} {e w : E} (hew : ⟪e, w⟫_ℝ = 0)
    (hmaps : MapsTo (transvectionL e (-w)) U V) (hmaps' : MapsTo (transvectionL e w) V U)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {G : E → E} {u : W1p volume V 2}
    (hu : ∀ v : W1p0 volume V 2, energyFormH1 a 0 0 u (v : W1p volume V 2) =
      ∫ x in V, ⟪G x, W1p.gradient (v : W1p volume V 2) x⟫_ℝ)
    (v : W1p0 volume U 2) :
    energyFormH1 (pullbackPrincipal (transvectionL e (-w)) a) 0 0
        (shearCompOnL e w hew hmaps u) (v : W1p volume U 2) =
      ∫ x in U,
        ⟪pullbackDrift (transvectionL e (-w)) G x, W1p.gradient (v : W1p volume U 2) x⟫_ℝ := by
  have key := energyFormH1_compL_eq_setIntegral_add_setIntegral_inner (U := U) (V := V)
    (transvectionL e (-w)).differentiableOn
    (transvectionL_injective (inner_neg_right_eq_zero hew)).injOn hmaps
    (norm_fderiv_transvectionL_le e (-w)) one_pos
    (one_le_abs_det_fderiv_transvectionL (inner_neg_right_eq_zero hew))
    (Ψ := transvectionL e w) (transvectionL e w).differentiableOn hmaps'
    (norm_fderiv_transvectionL_le e w) one_pos (one_le_abs_det_fderiv_transvectionL hew)
    (fun x _ => transvectionL_transvectionL_neg hew x)
    (fun x _ => transvectionL_neg_transvectionL hew x)
    (a := a) (b := 0) (c := 0) (f := 0) (G := G) (u := u) (fun w => by rw [hu w]; simp) v
  rw [shearCompOnL]
  simpa [pullbackDrift_zero, pullbackDensity_zero] using key

/-- `u ∘ Φ` vanishes off `H` when `u` does, since `Φ x = x - ⟪e, x⟫ w` maps `H` onto itself. -/
private theorem value_shearCompL_ae_eq_zero {H : Opens E} {ν e w : E} {c₀ : ℝ}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hew : ⟪e, w⟫_ℝ = 0) (hνw : ⟪ν, w⟫_ℝ = 0)
    {u : W1p volume (⊤ : Opens E) 2} (hu0 : ∀ᵐ x, x ∉ H → W1p.value u x = 0) :
    ∀ᵐ x, x ∉ H → W1p.value (shearCompL e w hew u) x = 0 := by
  have h := value_shearCompOnL_ae (U := ⊤) hew (fun _ _ => trivial) u
  simp only [Opens.coe_top, Measure.restrict_univ] at h
  filter_upwards [h,
    (measurePreserving_transvectionL volume
      (inner_neg_right_eq_zero hew)).quasiMeasurePreserving.ae hu0] with x h1 h2 hx
  exact h1.trans (h2 fun h => hx ((transvectionL_mem_iff hH (inner_neg_right_eq_zero hνw) x).1 h))

/-- The gradient of `u ∘ Φ` is in `Lᵖ` when that of `u` is, and controls it:
`‖∇u‖_{Lᵖ} ≤ ‖T‖ ‖∇(u ∘ Φ)‖_{Lᵖ}` for the inverse shear `T x = x + ⟪e, x⟫ w`. -/
private theorem gradient_shearCompL_memLp {e w : E} (hew : ⟪e, w⟫_ℝ = 0) {p : ℝ≥0∞}
    {u : W1p volume (⊤ : Opens E) 2} (hgp : MemLp (W1p.gradient u : E → E) p volume) {κ : ℝ≥0}
    (hκ : ‖transvectionL e w‖ ≤ κ) :
    MemLp (W1p.gradient (shearCompL e w hew u) : E → E) p volume ∧
      eLpNorm (W1p.gradient u : E → E) p volume ≤
        κ * eLpNorm (W1p.gradient (shearCompL e w hew u) : E → E) p volume := by
  have hmp := measurePreserving_transvectionL volume (inner_neg_right_eq_zero hew)
  have hg : W1p.gradient (shearCompL e w hew u) =ᵐ[volume]
      fun x => (transvectionL e (-w)).adjoint (W1p.gradient u (transvectionL e (-w) x)) := by
    have h := gradient_shearCompOnL_ae (U := ⊤) hew (fun _ _ => trivial) u
    simp only [Opens.coe_top, Measure.restrict_univ] at h
    exact h
  refine ⟨((transvectionL e (-w)).adjoint.comp_memLp' (hgp.comp_measurePreserving hmp)).ae_eq
    hg.symm, ?_⟩
  -- `∇u ∘ Φ = T* ∇(u ∘ Φ)`, since `T* Φ* = (Φ T)* = 1`.
  have hTΦ : (transvectionL e w).adjoint ∘L (transvectionL e (-w)).adjoint =
      ContinuousLinearMap.id ℝ E := by
    rw [← ContinuousLinearMap.adjoint_comp, transvectionL_neg_comp_transvectionL hew,
      ContinuousLinearMap.adjoint_id]
  rw [← eLpNorm_comp_measurePreserving hgp.aestronglyMeasurable hmp]
  refine eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (hgp.aestronglyMeasurable.comp_measurePreserving hmp) ?_ p
  filter_upwards [hg] with x hx
  have h : (W1p.gradient u : E → E) (transvectionL e (-w) x) =
      (transvectionL e w).adjoint ((W1p.gradient (shearCompL e w hew u) : E → E) x) := by
    rw [hx, ← ContinuousLinearMap.comp_apply, hTΦ, ContinuousLinearMap.id_apply]
  rw [Function.comp_apply, h, adjoint_transvectionL, ← NNReal.coe_le_coe, coe_nnNorm,
    NNReal.coe_mul, coe_nnNorm]
  refine ((transvectionL w e).le_opNorm _).trans ?_
  rw [norm_transvectionL_comm]
  gcongr

/-- The transformed datum `G'(x) = T G(Φ x)` of a field `G ∈ Lᵖ(S')`, for the shear
`Φ x = x - ⟪e, x⟫ w` mapping `S` into `S'`, lies in `Lᵖ(S)`, with
`‖G'‖_{Lᵖ(S)} ≤ ‖T‖ ‖G‖_{Lᵖ(S')}`. -/
private theorem pullbackDrift_shear_memLp {e w : E} (hew : ⟪e, w⟫_ℝ = 0) {S S' : Set E}
    (hS' : MeasurableSet S') (hmaps : MapsTo (transvectionL e (-w)) S S') {p : ℝ≥0∞}
    {G : E → E} (hG : MemLp G p (volume.restrict S')) {κ : ℝ≥0} (hκ : ‖transvectionL e w‖ ≤ κ) :
    MemLp (pullbackDrift (transvectionL e (-w)) G) p (volume.restrict S) ∧
      eLpNorm (pullbackDrift (transvectionL e (-w)) G) p (volume.restrict S) ≤
        κ * eLpNorm G p (volume.restrict S') := by
  have hG' : pullbackDrift (transvectionL e (-w)) G =
      fun x => transvectionL e w (G (transvectionL e (-w) x)) := by
    funext x
    rw [pullbackDrift_eq_smul_apply G (T := transvectionL e w)
      (by rw [ContinuousLinearMap.fderiv, transvectionL_comp_transvectionL_neg hew]),
      abs_det_fderiv_transvectionL (inner_neg_right_eq_zero hew), one_smul]
  have hle : eLpNorm (pullbackDrift (transvectionL e (-w)) G) p (volume.restrict S) ≤
      κ * eLpNorm G p (volume.restrict S') := by
    rw [hG']
    exact (measurePreserving_transvectionL volume (inner_neg_right_eq_zero hew))
      |>.eLpNorm_clm_comp_restrict_le_of_mapsTo hS' hmaps hκ G p
  exact ⟨hle.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hG.eLpNorm_lt_top), hle⟩

/-- The matrix `A` transformed by the shear `Φ x = x - ⟪e, x⟫ w`, with `‖Φ‖, ‖Φ⁻¹‖ ≤ κ`, is
uniformly elliptic with constants `λ / κ²` and `κⁿ⁺³ Λ`. -/
private theorem uniformlyEllipticOn_pullbackPrincipal_shear {e w : E} (hew : ⟪e, w⟫_ℝ = 0)
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam κ : ℝ}
    (hA : UniformlyEllipticOn univ (fun _ : E => A) lam Lam) (hT : ‖transvectionL e w‖ ≤ κ)
    (hΦ : ‖transvectionL e (-w)‖ ≤ κ) :
    UniformlyEllipticOn univ
      (fun _ : E => pullbackPrincipal (transvectionL e (-w)) (fun _ => A) 0)
      (lam / κ ^ 2) (κ ^ (n + 1) * κ ^ 2 * Lam) := by
  have h := hA.pullbackPrincipal (Φ := transvectionL e (-w)) (L := κ) (L' := κ) (c := 1)
    (s := univ) (mapsTo_univ _ _) univ_nonempty (fun x _ => by rwa [ContinuousLinearMap.fderiv])
    (fun x _ v => by
      rw [ContinuousLinearMap.fderiv]
      calc ‖v‖ = ‖transvectionL e w (transvectionL e (-w) v)‖ := by
            rw [transvectionL_transvectionL_neg hew]
        _ ≤ κ * ‖transvectionL e (-w) v‖ := ((transvectionL e w).le_opNorm _).trans (by gcongr))
    one_pos (one_le_abs_det_fderiv_transvectionL (inner_neg_right_eq_zero hew))
  simp only [one_mul, Fintype.card_fin] at h
  exact h.congr fun x _ => by simp [pullbackPrincipal_apply, ContinuousLinearMap.fderiv]

/-- The coefficient `a ∘ Φ` read through the shear `Φ x = x - ⟪e, x⟫ w`, whose inverse `T` has
norm at most `κ > 0`: its bilinear form is within `δ` of that of the sheared matrix wherever `a` is
within `δ / κ²` of `A`. -/
private theorem norm_matrixBilinearForm_pullbackPrincipal_shear_sub_le {e w : E}
    (hew : ⟪e, w⟫_ℝ = 0) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {δ κ : ℝ} {x : E} (hκ : 0 < κ)
    (hT : ‖transvectionL e w‖ ≤ κ)
    (ha : ‖matrixBilinearForm (a (transvectionL e (-w) x)) - matrixBilinearForm A‖ ≤ δ / κ ^ 2)
    (y : E) :
    ‖matrixBilinearForm (pullbackPrincipal (transvectionL e (-w)) a x) -
        matrixBilinearForm (pullbackPrincipal (transvectionL e (-w)) (fun _ => A) y)‖ ≤ δ := by
  have hδ : 0 ≤ δ / κ ^ 2 :=
    (norm_nonneg (matrixBilinearForm (a (transvectionL e (-w) x)) - matrixBilinearForm A)).trans ha
  have hew' := inner_neg_right_eq_zero hew
  rw [matrixBilinearForm_pullbackPrincipal_of_fderiv_eq_transvectionL a hew'
      ((transvectionL e (-w)).fderiv (x := x)),
    matrixBilinearForm_pullbackPrincipal_of_fderiv_eq_transvectionL (fun _ => A) hew'
      ((transvectionL e (-w)).fderiv (x := y)), neg_neg]
  refine (ContinuousLinearMap.opNorm_le_bound₂ _
    (by positivity : 0 ≤ δ / κ ^ 2 * ‖transvectionL e w‖ * ‖transvectionL e w‖)
    fun η ξ => ?_).trans ?_
  swap
  · calc δ / κ ^ 2 * ‖transvectionL e w‖ * ‖transvectionL e w‖ ≤ δ / κ ^ 2 * κ * κ := by gcongr
      _ = δ := by field_simp
  have h := (matrixBilinearForm (a (transvectionL e (-w) x)) - matrixBilinearForm A).le_opNorm₂
    (transvectionL w e η) (transvectionL w e ξ)
  simp only [FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.bilinearComp_apply] at h ⊢
  refine h.trans ?_
  calc ‖matrixBilinearForm (a (transvectionL e (-w) x)) - matrixBilinearForm A‖ *
        ‖transvectionL w e η‖ * ‖transvectionL w e ξ‖ ≤
        δ / κ ^ 2 * (‖transvectionL w e‖ * ‖η‖) * (‖transvectionL w e‖ * ‖ξ‖) := by
        gcongr
        exacts [(transvectionL w e).le_opNorm η, (transvectionL w e).le_opNorm ξ]
    _ = δ / κ ^ 2 * ‖transvectionL e w‖ * ‖transvectionL e w‖ * ‖η‖ * ‖ξ‖ := by
        rw [norm_transvectionL_comm]
        ring


/-- The transformed coefficient `a ∘ Φ`, conjugated by the shear `Φ x = x - ⟪e, x⟫ w`, is
measurable on `S` when `a` is measurable on a set `S' ⊇ Φ(S)`. -/
private theorem aestronglyMeasurable_pullbackPrincipal_shear {e w : E} (hew : ⟪e, w⟫_ℝ = 0)
    {S S' : Set E} (hmaps : MapsTo (transvectionL e (-w)) S S')
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict S')) :
    AEStronglyMeasurable (pullbackPrincipal (transvectionL e (-w)) a) (volume.restrict S) := by
  have h := ha.comp_quasiMeasurePreserving ((measurePreserving_transvectionL volume
    (inner_neg_right_eq_zero hew)).quasiMeasurePreserving.restrict hmaps)
  set M := (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (transvectionL e (-w))
  have hF : Continuous fun X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
      |(transvectionL e (-w)).det| • (M⁻¹ * X * Matrix.transpose M⁻¹) :=
    (((continuous_const (y := M⁻¹)).matrix_mul continuous_id).matrix_mul
      (continuous_const (y := Matrix.transpose M⁻¹))).const_smul |(transvectionL e (-w)).det|
  refine (hF.comp_aestronglyMeasurable h).congr (Filter.Eventually.of_forall fun x => ?_)
  simp [M, pullbackPrincipal_apply, ContinuousLinearMap.fderiv]

/-! ### The estimate -/

/-- **The conormal shear of a symmetric elliptic matrix.** Let `A` be symmetric and uniformly
elliptic with constants `λ, Λ`, let `ν ≠ 0` and let `s` be the conormal shear vector of `A` and
`ν`. Then `⟪ν, -s⟫ = 0`, the shear `T x = x - ⟪ν, x⟫ s` and its inverse `Φ` have norm at most
`1 + |Λ / λ|`, and the matrix `A` transformed by `Φ` is invariant under the reflection in `ν⊥`. -/
private theorem conormalShearVector_spec {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {lam Lam : ℝ} {ν : E} (hν : ν ≠ 0) (hA : UniformlyEllipticOn univ (fun _ : E => A) lam Lam)
    (hAs : A.IsSymm) :
    ⟪ν, -conormalShearVector A ν⟫_ℝ = 0 ∧
      ‖transvectionL ν (-conormalShearVector A ν)‖ ≤ 1 + |Lam / lam| ∧
      ‖transvectionL ν (-(-conormalShearVector A ν))‖ ≤ 1 + |Lam / lam| ∧
      ∀ η ξ, matrixBilinearForm
          (pullbackPrincipal (transvectionL ν (-(-conormalShearVector A ν))) (fun _ => A) 0)
          ((ℝ ∙ ν)ᗮ.reflection η) ((ℝ ∙ ν)ᗮ.reflection ξ) =
        matrixBilinearForm
          (pullbackPrincipal (transvectionL ν (-(-conormalShearVector A ν))) (fun _ => A) 0)
          η ξ := by
  have hq : matrixBilinearForm A ν ν ≠ 0 := by
    have h := hA.lower_bound (mem_univ 0) ν
    rw [Matrix.toQuadraticForm'_apply, ← matrixBilinearForm_apply] at h
    exact (lt_of_lt_of_le (by have := hA.pos; have := norm_pos_iff.2 hν; positivity) h).ne'
  have hκs : 1 + ‖ν‖ * ‖-conormalShearVector A ν‖ ≤ 1 + |Lam / lam| := by
    rw [norm_neg]
    linarith [le_abs_self (Lam / lam), norm_mul_norm_conormalShearVector_le hA.pos hν
      (hA.lower_bound (mem_univ 0)) (hA.upper_bound (mem_univ 0))]
  exact ⟨inner_neg_right_eq_zero (inner_conormalShearVector_right_eq_zero hν hq),
    (norm_transvectionL_le ν _).trans hκs, (norm_transvectionL_le ν _).trans (by rwa [norm_neg]),
    matrixBilinearForm_pullbackPrincipal_reflection_of_fderiv_eq hν hq
      (fun η ξ => by rw [← matrixBilinearForm_transpose_apply, hAs.eq])
      (by rw [ContinuousLinearMap.fderiv, neg_neg])⟩

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
          MemLp (W1p.gradient u : E → E) p volume →
          MemLp G 2 (volume.restrict H) → MemLp G p (volume.restrict H) →
          eLpNorm (W1p.gradient u : E → E) p volume ≤ C * eLpNorm G p (volume.restrict H) := by
  -- `κ` bounds the shear and its inverse; the sheared problem has ellipticity `λ / κ², κⁿ⁺³ Λ`.
  set κ : ℝ≥0 := (1 + |Lam / lam|).toNNReal
  have hκdef : (κ : ℝ) = 1 + |Lam / lam| := Real.coe_toNNReal _ (by positivity)
  have hκ : (0 : ℝ) < κ := by rw [hκdef]; positivity
  obtain ⟨C₀, δ₀, hδ₀, h₀⟩ := exists_eLpNorm_gradient_le_of_norm_sub_le_of_reflection (n := n) hp
    hp_top (lam / (κ : ℝ) ^ 2) ((κ : ℝ) ^ (n + 1) * (κ : ℝ) ^ 2 * Lam)
  refine ⟨κ * C₀ * κ, δ₀ / (κ : ℝ) ^ 2, div_pos hδ₀ (pow_pos hκ 2), ?_⟩
  intro H ν c₀ a A hν hH ham hA hAs ha u G hu0 hu hgp hG2 hGp
  -- The shear is `T x = x - ⟪ν, x⟫ s` for the conormal shear vector `s`; its inverse is `Φ`.
  obtain ⟨hνs, hT, hΦ, hÃinv⟩ := conormalShearVector_spec hν hA hAs
  rw [← hκdef] at hT hΦ
  set s := conormalShearVector A ν
  -- The sheared problem satisfies the hypotheses of the reflection-invariant case.
  have hÃ := uniformlyEllipticOn_pullbackPrincipal_shear hνs hA hT hΦ
  have hãÃ (x : E) : ‖matrixBilinearForm (pullbackPrincipal (transvectionL ν (-(-s))) a x) -
      matrixBilinearForm (pullbackPrincipal (transvectionL ν (-(-s))) (fun _ => A) 0)‖ ≤ δ₀ := by
    exact norm_matrixBilinearForm_pullbackPrincipal_shear_sub_le hνs hκ hT (ha _) 0
  -- Apply the reflection-invariant estimate to `u ∘ Φ` and transform back.
  obtain ⟨hgp', hgu⟩ := gradient_shearCompL_memLp hνs hgp hT
  have hmapsH := mapsTo_transvectionL hH (inner_neg_right_eq_zero hνs) (e := ν)
  obtain ⟨hG2', -⟩ := pullbackDrift_shear_memLp hνs H.isOpen.measurableSet hmapsH hG2 hT
  obtain ⟨hGp', hGle⟩ := pullbackDrift_shear_memLp hνs H.isOpen.measurableSet hmapsH hGp hT
  have h := h₀ hν hH (aestronglyMeasurable_pullbackPrincipal_shear hνs hmapsH ham) hÃ hÃinv hãÃ
    (shearCompL ν (-s) hνs u) _ (value_shearCompL_ae_eq_zero hH hνs hνs hu0)
    (fun v => by
      have h := energyFormH1_shearCompOnL_eq hνs hmapsH (mapsTo_transvectionL hH hνs) hu v
      rwa [← restrictL_shearCompOnL hνs le_top le_top (fun _ _ => trivial) hmapsH u] at h)
    hgp' hG2' hGp'
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
          MemLp (W1p.gradient u : E → E) p volume →
          MemLp G 2 (volume.restrict H) → MemLp G p (volume.restrict H) →
          eLpNorm (W1p.gradient u : E → E) p volume ≤ C * eLpNorm G p (volume.restrict H) := by
  obtain ⟨C, δ, hδ, h⟩ := exists_eLpNorm_gradient_le_of_norm_sub_le_of_isSymm (n := n) hp hp_top
    lam Lam
  refine ⟨C, δ, hδ, ?_⟩
  intro H ν c₀ a A hν hH ham hA ha u G hu0 hu hgp hG2 hGp
  set K := A - coefficientSymmetricPart A with hK
  have hcoeff := memLp_energyIntegrand_zero_zero_of_norm_le (Omega := H) (Lam := Lam + δ)
    (by linarith [hA.upper_nonneg]) ham fun x _ =>
      hA.opNorm_matrixBilinearForm_le_add (mem_univ 0) (ha x)
  have hKt : Matrix.transpose (-K) = -(-K) := by
    rw [Matrix.transpose_neg, hK, transpose_sub_coefficientSymmetricPart_eq_neg]
  refine h (a := fun x => a x + -K) hν hH (ham.add aestronglyMeasurable_const)
    hA.coefficientSymmetricPart (coefficientSymmetricPart_isSymm A) (fun y => ?_) u G hu0
    (fun v => ?_) hgp hG2 hGp
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
`∫_H ⟨a ∇u, ∇v⟩ = ∫_H ⟨G, ∇v⟩` for every `v ∈ H¹₀(H)`, with `G ∈ L²(H) ∩ Lᵖ(H)`. If `∇u` lies in
`Lᵖ`, then

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
          MemLp (W1p.gradient u : E → E) p volume →
          MemLp G 2 (volume.restrict H) → MemLp G p (volume.restrict H) →
          eLpNorm (W1p.gradient u : E → E) p volume ≤ C * eLpNorm G p (volume.restrict H) := by
  obtain ⟨C, δ, hδ, h⟩ := exists_eLpNorm_gradient_le_of_norm_sub_le (n := n) hp hp_top lam Lam
  refine ⟨C, δ, hδ, ?_⟩
  intro H ν c₀ a A s hν hH hs ham hA hsA u G hu0 hus hu hgp hG2 hGp
  classical
  -- Replace `a` by `A` off `s ∩ H`, where `∇u` vanishes.
  set b : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := (s ∩ H).piecewise a (fun _ => A) with hbdef
  refine h (a := b) hν hH
    (ham.restrict.piecewise (hs.inter H.isOpen.measurableSet).nullMeasurableSet
      aestronglyMeasurable_const) hA (fun y => ?_) u G hu0 (fun v => ?_) hgp hG2 hGp
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

/-! ### Near a flat boundary portion -/

/-- The open half-ball `B(y₀, R) ∩ H`, as an infimum of open sets, is the intersection of the ball
with `H`. -/
private theorem coe_ball_inf (y₀ : E) (R : ℝ) (H : Opens E) :
    (((⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H : Opens E) : Set E) = ball y₀ R ∩ H := by
  rw [Opens.coe_inf, Opens.coe_mk]

/-- The `W^{1,p}` estimate on a half-ball centred on the boundary hyperplane, for coefficients close
to a reflection-invariant elliptic matrix: `w ∈ H¹(B(y₀, R))` vanishes off `H` and solves the
equation in `B(y₀, R) ∩ H`, tested against `H¹₀(B(y₀, R) ∩ H)`. -/
private theorem exists_eLpNorm_gradient_ball_inter_le_of_reflection {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {H : Opens E} {ν y₀ : E} {c₀ R : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪y₀, ν⟫_ℝ = c₀ → 0 < R →
        AEStronglyMeasurable a (volume.restrict (ball y₀ R ∩ H)) →
        UniformlyEllipticOn univ (fun _ : E => A) lam Lam →
        (∀ η ξ, matrixBilinearForm A ((ℝ ∙ ν)ᗮ.reflection η) ((ℝ ∙ ν)ᗮ.reflection ξ) =
          matrixBilinearForm A η ξ) →
        (∀ x ∈ ball y₀ R, x ∈ H → ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (w : W1p volume (⟨ball y₀ R, isOpen_ball⟩ : Opens E) 2) (G : E → E),
          (∀ᵐ x ∂volume.restrict (ball y₀ R), x ∉ H → W1p.value w x = 0) →
          (∀ v : W1p0 volume ((⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H) 2,
            energyFormH1 a 0 0 (W1p.restrictL inf_le_left w)
              (v : W1p volume ((⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H) 2) =
                ∫ x in (⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H, ⟪G x, W1p.gradient
                  (v : W1p volume ((⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H) 2) x⟫_ℝ) →
          MemLp (W1p.value w) p (volume.restrict (ball y₀ R ∩ H)) →
          MemLp (W1p.gradient w) p (volume.restrict (ball y₀ R ∩ H)) →
          MemLp G p (volume.restrict (ball y₀ R ∩ H)) →
          eLpNorm (W1p.gradient w) p (volume.restrict (ball y₀ (R / 2) ∩ H)) ≤
            C * (eLpNorm G p (volume.restrict (ball y₀ R ∩ H)) +
              volume (ball y₀ R) ^ (p.toReal⁻¹ - 2⁻¹) *
                eLpNorm (W1p.gradient w) 2 (volume.restrict (ball y₀ R ∩ H))) := by
  obtain ⟨C₀, δ₀, hδ₀, hint⟩ :=
    exists_eLpNorm_gradient_ball_le_eLpNorm_two_of_setAverage_le (n := n) hp hp_top lam (Lam + 1)
  refine ⟨2 * C₀, min δ₀ 1, lt_min hδ₀ one_pos, ?_⟩
  intro H ν y₀ c₀ R a A hν hH hy₀ hR ham hA hAinv ha w G hw0 hweq hvw hgw hGp
  classical
  let B : Opens E := ⟨ball y₀ R, isOpen_ball⟩
  have hBρ : MapsTo (hyperplaneReflection ν c₀) B B := mapsTo_hyperplaneReflection_ball hy₀ R
  have : IsFiniteMeasure (volume.restrict ((B : Set E) ∩ H)) :=
    isFiniteMeasure_restrict_ball_inter volume y₀ R H
  -- The coefficient `a` on `B ∩ H` and `A` elsewhere, and its reflection.
  set a' := ((B : Set E) ∩ H).piecewise a (fun _ => A) with ha'def
  have ha'A (y : E) (_ : c₀ ≤ ⟪y, ν⟫_ℝ) :
      ‖matrixBilinearForm (a' y) - matrixBilinearForm A‖ ≤ min δ₀ 1 := by
    by_cases hy : y ∈ (B : Set E) ∩ H
    · rw [ha'def, piecewise_eq_of_mem _ _ _ hy]
      exact ha y hy.1 hy.2
    · rw [ha'def, piecewise_eq_of_notMem _ _ _ hy]
      refine ContinuousLinearMap.opNorm_le_bound₂ _ (lt_min hδ₀ one_pos).le fun η ξ => ?_
      simp only [FunLike.coe_sub, Pi.sub_apply, sub_self, zero_apply, norm_zero]
      positivity
  have hãA := norm_matrixBilinearForm_reflectPrincipal_sub_le hν hAinv ha'A
  have hãbd (x : E) : ‖matrixBilinearForm (reflectPrincipal ν c₀ a' x)‖ ≤ Lam + 1 :=
    hA.opNorm_matrixBilinearForm_le_add (mem_univ 0) ((hãA x).trans (min_le_right _ _))
  have ha'm : AEStronglyMeasurable a' volume :=
    ham.piecewise (measurableSet_ball.inter H.isOpen.measurableSet).nullMeasurableSet
      aestronglyMeasurable_const
  have hãm : AEStronglyMeasurable (reflectPrincipal ν c₀ a') volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      aestronglyMeasurable_reflectPrincipal (mu := volume) hν hH
        (mapsTo_hyperplaneReflection_top ν c₀) ha'm.restrict
  -- `w` solves the equation with the coefficient `a'`.
  have hweq' (v : W1p0 volume (B ⊓ H) 2) :
      energyFormH1 a' 0 0 (W1p.restrictL (inf_le_left : B ⊓ H ≤ B) w)
        (v : W1p volume (B ⊓ H) 2) =
          ∫ x in B ⊓ H, ⟪G x, W1p.gradient (v : W1p volume (B ⊓ H) 2) x⟫_ℝ := by
    have ha'a : a' =ᵐ[volume.restrict (B ⊓ H : Opens E)] a := by
      filter_upwards [ae_restrict_mem (B ⊓ H).isOpen.measurableSet] with x hx
      rw [ha'def]
      exact piecewise_eq_of_mem _ _ _ hx
    rw [energyFormH1_congr_ae ha'a .rfl .rfl]
    exact hweq v
  -- The odd reflection `w - w ∘ ρ` of `w` and the reflected datum.
  have hle : volume.restrict ((B : Set E) ∩ H) ≤ volume.restrict (B : Set E) :=
    Measure.restrict_mono inter_subset_left le_rfl
  obtain ⟨hwrv, hwrg, -⟩ := W1p.memLp_sub_compHyperplaneReflectionL ENNReal.ofNat_ne_top hν hH
    hBρ (one_le_two.trans hp.le) hw0 hvw hgw
  obtain ⟨-, -, hwrg2⟩ := W1p.memLp_sub_compHyperplaneReflectionL ENNReal.ofNat_ne_top hν hH hBρ
    one_le_two hw0 ((Lp.memLp (W1p.value w)).mono_measure hle)
    ((Lp.memLp (W1p.gradient w)).mono_measure hle)
  obtain ⟨hGrp, hGrle⟩ :=
    memLp_indicator_sub_indicator_linearIsometryEquiv_comp_hyperplaneReflection
      (one_le_two.trans hp.le) H.isOpen.measurableSet measurableSet_ball hBρ
      (ℝ ∙ ν)ᗮ.reflection hGp
  -- The interior estimate for the odd reflection on `B`; its coefficient is within `δ₀` of `A`.
  have hosc (c : E) (r : ℝ) (_ : 0 < r) (_ : r ≤ 4 * R) :
      ∃ A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
        UniformlyEllipticOn (ball c r) (fun _ => A') lam (Lam + 1) ∧
          ⨍ x in ball c r, ‖matrixBilinearForm (reflectPrincipal ν c₀ a' x) -
            matrixBilinearForm A'‖ ≤ δ₀ := by
    refine ⟨A, (hA.mono_set (subset_univ _)).mono_constants hA.pos le_rfl (by linarith), ?_⟩
    exact setAverage_norm_matrixBilinearForm_sub_le hδ₀.le
      (fun x => (hãA x).trans (min_le_left _ _)) c r
  have hmain := hint hãm hãbd hosc (Ω := B) (x₀ := y₀) hR le_rfl subset_rfl _ _
    (energyFormH1_reflectPrincipal_sub_compHyperplaneReflectionL_eq hν hH hBρ hãm.restrict hãbd
      hw0 hweq' (by simpa only [B, Opens.coe_mk] using hGp.mono_exponent hp.le)) hwrv hwrg hGrp
  -- On `B(y₀, R/2) ∩ H`, the gradient of the odd reflection is that of `w`.
  have hgw' : W1p.gradient w =ᵐ[volume.restrict (ball y₀ (R / 2) ∩ H)]
      W1p.gradient (w - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hBρ w) :=
    ae_restrict_of_ae_restrict_of_subset
      (inter_subset_inter_left _ (ball_subset_ball (by linarith)))
      (W1p.gradient_sub_compHyperplaneReflectionL_ae_of_value_ae_eq_zero ENNReal.ofNat_ne_top hν
        hH hBρ hw0).symm
  calc eLpNorm (W1p.gradient w) p (volume.restrict (ball y₀ (R / 2) ∩ H))
      ≤ eLpNorm (W1p.gradient (w - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hBρ w))
          p (volume.restrict (ball y₀ (R / 2))) :=
        (eLpNorm_congr_ae hgw').trans_le
          (eLpNorm_mono_measure _ (Measure.restrict_mono inter_subset_left le_rfl))
    _ ≤ C₀ * (2 * eLpNorm G p (volume.restrict (ball y₀ R ∩ H)) +
          volume (ball y₀ R) ^ (p.toReal⁻¹ - 2⁻¹) *
            (2 * eLpNorm (W1p.gradient w) 2 (volume.restrict (ball y₀ R ∩ H)))) :=
        hmain.trans (by gcongr; exact hwrg2)
    _ = _ := by
        push_cast
        ring

/-! ### Transporting a half-ball problem along the shear -/

/-- The shear `Φ = transvectionL ν (-(-s))` with `⟪ν, s⟫ = 0` and `‖Φ‖ ≤ κ` maps the ball
`B(T y₀, r / κ)` about the image of `y₀` under its inverse `T = transvectionL ν (-s)` into
`B(y₀, r)`. -/
private theorem mapsTo_transvectionL_ball_div {ν s : E} (hνs : ⟪ν, -s⟫_ℝ = 0) {κ : ℝ≥0}
    (hκ : 0 < (κ : ℝ)) (hΦ : ‖transvectionL ν (-(-s))‖ ≤ κ) (y₀ : E) (r : ℝ) :
    MapsTo (transvectionL ν (-(-s))) (ball (transvectionL ν (-s) y₀) (r / κ)) (ball y₀ r) :=
  fun x hx => by
    have h := ((transvectionL ν (-(-s))).lipschitzWith.weaken (by exact_mod_cast hΦ)).mapsTo_ball
      (by exact_mod_cast hκ.ne') (transvectionL ν (-s) y₀) (r / κ) hx
    rwa [transvectionL_neg_transvectionL hνs, mul_div_cancel₀ r hκ.ne'] at h

/-- **A half-ball problem along the shear.** Let `Φ x = x + ⟪ν, x⟫ s` with `⟪ν, s⟫ = 0` and
`‖Φ‖ ≤ κ`, with inverse `T`, and let `y₀` lie on the boundary hyperplane of `H`. If
`w ∈ H¹(B(y₀, R))` vanishes off `H` and solves `-∂ᵢ(aⁱʲ ∂ⱼw) = -div G` in `B(y₀, R) ∩ H`, then
`w ∘ Φ`, on the ball `B(T y₀, R / κ)` that `Φ` maps into `B(y₀, R)`, vanishes off `H` and solves
the transformed equation in `B(T y₀, R / κ) ∩ H`. -/
private theorem exists_shear_ball {H : Opens E} {ν y₀ s : E} {c₀ R : ℝ} {κ : ℝ≥0}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hνs : ⟪ν, -s⟫_ℝ = 0) (hκ : 0 < (κ : ℝ))
    (hΦ : ‖transvectionL ν (-(-s))‖ ≤ κ) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {G : E → E} (w : W1p volume (⟨ball y₀ R, isOpen_ball⟩ : Opens E) 2)
    (hw0 : ∀ᵐ x ∂volume.restrict (ball y₀ R), x ∉ H → W1p.value w x = 0)
    (hweq : ∀ v : W1p0 volume ((⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H) 2,
      energyFormH1 a 0 0 (W1p.restrictL inf_le_left w)
        (v : W1p volume ((⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H) 2) =
          ∫ x in (⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H, ⟪G x, W1p.gradient
            (v : W1p volume ((⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H) 2) x⟫_ℝ) :
    ∃ w₁ : W1p volume (⟨ball (transvectionL ν (-s) y₀) (R / κ), isOpen_ball⟩ : Opens E) 2,
      (∀ᵐ x ∂volume.restrict (ball (transvectionL ν (-s) y₀) (R / κ)), x ∉ H →
        W1p.value w₁ x = 0) ∧
      (∀ v : W1p0 volume
          ((⟨ball (transvectionL ν (-s) y₀) (R / κ), isOpen_ball⟩ : Opens E) ⊓ H) 2,
        energyFormH1 (pullbackPrincipal (transvectionL ν (-(-s))) a) 0 0
          (W1p.restrictL inf_le_left w₁) (v : W1p volume
            ((⟨ball (transvectionL ν (-s) y₀) (R / κ), isOpen_ball⟩ : Opens E) ⊓ H) 2) =
          ∫ x in (⟨ball (transvectionL ν (-s) y₀) (R / κ), isOpen_ball⟩ : Opens E) ⊓ H,
            ⟪pullbackDrift (transvectionL ν (-(-s))) G x, W1p.gradient (v : W1p volume
              ((⟨ball (transvectionL ν (-s) y₀) (R / κ), isOpen_ball⟩ : Opens E) ⊓ H) 2) x⟫_ℝ) ∧
      W1p.value w₁ =ᵐ[volume.restrict (ball (transvectionL ν (-s) y₀) (R / κ))]
        (fun x => W1p.value w (transvectionL ν (-(-s)) x)) ∧
      W1p.gradient w₁ =ᵐ[volume.restrict (ball (transvectionL ν (-s) y₀) (R / κ))]
        (fun x => (transvectionL ν (-(-s))).adjoint
          (W1p.gradient w (transvectionL ν (-(-s)) x))) := by
  have hHΦ := transvectionL_mem_iff (e := ν) hH (inner_neg_right_eq_zero hνs)
  -- `Φ` maps `B₁ = B(T y₀, R/κ)` into `U' = Φ⁻¹(B(y₀, R))`, which `Φ` maps onto `B(y₀, R)`.
  let B : Opens E := ⟨ball y₀ R, isOpen_ball⟩
  let U' : Opens E := ⟨transvectionL ν (-(-s)) ⁻¹' ball y₀ R,
    isOpen_ball.preimage (transvectionL ν (-(-s))).continuous⟩
  let B₁ : Opens E := ⟨ball (transvectionL ν (-s) y₀) (R / κ), isOpen_ball⟩
  have hU'B : MapsTo (transvectionL ν (-(-s))) U' B := fun x hx => by
    simpa only [U', B, Opens.coe_mk, mem_preimage] using hx
  have hB₁U' : B₁ ≤ U' := fun x hx => by
    simp only [U', B₁, Opens.mem_mk, mem_preimage] at hx ⊢
    exact mapsTo_transvectionL_ball_div hνs hκ hΦ y₀ R hx
  have hmapsH : MapsTo (transvectionL ν (-(-s))) ((U' ⊓ H : Opens E) : Set E) (B ⊓ H : Opens E) :=
    fun x hx => ⟨hU'B hx.1, (hHΦ x).2 hx.2⟩
  have hmapsH' : MapsTo (transvectionL ν (-s)) ((B ⊓ H : Opens E) : Set E) (U' ⊓ H : Opens E) :=
    fun y hy => ⟨by
      simpa only [U', B, Opens.coe_mk, mem_preimage, transvectionL_neg_transvectionL hνs]
        using hy.1,
      (transvectionL_mem_iff hH hνs y).2 hy.2⟩
  set w' := shearCompOnL ν (-s) hνs hU'B w
  refine ⟨W1p.restrictL hB₁U' w', ?_, fun v => ?_, ?_, ?_⟩
  · have hq := (measurePreserving_transvectionL volume
      (inner_neg_right_eq_zero hνs)).quasiMeasurePreserving.restrict (s := B₁) (t := ball y₀ R)
        fun x hx => hB₁U' hx
    filter_upwards [W1p.value_restrictL_ae hB₁U' w', ae_restrict_of_ae_restrict_of_subset
      (SetLike.coe_subset_coe.mpr hB₁U') (value_shearCompOnL_ae hνs hU'B w), hq.ae hw0]
      with x h1 h2 h3 hxH
    rw [h1, h2]
    exact h3 fun h => hxH ((hHΦ x).1 h)
  · -- The equation on `U' ∩ H`, restricted to `B₁ ∩ H`.
    have heq (v : W1p0 volume (U' ⊓ H) 2) := energyFormH1_shearCompOnL_eq (U := U' ⊓ H)
      (V := B ⊓ H) hνs hmapsH hmapsH' hweq v
    rw [← restrictL_shearCompOnL hνs inf_le_left inf_le_left hU'B hmapsH] at heq
    have hV : B₁ ⊓ H ≤ U' ⊓ H := inf_le_inf_right H hB₁U'
    have h := W1p0.setIntegral_gradient_restrictL_extendByZeroL hV le_rfl v
      (fun x y => ⟪pullbackDrift (transvectionL ν (-(-s))) G x, y⟫_ℝ) (fun x => inner_zero_right _)
    rw [W1p.restrictL_self, inter_eq_right.2 (SetLike.coe_subset_coe.mpr hV)] at h
    rw [W1p.restrictL_restrictL, ← W1p.restrictL_restrictL (inf_le_left : U' ⊓ H ≤ U') hV,
      energyFormH1_restrictL, heq, h]
    simp only [B₁, Opens.coe_inf]
  · filter_upwards [W1p.value_restrictL_ae hB₁U' w', ae_restrict_of_ae_restrict_of_subset
      (SetLike.coe_subset_coe.mpr hB₁U') (value_shearCompOnL_ae hνs hU'B w)] with x h1 h2
    rw [h1, h2]
  · filter_upwards [W1p.gradient_restrictL_ae hB₁U' w', ae_restrict_of_ae_restrict_of_subset
      (SetLike.coe_subset_coe.mpr hB₁U') (gradient_shearCompOnL_ae hνs hU'B w)] with x h1 h2
    rw [h1, h2]

/-- **Back along the shear.** Let `T x = x - ⟪ν, x⟫ s` with `⟪ν, s⟫ = 0` and `‖T‖ ≤ κ`, with
inverse `Φ`. If `g₁ = Φ* (g ∘ Φ)` almost everywhere on `B(T y₀, r)`, then `g = T* (g₁ ∘ T)` on
`B(y₀, r / κ) ∩ H`, which `T` maps into `B(T y₀, r) ∩ H`, so
`‖g‖_{Lᵖ(B(y₀, r / κ) ∩ H)} ≤ κ ‖g₁‖_{Lᵖ(B(T y₀, r) ∩ H)}`. -/
private theorem eLpNorm_ball_div_inter_le_of_ae_eq_adjoint {H : Opens E} {ν y₀ s : E} {c₀ r : ℝ}
    {κ : ℝ≥0} (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) (hνs : ⟪ν, -s⟫_ℝ = 0) (hκ : 0 < (κ : ℝ))
    (hT : ‖transvectionL ν (-s)‖ ≤ κ) {g g₁ : E → E}
    (hg₁ : g₁ =ᵐ[volume.restrict (ball (transvectionL ν (-s) y₀) r)]
      fun x => (transvectionL ν (-(-s))).adjoint (g (transvectionL ν (-(-s)) x))) (p : ℝ≥0∞) :
    eLpNorm g p (volume.restrict (ball y₀ (r / κ) ∩ H)) ≤
      κ * eLpNorm g₁ p (volume.restrict (ball (transvectionL ν (-s) y₀) r ∩ H)) := by
  have hmapsT : MapsTo (transvectionL ν (-s)) (ball y₀ (r / κ) ∩ H)
      (ball (transvectionL ν (-s) y₀) r ∩ H) := fun y hy =>
    ⟨by
      have h := ((transvectionL ν (-s)).lipschitzWith.weaken (by exact_mod_cast hT)).mapsTo_ball
        (by exact_mod_cast hκ.ne') y₀ (r / κ) hy.1
      rwa [mul_div_cancel₀ r hκ.ne'] at h, (transvectionL_mem_iff hH hνs y).2 hy.2⟩
  have hBm := (measurableSet_ball (x := transvectionL ν (-s) y₀) (ε := r)).inter
    H.isOpen.measurableSet
  have hTa : ‖(transvectionL ν (-s)).adjoint‖ ≤ κ := by rwa [LinearIsometryEquiv.norm_map]
  -- `g = T* (g₁ ∘ T)`, since `T* Φ* = (Φ T)* = 1`.
  have hTΦ : (transvectionL ν (-s)).adjoint ∘L (transvectionL ν (-(-s))).adjoint =
      ContinuousLinearMap.id ℝ E := by
    rw [← ContinuousLinearMap.adjoint_comp, transvectionL_neg_comp_transvectionL hνs,
      ContinuousLinearMap.adjoint_id]
  have hg : g =ᵐ[volume.restrict (ball y₀ (r / κ) ∩ H)]
      fun y => (transvectionL ν (-s)).adjoint (g₁ (transvectionL ν (-s) y)) := by
    filter_upwards [((measurePreserving_transvectionL volume hνs).quasiMeasurePreserving.restrict
      hmapsT).ae (ae_restrict_of_ae_restrict_of_subset inter_subset_left hg₁)] with y hy
    rw [hy, transvectionL_neg_transvectionL hνs, ← ContinuousLinearMap.comp_apply, hTΦ,
      ContinuousLinearMap.id_apply]
  exact (eLpNorm_congr_ae hg).trans_le ((measurePreserving_transvectionL volume hνs)
    |>.eLpNorm_clm_comp_restrict_le_of_mapsTo hBm hmapsT hTa g₁ p)

/-- The `W^{1,p}` estimate on a half-ball for coefficients close to a symmetric elliptic matrix,
obtained from the reflection-invariant case by the conormal shear: the estimate holds on the
concentric half-ball of radius `θ R`, with `θ` depending only on `λ` and `Λ`. -/
private theorem exists_eLpNorm_gradient_ball_inter_le_of_isSymm {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ θ : ℝ, 0 < δ ∧ 0 < θ ∧
      ∀ {H : Opens E} {ν y₀ : E} {c₀ R : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪y₀, ν⟫_ℝ = c₀ → 0 < R →
        AEStronglyMeasurable a (volume.restrict (ball y₀ R ∩ H)) →
        UniformlyEllipticOn univ (fun _ : E => A) lam Lam → A.IsSymm →
        (∀ x ∈ ball y₀ R, x ∈ H → ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (w : W1p volume (⟨ball y₀ R, isOpen_ball⟩ : Opens E) 2) (G : E → E),
          (∀ᵐ x ∂volume.restrict (ball y₀ R), x ∉ H → W1p.value w x = 0) →
          (∀ v : W1p0 volume ((⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H) 2,
            energyFormH1 a 0 0 (W1p.restrictL inf_le_left w)
              (v : W1p volume ((⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H) 2) =
                ∫ x in (⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H, ⟪G x, W1p.gradient
                  (v : W1p volume ((⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H) 2) x⟫_ℝ) →
          MemLp (W1p.value w) p (volume.restrict (ball y₀ R ∩ H)) →
          MemLp (W1p.gradient w) p (volume.restrict (ball y₀ R ∩ H)) →
          MemLp G p (volume.restrict (ball y₀ R ∩ H)) →
          eLpNorm (W1p.gradient w) p (volume.restrict (ball y₀ (θ * R) ∩ H)) ≤
            C * (eLpNorm G p (volume.restrict (ball y₀ R ∩ H)) +
              volume (ball y₀ R) ^ (p.toReal⁻¹ - 2⁻¹) *
                eLpNorm (W1p.gradient w) 2 (volume.restrict (ball y₀ R ∩ H))) := by
  set κ : ℝ≥0 := (1 + |Lam / lam|).toNNReal
  have hκdef : (κ : ℝ) = 1 + |Lam / lam| := Real.coe_toNNReal _ (by positivity)
  have hκ1 : (1 : ℝ) ≤ κ := by rw [hκdef]; linarith [abs_nonneg (Lam / lam)]
  have hκ : (0 : ℝ) < κ := by linarith
  obtain ⟨C₀, δ₀, hδ₀, hcore⟩ := exists_eLpNorm_gradient_ball_inter_le_of_reflection (n := n) hp
    hp_top (lam / (κ : ℝ) ^ 2) ((κ : ℝ) ^ (n + 1) * (κ : ℝ) ^ 2 * Lam)
  refine ⟨κ * C₀ * κ ^ (n + 2), δ₀ / (κ : ℝ) ^ 2, (2 * (κ : ℝ) ^ 2)⁻¹,
    div_pos hδ₀ (pow_pos hκ 2), by positivity, ?_⟩
  intro H ν y₀ c₀ R a A hν hH hy₀ hR ham hA hAs ha w G hw0 hweq hvw hgw hGp
  -- The shear `Φ x = x + ⟪ν, x⟫ s` along the conormal shear vector `s`, with inverse `T`.
  obtain ⟨hνs, hT, hΦ, hÃinv⟩ := conormalShearVector_spec hν hA hAs
  rw [← hκdef] at hT hΦ
  set s := conormalShearVector A ν
  have hΦa : ‖(transvectionL ν (-(-s))).adjoint‖ ≤ κ := by rwa [LinearIsometryEquiv.norm_map]
  have hHΦ := transvectionL_mem_iff (e := ν) hH (inner_neg_right_eq_zero hνs)
  have hy₁ : ⟪transvectionL ν (-s) y₀, ν⟫_ℝ = c₀ := by
    rw [real_inner_comm, inner_transvectionL hνs, real_inner_comm, hy₀]
  -- `Φ` maps `B(T y₀, R/κ) ∩ H` into `B(y₀, R) ∩ H`.
  have hR₁ : 0 < R / κ := div_pos hR hκ
  have hmaps : MapsTo (transvectionL ν (-(-s))) (ball (transvectionL ν (-s) y₀) (R / κ) ∩ H)
      (ball y₀ R ∩ H) := fun x hx =>
    ⟨mapsTo_transvectionL_ball_div hνs hκ hΦ y₀ R hx.1, (hHΦ x).2 hx.2⟩
  have hBm := (measurableSet_ball (x := y₀) (ε := R)).inter H.isOpen.measurableSet
  have hΦmp := measurePreserving_transvectionL volume (inner_neg_right_eq_zero hνs)
  -- The sheared problem.
  obtain ⟨w₁, hw0₁, hweq₁, hv₁, hg₁⟩ := exists_shear_ball hH hνs hκ hΦ w hw0 hweq
  have hgle (q : ℝ≥0∞) : eLpNorm (W1p.gradient w₁) q
      (volume.restrict (ball (transvectionL ν (-s) y₀) (R / κ) ∩ H)) ≤
        κ * eLpNorm (W1p.gradient w) q (volume.restrict (ball y₀ R ∩ H)) :=
    (eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset inter_subset_left hg₁)).trans_le
      (hΦmp.eLpNorm_clm_comp_restrict_le_of_mapsTo hBm hmaps hΦa _ q)
  have hvle : eLpNorm (W1p.value w₁) p
      (volume.restrict (ball (transvectionL ν (-s) y₀) (R / κ) ∩ H)) ≤
        eLpNorm (W1p.value w) p (volume.restrict (ball y₀ R ∩ H)) :=
    (eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset inter_subset_left hv₁)).trans_le
      (hΦmp.eLpNorm_comp_restrict_le_of_mapsTo hBm hmaps _ p)
  obtain ⟨hGp₁, hGle⟩ := pullbackDrift_shear_memLp hνs hBm hmaps hGp hT
  -- The reflection-invariant estimate for `w₁`, whose coefficient is within `δ₀` of the
  -- sheared matrix.
  have hclose (x : E) (hx : x ∈ ball (transvectionL ν (-s) y₀) (R / κ)) (hxH : x ∈ H) :
      ‖matrixBilinearForm (pullbackPrincipal (transvectionL ν (-(-s))) a x) -
        matrixBilinearForm (pullbackPrincipal (transvectionL ν (-(-s))) (fun _ => A) 0)‖ ≤
          δ₀ := by
    exact norm_matrixBilinearForm_pullbackPrincipal_shear_sub_le hνs hκ hT
      (ha _ (hmaps ⟨hx, hxH⟩).1 (hmaps ⟨hx, hxH⟩).2) 0
  have hmain := hcore hν hH hy₁ hR₁ (aestronglyMeasurable_pullbackPrincipal_shear hνs hmaps ham)
    (uniformlyEllipticOn_pullbackPrincipal_shear hνs hA hT hΦ) hÃinv hclose w₁ _ hw0₁ hweq₁
    (hvle.trans_lt hvw.eLpNorm_lt_top)
    ((hgle p).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hgw.eLpNorm_lt_top)) hGp₁
  -- Back along the shear, from `B(T y₀, R/(2κ))` to `B(y₀, θ R)`, `θ = 1/(2κ²)`.
  have hθR : (2 * (κ : ℝ) ^ 2)⁻¹ * R = R / κ / 2 / κ := by field_simp
  rw [hθR]
  have hlow := eLpNorm_ball_div_inter_le_of_ae_eq_adjoint hH hνs hκ hT
    (ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (half_le_self hR₁.le)) hg₁) p
  have hV := Measure.addHaar_ball_div_rpow_le volume y₀ (transvectionL ν (-s) y₀) hR hκ1
    (e := p.toReal⁻¹ - 2⁻¹) (by
      have : 0 ≤ p.toReal⁻¹ := by positivity
      linarith)
  rw [finrank_euclideanSpace_fin, ENNReal.ofReal_coe_nnreal] at hV
  have hκ1' : (1 : ℝ≥0∞) ≤ κ := by exact_mod_cast hκ1
  calc eLpNorm (W1p.gradient w) p (volume.restrict (ball y₀ (R / κ / 2 / κ) ∩ H))
      ≤ κ * (C₀ * (κ * eLpNorm G p (volume.restrict (ball y₀ R ∩ H)) +
          κ ^ (n + 1) * volume (ball y₀ R) ^ (p.toReal⁻¹ - 2⁻¹) *
            (κ * eLpNorm (W1p.gradient w) 2 (volume.restrict (ball y₀ R ∩ H))))) :=
        hlow.trans (mul_le_mul_right (hmain.trans (mul_le_mul_right
          (add_le_add hGle (mul_le_mul' hV (hgle 2))) _)) _)
    _ = κ * C₀ * (κ * eLpNorm G p (volume.restrict (ball y₀ R ∩ H)) +
          κ ^ (n + 2) * (volume (ball y₀ R) ^ (p.toReal⁻¹ - 2⁻¹) *
            eLpNorm (W1p.gradient w) 2 (volume.restrict (ball y₀ R ∩ H)))) := by ring
    _ ≤ κ * C₀ * (κ ^ (n + 2) * eLpNorm G p (volume.restrict (ball y₀ R ∩ H)) +
          κ ^ (n + 2) * (volume (ball y₀ R) ^ (p.toReal⁻¹ - 2⁻¹) *
            eLpNorm (W1p.gradient w) 2 (volume.restrict (ball y₀ R ∩ H)))) := by
        gcongr
        exact le_self_pow₀ hκ1' (by omega)
    _ = _ := by
        push_cast
        ring

/-- The `W^{1,p}` estimate on a half-ball for coefficients close to an elliptic matrix, not
necessarily symmetric: the constant antisymmetric part `K` of the matrix does not change the energy
form against `H¹₀(B(y₀, R) ∩ H)`, so subtracting it reduces the estimate to the symmetric case. -/
private theorem exists_eLpNorm_gradient_ball_inter_le {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ∞)
    (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ θ : ℝ, 0 < δ ∧ 0 < θ ∧
      ∀ {H : Opens E} {ν y₀ : E} {c₀ R : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪y₀, ν⟫_ℝ = c₀ → 0 < R →
        AEStronglyMeasurable a (volume.restrict (ball y₀ R ∩ H)) →
        UniformlyEllipticOn univ (fun _ : E => A) lam Lam →
        (∀ x ∈ ball y₀ R, x ∈ H → ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (w : W1p volume (⟨ball y₀ R, isOpen_ball⟩ : Opens E) 2) (G : E → E),
          (∀ᵐ x ∂volume.restrict (ball y₀ R), x ∉ H → W1p.value w x = 0) →
          (∀ v : W1p0 volume ((⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H) 2,
            energyFormH1 a 0 0 (W1p.restrictL inf_le_left w)
              (v : W1p volume ((⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H) 2) =
                ∫ x in (⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H, ⟪G x, W1p.gradient
                  (v : W1p volume ((⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H) 2) x⟫_ℝ) →
          MemLp (W1p.value w) p (volume.restrict (ball y₀ R ∩ H)) →
          MemLp (W1p.gradient w) p (volume.restrict (ball y₀ R ∩ H)) →
          MemLp G p (volume.restrict (ball y₀ R ∩ H)) →
          eLpNorm (W1p.gradient w) p (volume.restrict (ball y₀ (θ * R) ∩ H)) ≤
            C * (eLpNorm G p (volume.restrict (ball y₀ R ∩ H)) +
              volume (ball y₀ R) ^ (p.toReal⁻¹ - 2⁻¹) *
                eLpNorm (W1p.gradient w) 2 (volume.restrict (ball y₀ R ∩ H))) := by
  obtain ⟨C, δ, θ, hδ, hθ, h⟩ :=
    exists_eLpNorm_gradient_ball_inter_le_of_isSymm (n := n) hp hp_top lam Lam
  refine ⟨C, min δ 1, θ, lt_min hδ one_pos, hθ, ?_⟩
  intro H ν y₀ c₀ R a A hν hH hy₀ hR ham hA ha w G hw0 hweq hvw hgw hGp
  set K := A - coefficientSymmetricPart A with hK
  have hKt : Matrix.transpose (-K) = -(-K) := by
    rw [Matrix.transpose_neg, hK, transpose_sub_coefficientSymmetricPart_eq_neg]
  have hcoeff := memLp_energyIntegrand_zero_zero_of_norm_le
    (Omega := (⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H) (by linarith [hA.upper_nonneg])
    (by rwa [coe_ball_inf]) fun x hx => hA.opNorm_matrixBilinearForm_le_add (mem_univ 0)
      ((ha x hx.1 hx.2).trans (min_le_right _ _))
  refine h (a := fun x => a x + -K) hν hH hy₀ hR (ham.add aestronglyMeasurable_const)
    hA.coefficientSymmetricPart (coefficientSymmetricPart_isSymm A) (fun y hy hyH => ?_) w G hw0
    (fun v => ?_) hvw hgw hGp
  · rw [← matrixBilinearForm_sub,
      show a y + -K - coefficientSymmetricPart A = a y - A by rw [hK]; abel,
      matrixBilinearForm_sub]
    exact (ha y hy hyH).trans (min_le_left _ _)
  · rw [energyFormH1_add_const_eq_of_transpose_eq_neg (b := 0) (c := 0) hcoeff hKt, hweq v]

/-- **Extension across a flat boundary portion.** Let `Ω ∩ B(y₀, 2R) = H ∩ B(y₀, 2R)` and let
`u ∈ H¹(Ω)` vanish on the flat boundary portion `∂Ω ∩ B(y₀, 2R)`, in the sense that `χ u ∈ H¹₀(Ω)`
for every smooth `χ` compactly supported in `B(y₀, 2R)`. Then there is `w ∈ H¹(B(y₀, R))` vanishing
off `H` and agreeing with `u` on `B(y₀, R) ∩ H`. If `u` solves `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in
`Ω`, tested against test functions, with `a` bounded and `G ∈ L²` on `B(y₀, R) ∩ H`, then `w` solves
the same equation in `B(y₀, R) ∩ H`, tested against `H¹₀(B(y₀, R) ∩ H)`. -/
private theorem exists_w1p_ball_forall_energyFormH1_eq {Ω H : Opens E} {y₀ : E} {R Lam : ℝ}
    (hR : 0 < R) (hΩ : (Ω : Set E) ∩ ball y₀ (2 * R) = (H : Set E) ∩ ball y₀ (2 * R))
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hLam : 0 ≤ Lam)
    (ham : AEStronglyMeasurable a (volume.restrict (ball y₀ R ∩ H)))
    (hbd : ∀ x ∈ ball y₀ R, x ∈ H → ‖matrixBilinearForm (a x)‖ ≤ Lam)
    (u : W1p volume Ω 2) {G : E → E}
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∫ x in Ω, ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ)
    (hu0 : ∀ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      tsupport χ ⊆ ball y₀ (2 * R) → ∃ v : W1p0 volume Ω 2,
        W1p.value (v : W1p volume Ω 2) =ᵐ[volume.restrict Ω] fun x => χ x * W1p.value u x)
    (hG : MemLp G 2 (volume.restrict (ball y₀ R ∩ H))) :
    ∃ w : W1p volume (⟨ball y₀ R, isOpen_ball⟩ : Opens E) 2,
      (∀ᵐ x ∂volume.restrict (ball y₀ R), x ∉ H → W1p.value w x = 0) ∧
      (∀ v : W1p0 volume ((⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H) 2,
        energyFormH1 a 0 0 (W1p.restrictL inf_le_left w)
          (v : W1p volume ((⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H) 2) =
            ∫ x in (⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H, ⟪G x, W1p.gradient
              (v : W1p volume ((⟨ball y₀ R, isOpen_ball⟩ : Opens E) ⊓ H) 2) x⟫_ℝ) ∧
      W1p.value w =ᵐ[volume.restrict (ball y₀ R ∩ H)] W1p.value u ∧
      W1p.gradient w =ᵐ[volume.restrict (ball y₀ R ∩ H)] W1p.gradient u := by
  set B : Opens E := ⟨ball y₀ R, isOpen_ball⟩ with hB
  have hBR : ball y₀ R ⊆ ball y₀ (2 * R) := ball_subset_ball (by linarith)
  -- Inside `B(y₀, 2R)`, `Ω` and `H` agree.
  have hmem (x : E) (hx : x ∈ ball y₀ (2 * R)) : x ∈ (Ω : Set E) ↔ x ∈ (H : Set E) := by
    have h := congrArg (x ∈ ·) hΩ
    simp only [mem_inter_iff, eq_iff_iff] at h
    exact ⟨fun hxΩ => (h.1 ⟨hxΩ, hx⟩).1, fun hxH => (h.2 ⟨hxH, hx⟩).1⟩
  have hBΩ : B ⊓ H ≤ Ω := fun x hx => (hmem x (hBR hx.1)).2 hx.2
  -- `w` is the extension by zero of `ψ u`, for a cutoff `ψ` equal to one on `closedBall y₀ R`.
  -- `«E»` names the lemma's type argument, since `E` is a local notation token in this file.
  obtain ⟨c, -, hcut⟩ := exists_forall_contDiff_cutoff_ball («E» := E)
  obtain ⟨ψ, hψ, hψc, -, hψ1, hψs, -⟩ := hcut y₀ hR.le (show R < 2 * R by linarith)
  obtain ⟨ψu, hψu⟩ := hu0 ψ hψ hψc hψs
  set w : W1p volume B 2 :=
    W1p.restrictL (le_top : B ≤ ⊤) (W1p0.extendByZeroL le_top ψu : W1p volume ⊤ 2)
  have hw := W1p0.value_restrictL_extendByZeroL_ae (le_top : Ω ≤ ⊤) (le_top : B ≤ ⊤) ψu
  have hwu : W1p.restrictL (inf_le_left : B ⊓ H ≤ B) w = W1p.restrictL hBΩ u := by
    refine W1p.ext_value (Lp.ext ?_)
    filter_upwards [W1p.value_restrictL_ae (inf_le_left : B ⊓ H ≤ B) w,
      W1p.value_restrictL_ae hBΩ u,
      ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr inf_le_left) hw,
      ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hBΩ) hψu,
      ae_restrict_mem (B ⊓ H).isOpen.measurableSet] with x h1 h2 h3 h4 hx
    rw [h1, h2, h3, indicator_of_mem (hBΩ hx), h4, hψ1 (ball_subset_closedBall hx.1),
      Pi.one_apply, one_mul]
  refine ⟨w, ?_, fun v => ?_, ?_, ?_⟩
  · filter_upwards [hw, ae_restrict_mem measurableSet_ball] with x h1 hxB hxH
    rw [h1, indicator_of_notMem fun hxΩ => hxH ((hmem x (hBR hxB)).1 hxΩ)]
  · have h := forall_energyFormH1_restrictL_eq_setIntegral_sub_setIntegral_neg_inner hBΩ
      (memLp_energyIntegrand_zero_zero_of_norm_le hLam (by rwa [hB, coe_ball_inf])
        fun x hx => hbd x hx.1 hx.2) (f := 0) (fun φ => by rw [hu φ]; simp)
      (by rwa [hB, coe_ball_inf] : MemLp G 2 _) MemLp.zero v
    rw [hwu, h]
    simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub, inner_neg_left, integral_neg,
      neg_neg]
    simp only [Opens.coe_inf]
  · filter_upwards [W1p.value_restrictL_ae inf_le_left w, W1p.value_restrictL_ae hBΩ u]
      with x h1 h2
    rw [← h1, hwu, h2]
  · filter_upwards [W1p.gradient_restrictL_ae inf_le_left w, W1p.gradient_restrictL_ae hBΩ u]
      with x h1 h2
    rw [← h1, hwu, h2]

/-- **The local `W^{1,p}` estimate near a flat boundary portion.** Let `2 < p < ∞` and
`0 < λ ≤ Λ`. There are constants `C`, `δ > 0` and `θ > 0`, depending only on `n`, `p`, `λ` and
`Λ`, with the following property. Let `H = {x | c₀ < ⟪x, ν⟫}` with `ν ≠ 0`, let `y₀` lie on its
boundary hyperplane, and let `Ω` be open with `Ω ∩ B(y₀, 2R) = H ∩ B(y₀, 2R)`, so that inside
`B(y₀, 2R)` the boundary of `Ω` is flat. Let `A` be a constant matrix, uniformly elliptic with
constants `λ, Λ` and not necessarily symmetric, and let `a` be measurable on `Ω ∩ B(y₀, R)` with
bilinear form within `δ` of that of `A`, in operator norm, there. Let `u ∈ H¹(Ω)` solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in `Ω`, tested against test functions, and vanish on the flat
boundary portion: `χ u ∈ H¹₀(Ω)` for every smooth `χ` compactly supported in `B(y₀, 2R)`. If `u`,
`∇u` and `G` lie in `Lᵖ(Ω ∩ B(y₀, R))`, then

`‖∇u‖_{Lᵖ(Ω ∩ B(y₀, θR))} ≤`
`  C (‖G‖_{Lᵖ(Ω ∩ B(y₀, R))} + |B(y₀, R)|^(1/p - 1/2) ‖∇u‖_{L²(Ω ∩ B(y₀, R))})`.

Nothing is assumed about the rest of `∂Ω`, nor about `a` away from `B(y₀, R) ∩ H`. For coefficients
continuous up to the flat boundary portion, `A` can be their value at `y₀` and `R` small. This is
the boundary counterpart of the interior estimate
`TauCeti.PDE.exists_eLpNorm_gradient_ball_le_eLpNorm_two_of_setAverage_le`. -/
theorem exists_eLpNorm_gradient_inter_ball_le_eLpNorm_two_of_norm_sub_le {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ∞) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ θ : ℝ, 0 < δ ∧ 0 < θ ∧
      ∀ {Ω H : Opens E} {ν y₀ : E} {c₀ R : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
        ν ≠ 0 → (∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) → ⟪y₀, ν⟫_ℝ = c₀ → 0 < R →
        (Ω : Set E) ∩ ball y₀ (2 * R) = (H : Set E) ∩ ball y₀ (2 * R) →
        AEStronglyMeasurable a (volume.restrict ((Ω : Set E) ∩ ball y₀ R)) →
        UniformlyEllipticOn univ (fun _ : E => A) lam Lam →
        (∀ x ∈ ball y₀ R, x ∈ H → ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : W1p volume Ω 2) (G : E → E),
          (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
            ∫ x in Ω, ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ) →
          (∀ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
            tsupport χ ⊆ ball y₀ (2 * R) → ∃ v : W1p0 volume Ω 2,
              W1p.value (v : W1p volume Ω 2) =ᵐ[volume.restrict Ω]
                fun x => χ x * W1p.value u x) →
          MemLp (W1p.value u) p (volume.restrict ((Ω : Set E) ∩ ball y₀ R)) →
          MemLp (W1p.gradient u) p (volume.restrict ((Ω : Set E) ∩ ball y₀ R)) →
          MemLp G p (volume.restrict ((Ω : Set E) ∩ ball y₀ R)) →
          eLpNorm (W1p.gradient u) p (volume.restrict ((Ω : Set E) ∩ ball y₀ (θ * R))) ≤
            C * (eLpNorm G p (volume.restrict ((Ω : Set E) ∩ ball y₀ R)) +
              volume (ball y₀ R) ^ (p.toReal⁻¹ - 2⁻¹) *
                eLpNorm (W1p.gradient u) 2 (volume.restrict ((Ω : Set E) ∩ ball y₀ R))) := by
  obtain ⟨C, δ, θ, hδ, hθ, h⟩ := exists_eLpNorm_gradient_ball_inter_le (n := n) hp hp_top lam Lam
  refine ⟨C, min δ 1, min θ 1, lt_min hδ one_pos, lt_min hθ one_pos, ?_⟩
  intro Ω H ν y₀ c₀ R a A hν hH hy₀ hR hΩ ham hA ha u G hu hu0 hvp hgp hGp
  -- Inside `B(y₀, 2R)`, `Ω` is the half-space.
  have hinter {r : ℝ} (hr : r ≤ 2 * R) : (Ω : Set E) ∩ ball y₀ r = ball y₀ r ∩ H := by
    have hsub := ball_subset_ball (x := y₀) hr
    calc (Ω : Set E) ∩ ball y₀ r = (Ω : Set E) ∩ ball y₀ (2 * R) ∩ ball y₀ r := by
          rw [inter_assoc, inter_eq_right.2 hsub]
      _ = (H : Set E) ∩ ball y₀ (2 * R) ∩ ball y₀ r := by rw [hΩ]
      _ = ball y₀ r ∩ H := by rw [inter_assoc, inter_eq_right.2 hsub, inter_comm]
  rw [hinter (r := R) (by linarith)] at ham hvp hgp hGp ⊢
  rw [hinter (r := min θ 1 * R) (by nlinarith [min_le_right θ 1])]
  have := isFiniteMeasure_restrict_ball_inter volume y₀ R H
  obtain ⟨w, hw0, hweq, hwv, hwg⟩ := exists_w1p_ball_forall_energyFormH1_eq hR hΩ
    (by linarith [hA.upper_nonneg] : (0 : ℝ) ≤ Lam + 1) ham
    (fun x hx hxH =>
      hA.opNorm_matrixBilinearForm_le_add (mem_univ 0) ((ha x hx hxH).trans (min_le_right _ _)))
    u hu hu0 (hGp.mono_exponent hp.le)
  have hmain := h hν hH hy₀ hR ham hA (fun x hx hxH => (ha x hx hxH).trans (min_le_left _ _))
    w G hw0 hweq (hvp.ae_eq hwv.symm) (hgp.ae_eq hwg.symm) hGp
  rw [eLpNorm_congr_ae hwg] at hmain
  refine (eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset
    (inter_subset_inter_left _ (ball_subset_ball ?_)) hwg.symm)).trans_le
    ((eLpNorm_mono_measure _ (Measure.restrict_mono
      (inter_subset_inter_left _ (ball_subset_ball ?_)) le_rfl)).trans hmain)
  · nlinarith [min_le_right θ 1]
  · nlinarith [min_le_left θ 1]

end PDE

end TauCeti

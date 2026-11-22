/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FiniteKernel
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Exp
import TauCeti.MeasureTheory.Function.L2Space.Basic
import TauCeti.MeasureTheory.Integral.Lebesgue.Truncation

/-!
# Exponential decay of the kernel of the gauge-fixed vortex operator

Let `x` be a plane vortex, in the coordinates of `TauCeti.Vortex.equation`, with `|α| → 1` and
`∇₁ α → 0` at infinity, and let `L_x = d₀* ⊕ d₁` be its gauge-fixed operator
(`TauCeti.Vortex.gaugeFixedOperator`). The `C²` square-integrable solutions of `L_x y = 0`
(`TauCeti.Vortex.gaugeFixedKernel`) form the tangent space of the vortex moduli space. This file
proves that they decay exponentially at every rate below the vacuum mass `1 / 2`: with
`ρ(z) = √(1 + |z|²)` and `c < 1 / 2`, there is `K`, depending only on the vortex and `c`, such
that every kernel element satisfies

`‖exp(c ρ) y‖₂ ≤ K ‖y‖₂`

(`TauCeti.Vortex.exists_eLpNorm_exp_mul_smul_le_of_mem_gaugeFixedKernel`). In particular
`exp(c ρ) y` is square integrable
(`TauCeti.Vortex.memLp_exp_mul_smul_of_mem_gaugeFixedKernel`). This is the decay that the kernel
projections need in the exponentially weighted estimates for the complement inverse, whose output
estimate is `TauCeti.Vortex.exists_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq`:
for an orthonormal basis `(eᵢ)` of the finite-dimensional kernel and `c ≥ 0`, the projection
`Π f = ∑ ⟪f, eᵢ⟫ eᵢ` satisfies `‖exp(c ρ) Π f‖₂ ≤ (∑ᵢ ‖exp(c ρ) eᵢ‖₂) ‖f‖₂`, and the bound here
makes the right side finite. The projection itself is not constructed here.

The proof is an Agmon-type estimate (Agmon 1982). The exterior coercivity of `L_x`
(`TauCeti.Vortex.exists_exterior_integral_norm_sq_gaugeFixedOperator_ge`) holds at every mass
`c₁ < 1 / 2` outside a large disc of radius `R`, and since `L_x (χ y) = σ(dχ) y` for a kernel
element `y`, it gives `c₁² ∫ |χ y|² ≤ ∫ |dχ|² |y|²` for every bounded weight `χ` vanishing on the
disc (`TauCeti.Vortex.mul_integral_norm_sq_smul_le_of_mem_gaugeFixedKernel`). Take
`χ = (1 - b) V` for a cutoff `b` equal to one on the disc and vanishing beyond radius `2 R`, and
the bounded weights `V = W / (1 + ε W)`, `W = exp(c ρ)`, whose logarithmic gradient is at most
`c` (for `c ≥ 0`; negative rates follow from `c = 0`). Then `|dχ|² ≤ c² χ² + K₀`, where `K₀`
collects the terms carrying `db`, which live on the disc of radius `2 R`. Since `c < c₁`, the term
`c² χ²` is absorbed on the left, leaving a bound on `∫ V² |y|²` that is uniform in `ε`, and
Fatou's lemma (`TauCeti.lintegral_ofReal_sq_mul_le_of_forall_lintegral_div_one_add_mul_le`) lets
`ε → 0`.

The constant `K` depends only on `c` and on the radius of the exterior estimate of the vortex.
Nothing here is uniform over the noncompact moduli space of vortices.

## Main results

* `TauCeti.Vortex.exists_eLpNorm_exp_mul_smul_le_of_mem_gaugeFixedKernel`: the weighted bound on
  the kernel.
* `TauCeti.Vortex.memLp_exp_mul_smul_of_mem_gaugeFixedKernel`: kernel elements decay
  exponentially in `L²`.

## References

* S. Agmon, *Lectures on Exponential Decay of Solutions of Second-Order Elliptic Equations:
  Bounds on Eigenfunctions of N-Body Schrödinger Operators*, Mathematical Notes 29, Princeton
  University Press, 1982.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric MeasureTheory Set
open scoped ENNReal NNReal Topology

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### Pointwise bounds for the weight `(1 - b) V` -/

/-- The derivative `(1 - β) dV - V db` of the weight `(1 - b) V` at a point, where
`|dV| ≤ d V` and `|db| ≤ a`, is bounded by `d² ((1 - β) V)² + (2 d a + a²) E²`, provided
`V ≤ E` wherever `db ≠ 0`. -/
private theorem norm_sq_smul_add_smul_neg_le {F : Type*} [SeminormedAddCommGroup F]
    [NormedSpace ℝ F] {β v d a E : ℝ} {p q : F} (hβ0 : 0 ≤ 1 - β) (hβ1 : 1 - β ≤ 1)
    (hv : 0 ≤ v) (hd : 0 ≤ d) (hp : ‖p‖ ≤ d * v) (hq : ‖q‖ ≤ a) (hqE : q ≠ 0 → v ≤ E) :
    ‖(1 - β) • p + v • -q‖ ^ 2 ≤ d ^ 2 * ((1 - β) * v) ^ 2 + (2 * d * a + a ^ 2) * E ^ 2 := by
  have hp' : ‖(1 - β) • p‖ ≤ d * ((1 - β) * v) := by
    rw [norm_smul, Real.norm_of_nonneg hβ0]
    nlinarith [mul_le_mul_of_nonneg_left hp hβ0]
  have hq' : ‖v • -q‖ = v * ‖q‖ := by rw [norm_smul, norm_neg, Real.norm_of_nonneg hv]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) ((norm_add_le _ _).trans (add_le_add hp' hq'.le)) 2
  have hdχ : d * ((1 - β) * v) ≤ d * v :=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hv hβ1) hd
  have hcross : v * ‖q‖ * (2 * (d * v) + v * ‖q‖) ≤ (2 * d * a + a ^ 2) * E ^ 2 := by
    have ha : 0 ≤ a := (norm_nonneg _).trans hq
    rcases eq_or_ne q 0 with rfl | hq0
    · simp only [norm_zero, mul_zero, zero_mul]
      exact mul_nonneg (add_nonneg (mul_nonneg (mul_nonneg zero_le_two hd) ha) (sq_nonneg a))
        (sq_nonneg E)
    have hvE := hqE hq0
    have hE : 0 ≤ E := hv.trans hvE
    have hvq : v * ‖q‖ ≤ E * a := mul_le_mul hvE hq (norm_nonneg _) hE
    calc v * ‖q‖ * (2 * (d * v) + v * ‖q‖) ≤ E * a * (2 * (d * E) + E * a) :=
          mul_le_mul hvq (add_le_add (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hvE hd) zero_le_two) hvq)
            (add_nonneg (by positivity) (mul_nonneg hv (norm_nonneg _))) (mul_nonneg hE ha)
      _ = (2 * d * a + a ^ 2) * E ^ 2 := by ring
  nlinarith [mul_nonneg (mul_nonneg hv (norm_nonneg q)) (sub_nonneg.2 hdχ)]

/-- Writing `v = (1 - β) v + β v`, with `β v ≤ E`, gives `v² ≤ 2 ((1 - β) v)² + 2 E²`. -/
private theorem sq_le_two_mul_sq_add_two_mul_sq {β v E : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hv : 0 ≤ v) (hβE : β ≠ 0 → v ≤ E) (hE : 0 ≤ E) :
    v ^ 2 ≤ 2 * ((1 - β) * v) ^ 2 + 2 * E ^ 2 := by
  have hbv : β * v ≤ E := by
    rcases eq_or_ne β 0 with rfl | hβ
    · simpa using hE
    · exact (mul_le_of_le_one_left hv hβ1).trans (hβE hβ)
  have hbv2 : (β * v) ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ (mul_nonneg hβ0 hv) hbv 2
  nlinarith [sq_nonneg ((1 - β) * v - β * v)]

/-! ### The weighted estimate -/

/-- `|χ y|²` is integrable for a kernel element `y` and a continuous weight with `χ² ≤ C`. -/
private theorem integrable_norm_smul_sq_of_mem_gaugeFixedKernel {χ : ℂ → ℝ} (hχ : Continuous χ)
    {C : ℝ} (hχC : ∀ z, χ z ^ 2 ≤ C) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hyK : y ∈ gaugeFixedKernel x) : Integrable fun z ↦ ‖χ z • y z‖ ^ 2 :=
  ((mem_gaugeFixedKernel.1 hyK).2.1.integrable_sq_mul_norm_sq hχ.aestronglyMeasurable
    (ae_of_all _ hχC)).congr (ae_of_all _ fun z ↦ by
      simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs])

/-- **Agmon's absorption.** If `L_x` satisfies the exterior estimate with mass `c₁` outside the
disc of radius `R`, a kernel element `y` and a bounded `C²` weight `χ` vanishing on that disc,
with `|dχ|² ≤ d² χ² + K₀` and `d² < c₁²`, satisfy `(c₁² - d²) ∫ |χ y|² ≤ K₀ ∫ |y|²`. -/
private theorem sub_mul_integral_norm_sq_smul_le (hx : Continuous x) {c₁ R d K₀ M : ℝ}
    (hR : ∀ u : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ z, ‖z‖ ≤ R → u z = 0) → c₁ ^ 2 * (∫ z, ‖u z‖ ^ 2) ≤ ∫ z, ‖gaugeFixedOperator x u z‖ ^ 2)
    {χ : ℂ → ℝ} {χ' : ℂ → ℂ →L[ℝ] ℝ} (hχ : ContDiff ℝ 2 χ) (hχM : ∀ z, |χ z| ≤ M)
    (hχ0 : ∀ z, ‖z‖ ≤ R → χ z = 0) (hχd : ∀ z, HasFDerivAt χ (χ' z) z) (hχ'c : Continuous χ')
    (hχ' : ∀ z, ‖χ' z‖ ^ 2 ≤ d ^ 2 * χ z ^ 2 + K₀) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hyK : y ∈ gaugeFixedKernel x) :
    (c₁ ^ 2 - d ^ 2) * ∫ z, ‖χ z • y z‖ ^ 2 ≤ K₀ * ∫ z, ‖y z‖ ^ 2 := by
  have hn : Integrable fun z ↦ ‖y z‖ ^ 2 :=
    (mem_gaugeFixedKernel.1 hyK).2.1.integrable_norm_pow two_ne_zero
  have hχ2 (z : ℂ) : χ z ^ 2 ≤ M ^ 2 := sq_le_sq' (abs_le.1 (hχM z)).1 (abs_le.1 (hχM z)).2
  have hχy := integrable_norm_smul_sq_of_mem_gaugeFixedKernel hχ.continuous hχ2 hyK
  have hB : Integrable fun z ↦ ‖χ' z‖ ^ 2 * ‖y z‖ ^ 2 :=
    Integrable.mono' (hn.const_mul (d ^ 2 * M ^ 2 + K₀))
      ((hχ'c.norm.pow 2).aestronglyMeasurable.mul hn.aestronglyMeasurable)
      (.of_forall fun z ↦ by
        rw [Real.norm_of_nonneg (by positivity)]
        refine mul_le_mul_of_nonneg_right ((hχ' z).trans ?_) (sq_nonneg _)
        nlinarith [hχ2 z, sq_nonneg d])
  have hext := mul_integral_norm_sq_smul_le_of_mem_gaugeFixedKernel hx hR hχ hχM hχ0 hχd hyK hB
  have hRHS : ∫ z, ‖χ' z‖ ^ 2 * ‖y z‖ ^ 2 ≤
      d ^ 2 * (∫ z, ‖χ z • y z‖ ^ 2) + K₀ * ∫ z, ‖y z‖ ^ 2 := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hχy.const_mul _)
      (hn.const_mul _)]
    refine integral_mono hB ((hχy.const_mul _).add (hn.const_mul _)) fun z ↦ ?_
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    nlinarith [mul_le_mul_of_nonneg_right (hχ' z) (sq_nonneg ‖y z‖)]
  linarith

/-- **The absorption for the weight `(1 - b) V`.** Let `b` be a cutoff equal to one on the disc
of radius `R` of the exterior estimate (mass `c₁`), whose derivative `db` is continuous, vanishes
beyond `2 R` and satisfies `|db| ≤ a`, and let `V ≥ 0` be a bounded `C²` weight with
`|dV| ≤ d V` and `V ≤ E` on the disc of radius `2 R`. Then
`(c₁² - d²) ∫ |(1 - b) V y|² ≤ (2 d a + a²) E² ∫ |y|²` on kernel elements. -/
private theorem sub_mul_integral_norm_sq_cutoff_smul_le (hx : Continuous x) {c₁ R d a E B : ℝ}
    (hR : ∀ u : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ z, ‖z‖ ≤ R → u z = 0) → c₁ ^ 2 * (∫ z, ‖u z‖ ^ 2) ≤ ∫ z, ‖gaugeFixedOperator x u z‖ ^ 2)
    (hd : 0 ≤ d) {b : ℂ → ℝ} {b' : ℂ → ℂ →L[ℝ] ℝ} (hb : ContDiff ℝ 2 b)
    (hb01 : ∀ z, 0 ≤ b z ∧ b z ≤ 1) (hb1 : ∀ z, ‖z‖ ≤ R → b z = 1)
    (hbd : ∀ z, HasFDerivAt b (b' z) z) (hbb : ∀ z, ‖b' z‖ ≤ a) (hb'c : Continuous b')
    (hb'0 : ∀ z, 2 * R < ‖z‖ → b' z = 0) {V : ℂ → ℝ} (hV : ContDiff ℝ 2 V) (hV0 : ∀ z, 0 ≤ V z)
    (hVB : ∀ z, V z ≤ B) (hdV : ∀ z, ‖fderiv ℝ V z‖ ≤ d * V z)
    (hVE : ∀ z, ‖z‖ ≤ 2 * R → V z ≤ E) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hyK : y ∈ gaugeFixedKernel x) :
    (c₁ ^ 2 - d ^ 2) * ∫ z, ‖((1 - b z) * V z) • y z‖ ^ 2 ≤
      (2 * d * a + a ^ 2) * E ^ 2 * ∫ z, ‖y z‖ ^ 2 := by
  exact sub_mul_integral_norm_sq_smul_le (χ := fun z ↦ (1 - b z) * V z) (M := B) hx hR
    ((contDiff_const.sub hb).mul hV)
    (fun z ↦ by
      rw [abs_of_nonneg (mul_nonneg (by linarith [hb01 z]) (hV0 z))]
      exact (mul_le_of_le_one_left (hV0 z) (by linarith [hb01 z])).trans (hVB z))
    (fun z hz ↦ by simp [hb1 z hz])
    (fun z ↦ ((hbd z).const_sub 1).mul (hV.differentiable two_ne_zero z).hasFDerivAt)
    (((continuous_const.sub hb.continuous).smul (hV.continuous_fderiv two_ne_zero)).add
      (hV.continuous.smul hb'c.neg))
    (fun z ↦ norm_sq_smul_add_smul_neg_le (by linarith [hb01 z]) (by linarith [hb01 z])
      (hV0 z) hd (hdV z) (hbb z) fun hq ↦ hVE z (not_lt.1 fun hz ↦ hq (hb'0 z hz))) hyK

/-- **The estimate for a bounded weight.** Under the hypotheses of
`sub_mul_integral_norm_sq_cutoff_smul_le`, with `d < c₁`, every kernel element satisfies
`∫ V² |y|² ≤ K ∫ |y|²`, with `K` independent of the bound on `V`. -/
private theorem lintegral_ofReal_sq_mul_norm_sq_le (hx : Continuous x) {c₁ R d a E B : ℝ}
    (hR : ∀ u : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ z, ‖z‖ ≤ R → u z = 0) → c₁ ^ 2 * (∫ z, ‖u z‖ ^ 2) ≤ ∫ z, ‖gaugeFixedOperator x u z‖ ^ 2)
    (hd : 0 ≤ d) (hdc₁ : d < c₁) (hE : 0 ≤ E) {b : ℂ → ℝ} {b' : ℂ → ℂ →L[ℝ] ℝ}
    (hb : ContDiff ℝ 2 b) (hb01 : ∀ z, 0 ≤ b z ∧ b z ≤ 1) (hb1 : ∀ z, ‖z‖ ≤ R → b z = 1)
    (hb0 : ∀ z, 2 * R < ‖z‖ → b z = 0) (hbd : ∀ z, HasFDerivAt b (b' z) z)
    (hbb : ∀ z, ‖b' z‖ ≤ a) (hb'c : Continuous b') (hb'0 : ∀ z, 2 * R < ‖z‖ → b' z = 0)
    {V : ℂ → ℝ} (hV : ContDiff ℝ 2 V) (hV0 : ∀ z, 0 ≤ V z)
    (hVB : ∀ z, V z ≤ B) (hdV : ∀ z, ‖fderiv ℝ V z‖ ≤ d * V z)
    (hVE : ∀ z, ‖z‖ ≤ 2 * R → V z ≤ E) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hyK : y ∈ gaugeFixedKernel x) :
    ∫⁻ z, ENNReal.ofReal (V z ^ 2 * ‖y z‖ ^ 2) ≤ ENNReal.ofReal
      ((2 * ((2 * d * a + a ^ 2) * E ^ 2 / (c₁ ^ 2 - d ^ 2)) + 2 * E ^ 2) * ∫ z, ‖y z‖ ^ 2) := by
  have hy₂ := (mem_gaugeFixedKernel.1 hyK).2.1
  have hn : Integrable fun z ↦ ‖y z‖ ^ 2 := hy₂.integrable_norm_pow two_ne_zero
  have hgap : 0 < c₁ ^ 2 - d ^ 2 := by nlinarith
  have hχ := sub_mul_integral_norm_sq_cutoff_smul_le hx hR hd hb hb01 hb1 hbd hbb hb'c hb'0 hV
    hV0 hVB hdV hVE hyK
  have hχy := integrable_norm_smul_sq_of_mem_gaugeFixedKernel (χ := fun z ↦ (1 - b z) * V z)
    ((continuous_const.sub hb.continuous).mul hV.continuous) (fun z ↦ pow_le_pow_left₀
      (mul_nonneg (by linarith [hb01 z]) (hV0 z))
      ((mul_le_of_le_one_left (hV0 z) (by linarith [hb01 z])).trans (hVB z)) 2) hyK
  have hVy : Integrable fun z ↦ V z ^ 2 * ‖y z‖ ^ 2 :=
    hy₂.integrable_sq_mul_norm_sq hV.continuous.aestronglyMeasurable
      (ae_of_all _ fun z ↦ pow_le_pow_left₀ (hV0 z) (hVB z) 2)
  rw [← ofReal_integral_eq_lintegral_ofReal hVy (.of_forall fun z ↦ by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- `V² ≤ 2 ((1 - b) V)² + 2 E²`, since `b V ≤ E`.
  calc ∫ z, V z ^ 2 * ‖y z‖ ^ 2
      ≤ ∫ z, (2 * ‖((1 - b z) * V z) • y z‖ ^ 2 + 2 * E ^ 2 * ‖y z‖ ^ 2) :=
        integral_mono hVy ((hχy.const_mul _).add (hn.const_mul _)) fun z ↦ by
          rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
          nlinarith [mul_le_mul_of_nonneg_right (sq_le_two_mul_sq_add_two_mul_sq (hb01 z).1
            (hb01 z).2 (hV0 z) (fun hβ ↦ hVE z (not_lt.1 fun hz ↦ hβ (hb0 z hz))) hE)
            (sq_nonneg ‖y z‖)]
    _ = 2 * (∫ z, ‖((1 - b z) * V z) • y z‖ ^ 2) + 2 * E ^ 2 * ∫ z, ‖y z‖ ^ 2 := by
      rw [integral_add (hχy.const_mul _) (hn.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ 2 * ((2 * d * a + a ^ 2) * E ^ 2 * (∫ z, ‖y z‖ ^ 2) / (c₁ ^ 2 - d ^ 2)) +
          2 * E ^ 2 * ∫ z, ‖y z‖ ^ 2 := by
      gcongr
      rw [le_div_iff₀ hgap]
      linarith
    _ = _ := by ring

/-! ### Exponential decay of the kernel -/

/-- **Exponential decay of the vortex kernel, quantitatively.** Let `x` be a `C¹` plane vortex
with `|α| → 1` and `∇₁ α → 0` at infinity, let `ρ(z) = √(1 + |z|²)` and `c < 1 / 2`. There is `K`
such that every `C²` square-integrable solution `y` of `L_x y = 0` satisfies

`‖exp(c ρ) y‖₂ ≤ K ‖y‖₂`. -/
theorem exists_eLpNorm_exp_mul_smul_le_of_mem_gaugeFixedKernel (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    {c : ℝ} (hc : c < 1 / 2) :
    ∃ K : ℝ≥0, ∀ y ∈ gaugeFixedKernel x,
      eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) 2 ≤ K * eLpNorm y 2 := by
  -- Work with the rate `d = max c 0` and an exterior mass `c₁` strictly between `d` and `1 / 2`.
  set d := max c 0
  have hd0 : 0 ≤ d := le_max_right _ _
  have hd2 : d < 1 / 2 := max_lt hc (by norm_num)
  obtain ⟨R, hR0, hR⟩ := exists_exterior_integral_norm_sq_gaugeFixedOperator_ge (μ := volume)
    hx hsol hlim hcov (c := (d + 1 / 2) / 2) (by linarith) (by linarith)
  -- `b` is one on the disc of radius `R` and vanishes beyond `2 R`; the cutoff is `1 - b`.
  obtain ⟨A, hA, hcut⟩ := exists_cutoff_fderiv_bound (E := ℂ)
  obtain ⟨b, b', hb, hb01, hb1, hb0, hbd, hbb, hb'c, hb'0⟩ := hcut 0 R hR0
  set W : ℂ → ℝ := fun z ↦ Real.exp (d * √(1 + ‖z‖ ^ 2))
  set E := Real.exp (d * √(1 + (2 * R) ^ 2))
  set K := 2 * ((2 * d * (A * R⁻¹) + (A * R⁻¹) ^ 2) * E ^ 2 / (((d + 1 / 2) / 2) ^ 2 - d ^ 2)) +
    2 * E ^ 2
  have hK : 0 ≤ K := by
    have : 0 < ((d + 1 / 2) / 2) ^ 2 - d ^ 2 := by nlinarith
    positivity
  refine ⟨NNReal.mk √K (Real.sqrt_nonneg K), fun y hyK ↦ ?_⟩
  obtain ⟨hy, hy₂, -⟩ := mem_gaugeFixedKernel.1 hyK
  -- The estimate for the bounded weights `V_n = W / (1 + W / (n + 1))`, and Fatou's lemma.
  have hVn (n : ℕ) : ∫⁻ z, ENNReal.ofReal ((W z / (1 + 1 / ((n : ℝ) + 1) * W z)) ^ 2 *
      ‖y z‖ ^ 2) ≤ ENNReal.ofReal (K * ∫ z, ‖y z‖ ^ 2) := by
    have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hV0 := exp_div_one_add_mul_exp_nonneg (E := ℂ) (b := 1) d hε.le
    refine lintegral_ofReal_sq_mul_norm_sq_le hx.continuous hR hd0 (by linarith)
      (Real.exp_pos _).le (hb 2) hb01 (fun z hz ↦ hb1 z (by simpa using hz))
      (fun z hz ↦ hb0 z (by simpa using hz)) hbd hbb hb'c
      (fun z hz ↦ hb'0 z (by simpa using hz))
      (contDiff_exp_div_one_add_mul_exp d one_pos hε.le) hV0
      (exp_div_one_add_mul_exp_le_one_div d hε) (fun z ↦ ?_) (fun z hz ↦ ?_) hyK
    · refine (norm_fderiv_exp_div_one_add_mul_exp_le d one_pos hε.le z).trans ?_
      rw [abs_of_nonneg hd0]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right hd0 (norm_div_sqrt_add_norm_sq_le_one zero_le_one z)) (hV0 z)
    · exact (exp_div_one_add_mul_exp_le_exp d hε.le z).trans (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by gcongr)) hd0))
  have hWy := lintegral_ofReal_sq_mul_le_of_forall_lintegral_div_one_add_mul_le
    (contDiff_exp_mul_sqrt_add_norm_sq (n := 0) d one_pos).continuous.aemeasurable
    (hy.continuous.norm.pow 2).aemeasurable hVn
  -- The weight `exp(c ρ)` is at most `W`.
  refine (hy₂.eLpNorm_two_smul_le_of_lintegral_le
    ((contDiff_exp_mul_sqrt_add_norm_sq (n := 0) c one_pos).continuous.smul
      hy.continuous).aestronglyMeasurable hK
    ((lintegral_mono fun z ↦ ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_right (le_max_left c 0) (Real.sqrt_nonneg _))) 2)
      (sq_nonneg _))).trans hWy)).trans_eq ?_
  rw [ENNReal.ofReal_eq_coe_nnreal (Real.sqrt_nonneg K)]

/-- **Kernel elements of the vortex operator decay exponentially.** Let `x` be a `C¹` plane vortex
with `|α| → 1` and `∇₁ α → 0` at infinity, let `ρ(z) = √(1 + |z|²)` and `c < 1 / 2`. Every `C²`
square-integrable solution `y` of `L_x y = 0` has `exp(c ρ) y` square integrable. -/
theorem memLp_exp_mul_smul_of_mem_gaugeFixedKernel (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    {c : ℝ} (hc : c < 1 / 2) {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : y ∈ gaugeFixedKernel x) :
    MemLp (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) 2 := by
  obtain ⟨K, hK⟩ := exists_eLpNorm_exp_mul_smul_le_of_mem_gaugeFixedKernel hx hsol hlim hcov hc
  obtain ⟨-, hy₂, -⟩ := mem_gaugeFixedKernel.1 hy
  exact memLp_iff.2 ((hK y hy).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hy₂))

end TauCeti.Vortex

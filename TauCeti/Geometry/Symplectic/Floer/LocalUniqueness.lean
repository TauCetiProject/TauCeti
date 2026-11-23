/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.QuadraticEstimate
public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Density
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Geometry.Symplectic.Floer.Splicing
import TauCeti.MeasureTheory.Integral.Bochner.Set
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# Local uniqueness of regular Floer solutions

Let `D_u` be the linearized Floer operator (`TauCeti.SymplecticForm.floerLinearization`) along a
solution `u` of the Floer equation `F(u) = 0` on the cylinder `ℝ × S¹`, for a symplectic vector
space target `(V, ω)`. The solution is *regular* in the sense of this file when `D_u` satisfies the
injectivity estimate

`‖ξ‖²_{W^{1,2}} ≤ C ‖D_u ξ‖²_{L²}`

on `C²` sections of period one in `t` with compact support in `s`, the estimate stated in
`TauCeti.Geometry.Symplectic.Floer.Splicing`. On the Sobolev completion it says that `D_u` is
injective with closed range; for an operator of index zero it is the transversality of `u`. This
file shows that such a solution is isolated among solutions of the same equation, uniformly: there
is `ε > 0`, depending only on `C`, on a bound `B` for the slice defect `∂t u - X_{Kt}(u)` and on the
data near the graph of `u`, such that every solution `u + ξ` with `ξ` square integrable on the
cylinder and `‖ξ‖ ≤ ε` everywhere is `u` itself
(`TauCeti.SymplecticForm.exists_pos_forall_eq_zero_of_floerOperator_add_eq_zero`). This is the
local input for the discreteness of rigid moduli spaces of regular solutions, which, together with
compactness and the convergence of the ends, makes their counts finite sums.

For data that do not depend on `s`, such as those of the Floer differential, the translates of a
solution are solutions too, and `∂s u` lies in the kernel of `D_u`: the estimate then holds only
transversally to the translation direction, and the statement here applies as it stands to the
stationary cylinders. It applies to data that depend on `s`, such as continuation data, whenever
`D_u` is injective.

The proof has an abstract and a Floer-specific half.

* **No small square-integrable approximate kernel.** Let `P` be an operator on sections of the
  cylinder obeying the Leibniz rule `P (β ξ) = β P ξ + β' σ ξ` for cutoffs `β(s)`, and satisfying
  the injectivity estimate with a constant `C`. If a `C²` section `ξ` of period one in `t`, square
  integrable on the cylinder, satisfies `‖P ξ‖ ≤ ε (‖∂t ξ‖ + ‖ξ‖)` pointwise with `16 C ε² ≤ 1`,
  then `ξ = 0` (`TauCeti.Floer.eq_zero_of_forall_norm_le_of_integrableOn`). The estimate is only
  assumed for sections of compact support, and `ξ` need not have one: cut it off by `β_R(s) =
  β(s / R)` for a fixed bump `β` equal to `1` on `[-1, 1]` and vanishing off `(-2, 2)`. The
  estimate for `β_R ξ`, the smallness of `P ξ` and the Leibniz rule bound the `W^{1,2}` energy of
  `ξ` on `[-R, R] × [0, 1]` by a constant times `R⁻² ‖ξ‖²_{L²}`, since the derivative of `β_R` is of
  size `R⁻¹`. Letting `R → ∞`, the `W^{1,2}` energy of `ξ` on every compact piece of the cylinder
  vanishes. For `ε = 0` this says that a square-integrable `C²` solution of `P ξ = 0` vanishes.
* **The quadratic estimate.** If `F(u) = 0` and `F(u + ξ) = 0`, then
  `D_u ξ = -(F(u + ξ) - F(u) - D_u ξ)`, which the quadratic estimate of the namespace
  `TauCeti.SymplecticForm`,
  (`exists_pos_forall_norm_floerOperator_add_sub_floerOperator_sub_floerLinearization_le`),
  bounds by `C' (‖ξ‖² (1 + B) + ‖ξ‖ ‖∂t ξ‖) ≤ C' (1 + B) ε (‖∂t ξ‖ + ‖ξ‖)` when `‖ξ‖ ≤ ε`. For
  small `ε` the first half applies to `P = D_u`.

The data are pulled back along an arbitrary parameter map `φ : ℝ × ℝ → P`, as in the quadratic
estimate: `φ z = z.2` gives `t`-dependent data with constants uniform over the cylinder, and data
that also depend on `s` through a compact set of parameters, such as continuation data, are covered
in the same way. The threshold `ε` does not depend on `φ`, `u` or `ξ`.

## Main results

* `TauCeti.Floer.eq_zero_of_forall_norm_le_of_integrableOn`: an operator satisfying the injectivity
  estimate on compactly supported sections has no small square-integrable approximate kernel.
* `TauCeti.SymplecticForm.exists_pos_forall_eq_zero_of_floerOperator_add_eq_zero`: a regular Floer
  solution is isolated, uniformly, among the solutions that are `C⁰`-close to it with
  square-integrable difference.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Chapter 3,
  on the implicit function theorem and the local structure of moduli spaces near regular
  solutions.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), on the Fredholm theory and transversality of Floer trajectories.
-/

public section

open Set MeasureTheory ContinuousLinearMap Filter Topology

namespace TauCeti

namespace Floer

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **The weighted energy of a cut-off section.** For `η = β ξ`, the `W^{1,2}` energy density of
`ξ` weighted by `β²` is at most `2` times that of `η` plus `2 m² ‖ξ‖²`, where `|β'| ≤ m`. -/
private theorem sq_mul_sobolev_le_smul_fst {ξ : ℝ × ℝ → E} {β β' : ℝ → ℝ} {z : ℝ × ℝ}
    (hβ : HasDerivAt β (β' z.1) z.1) (hξ : DifferentiableAt ℝ ξ z) {m : ℝ} (hm : |β' z.1| ≤ m) :
    β z.1 ^ 2 * (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
        ‖ξ z‖ ^ 2) ≤
      2 * (‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineImag‖ ^ 2 + ‖β z.1 • ξ z‖ ^ 2) +
        2 * m ^ 2 * ‖ξ z‖ ^ 2 := by
  have hs := fderiv_smul_fst_apply_stdComplexLineReal hβ hξ
  have ht := fderiv_smul_fst_apply_stdComplexLineImag hβ.differentiableAt hξ
  set b := β z.1
  set b' := β' z.1
  set ds := ‖fderiv ℝ ξ z stdComplexLineReal‖
  set dη := ‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal‖
  set x := ‖ξ z‖
  have hb'2 : b' ^ 2 ≤ m ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hm 2
  -- `|b| ds ≤ ‖∂s η‖ + |b'| x`, `‖∂t η‖ = |b| ‖∂t ξ‖` and `‖η‖ = |b| x`.
  have h1 : |b| * ds ≤ dη + |b'| * x := by
    have h := norm_sub_le (fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal) (b' • ξ z)
    have he : fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal - b' • ξ z =
        b • fderiv ℝ ξ z stdComplexLineReal := by
      rw [hs, add_sub_cancel_right]
    rw [he, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at h
    exact h
  have hsq : b ^ 2 * ds ^ 2 ≤ 2 * dη ^ 2 + 2 * b' ^ 2 * x ^ 2 := by
    have h1' := pow_le_pow_left₀ (by positivity) h1 2
    rw [mul_pow, sq_abs] at h1'
    nlinarith [sq_nonneg (dη - |b'| * x), sq_abs b', norm_nonneg (ξ z)]
  rw [ht, norm_smul, norm_smul, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
  nlinarith [mul_le_mul_of_nonneg_right hb'2 (sq_nonneg x),
    sq_nonneg (b * ‖fderiv ℝ ξ z stdComplexLineImag‖), sq_nonneg (b * x)]

/-- **The operator on a cut-off section.** If `P (β ξ) = β P ξ + β' σ ξ` at `z`, with `|β'| ≤ m`
and `‖P ξ‖ ≤ ε (‖∂t ξ‖ + ‖ξ‖)`, then `‖P (β ξ)‖²` is at most `4 ε² β²` times the `W^{1,2}` energy
density of `ξ` plus `2 (m ‖σ‖)² ‖ξ‖²`. -/
private theorem norm_sq_apply_smul_fst_le {P : (ℝ × ℝ → E) → ℝ × ℝ → F} (σ : E →L[ℝ] F)
    {ξ : ℝ × ℝ → E} {β β' : ℝ → ℝ} {z : ℝ × ℝ} {m ε : ℝ} (hm : |β' z.1| ≤ m)
    (hPη : P (fun w ↦ β w.1 • ξ w) z = β z.1 • P ξ z + β' z.1 • σ (ξ z))
    (hsmall : ‖P ξ z‖ ≤ ε * (‖fderiv ℝ ξ z stdComplexLineImag‖ + ‖ξ z‖)) :
    ‖P (fun w ↦ β w.1 • ξ w) z‖ ^ 2 ≤
      4 * ε ^ 2 * (β z.1 ^ 2 * (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2)) + 2 * (m * ‖σ‖) ^ 2 * ‖ξ z‖ ^ 2 := by
  set b := β z.1
  set dt := ‖fderiv ℝ ξ z stdComplexLineImag‖
  set x := ‖ξ z‖
  -- `‖P η‖ ≤ |b| ‖P ξ‖ + m ‖σ‖ x` and `‖P ξ‖ ≤ ε (dt + x)`.
  have h1 : ‖P (fun w ↦ β w.1 • ξ w) z‖ ≤ |b| * ‖P ξ z‖ + m * ‖σ‖ * x :=
    norm_apply_smul_fst_le σ hm hPη
  have hP0 : 0 ≤ ‖P ξ z‖ := norm_nonneg _
  have h2 : b ^ 2 * ‖P ξ z‖ ^ 2 ≤ 2 * ε ^ 2 * (b ^ 2 * (dt ^ 2 + x ^ 2)) := by
    have hsq : ‖P ξ z‖ ^ 2 ≤ ε ^ 2 * (dt + x) ^ 2 :=
      (pow_le_pow_left₀ hP0 hsmall 2).trans_eq (mul_pow _ _ _)
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg b), sq_nonneg (dt - x),
      mul_nonneg (sq_nonneg b) (sq_nonneg ε), mul_nonneg (mul_nonneg (sq_nonneg b)
        (sq_nonneg ε)) (sq_nonneg (dt - x))]
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (|b| * ‖P ξ z‖ - m * ‖σ‖ * x), sq_abs b, norm_nonneg σ,
    mul_nonneg (mul_nonneg (sq_nonneg ε) (sq_nonneg b))
      (sq_nonneg ‖fderiv ℝ ξ z stdComplexLineReal‖)]

/-- **The cutoff estimate.** Let `β` be a `C²` cutoff with `|β'| ≤ m` such that `β ξ` vanishes
outside the strip `(a, b) × ℝ`. If `P` satisfies the injectivity estimate with a constant
`C ≥ 0` and `‖P ξ‖ ≤ ε (‖∂t ξ‖ + ‖ξ‖)` with `16 C ε² ≤ 1`, then the `W^{1,2}` energy of `ξ`
weighted by `β²` on `[a, b] × [0, 1]` is at most `(8 C ‖σ‖² + 4) m²` times its `L²` norm there. -/
private theorem setIntegral_sq_mul_sobolev_le {P : (ℝ × ℝ → E) → ℝ × ℝ → F} (σ : E →L[ℝ] F)
    (hP : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → ∀ ⦃β β' : ℝ → ℝ⦄, (∀ s, HasDerivAt β (β' s) s) →
      ∀ z, P (fun w ↦ β w.1 • ξ w) z = β z.1 • P ξ z + β' z.1 • σ (ξ z))
    {C ε : ℝ} (hC : 0 ≤ C)
    (hest : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖P ξ z‖ ^ 2)
    (hε : 16 * C * ε ^ 2 ≤ 1) {ξ : ℝ × ℝ → E} (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    (hsmall : ∀ z, ‖P ξ z‖ ≤ ε * (‖fderiv ℝ ξ z stdComplexLineImag‖ + ‖ξ z‖))
    {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) {m : ℝ} (hm : ∀ s, |deriv β s| ≤ m) {a b : ℝ} (hab : a ≤ b)
    (hβ₀ : ∀ s, s ∉ Ioo a b → β s = 0) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, β z.1 ^ 2 * (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
      (8 * C * ‖σ‖ ^ 2 + 4) * m ^ 2 * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2 := by
  have hβd (s : ℝ) : HasDerivAt β (deriv β s) s := (hβ.differentiable two_ne_zero s).hasDerivAt
  set η : ℝ × ℝ → E := fun w ↦ β w.1 • ξ w
  have hη : ContDiff ℝ 2 η := (hβ.comp contDiff_fst).smul hξ
  have hpt₁ (z : ℝ × ℝ) :=
    sq_mul_sobolev_le_smul_fst (hβd z.1) (hξ.differentiable two_ne_zero z) (hm z.1)
  have hpt₂ (z : ℝ × ℝ) := norm_sq_apply_smul_fst_le σ (hm z.1) (hP hξ hβd z) (hsmall z)
  have hrect : MeasurableSet (Icc a b ×ˢ Icc (0 : ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  have hξc := hξ.continuous
  have hβc := hβ.continuous
  have hsξ : Continuous fun z ↦ ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2 := by
    simpa only [funext (sobolevDensity_apply ξ)] using
      continuous_sobolevDensity (hξ.of_le one_le_two)
  have hsη : Continuous fun z ↦ ‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2 := by
    simpa only [funext (sobolevDensity_apply η)] using
      continuous_sobolevDensity (hη.of_le one_le_two)
  set I := ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, β z.1 ^ 2 * (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
    ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2)
  set L := ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2
  set S := ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
    ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2)
  have hI0 : 0 ≤ I := setIntegral_nonneg hrect fun z _ ↦ by positivity
  -- The weighted energy of `ξ` against that of `η`.
  have hIS : I ≤ 2 * S + 2 * m ^ 2 * L :=
    setIntegral_le_mul_add_mul_of_le hrect (fun z _ ↦ by positivity)
      hsη.integrableOn_Icc_prod_Icc (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))
      fun z _ ↦ hpt₁ z
  -- The injectivity estimate for `η` and the smallness of `P ξ`.
  have hSP : S ≤ C * (4 * ε ^ 2 * I + 2 * (m * ‖σ‖) ^ 2 * L) := by
    refine (hest hη (fun s t ↦ by simp only [η, hper]) hab fun s t hs ↦ by
      simp only [η, hβ₀ s hs, zero_smul]).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact setIntegral_le_mul_add_mul_of_le hrect (fun z _ ↦ sq_nonneg _)
      (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))
      (Continuous.integrableOn_Icc_prod_Icc (by fun_prop)) fun z _ ↦ hpt₂ z
  -- Absorb `8 C ε² I ≤ I / 2`.
  have hab' : 8 * C * ε ^ 2 * I ≤ I / 2 := by nlinarith
  nlinarith [mul_nonneg hC (sq_nonneg (m * ‖σ‖)), mul_nonneg (mul_nonneg hC (sq_nonneg m))
    (sq_nonneg ‖σ‖), (setIntegral_nonneg hrect fun z _ ↦ by positivity : 0 ≤ L)]

/-- **The `L²` norm on a rectangle against the cutoff scale.** Let `β` be a `C²` bump equal to `1`
on `[-1, 1]` and to `0` outside `(-2, 2)`, with `|β'| ≤ M`, and cut `ξ` off by `β(s / R)`. Under the
hypotheses of `setIntegral_sq_mul_sobolev_le`, for `0 < R₀ ≤ R` the `L²` norm of `ξ` on
`[-R₀, R₀] × [0, 1]` is at most `(8 C ‖σ‖² + 4) (M / R)²` times its `L²` norm on the cylinder. -/
private theorem setIntegral_norm_sq_le_div_sq {P : (ℝ × ℝ → E) → ℝ × ℝ → F} (σ : E →L[ℝ] F)
    (hP : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → ∀ ⦃β β' : ℝ → ℝ⦄, (∀ s, HasDerivAt β (β' s) s) →
      ∀ z, P (fun w ↦ β w.1 • ξ w) z = β z.1 • P ξ z + β' z.1 • σ (ξ z))
    {C ε : ℝ} (hC : 0 ≤ C)
    (hest : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖P ξ z‖ ^ 2)
    (hε : 16 * C * ε ^ 2 ≤ 1) {ξ : ℝ × ℝ → E} (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    (hL2 : IntegrableOn (fun z ↦ ‖ξ z‖ ^ 2) (univ ×ˢ Icc (0 : ℝ) 1))
    (hsmall : ∀ z, ‖P ξ z‖ ≤ ε * (‖fderiv ℝ ξ z stdComplexLineImag‖ + ‖ξ z‖))
    {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) (hβ1 : ∀ s, |s| ≤ 1 → β s = 1)
    (hβ0 : ∀ s, 2 ≤ |s| → β s = 0) {M : ℝ} (hM : ∀ s, |deriv β s| ≤ M) {R₀ R : ℝ} (hR₀ : 0 < R₀)
    (hR : R₀ ≤ R) :
    ∫ z in Icc (-R₀) R₀ ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2 ≤
      (8 * C * ‖σ‖ ^ 2 + 4) * (M / R) ^ 2 * ∫ z in univ ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2 := by
  have hR0 : 0 < R := hR₀.trans_le hR
  have hξc := hξ.continuous
  have hsξ : Continuous fun z ↦ ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
      ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2 := by
    simpa only [funext (sobolevDensity_apply ξ)] using
      continuous_sobolevDensity (hξ.of_le one_le_two)
  set βR : ℝ → ℝ := fun s ↦ β (s / R)
  have hβR : ContDiff ℝ 2 βR := hβ.comp (contDiff_id.div_const R)
  have hβRc := hβR.continuous
  have hmR (s : ℝ) : |deriv βR s| ≤ M / R := by
    have hd : deriv βR s = deriv β (s / R) * (1 / R) :=
      (((hβ.differentiable two_ne_zero) (s / R)).hasDerivAt.comp s
        ((hasDerivAt_id s).div_const R)).deriv
    rw [hd, abs_mul, abs_of_pos (one_div_pos.2 hR0), mul_one_div]
    exact div_le_div_of_nonneg_right (hM _) hR0.le
  have hβR₀ (s : ℝ) (hs : s ∉ Ioo (-(2 * R)) (2 * R)) : βR s = 0 := by
    refine hβ0 _ ?_
    rw [abs_div, abs_of_pos hR0, le_div_iff₀ hR0]
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hs
    rcases hs with hs | hs
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  calc ∫ z in Icc (-R₀) R₀ ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2
      ≤ ∫ z in Icc (-R₀) R₀ ×ˢ Icc (0 : ℝ) 1, βR z.1 ^ 2 *
          (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
            ‖ξ z‖ ^ 2) := by
        refine setIntegral_mono_on (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))
          (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))
          (measurableSet_Icc.prod measurableSet_Icc) fun z hz ↦ ?_
        have h1 : βR z.1 = 1 := hβ1 _ (by
          rw [abs_div, abs_of_pos hR0, div_le_one hR0, abs_le]
          exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩)
        rw [h1, one_pow, one_mul]
        nlinarith [sq_nonneg ‖fderiv ℝ ξ z stdComplexLineReal‖,
          sq_nonneg ‖fderiv ℝ ξ z stdComplexLineImag‖]
    _ ≤ ∫ z in Icc (-(2 * R)) (2 * R) ×ˢ Icc (0 : ℝ) 1, βR z.1 ^ 2 *
          (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
            ‖ξ z‖ ^ 2) :=
        setIntegral_mono_set (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))
          (Eventually.of_forall fun z ↦ by positivity)
          (prod_mono (Icc_subset_Icc (by linarith) (by linarith)) subset_rfl).eventuallySubset
    _ ≤ (8 * C * ‖σ‖ ^ 2 + 4) * (M / R) ^ 2 *
          ∫ z in Icc (-(2 * R)) (2 * R) ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2 :=
        setIntegral_sq_mul_sobolev_le σ hP hC hest hε hξ hper hsmall hβR hmR (by linarith) hβR₀
    _ ≤ _ :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set hL2
          (Eventually.of_forall fun z ↦ by positivity)
          (prod_mono (subset_univ _) subset_rfl).eventuallySubset) (by positivity)

/-- **No small square-integrable approximate kernel.** Let `P` be an operator on sections of the
cylinder obeying the Leibniz rule `P (β ξ) = β P ξ + β' σ ξ` for cutoffs `β(s)`, and satisfying the
injectivity estimate `‖ξ‖²_{W^{1,2}} ≤ C ‖P ξ‖²_{L²}` on `C²` sections of period one in `t`
vanishing outside a strip. If a `C²` section `ξ` of period one in `t`, square integrable on the
cylinder `ℝ × [0, 1]`, satisfies `‖P ξ‖ ≤ ε (‖∂t ξ‖ + ‖ξ‖)` pointwise with `16 C ε² ≤ 1`, then
`ξ = 0`. -/
theorem eq_zero_of_forall_norm_le_of_integrableOn {P : (ℝ × ℝ → E) → ℝ × ℝ → F}
    (σ : E →L[ℝ] F)
    (hP : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → ∀ ⦃β β' : ℝ → ℝ⦄, (∀ s, HasDerivAt β (β' s) s) →
      ∀ z, P (fun w ↦ β w.1 • ξ w) z = β z.1 • P ξ z + β' z.1 • σ (ξ z))
    {C ε : ℝ}
    (hest : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖P ξ z‖ ^ 2)
    (hε : 16 * C * ε ^ 2 ≤ 1) {ξ : ℝ × ℝ → E} (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    (hL2 : IntegrableOn (fun z ↦ ‖ξ z‖ ^ 2) (univ ×ˢ Icc (0 : ℝ) 1))
    (hsmall : ∀ z, ‖P ξ z‖ ≤ ε * (‖fderiv ℝ ξ z stdComplexLineImag‖ + ‖ξ z‖)) :
    ξ = 0 := by
  -- Replace `C` by `max C 0`, so that the constant is nonnegative.
  set C' := max C 0
  have hest' : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C' * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖P ξ z‖ ^ 2 :=
    fun η hη hηp a b hab hη₀ ↦ (hest hη hηp hab hη₀).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc)
        fun _ _ ↦ sq_nonneg _))
  have hε' : 16 * C' * ε ^ 2 ≤ 1 := by
    rcases le_total C 0 with h | h
    · simp [C', max_eq_right h]
    · simpa [C', max_eq_left h] using hε
  -- A smooth bump equal to `1` on `[-1, 1]` and to `0` outside `(-2, 2)`.
  let f : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨M, hM⟩ := (f.hasCompactSupport.deriv).exists_bound_of_continuous
    (f.contDiff (n := 1)).continuous_deriv_one
  have hbound (R₀ R : ℝ) (hR₀ : 0 < R₀) (hR : R₀ ≤ R) := setIntegral_norm_sq_le_div_sq σ hP
    (le_max_right _ _) hest' hε' hξ hper hL2 hsmall f.contDiff
    (fun s hs ↦ f.one_of_mem_closedBall (by simpa [Real.dist_eq] using hs))
    (fun s hs ↦ f.zero_of_le_dist (by simpa [Real.dist_eq] using hs)) (fun s ↦ hM s) hR₀ hR
  -- Letting `R → ∞`, the `L²` norm of `ξ` on every rectangle `[-R₀, R₀] × [0, 1]` vanishes.
  refine eq_zero_of_forall_setIntegral_rect_norm_sq_eq_zero hξ.continuous hper fun R₀ hR₀ ↦
    le_antisymm (ge_of_tendsto ?_ (eventually_atTop.2 ⟨R₀, fun R hR ↦ hbound R₀ R hR₀ hR⟩))
      (setIntegral_nonneg (measurableSet_Icc.prod measurableSet_Icc) fun _ _ ↦ sq_nonneg _)
  simpa using ((tendsto_const_nhds.div_atTop tendsto_id).pow 2).const_mul
    ((8 * C' * ‖σ‖ ^ 2 + 4)) |>.mul_const (∫ z in univ ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2)

end Floer

namespace SymplecticForm

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] (ω : SymplecticForm V)
  {J : P → V → V →L[ℝ] V} {Ks Kt : P → V → ℝ} {K : Set (P × V)}

/-- The arithmetic of the quadratic estimate: if `N ≤ c (x² (1 + d) + x y)` with `d ≤ B`,
`0 ≤ x ≤ ε` and `0 ≤ y`, then `N ≤ (max c 0 (1 + max B 0) + 1) ε (y + x)`. -/
private theorem norm_le_of_le_quadratic {N c x d y B ε : ℝ} (hN : N ≤ c * (x ^ 2 * (1 + d) + x * y))
    (hd : d ≤ B) (hx : 0 ≤ x) (hxε : x ≤ ε) (hy : 0 ≤ y) (hd0 : 0 ≤ d) :
    N ≤ (max c 0 * (1 + max B 0) + 1) * ε * (y + x) := by
  have hε : 0 ≤ ε := hx.trans hxε
  have hc : c ≤ max c 0 := le_max_left _ _
  have hc0 : 0 ≤ max c 0 := le_max_right _ _
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have hdB : d ≤ max B 0 := hd.trans (le_max_left _ _)
  have hinner : x ^ 2 * (1 + d) + x * y ≤ ε * ((1 + max B 0) * x + y) := by
    nlinarith [mul_le_mul_of_nonneg_left hdB (sq_nonneg x), mul_le_mul_of_nonneg_right hxε hy,
      mul_le_mul_of_nonneg_right hxε hx, mul_nonneg hε hx]
  calc N ≤ max c 0 * (ε * ((1 + max B 0) * x + y)) :=
        hN.trans ((mul_le_mul_of_nonneg_right hc (by positivity)).trans
          (mul_le_mul_of_nonneg_left hinner hc0))
    _ ≤ _ := by
        nlinarith [mul_nonneg (mul_nonneg hc0 hε) hy, mul_nonneg hε hy, mul_nonneg hε hx,
          mul_nonneg (mul_nonneg (mul_nonneg hc0 hB0) hε) hy, mul_nonneg (mul_nonneg hc0 hε) hx]

/-- The smallness condition of `Floer.eq_zero_of_forall_norm_le_of_integrableOn` for the threshold
chosen in `exists_pos_forall_eq_zero_of_floerOperator_add_eq_zero`: if `A > 0` and
`0 ≤ ε ≤ 1 / (4 A (max C 0 + 1))`, then `16 C (A ε)² ≤ 1`. -/
private theorem sixteen_mul_sq_le_one {A C ε : ℝ} (hA : 0 < A) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / (4 * A * (max C 0 + 1))) : 16 * C * (A * ε) ^ 2 ≤ 1 := by
  set C' := max C 0
  have hC' : C ≤ C' := le_max_left _ _
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hAε : A * ε ≤ 1 / (4 * (C' + 1)) :=
    calc A * ε ≤ A * (1 / (4 * A * (C' + 1))) := mul_le_mul_of_nonneg_left hε hA.le
      _ = 1 / (4 * (C' + 1)) := by field_simp
  have hsq : (A * ε) ^ 2 ≤ (1 / (4 * (C' + 1))) ^ 2 := pow_le_pow_left₀ (by positivity) hAε 2
  have key : 16 * C' * (1 / (4 * (C' + 1))) ^ 2 ≤ 1 := by
    rw [div_pow, one_pow, mul_one_div, div_le_one (by positivity)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 16 * C'),
    mul_le_mul_of_nonneg_right hC' (by positivity : (0 : ℝ) ≤ 16 * (A * ε) ^ 2)]

/-- **Local uniqueness of regular Floer solutions.** Let `K` be a compact set of pairs `(p, y)` of
a parameter and a target point at which `J` is jointly `C²` and `Ks`, `Kt` are jointly `C³`, and
let `C` and `B` be constants. There is `ε > 0` with the following property. Let `u` be a solution
of the Floer equation with data pulled back along a parameter map `φ`, whose graph `(φ z, u z)`
stays in `K`, whose slice defect `∂t u - X_{Kt}(u)` is bounded by `B`, and whose linearized operator
`D_u` satisfies the injectivity estimate `‖ξ‖²_{W^{1,2}} ≤ C ‖D_u ξ‖²_{L²}` on `C²` maps of period
one in `t` vanishing outside a strip. If `ξ` is a `C²` map of period one in `t`, square integrable
on `ℝ × [0, 1]`, with `‖ξ‖ ≤ ε` everywhere, and `u + ξ` solves the same Floer equation, then
`ξ = 0`. -/
theorem exists_pos_forall_eq_zero_of_floerOperator_add_eq_zero (hK : IsCompact K)
    (hJ : ∀ q ∈ K, ContDiffAt ℝ 2 (Function.uncurry J) q)
    (hKs : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Ks) q)
    (hKt : ∀ q ∈ K, ContDiffAt ℝ 3 (Function.uncurry Kt) q) (C B : ℝ) :
    ∃ ε > 0, ∀ (φ : ℝ × ℝ → P) (u : ℝ × ℝ → V), Differentiable ℝ u → (∀ z, (φ z, u z) ∈ K) →
      (∀ z, ‖fderiv ℝ u z stdComplexLineImag - ω.hamiltonianVectorField (Kt (φ z)) (u z)‖ ≤ B) →
      (∀ z, ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) u z = 0) →
      (∀ ⦃η : ℝ × ℝ → V⦄, ContDiff ℝ 2 η → (∀ s t, η (s, t + 1) = η (s, t)) →
        ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → η (s, t) = 0) →
          ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
              ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
            C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization (fun z ↦ J (φ z))
              (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) u η z‖ ^ 2) →
      ∀ ξ : ℝ × ℝ → V, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
        IntegrableOn (fun z ↦ ‖ξ z‖ ^ 2) (univ ×ˢ Icc (0 : ℝ) 1) → (∀ z, ‖ξ z‖ ≤ ε) →
        (∀ z, ω.floerOperator (fun z ↦ J (φ z)) (fun z ↦ Ks (φ z)) (fun z ↦ Kt (φ z)) (u + ξ) z =
          0) →
        ξ = 0 := by
  obtain ⟨δ, hδ, Cq, hq⟩ :=
    ω.exists_pos_forall_norm_floerOperator_add_sub_floerOperator_sub_floerLinearization_le
      hK hJ hKs hKt
  -- The constant `A` controls `D_u ξ` by `A ε (‖∂t ξ‖ + ‖ξ‖)`.
  set A := max Cq 0 * (1 + max B 0) + 1
  have hA : 0 < A := by positivity
  refine ⟨min δ (1 / (4 * A * (max C 0 + 1))), lt_min hδ (by positivity), fun φ u hu huK hdef hFu
    hest ξ hξ hper hL2 hξε hFuξ ↦ Floer.eq_zero_of_forall_norm_le_of_integrableOn
      (ContinuousLinearMap.id ℝ V) (fun η hη β β' hβ z ↦ ω.floerLinearization_smul_fst _ _ _ u η
        (hβ z.1) (hη.differentiable two_ne_zero z)) hest
      (sixteen_mul_sq_le_one hA (le_min hδ.le (by positivity)) (min_le_right _ _)) hξ hper hL2
      fun z ↦ ?_⟩
  -- `D_u ξ = -(F(u + ξ) - F(u) - D_u ξ)`, which the quadratic estimate bounds.
  have h := hq φ u ξ z (hu z) (hξ.differentiable two_ne_zero z) (huK z)
    ((hξε z).trans (min_le_left _ _))
  rw [hFuξ z, hFu z, sub_zero, zero_sub, norm_neg] at h
  exact norm_le_of_le_quadratic h (hdef z) (norm_nonneg _) (hξε z) (norm_nonneg _) (norm_nonneg _)

end SymplecticForm

end TauCeti

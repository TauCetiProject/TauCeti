/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization.Adjoint
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Symplectic.Floer.Sobolev.Density
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The uniform estimate for spliced operators on a long neck

Gluing two Floer cylinders `u` and `v` that meet at a nondegenerate orbit `x` along a neck of
length about `2R` produces an approximate solution `w_R` (`TauCeti.Floer.preglue`), and the
gluing theorem corrects it to an actual solution by a Newton iteration. The iteration needs a
right inverse of the linearized operator `D_{w_R}` whose norm is bounded **uniformly in `R`**.
Its analytic core is an a priori estimate for the glued operator with a constant independent of
the neck length, which this file proves from the corresponding estimates for the two pieces. On
the Sobolev completion, such an injectivity estimate for the formal adjoint of a Fredholm
operator is what makes the operator onto with a uniformly bounded right inverse.

**The abstract estimate.** Let `P`, `P₁` and `P₂` be operators sending maps `ξ : ℝ × ℝ → E` to maps
`ℝ × ℝ → F` which obey the Leibniz rule `P (β ξ) = β P ξ + β' σ ξ` for cutoffs `β(s)` depending only
on `s`, with a common symbol `σ : E →L[ℝ] F` in the `s` direction (`σ = 1` for the linearized Floer
operator `∂s + J ∂t + C`, `σ = -1` for its formal adjoint). Suppose that

* `P₁` and `P₂` satisfy the injectivity estimate `‖ξ‖²_{W^{1,2}} ≤ C ‖P_i ξ‖²_{L²}` on `C²`
  sections of period one in `t` vanishing outside a strip `(a, b) × ℝ`;
* for `t ∈ [0, 1]`, the operator `P` is `ε`-close to `P₁` where `s ≤ T`, and to `P₂` where
  `s ≥ -T`, in the sense `‖P ξ - P_i ξ‖ ≤ ε (‖∂t ξ‖ + ‖ξ‖)` pointwise;
* the neck is long and the comparison is good: `64 C ‖σ‖² ≤ T²` and `8 C ε² ≤ 1`.

Then `‖ξ‖²_{W^{1,2}} ≤ 64 C ‖P ξ‖²_{L²}` for every such section
(`TauCeti.Floer.setIntegral_sobolev_le_mul_setIntegral_of_splice`). The constant does not depend on
`T` or `ε`: this is the uniformity in the neck length. The proof cuts `ξ` into `β ξ` and
`(1 - β) ξ` with a cutoff `β` dropping from `1` to `0` across the neck `[-T, T]` at slope `1 / T`
(`TauCeti.exists_contDiff_antitone_cutoff_abs_deriv_le`). The first piece lives where `P` is
close to `P₁` and the second where it is close to `P₂`; the comparison errors are absorbed by the
estimates of the pieces, and the cutoff errors `β' σ ξ`, of size `‖σ‖ / T`, by the left-hand side.

**The linearized Floer operator.** For the linearized Floer operators
`D ξ = ∂s ξ + J(z, u z) ∂t ξ + C(z) ξ` (`TauCeti.SymplecticForm.floerLinearization`) of three data
sets, the pointwise closeness follows from closeness of the coefficients `J(z, u z)` and
`C(z) = floerLinearizationCoeff` on the two halves of the fundamental domain
(`TauCeti.SymplecticForm.setIntegral_sobolev_le_mul_setIntegral_floerLinearization_of_splice`). The
pieces of a glued map are translates of the two cylinders. Translating the data translates the
operator (`TauCeti.SymplecticForm.floerLinearization_comp_add_right`), and the injectivity
estimate is invariant under translation in `s`
(`TauCeti.SymplecticForm.setIntegral_sobolev_le_mul_setIntegral_floerLinearization_comp_add_right`).

**The formal adjoint.** For `s`-independent data the linearized operator along a nonstationary
trajectory has `∂s u` in its kernel, so the estimate that gluing trajectories uses is the one for
the formal adjoint `D^* η = -(∂s η + (∂t η) ∘ J(z, u z) + η ∘ A(z))`, with `A = ∂t J - C`
(`TauCeti.SymplecticForm.floerLinearizationAdjoint_eq_neg`), on covector fields. Its symbol in the
`s` direction is `σ = -1`, and the same statements hold: the spliced estimate follows from
closeness of `J(z, u z)` and `A(z)` (`TauCeti.SymplecticForm.`
`setIntegral_sobolev_le_mul_setIntegral_floerLinearizationAdjoint_of_splice`).
Translation invariance holds for any operator that commutes with translations in `s`
(`TauCeti.Floer.setIntegral_sobolev_le_mul_setIntegral_of_comp_add_right`), as the adjoint does
(`TauCeti.SymplecticForm.floerLinearizationAdjoint_comp_add_right`).

Sections are `C²` maps `ξ : ℝ × ℝ → E` of period one in `t` that vanish outside a strip
`(a, b) × ℝ`, and the integrals are over the fundamental domain `[a, b] × [0, 1]`, as in
`TauCeti.Geometry.Symplectic.Floer.SemiFredholm`. The Sobolev completion, the Fredholm property
and the construction of the right inverse are not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Chapter 10,
  on the uniformly bounded right inverses of glued Cauchy–Riemann operators.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), on gluing Floer trajectories.
-/

public section

open Set MeasureTheory ContinuousLinearMap

namespace TauCeti

namespace Floer

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- **Absorbing a comparison error.** If the `W^{1,2}` energy of `η` is controlled by the `L²` norm
of `g`, and `g` differs from `f` pointwise by at most `ε (‖∂t η‖ + ‖η‖)` with `8 C ε² ≤ 1`, then
the `W^{1,2}` energy of `η` is controlled by the `L²` norm of `f`, with the constant `4 C`. -/
private theorem setIntegral_sobolev_le_of_norm_le_add {η : ℝ × ℝ → E} (hη : ContDiff ℝ 1 η)
    {f g : ℝ × ℝ → F} (hf : Continuous f) (hg : Continuous g) {C ε a b : ℝ} (hC : 0 ≤ C)
    (hε : 8 * C * ε ^ 2 ≤ 1)
    (hest : ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
      C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖g z‖ ^ 2)
    (hle : ∀ z ∈ Icc a b ×ˢ Icc (0 : ℝ) 1,
      ‖g z‖ ≤ ‖f z‖ + ε * (‖fderiv ℝ η z stdComplexLineImag‖ + ‖η z‖)) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
      4 * C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖f z‖ ^ 2 := by
  set W := ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
    ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2)
  have hrect : MeasurableSet (Icc a b ×ˢ Icc (0 : ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  have hW : 0 ≤ W := setIntegral_nonneg hrect fun z _ ↦ by positivity
  have := hη.continuous_fderiv one_ne_zero
  have := hη.continuous
  -- Pointwise, `‖g‖² ≤ 2 ‖f‖² + 4 ε² (‖∂t η‖² + ‖η‖²)`.
  have hpt (z : ℝ × ℝ) (hz : z ∈ Icc a b ×ˢ Icc (0 : ℝ) 1) : ‖g z‖ ^ 2 ≤ 2 * ‖f z‖ ^ 2 +
      4 * ε ^ 2 * (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) := by
    have h := hle z hz
    have h0 := norm_nonneg (g z)
    nlinarith [sq_nonneg (‖f z‖ - ε * (‖fderiv ℝ η z stdComplexLineImag‖ + ‖η z‖)),
      sq_nonneg (‖fderiv ℝ η z stdComplexLineImag‖ - ‖η z‖),
      mul_nonneg (sq_nonneg ε) (sq_nonneg ‖fderiv ℝ η z stdComplexLineReal‖)]
  have hint : ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖g z‖ ^ 2 ≤
      2 * (∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖f z‖ ^ 2) + 4 * ε ^ 2 * W := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))
        ((continuous_sobolev hη).const_mul _).integrableOn_Icc_prod_Icc]
    exact setIntegral_mono_on (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))
      ((Continuous.integrableOn_Icc_prod_Icc (by fun_prop)).add
        ((continuous_sobolev hη).const_mul _).integrableOn_Icc_prod_Icc) hrect hpt
  nlinarith [mul_le_mul_of_nonneg_left hint hC, mul_le_mul_of_nonneg_right hε hW]

/-- **The `L²` norm of `P` on a cut-off section.** If `P (β ξ) = β P ξ + β' σ ξ` for cutoffs
`β(s)`, then for `|β| ≤ 1` and `|β'| ≤ M` the `L²` norm of `P (β ξ)` is bounded by those of `P ξ`
and of `ξ`. -/
private theorem setIntegral_norm_sq_smul_fst_le {P : (ℝ × ℝ → E) → ℝ × ℝ → F} (σ : E →L[ℝ] F)
    (hPc : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → Continuous (P ξ))
    (hP : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → ∀ ⦃β β' : ℝ → ℝ⦄, (∀ s, HasDerivAt β (β' s) s) →
      ∀ z, P (fun w ↦ β w.1 • ξ w) z = β z.1 • P ξ z + β' z.1 • σ (ξ z))
    {ξ : ℝ × ℝ → E} (hξ : ContDiff ℝ 2 ξ) {β : ℝ → ℝ} (hβc : ContDiff ℝ 2 β)
    (hβ₁ : ∀ s, |β s| ≤ 1) {M : ℝ} (hM : ∀ s, |deriv β s| ≤ M) (a b : ℝ) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖P (fun w ↦ β w.1 • ξ w) z‖ ^ 2 ≤
      2 * (∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖P ξ z‖ ^ 2) +
        2 * (M * ‖σ‖) ^ 2 * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2 := by
  have hβd (s : ℝ) : HasDerivAt β (deriv β s) s := (hβc.differentiable two_ne_zero s).hasDerivAt
  have hβξ : ContDiff ℝ 2 fun w : ℝ × ℝ ↦ β w.1 • ξ w := (hβc.comp contDiff_fst).smul hξ
  have hPξ := hPc hξ
  have hξc := hξ.continuous
  have hrect : MeasurableSet (Icc a b ×ˢ Icc (0 : ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  -- Pointwise, `‖β P ξ + β' σ ξ‖ ≤ ‖P ξ‖ + M ‖σ‖ ‖ξ‖`.
  have hpt (z : ℝ × ℝ) : ‖P (fun w ↦ β w.1 • ξ w) z‖ ^ 2 ≤
      2 * ‖P ξ z‖ ^ 2 + 2 * (M * ‖σ‖) ^ 2 * ‖ξ z‖ ^ 2 := by
    have h : ‖P (fun w ↦ β w.1 • ξ w) z‖ ≤ ‖P ξ z‖ + M * ‖σ‖ * ‖ξ z‖ := by
      rw [hP hξ hβd z]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hβ₁ z.1)
      · rw [norm_smul, Real.norm_eq_abs, mul_assoc]
        exact mul_le_mul (hM z.1) (σ.le_opNorm _) (norm_nonneg _)
          ((abs_nonneg _).trans (hM z.1))
    nlinarith [norm_nonneg (P (fun w ↦ β w.1 • ξ w) z),
      sq_nonneg (‖P ξ z‖ - M * ‖σ‖ * ‖ξ z‖)]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))
      (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))]
  exact setIntegral_mono_on (Continuous.integrableOn_Icc_prod_Icc (by have := hPc hβξ; fun_prop))
    ((Continuous.integrableOn_Icc_prod_Icc (by fun_prop)).add
      (Continuous.integrableOn_Icc_prod_Icc (by fun_prop))) hrect
    fun z _ ↦ by simpa [mul_pow] using hpt z

/-- **The estimate for one cut-off piece.** Let `β(s)` be a cutoff with `|β| ≤ 1` and `|β'| ≤ M`,
which vanishes with its derivative off a set `U` of `s` on which `P` is `ε`-close to `P₁` for
`t ∈ [0, 1]`. If `P₁`
satisfies the injectivity estimate with constant `C`, and `8 C ε² ≤ 1`, then the `W^{1,2}` energy of
`β ξ` is at most `4 C (2 ‖P ξ‖² + 2 (M ‖σ‖)² ‖ξ‖²)`, the norms being `L²` norms over the
rectangle. -/
private theorem setIntegral_sobolev_smul_fst_le {P P₁ : (ℝ × ℝ → E) → ℝ × ℝ → F}
    (σ : E →L[ℝ] F) {C ε M : ℝ} (hC : 0 ≤ C) (hε : 8 * C * ε ^ 2 ≤ 1)
    (hPc : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → Continuous (P ξ))
    (hP₁c : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → Continuous (P₁ ξ))
    (hP : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → ∀ ⦃β β' : ℝ → ℝ⦄, (∀ s, HasDerivAt β (β' s) s) →
      ∀ z, P (fun w ↦ β w.1 • ξ w) z = β z.1 • P ξ z + β' z.1 • σ (ξ z))
    (hP₁ : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → ∀ ⦃β β' : ℝ → ℝ⦄, (∀ s, HasDerivAt β (β' s) s) →
      ∀ z, P₁ (fun w ↦ β w.1 • ξ w) z = β z.1 • P₁ ξ z + β' z.1 • σ (ξ z))
    {U : Set ℝ} (hclose : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → ∀ z, z.1 ∈ U →
      z.2 ∈ Icc (0 : ℝ) 1 → ‖P ξ z - P₁ ξ z‖ ≤ ε * (‖fderiv ℝ ξ z stdComplexLineImag‖ + ‖ξ z‖))
    (hest : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖P₁ ξ z‖ ^ 2)
    {ξ : ℝ × ℝ → E} (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) {a b : ℝ}
    (hab : a ≤ b) (hξ₀ : ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) {β : ℝ → ℝ} (hβc : ContDiff ℝ 2 β)
    (hβ₁ : ∀ s, |β s| ≤ 1) (hM : ∀ s, |deriv β s| ≤ M) (hβU : ∀ s, s ∉ U → β s = 0)
    (hβ'U : ∀ s, s ∉ U → deriv β s = 0) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
        (‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineImag‖ ^ 2 + ‖β z.1 • ξ z‖ ^ 2) ≤
      4 * C * (2 * (∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖P ξ z‖ ^ 2) +
        2 * (M * ‖σ‖) ^ 2 * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) := by
  have hβd (s : ℝ) : HasDerivAt β (deriv β s) s := (hβc.differentiable two_ne_zero s).hasDerivAt
  set η : ℝ × ℝ → E := fun w ↦ β w.1 • ξ w
  have hη : ContDiff ℝ 2 η := (hβc.comp contDiff_fst).smul hξ
  -- Off `U` both operators vanish on `β ξ`; on `U` they are `ε`-close.
  have hle (z : ℝ × ℝ) (hzr : z ∈ Icc a b ×ˢ Icc (0 : ℝ) 1) :
      ‖P₁ η z‖ ≤ ‖P η z‖ + ε * (‖fderiv ℝ η z stdComplexLineImag‖ + ‖η z‖) := by
    by_cases hz : z.1 ∈ U
    · calc ‖P₁ η z‖ ≤ ‖P η z‖ + ‖P η z - P₁ η z‖ := by
            simpa [norm_sub_rev] using norm_le_insert' (P₁ η z) (P η z)
        _ ≤ _ := by gcongr; exact hclose hη z hz hzr.2
    · have h0 : P₁ η z = 0 := by
        simp [η, hP₁ hξ hβd z, hβU _ hz, hβ'U _ hz]
      rw [h0, norm_zero]
      have hη0 : η z = 0 := by simp [η, hβU _ hz]
      have hηd : fderiv ℝ η z stdComplexLineImag = 0 := by
        have hd : HasFDerivAt η _ z := ((hβd z.1).hasFDerivAt.comp z hasFDerivAt_fst).smul
          ((hξ.differentiable two_ne_zero) z).hasFDerivAt
        rw [hd.fderiv]
        simp [hβU _ hz, hβ'U _ hz]
      simp [hη0, hηd]
  have hηper (s t : ℝ) : η (s, t + 1) = η (s, t) := by simp only [η, hper]
  have hη₀ (s t : ℝ) (hs : s ∉ Ioo a b) : η (s, t) = 0 := by simp only [η, hξ₀ s t hs, smul_zero]
  calc _ ≤ 4 * C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖P η z‖ ^ 2 :=
        setIntegral_sobolev_le_of_norm_le_add (hη.of_le one_le_two) (hPc hη) (hP₁c hη) hC hε
          (hest hη hηper hab hη₀) hle
    _ ≤ _ := by
        gcongr
        exact setIntegral_norm_sq_smul_fst_le σ hPc hP hξ hβc hβ₁ hM a b

/-- **A cutoff across the neck.** For `T > 0` there is a `C²` cutoff `β` with `0 ≤ β ≤ 1`, equal to
`1` for `s ≤ -T` and to `0` for `s ≥ T`, whose derivative is at most `1 / T` and vanishes outside
`(-T, T)`. -/
private theorem exists_neck_cutoff {T : ℝ} (hT : 0 < T) :
    ∃ β : ℝ → ℝ, ContDiff ℝ 2 β ∧ (∀ s, 0 ≤ β s) ∧ (∀ s, β s ≤ 1) ∧ (∀ s, T ≤ s → β s = 0) ∧
      (∀ s ≤ -T, β s = 1) ∧ (∀ s, |deriv β s| ≤ 1 / T) ∧ ∀ s ∉ Ioo (-T) T, deriv β s = 0 := by
  obtain ⟨β, hβc, hβa, hβ0, hβT, hβm, hβ', hβ'0⟩ :=
    exists_contDiff_antitone_cutoff_abs_deriv_le (a := -T) (b := T) (v := 1) (τ := 1 / T)
      (by linarith) zero_le_one (by field_simp; linarith)
  refine ⟨β, hβc.of_le (by simp), hβ0, fun s ↦ ?_, hβT, hβm, hβ', hβ'0⟩
  rcases le_total s (-T) with hs | hs
  · exact (hβm s hs).le
  · exact (hβa hs).trans (hβm _ le_rfl).le

/-- **Splitting the energy with a cutoff.** For a `C²` cutoff `β(s)`, the `W^{1,2}` energy of a
`C²` map `ξ` over a rectangle is at most twice the sum of the energies of `β ξ` and `(1 - β) ξ`. -/
private theorem setIntegral_sobolev_le_add_of_cutoff {ξ : ℝ × ℝ → E} (hξ : ContDiff ℝ 2 ξ)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ 2 β) (a b : ℝ) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
      2 * (∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
        (‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineImag‖ ^ 2 + ‖β z.1 • ξ z‖ ^ 2)) +
      2 * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
        (‖fderiv ℝ (fun w ↦ (1 - β w.1) • ξ w) z stdComplexLineReal‖ ^ 2 +
          ‖fderiv ℝ (fun w ↦ (1 - β w.1) • ξ w) z stdComplexLineImag‖ ^ 2 +
            ‖(1 - β z.1) • ξ z‖ ^ 2) := by
  have hξ₁ : ContDiff ℝ 2 fun w : ℝ × ℝ ↦ β w.1 • ξ w := (hβ.comp contDiff_fst).smul hξ
  have hξ₂ : ContDiff ℝ 2 fun w : ℝ × ℝ ↦ (1 - β w.1) • ξ w :=
    ((contDiff_const.sub hβ).comp contDiff_fst).smul hξ
  have hsum : ξ = (fun w ↦ β w.1 • ξ w) + fun w ↦ (1 - β w.1) • ξ w :=
    funext fun w ↦ by simp [← add_smul]
  have hi₁ := ((continuous_sobolev (hξ₁.of_le one_le_two)).integrableOn_Icc_prod_Icc
    (a₁ := a) (b₁ := b) (a₂ := 0) (b₂ := 1)).const_mul 2
  have hi₂ := ((continuous_sobolev (hξ₂.of_le one_le_two)).integrableOn_Icc_prod_Icc
    (a₁ := a) (b₁ := b) (a₂ := 0) (b₂ := 1)).const_mul 2
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add hi₁ hi₂]
  refine setIntegral_mono_on (continuous_sobolev (hξ.of_le one_le_two)).integrableOn_Icc_prod_Icc
    (hi₁.add hi₂) (measurableSet_Icc.prod measurableSet_Icc) fun z _ ↦ ?_
  have h := sobolev_add_le (hξ₁.differentiable two_ne_zero z) (hξ₂.differentiable two_ne_zero z)
  rwa [← hsum] at h

/-- **The uniform estimate for a spliced operator.** Let `P`, `P₁` and `P₂` be operators on maps
`ℝ × ℝ → E` with the Leibniz rule `P (β ξ) = β P ξ + β' σ ξ` for cutoffs `β(s)`, sending `C²` maps
to continuous maps. Suppose that `P₁` and `P₂` satisfy the injectivity estimate
`‖ξ‖²_{W^{1,2}} ≤ C ‖P_i ξ‖²_{L²}` on `C²` maps of period one in `t` vanishing outside a strip
`(a, b) × ℝ`, that for `t ∈ [0, 1]` the operator `P` is `ε`-close to `P₁` where `s ≤ T` and to
`P₂` where `s ≥ -T`, and that `64 C ‖σ‖² ≤ T²` and `8 C ε² ≤ 1`. Then `P` satisfies the
injectivity estimate with the constant `64 C`, independent of `T` and `ε`. The norms are over the
rectangle `[a, b] × [0, 1]`. -/
theorem setIntegral_sobolev_le_mul_setIntegral_of_splice {P P₁ P₂ : (ℝ × ℝ → E) → ℝ × ℝ → F}
    (σ : E →L[ℝ] F) {C ε T : ℝ} (hC : 0 ≤ C) (hT : 0 < T) (hσ : 64 * C * ‖σ‖ ^ 2 ≤ T ^ 2)
    (hε : 8 * C * ε ^ 2 ≤ 1)
    (hPc : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → Continuous (P ξ))
    (hP₁c : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → Continuous (P₁ ξ))
    (hP₂c : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → Continuous (P₂ ξ))
    (hP : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → ∀ ⦃β β' : ℝ → ℝ⦄, (∀ s, HasDerivAt β (β' s) s) →
      ∀ z, P (fun w ↦ β w.1 • ξ w) z = β z.1 • P ξ z + β' z.1 • σ (ξ z))
    (hP₁ : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → ∀ ⦃β β' : ℝ → ℝ⦄, (∀ s, HasDerivAt β (β' s) s) →
      ∀ z, P₁ (fun w ↦ β w.1 • ξ w) z = β z.1 • P₁ ξ z + β' z.1 • σ (ξ z))
    (hP₂ : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → ∀ ⦃β β' : ℝ → ℝ⦄, (∀ s, HasDerivAt β (β' s) s) →
      ∀ z, P₂ (fun w ↦ β w.1 • ξ w) z = β z.1 • P₂ ξ z + β' z.1 • σ (ξ z))
    (hclose₁ : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → ∀ z, z.1 ≤ T → z.2 ∈ Icc (0 : ℝ) 1 →
      ‖P ξ z - P₁ ξ z‖ ≤ ε * (‖fderiv ℝ ξ z stdComplexLineImag‖ + ‖ξ z‖))
    (hclose₂ : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → ∀ z, -T ≤ z.1 → z.2 ∈ Icc (0 : ℝ) 1 →
      ‖P ξ z - P₂ ξ z‖ ≤ ε * (‖fderiv ℝ ξ z stdComplexLineImag‖ + ‖ξ z‖))
    (hest₁ : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖P₁ ξ z‖ ^ 2)
    (hest₂ : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖P₂ ξ z‖ ^ 2)
    {ξ : ℝ × ℝ → E} (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) {a b : ℝ}
    (hab : a ≤ b) (hξ₀ : ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
      64 * C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖P ξ z‖ ^ 2 := by
  -- A cutoff `β` dropping from `1` to `0` across the neck `[-T, T]` at slope at most `1 / T`,
  -- and the complementary cutoff `1 - β`.
  obtain ⟨β, hβc, hβ0, hβ1, hβT, hβm, hβ', hβ'0⟩ := exists_neck_cutoff hT
  have hγd (s : ℝ) : HasDerivAt (fun s ↦ 1 - β s) (-deriv β s) s := by
    simpa using ((hβc.differentiable two_ne_zero s).hasDerivAt).const_sub 1
  -- The piece `β ξ` lives where `P` is close to `P₁`, and `(1 - β) ξ` where it is close to `P₂`.
  have h₁ := setIntegral_sobolev_smul_fst_le σ hC hε hPc hP₁c hP hP₁ (U := Iic T)
    (fun η hη z hz ht ↦ hclose₁ hη z hz ht) hest₁ hξ hper hab hξ₀ hβc
    (fun s ↦ abs_le.2 ⟨by linarith [hβ0 s], hβ1 s⟩) hβ'
    (fun s hs ↦ hβT s (le_of_lt (not_le.1 hs))) (fun s hs ↦ hβ'0 s fun h ↦ hs (le_of_lt h.2))
  have h₂ := setIntegral_sobolev_smul_fst_le σ hC hε hPc hP₂c hP hP₂ (U := Ici (-T))
    (fun η hη z hz ht ↦ hclose₂ hη z hz ht) hest₂ hξ hper hab hξ₀ (contDiff_const.sub hβc)
    (fun s ↦ (abs_le.2 ⟨by linarith [hβ1 s], by linarith [hβ0 s]⟩ : |1 - β s| ≤ 1))
    (fun s ↦ by rw [(hγd s).deriv, abs_neg]; exact hβ' s)
    (fun s hs ↦ by rw [hβm s (le_of_lt (not_le.1 hs)), sub_self])
    (fun s hs ↦ by rw [(hγd s).deriv, hβ'0 s fun h ↦ hs (le_of_lt h.1), neg_zero])
  have hsplit := setIntegral_sobolev_le_add_of_cutoff hξ hβc a b
  have hL := setIntegral_norm_sq_le_sobolev (hξ.of_le one_le_two) a b
  -- The cutoff error `32 C (‖σ‖ / T)²` is at most `1 / 2`, and is absorbed.
  have hk : 64 * C * (1 / T * ‖σ‖) ^ 2 ≤ 1 := by
    rw [show 64 * C * (1 / T * ‖σ‖) ^ 2 = 64 * C * ‖σ‖ ^ 2 / T ^ 2 by field_simp,
      div_le_one (by positivity)]
    exact hσ
  have hrect : MeasurableSet (Icc a b ×ˢ Icc (0 : ℝ) 1) := measurableSet_Icc.prod measurableSet_Icc
  nlinarith [mul_le_mul_of_nonneg_right hk (le_trans (setIntegral_nonneg hrect
    fun _ _ ↦ sq_nonneg _) hL), mul_nonneg hC (sq_nonneg (1 / T * ‖σ‖))]

omit [NormedSpace ℝ F] in
/-- **The injectivity estimate is invariant under translation.** Let `P'` be the translate of an
operator `P` by `(c, 0)`, in the sense `P' (ξ (· + (c, 0))) z = P ξ (z + (c, 0))`. If `P` satisfies
the injectivity estimate `‖ξ‖²_{W^{1,2}} ≤ C ‖P ξ‖²_{L²}` on `C²` sections of period one in `t`
vanishing outside a strip, then so does `P'`, with the same constant. -/
theorem setIntegral_sobolev_le_mul_setIntegral_of_comp_add_right {P P' : (ℝ × ℝ → E) → ℝ × ℝ → F}
    {C : ℝ} (c : ℝ) (hP' : ∀ ξ z, P' (fun w ↦ ξ (w + (c, 0))) z = P ξ (z + (c, 0)))
    (hest : ∀ ⦃ξ : ℝ × ℝ → E⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖P ξ z‖ ^ 2)
    {ξ : ℝ × ℝ → E} (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) {a b : ℝ}
    (hab : a ≤ b) (hξ₀ : ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
      C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖P' ξ z‖ ^ 2 := by
  -- Apply the estimate to the translate `ξ'` of `ξ`, which vanishes outside `(a + c, b + c)`.
  set ξ' : ℝ × ℝ → E := fun w ↦ ξ (w + (-c, 0))
  have hξ'c : (fun w ↦ ξ' (w + (c, 0))) = ξ := funext fun w ↦ by
    simp only [ξ', add_assoc, Prod.mk_add_mk, add_neg_cancel, add_zero, Prod.mk_zero_zero]
  have h := hest (ξ := ξ') (hξ.comp (contDiff_id.add contDiff_const))
    (fun s t ↦ by simp only [ξ', Prod.mk_add_mk, add_zero, hper]) (a := a + c) (b := b + c)
    (by linarith) fun s t hs ↦ hξ₀ _ _ fun h ↦ hs ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [setIntegral_Icc_add_prod_eq, setIntegral_Icc_add_prod_eq] at h
  rw [← hξ'c]
  simpa only [fderiv_comp_add_right, hP'] using h

end Floer

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The injectivity estimate is invariant under translation.** If the linearized Floer operator
of the data `(J, K_s, K_t, u)` satisfies `‖ξ‖²_{W^{1,2}} ≤ C ‖D ξ‖²_{L²}` on `C²` maps of period
one in `t` vanishing outside a strip, then so does the linearized operator of the data translated
by `(c, 0)`, with the same constant. -/
theorem setIntegral_sobolev_le_mul_setIntegral_floerLinearization_comp_add_right
    (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
    {u : ℝ × ℝ → V} {C : ℝ} (c : ℝ)
    (hest : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) {a b : ℝ}
    (hab : a ≤ b) (hξ₀ : ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
      C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization (fun w ↦ J (w + (c, 0)))
        (fun w ↦ Ks (w + (c, 0))) (fun w ↦ Kt (w + (c, 0))) (fun w ↦ u (w + (c, 0))) ξ z‖ ^ 2 :=
  Floer.setIntegral_sobolev_le_mul_setIntegral_of_comp_add_right c
    (fun ξ z ↦ ω.floerLinearization_comp_add_right J Ks Kt u ξ (c, 0) z) hest hξ hper hab hξ₀

/-- **The uniform estimate for spliced linearized Floer operators.** Let `D`, `D₁` and `D₂` be the
linearized Floer operators `∂s + J(z, u z) ∂t + C(z)` of three data sets, all regular enough to send
`C²` maps to continuous maps. Suppose that `D₁` and `D₂` satisfy the injectivity estimate
`‖ξ‖²_{W^{1,2}} ≤ C ‖D_i ξ‖²_{L²}` on `C²` maps of period one in `t` vanishing outside a strip, and
that for `t ∈ [0, 1]` the coefficients `J(z, u z)` and `C(z)` of `D` are `ε`-close to those of
`D₁` where `s ≤ T` and to those of `D₂` where `s ≥ -T`. If `64 C ≤ T²` and `8 C ε² ≤ 1`, then `D`
satisfies the injectivity estimate with the constant `64 C`, independent of `T` and `ε`. -/
theorem setIntegral_sobolev_le_mul_setIntegral_floerLinearization_of_splice
    (ω : SymplecticForm V) {J J₁ J₂ : ℝ × ℝ → V → V →L[ℝ] V}
    {Ks Kt Ks₁ Kt₁ Ks₂ Kt₂ : ℝ × ℝ → V → ℝ} {u u₁ u₂ : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hJ₁ : ∀ z, ContDiffAt ℝ 1 (Function.uncurry J₁) (z, u₁ z))
    (hKs₁ : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Ks₁) (z, u₁ z))
    (hKt₁ : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Kt₁) (z, u₁ z)) (hu₁ : ContDiff ℝ 1 u₁)
    (hJ₂ : ∀ z, ContDiffAt ℝ 1 (Function.uncurry J₂) (z, u₂ z))
    (hKs₂ : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Ks₂) (z, u₂ z))
    (hKt₂ : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Kt₂) (z, u₂ z)) (hu₂ : ContDiff ℝ 1 u₂)
    {C ε T : ℝ} (hC : 0 ≤ C) (hT : 0 < T) (hCT : 64 * C ≤ T ^ 2) (hε : 8 * C * ε ^ 2 ≤ 1)
    (hJε₁ : ∀ z : ℝ × ℝ, z.1 ≤ T → z.2 ∈ Icc (0 : ℝ) 1 → ‖J z (u z) - J₁ z (u₁ z)‖ ≤ ε)
    (hCε₁ : ∀ z : ℝ × ℝ, z.1 ≤ T → z.2 ∈ Icc (0 : ℝ) 1 →
      ‖ω.floerLinearizationCoeff J Ks Kt u z - ω.floerLinearizationCoeff J₁ Ks₁ Kt₁ u₁ z‖ ≤ ε)
    (hJε₂ : ∀ z : ℝ × ℝ, -T ≤ z.1 → z.2 ∈ Icc (0 : ℝ) 1 → ‖J z (u z) - J₂ z (u₂ z)‖ ≤ ε)
    (hCε₂ : ∀ z : ℝ × ℝ, -T ≤ z.1 → z.2 ∈ Icc (0 : ℝ) 1 →
      ‖ω.floerLinearizationCoeff J Ks Kt u z - ω.floerLinearizationCoeff J₂ Ks₂ Kt₂ u₂ z‖ ≤ ε)
    (hest₁ : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization J₁ Ks₁ Kt₁ u₁ ξ z‖ ^ 2)
    (hest₂ : ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization J₂ Ks₂ Kt₂ u₂ ξ z‖ ^ 2)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) {a b : ℝ}
    (hab : a ≤ b) (hξ₀ : ∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
      64 * C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization J Ks Kt u ξ z‖ ^ 2 := by
  -- The symbol in the `s` direction is the identity, of norm at most `1`.
  have hσ : 64 * C * ‖ContinuousLinearMap.id ℝ V‖ ^ 2 ≤ T ^ 2 := by
    have h₀ := norm_nonneg (ContinuousLinearMap.id ℝ V)
    have h₁ := norm_id_le (𝕜 := ℝ) (E := V)
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_one₀ h₀ h₁ (n := 2)) hC]
  have hleib {J' : ℝ × ℝ → V → V →L[ℝ] V} {Ks' Kt' : ℝ × ℝ → V → ℝ} {u' : ℝ × ℝ → V}
      ⦃η : ℝ × ℝ → V⦄ (hη : ContDiff ℝ 2 η) ⦃β β' : ℝ → ℝ⦄ (hβ : ∀ s, HasDerivAt β (β' s) s)
      (z : ℝ × ℝ) : ω.floerLinearization J' Ks' Kt' u' (fun w ↦ β w.1 • η w) z =
        β z.1 • ω.floerLinearization J' Ks' Kt' u' η z +
          β' z.1 • ContinuousLinearMap.id ℝ V (η z) :=
    ω.floerLinearization_smul_fst J' Ks' Kt' u' η (hβ z.1) (hη.differentiable two_ne_zero z)
  have hclose {J' : ℝ × ℝ → V → V →L[ℝ] V} {Ks' Kt' : ℝ × ℝ → V → ℝ} {u' : ℝ × ℝ → V}
      {z : ℝ × ℝ} (hJz : ‖J z (u z) - J' z (u' z)‖ ≤ ε)
      (hCz : ‖ω.floerLinearizationCoeff J Ks Kt u z - ω.floerLinearizationCoeff J' Ks' Kt' u' z‖ ≤
        ε) (η : ℝ × ℝ → V) :
      ‖ω.floerLinearization J Ks Kt u η z - ω.floerLinearization J' Ks' Kt' u' η z‖ ≤
        ε * (‖fderiv ℝ η z stdComplexLineImag‖ + ‖η z‖) := by
    refine (ω.norm_floerLinearization_sub_floerLinearization_le J J' Ks Kt Ks' Kt' u u' η
      z).trans ?_
    rw [mul_add]
    gcongr
  exact Floer.setIntegral_sobolev_le_mul_setIntegral_of_splice (ContinuousLinearMap.id ℝ V) hC hT
    hσ hε (fun η hη ↦ ω.continuous_floerLinearization hJ hKs hKt hu (hη.of_le one_le_two))
    (fun η hη ↦ ω.continuous_floerLinearization hJ₁ hKs₁ hKt₁ hu₁ (hη.of_le one_le_two))
    (fun η hη ↦ ω.continuous_floerLinearization hJ₂ hKs₂ hKt₂ hu₂ (hη.of_le one_le_two))
    hleib hleib hleib (fun η _ z hz ht ↦ hclose (hJε₁ z hz ht) (hCε₁ z hz ht) η)
    (fun η _ z hz ht ↦ hclose (hJε₂ z hz ht) (hCε₂ z hz ht) η) hest₁ hest₂ hξ hper hab hξ₀

/-- **The uniform estimate for spliced formal adjoints.** Let `D^*`, `D₁^*` and `D₂^*` be the formal
adjoints `-(∂s + (∂t ·) ∘ J(z, u z) + (·) ∘ A(z))` of the linearized Floer operators of three data
sets, with `A = ∂t J - C` (`floerLinearizationAdjoint_eq_neg`), all regular enough to send `C²`
covector fields to continuous ones. Suppose that `D₁^*` and `D₂^*` satisfy the injectivity estimate
`‖η‖²_{W^{1,2}} ≤ C ‖D_i^* η‖²_{L²}` on `C²` covector fields of period one in `t` vanishing outside
a strip, and that for `t ∈ [0, 1]` the coefficients `J(z, u z)` and `A(z)` of `D^*` are `ε`-close to
those of `D₁^*` where `s ≤ T` and to those of `D₂^*` where `s ≥ -T`. If `64 C ≤ T²` and
`8 C ε² ≤ 1`, then `D^*` satisfies the injectivity estimate with the constant `64 C`, independent of
`T` and `ε`. On the Sobolev completion such an estimate for the adjoint makes the operator onto. -/
theorem setIntegral_sobolev_le_mul_setIntegral_floerLinearizationAdjoint_of_splice
    (ω : SymplecticForm V) {J J₁ J₂ : ℝ × ℝ → V → V →L[ℝ] V}
    {Ks Kt Ks₁ Kt₁ Ks₂ Kt₂ : ℝ × ℝ → V → ℝ} {u u₁ u₂ : ℝ × ℝ → V}
    (hJ : ∀ z, ContDiffAt ℝ 1 (Function.uncurry J) (z, u z))
    (hKs : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Ks) (z, u z))
    (hKt : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Kt) (z, u z)) (hu : ContDiff ℝ 1 u)
    (hJ₁ : ∀ z, ContDiffAt ℝ 1 (Function.uncurry J₁) (z, u₁ z))
    (hKs₁ : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Ks₁) (z, u₁ z))
    (hKt₁ : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Kt₁) (z, u₁ z)) (hu₁ : ContDiff ℝ 1 u₁)
    (hJ₂ : ∀ z, ContDiffAt ℝ 1 (Function.uncurry J₂) (z, u₂ z))
    (hKs₂ : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Ks₂) (z, u₂ z))
    (hKt₂ : ∀ z, ContDiffAt ℝ 2 (Function.uncurry Kt₂) (z, u₂ z)) (hu₂ : ContDiff ℝ 1 u₂)
    {C ε T : ℝ} (hC : 0 ≤ C) (hT : 0 < T) (hCT : 64 * C ≤ T ^ 2) (hε : 8 * C * ε ^ 2 ≤ 1)
    (hJε₁ : ∀ z : ℝ × ℝ, z.1 ≤ T → z.2 ∈ Icc (0 : ℝ) 1 → ‖J z (u z) - J₁ z (u₁ z)‖ ≤ ε)
    (hAε₁ : ∀ z : ℝ × ℝ, z.1 ≤ T → z.2 ∈ Icc (0 : ℝ) 1 →
      ‖(fderiv ℝ (fun w ↦ J w (u w)) z stdComplexLineImag -
            ω.floerLinearizationCoeff J Ks Kt u z) -
          (fderiv ℝ (fun w ↦ J₁ w (u₁ w)) z stdComplexLineImag -
            ω.floerLinearizationCoeff J₁ Ks₁ Kt₁ u₁ z)‖ ≤ ε)
    (hJε₂ : ∀ z : ℝ × ℝ, -T ≤ z.1 → z.2 ∈ Icc (0 : ℝ) 1 → ‖J z (u z) - J₂ z (u₂ z)‖ ≤ ε)
    (hAε₂ : ∀ z : ℝ × ℝ, -T ≤ z.1 → z.2 ∈ Icc (0 : ℝ) 1 →
      ‖(fderiv ℝ (fun w ↦ J w (u w)) z stdComplexLineImag -
            ω.floerLinearizationCoeff J Ks Kt u z) -
          (fderiv ℝ (fun w ↦ J₂ w (u₂ w)) z stdComplexLineImag -
            ω.floerLinearizationCoeff J₂ Ks₂ Kt₂ u₂ z)‖ ≤ ε)
    (hest₁ : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → (∀ s t, η (s, t + 1) = η (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → η (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
            ‖ω.floerLinearizationAdjoint J₁ Ks₁ Kt₁ u₁ η z‖ ^ 2)
    (hest₂ : ∀ ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄, ContDiff ℝ 2 η → (∀ s t, η (s, t + 1) = η (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → η (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
          C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
            ‖ω.floerLinearizationAdjoint J₂ Ks₂ Kt₂ u₂ η z‖ ^ 2)
    {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : ContDiff ℝ 2 η) (hper : ∀ s t, η (s, t + 1) = η (s, t))
    {a b : ℝ} (hab : a ≤ b) (hη₀ : ∀ s t, s ∉ Ioo a b → η (s, t) = 0) :
    ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ η z stdComplexLineReal‖ ^ 2 +
        ‖fderiv ℝ η z stdComplexLineImag‖ ^ 2 + ‖η z‖ ^ 2) ≤
      64 * C * ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1,
        ‖ω.floerLinearizationAdjoint J Ks Kt u η z‖ ^ 2 := by
  -- The symbol in the `s` direction is `-1`, of norm at most `1`.
  set σ := -ContinuousLinearMap.id ℝ (V →L[ℝ] ℝ)
  have hσ : 64 * C * ‖σ‖ ^ 2 ≤ T ^ 2 := by
    have h₀ := norm_nonneg σ
    have h₁ : ‖σ‖ ≤ 1 := opNorm_le_bound _ zero_le_one fun η ↦ by simp [σ]
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_one₀ h₀ h₁ (n := 2)) hC]
  have hJu {J' : ℝ × ℝ → V → V →L[ℝ] V} {u' : ℝ × ℝ → V}
      (hJ' : ∀ z, ContDiffAt ℝ 1 (Function.uncurry J') (z, u' z)) (hu' : ContDiff ℝ 1 u')
      (z : ℝ × ℝ) : DifferentiableAt ℝ (fun w ↦ J' w (u' w)) z :=
    ((hJ' z).comp₂ contDiffAt_id hu'.contDiffAt).differentiableAt one_ne_zero
  have hleib {J' : ℝ × ℝ → V → V →L[ℝ] V} {Ks' Kt' : ℝ × ℝ → V → ℝ} {u' : ℝ × ℝ → V}
      (hJu' : ∀ z, DifferentiableAt ℝ (fun w ↦ J' w (u' w)) z) ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄
      (hη : ContDiff ℝ 2 η) ⦃β β' : ℝ → ℝ⦄ (hβ : ∀ s, HasDerivAt β (β' s) s) (z : ℝ × ℝ) :
      ω.floerLinearizationAdjoint J' Ks' Kt' u' (fun w ↦ β w.1 • η w) z =
        β z.1 • ω.floerLinearizationAdjoint J' Ks' Kt' u' η z + β' z.1 • σ (η z) := by
    rw [floerLinearizationAdjoint_smul_fst (hβ z.1) (hη.differentiable two_ne_zero z) (hJu' z)]
    simp [σ, sub_eq_add_neg]
  have hclose {J' : ℝ × ℝ → V → V →L[ℝ] V} {Ks' Kt' : ℝ × ℝ → V → ℝ} {u' : ℝ × ℝ → V}
      {z : ℝ × ℝ} (hJu' : DifferentiableAt ℝ (fun w ↦ J' w (u' w)) z)
      (hJz : ‖J z (u z) - J' z (u' z)‖ ≤ ε)
      (hAz : ‖(fderiv ℝ (fun w ↦ J w (u w)) z stdComplexLineImag -
            ω.floerLinearizationCoeff J Ks Kt u z) -
          (fderiv ℝ (fun w ↦ J' w (u' w)) z stdComplexLineImag -
            ω.floerLinearizationCoeff J' Ks' Kt' u' z)‖ ≤ ε)
      ⦃η : ℝ × ℝ → V →L[ℝ] ℝ⦄ (hη : ContDiff ℝ 2 η) :
      ‖ω.floerLinearizationAdjoint J Ks Kt u η z - ω.floerLinearizationAdjoint J' Ks' Kt' u' η z‖ ≤
        ε * (‖fderiv ℝ η z stdComplexLineImag‖ + ‖η z‖) := by
    refine (norm_floerLinearizationAdjoint_sub_floerLinearizationAdjoint_le
      (hη.differentiable two_ne_zero z) (hJu hJ hu z) hJu').trans ?_
    rw [mul_add]
    gcongr
  exact Floer.setIntegral_sobolev_le_mul_setIntegral_of_splice σ hC hT hσ hε
    (fun _ hη ↦ continuous_floerLinearizationAdjoint hJ hKs hKt hu (hη.of_le one_le_two))
    (fun _ hη ↦ continuous_floerLinearizationAdjoint hJ₁ hKs₁ hKt₁ hu₁ (hη.of_le one_le_two))
    (fun _ hη ↦ continuous_floerLinearizationAdjoint hJ₂ hKs₂ hKt₂ hu₂ (hη.of_le one_le_two))
    (hleib (hJu hJ hu)) (hleib (hJu hJ₁ hu₁)) (hleib (hJu hJ₂ hu₂))
    (fun _ hη z hz ht ↦ hclose (hJu hJ₁ hu₁ z) (hJε₁ z hz ht) (hAε₁ z hz ht) hη)
    (fun _ hη z hz ht ↦ hclose (hJu hJ₂ hu₂ z) (hJε₂ z hz ht) (hAε₂ z hz ht) hη)
    hest₁ hest₂ hη hper hab hη₀

end SymplecticForm

end TauCeti

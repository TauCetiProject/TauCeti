/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.HessianMultiplier
public import TauCeti.Analysis.Fourier.MihlinHormander
import TauCeti.Analysis.Calculus.IteratedFDeriv.Homogeneous

/-!
# The Riesz transforms

Let `E` be a finite-dimensional real inner product space and `F` a complex Hilbert space. The
**Riesz transform** in the direction `v ∈ E` is the Fourier multiplier on `L²(E, F)` with symbol

`ξ ↦ -i ⟪ξ, v⟫ / ‖ξ‖` (`TauCeti.rieszSymbol`),

given the value `0` at the origin (`TauCeti.rieszTransform`). For an orthonormal basis `eⱼ` the
operators `Rⱼ = R_{eⱼ}` are the classical Riesz transforms, with symbols `-i ξⱼ / ‖ξ‖`; in
dimension one, `R₁` is the Hilbert transform, with symbol `-i sign ξ`. The symbol is linear in
`v`, so `v ↦ R_v` is linear and `R_v = ∑ⱼ ⟪v, eⱼ⟫ Rⱼ`.

The symbol is bounded by `‖v‖` but discontinuous at the origin, and homogeneous of degree `0`.
Hence:

* `R_v` is bounded on `L²` with `‖R_v‖ ≤ ‖v‖`, and skew-adjoint: `R_v† = -R_v`.
* `R_v R_w = -T_{m_{v,w}}`, where `T_{m_{v,w}} = ∂_v ∂_w Δ⁻¹` is the Hessian multiplier with
  symbol `⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²` (`TauCeti.hessianSymbolLp`). On Schwartz functions this is the
  classical identity `∂_v ∂_w u = -R_v R_w Δu`, through which `Lᵖ` bounds for the Riesz transforms
  give the Calderón–Zygmund estimate `‖D²u‖_p ≤ C ‖Δu‖_p`.
* `∑ⱼ Rⱼ² = -1` and `∑ⱼ ‖Rⱼ f‖² = ‖f‖²` for every orthonormal basis.
* By the Mihlin–Hörmander theorem, `R_v` is bounded in every `Lᵖ` norm, `1 < p < ∞`:
  `‖R_v f‖_p ≤ C ‖v‖ ‖f‖_p` with `C` depending only on `E` and `p`.

The Riesz transforms are the basic examples of Calderón–Zygmund operators. Their kernel,
`c_n ⟪x - y, v⟫ / ‖x - y‖ ^ (n + 1)` with `c_n = Γ((n + 1) / 2) / π ^ ((n + 1) / 2)`, is
identified in `TauCeti.Analysis.Fourier.RieszTransform.Kernel`.

## Main declarations

* `TauCeti.rieszSymbol`, `TauCeti.rieszSymbolLp`: the symbol and its class in `L^∞`.
* `TauCeti.rieszTransform`: the Riesz transform `R_v` on `L²(E, F)`.
* `TauCeti.norm_rieszTransform_le`, `TauCeti.adjoint_rieszTransform`: `‖R_v‖ ≤ ‖v‖` and
  `R_v† = -R_v`.
* `TauCeti.rieszTransform_compL_rieszTransform`: `R_v R_w = -T_{m_{v,w}}`.
* `TauCeti.sum_rieszTransform_compL_rieszTransform`,
  `TauCeti.sum_norm_rieszTransform_apply_sq`: `∑ⱼ Rⱼ² = -1` and `∑ⱼ ‖Rⱼ f‖² = ‖f‖²`.
* `SchwartzMap.toLp_lineDerivOp_lineDerivOp_eq_neg_rieszTransform`: `∂_v ∂_w u = -R_v R_w Δu`.
* `TauCeti.exists_eLpNorm_rieszTransform_le`: the `Lᵖ` bound, `1 < p < ∞`.

## References

* M. Riesz, *Sur les fonctions conjuguées*, Math. Z. **27** (1928), 218–244.
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter III,
  §1.
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 5.1.4.
-/

public section

noncomputable section

open scoped ENNReal NNReal FourierTransform SchwartzMap RealInnerProductSpace Real Laplacian
  LineDeriv ContDiff
open FourierTransform MeasureTheory

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The symbol -/

/-- The symbol `ξ ↦ -i ⟪ξ, v⟫ / ‖ξ‖` of the Riesz transform in the direction `v`. At the origin
it takes the value `0`. -/
def rieszSymbol (v ξ : E) : ℂ :=
  -Complex.I * ((⟪ξ, v⟫ / ‖ξ‖ : ℝ) : ℂ)

theorem rieszSymbol_apply (v ξ : E) :
    rieszSymbol v ξ = -Complex.I * ((⟪ξ, v⟫ / ‖ξ‖ : ℝ) : ℂ) := (rfl)

@[simp]
theorem rieszSymbol_zero_left (ξ : E) : rieszSymbol 0 ξ = 0 := by
  simp [rieszSymbol]

@[simp]
theorem rieszSymbol_zero_right (v : E) : rieszSymbol v 0 = 0 := by
  simp [rieszSymbol]

theorem rieszSymbol_add_left (v w ξ : E) :
    rieszSymbol (v + w) ξ = rieszSymbol v ξ + rieszSymbol w ξ := by
  simp only [rieszSymbol, inner_add_right, add_div]
  push_cast
  ring

theorem rieszSymbol_smul_left (c : ℝ) (v ξ : E) :
    rieszSymbol (c • v) ξ = c * rieszSymbol v ξ := by
  simp only [rieszSymbol, real_inner_smul_right, mul_div_assoc]
  push_cast
  ring

/-- The symbol is homogeneous of degree `0`. -/
@[simp]
theorem rieszSymbol_smul_right {t : ℝ} (ht : 0 < t) (v ξ : E) :
    rieszSymbol v (t • ξ) = rieszSymbol v ξ := by
  simp only [rieszSymbol, real_inner_smul_left, norm_smul, Real.norm_of_nonneg ht.le,
    mul_div_mul_left _ _ ht.ne']

/-- The symbol is bounded by `‖v‖`, by the Cauchy–Schwarz inequality. -/
theorem norm_rieszSymbol_le (v ξ : E) : ‖rieszSymbol v ξ‖ ≤ ‖v‖ := by
  rw [rieszSymbol, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_div, abs_norm]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  · rw [div_le_iff₀ (norm_pos_iff.2 hξ), mul_comm]
    exact abs_real_inner_le_norm _ _

/-- The symbol is purely imaginary. -/
@[simp]
theorem star_rieszSymbol (v ξ : E) : star (rieszSymbol v ξ) = -rieszSymbol v ξ := by
  simp [rieszSymbol]

/-- The product of two Riesz symbols is minus the Hessian symbol `⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²`. -/
theorem rieszSymbol_mul_rieszSymbol (v w ξ : E) :
    rieszSymbol v ξ * rieszSymbol w ξ = -hessianSymbol v w ξ := by
  have hI : -Complex.I * -Complex.I = -1 := by simp
  rw [rieszSymbol, rieszSymbol, hessianSymbol_apply, mul_mul_mul_comm, hI, ← Complex.ofReal_mul,
    div_mul_div_comm, ← sq, neg_one_mul]

/-- For an orthonormal basis `eⱼ`, the squares of the symbols `-i ξⱼ / ‖ξ‖` sum to `-1` away
from the origin. -/
theorem sum_rieszSymbol_mul_rieszSymbol {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {ξ : E} (hξ : ξ ≠ 0) : ∑ i, rieszSymbol (b i) ξ * rieszSymbol (b i) ξ = -1 := by
  simp only [rieszSymbol_mul_rieszSymbol, Finset.sum_neg_distrib, sum_hessianSymbol_self b hξ]

/-- The symbol is smooth away from the origin. -/
theorem contDiffOn_rieszSymbol (v : E) : ContDiffOn ℝ ∞ (rieszSymbol v) {0}ᶜ := fun ξ hξ ↦ by
  refine ContDiffAt.contDiffWithinAt ?_
  refine contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp ξ ?_)
  exact (contDiffAt_id.inner ℝ contDiffAt_const).div (contDiffAt_norm ℝ hξ) (norm_ne_zero_iff.2 hξ)

variable [MeasurableSpace E]

@[fun_prop]
theorem measurable_rieszSymbol [OpensMeasurableSpace E] (v : E) :
    Measurable (rieszSymbol v) := by
  unfold rieszSymbol
  fun_prop

/-- The Riesz symbol is essentially bounded for every measure. -/
theorem memLp_rieszSymbol [OpensMeasurableSpace E] (v : E) (μ : Measure E) :
    MemLp (rieszSymbol v) ∞ μ :=
  memLp_top_of_bound (measurable_rieszSymbol v).aestronglyMeasurable _
    (.of_forall (norm_rieszSymbol_le v))

variable [BorelSpace E] [FiniteDimensional ℝ E]

/-- The symbol `ξ ↦ -i ⟪ξ, v⟫ / ‖ξ‖` of the Riesz transform, as an element of `L^∞`. -/
def rieszSymbolLp (v : E) : Lp ℂ ∞ (volume : Measure E) :=
  (memLp_rieszSymbol v volume).toLp _

theorem coeFn_rieszSymbolLp (v : E) : rieszSymbolLp v =ᵐ[volume] rieszSymbol v :=
  (memLp_rieszSymbol v volume).coeFn_toLp

theorem rieszSymbolLp_add (v w : E) :
    rieszSymbolLp (v + w) = rieszSymbolLp v + rieszSymbolLp w := by
  apply Lp.ext
  filter_upwards [coeFn_rieszSymbolLp (v + w), coeFn_rieszSymbolLp v, coeFn_rieszSymbolLp w,
    Lp.coeFn_add (rieszSymbolLp v) (rieszSymbolLp w)] with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₄, Pi.add_apply, h₂, h₃, rieszSymbol_add_left]

theorem rieszSymbolLp_smul (c : ℝ) (v : E) :
    rieszSymbolLp (c • v) = (c : ℂ) • rieszSymbolLp v := by
  apply Lp.ext
  filter_upwards [coeFn_rieszSymbolLp (c • v), coeFn_rieszSymbolLp v,
    Lp.coeFn_smul (c : ℂ) (rieszSymbolLp v)] with ξ h₁ h₂ h₃
  rw [h₁, h₃, Pi.smul_apply, h₂, rieszSymbol_smul_left, smul_eq_mul]

/-- The Riesz symbol is purely imaginary, so complex conjugation negates it. -/
@[simp]
theorem star_rieszSymbolLp (v : E) : star (rieszSymbolLp v) = -rieszSymbolLp v := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (rieszSymbolLp v), Lp.coeFn_neg (rieszSymbolLp v),
    coeFn_rieszSymbolLp v] with ξ hstar hneg hξ
  rw [hstar, hneg, Pi.star_apply, Pi.neg_apply, hξ, star_rieszSymbol]

/-- The product of the Riesz symbols in the directions `v` and `w` is minus the symbol of
`∂_v ∂_w Δ⁻¹`. -/
theorem rieszSymbolLp_smul_rieszSymbolLp (v w : E) :
    (rieszSymbolLp v • rieszSymbolLp w : Lp ℂ ∞ (volume : Measure E)) = -hessianSymbolLp v w := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := ∞) (rieszSymbolLp v) (rieszSymbolLp w),
    Lp.coeFn_neg (hessianSymbolLp v w), coeFn_rieszSymbolLp v, coeFn_rieszSymbolLp w,
    coeFn_hessianSymbolLp v w] with ξ h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₂, Pi.smul_apply', Pi.neg_apply, h₃, h₄, h₅, smul_eq_mul, rieszSymbol_mul_rieszSymbol]

/-- The `L^∞` norm of the Riesz symbol is at most `‖v‖`. -/
theorem norm_rieszSymbolLp_le (v : E) : ‖rieszSymbolLp v‖ ≤ ‖v‖ := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (eLpNormEssSup_le_of_ae_bound ?_)
  filter_upwards [coeFn_rieszSymbolLp v] with ξ hξ
  rw [hξ]
  exact norm_rieszSymbol_le v ξ

/-! ### The Riesz transform on `L²` -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable (F) in
/-- The **Riesz transform** `R_v` in the direction `v`: the Fourier multiplier on `L²(E, F)` with
symbol `-i ⟪ξ, v⟫ / ‖ξ‖`. -/
def rieszTransform (v : E) : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  Lp.fourierMultiplierCLM F (rieszSymbolLp v)

theorem rieszTransform_def (v : E) :
    rieszTransform F v = Lp.fourierMultiplierCLM F (rieszSymbolLp v) := (rfl)

/-- On the Fourier side, the Riesz transform multiplies by its symbol. -/
@[simp]
theorem fourier_rieszTransform (v : E) (f : Lp F 2 (volume : Measure E)) :
    𝓕 (rieszTransform F v f) = (rieszSymbolLp v • 𝓕 f : Lp F 2 (volume : Measure E)) :=
  Lp.fourier_fourierMultiplierCLM _ f

@[simp]
theorem rieszTransform_zero : rieszTransform F (0 : E) = 0 := by
  have h : rieszSymbolLp (0 : E) = 0 := by
    simpa using rieszSymbolLp_smul (E := E) 0 0
  rw [rieszTransform, h, Lp.fourierMultiplierCLM_zero]

theorem rieszTransform_add (v w : E) :
    rieszTransform F (v + w) = rieszTransform F v + rieszTransform F w := by
  rw [rieszTransform, rieszSymbolLp_add, Lp.fourierMultiplierCLM_add]
  rfl

theorem rieszTransform_smul (c : ℝ) (v : E) :
    rieszTransform F (c • v) = (c : ℂ) • rieszTransform F v := by
  rw [rieszTransform, rieszSymbolLp_smul, Lp.fourierMultiplierCLM_smul]
  rfl

/-- The Riesz transform in the direction `v` is the combination `∑ⱼ ⟪v, eⱼ⟫ Rⱼ` of the Riesz
transforms along an orthonormal basis. -/
theorem rieszTransform_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (v : E) :
    rieszTransform F v = ∑ i, (⟪b i, v⟫ : ℂ) • rieszTransform F (b i) := by
  classical
  conv_lhs => rw [← b.sum_repr' v]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, rieszTransform_add, rieszTransform_smul, ih,
      Finset.sum_insert hi]

/-- **Plancherel bound** for the Riesz transform: `‖R_v‖ ≤ ‖v‖`. -/
theorem norm_rieszTransform_le (v : E) : ‖rieszTransform (E := E) F v‖ ≤ ‖v‖ :=
  (Lp.norm_fourierMultiplierCLM_le _).trans (norm_rieszSymbolLp_le v)

/-- The Riesz transform is skew-adjoint: `R_v† = -R_v`. -/
theorem adjoint_rieszTransform (v : E) :
    ContinuousLinearMap.adjoint (rieszTransform (E := E) F v) = -rieszTransform F v := by
  rw [rieszTransform, Lp.adjoint_fourierMultiplierCLM, star_rieszSymbolLp, ← neg_one_smul ℂ,
    Lp.fourierMultiplierCLM_smul]
  exact neg_one_smul ℂ _

/-- The composition of two Riesz transforms is minus the Hessian multiplier: `R_v R_w` is the
Fourier multiplier `-∂_v ∂_w Δ⁻¹` with symbol `-⟪ξ, v⟫ ⟪ξ, w⟫ / ‖ξ‖²`. -/
theorem rieszTransform_compL_rieszTransform (v w : E) :
    rieszTransform F v ∘L rieszTransform F w =
      -Lp.fourierMultiplierCLM F (hessianSymbolLp v w) := by
  rw [rieszTransform, rieszTransform, Lp.fourierMultiplierCLM_compL_fourierMultiplierCLM,
    rieszSymbolLp_smul_rieszSymbolLp, ← neg_one_smul ℂ (hessianSymbolLp v w),
    Lp.fourierMultiplierCLM_smul]
  exact neg_one_smul ℂ (Lp.fourierMultiplierCLM F (hessianSymbolLp v w))

theorem rieszTransform_rieszTransform_apply (v w : E) (f : Lp F 2 (volume : Measure E)) :
    rieszTransform F v (rieszTransform F w f) =
      -Lp.fourierMultiplierCLM F (hessianSymbolLp v w) f := by
  rw [← ContinuousLinearMap.comp_apply, rieszTransform_compL_rieszTransform]
  rfl

/-- For an orthonormal basis `eⱼ`, the squares of the Riesz transforms `Rⱼ` sum to `-1`. -/
theorem sum_rieszTransform_compL_rieszTransform [Nontrivial E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) :
    ∑ i, rieszTransform F (b i) ∘L rieszTransform F (b i) =
      -ContinuousLinearMap.id ℂ (Lp F 2 (volume : Measure E)) := by
  classical
  have hsum : ∀ s : Finset ι, ∑ i ∈ s, Lp.fourierMultiplierCLM F (hessianSymbolLp (b i) (b i)) =
      Lp.fourierMultiplierCLM F (∑ i ∈ s, hessianSymbolLp (b i) (b i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, Lp.fourierMultiplierCLM_add]
  simp_rw [rieszTransform_compL_rieszTransform, Finset.sum_neg_distrib, hsum]
  rw [Lp.fourierMultiplierCLM_of_ae_eq_const (c := 1), one_smul]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ fun i ↦ hessianSymbolLp (b i) (b i),
    ae_all_iff.2 fun i ↦ coeFn_hessianSymbolLp (b i) (b i), Measure.ae_ne volume 0]
    with ξ h₁ h₂ hξ
  rw [h₁]
  simp_rw [h₂]
  exact sum_hessianSymbol_self b hξ

/-- For an orthonormal basis `eⱼ`, the Riesz transforms `Rⱼ` split the `L²` norm:
`∑ⱼ ‖Rⱼ f‖² = ‖f‖²`. -/
theorem sum_norm_rieszTransform_apply_sq [Nontrivial E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (f : Lp F 2 (volume : Measure E)) :
    ∑ i, ‖rieszTransform F (b i) f‖ ^ 2 = ‖f‖ ^ 2 := by
  have h : ∀ i, ‖rieszTransform F (b i) f‖ ^ 2 =
      -RCLike.re (inner ℂ f (rieszTransform F (b i) (rieszTransform F (b i) f))) := fun i ↦ by
    rw [@norm_sq_eq_re_inner ℂ, ← ContinuousLinearMap.adjoint_inner_right,
      adjoint_rieszTransform, FunLike.coe_neg, Pi.neg_apply, inner_neg_right,
      map_neg]
  have hsum : ∑ i, rieszTransform F (b i) (rieszTransform F (b i) f) = -f := by
    simpa using congrArg (fun T ↦ T f) (sum_rieszTransform_compL_rieszTransform (F := F) b)
  simp_rw [h, Finset.sum_neg_distrib, ← map_sum, ← inner_sum, hsum, inner_neg_right, map_neg,
    neg_neg, @norm_sq_eq_re_inner ℂ]

/-- The **Mihlin–Hörmander bound** for the Riesz transforms: for `1 < p < ∞` there is a constant
`C` with `‖R_v f‖_p ≤ C ‖v‖ ‖f‖_p` for every direction `v` and every `f ∈ L²`. -/
theorem exists_eLpNorm_rieszTransform_le [Nontrivial E] {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ (v : E) (f : Lp F 2 (volume : Measure E)),
      eLpNorm (rieszTransform F v f) p volume ≤ C * ‖v‖₊ * eLpNorm f p volume := by
  set b := stdOrthonormalBasis ℝ E
  obtain ⟨C, hC⟩ := exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le
    (V := E) (F := F) (N := Module.finrank ℝ E + 1) (by omega) hp hp_top
  have hA : ∀ i, ∃ A : ℝ≥0, ∀ k ≤ Module.finrank ℝ E + 1, ∀ ξ ≠ 0,
      ‖iteratedFDeriv ℝ k (rieszSymbol (b i)) ξ‖ ≤ A / ‖ξ‖ ^ k := fun i ↦
    exists_norm_iteratedFDeriv_le_div_pow_of_smul_eq
      ((contDiffOn_rieszSymbol (b i)).of_le (by exact_mod_cast le_top))
      fun t ht ξ ↦ rieszSymbol_smul_right ht (b i) ξ
  choose A hA using hA
  refine ⟨C * ∑ i, A i, fun v f ↦ ?_⟩
  have hi : ∀ i, eLpNorm (rieszTransform F (b i) f) p volume ≤ C * A i * eLpNorm f p volume :=
    fun i ↦ hC (contDiffOn_rieszSymbol (b i)) (hA i) _ (coeFn_rieszSymbolLp (b i)) f
  have hsum : ⇑(rieszTransform F v f) =ᵐ[volume]
      ∑ i, (⟪b i, v⟫ : ℂ) • ⇑(rieszTransform F (b i) f) := by
    have h : rieszTransform F v f = ∑ i, (⟪b i, v⟫ : ℂ) • rieszTransform F (b i) f := by
      rw [rieszTransform_eq_sum b v]
      simp
    rw [h]
    exact (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum fun i _ ↦ Lp.coeFn_smul _ _)
  rw [eLpNorm_congr_ae hsum]
  refine (eLpNorm_sum_le hp.le).trans ?_
  push_cast [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [eLpNorm_const_smul]
  have hv : ‖(⟪b i, v⟫ : ℂ)‖ₑ ≤ ‖v‖₊ := by
    rw [enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm,
      Complex.norm_real, Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (by simp [b.orthonormal.1 i])
  calc ‖(⟪b i, v⟫ : ℂ)‖ₑ * eLpNorm (rieszTransform F (b i) f) p volume
      ≤ ‖v‖₊ * (C * A i * eLpNorm f p volume) := by gcongr; exact hi i
    _ = C * A i * ‖v‖₊ * eLpNorm f p volume := by ring

end TauCeti

namespace SchwartzMap

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- On Schwartz functions, the second directional derivatives are given by the Laplacian and two
Riesz transforms: `∂_v ∂_w u = -R_v R_w Δu` in `L²`. -/
theorem toLp_lineDerivOp_lineDerivOp_eq_neg_rieszTransform (u : 𝓢(E, F)) (v w : E) :
    (∂_{v} (∂_{w} u)).toLp 2 = -rieszTransform F v (rieszTransform F w ((Δ u).toLp 2)) := by
  rw [rieszTransform_rieszTransform_apply, neg_neg,
    toLp_lineDerivOp_lineDerivOp_eq_fourierMultiplierCLM]

end SchwartzMap

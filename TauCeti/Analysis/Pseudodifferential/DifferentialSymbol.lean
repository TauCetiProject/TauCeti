/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization

/-!
# Quantization of polynomial differential symbols

A finite differential expression `u ↦ ∑ i ∈ s, bᵢ(x) (∂^{vᵢ} u)(x)` has left
Fourier symbol `∑ i ∈ s, (∏ j, i ⟪ξ, vᵢⱼ⟫) bᵢ(x)`. Here the directions are arbitrary
real vectors, the derivative orders may vary with the summand, and the coefficients are
continuous complex-linear maps between the input and output fibers.

`TauCeti.quantizeSchwartzValue_differentialSymbol` proves exact equality between this
expression and Kohn–Nirenberg quantization on Schwartz input. In particular the factor for
an order-`k` derivative is `i^k`, and there is no residual smoothing term. The frequency
rescaling by `2π` is the one in `TauCeti.quantizeSchwartzValue`.

No regularity or boundedness of the position-dependent coefficients is needed for the
pointwise identity or its absolute convergence: at a fixed position these are finitely
many fixed linear maps applied to Fourier transforms of Schwartz derivatives. Smooth
coefficients give smooth outputs. The support theorem records locality of these operators.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.1)–(1.4), for quantization and its differential-operator convention.
-/

public section

noncomputable section

open scoped ContDiff FourierTransform SchwartzMap RealInnerProductSpace LineDeriv
open MeasureTheory Real FourierTransform

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  {ι : Type*} {k : ι → ℕ}

/-- The left Fourier symbol of a finite differential expression with coefficient maps `b`
and derivative directions `v`. Each directional derivative contributes `i ⟪ξ, v⟫`. -/
def differentialSymbol (s : Finset ι) (v : ∀ i, Fin (k i) → E)
    (b : ι → E → V →L[ℂ] W) : E × E → V →L[ℂ] W :=
  fun p ↦ ∑ i ∈ s, (∏ j, (Complex.I * (⟪p.2, v i j⟫ : ℂ))) • b i p.1

theorem differentialSymbol_def (s : Finset ι) (v : ∀ i, Fin (k i) → E)
    (b : ι → E → V →L[ℂ] W) (p : E × E) :
    differentialSymbol s v b p =
      ∑ i ∈ s, (∏ j, (Complex.I * (⟪p.2, v i j⟫ : ℂ))) • b i p.1 := (rfl)

/-- The Fourier symbol of a differential expression is `i^order` times its geometric
polynomial symbol, separately in each summand. -/
theorem differentialSymbol_eq_sum_pow_mul (s : Finset ι) (v : ∀ i, Fin (k i) → E)
    (b : ι → E → V →L[ℂ] W) (p : E × E) :
    differentialSymbol s v b p =
      ∑ i ∈ s, (Complex.I ^ k i * ∏ j, (⟪p.2, v i j⟫ : ℂ)) • b i p.1 := by
  simp [differentialSymbol, Finset.prod_mul_distrib]

@[simp]
theorem differentialSymbol_empty (v : ∀ i, Fin (k i) → E)
    (b : ι → E → V →L[ℂ] W) : differentialSymbol ∅ v b = 0 := by
  funext p
  simp [differentialSymbol]

@[simp]
theorem differentialSymbol_singleton (i : ι) (v : ∀ i, Fin (k i) → E)
    (b : ι → E → V →L[ℂ] W) (p : E × E) :
    differentialSymbol {i} v b p =
      (∏ j, (Complex.I * (⟪p.2, v i j⟫ : ℂ))) • b i p.1 := by
  simp [differentialSymbol]

@[simp]
theorem differentialSymbol_insert [DecidableEq ι] (s : Finset ι) (i : ι) (hi : i ∉ s)
    (v : ∀ i, Fin (k i) → E) (b : ι → E → V →L[ℂ] W) (p : E × E) :
    differentialSymbol (insert i s) v b p =
      (∏ j, (Complex.I * (⟪p.2, v i j⟫ : ℂ))) • b i p.1 +
        differentialSymbol s v b p := by
  simp [differentialSymbol, Finset.sum_insert hi]

@[simp]
theorem differentialSymbol_zero (s : Finset ι) (v : ∀ i, Fin (k i) → E) :
    differentialSymbol s v (0 : ι → E → V →L[ℂ] W) = 0 := by
  funext p
  simp [differentialSymbol]

@[simp]
theorem differentialSymbol_add (s : Finset ι) (v : ∀ i, Fin (k i) → E)
    (b c : ι → E → V →L[ℂ] W) :
    differentialSymbol s v (b + c) = differentialSymbol s v b + differentialSymbol s v c := by
  funext p
  simp [differentialSymbol, smul_add, Finset.sum_add_distrib]

@[simp]
theorem differentialSymbol_smul (s : Finset ι) (v : ∀ i, Fin (k i) → E)
    (z : ℂ) (b : ι → E → V →L[ℂ] W) :
    differentialSymbol s v (z • b) = z • differentialSymbol s v b := by
  funext p
  simp [differentialSymbol, smul_comm _ z, Finset.smul_sum]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- After frequency rescaling, a differential monomial times `𝓕 u` is exactly the Fourier
transform of the corresponding derivative, with the coefficient map applied afterwards. -/
private theorem smul_apply_fourier_eq_apply_fourier_iteratedLineDerivOp {r : ℕ} (v : Fin r → E)
    (B : V →L[ℂ] W) (u : 𝓢(E, V)) (ζ : E) :
    ((∏ j, (Complex.I * (⟪(2 * π) • ζ, v j⟫ : ℂ))) • B) (𝓕 u ζ) =
      B (𝓕 (∂^{v} u) ζ) := by
  rw [smul_apply, SchwartzMap.fourier_iteratedLineDerivOp_apply,
    map_smul]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp only [real_inner_smul_left]
  push_cast
  ring

/-- Absolute convergence for a differential monomial follows from the Schwartz decay of
the Fourier transform of the derivative, regardless of the coefficient map. -/
private theorem integrable_quantizeSchwartzValue_integrand_prod_inner {r : ℕ}
    (v : Fin r → E) (B : V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    Integrable (fun ζ ↦ 𝐞 ⟪ζ, x⟫ •
      ((∏ j, (Complex.I * (⟪(2 * π) • ζ, v j⟫ : ℂ))) • B) (𝓕 u ζ)) := by
  simp only [smul_apply_fourier_eq_apply_fourier_iteratedLineDerivOp]
  have h : Integrable (fun ζ ↦ 𝐞 ⟪ζ, x⟫ • 𝓕 (∂^{v} u) ζ) := by
    simpa [inner_neg_right] using
      (Real.fourierIntegral_convergent_iff (μ := volume) (-x)).2 (𝓕 (∂^{v} u)).integrable
  simpa only [Circle.smul_def, map_smul] using B.integrable_comp h

/-- A polynomial differential symbol has an absolutely convergent quantization integral
on every Schwartz input, even without smoothness of its position-dependent coefficients. -/
theorem integrable_quantizeSchwartzValue_integrand_differentialSymbol
    (s : Finset ι) (v : ∀ i, Fin (k i) → E) (b : ι → E → V →L[ℂ] W)
    (u : 𝓢(E, V)) (x : E) :
    Integrable (fun ζ ↦ 𝐞 ⟪ζ, x⟫ • differentialSymbol s v b (x, (2 * π) • ζ) (𝓕 u ζ)) := by
  simp only [differentialSymbol_def, sum_apply, Finset.smul_sum]
  exact integrable_finsetSum _ fun i _ ↦
    integrable_quantizeSchwartzValue_integrand_prod_inner (v i) (b i x) u x

variable [CompleteSpace V] [CompleteSpace W]

/-- The monomial quantization integral is the corresponding derivative followed by
its fixed coefficient map. -/
private theorem integral_smul_apply_fourier_prod_inner {r : ℕ} (v : Fin r → E)
    (B : V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    (∫ ζ, 𝐞 ⟪ζ, x⟫ •
      ((∏ j, (Complex.I * (⟪(2 * π) • ζ, v j⟫ : ℂ))) • B) (𝓕 u ζ)) =
      B (∂^{v} u x) := by
  calc
    _ = quantizeSchwartzValue (fun _ ↦ B) (∂^{v} u) x := by
      simp only [quantizeSchwartzValue_def,
        smul_apply_fourier_eq_apply_fourier_iteratedLineDerivOp]
    _ = _ := quantizeSchwartzValue_comp_fst (fun _ ↦ B) (∂^{v} u) x

/-- Quantization of a differential monomial is exactly the indicated iterated derivative
followed by the coefficient map; the coefficient is evaluated at the output position. -/
theorem quantizeSchwartzValue_differentialSymbol_singleton (i : ι)
    (v : ∀ i, Fin (k i) → E) (b : ι → E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue (differentialSymbol {i} v b) u x = b i x (∂^{v i} u x) := by
  simp only [quantizeSchwartzValue_def, differentialSymbol_singleton]
  exact integral_smul_apply_fourier_prod_inner (v i) (b i x) u x

/-- **Exact differential-operator comparison.** The left quantization of the polynomial
Fourier symbol of a finite differential expression equals that expression on Schwartz input.
There are no derivatives of the coefficients in left quantization. -/
@[simp]
theorem quantizeSchwartzValue_differentialSymbol (s : Finset ι)
    (v : ∀ i, Fin (k i) → E) (b : ι → E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue (differentialSymbol s v b) u x =
      ∑ i ∈ s, b i x (∂^{v i} u x) := by
  simp only [quantizeSchwartzValue_def, differentialSymbol_def,
    sum_apply, Finset.smul_sum]
  rw [integral_finsetSum _ fun i _ ↦
    integrable_quantizeSchwartzValue_integrand_prod_inner (v i) (b i x) u x]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_smul_apply_fourier_prod_inner (v i) (b i x) u x

/-- The same comparison written with native iterated Fréchet derivatives. -/
theorem quantizeSchwartzValue_differentialSymbol_eq_sum_iteratedFDeriv (s : Finset ι)
    (v : ∀ i, Fin (k i) → E) (b : ι → E → V →L[ℂ] W) (u : 𝓢(E, V)) (x : E) :
    quantizeSchwartzValue (differentialSymbol s v b) u x =
      ∑ i ∈ s, b i x (iteratedFDeriv ℝ (k i) u x (v i)) := by
  simp only [quantizeSchwartzValue_differentialSymbol,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]

/-- Smooth coefficients give smooth quantized differential expressions. No global
boundedness of any coefficient or its derivatives is required. -/
theorem contDiff_quantizeSchwartzValue_differentialSymbol (s : Finset ι)
    (v : ∀ i, Fin (k i) → E) (b : ι → E → V →L[ℂ] W)
    (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i)) (u : 𝓢(E, V)) :
    ContDiff ℝ ∞ (quantizeSchwartzValue (differentialSymbol s v b) u) := by
  simp only [funext (quantizeSchwartzValue_differentialSymbol s v b u)]
  apply ContDiff.sum
  intro i hi
  -- Restrict coefficient maps to real scalars, since smoothness is over the real base.
  have hbi := (ContinuousLinearMap.restrictScalarsL ℂ V W ℝ ℝ).contDiff.comp (hb i hi)
  simpa only [Function.comp_apply, ContinuousLinearMap.coe_restrict_scalarsL',
    ContinuousLinearMap.coe_restrictScalars'] using hbi.clm_apply ((∂^{v i} u).smooth ⊤)

/-- The quantized differential expression is supported in the topological support
(closure of the support) of the Schwartz input, even for nonsmooth coefficients. -/
theorem support_quantizeSchwartzValue_differentialSymbol_subset (s : Finset ι)
    (v : ∀ i, Fin (k i) → E) (b : ι → E → V →L[ℂ] W) (u : 𝓢(E, V)) :
    Function.support (quantizeSchwartzValue (differentialSymbol s v b) u) ⊆ tsupport u := by
  intro x hx
  by_contra h
  apply hx
  rw [quantizeSchwartzValue_differentialSymbol]
  apply Finset.sum_eq_zero
  intro i _
  have hzero : (∂^{v i} u) x = 0 :=
    image_eq_zero_of_notMem_tsupport fun hx' ↦
      h (SchwartzMap.tsupport_iteratedLineDerivOp_subset (v i) u hx')
  simp [hzero]

end TauCeti

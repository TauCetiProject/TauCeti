/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# The asymptotic expansion of the composition symbol

Let `a` be a symbol of order `m'` with values in `W →L[ℂ] U` and `b` a symbol of order `m` with
values in `V →L[ℂ] W` that vanishes for positions outside a compact set. Their composition symbol
`a # b` (`TauCeti.Symbol.sharp`), whose quantization is the composition of the quantizations, has
the asymptotic expansion

`a # b ∼ ∑_γ (1 / i)^{|γ|} / γ! ∂_ξ^γ a ∘ ∂_x^γ b`,

in the sense that the remainder after the terms with `|γ| < N` is a symbol of order `m' + m - N`.
Here the terms are grouped by `k = |γ|` and written with words instead of multi-indices: the `k`-th
term is `(-i)ᵏ / k! ∑_{r : Fin k → Fin n} ∂_ξ^r a ∘ ∂_x^r b`, each multi-index `γ` with `|γ| = k`
being the content of `k! / γ!` words. This is the symbol calculus of composition: the leading
term is the pointwise composition `a ∘ b`, so `a # b - a ∘ b` has order `m' + m - 1`.

## Main declarations

* `TauCeti.Symbol.sharpTerm`: the `k`-th term of the expansion, a symbol of order `m' + m - k`
  built from the iterated derivatives `TauCeti.Symbol.iteratedFrequencyDeriv` and
  `TauCeti.Symbol.iteratedSpatialDeriv`, with the Leibniz rules
  `TauCeti.Symbol.spatialDeriv_sharpTerm` and `TauCeti.Symbol.frequencyDeriv_sharpTerm`,
  and leading term `a ∘ b` (`TauCeti.Symbol.sharpTerm_zero`).
* `TauCeti.Symbol.exists_sharp_sub_sum_sharpTerm`: **the composition expansion**. For every `N`,
  `a # b - ∑_{k < N} sharpTerm k a b` is a symbol of order `m' + m - N`.
* `TauCeti.Symbol.exists_sharp_sub_comp`: `a # b - a ∘ b` is a symbol of order `m' + m - 1`.

The coefficient spaces `W` and `U` are complete, for the Fourier inversion and Taylor's formula
with integral remainder below.

## Proof outline

The coefficient of `a # b` is `∫ exp(2πi ⟪η, x⟫) a(x, ξ + 2πη) ∘ b̂(η, ξ) dη`. Taylor's formula
with integral remainder (Mathlib's `map_add_eq_sum_add_integral_iteratedFDeriv`) expands
`a(x, ξ + 2πη)` in the frequency. Expanding the `k`-th derivative in the standard basis, the
monomial `∏ᵢ 2π η_{r i}` turns `b̂` into `(-i)ᵏ` times the Fourier transform of `∂_x^r b`, and
Fourier inversion integrates its term to `(-i)ᵏ / k! ∂_ξ^r a(x, ξ) ∘ ∂_x^r b(x, ξ)`. The integral
remainder involves the `N`-th frequency derivative of `a`, of order `m' - N`; Peetre's inequality
and the rapid decay of `b̂` bound the remainder by `C ⟨ξ⟩ ^ (m' + m - N)` for positions in a
compact set. For the derivatives of the remainder, the Leibniz rules for `#` and for the terms
show that a position or frequency derivative of the remainder for `(a, b)` is the sum of the
remainders for the pairs with one of the two symbols differentiated, so the full symbol estimates
follow by the same induction on the number of derivatives as for `a # b`
(`TauCeti.Symbol.exists_bound_mixedDeriv_of_leibniz`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.8.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (2.5)–(2.7).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

/-! ### The terms of the expansion -/

/-- The `k`-th term `(-i)ᵏ / k! ∑_{|r| = k} ∂_ξ^r a ∘ ∂_x^r b` of the asymptotic expansion of the
composition symbol `a # b`, a symbol of order `m' + m - k`. The sum runs over the words `r` of
length `k`, so in multi-index notation it is `∑_{|γ| = k} (1 / i)^{|γ|} / γ! ∂_ξ^γ a ∘ ∂_x^γ b`. -/
def sharpTerm (k : ℕ) (a : Symbol n W U m') (b : Symbol n V W m) : Symbol n V U (m' + m - k) :=
  inclusion (le_of_eq (by ring))
    (((-Complex.I) ^ k / k.factorial) •
      ∑ r : Fin k → Fin n, (iteratedFrequencyDeriv r a).comp (iteratedSpatialDeriv r b))

@[simp]
theorem coefficient_sharpTerm (k : ℕ) (a : Symbol n W U m') (b : Symbol n V W m)
    (x ξ : CoordinateSpace n) :
    (sharpTerm k a b).coefficient (x, ξ) = ((-Complex.I) ^ k / k.factorial) •
      ∑ r : Fin k → Fin n, (mixedDeriv [] (List.ofFn r) a.coefficient x ξ).comp
        (mixedDeriv (List.ofFn r) [] b.coefficient x ξ) := by
  simp [sharpTerm, coefficient_comp]

/-- The leading term of the expansion is the pointwise composition. -/
@[simp]
theorem sharpTerm_zero (a : Symbol n W U m') (b : Symbol n V W m) :
    sharpTerm 0 a b = inclusion (by simp) (a.comp b) := by
  ext1
  funext ⟨x, ξ⟩
  simp [coefficient_sharpTerm, coefficient_comp]

/-- **Leibniz rule in the position** for the terms of the expansion. -/
theorem spatialDeriv_sharpTerm (k : ℕ) (a : Symbol n W U m') (b : Symbol n V W m) (j : Fin n) :
    spatialDeriv j (sharpTerm k a b) =
      sharpTerm k (spatialDeriv j a) b + sharpTerm k a (spatialDeriv j b) := by
  ext1
  funext ⟨x, ξ⟩
  rw [coefficient_spatialDeriv]
  simp only [sharpTerm, coefficient_inclusion]
  rw [← coefficient_spatialDeriv]
  simp only [map_smul, map_sum, spatialDeriv_comp, spatialDeriv_iteratedFrequencyDeriv,
    spatialDeriv_iteratedSpatialDeriv, Finset.sum_add_distrib, smul_add, coefficient_add,
    coefficient_smul, coefficient_sum, coefficient_inclusion, Pi.add_apply]

/-- **Leibniz rule in the frequency** for the terms of the expansion. The orders
`m' - 1 + m - k` and `m' + (m - 1) - k` of the two terms are identified with the order
`m' + m - k - 1` of the left side through `Symbol.inclusion`. -/
theorem frequencyDeriv_sharpTerm (k : ℕ) (a : Symbol n W U m') (b : Symbol n V W m) (j : Fin n) :
    frequencyDeriv j (sharpTerm k a b) =
      inclusion (by linarith) (sharpTerm k (frequencyDeriv j a) b) +
        inclusion (by linarith) (sharpTerm k a (frequencyDeriv j b)) := by
  ext1
  funext ⟨x, ξ⟩
  rw [coefficient_frequencyDeriv]
  simp only [sharpTerm, coefficient_inclusion]
  rw [← coefficient_frequencyDeriv]
  simp only [map_smul, map_sum, frequencyDeriv_comp, Finset.sum_add_distrib, smul_add,
    coefficient_add, coefficient_smul, coefficient_sum, coefficient_inclusion, Pi.add_apply,
    Pi.smul_apply, Finset.sum_apply, coefficient_comp, frequencyDeriv_iteratedFrequencyDeriv,
    frequencyDeriv_iteratedSpatialDeriv]

/-! ### The terms of the expansion as integrals -/

section Fourier

variable {b : Symbol n V W m}

/-- The integrand `exp(2πi ⟪η, x⟫) (∏ᵢ 2π η_{r i}) b̂(η, ξ)` is `(-i)ᵏ` times the Fourier inversion
integrand of `∂_x^r b`. -/
private theorem fourierChar_smul_prod_smul_fourier_slice (hb : b.HasCompactSpatialSupport)
    {k : ℕ} (r : Fin k → Fin n) (x ξ η : CoordinateSpace n) :
    (𝐞 ⟪η, x⟫ : ℂ) • ((∏ i, 2 * π * η (r i)) • 𝓕 (fun y ↦ b.coefficient (y, ξ)) η) =
      (-Complex.I) ^ k • 𝐞 ⟪η, x⟫ •
        𝓕 (fun y ↦ (iteratedSpatialDeriv r b).coefficient (y, ξ)) η := by
  have hI : (-Complex.I) ^ k * Complex.I ^ k = 1 := by
    rw [← mul_pow]
    simp
  have hP : ∏ i, (2 * π * Complex.I * (⟪η, EuclideanSpace.single (r i) (1 : ℝ)⟫ : ℂ)) =
      Complex.I ^ k * ((∏ i, 2 * π * η (r i) : ℝ) : ℂ) := by
    simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul, Complex.ofReal_prod,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ ↦ by ring
  rw [hb.fourier_iteratedSpatialDeriv_slice, Circle.smul_def, ← Complex.coe_smul, smul_smul,
    smul_smul, smul_smul]
  congr 1
  rw [hP]
  linear_combination -(↑(𝐞 ⟪η, x⟫) * ((∏ i, 2 * π * η (r i) : ℝ) : ℂ)) * hI

/-- The `k`-th Taylor term `exp(2πi ⟪η, x⟫) (1 / k!) D^k_ξ a(x, ξ) (2πη, …, 2πη) ∘ b̂(η, ξ)` of the
integrand of `a # b`. -/
private def taylorTerm (a : Symbol n W U m') (b : Symbol n V W m) (k : ℕ)
    (x ξ η : CoordinateSpace n) : V →L[ℂ] U :=
  (𝐞 ⟪η, x⟫ : ℂ) • (((k.factorial : ℝ)⁻¹ •
    iteratedFDeriv ℝ k (fun ζ ↦ a.coefficient (x, ζ)) ξ fun _ ↦ (2 * π) • η).comp
      (𝓕 (fun y ↦ b.coefficient (y, ξ)) η))

/-- The `k`-th Taylor term of the integrand of `a # b` is integrable, with integral the `k`-th
term of the expansion. Expanding `D^k_ξ a(x, ξ) (2πη, …, 2πη)` in the standard basis, each
monomial `∏ᵢ 2π η_{r i}` turns `b̂` into `(-i)ᵏ` times the Fourier transform of `∂_x^r b`, whose
Fourier inversion integral is `∂_x^r b(x, ξ)`. -/
private theorem integrable_taylorTerm_and_integral_eq [CompleteSpace W] [CompleteSpace U]
    {a : Symbol n W U m'}
    (hb : b.HasCompactSpatialSupport) (k : ℕ) (x ξ : CoordinateSpace n) :
    Integrable (taylorTerm a b k x ξ) ∧
      ∫ η, taylorTerm a b k x ξ η = (sharpTerm k a b).coefficient (x, ξ) := by
  set D : (Fin k → Fin n) → W →L[ℂ] U := fun r ↦ mixedDeriv [] (List.ofFn r) a.coefficient x ξ
  set g : (Fin k → Fin n) → CoordinateSpace n → V →L[ℂ] W :=
    fun r η ↦ 𝐞 ⟪η, x⟫ • 𝓕 (fun y ↦ (iteratedSpatialDeriv r b).coefficient (y, ξ)) η
  have hg (r : Fin k → Fin n) : Integrable (g r) :=
    (hb.iteratedSpatialDeriv r).integrable_fourierChar_smul_fourier_slice x ξ
  have hD (r : Fin k → Fin n) : iteratedFDeriv ℝ k (fun ζ ↦ a.coefficient (x, ζ)) ξ
      (fun i ↦ EuclideanSpace.single (r i) 1) = D r := by
    rw [← coordinateDeriv_ofFn_eq_iteratedFDeriv r (f := fun ζ ↦ a.coefficient (x, ζ))
      ((a.contDiff_coefficient.comp (contDiff_prodMk_right x)).of_le (mod_cast le_top))]
    simp only [D, mixedDeriv_def, coordinateDeriv_nil]
  have hexp (η : CoordinateSpace n) : taylorTerm a b k x ξ η =
      ∑ r, ((k.factorial : ℂ)⁻¹ * (-Complex.I) ^ k) •
        ContinuousLinearMap.compL ℂ V W U (D r) (g r η) := by
    set Φ : (W →L[ℂ] U) →L[ℂ] V →L[ℂ] U :=
      (ContinuousLinearMap.compL ℂ V W U).flip (𝓕 (fun y ↦ b.coefficient (y, ξ)) η)
    have hΦ (X : W →L[ℂ] U) : X.comp (𝓕 (fun y ↦ b.coefficient (y, ξ)) η) = Φ X := by simp [Φ]
    rw [taylorTerm, hΦ, ContinuousMultilinearMap.apply_eq_sum_single]
    simp only [hD, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    calc (𝐞 ⟪η, x⟫ : ℂ) • Φ ((k.factorial : ℝ)⁻¹ • (∏ i, ((2 * π) • η) (r i)) • D r)
        = (k.factorial : ℂ)⁻¹ • ContinuousLinearMap.compL ℂ V W U (D r)
            ((𝐞 ⟪η, x⟫ : ℂ) • ((∏ i, 2 * π * η (r i)) • 𝓕 (fun y ↦ b.coefficient (y, ξ)) η)) := by
          simp only [Φ, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
            ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, PiLp.smul_apply,
            smul_eq_mul]
          rw [smul_comm, ← Complex.coe_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
      _ = _ := by
          rw [fourierChar_smul_prod_smul_fourier_slice hb r x ξ η, map_smul, smul_smul]
  set F : (Fin k → Fin n) → CoordinateSpace n → V →L[ℂ] U := fun r η ↦
    ((k.factorial : ℂ)⁻¹ * (-Complex.I) ^ k) • ContinuousLinearMap.compL ℂ V W U (D r) (g r η)
  have hint (r : Fin k → Fin n) : Integrable (F r) :=
    ((ContinuousLinearMap.compL ℂ V W U (D r)).integrable_comp (hg r)).smul
      ((k.factorial : ℂ)⁻¹ * (-Complex.I) ^ k)
  have hT : taylorTerm a b k x ξ = fun η ↦ ∑ r, F r η := funext hexp
  rw [hT]
  refine ⟨integrable_finsetSum (f := F) _ fun r _ ↦ hint r, ?_⟩
  rw [integral_finsetSum (f := F) _ fun r _ ↦ hint r, coefficient_sharpTerm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [integral_smul, ContinuousLinearMap.integral_comp_comm _ (hg r),
    (hb.iteratedSpatialDeriv r).integral_fourierChar_smul_fourier_slice,
    coefficient_iteratedSpatialDeriv, ContinuousLinearMap.compL_apply,
    div_eq_inv_mul]

/-- **Taylor's formula** for the integrand of `a # b`: after the first `M + 1` Taylor terms of
`a(x, ξ + 2πη)` in the frequency, the integral remainder
`(1 / M!) ∫₀¹ (1 - t)ᴹ D^{M+1}_ξ a(x, ξ + 2πtη) (2πη, …, 2πη) dt` remains. -/
private theorem sharpIntegrand_sub_sum_taylorTerm [CompleteSpace U] (a : Symbol n W U m')
    (b : Symbol n V W m) (M : ℕ) (x ξ η : CoordinateSpace n) :
    (𝐞 ⟪η, x⟫ : ℂ) • (a.coefficient (x, ξ + (2 * π) • η)).comp
        (𝓕 (fun y ↦ b.coefficient (y, ξ)) η) -
      ∑ k ∈ Finset.range (M + 1), taylorTerm a b k x ξ η =
    (𝐞 ⟪η, x⟫ : ℂ) • (((M.factorial : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1, (1 - t) ^ M •
      iteratedFDeriv ℝ (M + 1) (fun ζ ↦ a.coefficient (x, ζ)) (ξ + t • (2 * π) • η)
        fun _ ↦ (2 * π) • η).comp (𝓕 (fun y ↦ b.coefficient (y, ξ)) η)) := by
  set Φ : (W →L[ℂ] U) →L[ℂ] V →L[ℂ] U :=
    (ContinuousLinearMap.compL ℂ V W U).flip (𝓕 (fun y ↦ b.coefficient (y, ξ)) η)
  have hΦ (X : W →L[ℂ] U) : X.comp (𝓕 (fun y ↦ b.coefficient (y, ξ)) η) = Φ X := by simp [Φ]
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (f := fun ζ ↦ a.coefficient (x, ζ))
    (x := ξ) (y := (2 * π) • η) (n := M) fun t _ ↦
      ((a.contDiff_coefficient.comp (contDiff_prodMk_right x)).of_le (mod_cast le_top)).contDiffAt
  simp only [taylorTerm, hΦ, ← Finset.smul_sum, ← smul_sub, ← map_sum, ← map_sub]
  rw [h, add_sub_cancel_left]

/-- The Taylor remainder of the integrand of `a # b` after `M + 1` terms is bounded by
`C ⟨ξ⟩ ^ (m' + m - (M + 1)) ⟨η⟩ ^ (-(n + 1))`, uniformly for positions in a compact set: the
`(M + 1)`-st frequency derivative of `a` has order `m' - (M + 1)`, Peetre's inequality moves its
weight from `ξ + 2πtη` to `ξ` at the cost of a power of `⟨η⟩`, and the rapid decay of `b̂` in `η`
absorbs that power and the factor `‖2πη‖ ^ (M + 1)`. -/
private theorem exists_norm_sharpIntegrand_sub_sum_taylorTerm_le [CompleteSpace U]
    (a : Symbol n W U m') (hb : b.HasCompactSpatialSupport) (M : ℕ) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) : ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ η,
      ‖(𝐞 ⟪η, x⟫ : ℂ) • (a.coefficient (x, ξ + (2 * π) • η)).comp
          (𝓕 (fun y ↦ b.coefficient (y, ξ)) η) -
        ∑ k ∈ Finset.range (M + 1), taylorTerm a b k x ξ η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - (M + 1 : ℕ)) / 2) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  set s : ℝ := m' - (M + 1 : ℕ)
  obtain ⟨G, hG0, hG⟩ := a.exists_norm_iteratedFDeriv_coordinateDeriv_le hK [] (M + 1)
  simp only [coordinateDeriv_nil] at hG
  obtain ⟨Cb, hCb0, hCb⟩ := hb.exists_norm_fourier_slice_le (|s| + (M + 1 : ℕ) + ((n : ℝ) + 1))
  have h2π : (1 : ℝ) ≤ 2 * π := by linarith [Real.two_le_pi]
  refine ⟨G * 2 ^ (|s| / 2) * (2 * π) ^ |s| * (2 * π) ^ (M + 1) * Cb, by positivity,
    fun x hx ξ η ↦ ?_⟩
  -- Write the remainder with Taylor's formula, bound the integral remainder pointwise in `t`
  -- (`hpt`, `hint`), then multiply by the decay of `b̂` and collect the powers of the weights.
  rw [sharpIntegrand_sub_sum_taylorTerm]
  set y : CoordinateSpace n := (2 * π) • η
  have hy : ‖y‖ = 2 * π * ‖η‖ := by rw [norm_smul, Real.norm_of_nonneg Real.two_pi_pos.le]
  -- The weight of the derivative of `a` along the segment from `ξ` to `ξ + y`.
  have hweight (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (1 + ‖ξ + t • y‖ ^ 2) ^ (s / 2) ≤
      2 ^ (|s| / 2) * (1 + ‖ξ‖ ^ 2) ^ (s / 2) * ((2 * π) ^ |s| * (1 + ‖η‖ ^ 2) ^ (|s| / 2)) := by
    refine one_add_norm_add_sq_rpow_le_mul_of_norm_le_mul h2π s ξ ?_
    rw [norm_smul, Real.norm_of_nonneg ht0, ← hy]
    exact mul_le_of_le_one_left (norm_nonneg y) ht1
  set B : ℝ := G * (2 ^ (|s| / 2) * (1 + ‖ξ‖ ^ 2) ^ (s / 2) *
    ((2 * π) ^ |s| * (1 + ‖η‖ ^ 2) ^ (|s| / 2))) *
      ((2 * π) ^ (M + 1) * (1 + ‖η‖ ^ 2) ^ (((M + 1 : ℕ) : ℝ) / 2)) with hB
  have hpt : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖(1 - t) ^ M •
      iteratedFDeriv ℝ (M + 1) (fun ζ ↦ a.coefficient (x, ζ)) (ξ + t • y) (fun _ ↦ y)‖ ≤ B := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    calc ‖(1 - t) ^ M •
          iteratedFDeriv ℝ (M + 1) (fun ζ ↦ a.coefficient (x, ζ)) (ξ + t • y) fun _ ↦ y‖
        ≤ ‖iteratedFDeriv ℝ (M + 1) (fun ζ ↦ a.coefficient (x, ζ)) (ξ + t • y)‖ *
            ‖y‖ ^ (M + 1) := by
          rw [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
          refine (mul_le_of_le_one_left (norm_nonneg _)
            (pow_le_one₀ (by linarith [ht.2]) (by linarith [ht.1]))).trans ?_
          refine (ContinuousMultilinearMap.le_opNorm
            (iteratedFDeriv ℝ (M + 1) (fun ζ ↦ a.coefficient (x, ζ)) (ξ + t • y))
              fun _ ↦ y).trans_eq ?_
          simp
      _ ≤ (G * (1 + ‖ξ + t • y‖ ^ 2) ^ (s / 2)) *
            ((2 * π) ^ (M + 1) * (1 + ‖η‖ ^ 2) ^ (((M + 1 : ℕ) : ℝ) / 2)) := by
          gcongr
          · exact hG x hx _
          · rw [hy, mul_pow]
            gcongr
            exact norm_pow_le_one_add_norm_sq_rpow η (M + 1)
      _ ≤ B := by
          rw [hB]
          gcongr
          exact hweight t ht.1.le ht.2
  have hint : ‖∫ t in (0 : ℝ)..1, (1 - t) ^ M •
      iteratedFDeriv ℝ (M + 1) (fun ζ ↦ a.coefficient (x, ζ)) (ξ + t • y) fun _ ↦ y‖ ≤ B := by
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const hpt
  have hξ : (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) =
      (1 + ‖ξ‖ ^ 2) ^ ((m' + m - (M + 1 : ℕ)) / 2) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  have hη : (1 + ‖η‖ ^ 2) ^ (|s| / 2) * (1 + ‖η‖ ^ 2) ^ (((M + 1 : ℕ) : ℝ) / 2) *
      (1 + ‖η‖ ^ 2) ^ (-(|s| + (M + 1 : ℕ) + ((n : ℝ) + 1)) / 2) =
        (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
    rw [← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]
    congr 1
    ring
  have hfact : ‖((M.factorial : ℝ)⁻¹ : ℝ)‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (mod_cast M.factorial_pos)
  calc ‖(𝐞 ⟪η, x⟫ : ℂ) • (((M.factorial : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1, (1 - t) ^ M •
        iteratedFDeriv ℝ (M + 1) (fun ζ ↦ a.coefficient (x, ζ)) (ξ + t • y) fun _ ↦ y).comp
          (𝓕 (fun y ↦ b.coefficient (y, ξ)) η))‖
      ≤ ‖∫ t in (0 : ℝ)..1, (1 - t) ^ M •
          iteratedFDeriv ℝ (M + 1) (fun ζ ↦ a.coefficient (x, ζ)) (ξ + t • y) fun _ ↦ y‖ *
          ‖𝓕 (fun y ↦ b.coefficient (y, ξ)) η‖ := by
        rw [norm_smul, Circle.norm_coe, one_mul]
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        rw [norm_smul]
        exact mul_le_of_le_one_left (norm_nonneg _) hfact
    _ ≤ B * (Cb * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
          (1 + ‖η‖ ^ 2) ^ (-(|s| + (M + 1 : ℕ) + ((n : ℝ) + 1)) / 2)) := by
        gcongr
        exact hCb η ξ
    _ = G * 2 ^ (|s| / 2) * (2 * π) ^ |s| * (2 * π) ^ (M + 1) * Cb *
          ((1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) *
          ((1 + ‖η‖ ^ 2) ^ (|s| / 2) * (1 + ‖η‖ ^ 2) ^ (((M + 1 : ℕ) : ℝ) / 2) *
            (1 + ‖η‖ ^ 2) ^ (-(|s| + (M + 1 : ℕ) + ((n : ℝ) + 1)) / 2)) := by rw [hB]; ring
    _ = _ := by rw [hξ, hη]

end Fourier

/-! ### The remainder of the expansion -/

section Remainder

/-- The remainder `a # b - ∑_{k < N} (sharpTerm k a b)` after `N` terms of the expansion, as a
symbol of order `m' + m`. -/
private def expansionRemainder (N : ℕ) (a : Symbol n W U m') {b : Symbol n V W m}
    (hb : b.HasCompactSpatialSupport) : Symbol n V U (m' + m) :=
  a.sharp b hb - ∑ k ∈ Finset.range N,
    inclusion (sub_le_self _ (Nat.cast_nonneg k)) (sharpTerm k a b)

private theorem coefficient_expansionRemainder (N : ℕ) (a : Symbol n W U m')
    {b : Symbol n V W m} (hb : b.HasCompactSpatialSupport) :
    (expansionRemainder N a hb).coefficient =
      (a.sharp b hb).coefficient - ∑ k ∈ Finset.range N, (sharpTerm k a b).coefficient := by
  simp [expansionRemainder]

/-- **Leibniz rule in the position** for the remainder. -/
private theorem coordinateDeriv_fst_coefficient_expansionRemainder (N : ℕ) (a : Symbol n W U m')
    {b : Symbol n V W m} (hb : b.HasCompactSpatialSupport) (j : Fin n) (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun y ↦ (expansionRemainder N a hb).coefficient (y, ξ)) x =
      (expansionRemainder N (spatialDeriv j a) hb).coefficient (x, ξ) +
        (expansionRemainder N a (hb.spatialDeriv j)).coefficient (x, ξ) := by
  rw [← coefficient_spatialDeriv, ← Pi.add_apply, ← coefficient_add]
  congr 1
  simp only [expansionRemainder, map_sub, map_sum, spatialDeriv_sharp, spatialDeriv_inclusion,
    spatialDeriv_sharpTerm, map_add, Finset.sum_add_distrib]
  abel

/-- **Leibniz rule in the frequency** for the remainder. -/
private theorem coordinateDeriv_snd_coefficient_expansionRemainder (N : ℕ) (a : Symbol n W U m')
    {b : Symbol n V W m} (hb : b.HasCompactSpatialSupport) (j : Fin n) (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun ζ ↦ (expansionRemainder N a hb).coefficient (x, ζ)) ξ =
      (expansionRemainder N (frequencyDeriv j a) hb).coefficient (x, ξ) +
        (expansionRemainder N a (hb.frequencyDeriv j)).coefficient (x, ξ) := by
  rw [← coefficient_frequencyDeriv]
  simp only [expansionRemainder, map_sub, map_sum, frequencyDeriv_inclusion, coefficient_sub,
    coefficient_sum, coefficient_inclusion, Pi.sub_apply, Finset.sum_apply,
    coefficient_frequencyDeriv_sharp, frequencyDeriv_sharpTerm, coefficient_add, Pi.add_apply,
    Finset.sum_add_distrib]
  abel

variable [CompleteSpace W] [CompleteSpace U]

/-- The pointwise bound `‖r_N(x, ξ)‖ ≤ C ⟨ξ⟩ ^ (m' + m - N)` on the remainder, for positions in
a compact set. The remainder is the integral of the Taylor remainder of the integrand of
`a # b`. -/
private theorem exists_norm_coefficient_expansionRemainder_le (N : ℕ) (a : Symbol n W U m')
    {b : Symbol n V W m} (hb : b.HasCompactSpatialSupport) {K : Set (CoordinateSpace n)}
    (hK : IsCompact K) : ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖(expansionRemainder N a hb).coefficient (x, ξ)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - N) / 2) := by
  cases N with
  | zero =>
    obtain ⟨C, hC0, hC⟩ := (a.sharp b hb).exists_bound_coefficient K hK
    exact ⟨C, hC0, fun x hx ξ ↦ by simpa [coefficient_expansionRemainder] using hC x hx ξ⟩
  | succ M =>
    obtain ⟨C, hC0, hC⟩ := exists_norm_sharpIntegrand_sub_sum_taylorTerm_le a hb M hK
    have hw : Integrable fun η : CoordinateSpace n ↦ (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) :=
      integrable_rpow_neg_one_add_norm_sq (by rw [finrank_euclideanSpace_fin]; linarith)
    set I := ∫ η : CoordinateSpace n, (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
    have hI : 0 ≤ I := integral_nonneg fun η ↦ by positivity
    refine ⟨C * I, mul_nonneg hC0 hI, fun x hx ξ ↦ ?_⟩
    have hT (k : ℕ) := integrable_taylorTerm_and_integral_eq (a := a) hb k x ξ
    have hA := integrable_coefficient_sharp_integrand (a := a) hb x ξ
    have heq : (expansionRemainder (M + 1) a hb).coefficient (x, ξ) =
        ∫ η, ((𝐞 ⟪η, x⟫ : ℂ) • (a.coefficient (x, ξ + (2 * π) • η)).comp
          (𝓕 (fun y ↦ b.coefficient (y, ξ)) η) -
            ∑ k ∈ Finset.range (M + 1), taylorTerm a b k x ξ η) := by
      rw [coefficient_expansionRemainder, Pi.sub_apply, Finset.sum_apply, coefficient_sharp,
        integral_sub hA (integrable_finsetSum _ fun k _ ↦ (hT k).1),
        integral_finsetSum _ fun k _ ↦ (hT k).1]
      exact congrArg _ (Finset.sum_congr rfl fun k _ ↦ (hT k).2.symm)
    rw [heq]
    refine (norm_integral_le_of_norm_le (hw.const_mul
      (C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - (M + 1 : ℕ)) / 2)))
        (.of_forall fun η ↦ hC x hx ξ η)).trans_eq ?_
    rw [integral_const_mul]
    ring

/-- **The composition expansion.** For a symbol `a` of order `m'` and a symbol `b` of order `m`
with compact spatial support, the composition symbol has the asymptotic expansion

`a # b ∼ ∑ₖ (-i)ᵏ / k! ∑_{|r| = k} ∂_ξ^r a ∘ ∂_x^r b`:

for every `N`, the remainder `a # b - ∑_{k < N} sharpTerm k a b` after `N` terms is a symbol of
order `m' + m - N`. -/
theorem exists_sharp_sub_sum_sharpTerm (a : Symbol n W U m') {b : Symbol n V W m}
    (hb : b.HasCompactSpatialSupport) (N : ℕ) : ∃ r : Symbol n V U (m' + m - N),
      (a.sharp b hb).coefficient - ∑ k ∈ Finset.range N, (sharpTerm k a b).coefficient =
        r.coefficient :=
  ⟨⟨(expansionRemainder N a hb).coefficient, (expansionRemainder N a hb).contDiff_coefficient,
    fun _ hK α β ↦ exists_bound_mixedDeriv_of_leibniz N
      (fun a _ hb ↦ (expansionRemainder N a hb).coefficient)
      (fun a _ hb ↦ (expansionRemainder N a hb).contDiff_coefficient)
      (fun a _ hb ↦ coordinateDeriv_fst_coefficient_expansionRemainder N a hb)
      (fun a _ hb ↦ coordinateDeriv_snd_coefficient_expansionRemainder N a hb)
      (fun a _ hb _ hK ↦ exists_norm_coefficient_expansionRemainder_le N a hb hK) a b hb α β hK⟩,
    (coefficient_expansionRemainder N a hb).symm⟩

/-- **The leading symbol of a composition.** For a symbol `a` of order `m'` and a symbol `b` of
order `m` with compact spatial support, `a # b - a ∘ b` is a symbol of order `m' + m - 1`. -/
theorem exists_sharp_sub_comp (a : Symbol n W U m') {b : Symbol n V W m}
    (hb : b.HasCompactSpatialSupport) : ∃ r : Symbol n V U (m' + m - 1),
      (a.sharp b hb).coefficient - (a.comp b).coefficient = r.coefficient := by
  obtain ⟨r, hr⟩ := exists_sharp_sub_sum_sharpTerm a hb 1
  refine ⟨inclusion (by simp) r, ?_⟩
  rw [coefficient_inclusion, ← hr, Finset.sum_range_one, sharpTerm_zero, coefficient_inclusion]

end Remainder

end Symbol

end TauCeti

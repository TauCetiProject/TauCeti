/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
public import TauCeti.Analysis.Pseudodifferential.AsymptoticSum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.Inversion
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# The asymptotic expansion of the composition symbol

Let `a` be a symbol of order `m'` with values in `W →L[ℂ] U` and `b` a symbol of order `m` with
values in `V →L[ℂ] W` and compact spatial support. Their composition symbol `a # b`
(`TauCeti.Symbol.sharp`), whose quantization is the composition of the quantizations of `a` and
`b`, has the asymptotic expansion

`a # b ∼ ∑_α (1 / α!) ∂_ξ^α a D_x^α b`, with `D_x = -i ∂_x`.

This file proves the expansion with an actual remainder symbol after every number of terms:

* `TauCeti.Symbol.sharpTerm a b k`: the term `((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b` of
  order `m' + m - k`, the sum running over the words `w` of coordinate indices of length `k`
  (`TauCeti.Symbol.coefficient_sharpTerm`). Grouping the words by the multi-index they determine
  gives the sum over `|α| = k` above. The leading term `sharpTerm a b 0` is the pointwise
  composition `a.comp b`, and the next one is `-i ∑ⱼ ∂_{ξⱼ} a ∘ ∂_{xⱼ} b`
  (`TauCeti.Symbol.coefficient_sharpTerm_one`). Derivatives satisfy the Leibniz rule for the terms
  (`TauCeti.Symbol.spatialDeriv_sharpTerm`, `TauCeti.Symbol.coefficient_frequencyDeriv_sharpTerm`).
* `TauCeti.Symbol.sharpRemainder a b hb N`: the remainder `a # b - ∑_{k < N} sharpTerm a b k`, a
  symbol of order `m' + m - N`.
* `TauCeti.Symbol.sharp_eq_sum_sharpTerm_add_sharpRemainder`: **the composition expansion**,
  `a # b = ∑_{k < N} sharpTerm a b k + sharpRemainder a b hb N` for every `N`. In particular
  `a # b - a ∘ b` has order `m' + m - 1` (`TauCeti.Symbol.sharp_eq_comp_add_sharpRemainder_one`),
  and `a # b` is an asymptotic sum of the terms (`TauCeti.Symbol.isAsymptoticSum_sharp`), which
  determines it modulo smoothing symbols.

## Proof outline

Write `b̂(η, ξ)` for the Fourier transform of the position slice `y ↦ b(y, ξ)`. For a real
parameter `t` consider

`C_t(x, ξ) = ∫ exp(2πi ⟪η, x⟫) a(x, ξ + 2πtη) ∘ b̂(η, ξ) dη`,

so that `C_1 = a # b` by definition and `C_0 = a ∘ b` by Fourier inversion. Since
`(∂_{x_j} b)^(η, ξ) = 2πi ηⱼ b̂(η, ξ)`, differentiating under the integral sign gives
`d/dt C_t(a, b) = -i ∑ⱼ C_t(∂_{ξⱼ} a, ∂_{xⱼ} b)`. The terms satisfy the matching recursion
`sharpTerm a b (k + 1) = (-i / (k + 1)) ∑ⱼ sharpTerm (∂_{ξⱼ} a) (∂_{xⱼ} b) k`, so the remainder
`R_N(t)(a, b) = C_t(a, b) - ∑_{k < N} t^k sharpTerm a b k` satisfies
`d/dt R_{N+1}(t)(a, b) = -i ∑ⱼ R_N(t)(∂_{ξⱼ} a, ∂_{xⱼ} b)` and `R_{N+1}(0) = 0`. The mean value
theorem and induction on `N` bound `R_N(t)` by `C ⟨ξ⟩ ^ (m' + m - N)` for positions in a compact
set, uniformly for `t ∈ [0, 1]`; the case `N = 0` is the rapid decay of `b̂` in `η` together with
Peetre's inequality. Derivatives obey the Leibniz rule both for `a # b` and for the terms, so every
mixed derivative of the remainder is a sum of remainders for derivatives of `a` and `b`, which gives
the symbol estimates of order `m' + m - N`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (2.5)–(2.7).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.8.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Finset
open scoped RealInnerProductSpace ContDiff SchwartzMap

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

/-! ### The terms of the expansion -/

section Term

/-- The term of order `m' + m - k` in the asymptotic expansion of the composition symbol:
`((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b`, the sum running over the words `w` of coordinate
indices of length `k` (`coefficient_sharpTerm`). It is defined by the recursion
`sharpTerm a b (k + 1) = (-i / (k + 1)) ∑ⱼ sharpTerm (∂_{ξⱼ} a) (∂_{xⱼ} b) k`, starting from the
pointwise composition `sharpTerm a b 0 = a ∘ b`. -/
def sharpTerm : {m' m : ℝ} → Symbol n W U m' → Symbol n V W m → (k : ℕ) →
    Symbol n V U (m' + m - k)
  | _, _, a, b, 0 => inclusion (by simp) (a.comp b)
  | _, _, a, b, k + 1 => inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, sharpTerm (frequencyDeriv j a) (spatialDeriv j b) k)

theorem sharpTerm_zero (a : Symbol n W U m') (b : Symbol n V W m) :
    a.sharpTerm b 0 = inclusion (by simp) (a.comp b) := by
  rw [sharpTerm]

theorem sharpTerm_succ (a : Symbol n W U m') (b : Symbol n V W m) (k : ℕ) :
    a.sharpTerm b (k + 1) = inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, (frequencyDeriv j a).sharpTerm (spatialDeriv j b) k) := by
  rw [sharpTerm]

@[simp]
theorem coefficient_sharpTerm_zero (a : Symbol n W U m') (b : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.sharpTerm b 0).coefficient p = (a.coefficient p).comp (b.coefficient p) := by
  rw [sharpTerm_zero, coefficient_inclusion, coefficient_comp]

theorem coefficient_sharpTerm_succ (a : Symbol n W U m') (b : Symbol n V W m) (k : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.sharpTerm b (k + 1)).coefficient p = (-Complex.I / (k + 1)) •
      ∑ j, ((frequencyDeriv j a).sharpTerm (spatialDeriv j b) k).coefficient p := by
  simp [sharpTerm_succ]

/-- The first correction term of the composition expansion is `-i ∑ⱼ ∂_{ξⱼ} a ∘ ∂_{xⱼ} b`. -/
theorem coefficient_sharpTerm_one (a : Symbol n W U m') (b : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.sharpTerm b 1).coefficient p = (-Complex.I) •
      ∑ j, ((frequencyDeriv j a).coefficient p).comp ((spatialDeriv j b).coefficient p) := by
  simp [coefficient_sharpTerm_succ]

/-- **The terms of the composition expansion** are `((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b`,
the sum running over the words `w` of coordinate indices of length `k`. Grouping the words by the
multi-index they determine gives the familiar form `∑_{|α| = k} (1 / α!) ∂_ξ^α a D_x^α b` with
`D_x = -i ∂_x`. -/
theorem coefficient_sharpTerm (a : Symbol n W U m') (b : Symbol n V W m) (k : ℕ)
    (x ξ : CoordinateSpace n) :
    (a.sharpTerm b k).coefficient (x, ξ) = ((-Complex.I) ^ k / k.factorial) •
      ∑ w : Fin k → Fin n, (mixedDeriv [] (List.ofFn w) a.coefficient x ξ).comp
        (mixedDeriv (List.ofFn w) [] b.coefficient x ξ) := by
  induction k generalizing m m' with
  | zero => simp
  | succ k ih =>
    rw [coefficient_sharpTerm_succ, ← (Fin.snocEquiv fun _ ↦ Fin n).sum_comp,
      Fintype.sum_prod_type]
    simp only [ih, mixedDeriv_frequencyDeriv, mixedDeriv_spatialDeriv, Finset.smul_sum, smul_smul,
      Fin.snocEquiv_apply, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last,
      List.concat_eq_append]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- **Leibniz rule in the position** for the terms of the composition expansion. -/
theorem spatialDeriv_sharpTerm (l : Fin n) (a : Symbol n W U m') (b : Symbol n V W m) (k : ℕ) :
    spatialDeriv l (a.sharpTerm b k) =
      (spatialDeriv l a).sharpTerm b k + a.sharpTerm (spatialDeriv l b) k := by
  induction k generalizing m m' with
  | zero => simp only [sharpTerm_zero, spatialDeriv_inclusion, spatialDeriv_comp, map_add]
  | succ k ih =>
    simp only [sharpTerm_succ, spatialDeriv_inclusion, map_smul, map_sum, ih,
      spatialDeriv_frequencyDeriv_comm l, spatialDeriv_comm l, Finset.sum_add_distrib, smul_add,
      map_add]

/-- **Leibniz rule in the frequency** for the terms of the composition expansion. The orders of the
two sides differ syntactically, so the rule is stated for their coefficients. -/
theorem coefficient_frequencyDeriv_sharpTerm (l : Fin n) (a : Symbol n W U m')
    (b : Symbol n V W m) (k : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (frequencyDeriv l (a.sharpTerm b k)).coefficient p =
      ((frequencyDeriv l a).sharpTerm b k).coefficient p +
        (a.sharpTerm (frequencyDeriv l b) k).coefficient p := by
  induction k generalizing m m' with
  | zero =>
    simp only [sharpTerm_zero, frequencyDeriv_inclusion, frequencyDeriv_comp, map_add,
      coefficient_add, coefficient_inclusion, Pi.add_apply]
  | succ k ih =>
    simp only [sharpTerm_succ, frequencyDeriv_inclusion, map_smul, map_sum, coefficient_inclusion,
      coefficient_smul, coefficient_sum, Pi.smul_apply, Finset.sum_apply, ih,
      frequencyDeriv_comm l, ← spatialDeriv_frequencyDeriv_comm _ l, Finset.sum_add_distrib,
      smul_add]

end Term

/-! ### The interpolating family `C_t` -/

section Scaled

variable {a : Symbol n W U m'} {b : Symbol n V W m}

variable (a b) in
/-- The integrand `exp(2πi ⟪η, x⟫) a(x, ξ + sη) ∘ b̂(η, ξ)` of the interpolating family, with the
frequency shift `2πη` of the composition symbol scaled to `sη`. -/
private def shiftIntegrand (s : ℝ) (x ξ η : CoordinateSpace n) : V →L[ℂ] U :=
  (𝐞 ⟪η, x⟫ : ℂ) • (a.coefficient (x, ξ + s • η)).comp (𝓕 (fun y ↦ b.coefficient (y, ξ)) η)

/-- The integrand decays like `⟨η⟩ ^ (-(n + 1))`, with the weight `⟨ξ⟩ ^ (m' + m)` in the
frequency, uniformly for positions in a compact set and shifts `|s| ≤ 4π`. -/
private theorem exists_norm_shiftIntegrand_le (hb : b.HasCompactSpatialSupport)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ 4 * π → ∀ x ∈ K, ∀ ξ η : CoordinateSpace n,
      ‖shiftIntegrand a b s x ξ η‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  obtain ⟨Ca, hCa0, hCa⟩ := a.exists_bound_coefficient K hK
  obtain ⟨Cb, hCb0, hCb⟩ := hb.exists_norm_fourier_slice_le ((n : ℝ) + 1 + |m'|)
  refine ⟨Ca * 2 ^ (|m'| / 2) * (4 * π) ^ |m'| * Cb, by positivity, fun s hs x hx ξ η ↦ ?_⟩
  have h4π : (1 : ℝ) ≤ 4 * π := by linarith [Real.two_le_pi]
  have hpeetre := one_add_norm_add_sq_rpow_le_mul m' ξ (s • η)
  -- `⟨sη⟩ ^ |m'| ≤ (4π) ^ |m'| ⟨η⟩ ^ |m'|` since `‖sη‖ ≤ ‖4π η‖`.
  have hsη : (1 + ‖s • η‖ ^ 2) ^ (|m'| / 2) ≤ (4 * π) ^ |m'| * (1 + ‖η‖ ^ 2) ^ (|m'| / 2) := by
    have hle : ‖s • η‖ ≤ ‖(4 * π) • η‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
      gcongr
    have h := one_add_norm_smul_sq_rpow_le h4π |m'| η
    rw [abs_abs] at h
    exact (Real.rpow_le_rpow (by positivity) (by gcongr) (by positivity)).trans h
  have hξ : (1 + ‖ξ‖ ^ 2) ^ (m' / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) =
      (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  have hη : (1 + ‖η‖ ^ 2) ^ (|m'| / 2) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1 + |m'|) / 2) =
      (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  calc ‖shiftIntegrand a b s x ξ η‖
      ≤ ‖a.coefficient (x, ξ + s • η)‖ * ‖𝓕 (fun y ↦ b.coefficient (y, ξ)) η‖ := by
        rw [shiftIntegrand, norm_smul, Circle.norm_coe, one_mul]
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (Ca * (2 ^ (|m'| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m' / 2) *
          ((4 * π) ^ |m'| * (1 + ‖η‖ ^ 2) ^ (|m'| / 2)))) *
        (Cb * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1 + |m'|) / 2)) := by
        gcongr
        · refine (hCa x hx _).trans ?_
          gcongr
          exact hpeetre.trans (by gcongr)
        · exact hCb η ξ
    _ = Ca * 2 ^ (|m'| / 2) * (4 * π) ^ |m'| * Cb *
          ((1 + ‖ξ‖ ^ 2) ^ (m' / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) *
          ((1 + ‖η‖ ^ 2) ^ (|m'| / 2) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1 + |m'|) / 2)) := by ring
    _ = _ := by rw [hξ, hη]

private theorem continuous_shiftIntegrand (hb : b.HasCompactSpatialSupport) (s : ℝ)
    (x ξ : CoordinateSpace n) : Continuous (shiftIntegrand a b s x ξ) := by
  have hB : Continuous fun η : CoordinateSpace n ↦ 𝓕 (fun y ↦ b.coefficient (y, ξ)) η := by
    have h := hb.continuous_fourier_slice.comp
      (continuous_id'.prodMk continuous_const : Continuous fun η : CoordinateSpace n ↦ (η, ξ))
    simpa only [Function.comp_def] using h
  have ha : Continuous fun η : CoordinateSpace n ↦ a.coefficient (x, ξ + s • η) :=
    a.contDiff_coefficient.continuous.comp (by fun_prop)
  have he : Continuous fun η : CoordinateSpace n ↦ (𝐞 ⟪η, x⟫ : ℂ) := by fun_prop
  unfold shiftIntegrand
  exact he.smul (ha.clm_comp hB)

private theorem integrable_shiftIntegrand (hb : b.HasCompactSpatialSupport) {s : ℝ}
    (hs : |s| ≤ 4 * π) (x ξ : CoordinateSpace n) : Integrable (shiftIntegrand a b s x ξ) := by
  obtain ⟨C, -, hC⟩ := exists_norm_shiftIntegrand_le (a := a) hb (isCompact_singleton (x := x))
  exact ((integrable_rpow_neg_one_add_norm_sq (by simp)).const_mul _).mono'
    (continuous_shiftIntegrand hb s x ξ).aestronglyMeasurable
    (.of_forall fun η ↦ hC s hs x rfl ξ η)

/-- The frequency shifts `2πtη` of the family with `|t| ≤ 2` are at most `4π ‖η‖`. -/
private theorem abs_mul_two_pi_le {t : ℝ} (ht : |t| ≤ 2) : |t * (2 * π)| ≤ 4 * π := by
  rw [abs_mul, abs_of_pos two_pi_pos]
  nlinarith [pi_pos]

/-- **Differentiation in the parameter** of the integrand: since `2π ηⱼ b̂ = -i (∂_{xⱼ} b)^`,
`d/dt` of the integrand of `C_t(a, b)` is `-i ∑ⱼ` the integrand of `C_t(∂_{ξⱼ} a, ∂_{xⱼ} b)`. -/
private theorem hasDerivAt_shiftIntegrand (hb : b.HasCompactSpatialSupport) (t : ℝ)
    (x ξ η : CoordinateSpace n) :
    HasDerivAt (fun t ↦ shiftIntegrand a b (t * (2 * π)) x ξ η)
      (∑ j, (-Complex.I) •
        shiftIntegrand (frequencyDeriv j a) (spatialDeriv j b) (t * (2 * π)) x ξ η) t := by
  have hD : HasFDerivAt (fun ζ ↦ a.coefficient (x, ζ))
      (fderiv ℝ (fun ζ ↦ a.coefficient (x, ζ)) (ξ + (t * (2 * π)) • η))
      (ξ + (t * (2 * π)) • η) :=
    ((a.contDiff_coefficient.comp (contDiff_prodMk_right x)).differentiable (by simp)
      _).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ ↦ ξ + (t * (2 * π)) • η) ((2 * π) • η) t := by
    simpa using (((hasDerivAt_id t).mul_const (2 * π)).smul_const η).const_add ξ
  set Ψ : (W →L[ℂ] U) →L[ℝ] (V →L[ℂ] U) :=
    ((ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ).flip
      (𝓕 (fun y ↦ b.coefficient (y, ξ)) η)
  have h := (Ψ.hasFDerivAt.comp_hasDerivAt t (hD.comp_hasDerivAt t hl)).const_smul
    (𝐞 ⟪η, x⟫ : ℂ)
  have hf : (fun t ↦ shiftIntegrand a b (t * (2 * π)) x ξ η) =
      fun t ↦ (𝐞 ⟪η, x⟫ : ℂ) • Ψ (a.coefficient (x, ξ + (t * (2 * π)) • η)) :=
    funext fun t ↦ by simp [shiftIntegrand, Ψ]
  rw [hf]
  refine h.congr_deriv ?_
  -- On the coordinate vectors the derivative of `ζ ↦ a(x, ζ)` is a frequency derivative.
  have hDj (j : Fin n) : fderiv ℝ (fun ζ ↦ a.coefficient (x, ζ)) (ξ + (t * (2 * π)) • η)
      (EuclideanSpace.single j 1) =
        (frequencyDeriv j a).coefficient (x, ξ + (t * (2 * π)) • η) := by
    rw [coefficient_frequencyDeriv, coordinateDeriv_cons, coordinateDeriv_nil]
  rw [ContinuousLinearMap.apply_eq_sum_single, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [map_smul, hDj, shiftIntegrand, hb.fourier_spatialDeriv_slice, Ψ,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_smul,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul, PiLp.smul_apply, smul_eq_mul,
    ← Complex.coe_smul, smul_apply, smul_smul]
  congr 1
  push_cast
  linear_combination (↑(𝐞 ⟪η, x⟫) * 2 * ↑π * ↑(η.ofLp j) : ℂ) * Complex.I_sq

variable (a b) in
/-- The family `C_t(x, ξ) = ∫ exp(2πi ⟪η, x⟫) a(x, ξ + 2πtη) ∘ b̂(η, ξ) dη` interpolating between
the pointwise composition (`t = 0`) and the composition symbol (`t = 1`). -/
private def scaledSharp (t : ℝ) (x ξ : CoordinateSpace n) : V →L[ℂ] U :=
  ∫ η, shiftIntegrand a b (t * (2 * π)) x ξ η

/-- `‖C_t(x, ξ)‖ ≤ C ⟨ξ⟩ ^ (m' + m)`, uniformly for positions in a compact set and `|t| ≤ 2`. -/
private theorem exists_norm_scaledSharp_le (hb : b.HasCompactSpatialSupport)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ 2 → ∀ x ∈ K, ∀ ξ : CoordinateSpace n,
      ‖scaledSharp a b t x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_shiftIntegrand_le (a := a) hb hK
  set I := ∫ η : CoordinateSpace n, (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hI : 0 ≤ I := integral_nonneg fun η ↦ by positivity
  refine ⟨C * I, mul_nonneg hC0 hI, fun t ht x hx ξ ↦ ?_⟩
  refine (norm_integral_le_of_norm_le
    ((integrable_rpow_neg_one_add_norm_sq (by simp)).const_mul
      (C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2)))
    (.of_forall fun η ↦ hC _ (abs_mul_two_pi_le ht) x hx ξ η)).trans_eq ?_
  rw [integral_const_mul]
  ring

/-- At `t = 1` the family is the composition symbol. -/
private theorem scaledSharp_one (hb : b.HasCompactSpatialSupport) (x ξ : CoordinateSpace n) :
    scaledSharp a b 1 x ξ = (a.sharp b hb).coefficient (x, ξ) := by
  simp only [scaledSharp, shiftIntegrand, one_mul, coefficient_sharp]

/-- **Differentiation in the parameter** under the integral sign:
`d/dt C_t(a, b) = -i ∑ⱼ C_t(∂_{ξⱼ} a, ∂_{xⱼ} b)`. -/
private theorem hasDerivAt_scaledSharp (hb : b.HasCompactSpatialSupport) {t₀ : ℝ}
    (ht₀ : |t₀| ≤ 1) (x ξ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ scaledSharp a b t x ξ)
      ((-Complex.I) • ∑ j, scaledSharp (frequencyDeriv j a) (spatialDeriv j b) t₀ x ξ) t₀ := by
  have hb' (j : Fin n) := hb.spatialDeriv j
  choose C hC0 hC using fun j ↦
    exists_norm_shiftIntegrand_le (a := frequencyDeriv j a) (hb' j) (isCompact_singleton (x := x))
  have hball : ∀ t ∈ Metric.ball t₀ 1, |t * (2 * π)| ≤ 4 * π := fun t ht ↦ by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have := abs_sub_abs_le_abs_sub t t₀
    exact abs_mul_two_pi_le (by linarith)
  set F' : ℝ → CoordinateSpace n → V →L[ℂ] U := fun t η ↦
    ∑ j, (-Complex.I) • shiftIntegrand (frequencyDeriv j a) (spatialDeriv j b) (t * (2 * π)) x ξ η
  set bound : CoordinateSpace n → ℝ := fun η ↦
    ∑ j, C j * (1 + ‖ξ‖ ^ 2) ^ ((m' - 1 + m) / 2) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hint (j : Fin n) : Integrable fun η ↦ (-Complex.I) •
      shiftIntegrand (frequencyDeriv j a) (spatialDeriv j b) (t₀ * (2 * π)) x ξ η :=
    (integrable_shiftIntegrand (hb' j) (abs_mul_two_pi_le (by linarith)) x ξ).fun_smul _
  have hbound : ∀ᵐ η ∂(volume : Measure (CoordinateSpace n)), ∀ t ∈ Metric.ball t₀ 1,
      ‖F' t η‖ ≤ bound η := .of_forall fun η t ht ↦ by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
    exact hC j _ (hball t ht) x rfl ξ η
  have hbound_int : Integrable bound :=
    integrable_finsetSum _ fun j _ ↦ (integrable_rpow_neg_one_add_norm_sq (by simp)).const_mul _
  have hc (j : Fin n) := continuous_shiftIntegrand (a := frequencyDeriv j a) (hb' j)
    (t₀ * (2 * π)) x ξ
  have hF'meas : AEStronglyMeasurable (F' t₀) := by
    refine Continuous.aestronglyMeasurable ?_
    simp only [F']
    fun_prop
  have hderiv : ∀ᵐ η ∂(volume : Measure (CoordinateSpace n)), ∀ t ∈ Metric.ball t₀ 1,
      HasDerivAt (fun t ↦ shiftIntegrand a b (t * (2 * π)) x ξ η) (F' t η) t :=
    .of_forall fun η t _ ↦ hasDerivAt_shiftIntegrand hb t x ξ η
  obtain ⟨-, h⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t η ↦ shiftIntegrand a b (t * (2 * π)) x ξ η) (F' := F')
    (Metric.ball_mem_nhds t₀ one_pos)
    (.of_forall fun t ↦ (continuous_shiftIntegrand hb _ x ξ).aestronglyMeasurable)
    (integrable_shiftIntegrand hb (abs_mul_two_pi_le (by linarith)) x ξ)
    hF'meas hbound hbound_int hderiv
  refine h.congr_deriv ?_
  simp only [F', integral_finsetSum _ fun j _ ↦ hint j, integral_smul, Finset.smul_sum,
    scaledSharp]

variable [CompleteSpace W] [CompleteSpace U]

/-- At `t = 0` the family is the pointwise composition, by Fourier inversion. -/
private theorem scaledSharp_zero (hb : b.HasCompactSpatialSupport) (x ξ : CoordinateSpace n) :
    scaledSharp a b 0 x ξ = (a.coefficient (x, ξ)).comp (b.coefficient (x, ξ)) := by
  set f : CoordinateSpace n → V →L[ℂ] W := fun y ↦ b.coefficient (y, ξ)
  set φ : 𝓢(CoordinateSpace n, V →L[ℂ] W) := hb.sliceSchwartz ξ
  have hfS : ⇑φ = f := hb.coe_sliceSchwartz ξ
  have hFS : 𝓕 f = ⇑(𝓕 φ : 𝓢(CoordinateSpace n, V →L[ℂ] W)) := by
    rw [SchwartzMap.fourier_coe, hfS]
  have hint : Integrable (𝓕 f) := hFS ▸ (𝓕 φ : 𝓢(CoordinateSpace n, V →L[ℂ] W)).integrable
  have hinv : 𝓕⁻ (𝓕 f) = f :=
    Continuous.fourierInv_fourier_eq (hfS ▸ φ.continuous) (hfS ▸ φ.integrable) hint
  have he : Continuous fun η : CoordinateSpace n ↦ (𝐞 ⟪η, x⟫ : ℂ) := by fun_prop
  have hint' : Integrable fun η ↦ (𝐞 ⟪η, x⟫ : ℂ) • 𝓕 f η :=
    hint.norm.mono' (he.aestronglyMeasurable.smul hint.aestronglyMeasurable)
      (.of_forall fun η ↦ by rw [norm_smul, Circle.norm_coe, one_mul])
  set L : (V →L[ℂ] W) →L[ℂ] V →L[ℂ] U :=
    ContinuousLinearMap.compL ℂ V W U (a.coefficient (x, ξ))
  calc scaledSharp a b 0 x ξ = ∫ η, L ((𝐞 ⟪η, x⟫ : ℂ) • 𝓕 f η) := by
        simp only [scaledSharp, shiftIntegrand, zero_mul, zero_smul, add_zero, L,
          ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_smul, f]
    _ = L (𝓕⁻ (𝓕 f) x) := by
        rw [L.integral_comp_comm hint', Real.fourierInv_eq]
        simp only [Circle.smul_def]
    _ = _ := by rw [hinv]; rfl

end Scaled

/-! ### The remainder along the family -/

section Remainder

variable {a : Symbol n W U m'} {b : Symbol n V W m}

variable (a b) in
/-- The remainder `C_t(a, b) - ∑_{k < N} t^k sharpTerm a b k` of the expansion along the
interpolating family. -/
private def remainderAt (N : ℕ) (t : ℝ) (x ξ : CoordinateSpace n) : V →L[ℂ] U :=
  scaledSharp a b t x ξ - ∑ k ∈ range N, t ^ k • (a.sharpTerm b k).coefficient (x, ξ)

/-- The derivative of the polynomial part `∑_{k < N + 1} t^k sharpTerm a b k` is given by the
recursion defining `sharpTerm`. -/
private theorem hasDerivAt_sum_pow_smul_sharpTerm (N : ℕ) (a : Symbol n W U m')
    (b : Symbol n V W m) (x ξ : CoordinateSpace n) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∑ k ∈ range (N + 1), t ^ k • (a.sharpTerm b k).coefficient (x, ξ))
      (∑ k ∈ range N, t ^ k • ((-Complex.I) •
        ∑ j, ((frequencyDeriv j a).sharpTerm (spatialDeriv j b) k).coefficient (x, ξ))) t := by
  have h := HasDerivAt.fun_sum (u := range (N + 1)) fun k _ ↦
    (hasDerivAt_pow k t).smul_const ((a.sharpTerm b k).coefficient (x, ξ))
  refine h.congr_deriv ?_
  rw [Finset.sum_range_succ']
  simp only [CharP.cast_eq_zero, zero_mul, zero_smul, add_zero]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coefficient_sharpTerm_succ, Nat.add_sub_cancel, mul_comm, mul_smul]
  congr 1
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  field_simp

/-- The derivative in `t` of the remainder with `N + 1` terms is `-i ∑ⱼ` the remainders with `N`
terms of `∂_{ξⱼ} a` and `∂_{xⱼ} b`. -/
private theorem hasDerivAt_remainderAt (hb : b.HasCompactSpatialSupport) (N : ℕ) {t : ℝ}
    (ht : |t| ≤ 1) (x ξ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ remainderAt a b (N + 1) t x ξ)
      ((-Complex.I) • ∑ j, remainderAt (frequencyDeriv j a) (spatialDeriv j b) N t x ξ) t := by
  refine ((hasDerivAt_scaledSharp hb ht x ξ).fun_sub
    (hasDerivAt_sum_pow_smul_sharpTerm N a b x ξ t)).congr_deriv ?_
  simp only [remainderAt, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib, smul_comm (t ^ _)]
  rw [Finset.sum_comm]

variable [CompleteSpace W] [CompleteSpace U]

/-- The remainder vanishes at `t = 0`. -/
private theorem remainderAt_zero (hb : b.HasCompactSpatialSupport) (N : ℕ)
    (x ξ : CoordinateSpace n) : remainderAt a b (N + 1) 0 x ξ = 0 := by
  rw [remainderAt, scaledSharp_zero hb, Finset.sum_range_succ']
  simp

/-- **The remainder estimate.** `‖C_t(a, b) - ∑_{k < N} t^k sharpTerm a b k‖ ≤ C ⟨ξ⟩ ^ (m' + m - N)`
for positions in a compact set, uniformly in `t ∈ [0, 1]`. -/
private theorem exists_norm_remainderAt_le (N : ℕ) :
    ∀ {m m' : ℝ} {a : Symbol n W U m'} {b : Symbol n V W m}, b.HasCompactSpatialSupport →
      ∀ {K : Set (CoordinateSpace n)}, IsCompact K →
        ∃ C, 0 ≤ C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ K, ∀ ξ : CoordinateSpace n,
          ‖remainderAt a b N t x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - N) / 2) := by
  induction N with
  | zero =>
    intro m m' a b hb K hK
    obtain ⟨C, hC0, hC⟩ := exists_norm_scaledSharp_le (a := a) hb hK
    refine ⟨C, hC0, fun t ht x hx ξ ↦ ?_⟩
    have ht2 : |t| ≤ 2 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa [remainderAt] using hC t ht2 x hx ξ
  | succ N ih =>
    intro m m' a b hb K hK
    choose C hC0 hC using fun j ↦ ih (a := frequencyDeriv j a) (hb.spatialDeriv j) hK
    refine ⟨∑ j, C j, Finset.sum_nonneg fun j _ ↦ hC0 j, fun t ht x hx ξ ↦ ?_⟩
    have hw : (1 + ‖ξ‖ ^ 2) ^ ((m' - 1 + m - N) / 2) =
        (1 + ‖ξ‖ ^ 2) ^ ((m' + m - ((N + 1 : ℕ) : ℝ)) / 2) := by
      congr 1
      push_cast
      ring
    have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
        ‖(-Complex.I) • ∑ j, remainderAt (frequencyDeriv j a) (spatialDeriv j b) N s x ξ‖ ≤
          (∑ j, C j) * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - ((N + 1 : ℕ) : ℝ)) / 2) := by
      intro s hs
      rw [norm_smul, norm_neg, Complex.norm_I, one_mul, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      rw [← hw]
      exact hC j s (Set.Ico_subset_Icc_self hs) x hx ξ
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs ↦ (hasDerivAt_remainderAt hb N (abs_le.2 ⟨by linarith [hs.1], hs.2⟩) x
        ξ).hasDerivWithinAt) hbound t ht
    rw [remainderAt_zero hb, sub_zero, sub_zero] at hmv
    have hB : 0 ≤ (∑ j, C j) * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - ((N + 1 : ℕ) : ℝ)) / 2) :=
      mul_nonneg (Finset.sum_nonneg fun j _ ↦ hC0 j) (by positivity)
    exact hmv.trans (mul_le_of_le_one_right hB ht.2)

end Remainder

/-! ### The remainder symbol -/

section RemainderSymbol

variable {a : Symbol n W U m'} {b : Symbol n V W m}

variable (a b) in
/-- The remainder `a # b - ∑_{k < N} sharpTerm a b k`, as a symbol of order `m' + m`. -/
private def remainderSymbol (hb : b.HasCompactSpatialSupport) (N : ℕ) : Symbol n V U (m' + m) :=
  a.sharp b hb - ∑ k ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg k)) (a.sharpTerm b k)

private theorem coefficient_remainderSymbol (hb : b.HasCompactSpatialSupport) (N : ℕ)
    (x ξ : CoordinateSpace n) :
    (remainderSymbol a b hb N).coefficient (x, ξ) = remainderAt a b N 1 x ξ := by
  simp [remainderSymbol, remainderAt, scaledSharp_one hb]

private theorem spatialDeriv_remainderSymbol (hb : b.HasCompactSpatialSupport) (N : ℕ)
    (j : Fin n) :
    spatialDeriv j (remainderSymbol a b hb N) =
      remainderSymbol (spatialDeriv j a) b hb N +
        remainderSymbol a (spatialDeriv j b) (hb.spatialDeriv j) N := by
  simp only [remainderSymbol, map_sub, map_sum, spatialDeriv_sharp, spatialDeriv_inclusion,
    spatialDeriv_sharpTerm, map_add, Finset.sum_add_distrib]
  abel

private theorem coefficient_frequencyDeriv_remainderSymbol (hb : b.HasCompactSpatialSupport)
    (N : ℕ) (j : Fin n) (p : CoordinateSpace n × CoordinateSpace n) :
    (frequencyDeriv j (remainderSymbol a b hb N)).coefficient p =
      (remainderSymbol (frequencyDeriv j a) b hb N).coefficient p +
        (remainderSymbol a (frequencyDeriv j b) (hb.frequencyDeriv j) N).coefficient p := by
  obtain ⟨x, ξ⟩ := p
  simp only [remainderSymbol, map_sub, map_sum, coefficient_sub, coefficient_sum,
    frequencyDeriv_inclusion, coefficient_inclusion, Pi.sub_apply, Finset.sum_apply,
    coefficient_frequencyDeriv_sharp, coefficient_frequencyDeriv_sharpTerm, Finset.sum_add_distrib]
  abel

variable [CompleteSpace W] [CompleteSpace U]

/-- The symbol estimates of order `m' + m - N` for the remainder: every mixed derivative of the
remainder for `a` and `b` is a sum of remainders for derivatives of `a` and `b`, and a frequency
derivative lowers the order of one of them by one. -/
private theorem exists_bound_remainderSymbol (N D : ℕ) :
    ∀ {m m' : ℝ} {a : Symbol n W U m'} {b : Symbol n V W m} (hb : b.HasCompactSpatialSupport)
      (α β : List (Fin n)), α.length + β.length = D → ∀ {K : Set (CoordinateSpace n)},
        IsCompact K → ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
          ‖mixedDeriv α β (remainderSymbol a b hb N).coefficient x ξ‖ ≤
            C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - N - β.length) / 2) := by
  induction D with
  | zero =>
    intro m m' a b hb α β hD K hK
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by
      simpa [List.length_eq_zero_iff] using hD
    obtain ⟨C, hC0, hC⟩ := exists_norm_remainderAt_le N (a := a) hb hK
    refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
    simpa [coefficient_remainderSymbol] using hC 1 ⟨zero_le_one, le_rfl⟩ x hx ξ
  | succ D ih =>
    intro m m' a b hb α β hD K hK
    rcases List.eq_nil_or_concat' β with rfl | ⟨β', j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α', j, rfl⟩
      · simp at hD
      · have hlen : α'.length + ([] : List (Fin n)).length = D := by
          simp only [List.length_append, List.length_singleton, List.length_nil] at hD ⊢
          omega
        obtain ⟨C₁, hC₁0, hC₁⟩ := ih (a := spatialDeriv j a) hb α' [] hlen hK
        obtain ⟨C₂, hC₂0, hC₂⟩ := ih (a := a) (hb.spatialDeriv j) α' [] hlen hK
        refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x hx ξ ↦ ?_⟩
        rw [← mixedDeriv_spatialDeriv, spatialDeriv_remainderSymbol, coefficient_add]
        exact norm_mixedDeriv_add_le (remainderSymbol _ _ _ _).contDiff_coefficient
          (remainderSymbol _ _ _ _).contDiff_coefficient (hC₁ x hx ξ) (hC₂ x hx ξ)
    · have hlen : α.length + β'.length = D := by
        simp only [List.length_append, List.length_singleton] at hD
        omega
      obtain ⟨C₁, hC₁0, hC₁⟩ := ih (a := frequencyDeriv j a) hb α β' hlen hK
      obtain ⟨C₂, hC₂0, hC₂⟩ := ih (a := a) (hb.frequencyDeriv j) α β' hlen hK
      refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x hx ξ ↦ ?_⟩
      have hfun : (frequencyDeriv j (remainderSymbol a b hb N)).coefficient =
          (remainderSymbol (frequencyDeriv j a) b hb N).coefficient +
            (remainderSymbol a (frequencyDeriv j b) (hb.frequencyDeriv j) N).coefficient :=
        funext fun p ↦ coefficient_frequencyDeriv_remainderSymbol hb N j p
      have e₁ : (m' - 1 + m - N - β'.length) / 2 = (m' + m - N - (β' ++ [j]).length) / 2 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      have e₂ : (m' + (m - 1) - N - β'.length) / 2 = (m' + m - N - (β' ++ [j]).length) / 2 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      have h₁ := hC₁ x hx ξ
      have h₂ := hC₂ x hx ξ
      rw [e₁] at h₁
      rw [e₂] at h₂
      rw [← mixedDeriv_frequencyDeriv, hfun]
      exact norm_mixedDeriv_add_le (remainderSymbol _ _ _ _).contDiff_coefficient
        (remainderSymbol _ _ _ _).contDiff_coefficient h₁ h₂

variable (a b) in
/-- The remainder `a # b - ∑_{k < N} sharpTerm a b k` of the composition expansion after `N`
terms, a symbol of order `m' + m - N` (`sharp_eq_sum_sharpTerm_add_sharpRemainder`). -/
def sharpRemainder (hb : b.HasCompactSpatialSupport) (N : ℕ) : Symbol n V U (m' + m - N) where
  coefficient := (remainderSymbol a b hb N).coefficient
  contDiff_coefficient := (remainderSymbol a b hb N).contDiff_coefficient
  exists_bound _ hK α β := exists_bound_remainderSymbol N _ (a := a) hb α β rfl hK

@[simp]
theorem coefficient_sharpRemainder (hb : b.HasCompactSpatialSupport) (N : ℕ) :
    (a.sharpRemainder b hb N).coefficient =
      (a.sharp b hb).coefficient - ∑ k ∈ range N, (a.sharpTerm b k).coefficient := by
  simp [sharpRemainder, remainderSymbol]

/-- **The asymptotic expansion of the composition symbol.** For every `N`,
`a # b = ∑_{k < N} sharpTerm a b k + sharpRemainder a b hb N`, where `sharpTerm a b k` is the term
`((-i)^k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b` of order `m' + m - k` and the remainder is a symbol
of order `m' + m - N`. -/
theorem sharp_eq_sum_sharpTerm_add_sharpRemainder (hb : b.HasCompactSpatialSupport) (N : ℕ) :
    a.sharp b hb =
      ∑ k ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg k)) (a.sharpTerm b k) +
        inclusion (sub_le_self _ (Nat.cast_nonneg N)) (a.sharpRemainder b hb N) := by
  ext1
  simp

/-- The composition symbol `a # b` is the pointwise composition `a ∘ b` up to a symbol of order
`m' + m - 1`. -/
theorem sharp_eq_comp_add_sharpRemainder_one (hb : b.HasCompactSpatialSupport) :
    a.sharp b hb = a.comp b + inclusion (by simp) (a.sharpRemainder b hb 1) := by
  ext1
  funext p
  simp

/-- The composition symbol is an asymptotic sum `a # b ∼ ∑ₖ sharpTerm a b k` of the terms of the
expansion, of orders `m' + m - k`. In particular it is determined by the terms modulo smoothing
symbols (`TauCeti.Symbol.IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub`). -/
theorem isAsymptoticSum_sharp (hb : b.HasCompactSpatialSupport) :
    IsAsymptoticSum (m := fun k : ℕ ↦ m' + m - k) (inclusion (by simp) (a.sharp b hb))
      (a.sharpTerm b) :=
  isAsymptoticSum_iff.2 fun N ↦ ⟨a.sharpRemainder b hb N, by simp⟩

end RemainderSymbol

end Symbol

end TauCeti

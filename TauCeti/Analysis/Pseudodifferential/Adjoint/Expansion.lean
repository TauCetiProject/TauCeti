/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Basic
public import TauCeti.Analysis.Pseudodifferential.AsymptoticSum
public import TauCeti.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic

/-!
# The asymptotic expansion of the adjoint symbol

Let `a` be a symbol of order `m` with compact spatial support, with values in operators between
complex Hilbert spaces. Its adjoint symbol `a*` (`TauCeti.Symbol.adjoint`), whose quantization is
the formal adjoint of the quantization of `a`, has the asymptotic expansion

`a* ∼ ∑_α (1 / α!) ∂_ξ^α D_x^α a†`, with `D_x = -i ∂_x`,

where `a†(x, ξ) = a(x, ξ)†` is the pointwise Hilbert space adjoint. This file proves the expansion
with an actual remainder symbol after every number of terms:

* `TauCeti.Symbol.adjointTerm a k`: the term `((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†` of
  order `m - k`, the sum running over the words `w` of coordinate indices of length `k`
  (`TauCeti.Symbol.coefficient_adjointTerm`). Grouping the words by the multi-index they
  determine gives the sum over `|α| = k` above. The leading term `adjointTerm a 0` is `a†`.
* `TauCeti.Symbol.adjointRemainder a ha N`: the remainder `a* - ∑_{k < N} adjointTerm a k`, a symbol
  of order `m - N` with estimates uniform in the position
  (`TauCeti.Symbol.isUniform_adjointRemainder`).
* `TauCeti.Symbol.adjoint_eq_sum_adjointTerm_add_adjointRemainder`: **the adjoint expansion**,
  `a* = ∑_{k < N} adjointTerm a k + adjointRemainder a ha N` for every `N`. In particular
  `a* - a†` has order `m - 1` (`TauCeti.Symbol.adjoint_eq_map_add_adjointRemainder_one`), and
  `a*` is an asymptotic sum of the terms (`TauCeti.Symbol.isAsymptoticSum_adjoint`), which
  determines it modulo smoothing symbols.
* `TauCeti.Symbol.exists_seminorm_adjointRemainder_le`: **the seminorm estimate of the
  remainder.** For compact sets `K` and `L`, each seminorm `p_{L,α,β}` of the remainder after `N`
  terms, in the class of order `m - N`, is at most a constant times finitely many seminorms on `K`
  of `a`, for all `a` vanishing at positions outside `K`. Its case `N = 0` is the estimate
  `TauCeti.Symbol.exists_seminorm_adjoint_le` for `a*` itself. Together with the additivity of the
  terms and remainders (`TauCeti.Symbol.adjointTerm_add`, `TauCeti.Symbol.adjointRemainder_add`),
  these give the continuity of `a ↦ a*` and of the remainders in
  `TauCeti.Analysis.Pseudodifferential.Adjoint.Continuity`. Like `a ↦ a*`, the terms and
  remainders are conjugate-linear in `a` (`TauCeti.Symbol.adjointTerm_smul`,
  `TauCeti.Symbol.adjointRemainder_smul`).

## Proof outline

Write `â(θ, ξ)` for the Fourier transform of the position slice `x ↦ a(x, ξ)`. For a real
parameter `t` consider

`A_t(x, ξ) = (∫ exp(2πi ⟪θ, x⟫) â(θ, ξ - 2πtθ) dθ)†`,

so that `A_1 = a*` by definition and `A_0 = a†` by Fourier inversion. Since
`(∂_{x_j} a)^(θ, ξ) = 2πi θⱼ â(θ, ξ)`, differentiating under the integral sign gives
`d/dt A_t(a) = -i ∑ⱼ A_t(∂_{x_j} ∂_{ξ_j} a)`. The terms satisfy the matching recursion
`adjointTerm a (k + 1) = (-i / (k + 1)) ∑ⱼ adjointTerm (∂_{x_j} ∂_{ξ_j} a) k`, so the remainder
`R_N(t) = A_t(a) - ∑_{k < N} t^k adjointTerm a k` satisfies
`d/dt R_{N+1}(t)(a) = -i ∑ⱼ R_N(t)(∂_{x_j} ∂_{ξ_j} a)` and `R_{N+1}(0) = 0`. The mean value theorem
and induction on `N` bound `R_N(t)` by `C ⟨ξ⟩ ^ (m - N)` uniformly for `t ∈ [0, 1]`, starting from
the decay of `â(θ, ξ - 2πtθ)` in `θ`
(`TauCeti.Symbol.exists_norm_fourier_slice_sub_smul_le_sum_seminorm`). Derivatives
commute with the adjoint symbol and with the terms, so every mixed derivative of the remainder is
the remainder of a derivative of `a`, which gives the symbol estimates of order `m - N`. The
constants are tracked through the induction: for `a` vanishing outside a compact set `K`, the
decay constant is a finite sum of seminorms of `a` on `K`, and the derivative `∂_{x_j} ∂_{ξ_j} a`
has the seminorms of `a` with `j` appended to both words, so every constant is a finite sum of
seminorms of `a` on `K`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Finset
open TopologicalSpace (Compacts)
open scoped RealInnerProductSpace ContDiff SchwartzMap

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

open ContinuousLinearMap (adjointRealCLM adjointRealCLM_apply)

/-! ### The terms of the expansion -/

section Term

variable [CompleteSpace V] [CompleteSpace W]

/-- The term of order `m - k` in the asymptotic expansion of the adjoint symbol:
`((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†`, the sum running over the words `w` of coordinate
indices of length `k` and `†` denoting the pointwise Hilbert space adjoint
(`coefficient_adjointTerm`). It is defined by the recursion
`adjointTerm a (k + 1) = (-i / (k + 1)) ∑ⱼ adjointTerm (∂_{xⱼ} ∂_{ξⱼ} a) k`, starting from the
pointwise adjoint `adjointTerm a 0 = a†`. -/
def adjointTerm : {m : ℝ} → Symbol n V W m → (k : ℕ) → Symbol n W V (m - k)
  | _, a, 0 => inclusion (by simp) (a.map adjointRealCLM)
  | _, a, k + 1 => inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, adjointTerm (spatialDeriv j (frequencyDeriv j a)) k)

theorem adjointTerm_zero (a : Symbol n V W m) :
    a.adjointTerm 0 = inclusion (by simp) (a.map adjointRealCLM) := by
  rw [adjointTerm]

theorem adjointTerm_succ (a : Symbol n V W m) (k : ℕ) :
    a.adjointTerm (k + 1) = inclusion (by push_cast; linarith)
      ((-Complex.I / (k + 1)) • ∑ j, (spatialDeriv j (frequencyDeriv j a)).adjointTerm k) := by
  rw [adjointTerm]

@[simp]
theorem coefficient_adjointTerm_zero (a : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.adjointTerm 0).coefficient p = ContinuousLinearMap.adjoint (a.coefficient p) := by
  rw [adjointTerm_zero, coefficient_inclusion, coefficient_map, adjointRealCLM_apply]

theorem coefficient_adjointTerm_succ (a : Symbol n V W m) (k : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (a.adjointTerm (k + 1)).coefficient p = (-Complex.I / (k + 1)) •
      ∑ j, ((spatialDeriv j (frequencyDeriv j a)).adjointTerm k).coefficient p := by
  simp [adjointTerm_succ]

/-- **The terms of the adjoint expansion** are `((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†`, the
sum running over the words `w` of coordinate indices of length `k`. Grouping the words by the
multi-index they determine gives the familiar form `∑_{|α| = k} (1 / α!) ∂_ξ^α D_x^α a†` with
`D_x = -i ∂_x`. -/
theorem coefficient_adjointTerm (a : Symbol n V W m) (k : ℕ) (x ξ : CoordinateSpace n) :
    (a.adjointTerm k).coefficient (x, ξ) = ((-Complex.I) ^ k / k.factorial) •
      ∑ w : Fin k → Fin n,
        ContinuousLinearMap.adjoint (mixedDeriv (List.ofFn w) (List.ofFn w) a.coefficient x ξ) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [coefficient_adjointTerm_succ, ← (Fin.snocEquiv fun _ ↦ Fin n).sum_comp,
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

/-- The terms of the adjoint expansion are additive in the symbol. -/
@[simp]
theorem adjointTerm_add (a b : Symbol n V W m) (k : ℕ) :
    (a + b).adjointTerm k = a.adjointTerm k + b.adjointTerm k := by
  induction k generalizing m with
  | zero =>
    ext1
    funext p
    simp
  | succ k ih => simp only [adjointTerm_succ, map_add, ih, Finset.sum_add_distrib, smul_add]

/-- The terms of the adjoint expansion of a difference are the differences of the terms. -/
@[simp]
theorem adjointTerm_sub (a b : Symbol n V W m) (k : ℕ) :
    (a - b).adjointTerm k = a.adjointTerm k - b.adjointTerm k := by
  rw [eq_sub_iff_add_eq, ← adjointTerm_add, sub_add_cancel]

/-- The terms of the adjoint expansion are conjugate-linear in the symbol:
`adjointTerm (c • a) k = conj c • adjointTerm a k`. -/
@[simp]
theorem adjointTerm_smul (c : ℂ) (a : Symbol n V W m) (k : ℕ) :
    (c • a).adjointTerm k = (starRingEnd ℂ) c • a.adjointTerm k := by
  induction k generalizing m with
  | zero =>
    ext1
    funext p
    simp [LinearIsometryEquiv.map_smulₛₗ]
  | succ k ih =>
    rw [adjointTerm_succ, adjointTerm_succ, ← map_smul, smul_comm ((starRingEnd ℂ) c)]
    simp only [map_smul, ih, Finset.smul_sum]

/-- Spatial derivatives commute with the terms of the adjoint expansion. -/
@[simp]
theorem spatialDeriv_adjointTerm (l : Fin n) (a : Symbol n V W m) (k : ℕ) :
    spatialDeriv l (a.adjointTerm k) = (spatialDeriv l a).adjointTerm k := by
  induction k generalizing m with
  | zero => simp [adjointTerm_zero]
  | succ k ih =>
    simp only [adjointTerm_succ, spatialDeriv_inclusion, map_smul, map_sum, ih]
    refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [spatialDeriv_comm l j, spatialDeriv_frequencyDeriv_comm l j]

/-- Frequency derivatives commute with the terms of the adjoint expansion. The orders
`m - k - 1` and `m - 1 - k` of the two sides differ syntactically, so the rule is stated for
their coefficients. -/
theorem coefficient_frequencyDeriv_adjointTerm (l : Fin n) (a : Symbol n V W m) (k : ℕ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (frequencyDeriv l (a.adjointTerm k)).coefficient p =
      ((frequencyDeriv l a).adjointTerm k).coefficient p := by
  induction k generalizing m with
  | zero => simp [adjointTerm_zero]
  | succ k ih =>
    simp only [adjointTerm_succ, frequencyDeriv_inclusion, map_smul, map_sum, coefficient_inclusion,
      coefficient_smul, coefficient_sum, Pi.smul_apply, Finset.sum_apply]
    refine congrArg _ (Finset.sum_congr rfl fun j _ ↦ ?_)
    rw [ih, ← spatialDeriv_frequencyDeriv_comm j l, frequencyDeriv_comm l j]

end Term

/-! ### The interpolating family `A_t` -/

section Scaled

variable (a : Symbol n V W m)

/-- The integrand `exp(2πi ⟪θ, x⟫) â(θ, ξ - sθ)` of the interpolating family, with the frequency
shift `2πθ` of the adjoint symbol scaled to `sθ`. -/
private def shiftIntegrand (s : ℝ) (x ξ θ : CoordinateSpace n) : V →L[ℂ] W :=
  (𝐞 ⟪θ, x⟫ : ℂ) • 𝓕 (fun y ↦ a.coefficient (y, ξ - s • θ)) θ

variable {a}

/-- The integrand decays like `(1 + ‖θ‖) ^ (-(n + 1)) ⟨ξ⟩ ^ m`, uniformly in the position and in
the shifts `|s| ≤ 4π`. -/
private theorem exists_norm_shiftIntegrand_le
    (ha : a.HasCompactSpatialSupport) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ 4 * π → ∀ x ξ θ : CoordinateSpace n,
      ‖shiftIntegrand a s x ξ θ‖ ≤
        C * ((1 + ‖θ‖) ^ (-((n : ℝ) + 1)) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_fourier_slice_sub_smul_le (4 * π)
  refine ⟨C, hC0, fun s hs x ξ θ ↦ ?_⟩
  rw [shiftIntegrand, norm_smul, Circle.norm_coe, one_mul]
  exact hC s hs θ ξ

/-- The frequency shifts `2πtθ` of the family with `|t| ≤ 2` are at most `4π ‖θ‖`. -/
private theorem abs_mul_two_pi_le {t : ℝ} (ht : |t| ≤ 2) : |t * (2 * π)| ≤ 4 * π := by
  rw [abs_mul, abs_of_pos two_pi_pos]
  nlinarith [pi_pos]

/-- **Differentiation in the parameter** of the integrand: since `2π θⱼ â = -i (∂_{xⱼ} a)^`,
`d/dt` of the integrand of `A_t(a)` is `i ∑ⱼ` the integrand of `A_t(∂_{xⱼ} ∂_{ξⱼ} a)`, before the
adjoint is taken. -/
private theorem hasDerivAt_shiftIntegrand
    (ha : a.HasCompactSpatialSupport) (t : ℝ) (x ξ θ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ shiftIntegrand a (t * (2 * π)) x ξ θ)
      (∑ j, Complex.I •
        shiftIntegrand (spatialDeriv j (frequencyDeriv j a)) (t * (2 * π)) x ξ θ) t := by
  set ζ := ξ - (t * (2 * π)) • θ
  have hF := ha.hasFDerivAt_fourier_slice θ ζ
  have hl : HasDerivAt (fun t : ℝ ↦ ξ - (t * (2 * π)) • θ) (-((2 * π) • θ)) t := by
    simpa using (((hasDerivAt_id t).mul_const (2 * π)).smul_const θ).const_sub ξ
  have h := (hF.comp_hasDerivAt t hl).const_smul (𝐞 ⟪θ, x⟫ : ℂ)
  refine h.congr_deriv ?_
  -- On the coordinate vectors the derivative of `ζ ↦ â(θ, ζ)` is the Fourier transform of the
  -- frequency derivatives.
  have hD (j : Fin n) : (∫ y, (𝐞 (-⟪y, θ⟫) : ℂ) •
      fderiv ℝ (fun ζ ↦ a.coefficient (y, ζ)) ζ) (EuclideanSpace.single j 1) =
        𝓕 (fun y ↦ (frequencyDeriv j a).coefficient (y, ζ)) θ := by
    rw [← ha.coordinateDeriv_fourier_slice j θ ζ, coordinateDeriv_cons, coordinateDeriv_nil,
      hF.fderiv]
  rw [ContinuousLinearMap.apply_eq_sum_single, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [hD, shiftIntegrand, (ha.frequencyDeriv j).fourier_spatialDeriv_slice,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul, PiLp.neg_apply, PiLp.smul_apply,
    smul_eq_mul, ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  linear_combination (-(↑(𝐞 ⟪θ, x⟫) * 2 * ↑π * ↑(θ.ofLp j)) : ℂ) * Complex.I_sq

variable [CompleteSpace V] [CompleteSpace W]

variable (a) in
/-- The family `A_t(x, ξ) = (∫ exp(2πi ⟪θ, x⟫) â(θ, ξ - 2πtθ) dθ)†` interpolating between the
pointwise adjoint (`t = 0`) and the adjoint symbol (`t = 1`). -/
private def scaledAdjoint (t : ℝ) (x ξ : CoordinateSpace n) : W →L[ℂ] V :=
  ContinuousLinearMap.adjoint (∫ θ, shiftIntegrand a (t * (2 * π)) x ξ θ)

/-- `‖A_t(x, ξ)‖ ≤ C (∑_α p_{K,α,[]}(a)) ⟨ξ⟩ ^ m` for every symbol `a` vanishing at positions
outside `K`, uniformly in the position and in `|t| ≤ 2`. -/
private theorem exists_norm_scaledAdjoint_le (K : Compacts (CoordinateSpace n)) :
    ∃ (s : Finset (List (Fin n))) (C : ℝ), 0 ≤ C ∧ ∀ a : Symbol n V W m,
      (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) → ∀ t : ℝ, |t| ≤ 2 → ∀ x ξ : CoordinateSpace n,
        ‖scaledAdjoint a t x ξ‖ ≤
          C * (∑ α ∈ s, Symbol.seminorm K α [] a) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨s, C, hC0, hC⟩ :=
    exists_norm_integral_fourierChar_smul_fourier_slice_sub_smul_le_sum_seminorm (V := V)
      (W := W) (m := m) K (4 * π)
  refine ⟨s, C, hC0, fun a haK t ht x ξ ↦ ?_⟩
  rw [scaledAdjoint, LinearIsometryEquiv.norm_map]
  exact hC a haK _ (abs_mul_two_pi_le ht) x ξ

/-- At `t = 1` the family is the adjoint symbol. -/
private theorem scaledAdjoint_one (ha : a.HasCompactSpatialSupport)
    (x ξ : CoordinateSpace n) : scaledAdjoint a 1 x ξ = (adjoint a ha).coefficient (x, ξ) := by
  simp only [scaledAdjoint, shiftIntegrand, one_mul, coefficient_adjoint]

/-- At `t = 0` the family is the pointwise adjoint, by Fourier inversion. -/
private theorem scaledAdjoint_zero (ha : a.HasCompactSpatialSupport)
    (x ξ : CoordinateSpace n) :
    scaledAdjoint a 0 x ξ = ContinuousLinearMap.adjoint (a.coefficient (x, ξ)) := by
  set f : CoordinateSpace n → V →L[ℂ] W := fun y ↦ a.coefficient (y, ξ)
  set φ : 𝓢(CoordinateSpace n, V →L[ℂ] W) := ha.sliceSchwartz ξ
  have hfS : ⇑φ = f := ha.coe_sliceSchwartz ξ
  have hFS : 𝓕 f = ⇑(𝓕 φ : 𝓢(CoordinateSpace n, V →L[ℂ] W)) := by
    rw [SchwartzMap.fourier_coe, hfS]
  have hint : Integrable (𝓕 f) := hFS ▸ (𝓕 φ : 𝓢(CoordinateSpace n, V →L[ℂ] W)).integrable
  have hinv : 𝓕⁻ (𝓕 f) = f :=
    Continuous.fourierInv_fourier_eq (hfS ▸ φ.continuous) (hfS ▸ φ.integrable) hint
  rw [scaledAdjoint]
  congr 1
  calc ∫ θ, shiftIntegrand a (0 * (2 * π)) x ξ θ = 𝓕⁻ (𝓕 f) x := by
        simp only [shiftIntegrand, zero_mul, zero_smul, sub_zero, Real.fourierInv_eq,
          Circle.smul_def, f]
    _ = f x := by rw [hinv]

/-- **Differentiation in the parameter** under the integral sign:
`d/dt A_t(a) = -i ∑ⱼ A_t(∂_{xⱼ} ∂_{ξⱼ} a)`. -/
private theorem hasDerivAt_scaledAdjoint
    (ha : a.HasCompactSpatialSupport) {t₀ : ℝ} (ht₀ : |t₀| ≤ 1) (x ξ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ scaledAdjoint a t x ξ)
      ((-Complex.I) • ∑ j, scaledAdjoint (spatialDeriv j (frequencyDeriv j a)) t₀ x ξ) t₀ := by
  have hb (j : Fin n) := (ha.frequencyDeriv j).spatialDeriv j
  choose C _ hC using fun j ↦ exists_norm_shiftIntegrand_le (hb j)
  have hball : ∀ t ∈ Metric.ball t₀ 1, |t * (2 * π)| ≤ 4 * π := fun t ht ↦ by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have := abs_sub_abs_le_abs_sub t t₀
    exact abs_mul_two_pi_le (by linarith)
  set F' : ℝ → CoordinateSpace n → V →L[ℂ] W := fun t θ ↦
    ∑ j, Complex.I • shiftIntegrand (spatialDeriv j (frequencyDeriv j a)) (t * (2 * π)) x ξ θ
  set bound : CoordinateSpace n → ℝ := fun θ ↦
    ∑ j, C j * ((1 + ‖θ‖) ^ (-((n : ℝ) + 1)) * (1 + ‖ξ‖ ^ 2) ^ ((m - 1) / 2))
  have hint (j : Fin n) : Integrable fun θ ↦ Complex.I •
      shiftIntegrand (spatialDeriv j (frequencyDeriv j a)) (t₀ * (2 * π)) x ξ θ :=
    ((hb j).integrable_fourierChar_smul_fourier_slice_sub_smul _ x ξ).fun_smul _
  have hbound : ∀ᵐ θ ∂(volume : Measure (CoordinateSpace n)), ∀ t ∈ Metric.ball t₀ 1,
      ‖F' t θ‖ ≤ bound θ := .of_forall fun θ t ht ↦ by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    rw [norm_smul, Complex.norm_I, one_mul]
    exact hC j _ (hball t ht) x ξ θ
  have hbound_int : Integrable bound :=
    integrable_finsetSum _ fun j _ ↦
      (integrable_one_add_norm_rpow_neg_add_one.mul_const _).const_mul _
  obtain ⟨-, h⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t θ ↦ shiftIntegrand a (t * (2 * π)) x ξ θ) (F' := F')
    (Metric.ball_mem_nhds t₀ one_pos)
    (.of_forall fun t ↦
      (ha.continuous_fourierChar_smul_fourier_slice_sub_smul _ x ξ).aestronglyMeasurable)
    (ha.integrable_fourierChar_smul_fourier_slice_sub_smul _ x ξ)
    (continuous_finsetSum _ fun j _ ↦
      ((hb j).continuous_fourierChar_smul_fourier_slice_sub_smul _ x ξ).const_smul
        Complex.I).aestronglyMeasurable
    hbound hbound_int (.of_forall fun θ t _ ↦ hasDerivAt_shiftIntegrand ha t x ξ θ)
  have h' := adjointRealCLM.hasFDerivAt.comp_hasDerivAt t₀ h
  simp only [Function.comp_def, adjointRealCLM_apply] at h'
  refine h'.congr_deriv ?_
  simp only [F', integral_finsetSum _ fun j _ ↦ hint j, integral_smul, map_sum,
    LinearIsometryEquiv.map_smulₛₗ, Complex.conj_I, Finset.smul_sum, scaledAdjoint]

end Scaled

/-! ### The remainder along the family -/

section Remainder

variable [CompleteSpace V] [CompleteSpace W]

variable {a : Symbol n V W m}

variable (a) in
/-- The remainder `A_t(a) - ∑_{k < N} t^k adjointTerm a k` of the expansion along the
interpolating family. -/
private def remainderAt (N : ℕ) (t : ℝ) (x ξ : CoordinateSpace n) : W →L[ℂ] V :=
  scaledAdjoint a t x ξ - ∑ k ∈ range N, t ^ k • (a.adjointTerm k).coefficient (x, ξ)

/-- The derivative of the polynomial part `∑_{k < N + 1} t^k adjointTerm a k` is given by the
recursion defining `adjointTerm`. -/
private theorem hasDerivAt_sum_pow_smul_adjointTerm (N : ℕ) (a : Symbol n V W m)
    (x ξ : CoordinateSpace n) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∑ k ∈ range (N + 1), t ^ k • (a.adjointTerm k).coefficient (x, ξ))
      (∑ k ∈ range N, t ^ k • ((-Complex.I) •
        ∑ j, ((spatialDeriv j (frequencyDeriv j a)).adjointTerm k).coefficient (x, ξ))) t := by
  have h := HasDerivAt.fun_sum (u := range (N + 1)) fun k _ ↦
    (hasDerivAt_pow k t).smul_const ((a.adjointTerm k).coefficient (x, ξ))
  refine h.congr_deriv ?_
  rw [Finset.sum_range_succ']
  simp only [CharP.cast_eq_zero, zero_mul, zero_smul, add_zero]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [coefficient_adjointTerm_succ, Nat.add_sub_cancel, mul_comm, mul_smul]
  congr 1
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  field_simp

/-- The derivative in `t` of the remainder with `N + 1` terms is `-i ∑ⱼ` the remainders with `N`
terms of `∂_{xⱼ} ∂_{ξⱼ} a`. -/
private theorem hasDerivAt_remainderAt (ha : a.HasCompactSpatialSupport)
    (N : ℕ) {t : ℝ} (ht : |t| ≤ 1) (x ξ : CoordinateSpace n) :
    HasDerivAt (fun t ↦ remainderAt a (N + 1) t x ξ)
      ((-Complex.I) • ∑ j, remainderAt (spatialDeriv j (frequencyDeriv j a)) N t x ξ) t := by
  refine ((hasDerivAt_scaledAdjoint ha ht x ξ).fun_sub
    (hasDerivAt_sum_pow_smul_adjointTerm N a x ξ t)).congr_deriv ?_
  simp only [remainderAt, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib, smul_comm (t ^ _)]
  rw [Finset.sum_comm]

/-- The remainder vanishes at `t = 0`. -/
private theorem remainderAt_zero (ha : a.HasCompactSpatialSupport)
    (N : ℕ) (x ξ : CoordinateSpace n) : remainderAt a (N + 1) 0 x ξ = 0 := by
  rw [remainderAt, scaledAdjoint_zero ha, Finset.sum_range_succ']
  simp

omit [CompleteSpace V] [CompleteSpace W] in
/-- The seminorms of `∂_{x_j} ∂_{ξ_j} a` on `K` are those of `a` with the letter `j` appended to
both words, so their sum over a finite set of pairs of words is at most the sum of the seminorms of
`a` over the images of that set. -/
private theorem sum_seminorm_spatialDeriv_frequencyDeriv_le [DecidableEq (List (Fin n))]
    (K : Compacts (CoordinateSpace n)) (s : Finset (List (Fin n) × List (Fin n))) (j : Fin n)
    (a : Symbol n V W m) :
    ∑ i ∈ s, Symbol.seminorm K i.1 i.2 (spatialDeriv j (frequencyDeriv j a)) ≤
      ∑ i ∈ univ.biUnion fun l ↦ s.image fun i ↦ (i.1 ++ [l], i.2 ++ [l]),
        Symbol.seminorm K i.1 i.2 a := by
  refine Finset.sum_le_sum_of_injOn (fun i ↦ (i.1 ++ [j], i.2 ++ [j])) (fun i _ k _ h ↦ ?_)
    (Finset.subset_biUnion_of_mem (fun l ↦ s.image fun i ↦ (i.1 ++ [l], i.2 ++ [l]))
      (Finset.mem_univ j)) (fun i _ ↦ by simp) fun _ _ _ ↦ apply_nonneg _ _
  simp only [Prod.mk.injEq, List.append_cancel_right_eq] at h
  exact Prod.ext h.1 h.2

/-- **The remainder estimate, with seminorm constants.** For a compact set `K` there are finitely
many pairs of words and a constant `C` such that
`‖A_t(a) - ∑_{k < N} t^k adjointTerm a k‖ ≤ C (∑ᵢ p_{K,αᵢ,βᵢ}(a)) ⟨ξ⟩ ^ (m - N)` for every symbol
`a` vanishing at positions outside `K`, uniformly in the position and in `t ∈ [0, 1]`. -/
private theorem exists_norm_remainderAt_le (K : Compacts (CoordinateSpace n)) (N : ℕ) :
    ∀ {m : ℝ}, ∃ (s : Finset (List (Fin n) × List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ a : Symbol n V W m, (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) →
        ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x ξ : CoordinateSpace n,
          ‖remainderAt a N t x ξ‖ ≤
            C * (∑ i ∈ s, Symbol.seminorm K i.1 i.2 a) * (1 + ‖ξ‖ ^ 2) ^ ((m - N) / 2) := by
  classical
  induction N with
  | zero =>
    intro m
    obtain ⟨s, C, hC0, hC⟩ := exists_norm_scaledAdjoint_le (V := V) (W := W) (m := m) K
    refine ⟨s.image fun α ↦ (α, []), C, hC0, fun a haK t ht x ξ ↦ ?_⟩
    have ht2 : |t| ≤ 2 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [Finset.sum_image fun _ _ _ _ h ↦ congrArg Prod.fst h]
    simpa [remainderAt] using hC a haK t ht2 x ξ
  | succ N ih =>
    intro m
    -- the remainder of `a` with `N + 1` terms is driven by those of `∂_{x_j} ∂_{ξ_j} a` with `N`
    obtain ⟨s, C, hC0, hC⟩ := ih (m := m - 1)
    set S := univ.biUnion fun l ↦ s.image fun i ↦ (i.1 ++ [l], i.2 ++ [l])
    refine ⟨S, n * C, by positivity, fun a haK t ht x ξ ↦ ?_⟩
    have ha : a.HasCompactSpatialSupport := hasCompactSpatialSupport_iff.2 ⟨K, K.isCompact, haK⟩
    set P := ∑ i ∈ S, Symbol.seminorm K i.1 i.2 a
    set w := (1 + ‖ξ‖ ^ 2) ^ ((m - ((N + 1 : ℕ) : ℝ)) / 2)
    have hw : (1 + ‖ξ‖ ^ 2) ^ ((m - 1 - N) / 2) = w := by
      congr 1
      push_cast
      ring
    have hb (j : Fin n) : ∀ x ∉ K, ∀ ξ,
        (spatialDeriv j (frequencyDeriv j a)).coefficient (x, ξ) = 0 := fun x hx ↦
      coefficient_spatialDeriv_eq_zero K.isCompact.isClosed
        (fun y hy ↦ coefficient_frequencyDeriv_eq_zero (haK y hy) j) j hx
    have hbound : ∀ s' ∈ Set.Ico (0 : ℝ) 1,
        ‖(-Complex.I) • ∑ j, remainderAt (spatialDeriv j (frequencyDeriv j a)) N s' x ξ‖ ≤
          n * C * P * w := by
      intro s' hs'
      rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j, ‖remainderAt (spatialDeriv j (frequencyDeriv j a)) N s' x ξ‖
          ≤ ∑ _j : Fin n, C * P * w := Finset.sum_le_sum fun j _ ↦ by
            refine (hC _ (hb j) s' (Set.Ico_subset_Icc_self hs') x ξ).trans ?_
            rw [hw]
            gcongr
            exact sum_seminorm_spatialDeriv_frequencyDeriv_le K s j a
        _ = n * C * P * w := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s hs ↦ (hasDerivAt_remainderAt ha N (abs_le.2 ⟨by linarith [hs.1], hs.2⟩) x
        ξ).hasDerivWithinAt) hbound t ht
    rw [remainderAt_zero ha, sub_zero, sub_zero] at hmv
    have hB : 0 ≤ n * C * P * w :=
      mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _))
        (by positivity)
    exact hmv.trans (mul_le_of_le_one_right hB ht.2)

end Remainder

/-! ### The remainder symbol -/

section RemainderSymbol

variable [CompleteSpace V] [CompleteSpace W]

variable {a : Symbol n V W m}

variable (a) in
/-- The remainder `a* - ∑_{k < N} adjointTerm a k`, as a symbol of order `m`. -/
private def remainderSymbol (ha : a.HasCompactSpatialSupport) (N : ℕ) : Symbol n W V m :=
  adjoint a ha - ∑ k ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg k)) (a.adjointTerm k)

private theorem coefficient_remainderSymbol (ha : a.HasCompactSpatialSupport) (N : ℕ)
    (x ξ : CoordinateSpace n) :
    (remainderSymbol a ha N).coefficient (x, ξ) = remainderAt a N 1 x ξ := by
  simp [remainderSymbol, remainderAt, scaledAdjoint_one ha]

private theorem spatialDeriv_remainderSymbol (ha : a.HasCompactSpatialSupport) (N : ℕ)
    (j : Fin n) :
    spatialDeriv j (remainderSymbol a ha N) =
      remainderSymbol (spatialDeriv j a) (ha.spatialDeriv j) N := by
  simp only [remainderSymbol, map_sub, map_sum, spatialDeriv_adjoint, spatialDeriv_inclusion,
    spatialDeriv_adjointTerm]

private theorem frequencyDeriv_remainderSymbol (ha : a.HasCompactSpatialSupport) (N : ℕ)
    (j : Fin n) :
    frequencyDeriv j (remainderSymbol a ha N) =
      remainderSymbol (frequencyDeriv j a) (ha.frequencyDeriv j) N := by
  ext1
  funext p
  simp only [remainderSymbol, map_sub, map_sum, coefficient_sub, coefficient_sum,
    frequencyDeriv_inclusion, coefficient_inclusion, Pi.sub_apply, Finset.sum_apply,
    frequencyDeriv_adjoint, coefficient_frequencyDeriv_adjointTerm]

/-- **The symbol estimates of the remainder, with seminorm constants.** For a compact set `K` and
words `α`, `β` there are finitely many pairs of words and a constant `C` such that
`‖∂_x^α ∂_ξ^β (a* - ∑_{k < N} adjointTerm a k)‖ ≤ C (∑ᵢ p_{K,αᵢ,βᵢ}(a)) ⟨ξ⟩ ^ (m - N - |β|)` for
every symbol `a` vanishing at positions outside `K`, uniformly in the position: every mixed
derivative of the remainder of `a` is the remainder of a derivative of `a`, and a frequency
derivative lowers the order of `a` by one. -/
private theorem exists_bound_remainderSymbol (K : Compacts (CoordinateSpace n)) (N : ℕ)
    (α β : List (Fin n)) :
    ∀ {m : ℝ}, ∃ (s : Finset (List (Fin n) × List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport),
        (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) → ∀ x ξ,
          ‖mixedDeriv α β (remainderSymbol a ha N).coefficient x ξ‖ ≤
            C * (∑ i ∈ s, Symbol.seminorm K i.1 i.2 a) *
              (1 + ‖ξ‖ ^ 2) ^ ((m - N - β.length) / 2) := by
  classical
  obtain ⟨D, hD⟩ : ∃ D, α.length + β.length = D := ⟨_, rfl⟩
  induction D generalizing α β with
  | zero =>
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by
      simpa [List.length_eq_zero_iff] using hD
    intro m
    obtain ⟨s, C, hC0, hC⟩ := exists_norm_remainderAt_le (V := V) (W := W) K N (m := m)
    refine ⟨s, C, hC0, fun a ha haK x ξ ↦ ?_⟩
    simpa [coefficient_remainderSymbol] using hC a haK 1 ⟨zero_le_one, le_rfl⟩ x ξ
  | succ D ih =>
    intro m
    rcases List.eq_nil_or_concat' β with rfl | ⟨β', j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α', j, rfl⟩
      · simp at hD
      · obtain ⟨s, C, hC0, hC⟩ := ih α' [] (by simpa using hD) (m := m)
        refine ⟨s.image (Prod.map (· ++ [j]) id), C, hC0, fun a ha haK x ξ ↦ ?_⟩
        rw [Finset.sum_image fun _ _ _ _ h ↦
          ((List.append_left_injective [j]).prodMap Function.injective_id) h,
          ← mixedDeriv_spatialDeriv, spatialDeriv_remainderSymbol]
        simpa using hC _ (ha.spatialDeriv j)
          (fun y hy ↦ coefficient_spatialDeriv_eq_zero K.isCompact.isClosed haK j hy) x ξ
    · have hlen : α.length + β'.length = D := by
        simp only [List.length_append, List.length_singleton] at hD
        omega
      obtain ⟨s, C, hC0, hC⟩ := ih α β' hlen (m := m - 1)
      refine ⟨s.image (Prod.map id (· ++ [j])), C, hC0, fun a ha haK x ξ ↦ ?_⟩
      have e : (m - 1 - N - β'.length) / 2 = (m - N - (β' ++ [j]).length) / 2 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      rw [Finset.sum_image fun _ _ _ _ h ↦
        (Function.injective_id.prodMap (List.append_left_injective [j])) h,
        ← mixedDeriv_frequencyDeriv, frequencyDeriv_remainderSymbol, ← e]
      simpa using hC _ (ha.frequencyDeriv j)
        (fun y hy ↦ coefficient_frequencyDeriv_eq_zero (haK y hy) j) x ξ

/-- The symbol estimates of order `m - N` for the remainder of a symbol with compact spatial
support, uniformly in the position. -/
private theorem HasCompactSpatialSupport.exists_bound_remainderSymbol
    (ha : a.HasCompactSpatialSupport) (N : ℕ) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ x ξ, ‖mixedDeriv α β (remainderSymbol a ha N).coefficient x ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m - N - β.length) / 2) := by
  obtain ⟨K, hK, haK⟩ := hasCompactSpatialSupport_iff.1 ha
  obtain ⟨s, C, hC0, hC⟩ :=
    Symbol.exists_bound_remainderSymbol (V := V) (W := W) ⟨K, hK⟩ N α β (m := m)
  exact ⟨_, mul_nonneg hC0 (Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _), hC a ha haK⟩

variable (a) in
/-- The remainder `a* - ∑_{k < N} adjointTerm a k` of the adjoint expansion after `N` terms, a
symbol of order `m - N` (`adjoint_eq_sum_adjointTerm_add_adjointRemainder`). -/
def adjointRemainder (ha : a.HasCompactSpatialSupport) (N : ℕ) : Symbol n W V (m - N) where
  coefficient := (remainderSymbol a ha N).coefficient
  contDiff_coefficient := (remainderSymbol a ha N).contDiff_coefficient
  exists_bound _ _ α β := by
    obtain ⟨C, hC0, hC⟩ := ha.exists_bound_remainderSymbol N α β
    exact ⟨C, hC0, fun x _ ξ ↦ hC x ξ⟩

@[simp]
theorem coefficient_adjointRemainder (ha : a.HasCompactSpatialSupport) (N : ℕ) :
    (a.adjointRemainder ha N).coefficient =
      (adjoint a ha).coefficient - ∑ k ∈ range N, (a.adjointTerm k).coefficient := by
  simp [adjointRemainder, remainderSymbol]

/-- The remainder of the adjoint expansion satisfies its estimates uniformly in the position. -/
@[simp]
theorem isUniform_adjointRemainder (ha : a.HasCompactSpatialSupport) (N : ℕ) :
    (a.adjointRemainder ha N).IsUniform :=
  isUniform_iff.2 fun α β ↦ ha.exists_bound_remainderSymbol N α β

/-- **Seminorm estimate for the remainder of the adjoint expansion.** For compact sets `K` and `L`
of positions, every `N` and words `α`, `β`, there are finitely many pairs of words and a constant
`C` such that the remainder `R_N(a) = a* - ∑_{k < N} adjointTerm a k`, a symbol of order `m - N`,
satisfies

`p_{L,α,β}(R_N(a)) ≤ C ∑ᵢ p_{K,αᵢ,βᵢ}(a)`

for every symbol `a` of order `m` vanishing at positions outside `K`. -/
theorem exists_seminorm_adjointRemainder_le (K L : Compacts (CoordinateSpace n)) (N : ℕ)
    (α β : List (Fin n)) :
    ∃ (s : Finset (List (Fin n) × List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport),
        (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) →
          Symbol.seminorm L α β (a.adjointRemainder ha N) ≤
            C * ∑ i ∈ s, Symbol.seminorm K i.1 i.2 a := by
  obtain ⟨s, C, hC0, hC⟩ := exists_bound_remainderSymbol (V := V) (W := W) K N α β (m := m)
  exact ⟨s, C, hC0, fun a ha haK ↦ seminorm_le_bound L α β _
    (mul_nonneg hC0 (Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _)) fun x _ ξ ↦ hC a ha haK x ξ⟩

/-- **Seminorm estimate for the adjoint symbol.** For compact sets `K` and `L` of positions and
words `α`, `β`, there are finitely many pairs of words and a constant `C` such that

`p_{L,α,β}(a*) ≤ C ∑ᵢ p_{K,αᵢ,βᵢ}(a)`

for every symbol `a` of order `m` vanishing at positions outside `K`. This is the case of no terms
of the remainder estimate `exists_seminorm_adjointRemainder_le`. -/
theorem exists_seminorm_adjoint_le (K L : Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    ∃ (s : Finset (List (Fin n) × List (Fin n))) (C : ℝ), 0 ≤ C ∧
      ∀ (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport),
        (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) →
          Symbol.seminorm L α β (adjoint a ha) ≤ C * ∑ i ∈ s, Symbol.seminorm K i.1 i.2 a := by
  obtain ⟨s, C, hC0, hC⟩ := exists_bound_remainderSymbol (V := V) (W := W) K 0 α β (m := m)
  refine ⟨s, C, hC0, fun a ha haK ↦ seminorm_le_bound L α β _
    (mul_nonneg hC0 (Finset.sum_nonneg fun _ _ ↦ apply_nonneg _ _)) fun x _ ξ ↦ ?_⟩
  simpa [remainderSymbol] using hC a ha haK x ξ

/-- The remainder of the adjoint expansion is additive in the symbol. -/
@[simp]
theorem adjointRemainder_add {b : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) (N : ℕ) :
    (a + b).adjointRemainder (ha.add hb) N = a.adjointRemainder ha N + b.adjointRemainder hb N := by
  ext1
  simp only [coefficient_adjointRemainder, adjoint_add a b ha hb, adjointTerm_add, coefficient_add,
    Finset.sum_add_distrib]
  abel

/-- The remainder of the adjoint expansion is conjugate-linear in the symbol:
`R_N(c • a) = conj c • R_N(a)`. -/
@[simp]
theorem adjointRemainder_smul (c : ℂ) (ha : a.HasCompactSpatialSupport) (N : ℕ) :
    (c • a).adjointRemainder (ha.smul c) N = (starRingEnd ℂ) c • a.adjointRemainder ha N := by
  ext1
  simp only [coefficient_adjointRemainder, adjoint_smul c a ha, adjointTerm_smul, coefficient_smul,
    Finset.smul_sum, smul_sub]

/-- The remainder of the adjoint expansion of a difference is the difference of the remainders. -/
@[simp]
theorem adjointRemainder_sub {b : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) (N : ℕ) :
    (a - b).adjointRemainder (ha.sub hb) N = a.adjointRemainder ha N - b.adjointRemainder hb N := by
  rw [eq_sub_iff_add_eq, ← adjointRemainder_add]
  congr 1
  exact sub_add_cancel a b

/-- **The asymptotic expansion of the adjoint symbol.** For every `N`,
`a* = ∑_{k < N} adjointTerm a k + adjointRemainder a ha N`, where `adjointTerm a k` is the term
`((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†` of order `m - k` and the remainder is a symbol of
order `m - N`. -/
theorem adjoint_eq_sum_adjointTerm_add_adjointRemainder (ha : a.HasCompactSpatialSupport)
    (N : ℕ) :
    adjoint a ha = ∑ k ∈ range N, inclusion (sub_le_self _ (Nat.cast_nonneg k)) (a.adjointTerm k) +
      inclusion (sub_le_self _ (Nat.cast_nonneg N)) (a.adjointRemainder ha N) := by
  ext1
  simp

/-- The adjoint symbol `a*` is the pointwise adjoint `a†` up to a symbol of order `m - 1`. -/
theorem adjoint_eq_map_add_adjointRemainder_one (ha : a.HasCompactSpatialSupport) :
    adjoint a ha = a.map adjointRealCLM + inclusion (by simp) (a.adjointRemainder ha 1) := by
  ext1
  funext p
  simp [adjointRealCLM_apply]

/-- The adjoint symbol is an asymptotic sum `a* ∼ ∑ₖ adjointTerm a k` of the terms of the
expansion, of orders `m - k`. In particular it is determined by the terms modulo smoothing
symbols (`TauCeti.Symbol.IsAsymptoticSum.isAsymptoticSum_iff_isSmoothing_sub`). -/
theorem isAsymptoticSum_adjoint (ha : a.HasCompactSpatialSupport) :
    IsAsymptoticSum (m := fun k : ℕ ↦ m - k) (inclusion (by simp) (adjoint a ha))
      a.adjointTerm :=
  isAsymptoticSum_iff.2 fun N ↦ ⟨a.adjointRemainder ha N, by simp⟩

end RemainderSymbol

end Symbol

end TauCeti

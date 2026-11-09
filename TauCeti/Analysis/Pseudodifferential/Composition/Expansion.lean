/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import TauCeti.Analysis.Calculus.Taylor
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# The asymptotic expansion of the composition symbol

Let `a` be a symbol of order `m'` and `b` a symbol of order `m` with compact spatial support. The
composition symbol `a # b` of `TauCeti.Analysis.Pseudodifferential.Composition.Basic`, the symbol
of `Op(a) ∘ Op(b)`, has the asymptotic expansion

`a # b ∼ ∑_α (1 / α!) ∂_ξ^α a D_x^α b`, with `D_x = -i ∂_x`:

for every `N`, the remainder `a # b - ∑_{|α| < N} (1 / α!) ∂_ξ^α a D_x^α b` is a symbol of order
`m' + m - N` (`TauCeti.Symbol.exists_sharp_sub_sum_sharpTerm`). In particular `a # b` and the
pointwise composition `a ∘ b` differ by a symbol of order `m' + m - 1`
(`TauCeti.Symbol.exists_sharp_sub_comp`): modulo symbols of order `m' + m - 1`, the composition
symbol is the pointwise composition of the two symbols.

The terms of a fixed degree `k` are collected in `TauCeti.Symbol.sharpTerm a b k`, a symbol of
order `m' + m - k`. Summing over the words `w` of length `k` of coordinate indices instead of the
multi-indices of length `k` counts each `α` exactly `k! / α!` times, so the term is
`(1 / k!) ∑_{|w| = k} ∂_ξ^w a D_x^w b`. It is defined by the recursion

`T₀(a, b) = a ∘ b`, `T_{k+1}(a, b) = (-i / (k + 1)) ∑ⱼ T_k(∂_{ξⱼ} a, ∂_{xⱼ} b)`,

and satisfies the Leibniz rules `TauCeti.Symbol.spatialDeriv_sharpTerm` and
`TauCeti.Symbol.coefficient_frequencyDeriv_sharpTerm`.

## Proof outline

Fix a position `x` and a frequency `ξ`, write `A(ζ) = a(x, ζ)` and `b̂(η) = b̂(η, ξ)`, so that
`(a # b)(x, ξ) = ∫ exp(2πi ⟪η, x⟫) A(ξ + 2πη) ∘ b̂(η) dη`. Replacing `A(ξ + 2πη)` by its Taylor
term `D^k A(ξ) (2πη, …, 2πη) / k!` gives the term `T_k(a, b)(x, ξ)`: by induction on `k`, each
factor `2πηⱼ b̂(η)` is `-i` times the Fourier transform of `∂_{xⱼ} b`, and for `k = 0` Fourier
inversion recovers `b(x, ξ)`. The remainder after `N` terms is therefore the integral of the Taylor
remainder of `A` at `ξ` against `b̂`. Taylor's theorem bounds the Taylor remainder by
`‖2πη‖^N` times the size of `D^N A` on the segment from `ξ` to `ξ + 2πη`, which is at most
`C ⟨ξ⟩ ^ (m' - N) ⟨η⟩ ^ |m' - N|` by Peetre's inequality. The rapid decay of `b̂` absorbs all powers
of `⟨η⟩`, so the remainder is bounded by `C ⟨ξ⟩ ^ (m' + m - N)`.

Both `a # b` and the terms `T_k` satisfy the Leibniz rules for spatial and frequency derivatives,
hence so does the remainder; the estimates for its derivatives follow by induction on their
number, as for the composition symbol itself, each frequency derivative lowering the order of one
of the two symbols by one.

## Main results

* `TauCeti.Symbol.sharpTerm`: the terms of the expansion, with `coefficient_sharpTerm_zero`,
  `sharpTerm_succ` and the sum over words `coefficient_sharpTerm`.
* `TauCeti.Symbol.exists_sharp_sub_sum_sharpTerm`: **the composition expansion**: after `N` terms,
  the remainder is a symbol of order `m' + m - N`.
* `TauCeti.Symbol.exists_sharp_sub_comp`: `a # b - a ∘ b` is a symbol of order `m' + m - 1`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (2.5)–(2.7).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.8.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Set
open scoped ContDiff RealInnerProductSpace Nat

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

/-! ### The terms of the expansion -/

section Term

/-- The term of degree `k` of the asymptotic expansion of the composition symbol `a # b`, the
symbol `∑_{|α| = k} (1 / α!) ∂_ξ^α a D_x^α b` of order `m' + m - k`, where `D_x = -i ∂_x`. It is
defined by the recursion `T₀(a, b) = a ∘ b` and
`T_{k+1}(a, b) = (-i / (k + 1)) ∑ⱼ T_k(∂_{ξⱼ} a, ∂_{xⱼ} b)`. -/
def sharpTerm : {m' : ℝ} → (a : Symbol n W U m') → (b : Symbol n V W m) → (k : ℕ) →
    Symbol n V U (m' + m - k)
  | _, a, b, 0 => inclusion (by simp) (a.comp b)
  | _, a, b, k + 1 => (-Complex.I / (k + 1 : ℂ)) • ∑ j, inclusion (by push_cast; linarith)
      (sharpTerm (frequencyDeriv j a) (spatialDeriv j b) k)

@[simp]
theorem coefficient_sharpTerm_zero (a : Symbol n W U m') (b : Symbol n V W m) :
    (a.sharpTerm b 0).coefficient = (a.comp b).coefficient := by
  rw [sharpTerm, coefficient_inclusion]

theorem sharpTerm_succ (a : Symbol n W U m') (b : Symbol n V W m) (k : ℕ) :
    a.sharpTerm b (k + 1) = (-Complex.I / (k + 1 : ℂ)) • ∑ j, inclusion (by push_cast; linarith)
      ((frequencyDeriv j a).sharpTerm (spatialDeriv j b) k) := by
  rw [sharpTerm]

/-- The term of degree `k` as a sum over the words `w` of length `k` of coordinate indices:
`T_k(a, b) = ((-i) ^ k / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b`. Each multi-index `α` of length `k` is
the multiset of letters of exactly `k! / α!` words, so this is
`∑_{|α| = k} (1 / α!) ∂_ξ^α a D_x^α b`. -/
theorem coefficient_sharpTerm (a : Symbol n W U m') (b : Symbol n V W m) (k : ℕ)
    (x ξ : CoordinateSpace n) :
    (a.sharpTerm b k).coefficient (x, ξ) = ((-Complex.I) ^ k / k !) • ∑ w : Fin k → Fin n,
      (mixedDeriv [] (List.ofFn w) a.coefficient x ξ).comp
        (mixedDeriv (List.ofFn w) [] b.coefficient x ξ) := by
  induction k generalizing m' a b with
  | zero => simp
  | succ k ih =>
    rw [sharpTerm_succ, coefficient_smul, Pi.smul_apply, coefficient_sum, Finset.sum_apply]
    simp only [coefficient_inclusion, ih, mixedDeriv_frequencyDeriv, mixedDeriv_spatialDeriv,
      Finset.smul_sum, smul_smul]
    rw [← (Fin.snocEquiv fun _ ↦ Fin n).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.snocEquiv_apply, List.ofFn_succ', Fin.snoc_last, Fin.snoc_castSucc,
      List.concat_eq_append]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun w _ ↦ ?_
    congr 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- **Leibniz rule in the position** for the terms of the expansion. -/
theorem spatialDeriv_sharpTerm (j : Fin n) (a : Symbol n W U m') (b : Symbol n V W m) (k : ℕ) :
    spatialDeriv j (a.sharpTerm b k) =
      (spatialDeriv j a).sharpTerm b k + a.sharpTerm (spatialDeriv j b) k := by
  induction k generalizing m' a b with
  | zero =>
    ext1
    simp [sharpTerm, spatialDeriv_comp]
  | succ k ih =>
    simp only [sharpTerm_succ, map_smul, map_sum, spatialDeriv_inclusion, ih, map_add,
      Finset.sum_add_distrib, smul_add, spatialDeriv_frequencyDeriv]
    congr 3
    funext i
    rw [spatialDeriv_comm]

/-- **Leibniz rule in the frequency** for the terms of the expansion. -/
theorem coefficient_frequencyDeriv_sharpTerm (j : Fin n) (a : Symbol n W U m')
    (b : Symbol n V W m) (k : ℕ) :
    (frequencyDeriv j (a.sharpTerm b k)).coefficient =
      ((frequencyDeriv j a).sharpTerm b k).coefficient +
        (a.sharpTerm (frequencyDeriv j b) k).coefficient := by
  induction k generalizing m' a b with
  | zero =>
    have h := congrArg coefficient (frequencyDeriv_comp j a b)
    simp only [coefficient_add, coefficient_inclusion] at h
    simp [sharpTerm, h]
  | succ k ih =>
    simp only [sharpTerm_succ, map_smul, map_sum, frequencyDeriv_inclusion, coefficient_smul,
      coefficient_sum, coefficient_inclusion, ih, Finset.sum_add_distrib, smul_add]
    congr 3
    · funext i
      rw [frequencyDeriv_comm]
    · funext i
      rw [spatialDeriv_frequencyDeriv]

end Term

/-! ### The terms as Fourier integrals -/

section Integral

variable {a : Symbol n W U m'} {b : Symbol n V W m}

/-- For every real `s` there is a constant `D` such that every continuous function `f` with
`‖f η‖ ≤ C ⟨η⟩ ^ s ‖b̂(η, ξ)‖` is integrable, with `‖∫ f‖ ≤ C D ⟨ξ⟩ ^ m`: the rapid decay of `b̂`
absorbs every power of `⟨η⟩`. -/
private theorem exists_integrable_and_norm_integral_le (hb : b.HasCompactSpatialSupport) (s : ℝ) :
    ∃ D, 0 ≤ D ∧ ∀ (ξ : CoordinateSpace n) (f : CoordinateSpace n → V →L[ℂ] U) (C : ℝ), 0 ≤ C →
      Continuous f →
      (∀ η, ‖f η‖ ≤ C * (1 + ‖η‖ ^ 2) ^ (s / 2) * ‖𝓕 (fun y ↦ b.coefficient (y, ξ)) η‖) →
        Integrable f ∧ ‖∫ η, f η‖ ≤ C * D * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  have hw : Integrable fun η : CoordinateSpace n ↦ (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) :=
    integrable_rpow_neg_one_add_norm_sq (by rw [finrank_euclideanSpace_fin]; linarith)
  obtain ⟨Cb, hCb0, hCb⟩ := hb.exists_norm_fourier_slice_le (s + n + 1)
  set I := ∫ η : CoordinateSpace n, (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hI : 0 ≤ I := integral_nonneg fun η ↦ by positivity
  refine ⟨Cb * I, mul_nonneg hCb0 hI, fun ξ f C hC hf hfC ↦ ?_⟩
  have hbound (η : CoordinateSpace n) : ‖f η‖ ≤
      C * Cb * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
    have hη : (1 + ‖η‖ ^ 2) ^ (s / 2) * (1 + ‖η‖ ^ 2) ^ (-(s + n + 1) / 2) =
        (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
      rw [← Real.rpow_add (by positivity)]
      ring_nf
    calc ‖f η‖ ≤ C * (1 + ‖η‖ ^ 2) ^ (s / 2) *
          (Cb * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-(s + n + 1) / 2)) :=
          (hfC η).trans (by gcongr; exact hCb η ξ)
      _ = C * Cb * (1 + ‖ξ‖ ^ 2) ^ (m / 2) *
          ((1 + ‖η‖ ^ 2) ^ (s / 2) * (1 + ‖η‖ ^ 2) ^ (-(s + n + 1) / 2)) := by ring
      _ = _ := by rw [hη]
  have hint := hw.const_mul (C * Cb * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
  refine ⟨hint.mono' hf.aestronglyMeasurable (.of_forall hbound), ?_⟩
  refine (norm_integral_le_of_norm_le hint (.of_forall hbound)).trans_eq ?_
  rw [integral_const_mul]
  ring

private theorem continuous_fourier_slice_apply (hb : b.HasCompactSpatialSupport)
    (ξ : CoordinateSpace n) : Continuous fun η ↦ 𝓕 (fun y ↦ b.coefficient (y, ξ)) η := by
  simpa only [Function.comp_def, id] using
    hb.continuous_fourier_slice.comp (continuous_id.prodMk continuous_const)

variable (a b) in
/-- The integrand `exp(2πi ⟪η, x⟫) (D^k A(ξ) (2πη, …, 2πη) / k!) ∘ b̂(η, ξ)` of the term of degree
`k`, where `A = a(x, ·)`: the Taylor term of degree `k` of `ζ ↦ a(x, ξ + ζ)` at `ζ = 2πη`, in
place of `a(x, ξ + 2πη)` in the integrand of `a # b`. -/
private def taylorIntegrand (k : ℕ) (x ξ η : CoordinateSpace n) : V →L[ℂ] U :=
  (𝐞 ⟪η, x⟫ : ℂ) • ((k ! : ℝ)⁻¹ • iteratedFDeriv ℝ k (fun ζ ↦ a.coefficient (x, ζ)) ξ
    (fun _ ↦ (2 * π) • η)).comp (𝓕 (fun y ↦ b.coefficient (y, ξ)) η)

private theorem norm_taylorIntegrand_le (k : ℕ) (x ξ η : CoordinateSpace n) :
    ‖taylorIntegrand a b k x ξ η‖ ≤
      (k ! : ℝ)⁻¹ * ‖iteratedFDeriv ℝ k (fun ζ ↦ a.coefficient (x, ζ)) ξ‖ * (2 * π) ^ k *
        (1 + ‖η‖ ^ 2) ^ ((k : ℝ) / 2) * ‖𝓕 (fun y ↦ b.coefficient (y, ξ)) η‖ := by
  set M := iteratedFDeriv ℝ k (fun ζ ↦ a.coefficient (x, ζ)) ξ
  have hM : ‖M (fun _ ↦ (2 * π) • η)‖ ≤ ‖M‖ * ((2 * π) ^ k * (1 + ‖η‖ ^ 2) ^ ((k : ℝ) / 2)) := by
    refine (M.le_opNorm _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_smul,
      Real.norm_of_nonneg (by positivity), mul_pow]
    gcongr
    exact norm_pow_le_one_add_norm_sq_rpow η k
  rw [taylorIntegrand, norm_smul, Circle.norm_coe, one_mul]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  calc _ ≤ (k ! : ℝ)⁻¹ * (‖M‖ * ((2 * π) ^ k * (1 + ‖η‖ ^ 2) ^ ((k : ℝ) / 2))) *
        ‖𝓕 (fun y ↦ b.coefficient (y, ξ)) η‖ := by gcongr
    _ = _ := by ring

private theorem continuous_taylorIntegrand (hb : b.HasCompactSpatialSupport) (k : ℕ)
    (x ξ : CoordinateSpace n) : Continuous (taylorIntegrand a b k x ξ) := by
  have he : Continuous fun η : CoordinateSpace n ↦ (𝐞 ⟪η, x⟫ : ℂ) := by fun_prop
  have hM : Continuous fun η : CoordinateSpace n ↦
      iteratedFDeriv ℝ k (fun ζ ↦ a.coefficient (x, ζ)) ξ (fun _ ↦ (2 * π) • η) :=
    (iteratedFDeriv ℝ k (fun ζ ↦ a.coefficient (x, ζ)) ξ).cont.comp
      (continuous_pi fun _ ↦ continuous_id.const_smul ((2 : ℝ) * π))
  exact he.smul ((hM.const_smul ((k ! : ℝ)⁻¹)).clm_comp (continuous_fourier_slice_apply hb ξ))

private theorem integrable_taylorIntegrand (hb : b.HasCompactSpatialSupport) (k : ℕ)
    (x ξ : CoordinateSpace n) : Integrable (taylorIntegrand a b k x ξ) := by
  obtain ⟨D, -, hD⟩ := exists_integrable_and_norm_integral_le (U := U) hb k
  exact (hD ξ _ _ (by positivity) (continuous_taylorIntegrand hb k x ξ)
    (norm_taylorIntegrand_le k x ξ)).1

/-- The recursion of the Taylor integrands: the factor `2πηⱼ b̂(η, ξ)` of the derivative of order
`k + 1` in the direction `2πη` is `-i` times the Fourier transform of `∂_{xⱼ} b`. -/
private theorem taylorIntegrand_succ (hb : b.HasCompactSpatialSupport) (k : ℕ)
    (x ξ η : CoordinateSpace n) :
    taylorIntegrand a b (k + 1) x ξ η = (-Complex.I / (k + 1 : ℂ)) •
      ∑ j, taylorIntegrand (frequencyDeriv j a) (spatialDeriv j b) k x ξ η := by
  have hA : ContDiff ℝ (k + 1) fun ζ ↦ a.coefficient (x, ζ) :=
    (a.contDiff_coefficient.comp (contDiff_prodMk_right x)).of_le (by exact_mod_cast le_top)
  have hfd (j : Fin n) : (fun ζ ↦ (frequencyDeriv j a).coefficient (x, ζ)) =
      coordinateDeriv [j] (fun ζ ↦ a.coefficient (x, ζ)) :=
    funext fun ζ ↦ coefficient_frequencyDeriv j a x ζ
  simp only [taylorIntegrand, iteratedFDeriv_succ_const_eq_sum_coordinateDeriv hA, hfd,
    hb.fourier_spatialDeriv_slice]
  ext v
  simp only [smul_apply, ContinuousLinearMap.comp_apply, sum_apply, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [← Complex.coe_smul, smul_smul]
  congr 1
  have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hf : (k ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  simp only [PiLp.smul_apply, smul_eq_mul, EuclideanSpace.inner_single_right, Nat.factorial_succ,
    conj_trivial, one_mul]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem integral_taylorIntegrand [CompleteSpace W] [CompleteSpace U]
    (hb : b.HasCompactSpatialSupport) (k : ℕ) (x ξ : CoordinateSpace n) :
    ∫ η, taylorIntegrand a b k x ξ η = (a.sharpTerm b k).coefficient (x, ξ) := by
  induction k generalizing m' a b with
  | zero =>
    have h (η : CoordinateSpace n) : taylorIntegrand a b 0 x ξ η =
        ContinuousLinearMap.compL ℂ V W U (a.coefficient (x, ξ))
          ((𝐞 ⟪η, x⟫ : ℂ) • 𝓕 (fun y ↦ b.coefficient (y, ξ)) η) := by
      simp [taylorIntegrand]
    simp_rw [h]
    rw [ContinuousLinearMap.integral_comp_comm _
      (hb.integrable_fourierChar_smul_fourier_slice x ξ),
      hb.integral_fourierChar_smul_fourier_slice, coefficient_sharpTerm_zero]
    simp
  | succ k ih =>
    simp_rw [taylorIntegrand_succ hb]
    rw [integral_smul, integral_finsetSum _ fun j _ ↦
      integrable_taylorIntegrand (hb.spatialDeriv j) k x ξ, sharpTerm_succ]
    simp only [coefficient_smul, coefficient_sum, coefficient_inclusion, Pi.smul_apply,
      Finset.sum_apply, ih (hb.spatialDeriv _)]

end Integral

/-! ### The remainder of the expansion -/

section Remainder

variable {a : Symbol n W U m'} {b : Symbol n V W m}

variable (a b) in
/-- The integrand of the remainder after `N` terms: the Taylor remainder of order `N` of
`ζ ↦ a(x, ξ + ζ)` at `ζ = 2πη`, in place of `a(x, ξ + 2πη)` in the integrand of `a # b`. -/
private def remainderIntegrand (N : ℕ) (x ξ η : CoordinateSpace n) : V →L[ℂ] U :=
  (𝐞 ⟪η, x⟫ : ℂ) • (a.coefficient (x, ξ + (2 * π) • η) -
    ∑ k ∈ Finset.range N, (k ! : ℝ)⁻¹ •
      iteratedFDeriv ℝ k (fun ζ ↦ a.coefficient (x, ζ)) ξ (fun _ ↦ (2 * π) • η)).comp
    (𝓕 (fun y ↦ b.coefficient (y, ξ)) η)

private theorem remainderIntegrand_eq (N : ℕ) (x ξ η : CoordinateSpace n) :
    remainderIntegrand a b N x ξ η =
      (𝐞 ⟪η, x⟫ : ℂ) • (a.coefficient (x, ξ + (2 * π) • η)).comp
        (𝓕 (fun y ↦ b.coefficient (y, ξ)) η) -
      ∑ k ∈ Finset.range N, taylorIntegrand a b k x ξ η := by
  ext v
  simp [remainderIntegrand, taylorIntegrand, sum_apply, smul_sub, Finset.smul_sum]

private theorem continuous_remainderIntegrand (hb : b.HasCompactSpatialSupport) (N : ℕ)
    (x ξ : CoordinateSpace n) : Continuous (remainderIntegrand a b N x ξ) := by
  have he : Continuous fun η : CoordinateSpace n ↦ (𝐞 ⟪η, x⟫ : ℂ) := by fun_prop
  have hA : Continuous fun η : CoordinateSpace n ↦ a.coefficient (x, ξ + (2 * π) • η) :=
    a.contDiff_coefficient.continuous.comp
      (continuous_const.prodMk (continuous_const.add (continuous_id.const_smul ((2 : ℝ) * π))))
  have hM (k : ℕ) : Continuous fun η : CoordinateSpace n ↦
      iteratedFDeriv ℝ k (fun ζ ↦ a.coefficient (x, ζ)) ξ (fun _ ↦ (2 * π) • η) :=
    (iteratedFDeriv ℝ k (fun ζ ↦ a.coefficient (x, ζ)) ξ).cont.comp
      (continuous_pi fun _ ↦ continuous_id.const_smul ((2 : ℝ) * π))
  have hS : Continuous fun η : CoordinateSpace n ↦ ∑ k ∈ Finset.range N, (k ! : ℝ)⁻¹ •
      iteratedFDeriv ℝ k (fun ζ ↦ a.coefficient (x, ζ)) ξ (fun _ ↦ (2 * π) • η) :=
    continuous_finsetSum _ fun k _ ↦ (hM k).const_smul ((k ! : ℝ)⁻¹)
  exact he.smul ((hA.sub hS).clm_comp (continuous_fourier_slice_apply hb ξ))

/-- On the segment from `ξ` to `ξ + 2πη`, the derivatives of order `N` of `ζ ↦ a(x, ζ)` are at
most `C ⟨ξ⟩ ^ (m' - N) ⟨η⟩ ^ |m' - N|`, uniformly for positions in a compact set: the symbol
estimates of order `m' - N` and Peetre's inequality. -/
private theorem exists_norm_iteratedFDeriv_coefficient_add_smul_le
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ η, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ N (fun ζ ↦ a.coefficient (x, ζ)) (ξ + t • (2 * π) • η)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m' - N) / 2) * (1 + ‖η‖ ^ 2) ^ (|m' - N| / 2) := by
  set s := m' - N
  obtain ⟨G, hG0, hG⟩ := a.exists_norm_iteratedFDeriv_coordinateDeriv_le hK [] N
  have h2π : (1 : ℝ) ≤ 2 * π := by linarith [Real.two_le_pi]
  refine ⟨G * 2 ^ (|s| / 2) * (2 * π) ^ |s|, by positivity, fun x hx ξ η t ht ↦ ?_⟩
  set v := (2 * π) • η
  have hv : ‖v‖ = 2 * π * ‖η‖ := by rw [norm_smul, Real.norm_of_nonneg Real.two_pi_pos.le]
  have htv : (1 + ‖t • v‖ ^ 2) ^ (|s| / 2) ≤ (1 + ‖v‖ ^ 2) ^ (|s| / 2) := by
    have : ‖t • v‖ ≤ ‖v‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    gcongr
  have hscale := one_add_norm_sq_rpow_le_of_norm_eq_mul h2π |s| hv
  rw [abs_abs] at hscale
  calc _ ≤ G * (1 + ‖ξ + t • v‖ ^ 2) ^ (s / 2) := by simpa using hG x hx (ξ + t • v)
    _ ≤ G * (2 ^ (|s| / 2) * (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖t • v‖ ^ 2) ^ (|s| / 2)) := by
        gcongr
        exact one_add_norm_add_sq_rpow_le_mul s ξ (t • v)
    _ ≤ G * (2 ^ (|s| / 2) * (1 + ‖ξ‖ ^ 2) ^ (s / 2) *
          ((2 * π) ^ |s| * (1 + ‖η‖ ^ 2) ^ (|s| / 2))) := by
        gcongr
        exact htv.trans hscale
    _ = _ := by ring

/-- **The Taylor remainder.** After `N + 1` terms the remainder integrand is at most
`C ⟨ξ⟩ ^ (m' - N - 1) ⟨η⟩ ^ (|m' - N - 1| + N + 1) ‖b̂(η, ξ)‖`, uniformly for positions in a compact
set, by Taylor's theorem along the segment from `ξ` to `ξ + 2πη`. -/
private theorem exists_norm_remainderIntegrand_le {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (N : ℕ) : ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ η, ‖remainderIntegrand a b (N + 1) x ξ η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m' - (N + 1)) / 2) *
        (1 + ‖η‖ ^ 2) ^ ((|m' - (N + 1)| + (N + 1)) / 2) *
          ‖𝓕 (fun y ↦ b.coefficient (y, ξ)) η‖ := by
  obtain ⟨G, hG0, hG⟩ := exists_norm_iteratedFDeriv_coefficient_add_smul_le (a := a) hK (N + 1)
  push_cast at hG
  refine ⟨G * (2 * π) ^ (N + 1) / N !, by positivity, fun x hx ξ η ↦ ?_⟩
  have hA : ContDiff ℝ (N + 1) fun ζ ↦ a.coefficient (x, ζ) :=
    (a.contDiff_coefficient.comp (contDiff_prodMk_right x)).of_le (by exact_mod_cast le_top)
  have htaylor := norm_sub_sum_iteratedFDeriv_le hA (hG x hx ξ η)
  have hv : ‖(2 * π) • η‖ = 2 * π * ‖η‖ := by
    rw [norm_smul, Real.norm_of_nonneg Real.two_pi_pos.le]
  have hη := norm_pow_le_one_add_norm_sq_rpow η (N + 1)
  have hw : (1 + ‖η‖ ^ 2) ^ (|m' - (N + 1)| / 2) * (1 + ‖η‖ ^ 2) ^ (((N + 1 : ℕ) : ℝ) / 2) =
      (1 + ‖η‖ ^ 2) ^ ((|m' - (N + 1)| + (N + 1)) / 2) := by
    rw [← Real.rpow_add (by positivity)]
    push_cast
    ring_nf
  rw [remainderIntegrand, norm_smul, Circle.norm_coe, one_mul]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  -- Taylor's theorem, then `‖2πη‖ ^ (N + 1) ≤ (2π) ^ (N + 1) ⟨η⟩ ^ (N + 1)`.
  calc _ ≤ G * (1 + ‖ξ‖ ^ 2) ^ ((m' - (N + 1)) / 2) * (1 + ‖η‖ ^ 2) ^ (|m' - (N + 1)| / 2) *
        ‖(2 * π) • η‖ ^ (N + 1) / N ! * ‖𝓕 (fun y ↦ b.coefficient (y, ξ)) η‖ := by
        gcongr
    _ = G * (2 * π) ^ (N + 1) / N ! * (1 + ‖ξ‖ ^ 2) ^ ((m' - (N + 1)) / 2) *
        ((1 + ‖η‖ ^ 2) ^ (|m' - (N + 1)| / 2) * ‖η‖ ^ (N + 1)) *
          ‖𝓕 (fun y ↦ b.coefficient (y, ξ)) η‖ := by
        rw [hv, mul_pow]
        ring
    _ ≤ G * (2 * π) ^ (N + 1) / N ! * (1 + ‖ξ‖ ^ 2) ^ ((m' - (N + 1)) / 2) *
        ((1 + ‖η‖ ^ 2) ^ (|m' - (N + 1)| / 2) * (1 + ‖η‖ ^ 2) ^ (((N + 1 : ℕ) : ℝ) / 2)) *
          ‖𝓕 (fun y ↦ b.coefficient (y, ξ)) η‖ := by
        gcongr
    _ = _ := by rw [hw]

/-- The remainder integrand after `N + 1` terms is integrable, and its integral is at most
`C ⟨ξ⟩ ^ (m' + m - N - 1)`, uniformly for positions in a compact set. -/
private theorem exists_norm_integral_remainderIntegrand_le (hb : b.HasCompactSpatialSupport)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, Integrable (remainderIntegrand a b (N + 1) x ξ) ∧
      ‖∫ η, remainderIntegrand a b (N + 1) x ξ η‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - (N + 1)) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_remainderIntegrand_le (a := a) (b := b) hK N
  obtain ⟨D, hD0, hD⟩ :=
    exists_integrable_and_norm_integral_le (U := U) hb (|m' - (N + 1)| + (N + 1))
  refine ⟨C * D, mul_nonneg hC0 hD0, fun x hx ξ ↦ ?_⟩
  obtain ⟨hint, hle⟩ := hD ξ _ (C * (1 + ‖ξ‖ ^ 2) ^ ((m' - (N + 1)) / 2)) (by positivity)
    (continuous_remainderIntegrand hb (N + 1) x ξ) (hC x hx ξ)
  refine ⟨hint, hle.trans_eq ?_⟩
  have h : (1 + ‖ξ‖ ^ 2) ^ ((m' - (N + 1)) / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) =
      (1 + ‖ξ‖ ^ 2) ^ ((m' + m - (N + 1)) / 2) := by
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  rw [← h]
  ring

variable (a) in
/-- The remainder `a # b - ∑_{k < N} T_k(a, b)` of the expansion after `N` terms, as a symbol of
order `m' + m`. -/
private def sharpRemainder (hb : b.HasCompactSpatialSupport) (N : ℕ) : Symbol n V U (m' + m) :=
  a.sharp b hb - ∑ k ∈ Finset.range N, inclusion (sub_le_self _ k.cast_nonneg) (a.sharpTerm b k)

private theorem coefficient_sharpRemainder (hb : b.HasCompactSpatialSupport) (N : ℕ) :
    (a.sharpRemainder hb N).coefficient =
      (a.sharp b hb).coefficient - ∑ k ∈ Finset.range N, (a.sharpTerm b k).coefficient := by
  simp [sharpRemainder]

/-- The remainder after `N + 1` terms is the integral of the remainder integrand. -/
private theorem coefficient_sharpRemainder_succ [CompleteSpace W] [CompleteSpace U]
    (hb : b.HasCompactSpatialSupport) (N : ℕ) (x ξ : CoordinateSpace n)
    (hint : Integrable (remainderIntegrand a b (N + 1) x ξ)) :
    (a.sharpRemainder hb (N + 1)).coefficient (x, ξ) =
      ∫ η, remainderIntegrand a b (N + 1) x ξ η := by
  have htay : Integrable fun η ↦ ∑ k ∈ Finset.range (N + 1), taylorIntegrand a b k x ξ η :=
    integrable_finsetSum (f := fun k η ↦ taylorIntegrand a b k x ξ η) _
      fun k _ ↦ integrable_taylorIntegrand hb k x ξ
  have hsharp : (fun η ↦ (𝐞 ⟪η, x⟫ : ℂ) • (a.coefficient (x, ξ + (2 * π) • η)).comp
      (𝓕 (fun y ↦ b.coefficient (y, ξ)) η)) = fun η ↦ remainderIntegrand a b (N + 1) x ξ η +
        ∑ k ∈ Finset.range (N + 1), taylorIntegrand a b k x ξ η := by
    funext η
    rw [remainderIntegrand_eq, sub_add_cancel]
  rw [coefficient_sharpRemainder, Pi.sub_apply, coefficient_sharp, hsharp,
    integral_add hint htay, integral_finsetSum _ fun k _ ↦ integrable_taylorIntegrand hb k x ξ,
    Finset.sum_apply]
  simp only [integral_taylorIntegrand hb]
  abel

/-- The remainder after `N` terms is at most `C ⟨ξ⟩ ^ (m' + m - N)`, uniformly for positions in a
compact set. -/
private theorem exists_norm_sharpRemainder_le [CompleteSpace W] [CompleteSpace U]
    (hb : b.HasCompactSpatialSupport) (N : ℕ) {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖(a.sharpRemainder hb N).coefficient (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - N) / 2) := by
  cases N with
  | zero =>
    obtain ⟨C, hC0, hC⟩ := (a.sharp b hb).exists_bound K hK [] []
    exact ⟨C, hC0, fun x hx ξ ↦ by simpa [coefficient_sharpRemainder] using hC x hx ξ⟩
  | succ N =>
    obtain ⟨C, hC0, hC⟩ := exists_norm_integral_remainderIntegrand_le (a := a) hb hK N
    refine ⟨C, hC0, fun x hx ξ ↦ ?_⟩
    rw [coefficient_sharpRemainder_succ hb N x ξ (hC x hx ξ).1]
    push_cast
    exact (hC x hx ξ).2

/-- **Leibniz rule in the position** for the remainder. -/
private theorem spatialDeriv_sharpRemainder (hb : b.HasCompactSpatialSupport) (j : Fin n)
    (N : ℕ) : spatialDeriv j (a.sharpRemainder hb N) =
      (spatialDeriv j a).sharpRemainder hb N + a.sharpRemainder (hb.spatialDeriv j) N := by
  simp only [sharpRemainder, map_sub, map_sum, spatialDeriv_inclusion, spatialDeriv_sharp,
    spatialDeriv_sharpTerm, map_add, Finset.sum_add_distrib]
  abel

/-- **Leibniz rule in the frequency** for the remainder. -/
private theorem coefficient_frequencyDeriv_sharpRemainder (hb : b.HasCompactSpatialSupport)
    (j : Fin n) (N : ℕ) : (frequencyDeriv j (a.sharpRemainder hb N)).coefficient =
      ((frequencyDeriv j a).sharpRemainder hb N).coefficient +
        (a.sharpRemainder (hb.frequencyDeriv j) N).coefficient := by
  funext ⟨x, ξ⟩
  have h (k : ℕ) := congrFun (coefficient_frequencyDeriv_sharpTerm j a b k) (x, ξ)
  simp only [sharpRemainder, map_sub, map_sum, frequencyDeriv_inclusion, coefficient_sub,
    coefficient_sum, coefficient_inclusion, Pi.sub_apply, Pi.add_apply, Finset.sum_apply,
    coefficient_frequencyDeriv_sharp hb, h, Finset.sum_add_distrib]
  abel

/-- The symbol estimates of order `m' + m - N` for the remainder, by induction on the number of
derivatives: each derivative falls on one of the two symbols by the Leibniz rules, and a frequency
derivative lowers the order of that symbol by one. -/
private theorem exists_bound_sharpRemainder [CompleteSpace W] [CompleteSpace U] (N L : ℕ) :
    ∀ {m m' : ℝ} (a : Symbol n W U m') (b : Symbol n V W m) (hb : b.HasCompactSpatialSupport),
      ∀ α β : List (Fin n), α.length + β.length = L → ∀ K : Set (CoordinateSpace n),
        IsCompact K → ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
          ‖mixedDeriv α β (a.sharpRemainder hb N).coefficient x ξ‖ ≤
            C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - N - β.length) / 2) := by
  induction L with
  | zero =>
    intro m m' a b hb α β hL K hK
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by
      simpa [List.length_eq_zero_iff] using hL
    obtain ⟨C, hC0, hC⟩ := exists_norm_sharpRemainder_le (a := a) hb N hK
    exact ⟨C, hC0, fun x hx ξ ↦ by simpa using hC x hx ξ⟩
  | succ L ih =>
    intro m m' a b hb α β hL K hK
    rcases List.eq_nil_or_concat' β with rfl | ⟨β', j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α', j, rfl⟩
      · simp at hL
      · -- The innermost derivative is `∂_{xⱼ}`: it falls on `a` or on `b`, keeping both orders.
        have hlen : α'.length + ([] : List (Fin n)).length = L := by
          simp only [List.length_append, List.length_singleton, List.length_nil] at hL ⊢
          omega
        obtain ⟨C₁, hC₁0, hC₁⟩ := ih (spatialDeriv j a) b hb α' [] hlen K hK
        obtain ⟨C₂, hC₂0, hC₂⟩ := ih a (spatialDeriv j b) (hb.spatialDeriv j) α' [] hlen K hK
        refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x hx ξ ↦ ?_⟩
        rw [← mixedDeriv_spatialDeriv, spatialDeriv_sharpRemainder, coefficient_add]
        exact norm_mixedDeriv_add_le ((spatialDeriv j a).sharpRemainder hb N).contDiff_coefficient
          (a.sharpRemainder (hb.spatialDeriv j) N).contDiff_coefficient (hC₁ x hx ξ) (hC₂ x hx ξ)
    · -- The innermost derivative is `∂_{ξⱼ}`: it falls on `a` or on `b`, lowering that order.
      have hlen : α.length + β'.length = L := by
        simp only [List.length_append, List.length_singleton] at hL
        omega
      obtain ⟨C₁, hC₁0, hC₁⟩ := ih (frequencyDeriv j a) b hb α β' hlen K hK
      obtain ⟨C₂, hC₂0, hC₂⟩ :=
        ih a (frequencyDeriv j b) (hb.frequencyDeriv j) α β' hlen K hK
      refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x hx ξ ↦ ?_⟩
      have e₁ : (m' - 1 + m - N - β'.length) / 2 = (m' + m - N - (β' ++ [j]).length) / 2 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      have e₂ : (m' + (m - 1) - N - β'.length) / 2 =
          (m' + m - N - (β' ++ [j]).length) / 2 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      have h₁ := hC₁ x hx ξ
      have h₂ := hC₂ x hx ξ
      rw [e₁] at h₁
      rw [e₂] at h₂
      rw [← mixedDeriv_frequencyDeriv, coefficient_frequencyDeriv_sharpRemainder]
      exact norm_mixedDeriv_add_le ((frequencyDeriv j a).sharpRemainder hb N).contDiff_coefficient
        (a.sharpRemainder (hb.frequencyDeriv j) N).contDiff_coefficient h₁ h₂

end Remainder

/-! ### The expansion -/

section Expansion

variable {a : Symbol n W U m'} {b : Symbol n V W m} [CompleteSpace W] [CompleteSpace U]

/-- **The asymptotic expansion of the composition symbol.** For a symbol `a` of order `m'` and a
symbol `b` of order `m` with compact spatial support, the remainder
`a # b - ∑_{k < N} T_k(a, b)` after the terms `T_k(a, b) = ∑_{|α| = k} (1 / α!) ∂_ξ^α a D_x^α b`
of degree `k < N` is a symbol of order `m' + m - N`. -/
theorem exists_sharp_sub_sum_sharpTerm (hb : b.HasCompactSpatialSupport) (N : ℕ) :
    ∃ r : Symbol n V U (m' + m - N), r.coefficient =
      (a.sharp b hb).coefficient - ∑ k ∈ Finset.range N, (a.sharpTerm b k).coefficient :=
  ⟨⟨(a.sharpRemainder hb N).coefficient, (a.sharpRemainder hb N).contDiff_coefficient,
    fun K hK α β ↦ exists_bound_sharpRemainder N _ a b hb α β rfl K hK⟩,
    coefficient_sharpRemainder hb N⟩

/-- **The leading term of a composition.** The composition symbol `a # b` and the pointwise
composition `a ∘ b` differ by a symbol of order `m' + m - 1`. -/
theorem exists_sharp_sub_comp (hb : b.HasCompactSpatialSupport) :
    ∃ r : Symbol n V U (m' + m - 1), r.coefficient =
      (a.sharp b hb).coefficient - (a.comp b).coefficient := by
  obtain ⟨r, hr⟩ := exists_sharp_sub_sum_sharpTerm (a := a) hb 1
  exact ⟨inclusion (by simp) r, by simpa using hr⟩

end Expansion

end Symbol

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
public import TauCeti.Analysis.Pseudodifferential.Symbol.Frequency
public import Mathlib.RingTheory.Binomial
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Deriv
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.RingTheory.Binomial

/-!
# The Bessel potential is a classical symbol

The Bessel weight `⟨ξ / 2π⟩ ^ s = (1 + ‖ξ / 2π‖ ^ 2) ^ (s / 2)` in the angular frequency `ξ`
(`TauCeti.Symbol.besselPotential`), the symbol of Mathlib's Bessel potential, is a classical
symbol of order `s` for every real `s` (`TauCeti.ClassicalSymbol.besselPotential`). Its expansion
is the binomial series of `(1 + ‖ξ / 2π‖⁻²) ^ (s / 2)`:

`⟨ξ / 2π⟩ ^ s ∼ ∑ₖ (s / 2 choose k) ‖ξ / 2π‖ ^ (s - 2k)`,

so the homogeneous term of degree `s - j` is `(s / 2 choose j / 2) ‖ξ / 2π‖ ^ (s - j)` for even
`j` and zero for odd `j` (`TauCeti.ClassicalSymbol.coefficient_term_besselPotential`). In
particular the principal symbol is `‖ξ / 2π‖ ^ s`
(`TauCeti.ClassicalSymbol.coefficient_principal_besselPotential`), which is invertible away from
`ξ = 0`, so the Bessel potential is elliptic
(`TauCeti.ClassicalSymbol.isElliptic_besselPotential`). Composing a classical symbol with the
Bessel potential of order `t`, as `TauCeti.ClassicalSymbol.comp`, therefore changes its order by
`t` within the classical calculus and multiplies its principal symbol by `‖ξ / 2π‖ ^ t`.

## Proof outline

Write `u = ‖ξ / 2π‖ ^ 2`, `a = s / 2` and, for a frequency cutoff `χ`,

`r_a(ξ) = (1 + u) ^ a - χ(ξ) ∑_{k<K} (a choose k) u ^ (a - k)`

for the remainder after the first `K` nonzero terms. Where `‖ξ‖ ≥ 2π`, so that `u ≥ 1`, it equals
`u ^ a e(1 / u)` with the error `e(t) = (1 + t) ^ a - ∑_{k<K} (a choose k) t ^ k` of the binomial
series (`TauCeti.binomialError`), and `|e(t)| ≤ C t ^ K` on `[0, 1]`
(`TauCeti.exists_abs_binomialError_le`). Hence `|r_a(ξ)| ≤ C ⟨ξ⟩ ^ (2a - 2K)`.
For the derivatives, the absorption identities of the binomial coefficients give

`∂ⱼ r_a = 2 (2π)⁻² a ξⱼ r_{a - 1}` at frequencies of norm greater than `2`,

where the cutoff is constant. Each derivative of `r_a` is therefore a derivative of one order
less of `r_{a - 1}` times a linear function, and induction on the number of derivatives, for all
`a` at once, gives `‖D^k r_a(ξ)‖ ≤ C ⟨ξ⟩ ^ (2a - 2K - k)` at large frequencies; on the remaining
compact set of frequencies the derivatives are bounded by continuity. Thus `r_a` is a symbol of
order `s - 2K ≤ s - N` when `K = ⌈N / 2⌉`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.5
  (classical symbols).
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.17) (classical symbols).
-/

public section

noncomputable section

open Filter Set Real Topology
open scoped ContDiff

namespace TauCeti

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ### The remainders of the expansion -/

/-- The squared rescaled norm `‖ξ / 2π‖ ^ 2`. -/
private def besselSq (ξ : CoordinateSpace n) : ℝ :=
  ‖(2 * π)⁻¹ • ξ‖ ^ 2

private theorem besselSq_eq (ξ : CoordinateSpace n) : besselSq ξ = (2 * π)⁻¹ ^ 2 * ‖ξ‖ ^ 2 := by
  rw [besselSq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

private theorem besselSq_pos {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) : 0 < besselSq ξ := by
  rw [besselSq_eq]
  have := norm_pos_iff.2 hξ
  positivity

/-- The derivative `ξ ↦ 2 (2π)⁻² ⟪ξ, ·⟫` of `besselSq`. -/
private def besselSqDeriv : CoordinateSpace n →L[ℝ] (CoordinateSpace n →L[ℝ] ℝ) :=
  (2 * π)⁻¹ ^ 2 • (2 : ℕ) • innerSL ℝ

private theorem hasFDerivAt_besselSq (ξ : CoordinateSpace n) :
    HasFDerivAt besselSq (besselSqDeriv ξ) ξ := by
  rw [show (besselSq : CoordinateSpace n → ℝ) = fun ξ ↦ (2 * π)⁻¹ ^ 2 * ‖ξ‖ ^ 2 from
    funext besselSq_eq]
  simpa only [besselSqDeriv, smul_apply] using
    (hasStrictFDerivAt_norm_sq ξ).hasFDerivAt.const_mul ((2 * π)⁻¹ ^ 2)

private theorem contDiff_besselSq : ContDiff ℝ ∞ (besselSq : CoordinateSpace n → ℝ) := by
  rw [show (besselSq : CoordinateSpace n → ℝ) = fun ξ ↦ (2 * π)⁻¹ ^ 2 * ‖ξ‖ ^ 2 from
    funext besselSq_eq]
  exact contDiff_const.mul (contDiff_norm_sq ℝ)

/-- The first `K` nonzero terms `∑_{k<K} (a choose k) ‖ξ / 2π‖ ^ (2a - 2k)` of the expansion of
`⟨ξ / 2π⟩ ^ (2a)`. -/
private def besselSum (a : ℝ) (K : ℕ) (ξ : CoordinateSpace n) : ℝ :=
  ∑ k ∈ Finset.range K, Ring.choose a k * besselSq ξ ^ (a - k)

/-- The remainder `⟨ξ / 2π⟩ ^ (2a) - χ(ξ) ∑_{k<K} (a choose k) ‖ξ / 2π‖ ^ (2a - 2k)`. -/
private def besselRem (χ : FrequencyCutoff (CoordinateSpace n)) (a : ℝ) (K : ℕ)
    (ξ : CoordinateSpace n) : ℝ :=
  (1 + besselSq ξ) ^ a - χ ξ * besselSum a K ξ

private theorem contDiff_besselRem (χ : FrequencyCutoff (CoordinateSpace n)) (a : ℝ) (K : ℕ) :
    ContDiff ℝ ∞ (besselRem χ a K) := by
  refine ((contDiff_const.add contDiff_besselSq).rpow_const_of_ne fun ξ ↦
    (by unfold besselSq; positivity : (0 : ℝ) < 1 + besselSq ξ).ne').sub ?_
  refine contDiff_iff_contDiffAt.2 fun ξ ↦ ?_
  rcases eq_or_ne ξ 0 with rfl | hξ
  · -- Near `ξ = 0` the cutoff vanishes, which removes the singularity of the terms.
    refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [χ.eventuallyEq_zero_of_norm_lt_one (by simp)] with η hη
    simp [hη]
  · refine χ.contDiff.contDiffAt.mul (ContDiffAt.sum fun k _ ↦ contDiffAt_const.mul ?_)
    exact contDiff_besselSq.contDiffAt.rpow_const_of_ne (besselSq_pos hξ).ne'

/-- At frequencies of norm greater than `2`, `∂ⱼ r_a = 2 (2π)⁻² a ξⱼ r_{a - 1}`. -/
private theorem hasFDerivAt_besselRem (χ : FrequencyCutoff (CoordinateSpace n)) (a : ℝ) (K : ℕ)
    {ξ : CoordinateSpace n} (hξ : 2 < ‖ξ‖) :
    HasFDerivAt (besselRem χ a K) ((a * besselRem χ (a - 1) K ξ) • besselSqDeriv ξ) ξ := by
  have hu := besselSq_pos (norm_pos_iff.1 (by linarith) : ξ ≠ 0)
  have hχ : χ ξ = 1 := χ.apply_eq_one_of_two_le_norm hξ.le
  have heq : besselRem χ a K =ᶠ[𝓝 ξ] fun η ↦ (1 + besselSq η) ^ a - besselSum a K η := by
    filter_upwards [χ.eventuallyEq_one_of_two_lt_norm hξ] with η hη
    simp [besselRem, hη]
  refine HasFDerivAt.congr_of_eventuallyEq ?_ heq
  have h1 := ((hasFDerivAt_besselSq ξ).const_add 1).rpow_const (p := a)
    (Or.inl (by positivity : (0 : ℝ) < 1 + besselSq ξ).ne')
  have h2 : HasFDerivAt (besselSum a K)
      ((∑ k ∈ Finset.range K, Ring.choose a k * ((a - k) * besselSq ξ ^ (a - k - 1))) •
        besselSqDeriv ξ) ξ := by
    unfold besselSum
    rw [Finset.sum_smul]
    refine HasFDerivAt.fun_sum fun k _ ↦ ?_
    rw [mul_smul]
    exact ((hasFDerivAt_besselSq ξ).rpow_const (Or.inl hu.ne')).const_mul _
  refine (h1.sub h2).congr_fderiv ?_
  rw [← sub_smul]
  refine congrArg (· • besselSqDeriv ξ) ?_
  simp only [besselRem, hχ, one_mul, besselSum, mul_sub, Finset.mul_sum]
  refine congrArg (_ - ·) (Finset.sum_congr rfl fun k _ ↦ ?_)
  -- `(a choose k) (a - k) = a (a - 1 choose k)`.
  have hk : Ring.choose a k * (a - k) = a * Ring.choose (a - 1) k := by
    rw [← Ring.succ_nsmul_choose_succ_eq_choose_mul_sub, Ring.succ_nsmul_choose_succ]
  rw [← mul_assoc, ← mul_assoc, hk, show a - k - 1 = a - 1 - k by ring]

/-- Where the cutoff is one, the remainder is `u ^ a` times the binomial error at `1 / u`. -/
private theorem besselRem_eq_mul_binomialError (χ : FrequencyCutoff (CoordinateSpace n)) (a : ℝ)
    (K : ℕ) {ξ : CoordinateSpace n} (hξ : 2 ≤ ‖ξ‖) :
    besselRem χ a K ξ = besselSq ξ ^ a * binomialError a K (besselSq ξ)⁻¹ := by
  have hu := besselSq_pos (norm_pos_iff.1 (by linarith) : ξ ≠ 0)
  rw [besselRem, χ.apply_eq_one_of_two_le_norm hξ, one_mul, binomialError_def, mul_sub,
    ← Real.mul_rpow hu.le (by positivity), mul_add, mul_one, mul_inv_cancel₀ hu.ne', add_comm,
    besselSum, Finset.mul_sum]
  refine congrArg (_ - ·) (Finset.sum_congr rfl fun k _ ↦ ?_)
  rw [Real.rpow_sub hu, Real.rpow_natCast, inv_pow, div_eq_mul_inv]
  ring

/-- The remainder after `K` terms is `O(⟨ξ⟩ ^ (2a - 2K))` at frequencies of norm greater than
`2π`. -/
private theorem exists_norm_besselRem_le (χ : FrequencyCutoff (CoordinateSpace n)) (a : ℝ)
    (K : ℕ) :
    ∃ C, ∀ ξ : CoordinateSpace n, 2 * π < ‖ξ‖ →
      ‖besselRem χ a K ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (a - K) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_binomialError_le a K (l := 0) (u := 1) (by norm_num)
  set p : ℝ := a - K
  obtain ⟨C', hC'⟩ := exists_one_add_norm_smul_sq_rpow_le (E := CoordinateSpace n)
    (inv_ne_zero (by positivity : (2 * π : ℝ) ≠ 0)) p
  refine ⟨C * (2 ^ |p| * C'), fun ξ hξ ↦ ?_⟩
  have h2π : 2 ≤ 2 * π := by linarith [Real.two_le_pi]
  have hu := besselSq_pos (norm_pos_iff.1 (by linarith) : ξ ≠ 0)
  have hη1 : 1 ≤ ‖(2 * π)⁻¹ • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_eq_div,
      le_div_iff₀ (by positivity)]
    linarith
  have hu1 : 1 ≤ besselSq ξ := one_le_pow₀ hη1
  -- Since `u ≥ 1`, `u` is comparable with `1 + u = 1 + ‖(2π)⁻¹ • ξ‖ ^ 2`.
  have hpow : besselSq ξ ^ p ≤ 2 ^ |p| * (1 + besselSq ξ) ^ p := by
    have h := norm_rpow_le_one_add_norm_sq_rpow hη1 (2 * p)
    rwa [abs_mul, abs_two, mul_div_cancel_left₀ _ two_ne_zero,
      mul_div_cancel_left₀ _ two_ne_zero, Real.rpow_mul (norm_nonneg _), Real.rpow_two] at h
  have he := hC (besselSq ξ)⁻¹ ⟨by positivity, inv_le_one_of_one_le₀ hu1⟩
  rw [abs_of_pos (inv_pos.2 hu)] at he
  rw [Real.norm_eq_abs, besselRem_eq_mul_binomialError χ a K (by linarith), abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hu a)]
  calc besselSq ξ ^ a * |binomialError a K (besselSq ξ)⁻¹|
      ≤ besselSq ξ ^ a * (C * (besselSq ξ)⁻¹ ^ K) := by gcongr
    _ = C * besselSq ξ ^ p := by
        rw [Real.rpow_sub hu, Real.rpow_natCast, inv_pow, div_eq_mul_inv]
        ring
    _ ≤ C * (2 ^ |p| * (C' * (1 + ‖ξ‖ ^ 2) ^ p)) := by
        gcongr
        exact hpow.trans (mul_le_mul_of_nonneg_left (hC' ξ) (by positivity))
    _ = _ := by ring

/-- The derivative bounds `‖D^k r_a(ξ)‖ ≤ C ⟨ξ⟩ ^ (2a - 2K - k)` of the remainder after `K`
terms. -/
private theorem exists_norm_iteratedFDeriv_besselRem_le (χ : FrequencyCutoff (CoordinateSpace n))
    (K k : ℕ) (a : ℝ) :
    ∃ C, ∀ ξ : CoordinateSpace n, ‖iteratedFDeriv ℝ k (besselRem χ a K) ξ‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ (a - K - k / 2) := by
  induction k using Nat.strong_induction_on generalizing a with
  | _ k ih =>
  have hcont := (contDiff_besselRem χ a K).continuous_iteratedFDeriv (m := k) (mod_cast le_top)
  rcases k with _ | k
  · obtain ⟨C, hC⟩ := exists_norm_besselRem_le χ a K
    refine hcont.exists_norm_le_one_add_norm_sq_rpow_of_lt_norm (R := 2 * π) (C := C)
      fun ξ hξ ↦ ?_
    simpa using hC ξ hξ
  · -- At large frequencies `D r_a = r_{a - 1} • (a • L)` with `L` linear, so the Leibniz rule and
    -- the bounds for the derivatives of `r_{a - 1}` give those for `r_a`.
    obtain ⟨C, hC⟩ :=
      (a • besselSqDeriv (n := n)).exists_norm_iteratedFDeriv_smul_le_one_add_norm_sq_rpow
        ((contDiff_besselRem χ (a - 1) K).of_le (mod_cast le_top)) (ρ := a - 1 - K)
        fun i hi ↦ ih i (Nat.lt_succ_of_le hi) (a - 1)
    refine hcont.exists_norm_le_one_add_norm_sq_rpow_of_lt_norm (R := 2) (C := C) fun ξ hξ ↦ ?_
    have hderiv : fderiv ℝ (besselRem χ a K) =ᶠ[𝓝 ξ]
        fun η ↦ besselRem χ (a - 1) K η • (a • besselSqDeriv) η := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
        (show ξ ∈ {η : CoordinateSpace n | 2 < ‖η‖} from hξ)] with η hη
      rw [(hasFDerivAt_besselRem χ a K hη).fderiv, smul_apply, smul_smul, mul_comm]
    rw [← norm_iteratedFDeriv_fderiv, (hderiv.iteratedFDeriv ℝ k).eq_of_nhds]
    convert hC ξ using 3
    push_cast
    ring

/-- The remainder after `K` terms, as a symbol of order `s - 2K`. -/
private def besselRemSymbol (χ : FrequencyCutoff (CoordinateSpace n)) (s : ℝ) (K : ℕ) :
    Symbol n V V (s - 2 * K) :=
  Symbol.ofFrequency (fun ξ ↦ (besselRem χ (s / 2) K ξ : ℂ) • ContinuousLinearMap.id ℂ V)
    ((Complex.ofRealCLM.contDiff.comp (contDiff_besselRem χ (s / 2) K)).smul contDiff_const)
    fun k ↦ by
      have h := ContinuousLinearMap.exists_norm_iteratedFDeriv_comp_left_le_one_add_norm_sq_rpow
        (Complex.ofRealCLM.smulRight (ContinuousLinearMap.id ℂ V))
        ((contDiff_besselRem χ (s / 2) K).of_le (mod_cast le_top))
        (exists_norm_iteratedFDeriv_besselRem_le χ K k (s / 2))
      simp only [ContinuousLinearMap.smulRight_apply, Complex.ofRealCLM_apply] at h
      obtain ⟨C, hC⟩ := h
      refine ⟨C, fun ξ ↦ (hC ξ).trans_eq ?_⟩
      congr 2
      ring

private theorem coefficient_besselRemSymbol (χ : FrequencyCutoff (CoordinateSpace n)) (s : ℝ)
    (K : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (besselRemSymbol (V := V) χ s K).coefficient p =
      (besselRem χ (s / 2) K p.2 : ℂ) • ContinuousLinearMap.id ℂ V :=
  Symbol.coefficient_ofFrequency _ _ p

/-! ### The homogeneous terms -/

/-- The homogeneous term of degree `s - j`: `(s / 2 choose j / 2) ‖ξ / 2π‖ ^ (s - j)` for even `j`,
and zero for odd `j`. -/
private def besselTerm (s : ℝ) (j : ℕ) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V V (s - j) :=
  ((((if Even j then Ring.choose (s / 2) (j / 2) else 0) * (2 * π)⁻¹ ^ (s - j) : ℝ) : ℂ)) •
    HomogeneousSymbol.normRpow (CoordinateSpace n) (CoordinateSpace n) V (s - j)

private theorem coefficient_besselTerm (s : ℝ) (j : ℕ) {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    (besselTerm (V := V) s j).coefficient (x, ξ) =
      (((if Even j then Ring.choose (s / 2) (j / 2) else 0) * ‖(2 * π)⁻¹ • ξ‖ ^ (s - j) : ℝ) :
        ℂ) • ContinuousLinearMap.id ℂ V := by
  rw [besselTerm, HomogeneousSymbol.coefficient_smul, Pi.smul_apply,
    HomogeneousSymbol.coefficient_normRpow_of_ne_zero _ _ _ hξ, ← Complex.coe_smul, smul_smul,
    ← Complex.ofReal_mul, norm_smul, Real.norm_of_nonneg (by positivity),
    Real.mul_rpow (by positivity) (norm_nonneg _), mul_assoc]

/-- The first `N` cut-off homogeneous terms sum to the first `⌈N / 2⌉` nonzero terms. -/
private theorem sum_coefficient_besselTerm (χ : FrequencyCutoff (CoordinateSpace n)) (s : ℝ)
    (N : ℕ) (x ξ : CoordinateSpace n) :
    ∑ j ∈ Finset.range N, χ ξ • (besselTerm (V := V) s j).coefficient (x, ξ) =
      ((χ ξ * besselSum (s / 2) ((N + 1) / 2) ξ : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [χ.apply_zero]
  have hreal : ∑ j ∈ Finset.range N, χ ξ * ((if Even j then Ring.choose (s / 2) (j / 2) else 0) *
      ‖(2 * π)⁻¹ • ξ‖ ^ (s - j)) = χ ξ * besselSum (s / 2) ((N + 1) / 2) ξ := by
    simp only [ite_mul, zero_mul]
    rw [← Finset.mul_sum, Finset.sum_range_ite_even, besselSum]
    refine congrArg _ (Finset.sum_congr rfl fun k _ ↦ ?_)
    -- `‖ξ / 2π‖ ^ (s - 2k) = (‖ξ / 2π‖ ^ 2) ^ (s / 2 - k)`.
    rw [Nat.mul_div_cancel_left _ two_pos, besselSq, ← Real.rpow_natCast,
      ← Real.rpow_mul (norm_nonneg _)]
    push_cast
    ring_nf
  calc ∑ j ∈ Finset.range N, χ ξ • (besselTerm (V := V) s j).coefficient (x, ξ)
      = ∑ j ∈ Finset.range N, ((χ ξ * ((if Even j then Ring.choose (s / 2) (j / 2) else 0) *
          ‖(2 * π)⁻¹ • ξ‖ ^ (s - j)) : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [coefficient_besselTerm s j hξ, ← Complex.coe_smul, smul_smul, ← Complex.ofReal_mul]
    _ = _ := by rw [← Finset.sum_smul, ← Complex.ofReal_sum, hreal]

/-! ### The classical Bessel potential -/

namespace ClassicalSymbol

/-- The Bessel weight `⟨ξ / 2π⟩ ^ s` (`TauCeti.Symbol.besselPotential`) as a classical symbol of
order `s`: its homogeneous term of degree `s - j` is `(s / 2 choose j / 2) ‖ξ / 2π‖ ^ (s - j)` for
even `j` and zero for odd `j` (`TauCeti.ClassicalSymbol.coefficient_term_besselPotential`). -/
def besselPotential (s : ℝ) : ClassicalSymbol n V V s where
  toSymbol := Symbol.besselPotential s
  term := besselTerm s
  exists_remainder' := ⟨default, fun N ↦
    ⟨Symbol.inclusion (sub_le_sub_left (by exact_mod_cast (by omega : N ≤ 2 * ((N + 1) / 2))) s)
      (besselRemSymbol default s ((N + 1) / 2)),
      fun p ↦ by
        rw [Symbol.coefficient_inclusion, coefficient_besselRemSymbol, sum_coefficient_besselTerm,
          Symbol.coefficient_besselPotential, ← sub_smul, besselRem, Complex.ofReal_sub, besselSq]⟩⟩

@[simp]
theorem toSymbol_besselPotential (s : ℝ) :
    (besselPotential s : ClassicalSymbol n V V s).toSymbol = Symbol.besselPotential s :=
  (rfl)

/-- **The terms of the Bessel potential.** At a nonzero frequency, the homogeneous term of degree
`s - j` of `⟨ξ / 2π⟩ ^ s` is `(s / 2 choose j / 2) ‖ξ / 2π‖ ^ (s - j)` for even `j` and zero for
odd `j`. -/
theorem coefficient_term_besselPotential (s : ℝ) (j : ℕ) {x ξ : CoordinateSpace n}
    (hξ : ξ ≠ 0) :
    ((besselPotential s : ClassicalSymbol n V V s).term j).coefficient (x, ξ) =
      (((if Even j then Ring.choose (s / 2) (j / 2) else 0) * ‖(2 * π)⁻¹ • ξ‖ ^ (s - j) : ℝ) :
        ℂ) • ContinuousLinearMap.id ℂ V :=
  coefficient_besselTerm s j hξ

/-- The homogeneous terms of odd index of the Bessel potential vanish: its expansion proceeds in
steps of two. -/
theorem term_besselPotential_of_odd (s : ℝ) {j : ℕ} (hj : Odd j) :
    (besselPotential s : ClassicalSymbol n V V s).term j = 0 :=
  HomogeneousSymbol.ext_of_ne_zero fun x ξ hξ ↦ by
    simp [coefficient_term_besselPotential s j hξ, Nat.not_even_iff_odd.2 hj]

/-- **The principal symbol of the Bessel potential** is `‖ξ / 2π‖ ^ s`. -/
theorem coefficient_principal_besselPotential (s : ℝ) {x ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    (besselPotential s : ClassicalSymbol n V V s).principal.coefficient (x, ξ) =
      ((‖(2 * π)⁻¹ • ξ‖ ^ s : ℝ) : ℂ) • ContinuousLinearMap.id ℂ V := by
  rw [coefficient_principal, coefficient_term_besselPotential s 0 hξ]
  simp

/-- The Bessel potential is elliptic: its principal symbol `‖ξ / 2π‖ ^ s` is a nonzero multiple of
the identity at every nonzero frequency. -/
theorem isElliptic_besselPotential (s : ℝ) :
    (besselPotential s : ClassicalSymbol n V V s).IsElliptic :=
  isElliptic_iff.2 fun x ξ hξ ↦ by
    rw [coefficient_principal_besselPotential s hξ]
    have hr : ((‖(2 * π)⁻¹ • ξ‖ ^ s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2
      (Real.rpow_pos_of_pos (norm_pos_iff.2 (smul_ne_zero (by positivity) hξ)) s).ne'
    exact (ContinuousLinearMap.isInvertible_smul_iff hr).2
      (by simpa using ContinuousLinearMap.isInvertible_equiv (f := .refl ℂ V))

end ClassicalSymbol

end TauCeti

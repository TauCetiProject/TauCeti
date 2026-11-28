/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.Fock.PolynomialVector
public import Mathlib.Analysis.CStarAlgebra.Matrix
import TauCeti.Analysis.SpecialFunctions.Gaussian.Homogeneous
import TauCeti.Data.Nat.Factorial.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Decay of the Fock matrix coefficients of homogeneous polynomial vectors

Let `ε : ι → ℤˣ` be signs, `v = v_P` the polynomial vector of a polynomial `P` homogeneous of
degree `d` in the Fock model `𝓕(ε)` of `U(ε)`, `σ ∈ U(ε)` and `y ∈ ℂ^ι`. This file shows that the
matrix coefficient `⟨v, ϱ(y) ω(σ) v⟩` of the Heisenberg action `ϱ` and the Weil representation `ω`
decays faster than every power of the Euclidean norm `|y|`: for natural numbers `A ≥ d + |ι|` and
`n`,

`|y|^{2n} |⟨v, ϱ(y) ω(σ) v⟩| ≤ (4 (A + n))^n ‖σ‖^{|ι| + 2n} ⟨v, v⟩`,

with `‖σ‖` the operator norm
(`TauCeti.Fock.norm_toLp_pow_mul_norm_innerSL_heisenbergRep_weilRep_le`).

The coefficient is an integral of `v(σ⁻¹ z)` against `conj (v (y + z))`, with the multiplier
`|Δ_∞(σ)| ≤ ‖σ‖^{|ι|}` in front (`TauCeti.ReproducingModel.innerSL_heisenbergRep_weilOp`). Since
`|y| ≤ ‖σ‖ (|y + z| + |σ⁻¹ z|)`, the weight `|y|^{2n}` is shared between the two factors, and
Cauchy–Schwarz reduces the bound to the Gaussian moments of `v`. These are computed exactly by
integration by parts against the Gaussian: `|v(x)|² = |P(ζ(x))|² exp (-|x|²)` with
`|P(ζ(x))|²` homogeneous of degree `2d` under real scalings, so
`∫ |x|^{2m} |v(x)|² dμ = ∏_{j < m} (d + |ι| + j) * ∫ |v(x)|² dμ`
(`TauCeti.Fock.lintegral_enorm_pow_mul_enorm_polyVector_sq`), and the rising factorial of even
length `2n` is at most `(d + |ι| + n)^{2n}` (`Nat.ascFactorial_two_mul_le_pow_add`).

This decay is what makes a theta series over a lattice without short vectors close to the term of
its zero vector.

## Main results

* `TauCeti.Fock.lintegral_enorm_pow_mul_enorm_polyVector_sq`: the Gaussian moments of a
  homogeneous polynomial vector.
* `TauCeti.Fock.norm_toLp_pow_mul_norm_innerSL_heisenbergRep_weilRep_le`: the decay of the matrix
  coefficients.

## Provenance

The statement and the method, integration by parts against the Gaussian, follow grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC),
`New.Fock.norm_fockInner_realHeisenbergOp_le` in
`src/New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean`. The proof here is written
independently: the Gaussian moments come from the scaling law of
`MeasureTheory.Measure.lintegral_ofReal_pow_mul_mul_ofReal_exp_neg_of_homogeneous`.

## References

* V. Bargmann, *On a Hilbert space of analytic functions and an associated integral transform,
  part I*, Comm. Pure Appl. Math. 14 (1961), 187–214.
* G. B. Folland, *Harmonic analysis in phase space*, Ann. of Math. Stud. 122 (1989), Chapter 1.
-/

public section

open MeasureTheory Matrix Finset
open scoped ENNReal

namespace TauCeti.Fock

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {ε : ι → ℤˣ}

/-! ### Gaussian moments of homogeneous polynomial vectors -/

/-- The moments in the degenerate case of no coordinates, where both sides vanish unless `m = 0`. -/
private theorem lintegral_enorm_pow_mul_enorm_polyVector_sq_of_isEmpty [IsEmpty ι]
    {P : MvPolynomial ι ℂ} {d : ℕ} (hP : P.IsHomogeneous d) (m : ℕ) :
    ∫⁻ x, ‖WithLp.toLp 2 x‖ₑ ^ (2 * m) * ‖polyVector ε P x‖ₑ ^ 2 ∂measure ι =
      (∏ j ∈ range m, ((d + Fintype.card ι + j : ℕ) : ℝ≥0∞)) *
        ∫⁻ x, ‖polyVector ε P x‖ₑ ^ 2 ∂measure ι := by
  cases m with
  | zero => simp
  | succ m =>
    have h_zero (x : ι → ℂ) : x = 0 := Subsingleton.elim x 0
    have h_left : ∫⁻ x, ‖WithLp.toLp 2 x‖ₑ ^ (2 * (m + 1)) * ‖polyVector ε P x‖ₑ ^ 2 ∂measure ι =
        0 := by
      simp [h_zero]
    rw [h_left]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [prod_range_succ']
    · -- A homogeneous polynomial of positive degree vanishes at `0`.
      have h_vec (x : ι → ℂ) : polyVector ε P x = 0 := by
        rw [polyVector_apply, h_zero (holomorphicCoord ε x), ← zero_smul ℂ (0 : ι → ℂ),
          hP.eval_smul, zero_pow hd.ne', zero_mul, zero_mul]
      simp [h_vec]

/-- **Gaussian moments of homogeneous polynomial vectors.** If `P` is homogeneous of degree `d`,
then `∫ |x|^{2m} |v_P(x)|² dμ = ∏_{j < m} (d + |ι| + j) * ∫ |v_P(x)|² dμ` for every `m`, with
`|x|` the Euclidean norm and `μ = π^{-|ι|} dx` the measure of the Fock space. -/
theorem lintegral_enorm_pow_mul_enorm_polyVector_sq {P : MvPolynomial ι ℂ} {d : ℕ}
    (hP : P.IsHomogeneous d) (m : ℕ) :
    ∫⁻ x, ‖WithLp.toLp 2 x‖ₑ ^ (2 * m) * ‖polyVector ε P x‖ₑ ^ 2 ∂measure ι =
      (∏ j ∈ range m, ((d + Fintype.card ι + j : ℕ) : ℝ≥0∞)) *
        ∫⁻ x, ‖polyVector ε P x‖ₑ ^ 2 ∂measure ι := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact lintegral_enorm_pow_mul_enorm_polyVector_sq_of_isEmpty hP m
  -- `|v_P(x)|² = g x * exp (-Q x)` with `Q x = |x|²` and `g x = |P(ζ(x))|²` of degree `2 d`.
  set Q : (ι → ℂ) → ℝ := fun x ↦ ‖WithLp.toLp 2 x‖ ^ 2
  set g : (ι → ℂ) → ℝ≥0∞ := fun x ↦ ‖MvPolynomial.eval (holomorphicCoord ε x) P‖ₑ ^ 2
  have h_weight (x : ι → ℂ) : ‖WithLp.toLp 2 x‖ₑ ^ (2 * m) = ENNReal.ofReal (Q x) ^ m := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ← pow_mul]
  have h_vec (x : ι → ℂ) :
      ‖polyVector ε P x‖ₑ ^ 2 = g x * ENNReal.ofReal (Real.exp (-Q x)) := by
    rw [polyVector_apply, eNorm_mul, mul_pow, ← ofReal_norm (gaussian ι x), norm_gaussian,
      ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_natCast_mul]
    simp only [Q, EuclideanSpace.norm_sq_eq, g]
    congr 3
    push_cast
    ring
  have hQ (c : ℝ) (hc : 0 < c) (x : ι → ℂ) : Q (c • x) = c ^ 2 * Q x := by
    simp only [Q, WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hc.le, mul_pow]
  have hQ_pos (x : ι → ℂ) (hx : x ≠ 0) : 0 < Q x :=
    pow_pos (norm_pos_iff.2 (by simpa using hx)) 2
  have hg (c : ℝ) (hc : 0 < c) (x : ι → ℂ) :
      g (c • x) = ENNReal.ofReal (c ^ ((2 * d : ℕ) : ℝ)) * g x := by
    have hc' : ‖(c : ℂ)‖ₑ = ENNReal.ofReal c := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hc.le]
    simp only [g, holomorphicCoord_real_smul, hP.eval_smul, Real.rpow_natCast]
    rw [eNorm_mul, eNorm_pow, mul_pow, hc', ← pow_mul, ENNReal.ofReal_pow hc.le, mul_comm 2 d]
  have h_finrank : (Module.finrank ℝ (ι → ℂ) : ℝ) = 2 * Fintype.card ι := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  have hk : 0 < (Module.finrank ℝ (ι → ℂ) : ℝ) + ((2 * d : ℕ) : ℝ) := by
    rw [h_finrank]
    have := Fintype.card_pos (α := ι)
    positivity
  have h_cont : Continuous g := by
    have := MvPolynomial.continuous_eval P
    fun_prop
  have h := (measure ι).lintegral_ofReal_pow_mul_mul_ofReal_exp_neg_of_homogeneous
    (by fun_prop) hQ hQ_pos h_cont.aemeasurable hg hk m
  simp_rw [h_weight, h_vec, ← mul_assoc]
  rw [h]
  congr 1
  refine prod_congr rfl fun j _ ↦ ?_
  rw [h_finrank, ← ENNReal.ofReal_natCast]
  congr 1
  push_cast
  ring

/-! ### Decay of the matrix coefficients -/

/-- Cauchy–Schwarz for the product of two values of `v` along measure-preserving maps `p`, `q`,
weighted at the first: if `∫ |x|^{4n} |v|² ≤ C² ∫ |v|²`, then
`∫ |p z|^{2n} |v (p z)| |v (q z)| dz ≤ C ∫ |v|²`. -/
private theorem lintegral_enorm_pow_mul_enorm_mul_enorm_le {v : FockSpace ε} {n : ℕ} {C : ℝ≥0∞}
    (hC : ∫⁻ x, ‖WithLp.toLp 2 x‖ₑ ^ (2 * (2 * n)) * ‖v x‖ₑ ^ 2 ∂measure ι ≤
      C ^ 2 * ∫⁻ x, ‖v x‖ₑ ^ 2 ∂measure ι)
    {p q : (ι → ℂ) → ι → ℂ} (hp : MeasurePreserving p (measure ι) (measure ι))
    (hq : MeasurePreserving q (measure ι) (measure ι)) :
    ∫⁻ z, ‖WithLp.toLp 2 (p z)‖ₑ ^ (2 * n) * ‖v (p z)‖ₑ * ‖v (q z)‖ₑ ∂measure ι ≤
      C * ∫⁻ x, ‖v x‖ₑ ^ 2 ∂measure ι := by
  set V := ∫⁻ x, ‖v x‖ₑ ^ 2 ∂measure ι
  have hv := v.continuous.measurable
  have h_holder := ENNReal.lintegral_mul_le_Lp_mul_Lq (measure ι) Real.HolderConjugate.two_two
    (f := fun z ↦ ‖WithLp.toLp 2 (p z)‖ₑ ^ (2 * n) * ‖v (p z)‖ₑ) (g := fun z ↦ ‖v (q z)‖ₑ)
    (by have := hp.measurable; fun_prop) (by have := hq.measurable; fun_prop)
  have h_p : ∫⁻ z, (‖WithLp.toLp 2 (p z)‖ₑ ^ (2 * n) * ‖v (p z)‖ₑ) ^ (2 : ℝ) ∂measure ι =
      ∫⁻ x, ‖WithLp.toLp 2 x‖ₑ ^ (2 * (2 * n)) * ‖v x‖ₑ ^ 2 ∂measure ι := by
    simp_rw [ENNReal.rpow_two, mul_pow, ← pow_mul, mul_comm (2 * n) 2]
    exact hp.lintegral_comp (f := fun x ↦ ‖WithLp.toLp 2 x‖ₑ ^ (2 * (2 * n)) * ‖v x‖ₑ ^ 2)
      (by fun_prop)
  have h_q : ∫⁻ z, ‖v (q z)‖ₑ ^ (2 : ℝ) ∂measure ι = V := by
    simp_rw [ENNReal.rpow_two]
    exact hq.lintegral_comp (f := fun x ↦ ‖v x‖ₑ ^ 2) (by fun_prop)
  simp only [Pi.mul_apply, h_p, h_q] at h_holder
  refine h_holder.trans ?_
  calc (∫⁻ x, ‖WithLp.toLp 2 x‖ₑ ^ (2 * (2 * n)) * ‖v x‖ₑ ^ 2 ∂measure ι) ^ (1 / 2 : ℝ) *
        V ^ (1 / 2 : ℝ)
      ≤ (C ^ 2 * V) ^ (1 / 2 : ℝ) * V ^ (1 / 2 : ℝ) := by gcongr
    _ = C * V := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_mul, mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num)
        (by norm_num)]
      norm_num

open scoped Matrix.Norms.L2Operator in
/-- The weight `|y|^{2n}` is shared between `y + z` and `σ⁻¹ z`:
`2 |y|^{2n} ≤ 4^n ‖σ‖^{2n} (|y + z|^{2n} + |σ⁻¹ z|^{2n})` for `σ ∈ U(ε)`. -/
private theorem two_mul_norm_toLp_pow_le (σ : unitaryGroup ε) (y z : ι → ℂ) (n : ℕ) :
    2 * ‖WithLp.toLp 2 y‖ ^ (2 * n) ≤ 4 ^ n * ‖((σ : GL ι ℂ) : Matrix ι ι ℂ)‖ ^ (2 * n) *
      (‖WithLp.toLp 2 (y + z)‖ ^ (2 * n) + ‖WithLp.toLp 2 (σ⁻¹ • z)‖ ^ (2 * n)) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · norm_num
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hy : WithLp.toLp 2 y = 0 := Subsingleton.elim _ _
    rw [hy, norm_zero, zero_pow (by positivity), mul_zero]
    positivity
  set s := ‖((σ : GL ι ℂ) : Matrix ι ι ℂ)‖
  set a := ‖WithLp.toLp 2 (y + z)‖
  set b := ‖WithLp.toLp 2 (σ⁻¹ • z)‖
  have hs : 1 ≤ s := one_le_norm_val_of_mem_unitaryGroupOf signMatrix_mem_unitary σ.property
  -- `|z| = |σ (σ⁻¹ z)| ≤ ‖σ‖ |σ⁻¹ z|`, so `|y| ≤ |y + z| + |z| ≤ ‖σ‖ (|y + z| + |σ⁻¹ z|)`.
  have hz : ‖WithLp.toLp 2 z‖ ≤ s * b := by
    have h := l2_opNorm_mulVec ((σ : GL ι ℂ) : Matrix ι ι ℂ) (WithLp.toLp 2 (σ⁻¹ • z))
    rwa [← smul_def, smul_inv_smul] at h
  have hy : ‖WithLp.toLp 2 y‖ ≤ s * (a + b) := by
    calc ‖WithLp.toLp 2 y‖ = ‖WithLp.toLp 2 (y + z) - WithLp.toLp 2 z‖ := by
          rw [← WithLp.toLp_sub, add_sub_cancel_right]
      _ ≤ a + s * b := (norm_sub_le _ _).trans (by gcongr)
      _ ≤ s * (a + b) := by nlinarith [norm_nonneg (WithLp.toLp 2 (y + z))]
  have h_pow := add_pow_le (norm_nonneg (WithLp.toLp 2 (y + z)))
    (norm_nonneg (WithLp.toLp 2 (σ⁻¹ • z))) (2 * n)
  calc 2 * ‖WithLp.toLp 2 y‖ ^ (2 * n) ≤ 2 * (s * (a + b)) ^ (2 * n) := by gcongr
    _ = s ^ (2 * n) * (2 * (a + b) ^ (2 * n)) := by rw [mul_pow]; ring
    _ ≤ s ^ (2 * n) * (2 * (2 ^ (2 * n - 1) * (a ^ (2 * n) + b ^ (2 * n)))) := by gcongr
    _ = 4 ^ n * s ^ (2 * n) * (a ^ (2 * n) + b ^ (2 * n)) := by
      have h4 : (2 : ℝ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
      rw [← mul_assoc 2, ← pow_succ', Nat.sub_add_cancel (by omega), h4]
      ring

/-- The matrix coefficient `⟨u, ϱ(y) ω(σ) w⟩` is bounded by `|Δ_∞(σ)|` times the integral of
`|w(σ⁻¹ z)| |u(y + z)|`. -/
private theorem enorm_innerSL_heisenbergRep_weilRep_le (u w : FockSpace ε) (σ : unitaryGroup ε)
    (y : ι → ℂ) :
    ‖ReproducingModel.innerSL u (ReproducingModel.heisenbergRep y (weilRep ε σ w))‖ₑ ≤
      ‖multiplier ε σ‖ₑ * ∫⁻ z, ‖w (σ⁻¹ • z)‖ₑ * ‖u (y + z)‖ₑ ∂measure ι := by
  rw [ReproducingModel.weilRep_apply_eq, ReproducingModel.innerSL_heisenbergRep_weilOp, eNorm_mul]
  gcongr
  refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono fun z ↦ ?_)
  simp [eNorm_mul]

open scoped Matrix.Norms.L2Operator in
/-- The weighted integral `|y|^{2n} ∫ |v(σ⁻¹ z)| |v(y + z)| dz` is at most
`4^n ‖σ‖^{2n} C ∫ |v|²` when `∫ |x|^{4n} |v|² ≤ C² ∫ |v|²`: the weight is shared between the two
factors (`two_mul_norm_toLp_pow_le`) and each half is bounded by Cauchy–Schwarz. -/
private theorem enorm_toLp_pow_mul_lintegral_le {v : FockSpace ε} {n : ℕ} {C : ℝ≥0∞}
    (hC : ∫⁻ x, ‖WithLp.toLp 2 x‖ₑ ^ (2 * (2 * n)) * ‖v x‖ₑ ^ 2 ∂measure ι ≤
      C ^ 2 * ∫⁻ x, ‖v x‖ₑ ^ 2 ∂measure ι) (σ : unitaryGroup ε) (y : ι → ℂ) :
    ‖WithLp.toLp 2 y‖ₑ ^ (2 * n) * ∫⁻ z, ‖v (σ⁻¹ • z)‖ₑ * ‖v (y + z)‖ₑ ∂measure ι ≤
      ENNReal.ofReal (4 ^ n * ‖((σ : GL ι ℂ) : Matrix ι ι ℂ)‖ ^ (2 * n)) *
        (C * ∫⁻ x, ‖v x‖ₑ ^ 2 ∂measure ι) := by
  set V := ∫⁻ x, ‖v x‖ₑ ^ 2 ∂measure ι
  set K := ENNReal.ofReal (4 ^ n * ‖((σ : GL ι ℂ) : Matrix ι ι ℂ)‖ ^ (2 * n))
  have hv := v.continuous.measurable
  have h_weight (z : ι → ℂ) : 2 * ‖WithLp.toLp 2 y‖ₑ ^ (2 * n) ≤
      K * (‖WithLp.toLp 2 (y + z)‖ₑ ^ (2 * n) + ‖WithLp.toLp 2 (σ⁻¹ • z)‖ₑ ^ (2 * n)) := by
    have h := ENNReal.ofReal_le_ofReal (two_mul_norm_toLp_pow_le σ y z n)
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)] at h
    simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_pow, norm_nonneg, ofReal_norm] using h
  have h_T1 := lintegral_enorm_pow_mul_enorm_mul_enorm_le hC
    (measurePreserving_add_left (measure ι) y) (measurePreserving_smul σ⁻¹)
  have h_T2 := lintegral_enorm_pow_mul_enorm_mul_enorm_le hC
    (measurePreserving_smul σ⁻¹) (measurePreserving_add_left (measure ι) y)
  refine (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).1 ?_
  calc 2 * (‖WithLp.toLp 2 y‖ₑ ^ (2 * n) * ∫⁻ z, ‖v (σ⁻¹ • z)‖ₑ * ‖v (y + z)‖ₑ ∂measure ι)
      = ∫⁻ z, 2 * ‖WithLp.toLp 2 y‖ₑ ^ (2 * n) * (‖v (σ⁻¹ • z)‖ₑ * ‖v (y + z)‖ₑ) ∂measure ι := by
        rw [lintegral_const_mul' _ _ (by finiteness), mul_assoc]
    _ ≤ ∫⁻ z, K * (‖WithLp.toLp 2 (y + z)‖ₑ ^ (2 * n) * ‖v (y + z)‖ₑ * ‖v (σ⁻¹ • z)‖ₑ +
          ‖WithLp.toLp 2 (σ⁻¹ • z)‖ₑ ^ (2 * n) * ‖v (σ⁻¹ • z)‖ₑ * ‖v (y + z)‖ₑ) ∂measure ι := by
        refine lintegral_mono fun z ↦ (mul_le_mul_left (h_weight z) _).trans_eq ?_
        ring
    _ = K * (∫⁻ z, ‖WithLp.toLp 2 (y + z)‖ₑ ^ (2 * n) * ‖v (y + z)‖ₑ * ‖v (σ⁻¹ • z)‖ₑ
            ∂measure ι +
          ∫⁻ z, ‖WithLp.toLp 2 (σ⁻¹ • z)‖ₑ ^ (2 * n) * ‖v (σ⁻¹ • z)‖ₑ * ‖v (y + z)‖ₑ
            ∂measure ι) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (by fun_prop)]
    _ ≤ K * (C * V + C * V) := by gcongr
    _ = 2 * (K * (C * V)) := by ring

/-- The Gaussian moment of order `4n` of a homogeneous polynomial vector of degree `d` is at most
`(A + n)^{4n}` times its squared norm, for `A ≥ d + |ι|`. -/
private theorem lintegral_enorm_pow_mul_enorm_polyVector_sq_le {P : MvPolynomial ι ℂ} {d : ℕ}
    (hP : P.IsHomogeneous d) {A : ℕ} (hA : d + Fintype.card ι ≤ A) (n : ℕ) :
    ∫⁻ x, ‖WithLp.toLp 2 x‖ₑ ^ (2 * (2 * n)) * ‖polyVector ε P x‖ₑ ^ 2 ∂measure ι ≤
      (((A + n) ^ n : ℕ) : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖polyVector ε P x‖ₑ ^ 2 ∂measure ι := by
  rw [lintegral_enorm_pow_mul_enorm_polyVector_sq hP, ← Nat.cast_prod,
    ← Nat.ascFactorial_eq_prod_range]
  gcongr
  rw [← Nat.cast_pow, Nat.cast_le, ← pow_mul, mul_comm n 2]
  exact (Nat.ascFactorial_two_mul_le_pow_add _ n).trans (by gcongr)

open scoped Matrix.Norms.L2Operator in
/-- **Decay of Fock matrix coefficients.** Let `P` be homogeneous of degree `d` with polynomial
vector `v = v_P`, `σ ∈ U(ε)` and `y : ι → ℂ`. For natural numbers `A ≥ d + |ι|` and `n`,
`|y|^{2n} |⟨v, ϱ(y) ω(σ) v⟩| ≤ (4 (A + n))^n ‖σ‖^{|ι| + 2n} ⟨v, v⟩`, with `|y|` the Euclidean
norm, `‖σ‖` the operator norm, `ϱ` the Heisenberg action and `ω` the Weil representation; for
`y ≠ 0` this bounds the coefficient by `(4 (A + n))^n |y|^{-2n} ‖σ‖^{|ι| + 2n} ⟨v, v⟩`. -/
theorem norm_toLp_pow_mul_norm_innerSL_heisenbergRep_weilRep_le {P : MvPolynomial ι ℂ} {d : ℕ}
    (hP : P.IsHomogeneous d) (σ : unitaryGroup ε) (y : ι → ℂ) {A : ℕ}
    (hA : d + Fintype.card ι ≤ A) (n : ℕ) :
    ‖WithLp.toLp 2 y‖ ^ (2 * n) * ‖ReproducingModel.innerSL (polyVector ε P)
        (ReproducingModel.heisenbergRep y (weilRep ε σ (polyVector ε P)))‖ ≤
      (4 * (A + n)) ^ n * ‖((σ : GL ι ℂ) : Matrix ι ι ℂ)‖ ^ (Fintype.card ι + 2 * n) *
        (ReproducingModel.innerSL (polyVector ε P) (polyVector ε P)).re := by
  set v := polyVector ε P
  set s := ‖((σ : GL ι ℂ) : Matrix ι ι ℂ)‖
  have h_V : ∫⁻ x, ‖v x‖ₑ ^ 2 ∂measure ι = ENNReal.ofReal (ReproducingModel.innerSL v v).re := by
    rw [ReproducingModel.innerSL_self, Complex.ofReal_re, ofReal_integral_eq_lintegral_ofReal
      (ReproducingModel.integrable_norm_sq v) (ae_of_all _ fun _ ↦ by positivity)]
    simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have h_re : 0 ≤ (ReproducingModel.innerSL v v).re := by
    rw [ReproducingModel.innerSL_self, Complex.ofReal_re]
    positivity
  have h_mult : ‖multiplier ε σ‖ₑ ≤ ENNReal.ofReal (s ^ Fintype.card ι) := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_multiplier_le σ)
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity)]
  calc ENNReal.ofReal (‖WithLp.toLp 2 y‖ ^ (2 * n) * ‖ReproducingModel.innerSL v
          (ReproducingModel.heisenbergRep y (weilRep ε σ v))‖)
      = ‖WithLp.toLp 2 y‖ₑ ^ (2 * n) * ‖ReproducingModel.innerSL v
          (ReproducingModel.heisenbergRep y (weilRep ε σ v))‖ₑ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
          ofReal_norm]
    _ ≤ ‖WithLp.toLp 2 y‖ₑ ^ (2 * n) * (‖multiplier ε σ‖ₑ *
          ∫⁻ z, ‖v (σ⁻¹ • z)‖ₑ * ‖v (y + z)‖ₑ ∂measure ι) :=
        mul_le_mul_right (enorm_innerSL_heisenbergRep_weilRep_le v v σ y) _
    _ ≤ ENNReal.ofReal (s ^ Fintype.card ι) * (ENNReal.ofReal (4 ^ n * s ^ (2 * n)) *
          ((((A + n) ^ n : ℕ) : ℝ≥0∞) * ∫⁻ x, ‖v x‖ₑ ^ 2 ∂measure ι)) := by
        rw [mul_left_comm]
        exact mul_le_mul' h_mult (enorm_toLp_pow_mul_lintegral_le
          (lintegral_enorm_pow_mul_enorm_polyVector_sq_le hP hA n) σ y)
    _ = ENNReal.ofReal ((4 * (A + n)) ^ n * s ^ (Fintype.card ι + 2 * n) *
          (ReproducingModel.innerSL v v).re) := by
        rw [h_V, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        push_cast
        rw [mul_pow, pow_add]
        ring

end TauCeti.Fock

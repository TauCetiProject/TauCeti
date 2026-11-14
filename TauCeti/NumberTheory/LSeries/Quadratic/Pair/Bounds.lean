/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
public import TauCeti.Data.Nat.GCD
import TauCeti.NumberTheory.LSeries.RiemannZeta.Bounds

/-!
# Uniform bounds for the two-character L-function product

For characters of positive levels `M` and `N`, the three nonprincipal factors in
`ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` have product bounded by `343 (MN)²` on
`|s - 2| ≤ 3/2`. The constant is independent of both characters and levels. This is the
level-dependent input for Cauchy estimates on the regularized four-factor product, and hence
for the two-character comparison near one. The zeta regularization is a fixed entire function
and can be bounded on this disk independently of the characters.

For arbitrary characters (principal or nonprincipal), combining the right-half-plane bounds on
`riemannZeta` and `DirichletCharacter.LFunction` also bounds the full four-factor product on
`Re s > 0` away from `s = 1` by `(MN)² (‖s - 1‖⁻¹ + 1 + ‖s‖ / Re s)⁴` (`norm_pair_le`), and
hence by `625 (MN)² (1 + (Im s)²)²` on `Re s ≥ 1 / 2` outside `‖s - 1‖ < 1 / 2`
(`norm_pair_le_of_one_half_le_re`) and across the critical line `Re s = 1 / 2`
(`norm_pair_le_of_re_eq_one_half`).

The estimates use the continued L-functions, not the junk value of a divergent series.
Quadraticity and primitivity are unnecessary; for primitive characters the levels are their
conductors. The product character stays at its actual least-common-multiple level, retaining all
deleted Euler factors.

## References

* H. Davenport, *Multiplicative Number Theory*, the chapter on Siegel's theorem.
* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
-/

public section

open Complex Metric

namespace DirichletCharacter

variable {M N : ℕ} [NeZero M] [NeZero N]
variable (χ : DirichletCharacter ℂ M) (ψ : DirichletCharacter ℂ N)

/-- The three nonprincipal L-factors in the two-character product have a uniform polynomial
level bound on the closed disk used for Cauchy estimates near one. -/
theorem norm_LFunction_mul_mul_le_of_mem_closedBall (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (hχψ : χ.mul ψ ≠ 1) {s : ℂ} (hs : s ∈ closedBall (2 : ℂ) (3 / 2)) :
    ‖χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s‖ ≤
      343 * ((M : ℝ) * N) ^ 2 := by
  have hdist : ‖s - 2‖ ≤ 3 / 2 := mem_closedBall_iff_norm.mp hs
  have hre : 1 / 2 ≤ s.re := by
    have hlo := neg_abs_le (s - 2).re
    have habs := abs_re_le_norm (s - 2)
    norm_num [sub_re] at hlo habs
    linarith
  have hnorm : ‖s‖ ≤ 7 / 2 := by
    have := norm_le_insert (2 : ℂ) s
    norm_num [norm_sub_rev (2 : ℂ) s] at this
    linarith
  have hbound {L : ℕ} [NeZero L] (ρ : DirichletCharacter ℂ L) (hρ : ρ ≠ 1) :
      ‖ρ.LFunction s‖ ≤ 7 * L := by
    have hb := ρ.norm_LFunction_le_level_mul_norm_div_re hρ (by linarith : 0 < s.re)
    apply hb.trans
    apply (div_le_iff₀ (by linarith : 0 < s.re)).mpr
    nlinarith
  have hlcm : (Nat.lcm M N : ℝ) ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (NeZero.pos M) (NeZero.pos N))
      (Nat.lcm_dvd_mul M N)
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (7 * (M : ℝ)) * (7 * N) * (7 * Nat.lcm M N) :=
      mul_le_mul (mul_le_mul (hbound χ hχ) (hbound ψ hψ) (norm_nonneg _) (by positivity))
        (hbound (χ.mul ψ) hχψ) (norm_nonneg _) (by positivity)
    _ ≤ (7 * M) * (7 * N) * (7 * ((M : ℝ) * N)) := by gcongr
    _ = 343 * ((M : ℝ) * N) ^ 2 := by ring

/-- On the open right half-plane `Re s > 0` away from `s = 1`, the four-factor product
`ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` of arbitrary characters of positive levels `M` and `N`
satisfies `‖F(s)‖ ≤ (M N)² (‖s - 1‖⁻¹ + 1 + ‖s‖ / Re s)⁴`. Neither quadraticity nor
nonprincipality is required. -/
theorem norm_pair_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s‖ ≤
      ((M : ℝ) * N) ^ 2 * (‖s - 1‖⁻¹ + 1 + ‖s‖ / s.re) ^ 4 := by
  set B : ℝ := ‖s - 1‖⁻¹ + 1 + ‖s‖ / s.re
  have hB : 0 ≤ B := by positivity
  have hlcm : (Nat.lcm M N : ℝ) ≤ (M : ℝ) * N := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (NeZero.pos M) (NeZero.pos N)) (Nat.lcm_dvd_mul M N)
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖riemannZeta s‖ * ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ * ‖(χ.mul ψ).LFunction s‖
      ≤ B * ((M : ℝ) * B) * ((N : ℝ) * B) * ((Nat.lcm M N : ℝ) * B) :=
        mul_le_mul
          (mul_le_mul
            (mul_le_mul (TauCeti.norm_riemannZeta_le hs) (χ.norm_LFunction_le hs (.inl hs1))
              (norm_nonneg _) hB)
            (ψ.norm_LFunction_le hs (.inl hs1)) (norm_nonneg _) (by positivity))
          ((χ.mul ψ).norm_LFunction_le hs (.inl hs1)) (norm_nonneg _) (by positivity)
    _ = (M : ℝ) * N * (Nat.lcm M N : ℝ) * B ^ 4 := by ring
    _ ≤ (M : ℝ) * N * ((M : ℝ) * N) * B ^ 4 := by gcongr
    _ = ((M : ℝ) * N) ^ 2 * B ^ 4 := by ring

/-- On the half-plane `Re s ≥ 1 / 2` outside `‖s - 1‖ < 1 / 2`, the four-factor product satisfies
the uniform polynomial vertical bound `‖F(s)‖ ≤ 625 (M N)² (1 + (Im s)²)²`. -/
theorem norm_pair_le_of_one_half_le_re {s : ℂ} (hre : 1 / 2 ≤ s.re) (hs1 : 1 / 2 ≤ ‖s - 1‖) :
    ‖riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s‖ ≤
      625 * ((M : ℝ) * N) ^ 2 * (1 + s.im ^ 2) ^ 2 := by
  have hs_pos : 0 < s.re := by linarith
  have hs_ne : s ≠ 1 := fun h ↦ by simp [h] at hs1; norm_num at hs1
  have hinv : ‖s - 1‖⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    simpa using hs1
  have hsq : ‖s‖ ^ 2 ≤ (2 * s.re * √(1 + s.im ^ 2)) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    have hre_sq : 1 ≤ 4 * s.re ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hre_sq (sq_nonneg s.im), sq_nonneg s.re]
  have hnorm : ‖s‖ ≤ 2 * s.re * √(1 + s.im ^ 2) :=
    le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq
  have hdiv : ‖s‖ / s.re ≤ 2 * √(1 + s.im ^ 2) :=
    (div_le_iff₀ hs_pos).mpr (by linarith)
  have hone : 1 ≤ √(1 + s.im ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg s.im])
  have hbase : ‖s - 1‖⁻¹ + 1 + ‖s‖ / s.re ≤ 5 * √(1 + s.im ^ 2) := by linarith
  have hpow : (‖s - 1‖⁻¹ + 1 + ‖s‖ / s.re) ^ 4 ≤ 625 * (1 + s.im ^ 2) ^ 2 :=
    calc (‖s - 1‖⁻¹ + 1 + ‖s‖ / s.re) ^ 4 ≤ (5 * √(1 + s.im ^ 2)) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hbase 4
      _ = 625 * (√(1 + s.im ^ 2) ^ 2) ^ 2 := by ring
      _ = 625 * (1 + s.im ^ 2) ^ 2 := by rw [Real.sq_sqrt (by positivity)]
  calc ‖riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s‖
      ≤ ((M : ℝ) * N) ^ 2 * (‖s - 1‖⁻¹ + 1 + ‖s‖ / s.re) ^ 4 := norm_pair_le χ ψ hs_pos hs_ne
    _ ≤ ((M : ℝ) * N) ^ 2 * (625 * (1 + s.im ^ 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 625 * ((M : ℝ) * N) ^ 2 * (1 + s.im ^ 2) ^ 2 := by ring

/-- On the critical line `Re s = 1 / 2`, the four-factor product satisfies
`‖F(s)‖ ≤ 625 (M N)² (1 + (Im s)²)²`. -/
theorem norm_pair_le_of_re_eq_one_half {s : ℂ} (hs : s.re = 1 / 2) :
    ‖riemannZeta s * χ.LFunction s * ψ.LFunction s * (χ.mul ψ).LFunction s‖ ≤
      625 * ((M : ℝ) * N) ^ 2 * (1 + s.im ^ 2) ^ 2 := by
  have hs1 : 1 / 2 ≤ ‖s - 1‖ := by
    have h := abs_re_le_norm (s - 1)
    rw [sub_re, hs, one_re] at h
    norm_num at h
    exact h
  exact norm_pair_le_of_one_half_le_re χ ψ hs.ge hs1

end DirichletCharacter

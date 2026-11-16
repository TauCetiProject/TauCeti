/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Bounds
public import TauCeti.Data.Nat.GCD

/-!
# Uniform bounds for the two-character L-function product

For characters of positive levels `M` and `N`, the three nonprincipal factors in
`ζ(s) L(s, χ) L(s, ψ) L(s, χ.mul ψ)` have product bounded by `343 (MN)²` on
`|s - 2| ≤ 3/2`. The constant is independent of both characters and levels. This is the
level-dependent input for Cauchy estimates on the regularized four-factor product, and hence
for the two-character comparison near one. The zeta regularization is a fixed entire function
and can be bounded on this disk independently of the characters.

The estimate uses the continued L-functions, not the junk value of a divergent series.
Quadraticity and primitivity are unnecessary for this estimate; for primitive characters
the levels are their conductors. The product character stays at its actual least-common-multiple
level, retaining all deleted Euler factors.

## References

* H. Davenport, *Multiplicative Number Theory*, the chapter on Siegel's theorem.
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

end DirichletCharacter

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.Analysis.Complex.JensenFormula
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.Analysis.Meromorphic.Divisor
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.StripGrowth
import TauCeti.NumberTheory.LSeries.DirichletEulerLog

/-!
# The conductor-uniform local expansion of `L′/L(s, χ)`

Let `χ` be a primitive nonprincipal Dirichlet character of conductor `N`. Fix a real `σ₀ > 1` and
radii `r < r'`. There is a constant `C`, depending only on `σ₀, r, r'` and not on `N` or `χ`,
such that for every centre `s₀` with `Re s₀ = σ₀` and every `s` with `‖s - s₀‖ ≤ r` and
`L(s, χ) ≠ 0`,
`‖L′/L(s, χ) - ∑_{‖ρ - s₀‖ ≤ r'} m(ρ)/(s - ρ)‖ ≤ C log(N (|Im s₀| + 2))`.
The sum runs over every zero `ρ` of `L(s, χ)` in the closed disc, trivial zeros included, weighted
by its analytic order `m(ρ)`. With the same uniformity, the zeros in such a disc, counted with
order, number `O(log(N (|Im s₀| + 2)))`; this count holds for discs centred on any vertical line.

These are the conductor-uniform zero count and local logarithmic derivative used for primitive
characters in Landau's and Siegel's arguments, in the zero-free regions and in the explicit
formula. The case `N = 1`, where `L(s, χ) = ζ(s)` has a pole, is
`TauCeti.riemannZeta_local_logDeriv`.

## Main results

* `DirichletCharacter.divisor_LFunction_closedBall_apply`: for `χ ≠ 1`, the divisor of
  `L(·, χ)` on a closed disc records the orders of its zeros in the disc.
* `DirichletCharacter.finsum_subtype_LFunction_eq_finsum_divisor`: an order-weighted sum over the
  zeros of `L(·, χ)` in a closed disc is the corresponding divisor sum.
* `TauCeti.exists_norm_LFunction_le_rpow_mul`: on discs centred on a line `Re s₀ = σ₀ > 1`,
  `‖L(w, χ)‖ ≤ (N (|Im s₀| + 2)) ^ D ‖L(s₀, χ)‖`, uniformly in `N` and `χ`.
* `TauCeti.exists_finsum_analyticOrderAt_LFunction_le`: the zeros of `L(·, χ)` in a closed disc
  of fixed radius centred on a line `Re s₀ = σ₀` number `O(log(N (|Im s₀| + 2)))`.
* `TauCeti.LFunction_local_logDeriv`: the local expansion of `L′/L(s, χ)`.

## Implementation notes

For `χ ≠ 1` the function `L(·, χ)` is entire. The relative growth bound
`TauCeti.exists_norm_LFunction_le_rpow_mul` combines the conductor-uniform disc bound
`TauCeti.exists_norm_LFunction_le_rpow_of_norm_sub_le` with the centre lower bound
`‖L(s₀, χ)‖ ≥ exp(-Re ζ(σ₀))` from `DirichletCharacter.exp_neg_re_riemannZeta_le_norm_LFunction`,
which holds for every character; `Real.exists_mul_rpow_le_rpow_mul` absorbs the constants. Jensen's
bound `AnalyticOnNhd.sum_divisor_le_log_div_log_of_closedBall_subset` on a larger disc about
`2 + i Im s₀` then counts the zeros, and Landau's local lemma, in the uniform form
`TauCeti.exists_norm_logDeriv_sub_finsum_divisor_le`, on the discs of radii `r'` and `r' + 1` gives
the expansion. The divisor translations are instances of
`AnalyticOnNhd.divisor_closedBall_apply` and `AnalyticOnNhd.finsum_subtype_eq_finsum_divisor`.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Lemma 8.6, pp.90–91, and Lemmas 11.2
  and 11.4, pp.113–115.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 16.
-/

public section

open Complex Metric Set

namespace DirichletCharacter

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- For a nonprincipal character `χ`, the divisor of the entire function `L(·, χ)` on a closed
disc is the analytic order of `L(·, χ)` at its zeros in the disc, and zero elsewhere. -/
theorem divisor_LFunction_closedBall_apply (hχ : χ ≠ 1) (s₀ ρ : ℂ) (r : ℝ) :
    MeromorphicOn.divisor χ.LFunction (closedBall s₀ r) ρ =
      if ‖ρ - s₀‖ ≤ r ∧ χ.LFunction ρ = 0 then ((analyticOrderAt χ.LFunction ρ).toNat : ℤ)
      else 0 :=
  AnalyticOnNhd.divisor_closedBall_apply (fun _ _ ↦ χ.analyticAt_LFunction (.inr hχ)) ρ

/-- For a nonprincipal character `χ`, a sum over the zeros of `L(·, χ)` in a closed disc, each
weighted by its analytic order, is the corresponding sum against the divisor of `L(·, χ)` on that
disc. -/
theorem finsum_subtype_LFunction_eq_finsum_divisor {R : Type*} [Ring R] (hχ : χ ≠ 1) (s₀ : ℂ)
    (r : ℝ) (w : ℂ → R) :
    ∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r ∧ χ.LFunction z = 0},
        ((analyticOrderAt χ.LFunction ρ.val).toNat : R) * w ρ.val =
      ∑ᶠ ρ, (MeromorphicOn.divisor χ.LFunction (closedBall s₀ r) ρ : R) * w ρ :=
  AnalyticOnNhd.finsum_subtype_eq_finsum_divisor (fun _ _ ↦ χ.analyticAt_LFunction (.inr hχ)) w

end DirichletCharacter

open DirichletCharacter

namespace TauCeti

/-- **Conductor-uniform relative growth on discs.** For real `σ₀ > 1` and a radius `R` there is
an exponent `D` such that every primitive nonprincipal Dirichlet character `χ` of conductor `N`
satisfies `‖L(w, χ)‖ ≤ (N (|Im s₀| + 2)) ^ D ‖L(s₀, χ)‖` for every centre `s₀` with
`Re s₀ = σ₀` and every `w` with `‖w - s₀‖ ≤ R`. The exponent depends on `σ₀` and `R` alone. -/
theorem exists_norm_LFunction_le_rpow_mul {σ₀ : ℝ} (hσ₀ : 1 < σ₀) (R : ℝ) :
    ∃ D : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ s₀ w : ℂ, s₀.re = σ₀ → ‖w - s₀‖ ≤ R →
        ‖χ.LFunction w‖ ≤ (N * (|s₀.im| + 2)) ^ D * ‖χ.LFunction s₀‖ := by
  obtain ⟨K, B, -, -, hdisc⟩ := exists_norm_LFunction_le_rpow_of_norm_sub_le σ₀ R
  obtain ⟨D, hD⟩ := Real.exists_mul_rpow_le_rpow_mul K B (Real.exp_pos (-(riemannZeta σ₀).re))
    one_lt_two
  refine ⟨D, fun N _ χ hχ hne s₀ w hs₀ hw ↦ (hdisc N χ hχ hne s₀ w hs₀ hw).trans (hD _ _ ?_ ?_)⟩
  · have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr NeZero.one_le
    nlinarith [abs_nonneg s₀.im]
  · simpa [hs₀] using χ.exp_neg_re_riemannZeta_le_norm_LFunction (s := s₀) (by linarith)

/-- **Conductor-uniform count of zeros in discs.** For real `σ₀` and `r` there is a constant `C`
such that for every primitive nonprincipal Dirichlet character `χ` of conductor `N` and every
centre `s₀` with `Re s₀ = σ₀`, the zeros of `L(·, χ)` in the closed disc of radius `r` about `s₀`,
counted with analytic order, number at most `C log(N (|Im s₀| + 2))`. -/
theorem exists_finsum_analyticOrderAt_LFunction_le (σ₀ r : ℝ) :
    ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ s₀ : ℂ, s₀.re = σ₀ →
        ∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r ∧ χ.LFunction z = 0},
            ((analyticOrderAt χ.LFunction ρ.val).toNat : ℝ) ≤
          C * Real.log (N * (|s₀.im| + 2)) := by
  set R := |r| + |σ₀ - 2| + 1
  have hR : 0 < R := by positivity
  obtain ⟨D, hD⟩ := exists_norm_LFunction_le_rpow_mul one_lt_two (R + 1)
  refine ⟨D / Real.log ((R + 1) / R), fun N _ χ hχ hne s₀ hs₀ ↦ ?_⟩
  set c : ℂ := 2 + s₀.im * I
  have hc : c.re = 2 := by simp [c]
  have hcim : c.im = s₀.im := by simp [c]
  have hX : 0 < (N : ℝ) * (|s₀.im| + 2) := by have := NeZero.pos N; positivity
  have hsub : closedBall s₀ r ⊆ closedBall c R := closedBall_subset_closedBall' <| by
    rw [Complex.dist_of_im_eq hcim.symm, hs₀, hc, Real.dist_eq]
    linarith [le_abs_self r]
  have hJ := AnalyticOnNhd.sum_divisor_le_log_div_log_of_closedBall_subset
    (fun _ _ ↦ χ.analyticAt_LFunction (.inr hne)) hR (lt_add_one R)
    (LFunction_ne_zero_of_one_le_re χ (.inl hne) (by simp [hc]))
    (fun w hw ↦ hD N χ hχ hne c w hc (by rw [mem_sphere, dist_eq_norm] at hw; exact hw.le)) hsub
  rw [Real.log_rpow (by rwa [hcim]), hcim] at hJ
  have hsum := χ.finsum_subtype_LFunction_eq_finsum_divisor (R := ℝ) hne s₀ r fun _ ↦ 1
  simp only [mul_one] at hsum
  have hcast := map_finsum (Int.castRingHom ℝ)
    ((MeromorphicOn.divisor χ.LFunction (closedBall s₀ r)).finiteSupport (isCompact_closedBall _ _))
  simp only [eq_intCast] at hcast
  rw [hsum, ← hcast]
  exact hJ.trans_eq (by ring)

/-- **The conductor-uniform local expansion of `L′/L`.** For real `σ₀ > 1` and radii `r < r'`
there is a constant `C` such that for every primitive nonprincipal Dirichlet character `χ` of
conductor `N`, every `s₀` with `Re s₀ = σ₀` and every `s` with `‖s - s₀‖ ≤ r` and `L(s, χ) ≠ 0`,
`L′/L(s, χ)` differs from `∑ m(ρ)/(s - ρ)` over the zeros `ρ` of `L(·, χ)` with
`‖ρ - s₀‖ ≤ r'`, counted with analytic order `m(ρ)`, by at most `C log(N (|Im s₀| + 2))`. The
constant depends on `σ₀, r, r'` alone. -/
theorem LFunction_local_logDeriv {σ₀ r r' : ℝ} (hσ₀ : 1 < σ₀) (hrr' : r < r') :
    ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ s₀ s : ℂ, s₀.re = σ₀ → ‖s - s₀‖ ≤ r → χ.LFunction s ≠ 0 →
        ‖deriv χ.LFunction s / χ.LFunction s -
            ∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r' ∧ χ.LFunction z = 0},
              ((analyticOrderAt χ.LFunction ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
          C * Real.log (N * (|s₀.im| + 2)) := by
  obtain ⟨D, hD⟩ := exists_norm_LFunction_le_rpow_mul hσ₀ (r' + 1)
  obtain ⟨A, hA⟩ := exists_norm_logDeriv_sub_finsum_divisor_le hrr' (lt_add_one r')
  refine ⟨A * D, fun N _ χ hχ hne s₀ s hs₀ hs hL ↦ ?_⟩
  have hX : 0 < (N : ℝ) * (|s₀.im| + 2) := by have := NeZero.pos N; positivity
  have key := hA (fun _ _ ↦ χ.analyticAt_LFunction (.inr hne))
    (fun w hw ↦ hD N χ hχ hne s₀ w hs₀ (by rw [mem_sphere, dist_eq_norm] at hw; exact hw.le))
    (LFunction_ne_zero_of_one_le_re χ (.inl hne) (by linarith)) hs hL
  have hsum := χ.finsum_subtype_LFunction_eq_finsum_divisor (R := ℂ) hne s₀ r' fun ρ ↦ 1 / (s - ρ)
  simp only [mul_one_div] at hsum
  rw [logDeriv_apply, ← hsum, Real.log_rpow hX] at key
  exact key.trans_eq (by ring)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.Analysis.Complex.AbsMax
import TauCeti.Analysis.Complex.JensenFormula
import TauCeti.Analysis.Complex.LocalLogDeriv
import TauCeti.Analysis.Meromorphic.Divisor
import TauCeti.NumberTheory.DirichletCharacter.LFunction.StripGrowth
import TauCeti.NumberTheory.LSeries.DirichletEulerLog

/-!
# The conductor-uniform local expansion of `L′/L(s, χ)`

Let `χ` be a primitive nonprincipal Dirichlet character of conductor `N`. Fix a real `σ₀ > 1` and
radii `0 < r < r'`. There is a constant `C`, depending only on `σ₀, r, r'` and not on `N` or `χ`,
such that for every centre `s₀` with `Re s₀ = σ₀` and every `s` with `‖s - s₀‖ ≤ r` and
`L(s, χ) ≠ 0`,
`‖L′/L(s, χ) - ∑_{‖ρ - s₀‖ ≤ r'} m(ρ)/(s - ρ)‖ ≤ C log(N (|Im s₀| + 2))`.
The sum runs over every zero `ρ` of `L(s, χ)` in the closed disc, trivial zeros included, weighted
by its analytic order `m(ρ)`. With the same uniformity, the zeros in such a disc, counted with
order, number `O(log(N (|Im s₀| + 2)))`.

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
  of fixed radius centred on `Re s₀ = σ₀ > 1` number `O(log(N (|Im s₀| + 2)))`.
* `TauCeti.LFunction_local_logDeriv`: the local expansion of `L′/L(s, χ)`.

## Implementation notes

For `χ ≠ 1` the function `L(·, χ)` is entire. The relative growth bound
`TauCeti.exists_norm_LFunction_le_rpow_mul` combines the conductor-uniform disc bound
`TauCeti.exists_norm_LFunction_le_rpow_of_norm_sub_le` with the centre lower bound
`‖L(s₀, χ)‖ ≥ exp(-Re ζ(σ₀))` from `DirichletCharacter.exp_neg_re_riemannZeta_le_norm_LFunction`,
which holds for every character. Jensen's bound `AnalyticOnNhd.sum_divisor_le_log_div_log` then
counts the zeros, and Landau's local lemma `AnalyticOnNhd.norm_logDeriv_sub_finsum_divisor_le` on
the discs of radii `r'` and `r' + 1` gives the expansion.

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
      else 0 := by
  have hF := (differentiable_LFunction hχ).differentiableOn.analyticOnNhd isOpen_univ
  by_cases hρ : ‖ρ - s₀‖ ≤ r ∧ χ.LFunction ρ = 0
  · have hmem : ρ ∈ closedBall s₀ r := by
      rw [mem_closedBall, dist_eq_norm]
      exact hρ.1
    rw [ite_eq_left hρ, (hF.mono (subset_univ _)).meromorphicOn.divisor_eq_analyticOrderNatAt
      (hF ρ trivial) hmem, analyticOrderNatAt]
  · rw [ite_eq_right hρ]
    by_cases hmem : ρ ∈ closedBall s₀ r
    · refine (hF ρ trivial).divisor_apply_eq_zero fun h ↦ hρ ⟨?_, h⟩
      rwa [mem_closedBall, dist_eq_norm] at hmem
    · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hmem

/-- For a nonprincipal character `χ`, a sum over the zeros of `L(·, χ)` in a closed disc, each
weighted by its analytic order, is the corresponding sum against the divisor of `L(·, χ)` on that
disc. -/
theorem finsum_subtype_LFunction_eq_finsum_divisor {R : Type*} [Ring R] (hχ : χ ≠ 1) (s₀ : ℂ)
    (r : ℝ) (w : ℂ → R) :
    ∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r ∧ χ.LFunction z = 0},
        ((analyticOrderAt χ.LFunction ρ.val).toNat : R) * w ρ.val =
      ∑ᶠ ρ, (MeromorphicOn.divisor χ.LFunction (closedBall s₀ r) ρ : R) * w ρ := by
  refine (finsum_subtype_eq_finsum_cond (f := fun z ↦
    ((analyticOrderAt χ.LFunction z).toNat : R) * w z) _).trans (finsum_congr fun ρ ↦ ?_)
  rw [finsum_eq_if, χ.divisor_LFunction_closedBall_apply hχ]
  split_ifs <;> simp

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
  obtain ⟨K, B, hK, -, hdisc⟩ := exists_norm_LFunction_le_rpow_of_norm_sub_le σ₀ R
  set c₀ := Real.exp (-(riemannZeta σ₀).re)
  have hc₀ : 0 < c₀ := Real.exp_pos _
  set E := |Real.log K| + |Real.log c₀|
  have := Real.log_pos one_lt_two
  refine ⟨B + E / Real.log 2, fun N _ χ hχ hne s₀ w hs₀ hw ↦ ?_⟩
  set X : ℝ := N * (|s₀.im| + 2)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hX : 2 ≤ X := by
    simp only [X]
    nlinarith [abs_nonneg s₀.im]
  have hcentre : c₀ ≤ ‖χ.LFunction s₀‖ := by
    simpa [c₀, hs₀] using χ.exp_neg_re_riemannZeta_le_norm_LFunction (s := s₀) (by linarith)
  have hKc : K ≤ c₀ * Real.exp E := by
    rw [← Real.exp_log hK, ← Real.exp_log hc₀, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [le_abs_self (Real.log K), neg_abs_le (Real.log c₀)])
  have hEX : Real.exp E ≤ X ^ (E / Real.log 2) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    refine Real.exp_le_exp.mpr ?_
    calc E = Real.log 2 * (E / Real.log 2) := by field_simp
      _ ≤ Real.log X * (E / Real.log 2) := by gcongr
  calc ‖χ.LFunction w‖ ≤ K * X ^ B := hdisc N χ hχ hne s₀ w hs₀ hw
    _ ≤ c₀ * X ^ (E / Real.log 2) * X ^ B := by gcongr; exact hKc.trans (by gcongr)
    _ = X ^ (B + E / Real.log 2) * c₀ := by rw [Real.rpow_add (by linarith)]; ring
    _ ≤ _ := by gcongr

/-- **Conductor-uniform count of zeros in discs.** For real `σ₀ > 1` and `r > 0` there is a
constant `C` such that for every primitive nonprincipal Dirichlet character `χ` of conductor `N`
and every centre `s₀` with `Re s₀ = σ₀`, the zeros of `L(·, χ)` in the closed disc of radius `r`
about `s₀`, counted with analytic order, number at most `C log(N (|Im s₀| + 2))`. -/
theorem exists_finsum_analyticOrderAt_LFunction_le {σ₀ r : ℝ} (hσ₀ : 1 < σ₀) (hr : 0 < r) :
    ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ s₀ : ℂ, s₀.re = σ₀ →
        ∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r ∧ χ.LFunction z = 0},
            ((analyticOrderAt χ.LFunction ρ.val).toNat : ℝ) ≤
          C * Real.log (N * (|s₀.im| + 2)) := by
  obtain ⟨D, hD⟩ := exists_norm_LFunction_le_rpow_mul hσ₀ (r + 1)
  refine ⟨D / Real.log ((r + 1) / r), fun N _ χ hχ hne s₀ hs₀ ↦ ?_⟩
  have hX : 0 < (N : ℝ) * (|s₀.im| + 2) :=
    mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))) (by positivity)
  have hF := (differentiable_LFunction hne).differentiableOn.analyticOnNhd isOpen_univ
  have hFs₀ : χ.LFunction s₀ ≠ 0 := LFunction_ne_zero_of_one_le_re χ (.inl hne) (by linarith)
  have hJ := (hF.mono (subset_univ _)).sum_divisor_le_log_div_log hr (lt_add_one r) hFs₀
    fun w hw ↦ hD N χ hχ hne s₀ w hs₀ (by rw [mem_sphere, dist_eq_norm] at hw; exact hw.le)
  rw [Real.log_rpow hX] at hJ
  have hfin : Function.HasFiniteSupport (MeromorphicOn.divisor χ.LFunction (closedBall s₀ r)) :=
    (MeromorphicOn.divisor χ.LFunction (closedBall s₀ r)).finiteSupport (isCompact_closedBall _ _)
  have hsum := χ.finsum_subtype_LFunction_eq_finsum_divisor (R := ℝ) hne s₀ r fun _ ↦ 1
  simp only [mul_one] at hsum
  have hcast := map_finsum (Int.castRingHom ℝ) hfin
  simp only [eq_intCast] at hcast
  rw [hsum, ← hcast]
  calc _ ≤ D * Real.log (N * (|s₀.im| + 2)) / Real.log ((r + 1) / r) := hJ
    _ = _ := by ring

/-- **The conductor-uniform local expansion of `L′/L`.** For real `σ₀ > 1` and radii `0 < r < r'`
there is a constant `C` such that for every primitive nonprincipal Dirichlet character `χ` of
conductor `N`, every `s₀` with `Re s₀ = σ₀` and every `s` with `‖s - s₀‖ ≤ r` and `L(s, χ) ≠ 0`,
`L′/L(s, χ)` differs from `∑ m(ρ)/(s - ρ)` over the zeros `ρ` of `L(·, χ)` with
`‖ρ - s₀‖ ≤ r'`, counted with analytic order `m(ρ)`, by at most `C log(N (|Im s₀| + 2))`. The
constant depends on `σ₀, r, r'` alone. -/
theorem LFunction_local_logDeriv {σ₀ r r' : ℝ} (hσ₀ : 1 < σ₀) (hr : 0 < r) (hrr' : r < r') :
    ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
      ∀ s₀ s : ℂ, s₀.re = σ₀ → ‖s - s₀‖ ≤ r → χ.LFunction s ≠ 0 →
        ‖deriv χ.LFunction s / χ.LFunction s -
            ∑ᶠ ρ : {z : ℂ // ‖z - s₀‖ ≤ r' ∧ χ.LFunction z = 0},
              ((analyticOrderAt χ.LFunction ρ.val).toNat : ℂ) / (s - ρ.val)‖ ≤
          C * Real.log (N * (|s₀.im| + 2)) := by
  obtain ⟨D, hD⟩ := exists_norm_LFunction_le_rpow_mul hσ₀ (r' + 1)
  have hlog : 0 < Real.log ((r' + 1) / r') :=
    Real.log_pos ((one_lt_div (by linarith)).mpr (by linarith))
  have hR : 0 < (r' + 1) ^ 2 - r' * r := by nlinarith
  set A := 4 * (r' + r) / (r' - r) ^ 2 +
    r' / (((r' + 1) ^ 2 - r' * r) * Real.log ((r' + 1) / r')) with hAdef
  refine ⟨A * D, fun N _ χ hχ hne s₀ s hs₀ hs hL ↦ ?_⟩
  have hF := (differentiable_LFunction hne).differentiableOn.analyticOnNhd isOpen_univ
  have hFb := hF.mono (subset_univ (closedBall s₀ (r' + 1)))
  set X : ℝ := N * (|s₀.im| + 2)
  have hX : 0 < X := mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))) (by positivity)
  have hsphere (w : ℂ) (hw : w ∈ sphere s₀ (r' + 1)) :
      ‖χ.LFunction w‖ ≤ X ^ D * ‖χ.LFunction s₀‖ :=
    hD N χ hχ hne s₀ w hs₀ (by rw [mem_sphere, dist_eq_norm] at hw; exact hw.le)
  have hFs₀ : χ.LFunction s₀ ≠ 0 := LFunction_ne_zero_of_one_le_re χ (.inl hne) (by linarith)
  have hM1 : 1 ≤ X ^ D :=
    (hFb.differentiableOn.diffContOnCl_ball Subset.rfl).one_le_of_forall_mem_sphere_norm_le_mul
      (by linarith) hFs₀ hsphere
  have key := hFb.norm_logDeriv_sub_finsum_divisor_le (lt_add_one r') hsphere (hs.trans_lt hrr') hL
  have hsum := χ.finsum_subtype_LFunction_eq_finsum_divisor (R := ℂ) hne s₀ r' fun ρ ↦ 1 / (s - ρ)
  simp only [mul_one_div] at hsum
  rw [logDeriv_apply, ← hsum] at key
  have hA : 4 * (r' + ‖s - s₀‖) / (r' - ‖s - s₀‖) ^ 2 +
      r' / (((r' + 1) ^ 2 - r' * ‖s - s₀‖) * Real.log ((r' + 1) / r')) ≤ A := by
    rw [hAdef]
    gcongr <;> nlinarith [norm_nonneg (s - s₀)]
  calc _ ≤ _ := key
    _ ≤ A * Real.log (X ^ D) := mul_le_mul_of_nonneg_right hA (Real.log_nonneg hM1)
    _ = _ := by rw [Real.log_rpow hX]; ring

end TauCeti
